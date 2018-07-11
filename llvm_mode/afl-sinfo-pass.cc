/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"
//#include "../alloc-inl.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/stat.h>
#include <set>
#include <map>


#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/CFG.h"

using namespace llvm;

#define AFL_TMP_FILE  "/tmp/afl_tmp_file"

namespace {

  class AFLSinfoCount : public ModulePass {

    public:

      static char ID;
      AFLSinfoCount() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      //const char *getPassName() const override {
      StringRef getPassName() const override {
        return "American Fuzzy Lop Instrumentation";
      }
      bool getInstructionDebugInfo(const llvm::Instruction *I, 
              std::string &File,
              unsigned &Line);

      unsigned int func_num;
      unsigned int bb_num;
      unsigned int edge_num;
      unsigned int mulin_bb_num;  // a bb have multi income edges
      unsigned int mulout_bb_num;


  };

}

static int writeIndex(char* fd_file_name, int value)
{

    FILE	*fd;										/* output-file pointer */

    fd	= fopen( fd_file_name, "w" );
    if ( fd == NULL ) {
        fprintf ( stderr, "couldn't open file '%s'; %s\n",
                fd_file_name, strerror(errno) );
        return -1;
    }

    if( fprintf( fd, "%d", value) != 1 )
        return -1;

    if( fclose(fd) == EOF ) {			/* close output file   */
        fprintf ( stderr, "couldn't close file '%s'; %s\n",
                fd_file_name, strerror(errno) );
        exit (EXIT_FAILURE);
    }

    return 0;

}

static int readIndex(char* fd_file_name)
{

    FILE	*fd;										/* input-file pointer */
    int index;
    struct stat buf;

    fd	= fopen( fd_file_name, "r" );
    if ( fd == NULL ) {
        fprintf ( stderr, "couldn't open file '%s'; %s\n",
                fd_file_name, strerror(errno) );
        return -2;
    }

    fstat(fileno(fd), &buf);
    long modifyTime = buf.st_mtime;
    long curTime = time((time_t*)NULL);
    if( curTime - modifyTime > 10) {
        printf("time-diff = %d\n", curTime-modifyTime);
        fclose(fd);
        writeIndex(fd_file_name, 0);
        return 0;
    }
    

    if( fscanf(fd, "%d", &index) != 1 )
        return -1;

    if( fclose(fd) == EOF ) {			/* close input file   */
        fprintf ( stderr, "couldn't close file '%s'; %s\n",
                fd_file_name, strerror(errno) );
        exit (EXIT_FAILURE);
    }

    return index;
}


static unsigned char* alloc_printf(const char* _str, ...) { 
    unsigned char* _tmp; 
    va_list ap;
    va_start(ap, _str);
    int _len = snprintf(NULL, 0, _str); 
    if (_len < 0) FATAL("Whoa, snprintf() fails?!"); 
    _tmp = (unsigned char*)malloc(_len + 1); 
    snprintf((char*)_tmp, _len + 1, _str); 
    va_end(ap);
    return _tmp; 
}

static std::string getDSPIPath(DILocation *Loc) {
  std::string dir = Loc->getDirectory();
  std::string file = Loc->getFilename();
  if (dir.empty() || file[0] == '/') {
    return file;
  } else if (*dir.rbegin() == '/') {
    return dir + file;
  } else {
    return dir + "/" + file;
  }
}

bool AFLSinfoCount::getInstructionDebugInfo(const llvm::Instruction *I, 
                                                   std::string &File,
                                                   unsigned &Line) {
  //if (MDNode *N = I->getMetadata("dbg")) {
    //DILocation Loc(N);
  if(DILocation *Loc = I->getDebugLoc()) {
    File = getDSPIPath(Loc);
    Line = Loc->getLine();
    return true;
  }
  else {
      File="nofilefind";
      Line = 0;
      return false;
  }

}



char AFLSinfoCount::ID = 0;


bool AFLSinfoCount::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-sinfo-count " cBRI VERSION cRST " by <xiaoqixue_1@163.com>\n");

  } else be_quiet = 1;

  func_num=bb_num=edge_num=0;
  char* func_num_str = getenv("AFL_FUNC_NUM");
  if (func_num_str) {

    if (sscanf(func_num_str, "%u", &func_num) != 1)
      FATAL("Bad value of AFL_FUNC_NUM must be a number)");

  }

  char* bb_num_str = getenv("AFL_BB_NUM");
  if (bb_num_str) {

    if (sscanf(bb_num_str, "%u", &bb_num) != 1)
      FATAL("Bad value of AFL_BB_NUM must be a number)");

  }
  
  char* edge_num_str = getenv("AFL_EDGE_NUM");
  if (edge_num_str) {

    if (sscanf(edge_num_str, "%u", &edge_num) != 1)
      FATAL("Bad value of AFL_EDGE_NUM must be a number)");

  }
  //printf("edge_num=%d\n", edge_num);

  unsigned int inst_funcs = 0;
  unsigned int inst_blocks = 0;
  unsigned int inst_edges = 0;
  unsigned int inst_mul_blocks = 0;

  typedef std::map<unsigned, std::set<unsigned> > BBSrcLineMapTy;
  typedef std::map<llvm::Function*, BBSrcLineMapTy> FuncBBMapTy;
  typedef std::map<std::string, FuncBBMapTy> srcBcMapTy;
  srcBcMapTy srcBcMap;


  for (auto &F : M) {
    if( F.isDeclaration() ) continue;
    inst_funcs++;
    //BasicBlock &entryBB = F.getEntryBlock();
    for (auto &BB : F) {

      inst_blocks++;

      /* Make up cur_loc */
      //unsigned int cur_loc = R(MAP_SIZE);
      unsigned int cur_loc = AFL_R(MAP_SIZE);
      //printf("bbID=%d, mapID=%d, func=%s\n", inst_blocks, cur_loc, 
              //F.getName().str().c_str());

      const TerminatorInst *term_inst = BB.getTerminator();
      unsigned int succ_edges = term_inst->getNumSuccessors();
      inst_edges += succ_edges;
      unsigned int pred_edges=0;
      for( BasicBlock *pred : predecessors(&BB) ) {
            pred_edges+=1;
      }
      if(succ_edges>1 && pred_edges>1) 
          inst_mul_blocks++;


      for (auto &II : BB) {
          std::string filename;
          unsigned line;
          bool bRet = getInstructionDebugInfo( &II, filename, line);
          if( bRet ) {
              //printf("%s:%d\n", filename.c_str(), line);
              FuncBBMapTy  &funcBBMap = srcBcMap[filename];
              BBSrcLineMapTy &bbSrcLineMap = funcBBMap[&F];
              bbSrcLineMap[inst_blocks].insert(line);
          }

      }

      
    }
  } //end for (auto F :M)

#define alloc_printf(_str...) ({ \
    u8* _tmp; \
    s32 _len = snprintf(NULL, 0, _str); \
    if (_len < 0) FATAL("Whoa, snprintf() fails?!"); \
    _tmp = (u8*)malloc(_len + 1); \
    snprintf((char*)_tmp, _len + 1, _str); \
    _tmp; \
  })


  func_num += inst_funcs;
  bb_num += inst_blocks;
  edge_num += inst_edges;
  u8* buf = alloc_printf("%d", func_num);
  setenv("AFL_FUNC_NUM", (const char*)buf, 1);
  buf = alloc_printf("%d", bb_num);
  setenv("AFL_BB_NUM", (const char*)buf, 1);
  buf = alloc_printf("%d", edge_num);
  setenv("AFL_EDGE_NUM", (const char*)buf, 1);
  free(buf);

  SAYF("func-num=%d, bb-num=%d(%d), edge-num=%d  in %s\n", 
          func_num, bb_num, inst_mul_blocks, edge_num,   M.getSourceFileName().c_str());

#if 0
  /* dump to src-id.txt */
  if( 0 ) {
    FILE *fd;
    char *file_name="src-id.txt";


    /* check the file modify time , if 10s earlier than now, clear it  */
    struct stat buf;
    fd	= fopen( file_name, "r" );
    if ( fd == NULL ) {
        fprintf ( stderr, "'%s': %s, open again\n",
                file_name, strerror(errno) );
        fd = fopen(file_name, "w");
    }
    else {
        fstat(fileno(fd), &buf);
        long modifyTime = buf.st_mtime;
        long curTime = time((time_t*)NULL);
        fclose(fd);

        if( curTime - modifyTime > 10) 
            fd = fopen(file_name, "w");
        else
            fd = fopen(file_name, "a+");
    }

    if(fd==NULL) {
        fprintf ( stderr, "couldn't open file 'src-id.txt'; %s\n",
                 strerror(errno) );
        return -1;
    }
    srcBcMapTy::iterator sit = srcBcMap.begin(), sie = srcBcMap.end();
    for( ; sit!=sie; sit++) {
        std::string file = sit->first;
        fprintf(fd, "File: %s\n", file.c_str());
          //*srcInfoFile << "File: " << sit->first << "\n";
          FuncBBMapTy::iterator fit = sit->second.begin(), fie = sit->second.end();
          for(; fit!=fie; fit++) {
              llvm::Function* f =  fit->first;
              fprintf(fd, "Func: %s:\n", f->getName().str().c_str());
              //*srcInfoFile << "Func: " << f->getNameStr() << ":\n";
              BBSrcLineMapTy::iterator bit=fit->second.begin(), bie=fit->second.end();
              for(; bit!=bie; bit++) {
                  std::set<unsigned>::iterator it=bit->second.begin(), ie=bit->second.end();
                  for(; it!=ie; it++) {
                      if( *it == 0 ) continue;
                      fprintf(fd, "%d  %d\n", bit->first, *it);
                      //*srcInfoFile << bit->first << "  " << *it << "\n";
                  }
              }
          }
      }

    if( fclose(fd) == EOF ) {			/* close output file   */
        fprintf ( stderr, "couldn't close file 'src-id.txt'; %s\n",
                 strerror(errno) );
        exit (EXIT_FAILURE);
    }
  }
#endif
  /* Say something nice. */
  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLSinfoCount());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
