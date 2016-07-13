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

#include "../config.h"
#include "../debug.h"

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
#include "llvm/DebugInfo.h"


using namespace llvm;

#define AFL_TMP_FILE  "/tmp/afl_tmp_file"

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      const char *getPassName() const override {
        return "American Fuzzy Lop Instrumentation";
      }
      bool getInstructionDebugInfo(const llvm::Instruction *I, 
              std::string &File,
              unsigned &Line);

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

static std::string getDSPIPath(DILocation Loc) {
  std::string dir = Loc.getDirectory();
  std::string file = Loc.getFilename();
  if (dir.empty() || file[0] == '/') {
    return file;
  } else if (*dir.rbegin() == '/') {
    return dir + file;
  } else {
    return dir + "/" + file;
  }
}

bool AFLCoverage::getInstructionDebugInfo(const llvm::Instruction *I, 
                                                   std::string &File,
                                                   unsigned &Line) {
  if (MDNode *N = I->getMetadata("dbg")) {
    DILocation Loc(N);
    File = getDSPIPath(Loc);
    Line = Loc.getLineNumber();
    return true;
  }
  else {
      File="nofilefind";
      Line = 0;
      return false;
  }

}



char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  int inst_blocks = 0;
  inst_blocks = readIndex(AFL_TMP_FILE);
  if( inst_blocks == -1 ) {
      printf("error when readIndex\n");
      exit(0);
  }
  srand(inst_blocks);


  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLBBMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_bbcov_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */
  typedef std::map<unsigned, std::set<unsigned> > BBSrcLineMapTy;
  typedef std::map<llvm::Function*, BBSrcLineMapTy> FuncBBMapTy;
  typedef std::map<std::string, FuncBBMapTy> srcBcMapTy;
  srcBcMapTy srcBcMap;


  for (auto &F : M) {
    if( F.isDeclaration() ) continue;
    //BasicBlock &entryBB = F.getEntryBlock();
    for (auto &BB : F) {

      inst_blocks++;
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (R(100) >= inst_ratio) continue;

      /* Make up cur_loc */
      unsigned int cur_loc = R(MAP_SIZE);
      printf("bbID=%d, mapID=%d, func=%s\n", inst_blocks, cur_loc, 
              F.getName().str().c_str());
      for (auto &II : BB) {
          std::string filename;
          unsigned line;
          bool bRet = getInstructionDebugInfo( &II, filename, line);
          if( bRet ) {
              printf("%s:%d\n", filename.c_str(), line);
              FuncBBMapTy  &funcBBMap = srcBcMap[filename];
              BBSrcLineMapTy &bbSrcLineMap = funcBBMap[&F];
              bbSrcLineMap[inst_blocks].insert(line);
          }

      }
      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


      /* Load BBMap SHM pointer, addbyxqx */
      LoadInst *MapBBPtr = IRB.CreateLoad(AFLBBMapPtr);
      MapBBPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      ConstantInt *CurBB = ConstantInt::get(Int32Ty, inst_blocks);
      Value *MapBBPtrIdx =
          IRB.CreateGEP(MapBBPtr,IRB.CreateZExt(CurBB, IRB.getInt32Ty()) );
      /* Update bitmap */
      LoadInst *BBCounter = IRB.CreateLoad(MapBBPtrIdx);
      BBCounter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *BBIncr = IRB.CreateAdd(BBCounter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(BBIncr, MapBBPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));


    }
  } //end for (auto F :M)

  writeIndex(AFL_TMP_FILE, inst_blocks);

  /* dump to src-id.txt */
  if( 1 ) {
    FILE *fd;
    char *file_name="src-id.txt";


    /* check the file modify time , if 10s earlier than now, clear it  */
    struct stat buf;
    fd	= fopen( file_name, "r" );
    if ( fd == NULL ) {
        fprintf ( stderr, "couldn't open file '%s'; %s\n",
                file_name, strerror(errno) );
        return -2;
    }
    fstat(fileno(fd), &buf);
    long modifyTime = buf.st_mtime;
    long curTime = time((time_t*)NULL);
    fclose(fd);

    if( curTime - modifyTime > 10) 
        fd = fopen(file_name, "w");
    else
        fd = fopen(file_name, "a+");

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

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks,
             getenv("AFL_HARDEN") ? "hardened" : "non-hardened",
             inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
