#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include <map>
#include <iterator>
using namespace llvm;
using namespace std;

namespace {
  struct SkeletonPass : public FunctionPass {
    static char ID;
    SkeletonPass() : FunctionPass(ID) {}


    struct node {
	    Instruction *I;
	    int ant;
    };

    node *graph;

    typedef std::map <Instruction*, int> ant;
    ant ant_in;
    ant ant_out;
    ant::iterator it;


    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      graph = NULL;
      node *ptr = graph;
      //return false;
      for(auto& B : F) {
	      errs()<< "I saw a basic block\n";
        //Instruction *I = (Instruction*) B.getFirstNonPHI();
        //errs()<< I->getOpcodeName() << " is the first instruction\n";
	      //Instruction  *TInst = (Instruction*) B.getTerminator();
	      //errs()<< TInst->getOpcodeName() << " is the terminator\n";
	      for(auto& I : B) {
		      ant_in.insert(make_pair(&I,0));
	      }
	      for (it = ant_in.begin(); it != ant_in.end(); ++it) {
		      errs()<< it->first->getOpcodeName() << " " << it->second << "\n";
	      }

      }

      return false;
    }
  };
}

char SkeletonPass::ID = 0;

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
static void registerSkeletonPass(const PassManagerBuilder &,
                         legacy::PassManagerBase &PM) {
  PM.add(new SkeletonPass());
}
static RegisterStandardPasses
  RegisterMyPass(PassManagerBuilder::EP_EarlyAsPossible,
                 registerSkeletonPass);
