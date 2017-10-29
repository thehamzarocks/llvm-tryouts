#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
using namespace llvm;

namespace {

  struct SkeletonPass : public FunctionPass {
    static char ID;
    SkeletonPass() : FunctionPass(ID) {}

    struct inst {
	    char lhs;
	    char rhs;
	    struct node* next;
    };

    struct inst* insts;

    getVariable(

    addToInsts(auto* op) {
	    if(insts == NULL) {
		    insts = new node;
		    insts->lhs = getVariable(op->getOperand(0));
		    insts->rhs = getVariable(op->getOperand(1));
	    }
    }

   
    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      insts = (inst*) malloc(sizeof(struct inst));
      //return false;
      for(auto& B : F) {
	      for(auto& I : B) {
		      errs()<< I.getOpcode() <<"\n";
		      if(auto* op = dyn_cast<BinaryOperator>(&I)) {
			      /*IRBuilder<> builder(op);
			      Value *lhs = op->getOperand(0);
			      Value *rhs = op->getOperand(1);
			      Value *mul = builder.CreateAdd(lhs, rhs);
			      errs()<< *op <<"is the binary instruction\n";
			      errs()<< *mul << " is the op built\n";
			      errs()<< *(lhs) << "along with "<< *(rhs) << "\n";*/

			      addToInsts(op);


		      }
		      if(I.getOpcode() == 30) { //load
			      errs()<< "load found\n";
			      errs()<< *(I.getOperand(0)) << " is the variable\n";
		      }



	      }      
      }
      
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
