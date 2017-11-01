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
	    struct inst* next;
    };

    struct inst* insts;

    //takes an alloc of the form %a = alloca .. and gets a
   char getVariable(Instruction *I) {
	   std::string str;
	   llvm::raw_string_ostream rso(str);
	   I->print(rso);
	   char var;
	   int i;
	   for(i=0; str[i]!='%';i++);
	   return str[i+1];
   }

   void addToInsts(Instruction *I) {
	   //errs()<< *(I->getOperand(0)) << " is the lhs\n";
	   Instruction *lhs = (Instruction*)I->getOperand(0); //of the form %2= load ...
	   Instruction *rhs = (Instruction*)I->getOperand(1); //we need to get load operand

	   Instruction *lvar = (Instruction*)lhs->getOperand(0); 
	   Instruction *rvar = (Instruction*)rhs->getOperand(0);
	   //the above is of the form %a = alloca
	   //errs()<< *lvar << " is the left variable\n";
	   if(insts == NULL) {
		   insts = new inst;
		   insts->lhs = getVariable(lvar);
		   insts->rhs = getVariable(rvar);
		   insts->next = NULL;
	   }
	   else if(insts != NULL) {
		   inst* temp = new inst;
		   temp->lhs = getVariable(lvar);
		   temp->rhs = getVariable(rvar);
		   temp->next = insts;
		   insts = temp;
	   }

   }
   
   
    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      insts = NULL;
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



		      }
		      if(I.getOpcode() == 11) {//add
			      Instruction *lhs = (Instruction*) I.getOperand(0); //I is add
			      Instruction *lload = (Instruction*) lhs->getOperand(0); //lhs is load
			      errs() << (*lload) << " is the variable\n";
			      addToInsts(&I);
		      }
		      if(I.getOpcode() == 30) { //load
		      }



	      }
      }	
      /*inst* first = insts;
      while(first->next != NULL) {
	      inst* check = first->next;
	      while(check != NULL) {
		      if(check->lhs == first->lhs && check->rhs == first->rhs) {
			      errs()<<first->lhs <<" + "<< first->rhs << " is redundant\n";
			      break;
		      }
		      check = check->next;
	      }
		      first = first->next;
     }*/
     
      
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
