#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include <map>
#include <iterator>
using namespace llvm;
using namespace std;

namespace {
  struct SkeletonPass : public FunctionPass {
    static char ID;
    SkeletonPass() : FunctionPass(ID) {}


    struct inst {
	    Instruction *lhs;
	    Instruction *rhs;
	    struct inst* next, *prev;
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
		   insts->lhs = lvar;
		   insts->rhs = rvar;
		   insts->next = NULL;
       insts->prev = NULL;
	   }
	   else {
		   inst* ptr = insts;
		   while(ptr->next != NULL) {
			   ptr = ptr->next;
		   }
		   ptr->next = new inst;
       (ptr->next)->prev = ptr;
		   ptr = ptr->next;
		   ptr->lhs = lvar;
		   ptr->rhs = rvar;
		   ptr->next = NULL;
	   }

   }

    typedef std::map <Instruction*, int> ant;
    ant ant_in;
    ant ant_out;
    ant::iterator it;

    bool transp(Instruction *i, inst *expr) {
      if(i->getOpcode() != 11) {  //if no computation, it is transp
    		return true;
    	}
      //if a computation is being performed
    	Instruction *lvar = expr->lhs;
    	Instruction *rvar = expr->rhs;

      i = i->getNextNode(); //see what is being modified
      Instruction *storedvar = (Instruction*) i->getOperand(0);
      //check if the store instruction is done on a variable of the expression
      if(storedvar == lvar || storedvar == rvar) {
        return false;
      }

      return true;
    }

    bool antloc(Instruction *i, int *expr) {
      if(i->getOpcode() != 11) {  //if no computation => expression not anticipated.
    		return false;
    	}

    	Instruction *lhs = (Instruction*) i->getOperand(0);
    	Instruction *rhs = (Instruction*) i->getOperand(1);

    	Instruction *lvar = (Instruction*)lhs->getOperand(0);
    	Instruction *rvar = (Instruction*)rhs->getOperand(0);


    	//we've got the operands. If they match, it is locally anticipable
    	if(expr->lhs == lvar && expr->rhs == rvar) {
    		return true;
    	}

      return false; 
    }


    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      //return false;
      for(auto& B : F) {
	      errs()<< "I saw a basic block\n";

        //Instruction *I = (Instruction*) B.getFirstNonPHI();
        //errs()<< I->getOpcodeName() << " is the first instruction\n";
	      //Instruction  *TInst = (Instruction*) B.getTerminator();
	      //errs()<< TInst->getOpcodeName() << " is the terminator\n";
        for(auto& I : B) {

		      if(I.getOpcode() == 11) {
     				addToInsts(&I);
			    }

		      ant_in.insert(make_pair(&I,0));
		      ant_out.insert(make_pair(&I,0));

		      //only the first instruction in a basic block can have multiple predecessors
		      Instruction *inst = (Instruction*) B.getFirstNonPHI();

	      }

      }

      for (it = ant_in.begin(); it != ant_in.end(); ++it) {
        errs()<< it->first->getOpcodeName() << " " << it->second << "\n";
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
