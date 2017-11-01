#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/BasicBlock.h"
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
		   insts->lhs = lvar;
		   insts->rhs = rvar;
		   insts->next = NULL;
	   }
	   else if(insts != NULL) {
		   inst* ptr = insts;
		   while(ptr->next != NULL) {
			   ptr = ptr->next;
		   }
		   ptr->next = new inst;
		   ptr = ptr->next;
		   ptr->lhs = lvar;
		   ptr->rhs = rvar;
		   ptr->next = NULL;
	   }

   }

   //check if the expression is computed within the node without modifying any of its operands

   bool comp(Instruction *i, inst* expr) {
	if(i->getOpcode() != 11) {
		return false;
	}

	Instruction *lhs = (Instruction*) i->getOperand(0);
	Instruction *rhs = (Instruction*) i->getOperand(1);

	Instruction *lvar = (Instruction*)lhs->getOperand(0);
	Instruction *rvar = (Instruction*)rhs->getOperand(0);


	//we've got the operands. If they match, it is locally anticipable, but we need to check if they are being modified
	if(expr->lhs == lvar && expr->rhs == rvar) {
		//check what the next instruction is storing
		i = i->getNextNode();
		Instruction *storedvar = (Instruction*) i->getOperand(0);
		if(storedvar == lvar || storedvar == rvar) {
			return false;
		}
		return true;
	}



   }




    typedef std::map <Instruction*, int> avail;
    avail avail_in;
    avail avail_out;
    avail::iterator it;


    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      insts = NULL;

      Instruction *adder = NULL;
      //return false;
      for(auto& B : F) {
	      errs()<< "I saw a basic block\n";
	      Instruction  *TInst = (Instruction*) B.getTerminator();
	      //errs()<< (*TInst) << "is the terminator\n";
	      //Instruction *I = (Instruction*) B.getFirstNonPHI();
	      //errs()<< (*I) << "is the first instruction\n";
	      for(auto& I : B) {

		      if(I.getOpcode() == 11) {
     				addToInsts(&I);
			}			

		      avail_in.insert(make_pair(&I,0));
		      avail_out.insert(make_pair(&I,0));

		      //only the first instruction in a basic block can have multiple predecessors
		      Instruction *inst = (Instruction*) B.getFirstNonPHI();
		
	      }	      
      }

      for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
	      //BasicBlock *B = (BasicBlock*)  b;
	      //errs() << "The last instruction is " << (*--B->end()) << "\n";
	      BasicBlock *B = (BasicBlock*) b;
	      for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
		      Instruction *I = (Instruction*) i;
		      if(b==F.begin() && i==B->begin()) {
			      //errs() << I << " " << (*I) << "\n";
			      avail_in[I] = 0;
			      avail_out[I] = comp(I, insts);
		      }
		      else if(i==B->begin() && b!=F.begin()) {
			      avail_in[I] = 1;
			      for(auto it=pred_begin(B), et=pred_end(B); it!=et; ++it) {
				      BasicBlock* predecessor = *it;
				      Instruction *lastInstruction = (Instruction*) (--predecessor->end());
				      if(avail_out[lastInstruction] == 0) {
					      avail_in[I] = 0;
					      break;
				      }
			      }
			      avail_out[I] = avail_in[I] || comp(I, insts);
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/

			      BasicBlock::iterator j = i;
			      j--;

			      
			      avail_in[I] = avail_out[(Instruction*) (j)]; //this is wrong. Instruction order in the map differs from the actual instruction order
			      avail_out[I] = avail_in[I] || comp(I, insts);
		      }
	      }
      }

      errs() << "Ins\n";
	for(avail::iterator it = avail_in.begin(), ite=avail_in.end(); it!=ite; it++) {
	      errs() << "-" <<  *(it->first)  << " " << it->second <<  "\n";
      }

	errs() << "Outs\n";

      for(avail::iterator it = avail_out.begin(), ite=avail_out.end(); it!=ite; it++) {
	      errs() << "-" <<  *(it->first)  << " " << it->second <<  "\n";
      }





      for(avail::iterator it=avail_in.begin(), ite=avail_in.end(); it!=ite; it++) {
	      
	      //errs() << (*it->first) << " has avail_in " << it->second << "\n";
      }

	      //for(BasicBlock::iterator i=b.begin(), ie=b.end(); i!=ie; i++) {


      /*inst* ptr = insts;
      while(ptr != NULL) {
	      for(auto& B : F) {
		      for(BasicBlock::iterator i = B.begin(), ie=B.end(); i!=ie;  ++i) {
			      errs() << "Iterating through instructions\n";
		      }
		      
		      Function::iterator b = F.begin();
		      Instruction *i = (Instruction*) B.getFirstNonPHI();
		      //the very first instruction. Available is 0 at the start
		      if(&B == b) {
			      avail_in[i] = 0;
			      avail_out[i] = comp(i, ptr);
		      	    
	     		      //errs()<<*(inst->getNextNode()) << "is the second instruction\n";
		      }
		      while(i != NULL) {
			      avail_in[i->getNextNode()] = avail_out[i]; //could use an iterator here?

			      
		      }
		     
		     		
	      }

      }*/
      
      
      for (it = avail_in.begin(); it != avail_in.end(); ++it) {
	      //errs()<< it->first << " " << it->second << "\n";
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
