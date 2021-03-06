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
		Instruction *storedvar = (Instruction*) i->getOperand(1);
		if(storedvar == lvar || storedvar == rvar) {
			return false;
		}
		return true;
	}



   }

    bool antloc(Instruction *i, inst *expr) {
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


   bool transp(Instruction *i, inst *expr) {
     if(i->getOpcode() != 11) {
   		return true;
   	}


   	Instruction *lvar = expr->lhs;
   	Instruction *rvar = expr->rhs;


    i = i->getNextNode();
    //errs() << "The store is " << (*i) << "\n";
    Instruction *storedvar = (Instruction*) i->getOperand(1);
    //errs() << "The stored var  is " << (*storedvar) << "\n";
    if(storedvar == lvar || storedvar == rvar) {
      return false;
    }

    return true;
   }




    typedef std::map <Instruction*, int> avail;
    avail avail_in;
    avail avail_out;
    //avail::iterator it;

    typedef std::map <Instruction*, int> ant;
    ant ant_in;
    ant ant_out;
    //ant::iterator it;

    typedef std::map <Instruction*, int> safe;
    safe safe_in;
    safe safe_out;

    typedef std::map <Instruction*, int> spav;
    spav spav_in;
    spav spav_out;

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

	//Availability

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
			      avail_out[I] = (avail_in[I] && transp(I, insts)) || comp(I, insts);
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/

			      BasicBlock::iterator j = i;
			      j--;


			      avail_in[I] = avail_out[(Instruction*) (j)]; //this is wrong. Instruction order in the map differs from the actual instruction order
			      avail_out[I] = (avail_in[I] && transp(I, insts)) || comp(I, insts);
          /*  if(I->getOpcode()==11) {
              errs() << (*I) << "Transp " << transp(I, insts) << "comp " << comp(I, insts)<<"\n";
            }*/
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

	//Anticipability
	int c = 0;

      for(Function::iterator b = F.end(); b != F.begin(); b--) {
        BasicBlock *B = (BasicBlock*) --b;
        b++;
        for(BasicBlock::iterator i=B->end(); i != B->begin(); i--) {
          Instruction *I = (Instruction*) --i;
          i++;
          if(c == 0) {
            ant_out[I] = 0;
            ant_in[I] = antloc(I, insts) || (ant_out[I] && transp(I, insts));
            c = 1;
          }

          else if(I == (Instruction *)B->getTerminator()) {
            ant_out[I] = 1;
            TerminatorInst *TInst = B->getTerminator();
            for (unsigned x = 0, NSucc = TInst->getNumSuccessors(); x < NSucc; ++x) {
              BasicBlock *Succ = TInst->getSuccessor(x);
              Instruction *firstInstruction = (Instruction*) Succ->begin();
				      if(ant_in[firstInstruction] == 0) {
					      ant_out[I] = 0;
					      break;
				      }
            }

			      ant_in[I] = (ant_out[I] && transp(I, insts)) || antloc(I, insts);
          }

          else {
            BasicBlock::iterator j = i;

			      ant_out[I] = ant_in[(Instruction*) (j)];
			      ant_in[I] = (ant_out[I] && transp(I, insts)) || antloc(I, insts);
          }
        }

      }

      errs() << "Outs\n";

      for(ant::iterator it = ant_out.begin(), ite=ant_out.end(); it!=ite; it++) {
	      errs() << "-" <<  *(it->first)  << " " << it->second <<  "\n";
      }

      errs() << "Ins\n";
	    for(ant::iterator it = ant_in.begin(), ite=ant_in.end(); it!=ite; it++) {
	      errs() << "-" <<  *(it->first)  << " " << it->second <<  "\n";
      }

	//safety
	for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
		BasicBlock *B = (BasicBlock*) b;
		for(BasicBlock::iterator i=B->begin(),ie=B->end(); i!=ie; i++) {
			Instruction* I = (Instruction*) i;
			if(avail_in[I] == 0  && ant_in[I] == 0) {
				safe_in[I] = 0;
			}
			else {
				safe_in[I] = 1;
			}

			if(avail_out[I] == 0 &&  ant_out[I] == 0) {
				safe_out[I] = 0;
			}
			else {
				safe_out[I] = 1;
			}
		}
	}

	errs() << "Safe in and out\n";
	for(safe::iterator it=safe_in.begin(), ite=safe_in.end(); it!=ite; it++) {
		errs() << (*it->first) << " " << it->second << "\n";
	}

	for(safe::iterator it=safe_out.begin(), ite=safe_out.end(); it!=ite; it++) {
		errs() << (*it->first) << " " << it->second << "\n";
	}

	//Safe Partial Availability

	for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
	      //BasicBlock *B = (BasicBlock*)  b;
	      //errs() << "The last instruction is " << (*--B->end()) << "\n";
	      BasicBlock *B = (BasicBlock*) b;
	      for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
		      Instruction *I = (Instruction*) i;
		      if(b==F.begin() && i==B->begin()) {
			      //errs() << I << " " << (*I) << "\n";
			      
			      spav_in[I] = 0;

			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, insts) || (spav_in[I] && transp(I, insts));
			      }			      
			      
		      }
		      else if(i==B->begin() && b!=F.begin()) {

			      if(safe_in[I] == 0) {
				      spav_in[I] = 0;
			      }
			      else {
				      spav_in[I] = 0;
				      for(auto it=pred_begin(B), et=pred_end(B); it!=et; ++it) {
					      BasicBlock *predecessor = *it;
					      Instruction *lastInstruction = (Instruction*) (--predecessor->end());
					      if(avail_out[lastInstruction] == 1) {
						      spav_in[I] = 1;
						      break;
					      }
				      }
			      }

			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, insts) || (spav_in[I] && transp(I, insts));
			      }
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/

			      if(safe_in[I] == 0) {
				      spav_in[I] = 0;
			      }
			      else {
				      BasicBlock::iterator j = i;
				      j--;
				      spav_in[I] = spav_out[(Instruction*) j];
			      }

			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, insts) || (spav_in[I] && transp(I, insts));
			      }

		      }
	      }
      }

	//spav in
	//
	errs() << "spav in\n";
	for(safe::iterator it=spav_in.begin(), ite=spav_in.end(); it!=ite; it++) {
		errs() << (*it->first) << " " << it->second << "\n";
	}

	//spav out
	//
	errs() << "spav out\n";

	for(safe::iterator it=spav_out.begin(), ite=spav_out.end(); it!=ite; it++) {
		errs() << (*it->first) << " " << it->second << "\n";
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
