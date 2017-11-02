#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include <map>
#include <iterator>
#include <list>
using namespace llvm;
using namespace std;

namespace {
  struct SkeletonPass : public FunctionPass {
    static char ID;
    SkeletonPass() : FunctionPass(ID) {}

    struct inst {
      Instruction *instruction;
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
       insts->instruction = I;
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
       ptr->instruction = I;
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


    typedef std::map <Instruction*, int> ant;
    ant ant_in;
    ant ant_out;

    typedef std::map <Instruction*, int> avail;
    avail avail_in;
    avail avail_out;

    typedef std::map <Instruction*, int> safe;
    safe safe_in;
    safe safe_out;

    typedef std::map <Instruction*, int> spav;
    spav spav_in;
    spav spav_out;

    typedef std::map <Instruction*, int> spant;
    spant spant_in;
    spant spant_out;

    typedef std::map <int, Instruction*> numInstr;
    numInstr numToInstr;

    list<Instruction*> insertnodes;

    typedef std::map<Instruction*, Instruction*> edge;
    edge insertedges;

    list<Instruction*> replacenodes;


    void antPass(Function &F, inst *expr) {
      int c = 0;

      for(Function::iterator b = F.end(); b != F.begin(); b--) {
        BasicBlock *B = (BasicBlock*) --b;
        b++;
        for(BasicBlock::iterator i=B->end(); i != B->begin(); i--) {
          Instruction *I = (Instruction*) --i;
          i++;
          if(c == 0) {
            ant_out[I] = 0;
            ant_in[I] = antloc(I, expr) || (ant_out[I] && transp(I, expr));
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

			      ant_in[I] = (ant_out[I] && transp(I, expr)) || antloc(I, expr);
          }

          else {
            BasicBlock::iterator j = i;

			      ant_out[I] = ant_in[(Instruction*) (j)];
			      ant_in[I] = (ant_out[I] && transp(I, expr)) || antloc(I, expr);
          }
        }

      }

    }


    void availPass(Function &F, inst *expr) {
      for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
	      //BasicBlock *B = (BasicBlock*)  b;
	      //errs() << "The last instruction is " << (*--B->end()) << "\n";
	      BasicBlock *B = (BasicBlock*) b;
	      for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
		      Instruction *I = (Instruction*) i;
		      if(b==F.begin() && i==B->begin()) {
			      //errs() << I << " " << (*I) << "\n";
			      avail_in[I] = 0;
			      avail_out[I] = comp(I, expr);
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
			      avail_out[I] = (avail_in[I] && transp(I, expr)) || comp(I, expr);
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/

			      BasicBlock::iterator j = i;
			      j--;


			      avail_in[I] = avail_out[(Instruction*) (j)];
			      avail_out[I] = (avail_in[I] && transp(I, expr)) || comp(I, expr);
          /*  if(I->getOpcode()==11) {
              errs() << (*I) << "Transp " << transp(I, insts) << "comp " << comp(I, insts)<<"\n";
            }*/
		      }
	      }
      }

    }

    void safetyPass(Function &F, inst *expr) {
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

    }

    void spavPass(Function &F, inst *expr) {
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
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
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
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
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
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
			      }

		      }
	      }
      }

    }

    void spantPass(Function &F, inst *expr) {

      int c=0;

      for(Function::iterator b = F.end(); b != F.begin(); b--) {
        BasicBlock *B = (BasicBlock*) --b;
        b++;
        for(BasicBlock::iterator i=B->end(); i != B->begin(); i--) {
          Instruction *I = (Instruction*) --i;
          i++;
          if(c == 0) {
            spant_out[I] = 0;

            spant_in[I] = (antloc(I, expr) || (spant_out[I] && transp(I, expr))) && (safe_in[I]);
            c = 1;
          }

          else if(I == (Instruction *)B->getTerminator()) {
            spant_out[I] = 0;
            TerminatorInst *TInst = B->getTerminator();
            for (unsigned x = 0, NSucc = TInst->getNumSuccessors(); x < NSucc; ++x) {
              BasicBlock *Succ = TInst->getSuccessor(x);
              Instruction *firstInstruction = (Instruction*) Succ->begin();
              if(spant_in[firstInstruction] == 1) {
                spant_out[I] = 1;
                break;
              }
            }
            if(!safe_out[I])  {
              spant_out[I] = 0;
            }
            spant_in[I] = (spant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(!safe_in[I])  {
              spant_in[I] = 0;
            }
          }

          else {
            BasicBlock::iterator j = i;

            spant_out[I] = spant_in[(Instruction*) (j)];
            if(!safe_out[I])  {
              spant_out[I] = 0;
            }
            spant_in[I] = (spant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(!safe_in[I])  {
              spant_in[I] = 0;
            }

          }
        }

      }


    }

  void calculateInsertNodes(Function &F, inst *expr) {
		for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
			BasicBlock *B = (BasicBlock*) b;
			for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
				Instruction *I = (Instruction*) i;

				if(comp(I, expr) && !(spav_in[I]) && spant_out[I]) {
					insertnodes.push_back(I);
				}
			}
		}

	 }

	 void calculateInsertEdges(Function &F, inst *expr) {
  		for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
  			BasicBlock *B = (BasicBlock*) b;
  			for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
  				Instruction *I = (Instruction*) i;

  				if(I == B->getTerminator()) {
  				     TerminatorInst *TInst = B->getTerminator();
  			            for (unsigned x = 0, NSucc = TInst->getNumSuccessors(); x < NSucc; ++x) {
  				                BasicBlock *Succ = TInst->getSuccessor(x);
  			              	        Instruction *J = (Instruction*) Succ->begin();
  						if(!(spav_out[I]) && spav_in[J] && spant_in[J]) {
  							insertedges[I] = J;
  							insertedges[I] = J;
  						}
  					}
  				}

  				else {
  					Instruction* J = (Instruction*) ++i;
  					if(!(spav_out[I]) && spav_in[J] && spant_in[J]) {
  						insertedges[I] = J;
  					}
  				}
  			}
  		}

  		/*for(list<Instruction*, Instruction*>::iterator i=insertedges.begin(); i!=insertedges.end(); i++) {
  			errs() << *(i->first) << " and " << *(i->second) << "\n";
  		}*/
	 }

	void calculateReplaceNodes(Function &F, inst *expr) {
		for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
			BasicBlock *B = (BasicBlock*) b;
			for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
				Instruction *I = (Instruction*) i;
				if ((antloc(I, expr) && spav_in[I]) || (comp(I, expr) && spant_out[I]))   {
					replacenodes.push_back(I);
				}
			}
		}

  }

    void showResults(inst *expr) {
      errs() << "\n\n\nExpression : " << getVariable(expr->lhs) << " + " << getVariable(expr->rhs) << "\n";
      errs() << "\nOrder : AVIN, AVOUT, ANTIN, ANTOUT, SAFEIN, SAFEOUT, SPAVIN, SPAVOUT, SPANTIN, SPANTOUT\n\n";
      for(numInstr::iterator it = numToInstr.begin(), ite = numToInstr.end(); it != ite; it++) {
        Instruction *I;
        I = it->second;
        errs() << "-" << *I << "\t=> " << avail_in[I] << " " << avail_out[I] << " " << ant_in[I] << " " << ant_out[I] << " " << safe_in[I] << " " << safe_out[I] << " " << spav_in[I] << " "
        << spav_out[I] << " " << spant_in[I] << " " << spant_out[I] << "\n\n";
      }

      errs() << "\nThe points of insertion are:\n";
  		for(list<Instruction*>::iterator i = insertnodes.begin(); i != insertnodes.end(); i++) {
  			errs() << (**i) << "\n";
  		}

      errs() << "\nThe edges to be considered for insertion are those between\n";
  		for(edge::iterator i=insertedges.begin(), ie=insertedges.end(); i!=ie; i++) {
  			errs() << *(i->first) << " and " << *(i->second) << "\n";
  		}

      errs() << "\nThe points of replacement are:\n";
  		for(list<Instruction*>::iterator i = replacenodes.begin(); i != replacenodes.end(); i++) {
  			errs() << (**i) << "\n";
  		}

    }


    virtual bool runOnFunction(Function &F) {
      errs() << "I saw a function called " << F.getName() << "!\n";
      F.dump();
      insts = NULL;

      int num = 0;

      for(auto& B : F) {
	      errs()<< "I saw a basic block\n";
	      Instruction  *TInst = (Instruction*) B.getTerminator();
	      //errs()<< (*TInst) << "is the terminator\n";
	      //Instruction *I = (Instruction*) B.getFirstNonPHI();
	      //errs()<< (*I) << "is the first instruction\n";
	      for(auto& I : B) {

		      if(I.getOpcode() == 11) {
            inst *expr;
            expr = insts;
            int c = 0;
                  //checking duplicates and commutativity
            while(expr != NULL) {

              Instruction *lhsTest = (Instruction*)I.getOperand(0);
              Instruction *rhsTest = (Instruction*)I.getOperand(1);

              Instruction *lvarTest = (Instruction*)lhsTest->getOperand(0);
              Instruction *rvarTest = (Instruction*)rhsTest->getOperand(0);
              if((lvarTest==expr->lhs&&rvarTest==expr->rhs)||(rvarTest==expr->lhs&&lvarTest==expr->rhs)) {
                c = 1;
              }
              expr = expr->next;
            }

            if(c == 0) {
              addToInsts(&I);
            }

			    }

          numToInstr.insert(make_pair(num,&I));
          num++;

		      avail_in.insert(make_pair(&I,0));
		      avail_out.insert(make_pair(&I,0));
          ant_in.insert(make_pair(&I,0));
		      ant_out.insert(make_pair(&I,0));
          safe_in.insert(make_pair(&I,0));
		      safe_out.insert(make_pair(&I,0));

		      //only the first instruction in a basic block can have multiple predecessors
		      //Instruction *inst = (Instruction*) B.getFirstNonPHI();

	      }
      }

      inst *expr;
      expr = insts;

      while(expr != NULL) {
        availPass(F, expr);
        antPass(F, expr);
        safetyPass(F, expr);
        spavPass(F, expr);
        spantPass(F, expr);
        calculateInsertNodes(F, expr);
        calculateInsertEdges(F, expr);
        calculateReplaceNodes(F, expr);

        showResults(expr);

        expr = expr->next;
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
