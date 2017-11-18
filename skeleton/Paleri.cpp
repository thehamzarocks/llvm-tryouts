#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include <map>
#include <string>
#include <iterator>
#include <list>
using namespace llvm;
using namespace std;

namespace {
  struct SkeletonPass : public FunctionPass {
    static char ID;
    SkeletonPass() : FunctionPass(ID) {}

    struct inst {
      int opCode;
      Instruction *lhs;
	    Instruction *rhs;
	    struct inst* next;
    };

    struct inst* insts;

    //takes an alloc of the form %a = alloca .. and gets a
    std::string getVariable(Instruction *I) {
  	   std::string str;
       char vName[20];
       if(ConstantInt *constInt = dyn_cast<ConstantInt> (I)) { //if operand is a constant
      		int val = constInt->getSExtValue();
          str = std::to_string(val);
          return str;
       }

  	   llvm::raw_string_ostream rso(str);
  	   I->print(rso);
  	   char var;
  	   int i,n;
  	   for(i=0; str[i]!='%';i++);
       i++;
       n = i;
       for(;str[i]!=' ';i++) {
         vName[i-n] = str[i];
       }
       vName[i-n] = '\0';
       std::string str1(vName);
  	   return str1;
    }



   void addToInsts(Instruction *I) {
	   //errs()<< *(I->getOperand(0)) << " is the lhs\n";
	   Instruction *lhs = (Instruction*)I->getOperand(0); //of the form %2= load ...
	   Instruction *rhs = (Instruction*)I->getOperand(1); //we need to get load operand

	   Instruction *lvar;
     Instruction *rvar;
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (lhs)) { //if first operand is a constant
        lvar = lhs;
    		//int val = constInt->getSExtValue();
    		//errs() << "And its value is " << val << "\n";
     }
     else {
       lvar = (Instruction*)lhs->getOperand(0);
     }
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (rhs)) { //if second operand is a constant
        rvar = rhs;
     }
     else {
       rvar = (Instruction*)rhs->getOperand(0);
     }
	   //the above is of the form %a = alloca
	   //errs()<< *lvar << " is the left variable\n";
	   if(insts == NULL) {
		   insts = new inst;
       insts->opCode=I->getOpcode();
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
       ptr->opCode=I->getOpcode();
       ptr->lhs = lvar;
		   ptr->rhs = rvar;
		   ptr->next = NULL;
	   }

   }

   //check if the expression is computed within the node without modifying any of its operands

   int comp(Instruction *i, inst* expr) {
     if(i->getOpcode() != 11 && i->getOpcode() != 13 && i->getOpcode() != 15 && i->getOpcode() != 18 && i->getOpcode() != 21 && i->getOpcode() != 26 && i->getOpcode() != 27) {
       return 0;
     }

     Instruction *lhs = (Instruction*)i->getOperand(0); //of the form %2= load ...
     Instruction *rhs = (Instruction*)i->getOperand(1); //we need to get load operand

     Instruction *lvar;
     Instruction *rvar;
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (lhs)) { //if first operand is a constant
        lvar = lhs;
     }
     else {
       lvar = (Instruction*)lhs->getOperand(0);
     }
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (rhs)) { //if second operand is a constant
        rvar = rhs;
     }
     else {
       rvar = (Instruction*)rhs->getOperand(0);
     }


    	//we've got the operands. If they match, it is locally anticipable, but we need to check if they are being modified
    	if(expr->lhs == lvar && expr->rhs == rvar) {
    		//check what the next instruction is storing
    		i = i->getNextNode();
    		Instruction *storedvar = (Instruction*) i->getOperand(1);
        //errs() << "Opcode of store is " << i->getOpcode() << "\n";
    		if(storedvar == lvar || storedvar == rvar) {
    			return 0;
    		}

        return 1;
    	}

      return 0;

   }

    int transp(Instruction *i, inst *expr) {
     if(i->getOpcode() != 11 && i->getOpcode() != 13 && i->getOpcode() != 15 && i->getOpcode() != 18 && i->getOpcode() != 21 && i->getOpcode() != 26 && i->getOpcode() != 27) {
       if(i->getOpcode() == 31) {
         Instruction *storedvar = (Instruction*) i->getOperand(1);
         if(storedvar == expr->lhs || storedvar == expr->rhs) {
           return 0;
         }
       }

   		return 1;
   	}


   	Instruction *lvar = expr->lhs;
   	Instruction *rvar = expr->rhs;


    i = i->getNextNode();
    //errs() << "The store is " << (*i) << "\n";
    Instruction *storedvar = (Instruction*) i->getOperand(1);
    //errs() << "The stored var  is " << (*storedvar) << "\n";
    if(storedvar == lvar || storedvar == rvar) {
      return 0;
    }

    return 1;
   }

   int antloc(Instruction *i, inst *expr) {
     if(i->getOpcode() != 11 && i->getOpcode() != 13 && i->getOpcode() != 15 && i->getOpcode() != 18 && i->getOpcode() != 21 && i->getOpcode() != 26 && i->getOpcode() != 27) {  //if no computation => expression not anticipated.
       return 0;
     }

     Instruction *lhs = (Instruction*) i->getOperand(0);
     Instruction *rhs = (Instruction*) i->getOperand(1);

     Instruction *lvar;
     Instruction *rvar;
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (lhs)) { //if first operand is a constant
        lvar = lhs;
        //errs() << "The lvar is " << *lvar << "\n";
     }
     else {
       lvar = (Instruction*)lhs->getOperand(0);
     }
     if(ConstantInt *constInt = dyn_cast<ConstantInt> (rhs)) { //if second operand is a constant
        rvar = rhs;
        //errs() << "The rvar is " << *rvar << "\n";
     }
     else {
       rvar = (Instruction*)rhs->getOperand(0);
     }


     //we've got the operands. If they match, it is locally anticipable

     if(expr->lhs == lvar && expr->rhs == rvar) {
       //errs() << *lvar << " " << *rvar << " " << *expr->lhs << " " << *expr->rhs << "\n";
       return 1;
     }

     return 0;
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

    int change = 0;


    void antPass(Function &F, inst *expr) {
      int c = 0;
      int prev;

      for(Function::iterator b = F.end(); b != F.begin(); b--) {
        BasicBlock *B = (BasicBlock*) --b;
        b++;
        for(BasicBlock::iterator i=B->end(); i != B->begin(); i--) {
          Instruction *I = (Instruction*) --i;
          i++;
          if(c == 0) {
            prev = ant_out[I];
            ant_out[I] = 0;
            if(prev != ant_out[I]) {
              change = 1;
            }
            prev = ant_in[I];
            ant_in[I] = antloc(I, expr) || (ant_out[I] && transp(I, expr));
            if(prev != ant_in[I]) {
              change = 1;
            }
            c = 1;
          }

          else if(I == (Instruction *)B->getTerminator()) {
            prev = ant_out[I];
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

            if(prev != ant_out[I]) {
              change = 1;
            }

            prev = ant_in[I];
			      ant_in[I] = (ant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(prev != ant_in[I]) {
              change = 1;
            }
          }

          else {
            BasicBlock::iterator j = i;

            prev = ant_out[I];
			      ant_out[I] = ant_in[(Instruction*) (j)];
            if(prev != ant_out[I]) {
              change = 1;
            }

            prev = ant_in[I];
			      ant_in[I] = (ant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(prev != ant_in[I]) {
              change = 1;
            }
          }
        }

      }

    }


    void availPass(Function &F, inst *expr) {
      int prev;

      for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
	      //BasicBlock *B = (BasicBlock*)  b;
	      //errs() << "The last instruction is " << (*--B->end()) << "\n";
	      BasicBlock *B = (BasicBlock*) b;
	      for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
		      Instruction *I = (Instruction*) i;
		      if(b==F.begin() && i==B->begin()) {
			      //errs() << I << " " << (*I) << "\n";
            prev = avail_in[I];
			      avail_in[I] = 0;
            if(prev != avail_in[I]) {
              change = 1;
            }

            prev = avail_out[I];
			      avail_out[I] = comp(I, expr);
            if(prev != avail_out[I]) {
              change = 1;
            }
		      }
		      else if(i==B->begin() && b!=F.begin()) {
            prev = avail_in[I];

			      avail_in[I] = 1;
			      for(auto it=pred_begin(B), et=pred_end(B); it!=et; ++it) {
				      BasicBlock* predecessor = *it;
				      Instruction *lastInstruction = (Instruction*) (--predecessor->end());
				      if(avail_out[lastInstruction] == 0) {
					      avail_in[I] = 0;
					      break;
				      }
			      }

            if(prev != avail_in[I]) {
              change = 1;
            }

            prev = avail_out[I];
			      avail_out[I] = (avail_in[I] && transp(I, expr)) || comp(I, expr);
            if(prev != avail_out[I]) {
              change = 1;
            }
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/

			      BasicBlock::iterator j = i;
			      j--;

            prev = avail_in[I];
			      avail_in[I] = avail_out[(Instruction*) (j)];
            if(prev != avail_in[I]) {
              change = 1;
            }

            prev = avail_out[I];
			      avail_out[I] = (avail_in[I] && transp(I, expr)) || comp(I, expr);
            if(prev != avail_out[I]) {
              change = 1;
            }
          /*  if(I->getOpcode()==11) {
              errs() << (*I) << "Transp " << transp(I, insts) << "comp " << comp(I, insts)<<"\n";
            }*/
		      }
	      }
      }

    }

    void safetyPass(Function &F, inst *expr) {
      int prev;

      for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
    		BasicBlock *B = (BasicBlock*) b;
    		for(BasicBlock::iterator i=B->begin(),ie=B->end(); i!=ie; i++) {
    			Instruction* I = (Instruction*) i;

          prev = safe_in[I];

          if(avail_in[I] == 0  && ant_in[I] == 0) {
    				safe_in[I] = 0;
    			}
    			else {
    				safe_in[I] = 1;
    			}

          if(prev != safe_in[I]) {
            change = 1;
          }


          prev = safe_out[I];
    			if(avail_out[I] == 0 &&  ant_out[I] == 0) {
    				safe_out[I] = 0;
    			}
    			else {
    				safe_out[I] = 1;
    			}

          if(prev != safe_out[I]) {
            change = 1;
          }
    		}
    	}

    }

    void spavPass(Function &F, inst *expr) {
      int prev;

      for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
	      //BasicBlock *B = (BasicBlock*)  b;
	      //errs() << "The last instruction is " << (*--B->end()) << "\n";
	      BasicBlock *B = (BasicBlock*) b;
	      for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
		      Instruction *I = (Instruction*) i;
		      if(b==F.begin() && i==B->begin()) {
			      //errs() << I << " " << (*I) << "\n";
            prev = spav_in[I];
			      spav_in[I] = 0;
            if(prev != spav_in[I]) {
              change = 1;
            }

            prev = spav_out[I];

			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
			      }

            if(prev != spav_out[I]) {
              change = 1;
            }

		      }
		      else if(i==B->begin() && b!=F.begin()) {

            prev = spav_in[I];
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

            if(prev != spav_in[I]) {
              change = 1;
            }

            prev = spav_out[I];
			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
			      }

            if(prev != spav_out[I]) {
              change = 1;
            }
		      }
		      else {
			      //avail_in[I] = avail_out[--I];
			      /*while((Instruction*) j != I) {
				      j++;
			      }*/
            prev = spav_in[I];
			      if(safe_in[I] == 0) {
				      spav_in[I] = 0;
			      }
			      else {
				      BasicBlock::iterator j = i;
				      j--;
				      spav_in[I] = spav_out[(Instruction*) j];
			      }

            if(prev != spav_in[I]) {
              change = 1;
            }

            prev = spav_out[I];
			      if(safe_out[I] == 0) {
				      spav_out[I] = 0;
			      }
			      else {
				      spav_out[I] = comp(I, expr) || (spav_in[I] && transp(I, expr));
			      }

            if(prev != spav_out[I]) {
              change = 1;
            }

		      }
	      }
      }

    }

    void spantPass(Function &F, inst *expr) {

      int c=0,prev;

      for(Function::iterator b = F.end(); b != F.begin(); b--) {
        BasicBlock *B = (BasicBlock*) --b;
        b++;
        for(BasicBlock::iterator i=B->end(); i != B->begin(); i--) {
          Instruction *I = (Instruction*) --i;
          i++;
          if(c == 0) {
            prev = spant_out[I];
            spant_out[I] = 0;

            if(prev != spant_out[I]) {
              change = 1;
            }

            prev = spant_in[I];
            spant_in[I] = (antloc(I, expr) || (spant_out[I] && transp(I, expr))) && (safe_in[I]);
            if(prev != spant_in[I]) {
              change = 1;
            }
            c = 1;
          }

          else if(I == (Instruction *)B->getTerminator()) {
            prev = spant_out[I];
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

            if(prev != spant_out[I]) {
              change = 1;
            }

            prev = spant_in[I];
            spant_in[I] = (spant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(!safe_in[I])  {
              spant_in[I] = 0;
            }

            if(prev != spant_in[I]) {
              change = 1;
            }
          }

          else {
            BasicBlock::iterator j = i;

            prev = spant_out[I];
            spant_out[I] = spant_in[(Instruction*) (j)];
            if(!safe_out[I])  {
              spant_out[I] = 0;
            }

            if(prev != spant_out[I]) {
              change = 1;
            }

            prev = spant_in[I];
            spant_in[I] = (spant_out[I] && transp(I, expr)) || antloc(I, expr);
            if(!safe_in[I])  {
              spant_in[I] = 0;
            }

            if(prev != spant_in[I]) {
              change = 1;
            }

          }
        }

      }


    }

  void findInsertNodes(Function &F, inst *expr) {
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

	 void findInsertEdges(Function &F, inst *expr) {
  		for(Function::iterator b=F.begin(), be=F.end(); b!=be; b++) {
  			BasicBlock *B = (BasicBlock*) b;
        //errs() << "The first inst is " << *(B->begin()) << "numsucc of b is" << B->getTerminator()->getNumSuccessors() << "\n";
  			for(BasicBlock::iterator i=B->begin(), ie=B->end(); i!=ie; i++) {
  				Instruction *I = (Instruction*) i;
          errs() << *I << "\n";
  				if(I == B->getTerminator()) {
  				     TerminatorInst *TInst = B->getTerminator();
  			       for (unsigned x = 0, NSucc = TInst->getNumSuccessors(); x < NSucc; ++x) {
  				        BasicBlock *Succ = TInst->getSuccessor(x);
  			          Instruction *J = (Instruction*) Succ->begin();
                  //errs() << "The instruction following " << *TInst << " is " << *J << "and the numsucc is " << NSucc <<  "\n";
                  //errs() << spav_out[I] << spav_in[J] << spant_in[J] << "\n";
                  //The last instruction is br, so we need to insert just before it
      						if(!(spav_out[I]) && spav_in[J] && spant_in[J]) {
                    BasicBlock::iterator prev = i;
                    prev--;
                    Instruction* PrevInst = (Instruction*) prev;
      							insertedges[PrevInst] = I;
      							//insertedges[I] = J;
                    errs () << "We found a point of edge insertion";

      						}
  					   }
  				}

  				else {
  					Instruction* J = (Instruction*) i;
            J++;
  					if(!(spav_out[I]) && spav_in[J] && spant_in[J]) {
  						insertedges[I] = J;
              errs () << "We found a point of edge insertion";
  					}
  				}
  			}
  		}

  		/*for(list<Instruction*, Instruction*>::iterator i=insertedges.begin(); i!=insertedges.end(); i++) {
  			errs() << *(i->first) << " and " << *(i->second) << "\n";
  		}*/
	 }

	void findReplaceNodes(Function &F, inst *expr) {
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
      char op;
      switch(expr->opCode)
      {
        case 11: op='+';
                 break;
        case 13: op='-';
                 break;
        case 15: op='*';
                 break;
        case 18: op='/';
                 break;
        case 21: op='%';
                 break;
        case 26: op='|';
                 break;
        case 27: op='&';
                 break;
        default: op='#';
                 break;
      }
      errs() << "\n\n\nExpression : " << getVariable(expr->lhs) << " " << op << " " << getVariable(expr->rhs) << "\n";
      errs() << "\nOrder : AVIN, AVOUT, ANTIN, ANTOUT, SAFEIN, SAFEOUT, SPAVIN, SPAVOUT, SPANTIN, SPANTOUT, ANTLOC, COMP, TRANSP\n\n";
      for(numInstr::iterator it = numToInstr.begin(), ite = numToInstr.end(); it != ite; it++) {
        Instruction *I;
        I = it->second;
        errs() << "-" << *I << "\t=> " << avail_in[I] << " " << avail_out[I] << " " << ant_in[I] << " " << ant_out[I] << " " << safe_in[I] << " " << safe_out[I] << " " << spav_in[I] << " "
        << spav_out[I] << " " << spant_in[I] << " " << spant_out[I] << " " << antloc(I, expr) << " " << comp(I, expr) << " " << transp(I, expr) << "\n\n";
      }

      errs() << "\nThe points of insertion are:\n";
  		for(list<Instruction*>::iterator i = insertnodes.begin(); i != insertnodes.end(); i++) {
  			errs() << (**i) << "\n";
  		}

      errs() << "\nThe edges to be considered for insertion are those between:\n";
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
          //opCode add =11, sub= 13, multiply= 15, div = 18, percent = 21, bitwiseAnd = 26, bitwiseOr =27

		      if(I.getOpcode() == 11||I.getOpcode() == 13||I.getOpcode() == 15||I.getOpcode() == 18||I.getOpcode() == 21||I.getOpcode() == 26||I.getOpcode() == 27) {
            inst *expr;
            expr = insts;
            int c = 0;
            //checking duplicates and commutativity
            while(expr != NULL) {
              Instruction *lhsTest = (Instruction*)I.getOperand(0);
              Instruction *rhsTest = (Instruction*)I.getOperand(1);
              Instruction *lvarTest;
              Instruction *rvarTest;
              if(ConstantInt *constInt = dyn_cast<ConstantInt> (lhsTest)) { //if first operand is a constant
                 lvarTest = lhsTest;
              }
              else {
                lvarTest = (Instruction*)lhsTest->getOperand(0);
              }
              if(ConstantInt *constInt = dyn_cast<ConstantInt> (rhsTest)) { //if second operand is a constant
                 rvarTest = rhsTest;
              }
              else {
                rvarTest = (Instruction*)rhsTest->getOperand(0);
              }
              if(lvarTest==expr->lhs&&rvarTest==expr->rhs&&expr->opCode==I.getOpcode()) {
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
        do {
          change = 0;

          availPass(F, expr);
          antPass(F, expr);
          safetyPass(F, expr);
          spavPass(F, expr);
          spantPass(F, expr);

        } while(change == 1);

        findInsertNodes(F, expr);
        findInsertEdges(F, expr);
        findReplaceNodes(F, expr);

        showResults(expr);

        insertnodes.clear();
        replacenodes.clear();
        insertedges.clear();

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
