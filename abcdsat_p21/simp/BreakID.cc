#include <fstream>
#include <sstream>
#include <iterator>

#include "Graph.hpp"
#include "global.hpp"
#include "Algebraic.hpp"
#include "CNFtheory.hpp"
#include "Breaking.hpp"

using namespace std;

// ==== main
int breakID_main(abcdSAT::Solver* solver) 
{
  time(&startTime);

  sptr<CNF> theory = make_shared<CNF>(solver);

  if (verbosity > 3) theory->getGraph()->print();

  if (verbosity > 0) {
    std::clog << "c **** symmetry generators detected: " << theory->getGroup()->getSize() << std::endl;
    if (verbosity > 2) {
      theory->getGroup()->print();
    }
    std::clog << "c *** Detecting subgroups..." << std::endl;
  }
  vector<sptr<Group> > subgroups;
  theory->getGroup()->getDisjointGenerators(subgroups);
  if (verbosity > 0) {
    std::clog << "c **** subgroups detected: " << subgroups.size() << std::endl;
  }

  if (verbosity > 1) {
    for (auto grp : subgroups) {
      std::clog << "c group size: " << grp->getSize() << " support: " << grp->getSupportSize() << std::endl;
      if (verbosity > 2) {
        grp->print();
      }
    }
  }
  
  theory->cleanUp(); // improve some memory overhead
  
  uint totalNbMatrices = 0;
  uint totalNbRowSwaps = 0;
  
  Breaker brkr(theory);
//  std::clog << "c useMatrixDetection=" <<useMatrixDetection<< std::endl;
//  getchar();
   
  for (auto grp : subgroups) {
    if (grp->getSize() > 1 && useMatrixDetection) {
      if (verbosity > 1) {
        std::clog << "c *** Detecting row interchangeability..." << std::endl;
      }
      theory->setSubCNF(grp);
      grp->addMatrices();
      totalNbMatrices += grp->getNbMatrices();
      totalNbRowSwaps += grp->getNbRowSwaps();
    }
    if (verbosity > 1) {
      std::clog << "c *** Constructing symmetry breaking formula..." << std::endl;
    }
    grp->addBreakingClausesTo(brkr);
    grp.reset();
  }
  
  if (verbosity > 0) {
    std::clog << "c **** matrices detected: " << totalNbMatrices << std::endl;
    std::clog << "c **** row swaps detected: " << totalNbRowSwaps << std::endl;
    std::clog << "c **** extra binary symmetry breaking clauses added: " << brkr.getNbBinClauses() << "\n";
    std::clog << "c **** regular symmetry breaking clauses added: " << brkr.getNbRegClauses() << "\n";
    std::clog << "c **** row interchangeability breaking clauses added: " << brkr.getNbRowClauses() << "\n";
    std::clog << "c **** total symmetry breaking clauses added: " << brkr.getAddedNbClauses() << "\n";
    std::clog << "c **** auxiliary variables introduced: " << brkr.getAuxiliaryNbVars() << "\n";
    std::clog << "c *** Printing resulting CNF with symmetry breaking clauses..." << std::endl;
  }
 // cout << endl;
  abcdSAT::vec < abcdSAT:: Lit> ps;
  for (auto c : brkr.clauses) {
     vector<uint> & lits=c->getLits();
     ps.clear();
     for (auto lit : lits) {
         int Vn=lit/2+1;
         while (Vn > solver->nVars()) solver->newVar();
         ps.push(abcdSAT::toLit(lit));
     }
     solver->addClause_(ps);
  }
  return 0;
}
