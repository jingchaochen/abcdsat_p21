#include "CNFtheory.hpp"
#include <fstream>
#include <sstream>
#include <iterator>
#include <iostream>
#include <algorithm>
#include <bitset>
#include "Graph.hpp"
#include "Algebraic.hpp"
#include "Breaking.hpp"

//=========================CNF==================================================

using namespace std;

void CNF::readCNF(abcdSAT::Solver * solver) 
{
   if (verbosity > 0)  std::clog << "*** Reading CNF from a solver " << std::endl;
   set<uint> inclause = set<uint>();
   abcdSAT:: vec< abcdSAT:: CRef > & cs = solver->clauses;
   nVars=0;
   clauses.reserve(cs.size());
   for (int i=0; i < cs.size(); i++){
        abcdSAT:: Clause & c = solver->ca[cs[i]];
 	int sz=c.size();
        inclause.clear();
        for (int j = 0; j < sz; j++) {
	      abcdSAT:: Lit p=c[j];
              uint l2=toInt(p);
              if (l2 > nVars) nVars = l2;
              inclause.insert(l2);
       //       if(disp>0) printf("%d ",toIntLit(p));
             // int e2=encode(toIntLit(p));
             // if(l2!=e2){
             //       printf("<l2=%d e2=%d",l2,e2);
             //       getchar();
             // }
        }
      //  if(disp>0){
        //      disp--;
       // }
        sptr<Clause> cl(new Clause(inclause));
        clauses.insert(cl);
   }
   nVars = nVars/2+1;
}


CNF::CNF(abcdSAT::Solver * solver) {
  readCNF(solver);
  if (verbosity > 0) {
    std::clog << "c *** Creating first graph..." << std::endl;
  }
  graph = make_shared<Graph>(clauses);
  group = make_shared<Group>();
  if (verbosity > 0) {
    std::clog << "c *** Detecting symmetry group..." << std::endl;
  }
  std::vector<sptr<Permutation> > symgens;
  graph->getSymmetryGenerators(symgens);
  for (auto symgen : symgens) {
    group->add(symgen);
  }
}

CNF::CNF(std::vector<sptr<Clause> >& clss, sptr<Group> grp) {
  clauses.insert(clss.cbegin(), clss.cend());
  graph = make_shared<Graph>(clauses);
  group = grp;
  for (uint l = 0; l < 2 * nVars; ++l) {
    if (not grp->permutes(l)) {
      graph->setUniqueColor(l);
    }
  }
}

CNF::~CNF() {
}

void CNF::print() {
  std::clog << "p cnf " << nVars << " " << clauses.size() << "\n";
  for (auto clause : clauses) {
    clause->print(std::clog);
  }
}

uint CNF::getSize() {
  return clauses.size();
}

void CNF::setSubCNF(sptr<Group> subgroup) {
  std::vector<sptr<Clause> > subclauses;
  for (auto cl : clauses) {
    for (auto lit : cl->lits) {
      if (subgroup->permutes(lit)) {
        subclauses.push_back(cl);
        break;
      }
    }
  }
  subgroup->theory = new CNF(subclauses, subgroup);
}

void CNF::cleanUp(){
  graph.reset();
  group.reset();
}

sptr<Graph> CNF::getGraph() {
  return graph;
}

sptr<Group> CNF::getGroup() {
  return group;
}

bool CNF::isSymmetry(Permutation& prm) {
  for (auto cl : clauses) {
    sptr<Clause> symmetrical(new Clause());
    if (!prm.getImage(cl->lits, symmetrical->lits)) {
      continue;
    }
    std::sort(symmetrical->lits.begin(), symmetrical->lits.end());
    if (clauses.count(symmetrical) == 0) {
      return false;
    }
  }
  return true;
}
