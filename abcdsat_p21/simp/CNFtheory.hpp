#pragma once

#include "global.hpp"
#include "core/Solver.h"

//using namespace abcdSAT;

class Graph;
class Permutation;
class Group;
class Matrix;
class Breaker;

class CNF {
  friend class Breaker;

private:
  std::unordered_set<sptr<Clause>, UVecHash, UvecEqual> clauses; // must be an unordered_set, since we need to be able to test whether a clause exists to detect symmetries
  sptr<Graph> graph;
  sptr<Group> group;

  void readCNF(abcdSAT::Solver* solver);

public:
  CNF(abcdSAT::Solver* solver);
  CNF(std::vector<sptr<Clause> >& clss, sptr<Group> grp);
  ~CNF();

  void print();
  uint getSize();

  sptr<Graph> getGraph();
  sptr<Group> getGroup();
  void setSubCNF(sptr<Group> subgroup);
  
  void cleanUp();

  bool isSymmetry(Permutation& prm);
};
