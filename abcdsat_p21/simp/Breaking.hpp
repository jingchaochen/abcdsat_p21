#pragma once

#include "global.hpp"

class Permutation;
class CNF;

class Breaker {
public:
  std::unordered_set<sptr<Clause>, UVecHash, UvecEqual> clauses;
private:
  sptr<CNF> originalTheory;
  uint nbExtraVars = 0;
  uint nbBinClauses = 0;
  uint nbRowClauses = 0;
  uint nbRegClauses = 0;

  void addBinary(uint l1, uint l2);
  void addTernary(uint l1, uint l2, uint l3);
  void addQuaternary(uint l1, uint l2, uint l3, uint l4);
  void add(sptr<Clause> cl);
  void add(sptr<Permutation> perm, std::vector<uint>& order, bool limitExtraConstrs);
  void addShatter(sptr<Permutation> perm, std::vector<uint>& order, bool limitExtraConstrs);

public:
  Breaker(sptr<CNF> origTheo);

  ~Breaker() {
  };

  void print();

  void addBinClause(uint l1, uint l2);
  void addRegSym(sptr<Permutation> perm, std::vector<uint>& order);
  void addRowSym(sptr<Permutation> perm, std::vector<uint>& order);

  uint getAuxiliaryNbVars();
  uint getTotalNbVars();
  uint getAddedNbClauses();
  uint getTotalNbClauses();

  uint getNbBinClauses();
  uint getNbRowClauses();
  uint getNbRegClauses();

  uint getTseitinVar();
};
