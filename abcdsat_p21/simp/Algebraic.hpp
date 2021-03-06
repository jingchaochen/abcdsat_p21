#pragma once

#include "global.hpp"

class CNF;
class Breaker;

class Permutation : public std::enable_shared_from_this<Permutation> {
private:
  std::unordered_map<uint, uint> perm;
  std::vector<uint> cycleReprs; // smallest lit in each cycle
  uint maxCycleSize;
  size_t hash;

  

public:
  std::vector<uint> domain;
  std::vector<uint> posDomain;
  std::vector<uint> image;
  
  void addFromTo(uint from, uint to);

  Permutation();
  Permutation(std::vector<std::pair<uint, uint> >& tuples);
  // Permutation constructed from swapping two rows.
  Permutation(std::vector<uint>& row1, std::vector<uint>& row2);

  ~Permutation() {
  };

  uint getImage(uint from);
  // return value is true iff the image is different from the original
  bool getImage(std::vector<uint>& orig, std::vector<uint>& img);
  void getCycle(uint lit, std::vector<uint>& orb);
  bool isInvolution();
  bool permutes(uint lit);
  uint supportSize();
  bool isIdentity();

  void print();

  bool formsMatrixWith(sptr<Permutation> other);
  std::pair<sptr<Permutation>, sptr<Permutation> > getLargest(sptr<Permutation> other);
  void getSharedLiterals(sptr<Permutation> other, std::vector<uint>& shared);
  std::vector<uint>& getCycleReprs();
  uint getMaxCycleSize();
  uint getNbCycles();

  bool equals(sptr<Permutation> other);
};

class Matrix {
private:
  std::vector<std::vector<uint>* > rows;
  std::unordered_map<uint, uint> rowco;
  std::unordered_map<uint, uint> colco;

public:
  Matrix();
  ~Matrix();
  void print();

  void add(std::vector<uint>* row);
  uint nbColumns();
  uint nbRows();
  void tryToAddNewRow(sptr<Permutation> p, uint rowIndex, CNF* theory);
  std::vector<uint>* getRow(uint rowindex);
  bool permutes(uint x);
  uint getLit(uint row, uint column);

  uint getRowNb(uint x);
  uint getColumnNb(uint x);

  sptr<Permutation> testMembership(const sptr<Permutation> p);
  sptr<Permutation> getProductWithRowsWap(const sptr<Permutation> p, uint r1, uint r2); // return p*swap(r1,r2)
};

class Group {
private:
  std::vector<sptr<Permutation> > permutations;
  std::vector<sptr<Matrix> > matrices;
  std::unordered_set<uint> support;

  void cleanPermutations(sptr<Matrix> matrix); // remove permutations implied by the matrix
  void addMatrix(sptr<Matrix> m); // cnf-parameter, otherwise we have to store a pointer to the cnf here :(

public:
  // NOTE: if a group has a shared pointer to a theory, and a theory a shared pointer to a group, none of the memory pointed to by these pointers will ever be freed :(
  CNF* theory; // non-owning pointer

  Group() {
  };

  ~Group() {
  };

  void add(sptr<Permutation> p);
  void checkColumnInterchangeability(sptr<Matrix> m);

  void print();

  sptr<Matrix> getInitialMatrix();
  
  void addMatrices();
  uint getNbMatrices();
  uint getNbRowSwaps();

  void getDisjointGenerators(std::vector<sptr<Group> >& subgroups);
  uint getSize();

  bool permutes(uint lit);
  uint getSupportSize();

  void getOrderAndAddBinaryClausesTo(Breaker& brkr, std::vector<uint>& out_order); // returns a vector containing a lit for literals relevant to construct sym breaking clauses
  void addBinaryClausesTo(Breaker& brkr, std::vector<uint>& out_order, const std::unordered_set<uint>& excludedLits);
  void addBreakingClausesTo(Breaker& brkr);

  void maximallyExtend(sptr<Matrix> matrix, uint indexOfFirstNewRow);
};