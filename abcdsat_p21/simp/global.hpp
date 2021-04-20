#pragma once

#define sptr std::shared_ptr

#include <string>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>
#include <memory>
#include <iostream>
#include <functional>
#include <time.h>

typedef unsigned int uint;

// GLOBALS:
extern uint nVars;
extern std::vector<uint> fixedLits;
extern time_t startTime;

// OPTIONS:
extern int symBreakingFormLength;
extern bool useBinaryClauses;
extern bool onlyPrintBreakers;
extern bool useMatrixDetection;
extern bool useShatterTranslation;
extern uint verbosity;
extern uint timeLim;

size_t _getHash(const std::vector<uint>& xs);
uint timeLeft();
bool timeLimitPassed();

inline bool sign(uint lit) {
  return lit & 1;
}

inline uint neg(uint lit) {
  return lit ^ 1;
}

inline uint encode(int lit) {
  return (lit > 0 ? 2 * (lit - 1) : 2 * (-lit - 1) + 1);
}

inline int decode(uint lit) {
  return (sign(lit) ? -(lit / 2 + 1) : lit / 2 + 1);
}

void gracefulError(std::string str);

class Clause {
private:
  size_t hashValue;

public:
  std::vector<uint> lits;

  Clause(const std::set<uint>& inLits) : hashValue(0), lits(inLits.cbegin(), inLits.cend()) {
  }

 
  Clause() : hashValue(0) {
  };

  ~Clause() {
  };

  std::vector<uint> & getLits() { return lits;} 
  size_t getHashValue() {
    if (hashValue == 0) {
      hashValue = _getHash(lits);
      if (hashValue == 0) {
        // avoid recalculation of hash
        hashValue = 1;
      }
    }
    return hashValue;
  }

  void print(std::ostream& ostr) {
   // if(lits.size()>40){
      for (auto lit : lits) {
        ostr << decode(lit) << " ";
      }
      ostr << "0\n";
    //}
  }
};

struct UVecHash {

  size_t operator()(const sptr<std::vector<uint> > first) const {
    return _getHash(*first);
  }

  size_t operator()(const sptr<Clause> cl) const {
    return cl->getHashValue();
  }
};

struct UvecEqual {

  bool equals(const std::vector<uint>& first, const std::vector<uint>& second) const {
    if (first.size() != second.size()) {
      return false;
    }
    for (unsigned int k = 0; k < first.size(); ++k) {
      if (first.at(k) != second.at(k)) {
        return false;
      }
    }
    return true;
  }

  bool operator()(const sptr<std::vector<uint> > first, const sptr<std::vector<uint> > second) const {
    return equals(*first, *second);
  }

  bool operator()(const sptr<Clause> first, const sptr<Clause > second) const {
    return equals(first->lits, second->lits);
  }
};

template<class T>
bool isDisjoint(std::unordered_set<T>& uset, std::vector<T>& vec) {
  for (T x : vec) {
    if (uset.count(x) > 0) {
      return false;
    }
  }
  return true;
}

template<class T>
void swapErase(std::vector<T>& vec, uint index) {
  vec[index] = vec.back();
  vec.pop_back();
}
