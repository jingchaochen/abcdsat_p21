#include "Breaking.hpp"
#include "Algebraic.hpp"
#include "CNFtheory.hpp"
#include "global.hpp"

Breaker::Breaker(sptr<CNF> origTheo) : originalTheory(origTheo) {
}

void Breaker::print() {
  std::cout << "c number of breaking clauses added: " << getAddedNbClauses() << "\n";
  std::cout << "c max original variable: " << nVars << "\n";
  onlyPrintBreakers=1;
  std::cout << "c onlyPrintBreakers: " << onlyPrintBreakers << "\n";
  if(not onlyPrintBreakers){
    std::cout << "p cnf " << getTotalNbVars() << " " << getTotalNbClauses() << "\n";
    for (auto c : originalTheory->clauses) {
          c->print(std::cout);
    }
  } else{
    std::cout << "c auxiliary variables: " << getAuxiliaryNbVars() << "\n";
  }
  for (auto c : clauses) {
    c->print(std::cout);
  }
}

void Breaker::add(sptr<Clause> cl) {
  clauses.insert(cl);
}

void Breaker::addBinary(uint l1, uint l2) {
  sptr<Clause> toAdd(new Clause());
  toAdd->lits.push_back(l1);
  toAdd->lits.push_back(l2);
  add(toAdd);
}

void Breaker::addTernary(uint l1, uint l2, uint l3) {
  sptr<Clause> toAdd(new Clause());
  toAdd->lits.push_back(l1);
  toAdd->lits.push_back(l2);
  toAdd->lits.push_back(l3);
  add(toAdd);
}

void Breaker::addQuaternary(uint l1, uint l2, uint l3, uint l4) {
  sptr<Clause> toAdd(new Clause());
  toAdd->lits.push_back(l1);
  toAdd->lits.push_back(l2);
  toAdd->lits.push_back(l3);
  toAdd->lits.push_back(l4);
  add(toAdd);
}

void Breaker::addBinClause(uint l1, uint l2) {
  ++nbBinClauses;
  addBinary(l1, l2);
}

void Breaker::addRegSym(sptr<Permutation> perm, std::vector<uint>& order) {
  uint current = getTotalNbClauses();

//  std::clog << "c useShatterTranslation= " << useShatterTranslation << std::endl;

  if(useShatterTranslation){
    addShatter(perm, order, true);
  }else{
    add(perm, order, true);
  }
  nbRegClauses += getTotalNbClauses() - current;
}

void Breaker::addRowSym(sptr<Permutation> perm, std::vector<uint>& order) {
  uint current = getTotalNbClauses();
  if(useShatterTranslation){
    addShatter(perm, order, false);
  }else{
    add(perm, order, false);
  }
  nbRowClauses += getTotalNbClauses() - current;
}

void Breaker::add(sptr<Permutation> perm, std::vector<uint>& order, bool limitExtraConstrs) {
  std::unordered_set<uint> allowedLits; // which are not the last lit in their cycle, unless they map to their negation
  // std::clog << "order" <<std::endl;
  for (uint i = order.size(); i > 0; --i) {
    uint lit = order.at(i - 1);

    if (allowedLits.count(lit) == 0) { // we have a last lit of a cycle
      uint sym = perm->getImage(lit);
     // int xy=lit/2+1;
    //  std::clog << "\n(lit="<<xy/20<<' '<<xy%20<<')';
    //  xy=sym/2+1;
    //  std::clog << '('<<xy/20<<' '<<xy%20<<')';
    while (sym != lit) { // add the other lits of the cycle and the negated cycle
        allowedLits.insert(sym);
        allowedLits.insert(neg(sym));
        sym = perm->getImage(sym);
  //      int xy=sym/2+1;
  //      std::clog << '('<<xy/20<<' '<<xy%20<<')';
     }
    }
  }

  int nrExtraConstrs = 0;
  uint prevLit = 0;
  uint prevSym = 0;
  uint prevTst = 0; // previous tseitin
  //int k=0;
  for (auto l : order) {
    uint sym = perm->getImage(l);
    if (sym != l && allowedLits.count(l)) {
     //   int xy=sym/2+1;
      //  std::clog << '('<<k++<<' '<<xy<<" l="<<l<<')';
    }
  }
//  getchar();
  for (auto l : order) {
    if (limitExtraConstrs && nrExtraConstrs > symBreakingFormLength) {
      break;
    }
    uint sym = perm->getImage(l);
    if (sym != l && allowedLits.count(l)) {
  //      int xy=sym/2+1;
       // std::clog << '('<<k++<<' '<<xy/20<<' '<<xy%20<<')';
    //    std::clog << '('<<k++<<' '<<xy<<')';
      uint tst = 0;
      if (nrExtraConstrs == 0) {
        // adding clause for l => sym : sym = pi(l)
        // ~l | sym
        addBinary(neg(l), sym);
      } else if (nrExtraConstrs == 1) {
        // adding clauses for (prevSym => prevLit) => tst and tst => (l => sym)
        tst = getTseitinVar();
        // prevSym | tst
        addBinary(prevSym, tst);
        // ~prevLit | tst
        addBinary(neg(prevLit), tst);
        // ~tst | ~l | sym
        addTernary(neg(tst), neg(l), sym);
      } else {
        // adding clauses for (prevSym => prevLit) & prevTst => tst and tst => (l => sym)
        tst = getTseitinVar();
        // prevSym | ~prevTst | tst 
        addTernary(prevSym, neg(prevTst), tst);
        // ~prevLit | ~prevTst | tst
        addTernary(neg(prevLit), neg(prevTst), tst);
        // ~tst | ~l | sym
        addTernary(neg(tst), neg(l), sym);
      }
      ++nrExtraConstrs;
      if (sym == neg(l)) {
        break;
      }

      prevLit = l;
      prevSym = sym;
      prevTst = tst;
    }
  }
}

void Breaker::addShatter(sptr<Permutation> perm, std::vector<uint>& order, bool limitExtraConstrs) {
  std::unordered_set<uint> allowedLits; // which are not the last lit in their cycle, unless they map to their negation
  for (uint i = order.size(); i > 0; --i) {
    uint lit = order.at(i - 1);
    if (allowedLits.count(lit) == 0) { // we have a last lit of a cycle
      uint sym = perm->getImage(lit);
      while (sym != lit) { // add the other lits of the cycle and the negated cycle
        allowedLits.insert(sym);
        allowedLits.insert(neg(sym));
        sym = perm->getImage(sym);
      }
    }
  }

  int nrExtraConstrs = 0;
  uint prevLit = 0;
  uint prevSym = 0;
  uint prevTst = 0; // previous tseitin
  for (auto l : order) {
    if (limitExtraConstrs && nrExtraConstrs > symBreakingFormLength) {
      break;
    }
    uint sym = perm->getImage(l);
    if (sym != l && allowedLits.count(l)) {
      uint tst = 0;
      if (nrExtraConstrs == 0) {
        // adding clause for l => sym :
        // ~l | sym
        addBinary(neg(l), sym);
      } else if (nrExtraConstrs == 1) {
        tst = getTseitinVar();
        // clause(-z, -x, p[x], 0);
        addTernary(neg(prevLit), neg(l), sym);
        // clause(-z, vars+1, 0);
        addBinary(neg(prevLit), tst);
		// clause(p[z], -x, p[x], 0);
        addTernary(prevSym, neg(l), sym);
		// clause(p[z], vars+1, 0);        
        addBinary(prevSym, tst);
      } else {
        tst = getTseitinVar();
        // clause(-vars, -z, -x, p[x], 0);
        addQuaternary(neg(prevTst), neg(prevLit), neg(l), sym);
        // clause(-vars, -z, vars+1, 0);
        addTernary(neg(prevTst), neg(prevLit), tst);
		// clause(-vars, p[z], -x, p[x], 0);
        addQuaternary(neg(prevTst), prevSym, neg(l), sym);
		// clause(-vars, p[z], vars+1, 0);        
        addTernary(neg(prevTst), prevSym, tst);
      }
      ++nrExtraConstrs;
      if (sym == neg(l)) {
        break;
      }

      prevLit = l;
      prevSym = sym;
      prevTst = tst;
    }
  }
}

uint Breaker::getAuxiliaryNbVars() {
  return nbExtraVars;
}

uint Breaker::getTotalNbVars() {
  return nVars + nbExtraVars;
}

uint Breaker::getAddedNbClauses() {
  return clauses.size();
}

uint Breaker::getTotalNbClauses() {
  return originalTheory->getSize() + clauses.size();
}

uint Breaker::getNbBinClauses() {
  return nbBinClauses;
}

uint Breaker::getNbRowClauses() {
  return nbRowClauses;
}

uint Breaker::getNbRegClauses() {
  return nbRegClauses;
}

uint Breaker::getTseitinVar() {
  ++nbExtraVars;
  return encode(getTotalNbVars());
}
