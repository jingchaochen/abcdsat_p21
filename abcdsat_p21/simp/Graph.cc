#include "Graph.hpp"
#include "saucy.h"

//=====================SAUCYWRAPPER=METHODS=====================================

std::vector<sptr<Permutation> > perms;

// This method is given to Saucy as a polymorphic consumer of the detected generator permutations

static int addPermutation(int n, const int *ct_perm, int nsupp, int *support, void *arg) {
  if (n == 0 || nsupp == 0) {
    return not timeLimitPassed();
  }
  
  sptr<Permutation> perm = std::make_shared<Permutation>();
  for(int i=0; i<n; ++i) {
    if(i!=ct_perm[i]){
      perm->addFromTo(i,ct_perm[i]);
    }
  }
  perms.push_back(perm);

  return not timeLimitPassed();
}

//=====================GRAPH====================================================

Graph::Graph(std::unordered_set<sptr<Clause>, UVecHash, UvecEqual>& clauses) {
  sg = (saucy_graph*) malloc(sizeof (struct saucy_graph));

  int n = 2 * nVars + clauses.size();

  // Initialize colors:
  sg->colors = (int*) malloc(n * sizeof (int));
  for (uint i = 0; i < 2 * nVars; ++i) {
    sg->colors[i] = 0;
  }
  colorcount.push_back(2 * nVars);

  for (int i = 2 * nVars; i < n; ++i) {
    sg->colors[i] = 1;
  }
  colorcount.push_back(clauses.size());

  // Initialize edge lists
  // First construct for each node the list of neighbors
  std::vector<std::vector<uint> > neighbours(n);
  // Literals have their negations as neighbors
  for (uint l = 1; l <= nVars; ++l) {
    uint posID = encode(l);
    uint negID = encode(-l);
    neighbours[posID].push_back(negID);
    neighbours[negID].push_back(posID);
  }
  // Clauses have as neighbors the literals occurring in them
  uint c = 2 * nVars;
  for (auto cl : clauses) {
    for (auto lit : cl->lits) {
      neighbours[lit].push_back(c);
      neighbours[c].push_back(lit);
    }
    ++c;
  }

  // now count the number of neighboring nodes
  sg->adj = (int*) malloc((n + 1) * sizeof (int));
  sg->adj[0] = 0;
  int ctr = 0;
  for (auto nblist : neighbours) {
    sg->adj[ctr + 1] = sg->adj[ctr] + nblist.size();
    ++ctr;
  }

  // finally, initialize the lists of neighboring nodes, C-style
  sg->edg = (int*) malloc(sg->adj[n] * sizeof (int));
  ctr = 0;
  for (auto nblist : neighbours) {
    for (auto l : nblist) {
      sg->edg[ctr] = l;
      ++ctr;
    }
  }

  sg->n = n;
  sg->e = sg->adj[n] / 2;
  
  // look for unused lits, make their color unique so that no symmetries on them are found
  // useful for subgroups
  std::unordered_set<uint> usedLits;
  for (auto cl : clauses) {
    for (auto lit : cl->lits) {
      usedLits.insert(lit);
      usedLits.insert(neg(lit));
    }
  }
  for(uint i=0; i<2*nVars; ++i){
    if(usedLits.count(i)==0){
      setUniqueColor(i);
    }
  }
  
  // fix fixedLits
  setUniqueColor(fixedLits);
}

Graph::~Graph() {
  free(sg->adj);
  free(sg->edg);
  free(sg->colors);
  free(sg);
}

void Graph::print() {
  for (int i = 0; i < sg->n; ++i) {
    fprintf(stderr, "node %i with color %i has neighbours\n", i, sg->colors[i]);
    for (int j = sg->adj[i]; j < sg->adj[i + 1]; ++j) {
      fprintf(stderr, "%i ", sg->edg[j]);
    }
    fprintf(stderr, "\n");
  }
}

uint Graph::getNbNodes() {
  return (uint) sg->n;
}

void Graph::setUniqueColor(uint lit) {
  uint currentcount = colorcount[sg->colors[lit]];
  if (currentcount == 1) {
    return; // color was already unique
  }
  colorcount[sg->colors[lit]] = currentcount - 1;
  sg->colors[lit] = colorcount.size() - 1;
  colorcount.push_back(1);
}

void Graph::setUniqueColor(const std::vector<uint>& lits) {
  for (auto lit : lits) {
    setUniqueColor(lit);
  }
}

void Graph::getSymmetryGenerators(std::vector<sptr<Permutation> >& out_perms) {
  out_perms.clear();
  
  if(getNbNodes()<=2*nVars){ // Saucy does not like empty graphs, so don't call Saucy with an empty graph
    return;
  }
  
  if (timeLimitPassed()) { // do not call saucy again when interrupted by time limit previously
    return;
  }

  if (verbosity > 1) {
    std::clog << "c Running Saucy with time limit: " << timeLeft() << std::endl;
  }

  // WARNING: make sure that maximum color does not surpass the number of colors, as this seems to give saucy trouble...  
  struct saucy* s = saucy_alloc(sg->n, timeLeft());
  struct saucy_stats stats;
 // std::clog << "c saucy_search " << std::endl;
  
  saucy_search(s, sg, 0, addPermutation, 0, &stats);
  saucy_free(s);
  // TODO: how to check whether sg is correctly freed?

  std::swap(out_perms,perms);
}
