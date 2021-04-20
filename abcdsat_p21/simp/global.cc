#include "global.hpp"
#include "limits.h"

using namespace std;

uint nVars = 0;
std::vector<uint> fixedLits;
time_t startTime;

// OPTIONS:
bool useMatrixDetection = true;
bool useBinaryClauses = true;
bool onlyPrintBreakers = false;
bool useShatterTranslation = false;
int symBreakingFormLength = 50;
//uint verbosity = 1;
uint verbosity = 0;
uint timeLim = 100;//UINT_MAX;

size_t _getHash(const std::vector<uint>& xs) {
  size_t seed = xs.size();
  for (auto x : xs) {
    seed ^= x + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  }
  return seed;
}

uint timeLeft() {
  if (timeLim == UINT_MAX) {
    return UINT_MAX;
  } else {
    time_t now;
    time(&now);
    return timeLim - difftime(now, startTime);
  }
}

bool timeLimitPassed() {
  return timeLeft() < 0;
}

