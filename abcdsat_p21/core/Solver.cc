/***************************************************************************************[Solver.cc]
abcdSAT parallel -- Copyright (c) 2017-2021, Jingchao Chen   

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include "utils/System.h"
#include "mtl/Sort.h"
#include "core/Solver.h"
#include "core/Constants.h"

extern int **Bclauses;

using namespace abcdSAT;
using namespace std;

inline Lit makeLit(int lit) { return (lit > 0) ? mkLit(lit-1) : ~mkLit(-lit-1);}

//=================================================================================================
// Options:

static const char* _cat = "CORE";
static const char* _cr = "CORE -- RESTART";
static const char* _cred = "CORE -- REDUCE";
static const char* _cm = "CORE -- MINIMIZE";

static DoubleOption  opt_alpha         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));

static DoubleOption  opt_alpha_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_alpha     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));

static DoubleOption opt_K(_cr, "K", "The constant used to force restart", 0.8, DoubleRange(0, false, 1, false));
static DoubleOption opt_R(_cr, "R", "The constant used to block restart", 1.4, DoubleRange(1, false, 5, false));
static IntOption opt_size_lbd_queue(_cr, "szLBDQueue", "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX));
static IntOption opt_size_trail_queue(_cr, "szTrailQueue", "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX));

static IntOption opt_first_reduce_db(_cred, "firstReduceDB", "The number of conflicts before the first reduce DB", 2000, IntRange(0, INT32_MAX));
static IntOption opt_inc_reduce_db(_cred, "incReduceDB", "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static IntOption opt_spec_inc_reduce_db(_cred, "specialIncReduceDB", "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX));
static IntOption opt_lb_lbd_frozen_clause(_cred, "minLBDFrozenClause", "Protect clauses if their LBD decrease and is lower than (for one turn)", 30, IntRange(0, INT32_MAX));

static IntOption opt_lb_size_minimzing_clause(_cm, "minSizeMinimizingClause", "The min size required to minimize clause", 30, IntRange(3, INT32_MAX));
static IntOption opt_lb_lbd_minimzing_clause(_cm, "minLBDMinimizingClause", "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX));

static DoubleOption opt_var_decay(_cat, "var-decay", "The variable activity decay factor (starting point)", 0.8, DoubleRange(0, false, 1, false));
static DoubleOption opt_max_var_decay(_cat, "max-var-decay", "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, false));
static DoubleOption opt_clause_decay(_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false));
static DoubleOption opt_random_var_freq(_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption opt_random_seed(_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption opt_ccmin_mode(_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption opt_phase_saving(_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static DoubleOption opt_garbage_frac(_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20, DoubleRange(0, false, HUGE_VAL, false));

static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));

//=================================================================================================
// Constructor/Destructor:

Solver::Solver() :

// Parameters (user settable):
//
verbosity(0)
, K(opt_K)
, R(opt_R)
, sizeLBDQueue(opt_size_lbd_queue)
, sizeTrailQueue(opt_size_trail_queue)
, firstReduceDB(opt_first_reduce_db)
, incReduceDB(opt_inc_reduce_db)
, specialIncReduceDB(opt_spec_inc_reduce_db)
, lbLBDFrozenClause(opt_lb_lbd_frozen_clause)
, lbSizeMinimizingClause(opt_lb_size_minimzing_clause)
, lbLBDMinimizingClause(opt_lb_lbd_minimzing_clause)
, var_decay(opt_var_decay)
, max_var_decay(opt_max_var_decay)
, clause_decay(opt_clause_decay)
, random_var_freq(opt_random_var_freq)
, random_seed(opt_random_seed)
, ccmin_mode(opt_ccmin_mode)
, phase_saving(opt_phase_saving)
, rnd_pol(false)
, garbage_frac(opt_garbage_frac)
// Statistics: (formerly in 'SolverStats')
//
, nbRemovedClauses(0), nbBin(0), nbUn(0), nbReduceDB(0)
, starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
, dec_vars(0), clauses_literals(0), learnts_literals(0)
, curRestart(1)
, unitsum(0),equsum(0)
, sched_heap (VarSchedLt(vscore))

, ok(true)
, cla_inc(1)
, var_inc(1)
, watches(WatcherDeleted(ca))
, watchesBin(WatcherDeleted(ca))
, qhead(0)
, simpDB_assigns(-1)
, simpDB_props(0)
, order_heap(VarOrderLt(activity))
, remove_satisfied(true)
// Resource constraints:
, conflict_budget(-1)
, propagation_budget(-1)
, asynch_interrupt(false)
, restart_first    (opt_restart_first)
, restart_inc      (opt_restart_inc)
{
    MYFLAG = 0;
    lbdQueue.initSize(sizeLBDQueue);
    trailQueue.initSize(sizeTrailQueue);
    sumLBD = 0;
    nbclausesbeforereduce = firstReduceDB;
    parallel_pivot = lit_Undef;
    LBDmode = 1;
    bitVecNo = -1;
    vdecay_delta = 0.01;
    v_inc_factor = 0.5;
    atLeastTwo = false;
    BCDmode=false;
    inprocessmode=false;
    WVSIDSmode=1;
    varRange=0;
    touchMark=0;
    mark=0;
    markNo=0;
    equhead=equlink=0;
    originVars=0;
    symmtryMode=false;
    bitLim = 2e4;

    next_simplify_small=1000;
    beta= 1 - alpha;
    learnt_small=0;
    timer = 5000;
    alpha=opt_alpha;
    alpha_dec=opt_alpha_dec;
    min_alpha=opt_min_alpha;
    small_lbd_lim=3;
    sumLBD=0;
    next_LONG_reduce=15000;
    VSIDS=true;
    mix_simp_mode=0;
    pureMode=1;
    canPause=pause=false;

    cur_solustion_used  = false;
    freeze_restart_num   = 0;
    best_unsat_num       = INT_MAX;
    max_trail            = 0;
}

//-------------------------------------------------------
// Special constructor used for cloning solvers
//-------------------------------------------------------

Solver::Solver(const Solver &s) :
  verbosity(s.verbosity)
, K(s.K)
, R(s.R)
, sizeLBDQueue(s.sizeLBDQueue)
, sizeTrailQueue(s.sizeTrailQueue)
, firstReduceDB(s.firstReduceDB)
, incReduceDB(s.incReduceDB)
, specialIncReduceDB(s.specialIncReduceDB)
, lbLBDFrozenClause(s.lbLBDFrozenClause)
, lbSizeMinimizingClause(s.lbSizeMinimizingClause)
, lbLBDMinimizingClause(s.lbLBDMinimizingClause)
, var_decay(s.var_decay)
, max_var_decay(s.max_var_decay)
, clause_decay(s.clause_decay)
, random_var_freq(s.random_var_freq)
, random_seed(s.random_seed)
, ccmin_mode(s.ccmin_mode)
, phase_saving(s.phase_saving)
, rnd_pol(s.rnd_pol)
, garbage_frac(s.garbage_frac)
// Statistics: (formerly in 'SolverStats')
//
, nbRemovedClauses(0) 
, nbBin(0), nbUn(0), nbReduceDB(0)
, starts(0), decisions(0), rnd_decisions(0)
, propagations(0), conflicts(0)
, dec_vars(s.dec_vars), clauses_literals(s.clauses_literals)
, learnts_literals(s.learnts_literals)
, curRestart(s.curRestart)
, unitsum(s.unitsum),equsum(s.equsum)
, sched_heap (VarSchedLt(vscore))
, originVars(s.originVars)

, ok(true)
, cla_inc(s.cla_inc)
, var_inc(s.var_inc)
, watches(WatcherDeleted(ca))
, watchesBin(WatcherDeleted(ca))
, qhead(s.qhead)
, simpDB_assigns(s.simpDB_assigns)
, simpDB_props(s.simpDB_props)
, order_heap(VarOrderLt(activity))
, remove_satisfied(s.remove_satisfied)
// Resource constraints:
, conflict_budget(s.conflict_budget)
, propagation_budget(s.propagation_budget)
, asynch_interrupt(s.asynch_interrupt)
, restart_first    (opt_restart_first)
, restart_inc      (opt_restart_inc)
{
    // Copy clauses.
    s.ca.copyTo(ca);
    ca.extra_clause_field = s.ca.extra_clause_field;

    MYFLAG = 0;
    sumLBD = s.sumLBD;
    nbclausesbeforereduce = s.nbclausesbeforereduce;
   
    // Copy all other vectors
    s.watches.copyTo(watches);
    s.watchesBin.copyTo(watchesBin);
    s.assigns.memCopyTo(assigns);
    s.vardata.memCopyTo(vardata);
    s.activity.memCopyTo(activity);
    s.seen.memCopyTo(seen);
    s.permDiff.memCopyTo(permDiff);
    s.polarity.memCopyTo(polarity);
    s.decision.memCopyTo(decision);
   
    s.decisionTime.memCopyTo(decisionTime);
    s.varBumpCnt.memCopyTo(varBumpCnt);
    s.canceled.memCopyTo(canceled);

    s.trail.memCopyTo(trail);
    s.order_heap.copyTo(order_heap);
    s.clauses.memCopyTo(clauses);
    s.learnts.memCopyTo(learnts);

    s.lbdQueue.copyTo(lbdQueue);
    s.trailQueue.copyTo(trailQueue);
    parallel_pivot = lit_Undef;
    LBDmode = 1;
    bitVecNo = -1;
    vdecay_delta = 0.008;
    v_inc_factor = 0.5;
    atLeastTwo = false;
    BCDmode=false;
    inprocessmode=false;
    WVSIDSmode=1;
    varRange=0;
    touchMark=0;
    mark=0;
    markNo=0;
    s.vscore.memCopyTo(vscore);
    s.extendRemLit.memCopyTo(extendRemLit);
    if(s.equhead){
          equhead = (int * ) calloc (s.nVars()+1, sizeof(int));
          equlink = (int * ) calloc (s.nVars()+1, sizeof(int));
          for(int i=0; i<=s.nVars(); i++) {
              equhead[i]=s.equhead[i];
              equlink[i]=s.equlink[i];
          }
    }
    else equhead=equlink=0;
    symmtryMode=false;

    next_simplify_small=1000;
    beta= 1 - alpha;
    learnt_small=0;
    timer = 5000;
    alpha=opt_alpha;
    alpha_dec=opt_alpha_dec;
    min_alpha=opt_min_alpha;
    small_lbd_lim=3;
    sumLBD=0;
    next_LONG_reduce=15000;
    VSIDS=true;
    mix_simp_mode=0;
    pureMode=1;
    canPause=pause=false;

    cur_solustion_used  = false;
    freeze_restart_num   = 0;
    best_unsat_num       = INT_MAX;
    max_trail            = 0;
}

Solver::~Solver() {
}

//=================================================================================================
// Minor methods:

// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//

Var Solver::newVar(bool sign, bool dvar) {
    int v = nVars();
    watches .init(mkLit(v, false));
    watches .init(mkLit(v, true));
    watchesBin .init(mkLit(v, false));
    watchesBin .init(mkLit(v, true));
    assigns .push(l_Undef);
    vardata .push(mkVarData(CRef_Undef, 0));
    activity .push(0);
    seen .push(0);
    permDiff .push(0);
    polarity .push(sign);
    decision .push();
    trail .capacity(v + 1);
    setDecisionVar(v, dvar);

    decisionTime.push(0);
    varBumpCnt.push(0);
    canceled.push(0);

    return v;
}

bool Solver::addClause_(vec<Lit>& ps) {

    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);

    vec<Lit> oc;
    oc.clear();

    Lit p;
    int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);
    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}

void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];

    assert(c.size() > 1);
    if (c.size() == 2) {
        watchesBin[~c[0]].push(Watcher(cr, c[1]));
        watchesBin[~c[1]].push(Watcher(cr, c[0]));
    } else {
        watches[~c[0]].push(Watcher(cr, c[1]));
        watches[~c[1]].push(Watcher(cr, c[0]));
    }
    if (c.learnt()) learnts_literals += c.size();
    else clauses_literals += c.size();
}

void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];

    assert(c.size() > 1);
    if (c.size() == 2) {
        if (strict) {
            remove(watchesBin[~c[0]], Watcher(cr, c[1]));
            remove(watchesBin[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watchesBin.smudge(~c[0]);
            watchesBin.smudge(~c[1]);
        }
    } else {
        if (strict) {
            remove(watches[~c[0]], Watcher(cr, c[1]));
            remove(watches[~c[1]], Watcher(cr, c[0]));
        } else {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge(~c[0]);
            watches.smudge(~c[1]);
        }
    }
    if (c.learnt()) learnts_literals -= c.size();
    else clauses_literals -= c.size();
}

void Solver::removeClause(CRef cr) {

    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}

bool Solver::satisfied(const Clause& c) const 
{
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True) return true;
    return false;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int clevel) {
    if (decisionLevel() > clevel){
        for (int c = trail.size()-1; c >= trail_lim[clevel]; c--){
            Var      x  = var(trail[c]);

            if (!VSIDS){ //CHB:conflict history based
                uint32_t age = conflicts - decisionTime[x];
                if (age >0){
                    double adjusted_reward =  varBumpCnt[x]/(double) age;
                    double old_activity = activity[x];
                    activity[x] = alpha * adjusted_reward + (beta * old_activity);
                    if (order_heap.inHeap(x)){
                        if (activity[x] > old_activity) order_heap.decrease(x);
                        else order_heap.increase(x);
                    }
                }
                canceled[x] = conflicts;
            }

            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[clevel];
        trail.shrink(trail.size() - trail_lim[clevel]);
        trail_lim.shrink(trail_lim.size() - clevel);
    } 
}

//=================================================================================================
// Major methods:

Lit Solver::pure_pickBranchLit() 
{
    Var next = var_Undef;
    int clevel=decisionLevel();
    // Random decision:
    if(random_var_freq !=0 ){
      if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
        next = order_heap[irand(random_seed, order_heap.size())];
        if (value(next) == l_Undef && decision[next]) rnd_decisions++;
        goto nofound; 
      }
    }
//
    if(varRange && clevel>0 && clevel < 4){
            if( (int)conflicts >= 3000000) goto nofound;
            Lit lit=trail[trail_lim[0]];
            int v = var(lit);
            if(varRange[v]==0) goto nofound;
            int ed = varRange[v];
            double maxAct=-10000;
            int vec[20];
            for (int i = varRange[v]+1; i >=ed-5; i--){
                        int *plit = Bclauses[i];
                        int j=0;
                        while(*plit){
                            int cv=ABS(*plit)-1;
                            if(value(cv) == l_Undef){
                                if(decision[cv] && j<20) vec[j++]=cv;  
                            }
                            else {
                                if(value(cv) == l_True) { if(*plit>0) goto nexti;}
                                else   if(*plit<0) goto nexti;
                            }
                            plit++;
                        }
            //
                        for(j--; j>=0; j--){
                              if(activity[vec[j]]>maxAct){
                                   next=vec[j];
                                   maxAct=activity[next];
                              }
                        }
                        nexti: ;
            }
    }
//
nofound:
   if (next == var_Undef){
        if (order_heap.empty()) return lit_Undef;
        else next = order_heap.removeMin();
    }
   
   // Activity based decision:
    while (value(next) != l_Undef || !decision[next])
        if (order_heap.empty()) return lit_Undef;
        else next = order_heap.removeMin();
   
    if(bitVecNo>=0){
        if(clevel<12) polarity[next]=(bitVecNo>>(clevel% 4)) & 1;
     }

    return mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}

Lit Solver::pickBranchLit()
{
    Var next = var_Undef;
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()) return lit_Undef;
        else{
    
            if (!VSIDS){//CHB conflict history-based
                Var v = order_heap[0];
                uint32_t age = conflicts - canceled[v];
                while (age > 0){
                    double decay = pow(0.95, age);
                    activity[v] *= decay;
                    if (order_heap.inHeap(v)) order_heap.increase(v);
                    canceled[v] = conflicts;
                    v = order_heap[0];
                    age = conflicts - canceled[v];
                }
            }
            next = order_heap.removeMin();
        }

    if (!VSIDS){
        decisionTime[next] = conflicts;
        varBumpCnt[next] = 0;
        uint32_t age = conflicts - canceled[next];
        if (age > 0){//CHB
            double decay = pow(0.95, age);
            activity[next] *= decay;
            if (order_heap.inHeap(next)) order_heap.increase(next);
        }
    }

    return mkLit(next, polarity[next]);
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::pure_analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel,unsigned int &lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

	// Special case for binary clauses
	// The first one has to be SAT
	if( p != lit_Undef && c.size()==2 && value(c[0])==l_False) {
	  
	  assert(value(c[1])==l_True);
	  Lit tmp = c[0];
	  c[0] =  c[1], c[1] = tmp;
	}
	
       if (c.learnt())  claBumpActivity(c);

       // DYNAMIC NBLEVEL trick (see competition'09 companion paper)
       if(c.learnt()  && c.lbd()>2) { 
	 MYFLAG++;
	 unsigned  int nblevels =0;
	 for(int i=0;i<c.size();i++) {
	   int l = level(var(c[i]));
	//   if (l!=0 && permDiff[l] != MYFLAG) {//new idea
	   if (permDiff[l] != MYFLAG) {
	     permDiff[l] = MYFLAG;
	     nblevels++;
	   }
	 }
	 if(nblevels+1<c.lbd() ) { // improve the LBD
	   if(c.lbd()<=lbLBDFrozenClause) {
	     c.removable(false); 
	   }
	   // seems to be interesting : keep it for the next round
	   c.set_lbd(nblevels); // Update it
	 }
       }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                if(WVSIDSmode) varBumpActivity(var(q),(1e4-j)*var_inc/1e4);
                else           varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) {
                    pathC++;
		    if((reason(var(q))!= CRef_Undef)  && ca[reason(var(q))].learnt()) 
		      lastDecisionLevel.push(q);
		} else {
                    out_learnt.push(q);
		}
	    }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    } else if (ccmin_mode == 1) {
        for (i = j = 1; i < out_learnt.size(); i++) {
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = ((c.size() == 2) ? 0 : 1); k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0) {
                        out_learnt[j++] = out_learnt[i];
                        break;
                    }
            }
        }
    } else  i = j = out_learnt.size();

    out_learnt.shrink(i - j);
  
    /// Minimisation with binary clauses of the asserting clause
    if(out_learnt.size()<=lbSizeMinimizingClause) {
      // Find the LBD measure                                                                                                         
      lbd = 0;
      MYFLAG++;
      for(int i=0;i<out_learnt.size();i++) {

	int l = level(var(out_learnt[i]));
	if (permDiff[l] != MYFLAG) {
	  permDiff[l] = MYFLAG;
	  lbd++;
	}
      }


      if(lbd<=lbLBDMinimizingClause){
      MYFLAG++;
      
      for(int i = 1;i<out_learnt.size();i++) {
	permDiff[var(out_learnt[i])] = MYFLAG;
      }

      vec<Watcher>&  wbin  = watchesBin[p];
      int nb = 0;
      for(int k = 0;k<wbin.size();k++) {
	Lit imp = wbin[k].blocker;
	if(permDiff[var(imp)]==MYFLAG && value(imp)==l_True) {
	  nb++;
	  permDiff[var(imp)]= MYFLAG-1;
	}
      }
      int l = out_learnt.size()-1;
      if(nb>0) {
	for(int i = 1;i<out_learnt.size()-nb;i++) {
	  if(permDiff[var(out_learnt[i])]!=MYFLAG) {
	    Lit p = out_learnt[l];
	    out_learnt[l] = out_learnt[i];
	    out_learnt[i] = p;
	    l--;i--;
	  }
	}
	
	//    printClause(out_learnt);
	out_learnt.shrink(nb);
      }
    }
    }
    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }


  // Find the LBD measure 
  lbd = 0;
  MYFLAG++;
  for(int i=0;i<out_learnt.size();i++) {
    
    int l = level(var(out_learnt[i]));
    if (permDiff[l] != MYFLAG) {
//    if (l!=0 && permDiff[l] != MYFLAG) {//new idea
      permDiff[l] = MYFLAG;
      lbd++;
    }
  }
  
    for(int i = 0;i<lastDecisionLevel.size();i++) {
      if(ca[reason(var(lastDecisionLevel[i]))].lbd()<lbd)
	varBumpActivity(var(lastDecisionLevel[i]), v_inc_factor*var_inc);
    }
    lastDecisionLevel.clear();

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}

void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause & c = ca[confl];

        // For binary clauses, we don't rearrange literals in propagate(), so check and make sure the first is an implied lit.
        if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False){
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp; }

        // Update LBD if improved.
        if (c.learnt() && c.mark() != SMALL){
            unsigned int lbd = computeLBD(c);
            if (lbd < c.lbd()){
                if (c.lbd() <= 30) c.removable(false); // Protect once from reduction.
                c.set_lbd(lbd);
                if (lbd <= small_lbd_lim){
                    learnt_small++;
                    c.mark(SMALL);
                }else if (lbd <= 6 && c.mark() == LONG) c.mark(MIDSZ); 
            }

            if (c.mark() == MIDSZ) c.touched() = conflicts;
            else if (c.mark() == LONG) claBumpActivity(c);
        }

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];
            int v=var(q);
            if (!seen[v] && level(v) > 0){
                if (VSIDS){
                    varBumpVSIDSactivity(v, var_inc);
                }
                else varBumpCnt[v]++;
                seen[v] = 1;
                if (level(v) >= decisionLevel()) pathC++;
                else out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    analyze_toclear.clear();
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = c.size() == 2 ? 0 : 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

  //  max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
   // tot_literals += out_learnt.size();

    out_lbd = computeLBD(out_learnt);
    if (out_lbd <= 6 && out_learnt.size() <= 30) // Try further minimization?
        if (binResMinimize(out_learnt))
            out_lbd = computeLBD(out_learnt); // Recompute LBD if minimized.

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1) out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i]))) max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }
//
    for(int i = out_learnt.size() - 1; i >= 0; i--){
          Var v = var(out_learnt[i]);
          CRef rs = reason(v);
          if (rs == CRef_Undef) continue;
          Clause & rC = ca[rs];
          if (!VSIDS){
               int delta=1;
               for (int i = 0; i < rC.size(); i++) varBumpCnt[var(rC[i])] += delta; //varBumpCnt[var(rC[i])]++;
          }
          else for (int i = 0; i < rC.size(); i++){
                     int v=var(rC[i]);
                     varBumpVSIDSactivity(v, var_inc);
               }
     }
     for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;
}

// Try further learnt clause minimization by means of binary clause resolution.
bool Solver::binResMinimize(vec<Lit>& out_learnt)
{
    // Preparation: remember which false variables we have in 'out_learnt'.
    MYFLAG++;
    for (int i = 1; i < out_learnt.size(); i++)
        permDiff[var(out_learnt[i])] = MYFLAG;

    // Get the list of binary clauses containing 'out_learnt[0]'.
    const vec<Watcher>& ws = watchesBin[~out_learnt[0]];

    int to_remove = 0;
    for (int i = 0; i < ws.size(); i++){
        Lit the_other = ws[i].blocker;
        // Does 'the_other' appear negatively in 'out_learnt'?
        if (permDiff[var(the_other)] == MYFLAG && value(the_other) == l_True){
            to_remove++;
            permDiff[var(the_other)] = MYFLAG - 1; // Remember to remove this variable.
        }
    }

    // Shrink.
    if (to_remove > 0){
        int last = out_learnt.size() - 1;
        for (int i = 1; i < out_learnt.size() - to_remove; i++)
            if (permDiff[var(out_learnt[i])] != MYFLAG)
                out_learnt[i--] = out_learnt[last--];
        out_learnt.shrink(to_remove);
    }
    return to_remove != 0;
}

// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.

bool Solver::litRedundant(Lit p, uint32_t abstract_levels) {
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0) {
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))];
        analyze_stack.pop(); // 
        if (c.size() == 2 && value(c[0]) == l_False) {
            assert(value(c[1]) == l_True);
            Lit tmp = c[0];
            c[0] = c[1], c[1] = tmp;
        }

        for (int i = 1; i < c.size(); i++) {
            Lit p = c[i];
            if (!seen[var(p)]) {
                if (level(var(p)) > 0) {
                    if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0) {
                        seen[var(p)] = 1;
                        analyze_stack.push(p);
                        analyze_toclear.push(p);
                    } else {
                        for (int j = top; j < analyze_toclear.size(); j++)
                            seen[var(analyze_toclear[j])] = 0;
                        analyze_toclear.shrink(analyze_toclear.size() - top);
                        return false;
                    }
                }
            }
        }
    }

    return true;
}

/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict) 
{
    out_conflict.clear();
    out_conflict.push(p);
    if (decisionLevel() == 0) return;
    seen[var(p)] = 1;
    for (int i = trail.size() - 1; i >= trail_lim[0]; i--) {
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            } else {
                Clause& c = ca[reason(x)];
                for (int j = ((c.size() == 2) ? 0 : 1); j < c.size(); j++)
                    if (level(var(c[j])) > 0) seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }
    seen[var(p)] = 0;
}

void Solver::uncheckedEnqueue(Lit p, CRef from) {
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate() 
{
    CRef confl = CRef_Undef;
    int num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    while (qhead < trail.size()) {
        Lit p = trail[qhead++]; // 'p' is enqueued fact to propagate.
        vec<Watcher>& ws = watches[p];
        Watcher *i, *j, *end;
        num_props++;
        //  Propagate binary clauses 
        vec<Watcher>& wbin = watchesBin[p];
        for (int k = 0; k < wbin.size(); k++) {
            Lit imp = wbin[k].blocker;
            if (value(imp) == l_False) return wbin[k].cref;
            if (value(imp) == l_Undef) uncheckedEnqueue(imp, wbin[k].cref);
        }

        // propagate 2-watched clauses
        for (i = j = (Watcher*) ws, end = i + ws.size(); i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True) {
                *j++ = *i++;
                continue;
            }

            // Make sure the false literal is data[1]:
            CRef cr = i->cref;
            Clause& c = ca[cr];
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            Watcher w = Watcher(cr, first);
            if (first != blocker && value(first) == l_True) {
                *j++ = w;
                continue;
            }
	      for (int k = 2; k < c.size(); k++) {
		if (value(c[k]) != l_False){
		  c[1] = c[k]; c[k] = false_lit;
		  watches[~c[1]].push(w);
		  goto NextClause;
                }
	      }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end) *j++ = *i++;
            } else uncheckedEnqueue(first, cr);
NextClause:
            ;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;
    return confl;
}

struct reduceDB_lt_lbd{ 
    ClauseAllocator& ca;
    reduceDB_lt_lbd(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
 
    // Main criteria... Like in MiniSat we keep all binary clauses
    if(ca[x].size()> 2 && ca[y].size()==2) return 1; //old 
    if(ca[y].size()>2 && ca[x].size()==2) return 0;  //old
    
     if(ca[x].size()==2 && ca[y].size()==2) return 0;
    
    // Second one  based on literal block distance
    if(ca[x].lbd()> ca[y].lbd()) return 1;
    if(ca[x].lbd()< ca[y].lbd()) return 0;    
    
    
    // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
    }    
};

struct reduceDB_lt_sz { 
    ClauseAllocator& ca;
    reduceDB_lt_sz(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
 
      if(ca[x].size()> ca[y].size()) return 1;//new
      if(ca[x].size()< ca[y].size()) return 0;//new
   
       if(ca[x].size()==2)  return 0;
    
    // Second one  based on literal block distance
       if(ca[x].lbd()> ca[y].lbd()) return 1;
       if(ca[x].lbd()< ca[y].lbd()) return 0;    
       return ca[x].activity() < ca[y].activity();
    }    
};

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
void Solver:: pure_reduceDB()
{
  int     i, j;
  nbReduceDB++;
 // sort(learnts, reduceDB_lt(ca));
  if(LBDmode) sort(learnts, reduceDB_lt_lbd(ca));
  else  sort(learnts, reduceDB_lt_sz(ca));

  // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
  if(ca[learnts[learnts.size() / RATIOREMOVECLAUSES]].lbd()<=3) nbclausesbeforereduce +=specialIncReduceDB; 
  // Useless :-)
  if(ca[learnts.last()].lbd()<=5)  nbclausesbeforereduce +=specialIncReduceDB; 
  
  
  // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
  // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

  int limit = learnts.size() / 2;

  for (i = j = 0; i < learnts.size(); i++){
    Clause& c = ca[learnts[i]];
    if (c.lbd()>2 && c.size() > 2 && c.removable() &&  !locked(c) && (i < limit)) {
      removeClause(learnts[i]);
      nbRemovedClauses++;
    }
    else {
      if(!c.removable()) limit++; //we keep c, so we can delete an other clause
      c.removable(true);       // At the next step, c can be delete
      learnts[j++] = learnts[i];
    }
  }
  learnts.shrink(i - j);
  checkGarbage();
}

struct reduceDB_lt_act{ 
    ClauseAllocator & ca;
    vec<CRef> & learnt;
    reduceDB_lt_act(ClauseAllocator & ca_, vec<CRef> & learnt_) : ca(ca_), learnt(learnt_){}
    bool operator () (int m, int n) {
         CRef x=learnt[m], y=learnt[n]; 
         return ca[x].activity() < ca[y].activity();
    }    
};

void Solver::reduceDB()
{
    int     i, j;
  
    vec <int> learntNo;
    for (i =j=0; i < learnts.size(); i++)
           if(ca[learnts[i]].mark() == LONG) learntNo.push(i);

    sort(learntNo, reduceDB_lt_act(ca,learnts));

    int limit = learntNo.size() / 2;
    for (i =0; i < learntNo.size(); i++){
        int no=learntNo[i];
        Clause & c = ca[learnts[no]];
        if (c.removable() && !locked(c) && i < limit){
             removeClause(learnts[no]);
             learnts[no]=CRef_Undef;
        }
        else{
                if (!c.removable()) limit++;
                c.removable(true);
        }
    }

    reduceDB_midsz(); 
       
    checkGarbage();
}

void Solver::reduceDB_midsz()
{   int i,j;
    for (i = j = 0; i < learnts.size(); i++){
        CRef cr = learnts[i];
        if(cr == CRef_Undef) continue;
        learnts[j++] = cr;
        Clause & c = ca[cr];
        if (c.mark() == MIDSZ)
            if (!locked(c) && c.touched() + 25000 < conflicts){
                c.mark(LONG);// mid --> large
                c.activity() = 0;
                claBumpActivity(c);
            }
    }
    learnts.shrink(i-j);
}

void Solver::removeSatisfied(vec<CRef>& cs) 
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause& c = ca[cs[i]];
        if (satisfied(c))  removeClause(cs[i]);
        else   cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    if(equhead){//bug
         for (Var v = 0; v < nVars(); v++)
             if(decision[v] && equhead[v] &&  equhead[v] !=v) setDecisionVar(v, false);
    }
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef) vs.push(v);

    order_heap.build(vs);
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify() 
{
    if (!ok) return ok = false;
    else {
        CRef cr = propagate();
        if (cr != CRef_Undef) return ok = false;
    }

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0)) return true;

    removeSatisfied(learnts);
    if (remove_satisfied) removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props = clauses_literals + learnts_literals; // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::pure_search(int nof_conflicts) 
{
    assert(ok);
    int backtrack_level;
    vec<Lit> learnt_clause;
    unsigned int nblevels;
    bool restart=false;
    starts++;

    int     state_starts_delta  = 1500;//2000;//starts
    freeze_restart_num--;
    bool    can_propagate_solution = true;
    if(starts > (unsigned )state_starts_delta)  rand_rephase();

    for (;;) {
        CRef confl = propagate();
        if (confl != CRef_Undef) {
            if(OtherSolverFinished())  return l_Undef;
            conflicts++;
            if (conflicts % 5000 == 0 && var_decay < max_var_decay) var_decay += vdecay_delta; //0.01;
            if (decisionLevel() == 0) return l_False;

            trailQueue.push(trail.size());
            if (conflicts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && 
                trail.size() > R * trailQueue.getavg()) {
                lbdQueue.fastclear();
            }

            learnt_clause.clear();
            pure_analyze(confl, learnt_clause, backtrack_level, nblevels);

            lbdQueue.push(nblevels);
            sumLBD += nblevels;

            cancelUntil(backtrack_level);

            if (learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
                if( parallel_pivot != lit_Undef ) 
                          if(!BCDmode || conflicts>2000000)
                               if(originVars<=0 || var(learnt_clause[0])<=originVars)
                                   parallelExportBinClause(~parallel_pivot, learnt_clause[0]);
                nbUn++;
            } else {
                CRef cr = ca.alloc(learnt_clause, true);
                Clause & c = ca[cr];
                if(atLeastTwo) c.set_lbd(5000000);
                else c.set_lbd(nblevels);
                if (c.size() == 2) nbBin++; // stats
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(c);
                uncheckedEnqueue(learnt_clause[0], cr);
            }
            varDecayActivity();
            claDecayActivity();
            restart=(lbdQueue.isvalid() && ((lbdQueue.getavg() * K) > (sumLBD / conflicts)));

// the top_trail_soln should be update after each conflict
            if(trail.size() > max_trail){
               max_trail = trail.size();
               int var_nums = nVars();
               for(int idx_i=0; idx_i<var_nums; ++idx_i){
                  lbool value_i = value(idx_i);
                  if(value_i==l_Undef) top_trail_soln[idx_i] = !polarity[idx_i];
                  else{
                     top_trail_soln[idx_i] = value_i==l_True?1:0;
                  }
               }
          }

         } else {
            if (restart || pause) {
                lbdQueue.fastclear();
                cancelUntil(0);
                return l_Undef;
            }
// NO CONFLICT
           if(starts > (unsigned)state_starts_delta){
                float   conflict_ratio      = 0.4;
                float   percent_ratio       = 0.9; 
                if( can_propagate_solution && freeze_restart_num < 1 && cur_solustion_used  && (trail.size() > (int)(conflict_ratio * nVars()) || trail.size() > (int)(percent_ratio * max_trail) )){
                    can_propagate_solution     = false;
                    cur_solustion_used  = false;
                    freeze_restart_num = 300; // int restarts_gap        = 300;
                    propagate_solution();
                }
            }

            if (decisionLevel() == 0 && !simplify())  return l_False;
            // Perform clause database reduction !
            if (conflicts >= ((unsigned int) curRestart * nbclausesbeforereduce)) {
                if (learnts.size() > 0) {
                    curRestart = (conflicts / nbclausesbeforereduce) + 1;
                    pure_reduceDB();
                    if (!panicModeIsEnabled())
                        nbclausesbeforereduce += incReduceDB;
                }
            }

            decisions++;
            Lit  next = pure_pickBranchLit();
            if (next == lit_Undef) return l_True;
        
            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}

lbool Solver::search(int & nof_conflicts)
{
    int         backtrack_level,lbd;
    vec<Lit>    learnt_clause;
    starts++;
  
    int     state_starts_delta  = 1500;//2000;//starts
    freeze_restart_num--;
    bool    can_propagate_solution = true;
    if(starts > (unsigned )state_starts_delta)  rand_rephase();

    for (;;){
        CRef confl = propagate();
        if (confl != CRef_Undef){ // CONFLICT
            if (VSIDS){
                if (--timer == 0 && var_decay < 0.95) timer = 5000, var_decay += 0.01;
            }
            else if (alpha > min_alpha){
                    alpha -= alpha_dec;
                    beta = 1-alpha;
                 }

            conflicts++; nof_conflicts--;
            if (conflicts == 100000 && learnt_small < 100) small_lbd_lim = 5;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();

            analyze(confl, learnt_clause, backtrack_level, lbd);
            cancelUntil(backtrack_level);

            lbd--;
            if (VSIDS) lbdQueue.push(lbd);
            sumLBD += lbd;
                  
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
                if( parallel_pivot != lit_Undef ) 
                          if(conflicts>2000000)
                               if(originVars<=0 || var(learnt_clause[0])<=originVars)
                                   parallelExportBinClause(~parallel_pivot, learnt_clause[0]);
            }
            else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                Clause & c = ca[cr];
                c.set_lbd(lbd);
                if ((unsigned) lbd <= small_lbd_lim){
                    learnt_small++;
                    c.mark(SMALL);
                }else if (lbd <= 6){
                    c.mark(MIDSZ);
                    c.touched() = conflicts;
                }else claBumpActivity(c); 
                attachClause(cr);
                uncheckedEnqueue(learnt_clause[0], cr);
           }
   
            if (VSIDS) varDecayActivity();
            claDecayActivity();

            bool restart;
            if (!VSIDS) restart = nof_conflicts <= 0;
            else restart = lbdQueue.isvalid() && (lbdQueue.getavg() * K > (sumLBD/conflicts));
            if (restart){
                lbdQueue.fastclear();
                cancelUntil(0);
                return l_Undef; 
            }
// the top_trail_soln should be update after each conflict
            if(trail.size() > max_trail){
               max_trail = trail.size();
               int var_nums = nVars();
               for(int idx_i=0; idx_i<var_nums; ++idx_i){
                  lbool value_i = value(idx_i);
                  if(value_i==l_Undef) top_trail_soln[idx_i] = !polarity[idx_i];
                  else{
                     top_trail_soln[idx_i] = value_i==l_True?1:0;
                  }
               }
           }
        }
        else{
// NO CONFLICT
            if(starts > (unsigned)state_starts_delta){
                float   conflict_ratio      = 0.4;
                float   percent_ratio       = 0.9; 
                if( can_propagate_solution && freeze_restart_num < 1 && cur_solustion_used  && (trail.size() > (int)(conflict_ratio * nVars()) || trail.size() > (int)(percent_ratio * max_trail) )){
                    can_propagate_solution     = false;
                    cur_solustion_used  = false;
                    freeze_restart_num = 300; // int restarts_gap        = 300;
                    propagate_solution();
                }
             }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) return l_False;

            if (conflicts <200000 && conflicts > next_simplify_small){
                       if (!simplifysmallclause()) return l_False;
                       next_simplify_small=conflicts+5000;
            }
           
            if (conflicts >= next_LONG_reduce){
                next_LONG_reduce = conflicts + 15000;
                reduceDB();

                if(conflicts<500000) {
                      if(re_learn() == l_False) return l_False;
                      if(VSIDS) varDecayActivity();
                }
      
                if (conflicts <700000 || conflicts > next_simplify_small){
                       if (!simplifysmallclause()) return l_False;
                       next_simplify_small=conflicts+50000;
                }
            }

            decisions++;
            Lit next = pickBranchLit();
            if (next == lit_Undef)  return l_True;
          
            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}

double Solver::progressEstimate() const {
    double progress = 0;
    double F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}
void init_rand_seed () ;
int breakID_main(Solver* solver);

void Solver::symmtry()
{
    originVars=nVars();
    if(originVars<100000 && nClauses() <= 800000) breakID_main(this);
}  

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::pure_solve()
{
   if(symmtryMode) symmtry();

    model.clear();
    conflict.clear();
    if (!ok) return l_False;
    double curTime = cpuTime();

    cur_solution.resize(nVars());
    best_solution.resize(nVars());
    top_trail_soln.resize(nVars());
  
    if( parallel_pivot != lit_Undef){
           if( value(parallel_pivot) == l_False) { ok=false; return l_False;}
           if( value(parallel_pivot) != l_True) {
                 uncheckedEnqueue(parallel_pivot);
                 CRef confl = propagate();
                 if (confl != CRef_Undef) { ok=false; return l_False;}
                 if(!simplify()) {ok=false; return l_False;}
           }
           else parallel_pivot=lit_Undef;
    }
  
    lbool   status = l_Undef;
    if(inprocessmode) status = s_preprocess();

    if(BCDmode && nVars() < 200000 && nClauses() < 1000000) fast_bcd();
  
    int old_usize =0;
    uint64_t next_get=10000;
    uint64_t lim_conf=20000;
    int unFix=nUnfixedVars();
    while (status == l_Undef){
        if(canPause){
              if(isPause()){
                  cancelUntil(0);
                  cloneSolver();
                  setPause(false);
              }
        }
        if ( (int) conflicts < bitLim ) bitVecNo++;
        else {
             if(bitLim == -1 && bitVecNo >=0  && conflicts<1000000) bitVecNo++;
             else bitVecNo=-1;
        }
        if( parallel_pivot == lit_Undef){
              int m=FixedVars();
              for (int i = old_usize; i < m; i++) {
                   if(originVars>0 && var(trail[i]) >= originVars) continue;
                   ok=parallelExportUnitClause(trail[i]);
                   if (!ok) return l_False;
              }
              old_usize = m;
        }
        if(conflicts>next_get){
            next_get = conflicts+10000;
            while(1){
                Lit uLit=getUnit();
                if( uLit == lit_Undef) break;
                if( value (uLit) == l_False){ ok=false; return l_False;}
                if( value (uLit) == l_True) continue;
                uncheckedEnqueue(uLit);
                CRef confl = propagate();
                if (confl != CRef_Undef) { ok=false; return l_False;}
            }
            while(1){
                 Lit p,q=lit_Undef;
                 getbin(p,q);
                 if( q == lit_Undef) break;
                 putbin(p, q);
            }
       }
    
        status = pure_search(0); // the parameter is useless in glucose, kept to allow modifications
        if (!withinBudget()) break;
         int cur_unFix=nUnfixedVars();
         if(status == l_Undef && lim_conf<conflicts && cur_unFix != unFix) {
                 status = inprocess();
                 unFix=cur_unFix;
                 lim_conf = conflicts+3000;
         }
        
        if(OtherSolverFinished()) break;
    }

    if (status == l_True){
        ExtendCopyModel();
    }
    else if (status == l_False && conflict.size() == 0)  ok = false;
    cancelUntil(0);
    double finalTime = cpuTime();
    totalTime = finalTime-curTime;
    return status;
}

static double luby(double y, int x){
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);
    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }
    return pow(y, seq);
}

lbool Solver::CHB_VSIDS_solve()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;
    double curTime = cpuTime();

    cur_solution.resize(nVars());
    best_solution.resize(nVars());
    top_trail_soln.resize(nVars());
  
    if( parallel_pivot != lit_Undef){
           if( value(parallel_pivot) == l_False) { ok=false; return l_False;}
           if( value(parallel_pivot) != l_True) {
                 uncheckedEnqueue(parallel_pivot);
                 CRef confl = propagate();
                 if (confl != CRef_Undef) { ok=false; return l_False;}
                 if(!simplify()) {ok=false; return l_False;}
           }
           else parallel_pivot=lit_Undef;
    }
    lbool   status = l_Undef;
    int old_usize =0;
    uint64_t next_get=10000;
  
    VSIDS = true;
    int init = 10000;
    while (status == l_Undef && init > 0)
        status = search(init);
    VSIDS = false;

    int curr_restarts = 0;
    int switch_distance=500;
    while (status == l_Undef){
        if( parallel_pivot == lit_Undef){
              int m=FixedVars();
              for (int i = old_usize; i < m; i++) {
                   if(originVars>0 && var(trail[i]) >= originVars) continue;
                   ok=parallelExportUnitClause(trail[i]);
                   if (!ok) return l_False;
              }
              old_usize = m;
        }
        if(conflicts>next_get){
            next_get = conflicts+10000;
            while(1){
                Lit uLit=getUnit();
                if( uLit == lit_Undef) break;
                if( value (uLit) == l_False){ ok=false; return l_False;}
                if( value (uLit) == l_True) continue;
                uncheckedEnqueue(uLit);
                CRef confl = propagate();
                if (confl != CRef_Undef) { ok=false; return l_False;}
            }
            while(1){
                 Lit p,q=lit_Undef;
                 getbin(p,q);
                 if( q == lit_Undef) break;
                 putbin(p, q);
            }
       }

       if (VSIDS){
            int weighted = INT32_MAX;
            status = search(weighted);
        }else{
            int nof_conflicts = luby(restart_inc, curr_restarts) * restart_first;
            curr_restarts++;
            status = search(nof_conflicts);
        }
        if (status != l_Undef) break;

        switch_distance--;
        if(switch_distance<0){
            if(VSIDS){
                VSIDS = false;
            }else{
                VSIDS = true;
                decisionTime.clear();
                varBumpCnt.clear();
#ifdef ANTI_EXPLORATION
                canceled.clear();
#endif
            }
            switch_distance=500;
        }

        if(OtherSolverFinished()) break;
    }

    if (status == l_True){
        ExtendCopyModel();
    }
    else if (status == l_False && conflict.size() == 0)  ok = false;
    cancelUntil(0);
    double finalTime = cpuTime();
    totalTime = finalTime-curTime;
    return status;
}

void Solver::ExtendCopyModel() {
      s_extend ();     // Extend & copy model:
      model.growTo(nVars());
      for (int i = 0; i < nVars(); i++) model[i] = value(i);
      solveEqu(equhead, nVars(), model);
      int msz=originVars ? originVars : model.size();
      model.shrink(model.size()-msz);
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
static Var mapVar(Var x, vec<Var>& map, Var& max) {
    if (map.size() <= x || map[x] == -1) {
        map.growTo(x + 1, -1);
        map[x] = max++;
    }
    return map[x];
}

void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max) {
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max) + 1);
    fprintf(f, "0\n");
}

void Solver::toDimacs(const char *file, const vec<Lit>& assumps) {
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}

void Solver::toDimacs(FILE* f, const vec<Lit>& assumps) {
    // Handle case when solver is in contradictory state:
    if (!ok) {
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return;
    }

    vec<Var> map;
    Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])) {
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++) {
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max) + 1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to) {
    // All watchers:
    watches.cleanAll();
    watchesBin.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++) {
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws2 = watchesBin[p];
            for (int j = 0; j < ws2.size(); j++)
                ca.reloc(ws2[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++) {
        Var v = var(trail[i]);
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}

void Solver::garbageCollect() {
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
            ca.size() * ClauseAllocator::Unit_Size, to.size() * ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

//--------------------------------------------------------------
// parallel
bool Solver::panicModeIsEnabled() {
    return false;
}

bool Solver:: parallelExportUnitClause(Lit p) {
    return true;
}

void Solver:: parallelExportBinClause(Lit p, Lit q) {
    return;
}

Lit Solver::getUnit() {
    return lit_Undef;
}

void Solver:: getbin(Lit & p, Lit & q){
    return;
}

struct freq_lt {
    unsigned int * & freq2;
    freq_lt( unsigned int * & freq2_) : freq2(freq2_) { }
    bool operator()(int v1, int v2) { return freq2[v1]>freq2[v2];}
};

void Solver :: extractHighVar(vec <Lit> & highLit)
{
     int *freq = (int  * ) calloc (2*nVars()+1, sizeof(int));
     for (int i =0; i < clauses.size(); i++){
        CRef cr =clauses[i];
        Clause& c = ca[cr];
        for(int j=0; j<c.size(); j++) freq[toInt(c[j])]++;
     }
     int *highv = (int  *) malloc (nVars()*sizeof(int));
     unsigned int *freq2 = (unsigned int  *) malloc (nVars()*sizeof(int));
     unsigned int max_int=0x7ffffff0;
     for (int v =0; v < nVars(); v++){
           uint64_t nowf=(uint64_t)freq[2*v]*(uint64_t)freq[2*v+1];
           if(nowf > max_int) nowf = max_int;
           freq2[v]=nowf;
           highv[v]=v;
     }
     sort(highv, nVars(), freq_lt(freq2));
     highLit.clear();
     for (int i =0; i < nVars() && i<23; i++){
          int v=highv[i];
           if( value(v) != l_Undef) continue;
           Lit lit = (freq[2*v] < freq[2*v+1]) ? toLit(2*v+1) :toLit(2*v);
            if(i>14) lit = ~lit; 
           highLit.push(lit);
     }
     free(freq);
     free(freq2);
     free(highv);
}       

// a bin clasue exists?
bool Solver::hasBin(Lit p, Lit q)
{
    vec<Watcher>&  wbin  = watchesBin[~p];
    for(int k = 0;k<wbin.size();k++) {
	  Lit imp = wbin[k].blocker;
	  if( imp == q) return true;
    }
    return false;
}	  

inline bool Solver :: non_decision(Lit p)
{    Var v=var(p);
     if (value(v) != l_Undef || !decision[v]) return true;
     return false;
}

void Solver:: putbin(Lit p, Lit q)
{
     // if( value(p) != l_Undef || value(q) != l_Undef) return;//bug
      if(non_decision(p)) return; 
      if(non_decision(q)) return;
      if(equhead){
             int v = var(p)+1;
             if(equhead[v] &&  equhead[v] !=v){
                    setDecisionVar(v, false);
                    return;
             }
             v = var(q)+1;
             if(equhead[v] &&  equhead[v] !=v){
                    setDecisionVar(v, false);
                    return;
             }
      }         
      if( hasBin(p,q) ) return;
      vec<Lit> ps;
      ps.push(p);
      ps.push(q);
      CRef cr = ca.alloc(ps, false);
      clauses.push(cr);
      attachClause(cr);
}

//-----------------------------
extern int nVarsB;
extern int sumLit;
extern int nClausesB;

void MixBCD(int pure_mode); 

void Solver :: varOrderbyClause()
{  
   int rng=5;
   for (Var v = 0; v < nVars(); v++) varRange[v]=0;    
   for (int i = 0; i < nClausesB-5; i++){
      if(Bclauses[i][2]==0) continue;
      int *plit = Bclauses[i];
      int v=ABS(*plit)-1;
      if(varRange[v]==0){
          varRange[v]=i;
          if(varRange[v]<rng) varRange[v]=rng;
      }
   }
   for (int i = 0; i < nClausesB-5; i++){
      if(Bclauses[i][2]) continue;
      int *plit = Bclauses[i];
      int v=ABS(*plit)-1;
      if(varRange[v]==0){
          varRange[v]=i;
          if(varRange[v]<rng) varRange[v]=rng;
      }
   }
}
 
void Solver :: fast_bcd()
{  
   nVarsB = nVars();
   if(nVarsB < 60) return;
   nClausesB=clauses.size();
   sumLit=0;   
   for (int i = 0; i < nClausesB; i++){
      Clause& c = ca[clauses[i]];
      sumLit += c.size() + 1;
   }
   Bclauses = (int**) malloc(sizeof(int*) * (nClausesB+1));
   Bclauses[0] = (int*) malloc (sizeof(int)*sumLit);
   int j; 
   for (int i = 0; i < nClausesB; i++){
      Clause& c = ca[clauses[i]];
      for (j = 0; j < c.size(); j++){
           Bclauses[i][j] = toIntLit(c[j]);
      }
      Bclauses[i][j]=0;
      Bclauses[i+1] = Bclauses[i] +j+1;
  }
  MixBCD(0);

  varRange = (int* )calloc (nVars(), sizeof(int));
  varOrderbyClause();
}
//---------------------------------------
lbool Solver :: s_preprocess()
{
    if(nClauses() > 5000000 || nVars() > 600000) return l_Undef;
    lbool status = s_probe ();
    if(status != l_Undef) return status;
    status = distill();
    if(status != l_Undef) return status;
    status = tarjan_SCC();
    if(status != l_Undef) return status;
    status = transitive_reduction();
    if(status != l_Undef) return status;
    return s_eliminate ();
}

typedef struct RNG { unsigned z, w; } RNG;
RNG rng;
unsigned s_rand () 
{
  unsigned res;
  rng.z = 36969 * (rng.z & 65535) + (rng.z >> 16);
  rng.w = 18000 * (rng.w & 65535) + (rng.w >> 16);
  res = (rng.z << 16) + rng.w;
  return res;
}

void init_rand_seed () 
{
  rng.w = 0;
  rng.z = ~rng.w;
  rng.w <<= 1;
  rng.z <<= 1;
  rng.w += 1;
  rng.z += 1;
  rng.w *= 2019164533u, rng.z *= 1000632769u;
}

unsigned s_gcd (unsigned a, unsigned b) {
  unsigned tmp;
  if (a < b) Swap (a, b);
  while (b) tmp = b, b = a % b, a = tmp;
  return a;
}

inline void find_relative_prime(unsigned & pos, unsigned & delta, unsigned mod)
{
      pos   = s_rand () % mod;
      delta = s_rand () % mod;
      if (!delta) delta++;
      while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
}

void Solver :: s_addliftbincls (Lit p, Lit q)
{ 
    if(hasBin(p,q)) return;
    vec<Lit> ps;
    ps.push(p);
    ps.push(q);
    if(!is_conflict(ps)) return;
    CRef cr = ca.alloc(ps, false);
    clauses.push(cr);
    attachClause(cr);
}

int Solver :: s_randomprobe (vec<int> & outer) 
{
  unsigned mod = outer.size();
  if (mod==0) return -1;
  unsigned pos = s_rand () % mod;
  int res = outer[pos];
  if (assigns[res] != l_Undef) return -1;
  return res;
}

int Solver :: s_innerprobe (int start, vec<int> & probes) 
{
  vec<int> tmp;
  for (int i = start; i < trail.size(); i++) {
         Lit lit = trail[i];
         vec<Watcher>&  trn  = watches[lit];
         for(int j = 0; j<trn.size(); j++) {
                 CRef cr=trn[j].cref;
                 Clause & c = ca[cr];
                 if(c.size() != 3) continue;
                 int m=0;
                 for(int k=0; k<3; k++)
                       if(value(c[k]) != l_Undef) m++;
                 if(m>1) continue;
                 for(int k=0; k<3; k++){
                       if(value(c[k]) == l_Undef){
                             int v = var(c[k]);
                             if(seen[v]) continue;
                             tmp.push(v);
                             seen[v]=1;
                      }
                 }
         } 
  }//found %d inner probes in ternary clauses", s_cntstk (tmp));
  int res = s_randomprobe (tmp);
  for (int i = 0; i < tmp.size(); i++) seen[tmp[i]]=0;
  if (res<0) res = s_randomprobe (probes);
  return res;
}

lbool Solver :: addeqvlist (vec <int> & equal)
{
     Lit p=toLit(equal[0]);
     for (int i = 1; i < equal.size(); i++) {
             Lit q=toLit(equal[i]);
             lbool ret = check_add_equ (p, q);
             if(ret == l_False) return l_False;
     }
     return l_Undef;
}       

//double depth unit probe
lbool Solver :: s_liftaux () 
{
  int i,outer,inner;
  unsigned pos, delta, mod;
  vec<int> probes, represented[2], equal[2];
  vec<Lit> saved; 
 
  for (int idx = 0; idx < nVars(); idx++) {
      if (assigns [idx] != l_Undef) continue;
      probes.push(idx);
  }
  mod = probes.size();
  if (mod<20) return l_Undef;
  find_relative_prime(pos, delta, mod);

  lbool ret=l_Undef;
  CRef confl;
  Lit inlit;
  int loop=mod-10;
  if(loop>10000) loop=10000;
  while ( --loop > 0 ) {
       outer = probes[pos];
       pos = (pos + delta) % mod;
       if (assigns[outer] != l_Undef ) continue;
        //1st outer branch %d during lifting, outer
       represented[0].clear();
       represented[1].clear();
       equal[0].clear();
       equal[1].clear();
       int oldtrailsize = trail.size();
       Lit outlit=mkLit(outer);
       newDecisionLevel();
       uncheckedEnqueue(outlit);
       confl = propagate();
       if (confl != CRef_Undef) {
FIRST_OUTER_BRANCH_FAILED:
           Lit dom = s_prbana(confl, outlit);
            //1st outer branch failed literal %d during lifting, outer
            cancelUntil(0);
            confl = unitPropagation(~dom);
            if (confl == CRef_Undef) continue;
            ret=l_False;
            break;
       }
       inner = s_innerprobe (oldtrailsize, probes);
       if (inner<0) {
FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE:
          //no inner probe for 1st outer probe %d", outer
           for (i = oldtrailsize; i < trail.size(); i++) represented[0].push(toInt(trail[i]));
           goto END_OF_FIRST_OUTER_BRANCH;
       }   //1st inner branch %d in outer 1st branch %d", inner, outer
       inlit =mkLit(inner);
       newDecisionLevel();
       uncheckedEnqueue(inlit);
       confl = propagate();
       if (confl != CRef_Undef) {//1st inner branch failed literal %d on 1st outer branch %d,inner, outer
               cancelUntil(0);
               s_addliftbincls (~outlit, ~inlit);
               newDecisionLevel();
               uncheckedEnqueue(outlit);
               confl = propagate();
               if (confl == CRef_Undef ) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
               goto FIRST_OUTER_BRANCH_FAILED; //conflict after propagating negation of 1st inner branch
        }
        saved.clear();
        for (i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
        cancelUntil(1);
        newDecisionLevel();
        uncheckedEnqueue(~inlit);
        confl = propagate();  //2nd inner branch %d in 1st outer branch %d", -inner, outer
        if (confl != CRef_Undef) {// 2nd inner branch failed literal %d on 1st outer branch %d,-inner, outer
               cancelUntil(0);
               s_addliftbincls (~outlit, inlit);
               newDecisionLevel();
               uncheckedEnqueue(outlit);
               confl = propagate();
               if (confl == CRef_Undef) goto FIRST_OUTER_BRANCH_WIHOUT_INNER_PROBE;
               goto FIRST_OUTER_BRANCH_FAILED;  // conflict after propagating negation of 2nd inner branch
        } 
        equal[0].push(toInt(inlit));
        while (saved.size()) {
               Lit lit = saved.pop_();
               if(value(lit) == l_True) represented[0].push(toInt(lit));
               else if(value(lit) == l_False && lit != inlit) equal[0].push(toInt(lit));
       }
END_OF_FIRST_OUTER_BRANCH:
       cancelUntil(0); // 2nd outer branch %d during lifting, -outer
       newDecisionLevel();
       uncheckedEnqueue(~outlit);
       CRef confl = propagate();
       if (confl != CRef_Undef) {
SECOND_OUTER_BRANCH_FAILED:
             Lit dom = s_prbana(confl, ~outlit);   //2nd branch outer failed literal %d during lifting, -outer
             cancelUntil(0);
             confl = unitPropagation(~dom);
             if (confl == CRef_Undef) continue;
             ret=l_False;
             break;
      }

      if (inner < 0 || value(inlit) != l_Undef ) 
              inner = s_innerprobe (oldtrailsize, probes);
      if (inner < 0) {
SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE:
              //no inner probe for 2nd outer branch %d", -outer
             for (i = oldtrailsize; i < trail.size(); i++) represented[1].push(toInt(trail[i]));
             goto END_OF_SECOND_BRANCH;
      }
  //1st inner branch %d in outer 2nd branch %d", inner, -outer
      inlit =mkLit(inner);
      newDecisionLevel();
      uncheckedEnqueue(inlit);
      confl = propagate();
      if (confl != CRef_Undef) {//1st inner branch failed literal %d on 2nd outer branch %d", inner, -outer
             cancelUntil(0);
             s_addliftbincls (outlit, ~inlit);
             newDecisionLevel();
             uncheckedEnqueue(~outlit);
             confl = propagate();
             if (confl == CRef_Undef) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
                     // conflict after propagating negation of 1st inner branch
             goto SECOND_OUTER_BRANCH_FAILED;
       }
       saved.clear();
       for (i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
       cancelUntil(1);
              // 2nd inner branch %d in 2nd outer branch %d", -inner, -outer
       newDecisionLevel();
       uncheckedEnqueue(~inlit);
       confl = propagate(); 
       if (confl != CRef_Undef) {// 2nd inner branch failed literal %d on 2nd outer branch %d", -inner, -outer
              cancelUntil(0);
              s_addliftbincls (outlit, inlit);
              newDecisionLevel();
              uncheckedEnqueue(~outlit);
              confl = propagate();
              if (confl == CRef_Undef ) goto SECOND_OUTER_BRANCH_WIHOUT_INNER_PROBE;
                  //conflict after propagating negation of 2nd inner branch
              goto SECOND_OUTER_BRANCH_FAILED;
       }
       equal[1].push(toInt(inlit));
       while (saved.size()) {
               Lit lit = saved.pop_();
               if(value(lit) == l_True) represented[1].push(toInt(lit));
               else if(value(lit) == l_False && lit != inlit) equal[1].push(toInt(lit));
       }
END_OF_SECOND_BRANCH:
       cancelUntil(0);
       for (i = 0; i < represented[0].size(); i++) mark[represented[0][i]]=1;
       mark[2*outer]=mark[2*outer+1]=0;
       for (i = 0; i < represented[1].size(); i++) {
               int ulit=represented[1][i]; 
               if(mark[ulit]){
                    if(assigns[ulit/2] != l_Undef) continue;

                    Lit q=toLit(ulit);
                    if(checkUnit (ulit, 'p')){//2017.1.17 bug?
                  unitq:
                         confl = unitPropagation(q);
                         if (confl == CRef_Undef) continue;
                         ret=l_False;
                         break;
                    }
                    else {
                        if(!out_binclause(outlit, q)) continue;
                        if(!out_binclause(~outlit, q)) continue;
                        goto unitq;
                    }
               }
               if(mark[ulit^1]){
                      Lit q=toLit(ulit^1);
                      ret = check_add_equ (outlit,q);// outlit => q
                      if(ret == l_False) break;
               }
      }
      for (i = 0; i < represented[0].size(); i++) mark[represented[0][i]]=0;
      if(ret == l_False) break;
// p => A=B, ~p => A=B   ==>  A=B       
      for (i = 0; i < equal[0].size(); i++) mark[equal[0][i]]=1;
      int eqn=0;
      for (i = 0; i < equal[1].size(); i++) if(mark[equal[1][i]]) eqn++;
      if(eqn < 2){
         eqn=0;
         for (i = 0; i < equal[1].size(); i++){
                  int notl=equal[1][i]^1;
                  equal[1][i]=notl;
                  if(mark[notl]) eqn++;
         }
      }
      for (i = 0; i < equal[0].size(); i++) mark[equal[0][i]]=0;
      if(eqn >= 2){
            ret=addeqvlist(equal[0]);
            if(ret == l_False) break;
            ret=addeqvlist(equal[1]);
            if(ret == l_False) break;
      }
  }
  return ret;
}

lbool Solver :: s_lift ()
{ 
  if (nVars()>500000) return l_Undef;
  cancelUntil(0);
  mark = (char * ) calloc (2*nVars()+1, sizeof(char));
  int oldeqn = equsum;
  lbool ret= s_liftaux ();
  free(mark);
  if(oldeqn != equsum && ret ==l_Undef) return replaceEqVar();
  return ret;
}

// simple lift or probe unit
lbool Solver :: s_probe ()
{ 
   Lit dom=lit_Undef, rootlit;
   unsigned pos, delta;
   vec <int> probes;
   vec <Lit> lift, saved;
   int nprobes,oldtrailsize;

   for (int idx = 0; idx < nVars(); idx++) {
      if (assigns [idx] != l_Undef) continue;
      probes.push(idx);
   }
   nprobes = probes.size();
   if (nprobes < 20) return l_Undef;
   find_relative_prime(pos, delta, nprobes);
 
   int units=0;
   cancelUntil(0);
   lbool ret=l_Undef;
   int loop=nprobes-10;
   if(loop>10000) loop=10000;

   while ( --loop > 0 ) {
        int root = probes[pos];
        pos = (pos+delta) % nprobes;
        if (assigns [root] != l_Undef) continue;
        lift.clear();
        saved.clear();
    //-------------------------level==0
       oldtrailsize = trail.size();
       rootlit=mkLit(root);
       newDecisionLevel();
       uncheckedEnqueue(rootlit);
       CRef confl = propagate();
       if (confl == CRef_Undef) {
          for (int i = oldtrailsize; i < trail.size(); i++) saved.push(trail[i]);
       } 
       else {
             dom = s_prbana(confl, rootlit);
       }
       cancelUntil(0);
       if (confl != CRef_Undef) {// failed literal %d on probing, dom, root
               lift.push(~dom);
               goto LUNIT;
       }// next probe %d negative phase, -root
    //---------------------------------------
       newDecisionLevel();
       uncheckedEnqueue(~rootlit);
       confl = propagate();
       if (confl == CRef_Undef) {
          for (int i = 0; i <saved.size(); i++) 
                if(value(saved[i]) == l_True ) lift.push(saved[i]);
       } 
       else  dom = s_prbana(confl, ~rootlit);
       cancelUntil(0);
   //------------------------------------------------
      if (confl != CRef_Undef) {// failed literal %d on probing %d, dom, -root
             lift.push(~dom);
      }
LUNIT:
      for (int i = 0; i < lift.size(); i++){
             if(value(lift[i]) != l_Undef) continue;
             if(checkUnit (toInt(lift[i]), 's')){
                   units++;
                   confl = unitPropagation(lift[i]);
                   if (confl == CRef_Undef) continue;
                   ret=l_False;
                   goto DONE;
             }
      }
  }
DONE:
  return ret;
}

lbool Solver :: distill() 
{
  unsigned int pos, i, bin, delta, ncls;
  ncls = clauses.size(); 
  vec<CRef>& cs = clauses;
  for (i = bin=0; i < ncls; i++){
        Clause& c = ca[cs[i]];
        if(c.size()>2) continue;
        if(bin != i ){
             CRef tmp = cs[bin];
             cs[bin]  = cs[i];
             cs[i]    = tmp;
        }
        bin++;
  }
 
  unsigned int mod=ncls-bin;
  if (!mod)  return l_Undef;
  pos   = s_rand () % mod;
  delta = s_rand () % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
 
  for (i = bin; i < ncls; i++){
        unsigned int k=bin+pos;
        CRef tmp= cs[i];
        cs[i]   = cs[k];
        cs[k]   = tmp;
        pos = (pos+delta) % mod;
  }
  lbool ret=distillaux(clauses, 0);
  return ret;
}

void Solver::distill_analyze(vec<Lit> & out_clause, Lit p)
{
    vec<Var> scan,visit;
    out_clause.push(p); 
    scan.push(var(p)); 
    seen[var(p)]=1;
    visit.push(var(p));
    while(scan.size()>0){
  	Var qv=scan.pop_();
        CRef  confl = reason(qv);
        if( confl != CRef_Undef ){
               Clause & c = ca[confl];
               for (int i =0; i < c.size(); i++){
                    p = c[i];
                    Var pv= var(p);    
                    if (seen[pv]) continue;
                    seen[pv]=1;
                    visit.push(pv);
                    if( reason(pv) != CRef_Undef) scan.push(pv);
                    else  out_clause.push(p);
                } 
         }
    }
    for (int v = 0; v<visit.size(); v++)  seen[visit[v]] = 0;
}

lbool Solver::distillaux(vec<CRef>& cls,int start)
{
    vec<Lit> newCls;
    int i,j,k,m=0;
    lbool ret=l_Undef;
    cancelUntil(0);
    if(start+30000 < cls.size()) start=cls.size()-30000;
    for (i = j = start; i < cls.size(); i++){
        if(ret!=l_Undef){
            cls[j++] = cls[i];
            continue;
        }
        Clause& c = ca[cls[i]];
        newCls.clear();
        int T=0;
        int csize=c.size();
        for (k = 0; k < csize; k++){
             Lit p=c[k];
             if (value(p) == l_True) { T=1; break;}
             if (value(p) == l_False)  continue;
             newCls.push(p);
        }
        if(T){
           removeClause(cls[i]);
           continue;
        }

        if(newCls.size()==csize && csize>2){
             for (int k=0; k<csize; k++){
                  Lit p = newCls[k];
                  if ( value(p) == l_False ) {
                         newCls[k]=newCls[csize-1];
                         newCls.shrink_(1);
                         break;
                  }
                  if (value(p) == l_True) {
                        if(k>=csize-1){
                           if(m<20000){
                              m++;
                              newCls.clear();
                              distill_analyze(newCls, p);
                          }
                        }
                        else  newCls.shrink_(csize-k-1);
                        break;
                  } 
                  newDecisionLevel();
                  uncheckedEnqueue(~p);
                  CRef confl = propagate();
                  if (confl != CRef_Undef) {
                      newCls.shrink_(csize-k-1);
                      break;
                 }
            }
            cancelUntil(0);
        }

       if(newCls.size()>=csize){
               cls[j++] = cls[i];
               continue;
       }
       if(newCls.size()==0){
              cls[j++] = cls[i];
              ret=l_False;
              continue;
       }
       if(newCls.size()==1){
              cls[j++] = cls[i];
              if( unitPropagation(newCls[0]) != CRef_Undef ) ret=l_False;
              unitsum++;
              continue;
       }
       removeClause(cls[i]);
       CRef cr = ca.alloc(newCls, false);
       attachClause(cr);
       cls[j++] = cr;
    }

    cls.shrink(i - j);
    checkGarbage();
    return ret; 
}

// find equivalent literals by 
//Tarjan's strongly connected components algorithm, dfsi: depth first search index
lbool Solver :: tarjan_SCC () 
{
  int * dfsimap, * min_dfsimap, lit;
  int dfsi, mindfsi, repr,olit;
  lbool ret=l_Undef;
  int nvar=nVars();

  dfsimap      = (int* ) calloc (2*nvar+1, sizeof(int));
  min_dfsimap  = (int* ) calloc (2*nvar+1, sizeof(int));
  dfsimap     += nvar;
  min_dfsimap += nvar;
  watchesBin.cleanAll();

  vec<int>  stk,component;
  stk.clear();  component.clear();
  dfsi = 0;
  int eqvNum=0;
  for (int idx = 1; idx <= nvar; idx++) {
     if(assigns[idx-1] != l_Undef) continue;
     for (int sign = -1; sign <= 1; sign += 2) {
        lit = sign * idx;
        if (dfsimap[lit]) continue;
        stk.push(lit);
        while (stk.size()>0) {
	    lit = stk.pop_();
            if (lit) {
	        if (dfsimap[lit]) continue;
	        dfsimap[lit] = min_dfsimap[lit] = ++dfsi;
	        component.push(lit);
	        stk.push(lit);
                stk.push(0);
		Lit Lt = makeLit(lit);
                vec<Watcher>&  bin  = watchesBin[Lt];
                for(int k = 0;k<bin.size();k++) {
	             Lit other = bin[k].blocker;
                     int olit = toIntLit(other);
                     if(dfsimap[olit]) continue;
	             stk.push(olit);
	        }  
            } 
            else {
	        lit = stk.pop_();
                mindfsi = dfsimap[lit];
		Lit Lt = makeLit(lit);
                vec<Watcher>&  bin  = watchesBin[Lt];
                for(int k = 0;k<bin.size();k++) {
	             Lit other = bin[k].blocker;
                     int olit = toIntLit(other);
                     if (min_dfsimap[olit] < mindfsi) mindfsi = min_dfsimap[olit];
	        }   
                if (mindfsi == dfsimap[lit]) {
                      repr = lit;
                      for (int k = component.size()-1; (olit =component[k]) != lit; k--) {
	                  if (ABS(olit) < ABS(repr)) repr = olit;
	              }
	              Lit p=makeLit(repr);
                      while ((olit = component.pop_()) != lit) {
	                   min_dfsimap[olit] = INT_MAX;
	                   if (olit == repr) continue;
	                   if (olit == -repr) {//empty clause 
                                 ret =l_False; 
	                          goto DONE;
                            }
                            Lit q=makeLit(olit);
                            ret = check_add_equ (p, q);
                            if(ret == l_False){
                                  goto DONE;
                            }
                            eqvNum++;
                      }
                      min_dfsimap[lit] = INT_MAX;
     	       } 
               else min_dfsimap[lit] = mindfsi;
	  }
        }
      }
  }
DONE:
  dfsimap     -= nvar;
  min_dfsimap -= nvar;
  free(dfsimap);
  free(min_dfsimap);
  if(ret == l_False) return ret;
  if(eqvNum>0){
      touchMark=0;   
      return replaceEqVar();
  }
  return l_Undef;
}

//delete taut binary clause
lbool Solver :: transitive_reduction () 
{ int i;
  unsigned int pos,delta,v,mod=nVars();
  if (mod<20)  return l_Undef;
  pos     = s_rand () % mod;
  delta = s_rand () % mod;
  if (!delta) delta++;
  while (s_gcd (delta, mod) > 1)   if (++delta == mod) delta = 1;
  int remflag=0;
  lbool ret=l_Undef;
  cancelUntil(0);
  i=nVars();
  if(i>5000) i=5000;
  for(; i>0; i--) {
        v= pos/2;
        if(assigns[v] == l_Undef){
             Lit lit = (pos & 1) ? mkLit(v) : ~mkLit(v);
             ret=trdlit (lit, remflag);
             if(ret != l_Undef) break;
        }
        pos = (pos+delta) % mod;
  }
  if(remflag) {
       cleanClauses(clauses);
       cleanClauses(learnts);
  }
  return ret;
}

lbool Solver :: trdlit (Lit start, int & remflag) 
{ 
  vec<Watcher>&  bin  = watchesBin[start];
  for(int k = 0;k<bin.size(); k++) {
         Lit target = bin[k].blocker;
         if (var (start) > var (target)) continue;
         CRef cr=bin[k].cref;
         Clause & c = ca[cr];
         if(c.mark()) continue;
         int ret = trdbin (start, target, c.learnt());
         if(ret < 0 ) return l_False;
         if(ret > 0 ) {
              removeClause(cr);
              remflag=1;
              break;
         }
  }
  return l_Undef;
}

int  Solver :: trdbin (Lit start, Lit target, int learntflag) 
{
  int res=0;  
  int ign=1;
  vec<Lit> scan;
  scan.push(start); 
  seen[var(start)]=2+sign(start);
  for(int i=0; i<scan.size(); i++){
       Lit lit = scan[i];
       if(assigns[var(lit)] != l_Undef) continue;
       vec<Watcher>&  bin  = watchesBin[lit];
       for(int k = 0;k<bin.size();k++) {
            Lit other = bin[k].blocker;
            CRef cr=bin[k].cref;
            Clause& c = ca[cr];
            if(c.mark()) continue;
            if(c.learnt() && learntflag==0) continue;
            if (other == start) continue;
            if (other == target) {
                 if (lit == start && ign) { ign = 0; continue; }
                 res = 1;
	         goto DONE;
            }
            int mark=2+sign(other);
            Var ov=var(other);
            if(seen[ov]==0){
                    seen[ov] = mark;
                    scan.push(other);
                    continue;
            } 
            if(seen[ov] != mark){
               if (value(start) != l_Undef) continue;
               newDecisionLevel();
               uncheckedEnqueue(start);
               CRef confl = propagate();
               if (confl == CRef_Undef) continue;
               cancelUntil(0);
               confl = unitPropagation(~start);
               if (confl != CRef_Undef) { res = -1; goto DONE;}
            } 
       }
  }        
DONE:
  for(int i=0; i<scan.size(); i++)  seen[var(scan[i])]=0;
  return res;
}

#define PUSHDF(POSNEG, n, LIT) \
do { \
  if(!dfpr[LIT].discovered) break; \
  POSNEG[n].ulit = LIT; \
  POSNEG[n].discovered = dfpr[LIT].discovered; \
  POSNEG[n++].finished = dfpr[LIT].finished; \
} while (0)

typedef struct DF { int discovered, finished; int ulit;} DF;
DF *pos_df,*neg_df;
 
int cmpdf (const void * a, const void * b)
{  DF * c =(DF *)a;
   DF * d =(DF *)b;
   return c->discovered - d->discovered;
}

typedef struct DFPR  { int discovered, finished, parent, root;} DFPR;
typedef struct DFOPF { int observed, pushed, flag;} DFOPF;
DFOPF * dfopf;
DFPR * dfpr=0;

typedef struct DFL {
  int discovered, finished;
  int lit, sign;
} DFL;

typedef enum Wrag {
  PREFIX = 0,
  BEFORE = 1,
  AFTER = 2,
  POSTFIX = 3,
} Wrag;

typedef struct Work {
  Wrag wrag : 2;
  int lit : 30;
  int other : 30;
  unsigned red : 1;
  unsigned removed : 1;
  CRef cr;
} Work;

lbool Solver :: s_eliminate ()
{   int loop;
    if( nVars() < 20 || nVars() > 500000) return l_Undef;
    mark = (char * ) calloc (2*nVars()+1, sizeof(char));
 
    cancelUntil(0);
    markNo=0;
    pos_df=neg_df=0;
    vscore.clear(true);

    lbool ret = l_Undef;
    
    fullwatch = new vec<CRef>[2*nVars()];
    buildfullwatch ();
              
    ret = s_hte ();
    if( ret != l_Undef )  goto DONE;
 
    s_eschedall();
    s_block ();
//  
    s_eschedall ();
    loop = sched_heap.size();
    if( loop > 20000) loop =20000;
    markNo = (int * ) calloc (nVars()+1, sizeof(int));
    pos_df = (DF *)malloc (1000*sizeof(DF));
    neg_df = (DF *)malloc (1000*sizeof(DF));
   
    while ( --loop > 0){
        if (sched_heap.empty()) goto DONE;
        int v = sched_heap.removeMin();
        if(vscore[v]>160) continue;
        if (assigns[v] == l_Undef && decision[v]){
             ret = s_elimlit (v);
             if( ret != l_Undef ) goto DONE;
        }
   }

DONE:
  if (dfpr) free(dfpr);
  if(markNo) free(markNo);
  if(pos_df){
       free(pos_df);
       free(neg_df);
  }
  sched_heap.clear(true);
  vscore.clear(true);
  delete [] fullwatch;
  free(mark);
 
  cleanClauses(clauses);
  cleanNonDecision();
  return ret;
}

// probing analysis returns 1st UIP
Lit Solver::s_prbana(CRef confl, Lit res)
{
    vec<Var> scan;
    int tpos=trail.size();
    int open=0;
    while(tpos>0){
          Clause & c = ca[confl];
          for (int i =0; i < c.size(); i++){
                 Var pv= var(c[i]);    
                 if (seen[pv]) continue;
                 if(level(pv) > 0 ) {
                        seen[pv]=1;
                        scan.push(pv);
                        open++;
                 }
          }
          while(tpos>0){
                tpos--;
                if(seen[var(trail[tpos])]) break;
          }
          open--;
          if(open==0) {           
                res = trail[tpos];
                break;
          }     
          confl = reason(var(trail[tpos]));
    }
    for (int i = 0; i<scan.size(); i++)  seen[scan[i]] = 0;
    return res;
}

int Solver :: checkUnit (int uLit, char printflag)
{
     Lit unit=toLit(uLit^1);
     if(value(unit) == l_False) return 1;
     if(value(unit) == l_Undef) {
            newDecisionLevel();
            uncheckedEnqueue(unit);
            CRef confl = propagate();
            cancelUntil(0);
            if (confl != CRef_Undef) return 1;
     }
     return 0;
}

CRef Solver::unitPropagation(Lit p)
{
     uncheckedEnqueue(p);
     return propagate();
}

lbool Solver :: check_add_equ (Lit p, Lit q)
{
    if( p == q) return l_Undef;
    if( p == ~q ) return l_False;
    if(!out_binclause(p,  ~q)) return l_Undef;
    if(!out_binclause(~p, q)) return l_Undef;
    return add_equ_link(toInt(p), toInt(q));
}

bool Solver:: out_binclause(Lit p, Lit q)
{
      if(hasBin(p,q)) return true;
      vec<Lit> ps;
      ps.clear();
      ps.push(p);
      ps.push(q);
      if(is_conflict(ps)) return true;
      return false;
}

lbool Solver:: add_equ_link(int pul, int qul)
{
    if(equhead == 0) equhead = (int * ) calloc (nVars()+1, sizeof(int));
    if(equlink == 0) equlink = (int * ) calloc (nVars()+1, sizeof(int));

    if( pul < qul){
       int t=pul;  pul=qul;  qul=t;
    }
    int pl=toIntLit(toLit(pul));
    int ql=toIntLit(toLit(qul));

    if(pl<0){ pl=-pl; ql=-ql; }
    int qv=ABS(ql);
    if(equhead[pl] == equhead[qv]){
        if(equhead[pl] == 0){
           equhead[pl]=ql; equhead[qv]=qv;
           equlink[qv]=pl;
           equsum++;
           return l_Undef;
        }
        if(ql < 0) return l_False;
        return l_Undef;
    }
    if(equhead[pl] == -equhead[qv]){
        if(ql < 0) return l_Undef;
        return l_False;
    }
    equsum++;
    if(equhead[pl] == 0 && equhead[qv]){
        if(ql < 0) equhead[pl]=-equhead[qv];
        else equhead[pl]=equhead[qv];
        int h=ABS(equhead[pl]);
        int t = equlink[h];
        equlink[h]=pl;
        equlink[pl]=t;
        return l_Undef;
    }
    if(equhead[pl] && equhead[qv]==0){
        if(ql < 0) equhead[qv]=-equhead[pl];
        else equhead[qv]=equhead[pl];
        int h=ABS(equhead[qv]);
        int t = equlink[h];
        equlink[h]=qv;
        equlink[qv]=t;
        return l_Undef;
    }
//merge
    int x=equhead[pl];
    int y=equhead[qv];
    if(ql < 0) y=-y;
    int next=ABS(y);
    while(1){
         if(equhead[next]==y) equhead[next]=x;
         else  equhead[next]=-x;
         if(equlink[next]==0) break;
         next=equlink[next];
    }    
    int xh=ABS(x);
    int t=equlink[xh];
    equlink[xh]=ABS(y);
    equlink[next]=t;
    return l_Undef;
}

bool Solver :: is_conflict(vec<Lit> & lits)
{  
   cancelUntil(0);
   int i;
   for (i=0; i<lits.size(); i++){
        Lit p = ~lits[i];
        if ( value(p) == l_True) continue;
        if ( value(p) == l_False) break;
        newDecisionLevel();
        uncheckedEnqueue(p);
        CRef confl = propagate();
        if (confl != CRef_Undef) break;
   }
   cancelUntil(0);
   if(i<lits.size()) return true;
   return false;
}

bool Solver :: is_conflict(Lit p, Lit q)
{
      vec<Lit> ps;
      ps.push(p);
      ps.push(q);
      return is_conflict(ps);
}

lbool Solver::replaceEqVar()
{  
     watches.cleanAll();
     watchesBin.cleanAll();
     if(equhead==0) return l_Undef;

     lbool ret=removeEqVar(clauses, false);
     if(ret == l_False) return l_False;
     ret=removeEqVar(learnts, true);
     watches.cleanAll();
     watchesBin.cleanAll();
     return ret;
}

void Solver ::cleanClauses(vec<CRef>& cls)
{
    int i,j;
    for (i = j = 0; i < cls.size(); i++)
        if (ca[cls[i]].mark() == 0) cls[j++] = cls[i];
    cls.shrink(i - j);
}

void Solver :: cleanNonDecision()
{   int i,j;
    for (i = j = 0; i < learnts.size(); i++){
        CRef cr=learnts[i];
        Clause & c = ca[cr];
        if (c.mark()) continue;
        for (int k = 0; k < c.size(); k++){
             if (value(c[k]) == l_True || !decision[var(c[k])]) {
                    removeClause(cr);
                    goto NEXT;
             }
        }
        learnts[j++] = cr;
    NEXT: ;
    }   
    learnts.shrink(i -j);
}

inline void Solver :: update_score(int ulit)
{
      int v=ulit/2;
      int pos=fullwatch[ulit].size();
      int neg=fullwatch[ulit^1].size();
      if(sched_heap.inHeap(v)){
            int old=vscore[v];
            if( !pos  || !neg ) vscore[v] = 0;
            else if(pos < 10000 && neg < 10000) vscore[v] = pos*neg;
                 else vscore[v]=10000000;
            if(old > vscore[v]) sched_heap.decrease(v);
            if(old < vscore[v]) sched_heap.increase(v);
      }
      else{
        if(decision[v] && (pos+neg) < 16){
             if(vscore[v] > pos*neg && pos+neg>6){
                   vscore[v] = pos*neg;
                   sched_heap.insert(v);
             }
        } 
     }
}        

void Solver::removefullclause(CRef cr) 
{
  Clause& c = ca[cr];
  for(int i=0; i<c.size(); i++){
        int ulit=toInt(c[i]);
        remove(fullwatch[ulit], cr);
        if(vscore.size()>=nVars()) update_score(ulit);
  }
  removeClause(cr);
}

void Solver :: s_addfullcls (vec<Lit> & ps, int learntflag)
{ 
    CRef cr = ca.alloc(ps, learntflag);
    if(!learntflag) clauses.push(cr);
    else            learnts.push(cr);
    for(int i=0; i<ps.size(); i++) {
             int ulit=toInt(ps[i]);
             fullwatch[ulit].push(cr);
             if(vscore.size()>=nVars()) update_score(ulit);
    }
    attachClause(cr);
}

void Solver :: buildfullwatch ()
{
    for (int i =0; i < 2*nVars(); i++) fullwatch[i].clear();
    for (int i =0; i < clauses.size(); i++){
        CRef cr =clauses[i];
        Clause& c = ca[cr];
        if (c.mark()==1) continue;
        for(int j=0; j<c.size(); j++) fullwatch[toInt(c[j])].push(cr);
    }
}
//Hidden Tautology Elimination
//hidden literal addition
lbool Solver :: s_hte () //need remove learnt clauses
{ 
  unsigned int nlits = 2*nVars();
  if (nlits <= 40) return l_Undef;
 
  unsigned pos, delta; 
  find_relative_prime(pos, delta, nlits);
  lbool ret;
  vec <Lit> scan;
  vec <Lit> newCs;
  int limit= nlits/2;
  if(limit>10000) limit=10000; 
  vec <CRef> bigCr;
  int lsize;
  for(; limit>0; limit--) {
       Lit root = toLit(pos);
       if ( value(root) != l_Undef) goto CONTINUE;
       ret=s_hla(~root,scan); // root -> a^b^c.....
       if(ret != l_Undef) goto CONTINUE;
       lsize  = fullwatch[pos].size();
       bigCr.clear();
       for(int j = 0; j<lsize; j++) bigCr.push(fullwatch[pos][j]);
       for(int j = 0; j<bigCr.size(); j++){
              CRef cr=bigCr[j];
              Clause & c = ca[cr];
              if(c.mark()==1 || c.size()<3) continue;
              int taut=0;
              newCs.clear();
              newCs.push(root);
              for(int k=0; k<c.size(); k++){
                    if( c[k] == root) continue;
                    int ulit=toInt(c[k]);
                    if(mark[ulit]){
                         taut=1;
                         break;
                    }
                    if(mark[ulit^1]==0) newCs.push(c[k]);
              }
              if(taut==0){
                   if(newCs.size()==1){
                        if(checkUnit (toInt(newCs[0]), 'u')){
                            CRef confl = unitPropagation(newCs[0]);
                            if (confl != CRef_Undef) ret=l_False;
                         }
                         goto CONTINUE;
                   }
                   if(newCs.size() < c.size()) {
                              s_addfullcls (newCs, c.learnt());
                   }
              }
              if( newCs.size() < c.size()) {
                   removefullclause(cr);
              }
      }
CONTINUE:
       for(int j = 0; j<scan.size(); j++) mark[toInt(scan[j])]=0;
       if(ret == l_False ) return l_False;
       pos = (pos+delta) % nlits;
  }
  return l_Undef;
}

void Solver ::  s_eschedall() 
{   int nV=nVars();
    vscore.growTo(nV);
    sched_heap.clear();
    for(int v=0; v<nV; v++){
          if (assigns[v] == l_Undef && decision[v]){
              int pos=fullwatch[2*v].size();
              int neg=fullwatch[2*v+1].size();
              if( !pos  || !neg ) vscore[v] = 0;
              else  if(pos < 10000 && neg < 10000) vscore[v] = pos*neg;
                    else continue;
             sched_heap.insert(v);
         }
    }
}

void Solver :: s_block () 
{
  int count = 0;
  int loop = sched_heap.size();
  if( loop > 20000) loop =20000;
  while ( --loop > 0 && count <10000){
        if (sched_heap.empty()) return;
        int v = sched_heap.removeMin();
        if ( assigns [v] != l_Undef ) continue;
        count += s_blocklit (2*v);
        count += s_blocklit (2*v+1);
  }
}

typedef struct ELM_CLAUSE { CRef cr; int size; unsigned csig;} ELM_CLAUSE;
vec <ELM_CLAUSE> eclsInfo; //elim clause info

vec <int> elm_m2i, clv;
 
static const uint64_t s_basevar2funtab[6] = {
  0xaaaaaaaaaaaaaaaaull, 0xccccccccccccccccull, 0xf0f0f0f0f0f0f0f0ull,
  0xff00ff00ff00ff00ull, 0xffff0000ffff0000ull, 0xffffffff00000000ull,
};

// mapped external variable to marked variable
int Solver :: s_s2m (int ulit) 
{  int v=ulit/2;
   int res = markNo[v];
   if (!res) {
       elm_m2i.push(v); 
       res = elm_m2i.size();
       if (res > 11) return 0;
       markNo[v] = res;
  }
  return 2*res + (ulit%2);
}

// mapped external variable to marked variable
int Solver :: s_i2m (int ulit) 
{  int v=ulit/2;
   int res = markNo[v];
   if (!res) {
        elm_m2i.push(v);
        res = elm_m2i.size();
        markNo[v] = res;
  }
  return 2*res - 2 + (ulit%2);
}

// map marked variable to external variable
int Solver :: s_m2i (int mlit) {
  int res, midx = mlit/2;
  res = elm_m2i[midx-1];
  return 2*res + (mlit%2);
}

void s_var2funaux (int v, Fun res, int negate) {
  uint64_t tmp;
  int i, j, p;
  if (v < 6) {
    tmp = s_basevar2funtab[v];
    if (negate) tmp = ~tmp;
    for (i = 0; i < FUNQUADS; i++) res[i] = tmp;
  } else {
    tmp = negate ? ~0ull : 0ull;
    p = 1 << (v - 6);
    j = 0;
    for (i = 0; i < FUNQUADS; i++) {
      res[i] = tmp;
      if (++j < p) continue;
      tmp = ~tmp;
      j = 0;
    }
  }
}

static Cnf s_pos2cnf (int pos)  { return pos; }
static Cnf s_size2cnf (int s)   { return ((Cnf)s) << 32; }
static int s_cnf2pos (Cnf cnf)  { return cnf & 0xfffffll; }
static int s_cnf2size (Cnf cnf) { return cnf >> 32; }
static Cnf s_cnf (int pos, int size) {
  return s_pos2cnf (pos) | s_size2cnf (size);
}

void s_negvar2fun (int v, Fun res) {  s_var2funaux (v, res, 1);}
void s_var2fun (int v, Fun res)    {  s_var2funaux (v, res, 0);}

void s_s2fun (int marklit, Fun res) 
{
  int sidx = marklit/2 - 2;
  if ( marklit & 1 ){
        s_negvar2fun (sidx, res);
  }
  else {
       s_var2fun (sidx, res);
  }
}

static void s_orfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++) a[i] |= b[i];
}

static void s_andfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] &= b[i];
}

static void s_or3fun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)  a[i] = b[i] | c[i];
}

static void s_and3negfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] = b[i] & ~c[i];
}

static void s_and3fun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] = b[i] & c[i];
}

static void s_andornegfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)    a[i] &= b[i] | ~c[i];
}

static void s_funcpy (Fun dst, const Fun src) {
  for (int i = 0; i < FUNQUADS; i++) dst[i] = src[i];
}

static void s_ornegfun (Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++) a[i] |= ~b[i];
}

static void s_slfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = FUNQUADS - 1;
  i = j - q;
  l = 64 - b;
  while (j >= 0) {
    if (i >= 0) {
      tmp = a[i] << b;
      rest = (b && i > 0) ? (a[i-1] >> l) : 0ll;
      a[j] = rest | tmp;
    } else a[j] = 0ll;
    i--, j--;
  }
}

static void s_srfun (Fun a, int shift) {
  uint64_t rest, tmp;
  int i, j, q, b, l;
  b = shift & 63;
  q = shift >> 6;
  j = 0;
  i = j + q;
  l = 64 - b;
  while (j < FUNQUADS) {
    if (i < FUNQUADS) {
      tmp = a[i] >> b;
      rest = (b && i+1 < FUNQUADS) ? (a[i+1] << l) : 0ull;
      a[j] = rest | tmp;
    } else a[j] = 0ull;
    i++, j++;
  }
}

static void s_falsefun (Fun res) {
  for (int i = 0; i < FUNQUADS; i++)   res[i] = 0ll;
}

static void s_truefun (Fun res) {
  for (int i = 0; i < FUNQUADS; i++)
    res[i] = (unsigned long long)(~0ll);
}

static int s_isfalsefun (const Fun f) {
  for (int i = 0; i < FUNQUADS; i++)    if (f[i] != 0ll) return 0;
  return 1;
}

static int s_istruefun (const Fun f) {
  for (int i = 0; i < FUNQUADS; i++) if (f[i] != (unsigned long long)(~0ll)) return 0;
  return 1;
}

static void s_negcofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);            //mask <- v
  s_and3negfun (masked, f, mask); //masked = f & ~mask;
  s_funcpy (res, masked);         //res <-masked
  s_slfun (masked, (1 << v));     // masked << v
  s_orfun (res, masked);          // res = res | masked
}

static void s_poscofactorfun (const Fun f, int v, Fun res) {
  Fun mask, masked;
  s_var2fun (v, mask);     //mask <- v
  s_and3fun (masked, f, mask); // //masked = a[i] = f & v
  s_funcpy (res, masked);      
  s_srfun (masked, (1 << v)); //// masked >> v
  s_orfun (res, masked);   // res = res | masked
}

static int s_eqfun (const Fun a, const Fun b) {
  for (int i = 0; i < FUNQUADS; i++)    if (a[i] != b[i]) return 0;
  return 1;
}

static int s_smalltopvar (const Fun f, int min) {
  Fun p, n;
  int v;
  for (v = min; v < FUNVAR; v++) {
    s_poscofactorfun (f, v, p);
    s_negcofactorfun (f, v, n);
    if (!s_eqfun (p, n)) return v;
  }
  return v;
}

static void s_or3negfun (Fun a, const Fun b, const Fun c) {
  for (int i = 0; i < FUNQUADS; i++)  a[i] = b[i] | ~c[i];
}

static void s_smallevalcls (unsigned cls, Fun res) {
  Fun tmp;
  int v;
  s_falsefun (res);
  for (v = 0; v < FUNVAR; v++) {
    if (cls & (1 << (2*v + 1))) {
      s_var2fun (v, tmp);
      s_ornegfun (res, tmp);
    } else if (cls & (1 << (2*v))) {
      s_var2fun (v, tmp);
      s_orfun (res, tmp);
    }
  }
}

static void s_smallevalcnf (Cnf cnf, Fun res) {
  Fun tmp;
  int i, n, p, cls;
  p = s_cnf2pos (cnf);
  n = s_cnf2size (cnf);
  s_truefun (res);
  for (i = 0; i < n; i++) {
    cls = clv[p + i];
    s_smallevalcls (cls, tmp);
    s_andfun (res, tmp);//res = res & cls
  }
}

static Cnf s_smalladdlit2cnf (Cnf cnf, int lit) {
  int p, m, q, n, i, cls;
  Cnf res;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  q = clv.size();
  for (i = 0; i < m; i++) {
    cls = clv[p + i];
    cls |= lit;
    clv.push(cls);
  }
  n = clv.size() - q;
  res = s_cnf (q, n);
  return res;
}

#define FALSECNF	(1ll<<32)
#define TRUECNF		0ll

static Cnf s_smallipos (const Fun U, const Fun L, int min) {
  Fun U0, U1, L0, L1, Unew, ftmp;
  Cnf c0, c1, cstar, ctmp, res;
  int x, y, z;
  if (s_istruefun (U)) return TRUECNF;  //U=11111
  if (s_isfalsefun (L)) return FALSECNF;//U=00000
  y = s_smalltopvar (U, min);
  z = s_smalltopvar (L, min);
  x = (y < z) ? y : z;

  s_negcofactorfun (U, x, U0); // U0 = U & ~x 
  s_poscofactorfun (U, x, U1); // U1 = U & x
  
  s_negcofactorfun (L, x, L0); // L0 = L & ~x
  s_poscofactorfun (L, x, L1); // L1 = L & x

  s_or3negfun (ftmp, U0, L1); // ftmp = U0 | ~L1 => ftmp = (U & ~x) | ~(L & x)  
  c0 = s_smallipos (ftmp, L0, min+1);    // L0= L & ~x

  s_or3negfun (ftmp, U1, L0); // ftmp = U1 | ~L0 => ftmp = (U & x) | ~(L & ~x)
  c1 = s_smallipos (ftmp, L1, min+1);

  s_smallevalcnf (c0, ftmp);     // ftmp <- c0
  s_or3negfun (Unew, U0, ftmp); // Unew = U0 | ~c0;
 
  s_smallevalcnf (c1, ftmp);
  s_andornegfun (Unew, U1, ftmp); // Unew = Unew & (U1 | ~c1);

  s_or3fun (ftmp, L0, L1);//ftmp = L0 | L1
  cstar = s_smallipos (Unew, ftmp, min+1);

  ctmp = s_smalladdlit2cnf (c1, (1 << (2*x + 1)));
  res = s_cnf2pos (ctmp);

  ctmp = s_smalladdlit2cnf (c0, (1 << (2*x)));
  if (res == TRUECNF) res = s_cnf2pos (ctmp);

  ctmp = s_smalladdlit2cnf (cstar, 0);
  if (res == TRUECNF) res = s_cnf2pos (ctmp);

  res |= s_size2cnf (clv.size() - res);
  return res;
}

int Solver :: s_smallisunitcls (int cls) {
  int fidx, fsign, flit, ulit;
  ulit = -1;
  for (fidx = 0; fidx < FUNVAR; fidx++)
    for (fsign = 0; fsign <= 1; fsign++) {
      flit = 1<<(2*fidx + fsign);
      if (!(cls & flit)) continue;
      if (ulit>=0) return -1;
      int mlit = (fidx + 2) * 2 + fsign;
      ulit = s_m2i (mlit);
  }
  return ulit;
}

int Solver :: s_smallcnfunits (Cnf cnf) 
{
  int p, m, i, cls, ulit;
  p = s_cnf2pos (cnf);
  m = s_cnf2size (cnf);
  int units = 0;
  for (i = 0; i < m; i++) {
      cls = clv[p + i];
      ulit = s_smallisunitcls (cls);
      if (ulit < 0) continue;
      units++;
  }
  return units;
}

int Solver ::s_smallvccheck (int v) 
{
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   int pivot = (pos <= neg) ? (2*v) : (2*v+1);
   int npivot = pivot^1;
   vec<CRef> &  pcs  = fullwatch[pivot];
   vec<CRef> &  ncs  = fullwatch[npivot];
   Lit plit=toLit(pivot);
   Lit nlit=~plit;
   int oldsz=pcs.size()+ncs.size();
   int newsz=0;
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        Clause& a = ca[pcr];
        for(int k = 0; k < a.size(); k++){
               if (a[k] == plit) continue;
               mark[toInt(a[k])]=1;
        }
        for(int j = 0; j < ncs.size(); j++){
               CRef ncr=ncs[j];
               Clause & b = ca[ncr];
               for(int k = 0; k < b.size(); k++){
                     if (b[k] == nlit) continue;
                     int ul=toInt(b[k]);
                     if (mark[ul]) continue;
                     if (mark[ul^1]) goto NEXT;
               }
               newsz++;
               if(newsz>=oldsz) goto DONE;
        NEXT: ;
        } 
  DONE:
        for(int k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
        if(newsz>=oldsz) return newsz;
   }
   return newsz;
}

lbool Solver :: s_smallve (Cnf cnf, int pivotv, bool newaddflag) 
{
  int cls, v, trivial;
  vec <Lit> newCls;
  int end=s_cnf2pos (cnf)+s_cnf2size (cnf);
  int elimFlag=1;
  int count=0;
  for (int i = end-1; i >= s_cnf2pos (cnf); i--) {
     cls = clv[i];
     trivial = 0;
     newCls.clear();
     for (v = 0; v < FUNVAR; v++) {
         int ulit;
         if (cls & (1 << (2*v + 1)))  ulit = s_m2i (2*v+5);
         else if (cls & (1 << (2*v))) ulit = s_m2i (2*v+4);
              else continue;
         Lit lit=toLit(ulit);
         if (value (lit) == l_False) continue;
         if (value (lit) == l_True) trivial = 1;
         newCls.push(lit);
     }
     if (!trivial) {//small elimination resolvent
          count++;
          if(newCls.size()>1) {
              if(newaddflag) s_addfullcls (newCls, 0);
          }
          else {
             if(newCls.size()==1){
                  if(checkUnit (toInt(newCls[0]), 's')){
                      CRef confl = unitPropagation(newCls[0]);
                      if (confl != CRef_Undef) return l_False;
                  }
                  else elimFlag=0;
             }
             else elimFlag=0;
          } 
     }
  }
  if(elimFlag && count && newaddflag){
      s_epusheliminated (pivotv);
  }
  return l_Undef;
}

// init eliminate clause
int Solver :: s_initecls (int v) 
{
   eclsInfo.clear();
   elm_m2i.clear();
   neglidx = fullwatch[2*v].size();
  
  if(!s_ecls (2*v)) return 0;
  if(!s_ecls (2*v+1)) return 0;
  return 1;
}

unsigned s_sig (int ulit) 
{
  unsigned res = (1u << (ulit & 31));
  return res;
}

int Solver :: s_addecl (CRef cr, Lit pivot)
{
    unsigned csig = 0;
    Clause& c = ca[cr];
    int idx=eclsInfo.size();
    eclsInfo.push();
    eclsInfo[idx].cr=cr;
    eclsInfo[idx].size=c.size();
    for(int i = 0; i < c.size(); i++){
          if( pivot == c[i] ) continue;
          int ul=toInt(c[i]);
          int markedlit = s_i2m (ul);
          if(markedlit>1000) return 0;
          csig |= s_sig (markedlit);
    }
    eclsInfo[idx].csig = csig;
    return 1;
}

int Solver :: s_ecls (int ulit) 
{
   int occNum = fullwatch[ulit].size();
   vec<CRef> &  crs  = fullwatch[ulit];
   Lit lit=toLit(ulit);
   for(int i = 0; i < occNum; i++){
         if(!s_addecl (crs[i], lit)) return 0;
   }
   return 1;
}

inline void Solver :: clearMarkNO()
{ 
   for(int i=0; i<elm_m2i.size(); i++) markNo[elm_m2i[i]]=0;
   elm_m2i.clear();
}   

// trying to eliminate v
lbool Solver :: s_elimlit (int v) 
{
     if (!s_chkoccs4elm (v)) return l_Undef;
     int success=0;
     lbool ret=l_Undef;
     int pos=fullwatch[2*v].size();
     int neg=fullwatch[2*v+1].size();
     if(pos==0 && neg==0) return l_Undef;
     deletedCls.clear();
     if(pos==0 || neg==0){
         s_epusheliminated (v);
         goto DONE;
     }
     ret = s_trysmallve (v, success);
     clearMarkNO();
     if(success || ret == l_False) goto DONE;

    if(s_initecls (v)){
          ret=s_elimlitaux (v);
   }

DONE: 
     clearMarkNO();
     for(int i=0; i<deletedCls.size(); i++) {
          CRef cr=deletedCls[i];
          if(ca[cr].mark()==0) removefullclause(cr);
     }
   
     deletedCls.clear();
     eclsInfo.clear();
     return ret;
}

lbool Solver::removeEqVar(vec<CRef>& cls, bool learntflag)
{
    vec<Lit> newCls;
    int i, j,k,n;

    lbool ret=l_Undef;
  
    for (i = j = 0; i < cls.size(); i++){
        Clause& c = ca[cls[i]];
        if(c.mark()) continue;
        if(ret!=l_Undef){
            cls[j++] = cls[i];
            continue;
        }
        newCls.clear();
        int T=0;
        int del=0;
        for (k = 0; k < c.size(); k++){
             Lit p=c[k];
             if (value(p) == l_True) {
                    del=T=1; 
                    break;
             }
             if (value(p) == l_False){
                     del=1; 
                     continue;
             }
             int v = var(p)+1;
             Lit q;
             if(equhead[v]==0 || equhead[v]==v) q=p;
             else{ int lit;
                 if(sign(p)) lit = -equhead[v];
                 else        lit = equhead[v];
                 q = (lit>0) ? mkLit(lit-1) : ~mkLit(-lit-1);
                 del=1;
            }
             if(del){
                for(n=newCls.size()-1; n>=0; n--){
                   if( q  == newCls[n]) break;
                   if( ~q == newCls[n]) {T=1; break;}
                }
             }
             else n=-1;
             if(T) break;
             if(n<0) newCls.push(q);
        }
        if(del==0){
            cls[j++] = cls[i];
            continue;
        }
        if(T){
           removeClause(cls[i]);
           continue;
        }
        if(touchMark && newCls.size()<3){
            for (k = 0; k < newCls.size(); k++) touchMark[var(newCls[k])]=1;
        }
        if(newCls.size()==0){
              cls[j++] = cls[i];
              ret=l_False;
              continue;
       }
       if(newCls.size()==1){
              removeClause(cls[i]);
              if( unitPropagation(newCls[0]) != CRef_Undef ) ret=l_False;
              unitsum++;
              continue;
       }
       removeClause(cls[i]);
       CRef cr = ca.alloc(newCls, learntflag);
       attachClause(cr);
       cls[j++] = cr;
    }
    cls.shrink(i - j);
    checkGarbage();
    return ret; 
}

// hidden literal addition 
lbool Solver :: s_hla (Lit start,  vec <Lit> & scan) 
{
  scan.clear();
  scan.push(start);
  mark[toInt(start)]=1;
  //starting hidden literal addition start
  for(int next=0; next < scan.size() && next<1000; next++) {
          Lit lit = scan[next];
	  vec<Watcher>&  bin  = watchesBin[lit];
          for(int k = 0;k<bin.size();k++) {
                 Lit other = bin[k].blocker;
                 if( value(other) != l_Undef) continue;
                 int uo=toInt(other);
                 if ( mark[uo] ) continue;
                 if ( mark[uo^1]) {
                  	// failed literal %d in hidden tautology elimination, start
                      if(checkUnit (toInt(start)^1, 'h')){
                          CRef confl = unitPropagation(~start);
                          if (confl != CRef_Undef) return l_False;
                          return l_True;
                       }
                 }
                 mark[uo]=1;
                 scan.push(other);
          }
  }
  return l_Undef;
}

int Solver :: s_blocklit (int pivot) 
{
   int occNum = fullwatch[pivot].size();
   if(occNum == 0 || occNum >1500) return 0;

   vec<int> scan;
   vec<CRef> blockedcls;
   vec<CRef> &  crs  = fullwatch[pivot];
   Lit lit=toLit(pivot);
   for(int i = 0; i < occNum; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        int blocked = 0;
        scan.clear();
        int size =0;
        for(int j = 0; j < c.size(); j++){
               if (c[j] == lit) continue;
               if(fullwatch[toInt(c[j])].size() >1000) goto CONTINUE;
               if (++size > 1500) goto CONTINUE;
               int ul=toInt(c[j]);
                scan.push(ul);
	        mark[ul]=1;
        }
        blocked = s_blockcls (pivot^1);
CONTINUE:
        for(int k = 0; k < scan.size(); k++) mark[scan[k]]=0;
        if (blocked==0) continue;
       blockedcls.push(cr);
  }   
  int count = blockedcls.size();
  for(int i=0; i < count; i++){
        CRef cr=blockedcls[i];
        removefullclause(cr);
        Clause & c = ca[cr];
        extendRemLit.push (lit_Undef);
        extendRemLit.push (lit);
        for(int j = 0; j < c.size(); j++){
               if (c[j] == lit) continue;
               extendRemLit.push(c[j]);
        }
  }
  return count;
}

int Solver :: s_chkoccs4elmlit (int ulit) 
{
   vec <CRef> &  cs  = fullwatch[ulit];
   int sz=cs.size();
   for (int i = 0; i<sz; i++) {
         CRef cr=cs[i];
         Clause& c = ca[cr];
         int size = 0;
         for(int j=c.size()-1; j>=0; j--){
             if(fullwatch[toInt(c[j])].size() > 800) return 0;
             if (++size > 600) return 0;
         }
   }
   return 1;
}

int Solver :: s_chkoccs4elm (int v) 
{
   if(fullwatch[2*v].size()   > 800) return 0;
   if(fullwatch[2*v+1].size() > 800) return 0;
   if (!s_chkoccs4elmlit (2*v)) return 0;
   return s_chkoccs4elmlit (2*v+1);
}

void Solver :: s_epusheliminated (int v) 
{ 
   setDecisionVar(v, false);
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   deletedCls.clear();
   if(pos==0 && neg==0) return;
   int ulit= (pos <= neg) ? (2*v) : (2*v+1);
   vec<CRef> &  pcs  = fullwatch[ulit];
   Lit pivot=toLit(ulit);
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        deletedCls.push(pcr);
        Clause& c = ca[pcr];
        extendRemLit.push (lit_Undef);
        extendRemLit.push(pivot);
        for(int k = 0; k < c.size(); k++){
               if (c[k] == pivot) continue;
               extendRemLit.push(c[k]);
        }
  }
  extendRemLit.push (lit_Undef);
  extendRemLit.push(~pivot);
  vec<CRef> &  ncs  = fullwatch[ulit^1];
  for(int i = 0; i < ncs.size(); i++) deletedCls.push(ncs[i]);
}

lbool Solver :: s_trysmallve (int v, int & res) 
{
  int newsz, old, units;
  Fun pos, neg, fun;
  Cnf cnf;

  elm_m2i.clear();
  clv.clear();
  clv.push(0);
  res = 0;
//too many variables for small elimination
  if (s_initsmallve (2*v, pos) && s_initsmallve (2*v+1, neg)) {
        s_or3fun (fun, pos, neg); //fun = pos | neg
        cnf = s_smallipos (fun, fun, 0);
        newsz = s_cnf2size (cnf);
        units = s_smallcnfunits (cnf);
        old = fullwatch[2*v].size() + fullwatch[2*v+1].size();
        //small elimination of %d replaces "%d old with %d new clauses and %d units",idx, old, newsz, units);
        if ((newsz-units) < old || units > 0) {
                int cnt=s_smallvccheck (v);
                if(cnt==newsz){
                    res = 1;
                    return s_smallve (cnf, v, newsz <= old);
                }
                if(cnt<old) {
                     res = 1;
                     return s_forcedve (v);
                }
                if(units > 0){
                    res = 1;
                    return s_smallve (cnf, v, 0);
                } 
        }
  } 
  return l_Undef;
}

lbool Solver :: s_elimlitaux (int v) 
{  
   s_elmsub (v);
  // if(deletedCls.size()) return  l_Undef;
   return  l_Undef;
}

int Solver :: s_blockcls (int ulit) 
{
   vec<CRef>&  crs  = fullwatch[ulit];
   int occNum = fullwatch[ulit].size();
   for(int i = 0; i < occNum; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        int j, size =0;
        for(j = 0; j < c.size(); j++){
               if(mark[toInt(c[j])^1]) break;
               if (++size > 500) return 0;
        }
        if(j >= c.size()) return 0;
   }
   return 1;
}  

int Solver :: s_initsmallve (int ulit, Fun res) 
{
  Fun cls, tmp;
  //initializing small variable eliminiation for %d", lit);
  s_s2m (ulit);
  s_truefun (res);
  Lit pivot=toLit(ulit);
  int count = fullwatch[ulit].size();

  vec<CRef>&  crs  = fullwatch[ulit];
  int clsCnt=0;
  for(int i = 0; i < count; i++){
        CRef cr=crs[i];
        Clause& c = ca[cr];
        s_falsefun (cls);// cls <- 000000
        for(int j = 0; j < c.size(); j++){
              if( value(c[j]) != l_Undef ){
                    if( value(c[j]) == l_True ) goto NEXT;
              }
              if( c[j] == pivot ) continue;
              int mlit = s_s2m (toInt(c[j]));
              if (!mlit) {
                     return 0;
	      }
              s_s2fun (mlit, tmp); //convert to fun 
	      s_orfun (cls, tmp);  // cls = cls | tmp 
        }
        clsCnt=1;
        s_andfun (res, cls); //res = res & cls
  NEXT:  ;
  }
  return clsCnt;
}

lbool Solver ::s_forcedve (int v) 
{
   int pos=fullwatch[2*v].size();
   int neg=fullwatch[2*v+1].size();
   if(pos==0 && neg==0) return l_Undef;
 
   int pivot = (pos <= neg) ? (2*v) : (2*v+1);
   int npivot = pivot^1;
   int elimflag=1;
   int prevsize;
   lbool ret = l_Undef;
   vec<Lit> newcls;
   vec<CRef> &  pcs  = fullwatch[pivot];
   vec<CRef> &  ncs  = fullwatch[npivot];
   Lit plit=toLit(pivot);
   Lit nlit=~plit;
   for(int i = 0; i < pcs.size(); i++){
        CRef pcr=pcs[i];
        Clause & a = ca[pcr];
        newcls.clear();
        for(int k = 0; k < a.size(); k++){
               if (a[k] == plit) continue;
               if (value(a[k]) == l_False) continue;
               if (value(a[k]) == l_True) goto DONE;
               mark[toInt(a[k])]=1;
               newcls.push(a[k]);
        }
        if(newcls.size()==0) return l_Undef;
        prevsize=newcls.size();
        for(int j = 0; j < ncs.size(); j++){
               CRef ncr=ncs[j];
               Clause& b = ca[ncr];
               for(int k = 0; k < b.size(); k++){
                     if (b[k] == nlit) continue;
                     if (value(b[k]) == l_False) continue;
                     if (value(b[k]) == l_True) goto NEXT;
                     int ul=toInt(b[k]);
                     if (mark[ul]) continue;
                     if (mark[ul^1]) goto NEXT;
                     newcls.push(b[k]);
               }
               if(newcls.size()==1){
                    if( value(newcls[0]) != l_Undef ){
                               elimflag=0;
                               goto DONE;
                     }
                     if(checkUnit (toInt(newcls[0]), 'e')){
                            CRef confl = unitPropagation(newcls[0]);
                            if (confl != CRef_Undef) {ret=l_False; goto DONE;}
                       }
                       else elimflag=0; 
              }
              else{
                  s_addfullcls (newcls, 0);
              }
        NEXT:  
              newcls.shrink(newcls.size()-prevsize);
        } 
  DONE:
        for(int k = 0; k < a.size(); k++) mark[toInt(a[k])]=0;
        if(ret==l_False || elimflag==0) return ret;
   }
   if(elimflag)  s_epusheliminated (v);
   return ret;
}

// elimiate subsume
void  Solver :: s_elmsub (int v) 
{
  Lit pivot = toLit(2*v);
  int lastIdx=eclsInfo.size();
  int ret;
  for (int cIdx =0;  cIdx < lastIdx; cIdx++){
       if(cIdx < neglidx){
            if(neglidx<2) return;
            ret = s_backsub (cIdx, 0,       neglidx, pivot, 0);
       }
       else {
            if(lastIdx-neglidx<2) return;
            ret = s_backsub (cIdx, neglidx, lastIdx, ~pivot,0);
       }
       if (ret) {   //subsumed original irredundant clause, subsumed mapped irredundant clause
            deletedCls.push(eclsInfo[cIdx].cr);
            eclsInfo[cIdx].size=0;
       } 
  }
  //subsumed %d clauses containing %d or %d,subsumed, spf->elm.pivot, -spf->elm.pivot);
}

// backward subsume and strengthened 
  //backward check for clause, backward %s check for mapped clause", mode);
int Solver :: s_backsub (int cIdx, int startidx, int lastIdx, Lit pivot, int streFlag)
{
   int size = eclsInfo[cIdx].size;
   unsigned csig = eclsInfo[cIdx].csig;
   int res = 0;
   int marked=0;

   for (int i = startidx; i<lastIdx; i++){
        if(i == cIdx) continue;
        int osize = eclsInfo[i].size;
        if (osize > size || osize==0) continue;//size=0 => deleted
        unsigned ocsig = eclsInfo[i].csig;
        if ((ocsig & ~csig)) continue;
        if (!marked) {
               CRef cr=eclsInfo[cIdx].cr;
               Clause& c = ca[cr];
               for(int j = 0; j < c.size(); j++){
                    int ul=toInt(c[j]);
                    if(streFlag && pivot==c[j])  ul=ul^1;
                    mark[ul]=1;
               }
               marked = 1;
        }
        CRef cr=eclsInfo[i].cr;
        Clause & c = ca[cr];
        res=1;
        for(int k = 0; k < c.size(); k++){
              res=mark[toInt(c[k])];
              if(res==0) break;
        }
        if ( !res || !streFlag || osize < size) {
               if(res) break;
               continue;
        }
       //strengthening by double self-subsuming resolution, 
      // strengthened and subsumed original irredundant clause
        deletedCls.push(cr);
        eclsInfo[i].size=0;
        break;
  }
  if (marked) {
         CRef cr=eclsInfo[cIdx].cr;
         Clause & c = ca[cr];
         for(int j = 0; j < c.size(); j++){
                int ul=toInt(c[j]);
                if(streFlag && pivot==c[j])  ul=ul^1;
                mark[ul]=0;
         }
   }
   return res;
}

lbool Solver :: inprocess()
{
    lbool status = s_lift ();
    if(status != l_Undef) return status;
    return s_probe ();
}

void  Solver :: s_extend ()
{
  Lit lit;
  if (equhead){
       for(int i=0; i<extendRemLit.size(); i++){
          lit = extendRemLit[i];
          if (lit==lit_Undef) continue;
          int cv=var(lit)+1;
          if(equhead[cv] && equhead[cv]!=cv){
                int elit =  equhead[cv];
                Lit eqLit = makeLit(elit);
                if(sign(lit)) extendRemLit[i]= ~eqLit;
                else  extendRemLit[i]= eqLit;
                if (value (eqLit) == l_Undef ) assigns[var(eqLit)] = lbool(!sign(eqLit));
          }
      }
  }

  Lit next = lit_Undef;
  while (extendRemLit.size()) {
     int satisfied = 0;
     do {
          lit = next;
          next = extendRemLit.pop_();
          if (lit==lit_Undef || satisfied) continue;
          if ( value (lit) == l_True ) satisfied = 1;
     } while (next != lit_Undef);
     if (satisfied) continue;
     int cv=var(lit);
     assigns[cv] = lbool(!sign(lit));
  }
}

void Solver:: solveEqu(int *equRepr, int equVars, vec<lbool> & Amodel)
{   
   if(equRepr==0) return;
   for (int i=1; i <= equVars; i++){
         if(equRepr[i]==0 || equRepr[i]==i) continue;
         int v=equRepr[i];
         v=ABS(v)-1;
         Amodel[i-1] = l_False;
         if (Amodel[v] == l_Undef) Amodel[v] = l_True;
         if (Amodel[v] == l_True){
                   if(equRepr[i] > 0) Amodel[i-1] = l_True;
         }
         else      if(equRepr[i] < 0) Amodel[i-1] = l_True;
    }
}

//=========================================
void Solver::cancelUntil0(int nlevel)
{
    if (decisionLevel() > nlevel){
        qhead = trail_lim[nlevel];
        for (int c = trail.size()-1; c >= qhead; c--) assigns [var(trail[c])] = l_Undef;
        trail.shrink(trail.size()-qhead);
        trail_lim.shrink(trail_lim.size() - nlevel);
    } 
}
CRef Solver::simplePropagate()
{
    CRef    confl = CRef_Undef;
    watches.cleanAll();
    watchesBin.cleanAll();
    while (qhead < trail.size())
    {
        Lit            p = trail[qhead++]; 
        vec<Watcher>&  ws = watches[p];
        Watcher        *i, *j, *end;
  
        vec<Watcher>&  wbin = watchesBin[p];
        for (int k = 0; k<wbin.size(); k++)
        {
            Lit imp = wbin[k].blocker;
            if (value(imp) == l_False) return wbin[k].cref;
            if (assigns[var(imp)] == l_Undef) UncheckEnqueueNoLevel(imp, wbin[k].cref);
        }
        for (i = j = (Watcher*)ws, end = i + ws.size(); i != end;)
        {
            Lit blocker = i->blocker;
            if (value(blocker) == l_True)
            {
                *j++ = *i++; continue;
            }

            // Make sure the false literal is data[1]:
            CRef     cr = i->cref;
            Clause & c = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
            Lit     first = c[0];
            if (first != blocker && value(first) == l_True) {
                i->blocker = first;
                *j++ = *i++; continue;
            }
            else {
                for (int k = 2; k < c.size(); k++) {
                    if (value(c[k]) != l_False) {
                        Watcher w = Watcher(cr, first); i++;
                        c[1] = c[k]; c[k] = false_lit;
                        watches[~c[1]].push(w);
                        goto NextClause;
                    }
                }
            }
            i->blocker = first;
            *j++ = *i++;
            if (value(first) == l_False) {
                confl = cr;
                qhead = trail.size();
                while (i < end) *j++ = *i++;
            }
            else UncheckEnqueueNoLevel(first, cr);
NextClause:;
        }
        ws.shrink(i - j);
    }
    return confl;
}

void Solver::UncheckEnqueueNoLevel(Lit p, CRef from){
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p)); // this makes a lbool object whose value is sign(p)
    vardata[var(p)].reason = from;
    trail.push_(p);
}

void Solver::cancelUntil_fixedunits()
{
    for (int c = trail.size() - 1; c >= fixedUnits; c--) assigns[var(trail[c])] = l_Undef;

    qhead = fixedUnits;
    trail.shrink(trail.size() - fixedUnits);

}

void Solver::simpleAnalyze(CRef confl, vec<Lit> & out_learnt)
{
    int pathC = 0;
    Lit p = (out_learnt.size()==1) ? out_learnt.last(): lit_Undef;
    int index = trail.size() - 1;
    do{
        if (confl != CRef_Undef){
            Clause& c = ca[confl];
            // Special case for binary clauses
            // The first one has to be SAT
            if (p != lit_Undef && c.size() == 2 && value(c[0]) == l_False) {

                assert(value(c[1]) == l_True);
                Lit tmp = c[0];
                c[0] = c[1], c[1] = tmp;
            }
            // if True_confl==true, then choose p begin with the 1th index of c;
            for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
                Lit q = c[j];
                if (!seen[var(q)]){
                    seen[var(q)] = 1;
                    pathC++;
                }
            }
        }
        else if (confl == CRef_Undef){
            out_learnt.push(~p);
        }
        // if not break, while() will come to the index of trail blow 0, and fatal error occur;
        if (pathC == 0) break;
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        // if the reason cr from the 0-level assigned var, we must break avoid move forth further;
        // but attention that maybe seen[x]=1 and never be clear. However makes no matter;
        if (fixedUnits > index + 1) break;
        p = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC >= 0);
}

void Solver::simplifyLearnt( Clause & c )
{
    fixedUnits = trail.size();
    int i, j;
    CRef confl;
    new_learntcls.clear();
    for (i = 0, j = 0; i < c.size(); i++){
          Lit lit=c[i];
          if (value(lit) == l_True){
                c[j++] = lit;
                confl = reason(var(c[i]));
                new_learntcls.push(c[i]);
                break;
          }
          if (assigns[var(lit)] == l_Undef){
               UncheckEnqueueNoLevel(~lit);
               c[j++] = lit;
               confl = simplePropagate();
               if (confl != CRef_Undef) break;
          }
    }
    c.shrink(c.size() - j);
    if (confl != CRef_Undef){
        simpleAnalyze(confl, new_learntcls);
        if (new_learntcls.size() < c.size()){
            for (j = 0; j < new_learntcls.size(); j++) c[j] = new_learntcls[j];
            c.shrink(c.size() - j);
        }
    }
    cancelUntil_fixedunits();
}

bool Solver::simplifysmallclause()
{
  //  if(conflicts<260000) return true;
    if(!mix_simp_mode) return true;
    int ci, cj;
    cancelUntil(0);
    for (ci = 0, cj = 0; ci < learnts.size(); ci++){
        CRef cr = learnts[ci];
        Clause & c = ca[cr];
        if( c.mark() == 1 ) continue;//removed
        if (c.done() || c.mark() == LONG) learnts[cj++] = learnts[ci];
        else {
            for (int i = 0; i < c.size(); i++) 
                 if (value(c[i]) == l_True){
                     removeClause(cr);
                     goto nextc;
                 }
            detachClause(cr, true);
            simplifyLearnt(c);
                              
            if (c.size() == 1){
                 if(unitPropagation(c[0]) != CRef_Undef){ ok = false; learnts.clear(); return false;}
                 c.mark(1);
                 ca.free(cr);  // delete
            }
            else{
              //   if (old_size != c.size() && certifiedUNSAT) printDrupClause(c, 0, needExtVar); //add
                 c.done(true);
                 attachClause(cr);
                 learnts[cj++] = learnts[ci];
                 unsigned int nblevels = computeLBD(c);
                 if (nblevels < (unsigned)c.lbd()) c.set_lbd(nblevels);
                 if(c.mark() == MIDSZ){
                        if (c.lbd() <= small_lbd_lim){//3 or 5
                             learnt_small++;
                             c.mark(SMALL);
                         }
                 }
            }
nextc:       ;
        }
    }
    learnts.shrink(ci - cj);
    checkGarbage();
    return true;
}
//---------------------------
inline void Solver:: swapEqTofront(Lit * lits, int sz, int eqVal)
{     int j=0,k;
      for(int i=0; i<sz; i++){
           Lit lt=lits[i];
           if(mark[toInt(lt)]!=eqVal) continue;
           lits[i]=lits[j]; lits[j++]=lt;
      }
      if(j>11){
          sort(lits, j);
          return;
      }
      for(int i=1; i<j; i++){
           Lit lt=lits[i];
           int m=toInt(lt);
           for(k=i-1; k>=0; k--){
               if(m>toInt(lits[k])) break;
               lits[k+1]=lits[k];
           }
           lits[k+1]=lt;
     }
}

inline int Solver:: moveEqTofront(vec <Lit> & preLit,vec <Lit> & curLit,vec <Lit> & nxtLit)
{      
      for(int i=preLit.size()-1; i>=0; i--) mark[toInt(preLit[i])]  =1;
      for(int i=nxtLit.size()-1; i>=0; i--) mark[toInt(nxtLit[i])] +=2;
      int en1=0,en2=0,en3=0;
      for(int i=curLit.size()-1; i>=0; i--){
             int lit=toInt(curLit[i]);
             if(mark[lit]==1) en1++;
             else if(mark[lit]==2) en2++;
                  else if(mark[lit]==3) en3++;
      }
      swapEqTofront((Lit *)curLit, curLit.size(),3);
      swapEqTofront((Lit *)curLit+en3, curLit.size()-en3,1);
      swapEqTofront((Lit *)curLit+en1+en3, curLit.size()-en1-en3,2);
      for(int i=preLit.size()-1; i>=0; i--) mark[toInt(preLit[i])]=0;
      for(int i=nxtLit.size()-1; i>=0; i--) mark[toInt(nxtLit[i])]=0;
      return en1+en2+en3;
}


lbool Solver::re_learn()
{ 
 //   if(conflicts>260000) return l_Undef;
    if(!mix_simp_mode) return l_Undef;
 
    cancelUntil(0);
    lbool ret=l_Undef;
    mark = (char * ) calloc (2*nVars()+1, sizeof(char));
    vec <Lit> lits[3],best_learnt,tmplits,decLits;
    CRef confl;
    int elev, nx=2, cu_i=-1, truePos=1000000,Tflag;
    unsigned int newLBD;
    Lit pivot;
    int limit=learnts.size()-2000;
    for (int i = 0; i <= limit; i++){
          int cu=(nx+2)%3;
          int pr=(nx+1)%3;
          vec <Lit> & prLits=lits[pr];
          vec <Lit> & cuLits=lits[cu];
          vec <Lit> & nxLits=lits[nx];
//  
          nxLits.clear();
          while (i < limit){
              Clause & c =ca[learnts[i]];
              if(c.size()<5 || c.done()) {i++; continue;}
              for(int j=0; j<c.size(); j++){
                  nxLits.push(c[j]);
              }
              c.done(1);
              break;
          }
  
          if(cuLits.size()){
               moveEqTofront(prLits,cuLits,nxLits);
               if(1){
                     tmplits.clear();
                     for(int j=0; j<cuLits.size(); j++) mark[toInt(cuLits[j])]=2;
                     int eqvn=-1;
                     for(int j=0; j<prLits.size(); j++){
                           Lit lt=prLits[j];
                           if(mark[toInt(lt)]==2){
                               tmplits.push(lt);
                               mark[toInt(lt)]=0;
                           }
                           else if(eqvn ==-1 ) eqvn=j;
                     }
                     for(int j=0; j<cuLits.size(); j++){
                           Lit lt=cuLits[j];
                           if(mark[toInt(lt)]){
                               tmplits.push(lt);
                               mark[toInt(lt)]=0;
                           }
                           cuLits[j]=tmplits[j];
                     }
                 
                     if(eqvn <= 0 ) eqvn=0;
                     CRef cu_cr=learnts[cu_i];
                     Clause & c =ca[cu_cr];
                     detachClause(cu_cr, true);
                     if(truePos <= eqvn){//subsume  (A V B V C V D)(A V B V C) 
                              truePos=100000;
                              decLits.clear();      
                              goto Del;
                     }
                     if(eqvn >  decLits.size() ) eqvn = decLits.size();  
                     elev=0;
                     for(int k=0; k < eqvn; k++){
                         Lit lit=prLits[k];
                         if(level(var(lit))>elev) elev=level(var(lit));
                     }

                     if (decLits.size() < elev) elev=eqvn=0;
                     if (eqvn < elev) elev=eqvn;
                     decLits.shrink(decLits.size()-elev);
                     cancelUntil0(elev);
                     confl = CRef_Undef;
                     pivot = lit_Undef;
                     Tflag=0;
                     truePos=cuLits.size()+1;
           
                     for(int k = 0; k <cuLits.size(); k++){
                          Lit lit=cuLits[k];
                          if(k<eqvn){
                               if(assigns[var(lit)] == l_Undef){
                                  uncheckedEnqueue(~lit);
                               }
                               continue;
                          }
                          if(value(lit) == l_True){
                                if(level(var(lit))==0) goto Del;
                                confl = reason(var(lit));
                                 pivot=lit;
                                Tflag=1;
                                truePos=k+1;
                                break;
                          }
                          if(value(lit) == l_False){
                                continue;
                          }
                          decLits.push(lit);
                          newDecisionLevel();
                          uncheckedEnqueue(~lit);
                          confl = propagate();
                          if (confl != CRef_Undef) {truePos=k+1; break;}
                     }
        
                     best_learnt.clear();
                     if (confl == CRef_Undef){
                            if(Tflag) best_learnt.push(pivot);
                            for(int k=decLits.size()-1; k>=0; k--) best_learnt.push(decLits[k]);
                            if(best_learnt.size()==0){ 
                                   ret=l_False; 
                                   goto Del;
                            } 
                     }   
                     else {
                          simpAnalyze(confl, best_learnt, pivot);
                          if (best_learnt.size() >= decLits.size()+Tflag){
                               best_learnt.clear();
                               if(Tflag) best_learnt.push(pivot);
                               for(int k=decLits.size()-1; k>=0; k--) best_learnt.push(decLits[k]);
                          }
                     }
 
                     if (best_learnt.size() < c.size()){
                              if (best_learnt.size() == 1){
                                     cancelUntil0(0);
                                     decLits.clear();
                                     if(assigns[var(best_learnt[0])] == l_Undef){
                                          confl = unitPropagation(best_learnt[0]);
      	                                  if (confl != CRef_Undef) ret=l_False;
                                     }
Del:
                                     c.mark(1);
                                     ca.free(cu_cr);
                                     learnts[cu_i]=CRef_Undef;
                                     if(ret==l_False) goto done;
                                     goto next;
                               }
                               for (int k = 0; k < best_learnt.size(); k++) {
                                    c[k] = best_learnt[k];
                                    if(VSIDS) varBumpVSIDSactivity(var(c[k]), var_inc);
                               }
                             
                               claBumpActivity(c);
                               newLBD = computeLBD(best_learnt);
                               if(c.lbd()>newLBD || c.lbd()<=1) c.set_lbd(newLBD);

                               c.shrink(c.size() - best_learnt.size());//bug
                     }
                     attachClause(cu_cr);
               }
          }
next:      
          cu_i=i;
          nx = (nx+1)%3;
    }
done:
    free(mark);
    cancelUntil0(0);
    int j=0;
    for (int i = 0; i < learnts.size(); i++) if(learnts[i] != CRef_Undef) learnts[j++]=learnts[i];  
    learnts.shrink(learnts.size()-j);
    return ret;
}

void Solver::simpAnalyze(CRef confl, vec<Lit> & out_learnt, Lit p)
{
    if(p != lit_Undef) out_learnt.push(p);
    int index   = trail.size() - 1;
    int pathC = 0;

    do{
        Clause & c = ca[confl];
	if(c.size()==2 && value(c[0])==l_False) {
	    Lit tmp = c[0]; c[0] =  c[1], c[1] = tmp;
	}
   
        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];
            if (!seen[var(q)] && level(var(q)) > 0){
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) pathC++;
                else out_learnt.push(q);
	    }
        }
        
        if (pathC == 0){
             p=lit_Undef;
             break;
        }
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;
    } while (pathC > 0);
    if(p != lit_Undef) out_learnt.push(~p);

    for (int j = 0; j < out_learnt.size(); j++) seen[var(out_learnt[j])] = 0;
}
//======================================
void Solver::rand_rephase()
{       int var_nums  = nVars();
        if(rand()%100<50){
              for(int i=0;i<var_nums;++i) polarity[i] = !cur_solution[i];
              return;
        }
        int pick_rand = rand()%1000;
        if ((pick_rand-=100)<0){
           for(int i=0;i<var_nums;++i) polarity[i] = !best_solution[i];
        }else if((pick_rand-=300)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = !cur_solution[i];
            cur_solustion_used = true; 
        }
        //top_trail 200
        else if((pick_rand-=300)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = !top_trail_soln[i];
        }
        //reverse
        else if((pick_rand-=50)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = !polarity[i];
        }else if((pick_rand-=25)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = best_solution[i];
        }else if((pick_rand-=25)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = top_trail_soln[i];
        }
        //150
        else if((pick_rand-=140)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = rand()%2==0?1:0;
        }
        else if((pick_rand-=5)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = 1;
        }else if((pick_rand-=5)<0){
            for(int i=0;i<var_nums;++i) polarity[i] = 0;
        }
        //50
        else{
            //do nothing 
        }
}

void Solver::propagate_solution()
{
      int var_nums = nVars();
      int t_sz = trail.size();
      int idx = 0;
      int assumeUnit_sz = t_sz ;
      vector<Lit> assumeUnit(var_nums+2);
      for(int i=0;i<t_sz;++i) assumeUnit[i]=trail[i];
        
      int undef_nums = 0;
      vector<int> undef_vars(var_nums-t_sz+2);
      vector<int> idx_undef_vars(var_nums+1, -1); 
      for(int i=0;i<var_nums;++i) 
            if(value(i) == l_Undef){
                idx_undef_vars[i] = undef_nums;
                undef_vars[undef_nums++] = i;
            }else{
                cur_solution[i] = (value(i) == l_True) ? 1 : 0;
            }

      while(undef_nums > 0){
            while(idx < assumeUnit_sz){
                Lit  p  = assumeUnit[idx++];
                vec<Watcher>&   ws_bin = watchesBin[p];
                int ws_bin_sz=ws_bin.size();
                for(int k=0;k<ws_bin_sz;k++){
                    Lit the_other = ws_bin[k].blocker;
                    Var the_other_var = var(the_other);
                    if(idx_undef_vars[the_other_var]>-1){
                        //no conflict and can decide.
                        cur_solution[the_other_var] = sign(the_other) ? 0:1;
                        assumeUnit[assumeUnit_sz++] = the_other;

                        int end_var = undef_vars[--undef_nums];
                        int idx_end_var = idx_undef_vars[the_other_var];
                        undef_vars[idx_end_var] = end_var;
                        idx_undef_vars[end_var] = idx_end_var;
                        idx_undef_vars[the_other_var] = -1;
                    }
                }
                if(undef_nums==0) break;

                vec<Watcher>&   ws = watches[p];
                Watcher         *i,*j,*end;
                for(i = j = (Watcher*)ws, end = i + ws.size(); i!=end;){
                    // Make sure the false literal is data[1]:
                    CRef     cr        = i->cref;
                    Clause&  c         = ca[cr];
                    Lit      false_lit = ~p;
                    if (c[0] == false_lit) c[0] = c[1], c[1] = false_lit;
                    i++;

                    // If 0th watch is true, then clause is already satisfied.
                    Lit     first = c[0];
                    Var     first_var = var(first);
                    Watcher w = Watcher(cr, first);
                    if( idx_undef_vars[first_var]==-1 && cur_solution[first_var]==(!sign(first))){
                        *j++ = w; continue; 
                    }

                    int c_sz=c.size();
                    for(int k=2;k<c_sz;++k){
                        Lit tmp_lit = c[k];
                        Var tmp_var = var(tmp_lit);
                        if( idx_undef_vars[tmp_var]==-1 && cur_solution[tmp_var] == sign(tmp_lit)){}
                        else{
                            c[1] = c[k];
                            c[k] = false_lit;
                            watches[~c[1]].push(w);
                            goto check_next_clause;
                        }
                    }
                    *j++ = w;
                    if( idx_undef_vars[first_var] == -1 && cur_solution[first_var] == sign(first)){
                        continue;
                    }else{
                        cur_solution[first_var] = sign(first) ? 0:1;
                        assumeUnit[assumeUnit_sz++] = first;

                        int end_var = undef_vars[--undef_nums];
                        int idx_end_var = idx_undef_vars[first_var];
                        undef_vars[idx_end_var] = end_var;
                        idx_undef_vars[end_var] = idx_end_var;
                        idx_undef_vars[first_var] = -1;
                    }
check_next_clause:;
                }
                ws.shrink(i-j);
            }
            
            if(undef_nums == 0) break;
            int choosevar_idx = rand() % undef_nums;
            Var choosevar     = undef_vars[choosevar_idx];
            Lit choose        = mkLit(choosevar,polarity[choosevar]);

            cur_solution[choosevar] = sign(choose) ? 0:1;
            assumeUnit[assumeUnit_sz++] = choose;

            int end_var = undef_vars[--undef_nums];
            int idx_end_var = idx_undef_vars[choosevar];
            undef_vars[idx_end_var] = end_var;
            idx_undef_vars[end_var] = idx_end_var;
            idx_undef_vars[choosevar] = -1;
      }
      int unsat_num = 0;
      for (int i =0; i < clauses.size(); i++){
        Clause & c = ca[clauses[i]];
	    for (int j = 0; j < c.size(); j++) {
		    Lit p=c[j];
          	if (sign(p)){//negative
                    if(!cur_solution[var(p)]) goto nextc;
            }
            else    if(cur_solution[var(p)]) goto nextc;
 	    }
        unsat_num++;
        nextc:  ;
      }

//      printf("<unsat_num =%d best_unsat_num=%d clauses.size=%d> \n",unsat_num,best_unsat_num,clauses.size());
//      fflush(stdout);

      if(unsat_num <= best_unsat_num){
        for(int i=0;i<var_nums;++i) best_solution[i] = cur_solution[i];
        best_unsat_num = unsat_num;
     }
 }

