
#include <pthread.h>
#include "parallel/MainThread.h"
#include "mtl/Sort.h"
#include "utils/System.h"
#include "simp/SimpSolver.h"
#include <errno.h>
#include <string.h>

using namespace abcdSAT;

extern const char* _parallel ; // Options at the parallel solver level
static IntOption opt_maxmemory (_parallel, "maxmemory", "Maximum memory to use (in Mb, 0 for no software limit)", 56000);
//static IntOption opt_maxNosolver (_parallel, "maxnbthreads", "Maximum number of core threads to ask for (when nbthreads=0)", 24);
static IntOption opt_maxNosolver (_parallel, "maxnbthreads", "Maximum number of core threads to ask for (when nbthreads=0)", 63);

#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

MainThread::MainThread(): verb(0)
  , ok (true)
  , nbthreads(0)
  , maxmemory(opt_maxmemory), maxnbsolvers(opt_maxNosolver)
{   
    LocalThread * s = new LocalThread();    // Generate the first solver 0 to be copied
    s->sharedinfo   = new SharedInfo();
    solvers.push(s);
    s->verbosity = 0; 
    s->setThreadNumber(0);
    
    pthread_mutex_init(&m,NULL);         //PTHREAD_MUTEX_INITIALIZER;
    pthread_cond_init(&cfinished,NULL);  //PTHREAD_COND_INITIALIZER;
    pthread_cond_init(&Clonefinished,NULL); 
    pthread_mutex_init(&mfinished,NULL); // mutex on which main process may wait for
}

MainThread::~MainThread() { 
   for(int i=0;i< solvers.size();i++) delete solvers[i];
}

LocalThread * MainThread::generateOneSolver(int tn) 
{
    LocalThread *s  = (LocalThread*)solvers[0]->clone();
    s->verbosity = 0; 
    s->setThreadNumber(tn);
    s->sharedinfo     =   solvers[0]->sharedinfo;
    if(highLit.size() && tn > 3){
         s->parallel_pivot =  highLit.last();
         highLit.shrink_(1);
    }
    return s;
}

// Generate All solvers
void MainThread::generateAllSolvers() 
{
    for(int i=2;i<=nbthreads;i++) {
	LocalThread * s = generateOneSolver(i);
        solvers.push(s);
        configureParameters(i);
    }
}

void MainThread:: configureParameters(int tn)
{ 
   solvers[tn]->LBDmode    = (tn+1)%2;
   solvers[tn]->WVSIDSmode = (tn+1)%2;
   solvers[tn]->bitLim = -1; 
   
   if(tn>12 && tn%2) solvers[tn]->bitVecNo = 0;
   switch (tn%12){
     case 1 : solvers[1]->var_decay = 0.94;
              solvers[1]->max_var_decay = 0.96;
              solvers[1]->firstReduceDB=600;
              solvers[1]->rnd_pol = true;
              solvers[1]->atLeastTwo = true;
              solvers[tn]->bitLim = 2e4;
              return;
     case 2 :
              solvers[2]->var_decay = 0.90;
              solvers[2]->max_var_decay = 0.97;
              solvers[2]->firstReduceDB=500;
              solvers[2]->random_var_freq=0.05;
              solvers[2]->v_inc_factor = 1;
              solvers[2]->inprocessmode = true;
              return;
     case 3:
              solvers[3]->var_decay = 0.85;
              solvers[3]->max_var_decay = 0.95;
              solvers[3]->firstReduceDB=400;
              solvers[3]->bitVecNo = 0;
              solvers[3]->vdecay_delta = 0.008;
              return;
     case 4:
              solvers[4]->var_decay = 0.95;
              solvers[4]->max_var_decay = 0.95;
              solvers[4]->firstReduceDB=4000;
              solvers[4]->lbdQueue.growTo(100);
              solvers[4]->lbdQueue.growTo(100);
              solvers[4]->K = 0.7;
              solvers[4]->incReduceDB = 500;
              return;
    case 5:   
              solvers[5]->var_decay = 0.93;
              solvers[5]->max_var_decay = 0.96;
              solvers[5]->firstReduceDB=100;
              solvers[5]->incReduceDB = 600;
              return;
    case 6:   
              solvers[6]->var_decay = 0.75;
              solvers[6]->max_var_decay = 0.94;
              solvers[6]->firstReduceDB=1000;
              return; 
    case 7:   
              solvers[7]->var_decay = 0.94;
              solvers[7]->max_var_decay = 0.96;
              solvers[7]->firstReduceDB=800;
              return;
    case 8:   
              solvers[8]->var_decay = 0.92;
              solvers[8]->max_var_decay = 0.97;
              solvers[8]->firstReduceDB=200;
              solvers[8]->incReduceDB = 500;
              return;
    case 9:   
              solvers[tn]->var_decay = 0.916;
              solvers[tn]->max_var_decay = 0.97;
              solvers[tn]->firstReduceDB=300;
              solvers[tn]->incReduceDB = 700;
              return;
    default: break;
   }
   double noisevar_decay = 0.005;
   int noiseReduceDB = 50;
   if ( tn % 5 == 0) {
	  noisevar_decay += 0.006;
	  noiseReduceDB += 30;
   }
   solvers[tn]-> var_decay = solvers[tn%10]->var_decay+0.001;
   solvers[tn]-> max_var_decay = solvers[tn%10]->max_var_decay;
   solvers[tn]-> firstReduceDB= solvers[tn%10]->firstReduceDB;
   solvers[tn]->var_decay += noisevar_decay;
   solvers[tn]->firstReduceDB+=noiseReduceDB;
}

void MainThread::newVar(bool sign, bool dvar)
{
  solvers[0]->sharedinfo->newVar();
  for(int i=0;i<solvers.size(); i++) solvers[i]->newVar(sign,dvar);
}

bool MainThread::addClause_(vec<Lit>&ps) {
  if (!okay()) return ok=false;
  return ok = solvers[0]->addClause_(ps);
}

bool MainThread::simplify() {
  if (!okay()) return ok=false;
  ok = solvers[0]->simplify(); 
  if (!ok) return false;
  return true;
}

void *localLaunch(void*arg) {
  LocalThread* s = (LocalThread*)arg;
  
  s->ssolve_(); 

  pthread_exit(NULL);
}

void MainThread::printStats() {
    double cpu_time = cpuTime();
    printf("c %.0fs  \n",cpu_time);
    printf("c |--------------------------------------------------------------|\n");
    printf("c | id | starts | decisions  |  confls    | learnts  | progress  |\n");
    printf("c |--------------------------------------------------------------|\n");
    for(int i=0;i<solvers.size();i++) solvers[i]->reportProgress();
    long long int totalconf = 0, totalprop = 0;
    for(int i=0;i<solvers.size();i++) {
    	totalconf+=  (long int) solvers[i]->conflicts;
	    totalprop+= solvers[i]->propagations;
    }
    printf("c \n");
    printf("c synthesis %11lld conflicts %11lld propagations %8.0f conflicts/sec %8.0f propagations/sec\n",
            totalconf, totalprop, (double)totalconf / cpu_time, (double) totalprop / cpu_time);
}

void printsegmentLine(int n)
{ 
    printf("c |---------------");
    for(int i = 0;i<n; i++)  printf("|------------");
    printf("|-----------------|\n");    
}
void MainThread::printFinalStats() 
{
    printf("c\n");
    printf("c |------------------------- FINAL STATS ---------------------------------------|\n");
    printf("c\n");
    
    printsegmentLine(solvers.size());

    printf("c | Threads       ");
    for(int i = 0;i < solvers.size();i++) printf("| %10d ",i);
    printf("|      Total      |\n");

    printsegmentLine(solvers.size());
    
    printf("c | Conflicts     ");

    long long int totalconf = 0;
    for(int i=0;i<solvers.size();i++)  {
	printf("| %10" PRIu64" ", solvers[i]->conflicts);
	totalconf +=  solvers[i]->conflicts;
    }
    printf("| %15lld |\n",totalconf);
     
    printf("c | Unaries       ");
    for(int i=0;i<solvers.size();i++) printf("| %10" PRIu64" ", solvers[i]->nbUn);
    printf("|                 |\n"); 

    printf("c | Binaries      ");
    for(int i=0;i<solvers.size();i++) printf("| %10" PRIu64" ", solvers[i]->nbBin);
    printf("|                 |\n"); 

    int winner = -1;
    for(int i=0;i<solvers.size();i++) {
     if(solvers[0]->sharedinfo->winner()==solvers[i])
       winner = i;
    }
   
    if(winner!=-1) {
      int sum = 0;
      printf("c | Hamming       ");
      for(int i = 0;i<solvers.size();i++) {
        if(i==winner) {
             printf("|      X     ");
             continue;
        }
        int nb = 0;
        for(int j = 0;j<nVars();j++) {
           if(solvers[i]->valuePhase(j)!= solvers[winner]->valuePhase(j)) nb++;
        }
        printf("| %10d ",nb);
        sum+=nb;
      }
      printf("| %15d |\n",sum/(solvers.size()>1?solvers.size()-1:1));
    }
    printsegmentLine(solvers.size());
}

void MainThread::adjustNumberOfCores() {
 float mem = memUsed();
  if (nbthreads==0) { 
      if(verb>=1) 
          printf("c Automatic adjust the number of solvers. MaxMemory=%5d, MaxCores=%3d \n", maxmemory, maxnbsolvers);
      unsigned int tmpnbsolvers = maxmemory * 4 /  10 / mem;
      if (tmpnbsolvers > maxnbsolvers) tmpnbsolvers = maxnbsolvers;
      if (tmpnbsolvers < 32) tmpnbsolvers = 32;

      if(verb>=1) 
         printf("c One solver uses %.2fMb... Let's take %d solvers for this run (40%% of max memory)\n", mem, tmpnbsolvers);
      nbthreads = tmpnbsolvers;
   } 
}

lbool MainThread::solve() 
{
  pthread_attr_t thAttr; 
  int i; 

  adjustNumberOfCores();
  SharedInfo *sharedinfo=solvers[0]->sharedinfo;
  sharedinfo->setNbThreads(nbthreads);

  LocalThread * s = generateOneSolver(1);

  solvers.push(s);
  configureParameters(1);
  solvers[1]->parallel_pivot = lit_Undef;

  if(!solvers[0]->eliminate(true)) return l_False;

  solvers[0]->extractHighVar(highLit);
  solvers[0]->parallel_pivot = lit_Undef;

  generateAllSolvers();
  
  highLit.clear();

//  for (i = 1; i <=10 && i<nbthreads/2-1; i++) solvers[i]->pureMode=0;
  for (i = 1; i <=32 && i<nbthreads/2-1; i++) solvers[i]->pureMode=0;

  solvers[0]->canPause=true;
  if(nbthreads>2) solvers[1]->mix_simp_mode=true;
  if(nbthreads>10) {
        solvers[2]->pureMode=solvers[3]->pureMode=1;
        solvers[2]->symmtryMode=true;
        solvers[3]->BCDmode    =true;
  }
  if(verb>=1) {
    printf("c |  all clones generated. Memory = %6.2fMb.   |\n", memUsed());
    printf("c ========================================================================================|\n");
    fflush(stdout);
  }
  
  model.clear();

  // Initialize and set thread detached attribute 
  pthread_attr_init(&thAttr);
  pthread_attr_setdetachstate(&thAttr, PTHREAD_CREATE_JOINABLE);
  
 // launch all solvers
  for (i = 0; i <= nbthreads; i++) {
       pthread_t * pt = (pthread_t*)malloc(sizeof(pthread_t));
       threads.push(pt);
       solvers[i]->pcfinished = &cfinished;
       pthread_create(threads[i], &thAttr, &localLaunch, (void*)solvers[i]); 
  }

  bool done = false;
  while (!done) { 
    if(solvers[0]->OtherSolverFinished()) break;
    struct timespec timeout;
    time(&timeout.tv_sec);
    timeout.tv_sec += 5;
    timeout.tv_nsec = 0;
    if (pthread_cond_timedwait(&cfinished, &mfinished, &timeout) != ETIMEDOUT) done = true;
    else printStats();
 
    float mem = memUsed();
    if(verb>=1) printf("c Total Memory so far : %.2fMb\n",  mem);
    if ( (maxmemory > 0) && (mem > maxmemory) && !sharedinfo->panicMode) sharedinfo->panicMode = true;
    // reduceDB switching to Panic Mode due to memory limitations
      while(sharedinfo->NumPartjobFinished()){
             solvers[0]->setPause(true);
             while(solvers[0]->isPause()){
                 if(solvers[0]->OtherSolverFinished()) goto done;
                 time(&timeout.tv_sec);
                 timeout.tv_sec += 2;
                 timeout.tv_nsec = 0;
                 if (pthread_cond_timedwait(&Clonefinished, &mfinished, &timeout) != ETIMEDOUT) break;
             }
        
             LocalThread *s = sharedinfo->getPartFinished();
             int tn = s->threadNumber();
             pthread_join(*threads[tn], NULL);
             delete solvers[tn];
        
             solvers[tn] = solvers[0]->copysolver; 
        //     configureParameters(tn);
             solvers[tn]->symmtryMode=false;
             solvers[tn]->BCDmode    =false;
             solvers[tn]->pcfinished = &cfinished;
             solvers[tn]->parallel_pivot = lit_Undef;
             solvers[tn]->setThreadNumber(tn);
             solvers[tn]->canPause=false;
             pthread_t * pt = (pthread_t*)malloc(sizeof(pthread_t));
             threads[tn] = pt;
             pthread_create(threads[tn], &thAttr, &localLaunch, (void*)solvers[tn]);
     }
  }
done:  
    for (i = 0; i <= nbthreads; i++) { // Wait for all threads to finish
      pthread_join(*threads[i], NULL);//release all resource
    }
  
    lbool status = sharedinfo->jobStatus;
    if (status == l_True) {
        int n = sharedinfo->jobFinishedBy->nVars();
	model.growTo(n);
	for(int i = 0; i < n; i++)
	    model[i] = sharedinfo->jobFinishedBy->model[i];
    }
    return status;
}

