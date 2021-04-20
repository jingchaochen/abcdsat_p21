
#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include <sys/stat.h>


#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/SolverTypes.h"

#include "simp/SimpSolver.h"
#include "parallel/LocalThread.h"
#include "parallel/MainThread.h"

char* input_file    = NULL;

using namespace abcdSAT;

static MainThread* pmsolver;
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (pmsolver->verbosity() > 0){
        pmsolver->printFinalStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); 
}

#ifndef NUNLOCKED
#define A_putc_unlocked putc_unlocked
#define A_getc_unlocked getc_unlocked
#else
#define A_putc_unlocked putc
#define A_getc_unlocked getc
#endif

// These are signatures for supported compressed file types.  In 2018 the
// SAT Competition was running on StarExec and used internally 'bzip2'
// compressed files, but gave them uncompressed to the solver using exactly
// the same path (with '.bz2' suffix). 

static int xzsig[] = { 0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, EOF };
static int bz2sig[] = { 0x42, 0x5A, 0x68, EOF };
static int gzsig[] = { 0x1F, 0x8B, EOF };
static int zipsig[] = {0x50, 0x4B, 0x03, 0x04, EOF };
static int sig7z[] = { 0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C, EOF };
static int lzmasig[] = { 0x5D, 0x00, 0x00, 0x80, 0x00, EOF };
static int pipefile=true;

bool match (const char * path, const int * sig) 
{
  FILE * tmp = fopen (path, "r");
  if (!tmp) {
    printf("c WARNING: failed to open '%s' to check signature \n", path);
    return false;
  }
  bool res = true;
  for (const int *p = sig; res && (*p != EOF); p++) res = (A_getc_unlocked (tmp) == *p);
  fclose (tmp);
  if (!res) printf("c file type signature check for '%s' failed\n", path);
  else printf("c signature check for '%s' success\n", path);
  return res;
}

bool exists (const char * path) 
{
  struct stat buf;
  if (stat (path, &buf)) return false;
  if (access (path, R_OK)) return false;
  return true;
}

char * find (const char * prg) 
{
  size_t prglen = strlen (prg);
  const char * c = getenv ("PATH");
  if (!c) return 0;;
  size_t len = strlen (c);
  char * e = new char[len + 1];
  strcpy (e, c);
  char * res = 0;
  for (char * p = e, * q; !res && p < e + len; p = q) {
    for (q = p; *q && *q != ':'; q++)
      ;
    *q++ = 0;
    size_t pathlen = (q - p) + prglen;
    char * path = new char [pathlen + 1];
    sprintf (path, "%s/%s", p, prg);
    assert (strlen (path) == pathlen);
    if (exists (path)) res = path;
    else delete [] path;
  }
  delete [] e;
  return res;
}

FILE * open_pipe (const char * fmt, const char * path) 
{
  size_t prglen = 0;
  while (fmt[prglen] && fmt[prglen] != ' ') prglen++;
  char * prg = new char [prglen + 1];
  strncpy (prg, fmt, prglen);
  prg[prglen] = 0;
  char * found = find (prg);
  if (found) printf("c found '%s' in path for '%s'\n", found, prg);
  if (!found) printf ("did not find '%s' in path\n", prg);
  delete [] prg;
  if (!found) return 0;
  delete [] found;
  char * cmd = new char [strlen (fmt) + strlen (path)];
  sprintf (cmd, fmt, path);

  printf("c %s \n",cmd);

  FILE * res = popen (cmd, "r");
  delete [] cmd;
  return res;
}

bool has_suffix (const char * str, const char * suffix) {
  size_t k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

FILE * check_popen (const char * path) {
  FILE * file=0;
  if (has_suffix (path, ".xz")) {
  //  file = read_pipe ("xz -c -d %s", xzsig, path);
       if(match(path, xzsig)) file=open_pipe ("xz -c -d %s", path); 
  } else if (has_suffix (path, ".lzma")) {
    //file = read_pipe ("lzma -c -d %s", lzmasig, path);
       if(match(path, lzmasig)) file=open_pipe ("lzma -c -d %s", path); 
  } else if (has_suffix (path, ".bz2")) {
    //file = read_pipe ("bzip2 -c -d %s", bz2sig, path);
     if(match(path, bz2sig)) file=open_pipe ("bzip2 -c -d %s", path); 
 } else if (has_suffix (path, ".gz")) {
    //file = read_pipe ("gzip -c -d %s", gzsig, path);
     if(match(path, gzsig)) file=open_pipe ("gzip -c -d %s", path); 
 } else if (has_suffix (path, ".zip")) {
     if(match(path, zipsig)) file=open_pipe ("unzip -p %s", path); 
 } else if (has_suffix (path, ".7z")) {
   // file = read_pipe ("7z x -so %s 2>/dev/null", sig7z, path);
     if(match(path, sig7z)) file=open_pipe ("7z x -so %s 2>/dev/null", path); 
  }
  pipefile=true; 
  if(file==0) {
       file = fopen(path,"r");
       pipefile=false;
  }
  return file;
}

void verifyModel(char* filename, vec<bool> & true_var)
{
    SimpSolver  S;
   // gzFile in = gzopen(filename, "rb");
    FILE *in = check_popen(filename);
    if (in == NULL)
            printf("ERROR! Could not open file: %s\n", filename), exit(1);
           
// Parse CNF:
   printf("c final verify filename=%s \n",filename);
  
    parse_DIMACS(in, S);
  //  gzclose(in);
    if(pipefile) pclose(in);
    else fclose(in);
  
// Check satisfaction:
   vec<CRef>& cs = S.clauses;
  
   for (int i = 0; i < cs.size(); i++){
         Clause& c = S.ca[cs[i]];
        for (int j = 0; j < c.size(); j++){
              if (sign(c[j])==1 && true_var[var(c[j])]==false ) goto Satisfied;
              if (sign(c[j])==0 && true_var[var(c[j])]==true ) goto Satisfied;
        }
        printf("s INDETERMINATE\n");
        while(1){ i=1;}
        printf("{");
        for (int j = 0; j < c.size(); j++){
               if(sign(c[j])) printf("-");
               printf("%d:%d ", var(c[j])+1, true_var[var(c[j])]);
        }
        printf(" }\n");
        exit(0);

      Satisfied:;
    }
}

void init_rand_seed (); 

int main(int argc, char** argv)
{
   init_rand_seed ();
    double realTimeStart = realTime();
    printf("c\nc This is abcdSAT-parallel 2021 by Jingchao Chen \nc\n");
    try {
       setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        
        input_file=argv[1];
        parseOptions(argc, argv, true);
        bool ShowModel=true;
	MainThread msolver;
        pmsolver = & msolver;
        msolver.setVerbosity(verb);
  
        double initial_time = cpuTime();
      // Use signal handlers that forcibly quit until the solver will be able to respond to interrupts
	signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1) printf("c Reading from standard input... Use '--help' for help.\n");
        
        //gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        FILE *in = (argc == 1) ? stdin : check_popen(argv[1]);

        if (in == NULL)
            printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        parse_DIMACS(in, msolver);
//        gzclose(in);
        if(pipefile) pclose(in);
        else fclose(in);

        FILE* res = (argc >= 3) ? fopen(argv[argc-1], "wb") : NULL;
        int org_nvars=msolver.nVars();
        if (msolver.verbosity() > 0){
            printf("c |  Number of variables:  %12d  |\n", msolver.nVars());
            printf("c |  Number of clauses:    %12d  |\n", msolver.nClauses()); }
        
        double parsed_time = cpuTime();
        if (msolver.verbosity() > 0){
            printf("c |  Parse time:   %12.2f s   |\n", parsed_time - initial_time);
        }
 
        int ret2 = msolver.simplify();    	
        double simplified_time = cpuTime();
        if (msolver.verbosity() > 0){
            printf("c |  Simplification time:  %12.2f s  |\n", simplified_time-parsed_time);
        }
        if (!ret2 || !msolver.okay()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (msolver.verbosity() > 0){
	        printf("c =========================================================================================================\n");
                printf("Solved by unit propagation\n"); 
		printf("c real time : %g s\n", realTime() - realTimeStart);
		printf("c cpu time  : %g s\n", cpuTime());
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            exit(20);
        }
        lbool ret = msolver.solve();
	
        printf("c real time : %g s\n", realTime() - realTimeStart);
	printf("c cpu time  : %g s\n", cpuTime());
        if (msolver.verbosity() > 0){
            msolver.printFinalStats();
            printf("\n"); 
        }

        if (ret==l_True){
           vec<bool>   VarValue(org_nvars, false);
           for (int i = 0; i < org_nvars; i++)
	      if (msolver.model[i] == l_True) VarValue[i]=true;
              else VarValue[i]=false;
            verifyModel(input_file, VarValue);
            printf("c OK! verified \n");
        }

	printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");
	if(ShowModel && ret==l_True) {
	    printf("v ");
            for (int i = 0; i < org_nvars; i++)
	      if (msolver.model[i] != l_Undef)
		printf("%s%s%d", (i==0)?"":" ", (msolver.model[i]==l_True)?"":"-", i+1);
	    printf(" 0\n");
	}
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
      printf("c ===================================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
