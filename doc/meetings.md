## April 4st:

present:
* plain query vs median time

disucss:
* plain perf regression vs delta?
* next step experiment plans

## March 28st:

present:

* current overall figure (adjusted for unknown in the original solver query set pair)
* figures on time cutoff vs. instablity vs. perturbations 
* figures on extended timeout experiments 
* figure on linear vs. dynamic vbkv
* figure on query sizes
* CertiKOS export [Yoshi]
  * SAT queries are because of state machine refinements that are being sanity checked. They are from called as part of serval, not the project or Rosette itself
* git bisection [Yoshi]

discuss:
* potential deadlines: May 5th ASE, and May 11th FSE (industry track)
* what should instability measure? regression? divergence? both?
  * regression assumes something special about the plain query, then measures the delta between the plain and the mutants
  * divergence treats the plain as one sample of any perturbation group, then measures the variance within that group
  * high regression does not necessarily imply high divergence (mutants might be bad, but very consistently bad)
  * high divergence tends to imply regression (mutants differ, so at least some badness exists)

## March 21st:

meeting was canceled 

## March 14th:

* some experiment results on the new configs (60 seconds 60 instances, shortcut removed, 7 cores only)
 * 60 is probably overkill for a non-normal distribution?
 * false discovery rate https://www.statisticshowto.com/false-discovery-rate/
 * adjusting the timeouts and std thresholds and get different results
* unsolvable queries in the previous experiments
* cvc5 testing?
* db spliting


## March 7th:

present:

* current overall fig
* current categorization of queries
  * z-test for unsolvable/result stable
  * chi2-test for time unstable
* selection of timelimit and success rate cutoff
* pattern removal

discuss:

* z3 regression
* triaging of tasks
  * esp. eco-system vs moving on to controlled experiments?
* db too large for git?

## Feb 21th:

present:

* database schema updates
* DICE* results
* overall figure
* z3 seed option difference
* shuffle experiment
* cvc nl arith option (14% -> 22%)
* unsolvable correlation
* time varaince on stable queries
* average time on unstable queries (15s jump in df vbkv？)

discuss:
* what should be considered unsolvable? 
  * current: the intersection of everything (the original and the mutant all failed).
  * alterative: the plain result as predictor of solvability (?) the overall picture can inlcude the plain performance as well.

proposed changes:
 * use 40 seconds timeouts, cut off (say 30s) post experiment is adjustable  
 * use both sat-seed and smt-seed for randomization options

## Feb 14th:

* update on F* project exports
* present the summary graph
* advanced shuffling?

## Feb 7th:

* present some initial analysis on the current experiments 
   * time varaince cdf
   * sucess rate cdf
   * compare different perturbations
* plan on the z3 atuo-config and cvc5
   * what is the person to ask?

## Jan 31st

Tentative agenda:
* present current experiment setup
    * query cleaning
    * termination criterion
        * max and min sample sizes
        * timeout limit
        * number of processes
        * generated mutants not reused
    * config options
    * database setup
* present initial experiment results
* discuss current experiment setup
    * improve experiment efficiency?
    * non-standard options are ignored?
* discuss inclusion of sat queries
* discuss other projects to include
    * is there something more tailored to cvc4/5?
    * also what other solvers to include?
