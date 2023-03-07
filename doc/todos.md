

## Ecosystem Characterization Experiments:

### Z3 regression:

- [ ] figure out the conmmit between 4.8.5 and 4.8.6 that "broke" things?

### Making CVC5 work:

- [x] ping cvc5 guy

- [ ] cvc5 longer timeout?

- [ ] run cvc5 on F* projects

- [ ] finding cvc5 configs** <- this is esay

### Finding (more) unstable from unsolvable/stable

- [ ] longer timeouts on "unsolvable" parts <- small scale

- [ ] dice* shuffle

## Query Collection Tasks:

for details see [projects](projects.md)

## Engineering Tasks:

- [ ] Advanced command shuffling
- [ ] Dumping and parsing the unsat cores 
- [ ] Testing perturbations (did we perturb correctly?)
- [x] Erasing triggers (should be easy)

## Literature Questions:

* Variance Estimate: How to estimate the variance of a population?
Can we obtain confidence intervals for estimated variance?

* Average Time Estimate: We have a skewed distribution for run time due to timeouts. Can we still use t-score and obtain confidence intervals?

* Syntactic Similarity: Are there metrics that compare syntactic similarity between queries? Are there syntactic complexity metrics?

* Hardness of Canonization: CNF isomorphism (CNFI) is GI complete. CNF
canonization (CNFC) is at least as hard as CNF isomorphism. Is CNFC strictly
harder than CNFI? What about SMT isomorphism? What about SMT canonization
(SMTC)?
