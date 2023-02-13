| |z3_4_4_2|z3_4_5_0|z3_4_6_0|z3_4_8_5|z3_4_11_2|cvc5_1_0_3|
|:---------:|:---------:|:---------:|:---------:|:---------:|:---------:|:---------:|
|d_frames_vbkv|1.48%~2.5%, 0.86%|1.5%~2.37%, 0.77%|0.96%~1.92%, 1.07%|-~-, -|1.62%~4.36%, 2.57%|-~-, -|
|fs_vwasm|1.65%~1.82%, 0.17%|1.71%~1.88%, 0.11%|2.51%~2.51%, 0.06%|2.51%~2.56%, 0.11%|2.51%~2.62%, 0.11%|-~-, -|
|s_komodo|0.39%~1.68%, 4.14%|0.39%~1.68%, 3.49%|0.65%~1.16%, 0.65%|0.13%~0.78%, 2.59%|0.52%~1.42%, 4.79%|1.03%~1.03%, 0%|
|d_komodo|-~-, -|1.95%~3.46%, 4.33%|-~-, -|-~-, -|5.15%~8.31%, 7.34%|85.35%~86.32%, 1.22%|

cvc5 options to speed up queries (auto-config)

figure out which option is making z3 fast


## Query Collection Tasks:

for details see [projects](projects.md)

## Engineering Tasks:

* Advanced command shuffling
* Dumping and parsing the unsat cores 
* Testing perturbations (did we perturb correctly?)
* Erasing triggers (should be easy)

## Literature Questions:

* Variance Estimate: How to estimate the variance of a population?
Can we obtain confidence intervals for estimated variance?

* Average Time Estimate: We have a skewed distribution for run time due to timeouts. Can we still use t-score and obtain confidence intervals?

* Syntactic Similarity: Are there metrics that compare syntactic similarity between queries? Are there syntactic complexity metrics?

* Hardness of Canonization: CNF isomorphism (CNFI) is GI complete. CNF
canonization (CNFC) is at least as hard as CNF isomorphism. Is CNFC strictly
harder than CNFI? What about SMT isomorphism? What about SMT canonization
(SMTC)?
