## Configurations

Mariposa supports many configuration options that can drastically affect the outcome of your experiments.
These options are loaded from the `config/` directory, which provides several predefined settings.
To use a different setting, we recommend modifying the config files.

### Experiments

`config/expers.json` configures how the experiments are run. 

* `mutations` is a list of enabled mutation methods; currently `shuffle`, `rename`, `reseed` and `quake` are supported.
* `keep_mutants` controls whether the files containing the mutants will be removed after the experiment. Usually only set to `true` for debugging, since mutants can occupy a lot of space.
* `num_mutants` is the number of mutants to generate for each mutation method. It is set to `60` In the previous example, so `shuffle`, `rename`, `reseed` each generated `60` mutants for `180` in total.
* `exp_timeout` is the time limit in seconds for the solver to run on each mutant.
* `num_procs` is the number of processes to run in parallel when performing the experiments. We recommend setting this to be at most **number_of_physical_cores - 1**. 

There is a `default` configuration. Creating a new experiment configuration will **inherit this default setting**, while overriding specified fields using the new configuration. 

### Analyzers

`config/analyzers.json` 

There are a few predefined settings that control how the analysis is performed. The stability of a query can be classified as `unsolvable`, `unstable`, `stable`, or `inconclusive`. The classification depends on the query's success rate, like so:

```
    consistently                             consistently
        poor            inconsistent             good
0% |-----------|----------------------------|-----------|  100%
          r_solvable                    r_stable
                     mutant success rate
```

When a query's success rate, `r`, is greater than `r_stable`, it is stable. When `r` is less than `r_solvable`, it is unsolvable. Otherwise, it is unstable. The analysis can also be inconclusive for a variety of reasons (too small of a sample size, p value not low enough, etc.).

* `timeout` is the time limit in seconds used in the analysis, which can be different from the `exp_timeout` above. One may want to test out smaller `ana_timeout` thresholds and see how the results differ.
* `confidence` is the confidence level used in hypothesis tests.
* `r_solvable` is the threshold between an `unsolvable` and `unstable` query in terms of the success rate. 
* `r_stable` is the threshold between an `unstable` and `stable` query in terms of the success rate. 
* `discount` is used to account for stable queries that solve close to the time limit which could be falsely considered unstable. If queries are found to be unstable after an instability test, the mean runtime of the query and mutants, T, is taken into consideration. If T is greater than or equal to the discount * solver timeout time (`exp_timeout`), the query is not immediately labeled as unstable and will continue to a stability test where it can be categorized as inconclusive or stable.

### Solvers

`config/solvers.json` 

Under the key `solvers`, there are a few predefined solvers. 

* `path` is where the solver can be found. 
* `date` is the date when the solver was released. 

Please note that the solver name **should** start with either `z3` or `cvc5`, which mariposa needs to know in order to drive the solver binary properly. Other solvers are currently not supported yet, but PRs are welcome. 