# Mariposa

Mariposa is a tool for testing SMT proof stability.  Given a query and a solver, Mariposa:
* performs mutations to the query
* run the solver on the mutants
* report the stability status based on the performance of the mutants

## Prerequisites

In the current setup, the compressed database files from past experiments are all part of the commit history. Therefore, we recommend avoid fetching the full history when cloning this repository:

```
git clone --filter=blob:none git@github.com:secure-foundations/mariposa.git
```

We have some rust code that parses and mutates queries, to compile this part:

```
cargo build --release
```

We have some python code that performs the experiments and analysis. This part was written using `python 3.8.10` (and not well tested on other versions). To install the required packages:

```
pip3 install -r requirements.txt
```
## Quick Start

To perform a basic sanity check:
```
python3 scripts/main.py single -s z3_4_12_1 -q data/samples/single_check.smt2
```
This will test the stability of the query `data/samples/single_check.smt2` on the solver `Z3 4.12.1`, using the default settings. The result should be something like this:

```
solver used: solvers/z3-4.12.1
query: gen/single_check.smt2_/split.1.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | stable   | x            | x              | x             |
| shuffle    | stable   | 61/61 100.0% | 0.02           | 0.0           |
| rename     | stable   | 61/61 100.0% | 0.02           | 0.0           |
| reseed     | stable   | 61/61 100.0% | 0.02           | 0.0           |
```
This solver and query pair is expected to be stable. The first row is the overall status, which should be `stable`. Each row that follows is a summary of results from a mutation method, which includes the success rate, mean of response times, and standard deviation of response times. The success count is also given. Using the default configuration, in addition to the original query, `60` mutants are generated for each mutation method, `61/61` means all the mutants succeeded. 

## Configurations

The experiment or analysis results could differ drastically based on the specific 
configurations. Since there are many configuration parameters and easy to lose track, the parameters are loaded from `configs.json`, which provides several predefined settings. If one wishes to use a different setting, we recommend extending the `configs.json`, which contains 4 parts.

### Experiments

Under the key `experiments`, there are a few predefined settings on how to run the experiments. 

* `mutations` is the enabled mutation methods, where currently only `shuffle`, `rename`, `reseed` are supported.
* `num_mutants` is the number of mutants to generate for each mutation method. It is set to `60` In the following example, so `shuffle`, `rename`, `reseed` will each generate `60` mutants, `180` in total.
* `keep_mutants` controls whether the mutant will be removed after the experiment. Usually only set to `true` for debugging, since mutants can occupy a lot of space.
* `init_seed` TBD.
* `exp_timeout` is the time limit in seconds for the solver to run on each mutant.
* `num_procs` is the number of processes in parallel when performing the experiments. We recommend setting this to be at most **number_of_physical_cores - 1**. 
* `db_path` is the database file to store the results. This is automatically taken care of in the `single` mode, as explained below. 
* `db_mode` TBD.

```
{
    "name": "main",
    "mutations": [
        "shuffle",
        "rename",
        "reseed"
    ],
    "num_mutants": 60,
    "keep_mutants": false,
    "init_seed": "",
    "exp_timeout": 60,
    "num_procs": 7,
    "db_path": "./data/mariposa.db",
    "db_mode": "update"
}
```
### Analyzers

Under the key `analyzers`, there are a few predefined settings on how to run the analysis. 

* `ana_timeout` is the time limit in seconds used in the analysis, which can be different from the `exp_timeout` above. One may want to test out smaller `ana_timeout` thresholds and see how the results differ.
* `confidence` is the confidence level used in hypothesis tests.
* `r_solvable` is the threshold between `unsolvable` and `unstable` query in terms of the success rate. 
* `r_stable` is the threshold between `unstable` and `stable` query in terms of the success rate. 
* `discount` TBD.

```
{
    "name": "default",
    "ana_timeout": 60,
    "confidence": 0.05,
    "r_solvable": 0.05,
    "r_stable": 0.95,
    "discount": 0.8
}
```
### Solvers

Under the key `solvers`. there are a few predefined solvers. 

* `path` is where the solver can be found. When adding a solver, one does not have to follow the naming convention.
* `date` is the date when the solver was released. 

```
{
    "name": "z3_4_4_2",
    "path": "solvers/z3-4.4.2",
    "date": "2015/10/05"
}
```
### Projects

Under the key `projects`, there are a few predefined projects. A project specifies a collection of **preprocessed** queries in a directory. The directory contains only `*.smt2` files and no nested directories. Each `.smt2` file contains one `(check-sat)` command and is parsable by Mariposa. `preprocess` mode can be used to produce such directory (explained later). 

* `frame_work` is not important. 
* `clean_dir` is the directory that contains the preprocessed queries.
* `artifact_solver_name` is the solver that the project was using, which should match one of the definitions under `solvers`. 

```
{
    "name": "s_komodo",
    "frame_work": "serval",
    "clean_dir": "data/s_komodo_z3_clean",
    "artifact_solver_name": "z3_4_4_2"
},
```

## Use Cases

The python script `scripts/main.py` is the main interface of Mariposa. It has a required argument for operation mode, which is either `single`, `multiple` or `preprocess`.

* `single` mode "quickly" tests out the stability of a single query solver pair.
* `multiple` mode performs experiments on a predefined project (in the `configs.json`), which can contain many queries that is already *preprocessed*. 
* `preprocess` gathers and cleans the queries so that they can be ran in the `multiple` mode. 

### Sanity Check

To perform a basic sanity check:
```
python3 scripts/main.py single -s z3_4_12_1 -q data/samples/single_check.smt2
```
This will test the stability of `Z3 4.12.1` on the query `data/samples/single_check.smt2`, using the default settings. The result should be something like this:

```
solver used: solvers/z3-4.12.1
query: gen/single_check.smt2_/split.1.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | stable   | x            | x              | x             |
| shuffle    | stable   | 61/61 100.0% | 0.02           | 0.0           |
| rename     | stable   | 61/61 100.0% | 0.02           | 0.0           |
| reseed     | stable   | 61/61 100.0% | 0.02           | 0.0           |
```
This solver and query pair is expected to be stable. The first row is the overall status, which should be `stable`. Each row that follows is a summary of results from a mutation method, which includes the success rate, mean of response times, and standard deviation of response times. The success count is also given. Using the default configuration, in addition to the original query, `60` mutants are generated for each mutation method, `61/61` means all the mutants succeeded. 

### Single Mode 

`single` is generally used for a "quick" stability test of a single query and a solver. The two required arguments for this mode are:
* `-q/--query`, the path to the query 
* `-s/--solver`, the name of the solver (see `configs.json`)

The results are stored in a temporary database under `gen/`. This mode can handle a query with multiple `(check-sat)` commands. In that case, the input query will be split for each `(check-sat)`. For example: 
```
python3 scripts/main.py single -s z3_4_12_1 -q data/samples/multiple_checks.smt2
```
The query file actually contains 3 `(check-sat)` commands. The split queries are placed in `gen/multiple_checks.smt2_/`, which is named after the query that was ran.
```
[INFO] single mode will use db gen/multiple_checks.smt2_/test.db
[INFO] data/samples/multiple_checks.smt2 is split into 3 file(s)
[INFO] created table single_misc_z3_4_12_1_exp
[INFO] 550 tasks queued
[INFO] workers finished
[INFO] post processing exp data
solver used: solvers/z3-4.12.1
query: gen/multiple_checks.smt2_/split.3.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | stable   | x            | x              | x             |
| shuffle    | stable   | 61/61 100.0% | 0.02           | 0.0           |
| rename     | stable   | 61/61 100.0% | 0.02           | 0.0           |
| reseed     | stable   | 61/61 100.0% | 0.02           | 0.0           |
query: gen/multiple_checks.smt2_/split.2.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | stable   | x            | x              | x             |
| shuffle    | stable   | 61/61 100.0% | 0.02           | 0.0           |
| rename     | stable   | 61/61 100.0% | 0.02           | 0.0           |
| reseed     | stable   | 61/61 100.0% | 0.02           | 0.0           |
query: gen/multiple_checks.smt2_/split.1.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | stable   | x            | x              | x             |
| shuffle    | stable   | 61/61 100.0% | 0.02           | 0.0           |
| rename     | stable   | 61/61 100.0% | 0.02           | 0.0           |
| reseed     | stable   | 61/61 100.0% | 0.02           | 0.0           |
```
The temporary database is `gen/multiple_checks.smt2_/test.db`, as the debug info suggests. One can also repeat the analysis without the experiment:
```
python3 scripts/main.py single -s z3_4_12_1 -q data/samples/multiple_checks.smt2 --analysis-only
```
The above will load the temporary database. 

### Preprocess Mode 


### Multiple Mode 

`multiple` mode can be used for larger scale stability testing over a project. A project must be already defined in the `configs.json` and gone through the `preprocess`. To run a project named `dummy`:

```
python3 scripts/main.py multiple -p dummy -s z3_4_12_1 -e test 
```
`dummy` contains 4 queries, 2 of which are unstable.
```
project directory: data/dummy_clean
solver used: solvers/z3-4.12.1
total queries: 4
|--------------|-------|------------|
| category     | count | percentage |
| stable       | 2     | 50.0       |
| unstable     | 2     | 50.0       |
| inconclusive | 0     | 0.0        |
| unsolvable   | 0     | 0.0        |

listing unstable queries...

query: data/dummy_clean/lib-Lang-LinearSequence.i.dfy.Impl__LinearSequence__i.__default.AllocAndMoveLseq.smt2
| mutation   | status   | success     | mean(second)   | std(second)   |
|------------|----------|-------------|----------------|---------------|
| overall    | unstable | x           | x              | x             |
| shuffle    | unstable | 38/61 62.3% | 0.16           | 0.01          |
| rename     | unstable | 44/61 72.1% | 0.16           | 0.01          |
| reseed     | unstable | 52/61 85.2% | 0.16           | 0.01          |

query: data/dummy_clean/verified-sha-sha256.i.dfyImpl___module.__default.lemma__SHA256FinalHelper1.smt2
| mutation   | status   | success      | mean(second)   | std(second)   |
|------------|----------|--------------|----------------|---------------|
| overall    | unstable | x            | x              | x             |
| shuffle    | unstable | 55/61 90.2%  | 0.72           | 0.15          |
| rename     | unstable | 53/61 86.9%  | 0.76           | 0.23          |
| reseed     | stable   | 61/61 100.0% | 0.49           | 0.01          |

```
