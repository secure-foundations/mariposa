## Serval
repo: https://github.com/uw-unsat/serval

This explains how to run things pretty well:

https://unsat.cs.washington.edu/projects/serval/sosp19-artifact.html

### Serval-Komodo 

repo: https://github.com/uw-unsat/serval-sosp19

solver: `z3-4.4.2`

export status: OK

export notes:  
1. The docker image works pretty well.  `docker pull unsat/serval-tools:artifact
` then `docker run -it --name serval unsat/serval-tools:artifact`, later something like `docker start serval` and `docker attach serval`
2. I didn't find a direct option to log SMT queries. Instead I wrote a script that acts as `z3` and record the inputs. The original `z3` path is at `/code/rosette/bin/z3`
3. Some queries (I think 2 out of ~750) are supposed to be SAT. They are used to check if some top level preconditions are not vacuous. I have excluded those from the export.

cleanup notes:
1. all went pretty well, no warnings from z3 or cvc5

----
## Dafny

### Dafny-Komodo

repo: https://github.com/microsoft/Komodo

solver: `z3-4.5.0`

export status: OK

export notes: 
1. `.vad` files are using some direct verify option, not sure if I can handle those properly. Instead I set it up to generate the `.dfy` files, then verify and collect VCs later.
2. `make verified` seems to have some issues with convergence (maybe due to failures?). I needed to run it multiple times to cover all generated files. Instead, I wrote a script that verifies all `.dfy` files and export their VCs. That script does not care about import dependencies. 
4. The repo came with `z3.exe`. I was using a linux machine so I downloaded the ubuntu 14.04 release of `z3-4.5.0` and used that instead.
5. Some files have file-specific options, the export scripts run `z3` with those options. Those options are not being recorded. 
6. `smt.nl.arith` is set to false for most the files, not being recorded either.
7. Removed the body of `BitRotateRight` and `lemma_RotateRightCommutesXorSpecific` for `cvc5` compatibility issue. 

cleanup notes:
1. No major issue for `z3`, but there is a large body of unused commands after `check-sat`. 
2. Removed push and pop for `cvc5`, replaced `bv2int` with `bv2nat`. 

----
## F*

### DICE*

repo: https://github.com/verified-HRoT/dice-star

status: FAILED

export notes:
1. No docker image provided. Dockerfile exists but build fails when building F*. No revelant F* release found. 
```
File "src/extraction/ml/FStar_Extraction_ML_PrintML.ml", line 6, characters 5-31:
6 | open Migrate_parsetree.Versions
Error: Unbound module Migrate_parsetree.Versions
```
3. If we ignore the failure with F* build, Kremlin build also fails. No revelant Kremlin release found either. 
```
File "src/CFlatToWasm.ml", line 196, characters 18-32:
196 |   [ dummy_phrase (W.Ast.TeeLocal (mk_var (env.n_args + 2)));
Error: Unbound constructor W.Ast.TeeLocal
```

### VWasm
repo: https://github.com/secure-foundations/vWasm/

----
## LiquidHaskell

repo: https://github.com/ucsd-progsys/liquidhaskell


----
