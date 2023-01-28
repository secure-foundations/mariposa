## Serval
repo: https://github.com/uw-unsat/serval

### Serval-Komodo
repo: https://github.com/uw-unsat/serval-sosp19
solver: `z3-4.4.2`

notes:  
1. The docker image works pretty well.  `docker run -it --name serval unsat/serval-tools:artifact` then later something like `docker start serval` and `docker attach serval`
2. I didn't find a direct option to log SMT queries. Instead I wrote a script that acts as `z3` and record the inputs. The original `z3` path is at `/code/rosette/bin/z3`
3. Some queries (I think 2 out of ~750) are supposed to be SAT. They are used to check if some top level preconditions are not vacuous. I have excluded those from the export.

## Dafny

### Dafny-Komodo
repo: https://github.com/microsoft/Komodo
solver: `z3-4.5.0`

notes:  
1. `.vad` files are using some direct verify option, not sure if I can handle those properly. Instead I set it up to generate the `.dfy` files, then verify and collect VCs later.
2. `make verified` seems to have some issues with convergence (maybe due to failures?). I needed to run it multiple times to cover all generated files. Instead, I wrote a script that verifies all `.dfy` files and export their VCs. That script does not care about import dependencies. 
4. The repo came with `z3.exe`. I was using a linux machine so I downloaded the ubuntu 14.04 release of `z3-4.5.0` and used that instead.
5. Some files have file-specific options, the export scripts run `z3` with those options. Those options are not being recorded. 
6. `smt.nl.arith` is set to false for most the files, not being recorded either.

----
## F*

### DICE*
repo: https://github.com/verified-HRoT/dice-star

### VWasm
repo: https://github.com/secure-foundations/vWasm/

----
## LiquidHaskell

repo: https://github.com/ucsd-progsys/liquidhaskell


----
