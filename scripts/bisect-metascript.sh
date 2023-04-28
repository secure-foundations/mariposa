#!/bin/bash

# OUTPUT_LOG_FILE='bisect.log'

# parallel=$2
# smt=$1
# logfile="~/logs/$(echo $smt | sed 's/smt2$/log/g')"

# # check if the logfile exists. Then don't rerun.
# if !(cat $logfile | grep  'is the first bad commit')
# then
# # Not done yet
# # need to git bisect
#  cd $parallel
#  git bisect reset;
#  git bisect start;
#  git bisect good Z3-4.8.5;
#  git bisect bad z3-4.8.8;
#  /usr/bin/time git bisect run python3 /scripts/z3-bisect.py /home/ytakashima/smt-unstable/$smt $parallel | tee $OUTPUT_LOG_FILE
# mv $OUTPUT_LOG_FILE $logfile
# else
# echo "Skipping: already done. See $logfile"
# fi

git bisect reset;
git bisect start;
git bisect good Z3-4.8.5;
git bisect bad z3-4.8.8;
/usr/bin/time git bisect run python3 ./scripts/z3-bisect.py data/bisect_tasks/d_fvbkv_z3_clean--Betree-BetreeInv.i.dfy.Impl__BetreeInv.__default.InitImpliesInv.txt 
#  | tee $OUTPUT_LOG_FILE