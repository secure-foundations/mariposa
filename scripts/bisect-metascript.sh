git bisect reset;
git bisect start;
git bisect good Z3-4.8.5;
git bisect bad z3-4.8.8;
git bisect run python3 /home/yizhou7/mariposa/scripts/bisect_utils.py $1 | tee $1.log
git bisect log >> $1.log
