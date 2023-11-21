./target/release/mariposa -i temp/woot.smt2 -o temp/freq1 -m tree-shake-idf
./target/release/mariposa -i temp/woot.smt2 -o temp/out1.smt2 -m tree-shake --command-score-path temp/log1.txt
python3 scripts/diff_smt.py shake-layers temp/woot.smt2 temp/core.smt2 temp/log1.txt temp/freq1 > temp/parsed1.txt
# ./target/release/mariposa -i temp/woot.smt2 -o temp/freq2 -m tree-shake-idf
./target/release/mariposa -i temp/woot.smt2 -o temp/out2.smt2 -m tree-shake --command-score-path temp/log2.txt --shake-max-symbol-frequency 10 --shake-max-depth 6
python3 scripts/diff_smt.py shake-layers temp/woot.smt2 temp/core.smt2 temp/log2.txt temp/freq1 > temp/parsed2.txt
./target/release/mariposa -i temp/woot.smt2 -o temp/out3.smt2 -m tree-shake --command-score-path temp/log3.txt --shake-max-symbol-frequency 10 --shake-max-depth 5
python3 scripts/diff_smt.py shake-layers temp/woot.smt2 temp/core.smt2 temp/log3.txt temp/freq1 > temp/parsed3.txt
