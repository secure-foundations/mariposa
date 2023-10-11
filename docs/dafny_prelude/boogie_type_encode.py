import os

for e in ["p", "a", "m"]:
    os.system(f"dotnet tool run boogie temp/boogie_test.bpl /typeEncoding:{e} /proverLog:temp/boogie_test.{e}.smt2")
    
