import sys, os, subprocess, re, platform
from subprocess import PIPE, Popen
from os.path import exists
from parse_lib import *
import json

def rules():
    return f"""
rule instrument-query
    command = ./target/release/mariposa -i $in -o $out -p "unsat-core"
rule get-cores
    command = ./solvers/z3-4.12.1 $in > $out
rule minimize-query
    command = 
"""
