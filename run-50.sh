#! /bin/bash

i=1
for file in ../SAT-Solver-DPLL/local/uf100-430/*
do
    echo $i
    ./a.out < $file 
    i=$((i+1))
done
