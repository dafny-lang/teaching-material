#!/bin/bash

echo Verifying the Dafny code from the lectures

for dfyfile in `ls Lectures/Code/*.dfy`
do
    echo '...' Verifying $dfyfile
    dafny verify $dfyfile
done

echo Verifying the solutions to the exercises

for dfyfile in `ls Exercises/*_solution.dfy`
do
    echo '...' Verifying $dfyfile
    dafny verify $dfyfile
done
