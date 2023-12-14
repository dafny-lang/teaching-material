#!/bin/bash

DIR=`dirname "$0"`

echo Verifying the Dafny code from the lectures

for dfyfile in `ls $DIR/Lectures/Code/*.dfy`
do
    echo '...' Verifying $dfyfile
    dafny verify $dfyfile
done

echo Verifying the solutions to the exercises

for dfyfile in `ls $DIR/Exercises/*_solution.dfy`
do
    echo '...' Verifying $dfyfile
    dafny verify $dfyfile
done
