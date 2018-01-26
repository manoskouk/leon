#!/bin/bash

modearg=${1:?"Error: expected algorithm 'ste' or 'prob'"}
manualarg=${2:?"Error: expected manual 'm' or 'a'"}
grammararg=${3:?"Error: expected grammar 0 1 or 2"}

if [ "$grammararg" == 1 ]
then
    grammar=testcases/popl18/Grammar1Tags.scala
    axioms=on
    userdefined="--userdefined"
elif [ $grammararg == 2 ]
then
    grammar=testcases/popl18/Grammar2.scala
    axioms=off
    userdefined="--userdefined"
elif [ $grammararg == 0 ]
then
    grammar=testcases/popl18/GrammarEmpty.scala
    axioms=on
    userdefined=""
else 
    echo "Whoot?? wrong grammar"
fi

if [ $modearg == "ste" ]
then
    rule=1
else
    rule=2
fi

if [ $manualarg == "m" ]
then
    mode="manual"
else
    if [ $modearg == "ste" ]
    then
        mode="default"
    else
        mode="probwise"
    fi
fi


function run {
    cmd="./leon --debug=report --timeout=60 --synthesis $userdefined --partial=off \
                --mode=$mode --manual:script=$1 $grammar --probwise:axioms=$axioms $2"
    echo "Running " $cmd
    echo "------------------------------------------------------------------------------------------------------------------"
    $cmd;
}

echo "==================================================================================================================" >> synthesis-report.txt
echo "Config: $manualarg $modearg $grammararg" >> synthesis-report.txt
echo "==================================================================================================================" >> synthesis-report.txt

# List
run "$rule" testcases/popl18/synthesis/List/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/List/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule testcases/popl18/synthesis/List/Union.scala
run 4,0,$rule,1,0,0,$rule testcases/popl18/synthesis/List/Diff.scala
run 3,0,0,1,0,0,0,0,$rule testcases/popl18/synthesis/List/Split.scala
run 3,0,0,1,0,0,$rule testcases/popl18/synthesis/List/ListOfSize.scala

# SortedList
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/SortedList/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/SortedList/InsertAlways.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/SortedList/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule testcases/popl18/synthesis/SortedList/Union.scala
run 4,0,$rule,1,0,0,$rule testcases/popl18/synthesis/SortedList/Diff.scala
run 3,0,0,1,0,0,$rule testcases/popl18/synthesis/SortedList/InsertionSort.scala

# StrictSortedList
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/StrictSortedList/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule testcases/popl18/synthesis/StrictSortedList/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule testcases/popl18/synthesis/StrictSortedList/Union.scala

# UnaryNumerals
run 3,0,$rule,1,0,0,$rule testcases/popl18/synthesis/UnaryNumerals/Add.scala
run $rule             testcases/popl18/synthesis/UnaryNumerals/Distinct.scala
run 3,0,$rule,1,0,0,$rule testcases/popl18/synthesis/UnaryNumerals/Mult.scala

# BatchedQueue
run 0,0,3,0,$rule,1,$rule testcases/popl18/synthesis/BatchedQueue/Enqueue.scala
run 0,0,3,0,$rule,1,3,0,$rule,1,$rule testcases/popl18/synthesis/BatchedQueue/Dequeue.scala

# AddressBook
run 3,0,0,1,0,0,0,0,0,0,3,0,$rule,1,$rule testcases/popl18/synthesis/AddressBook/Make.scala
run 0,0,$rule testcases/popl18/synthesis/AddressBook/Merge.scala

# RunLength
run 3,0,0,1,0,0,4,0,$rule,1,0,0,3,0,$rule,1,$rule testcases/popl18/synthesis/RunLength/RunLength.scala

# Diffs
run 3,0,0,1,0,0,5,0,$rule,1,$rule testcases/popl18/synthesis/Diffs/Diffs.scala

