#!/bin/bash

modearg=${1:?"Error: expected algorithm 'ste' or 'prob'"}
manualarg=${2:?"Error: expected manual 'm' or 'a'"}
grammararg=${3:?"Error: expected grammar 0 1 or 2"}
print=${4:-"no"}

if [ "$grammararg" == 1 ]
then
    grammar=testcases/popl18/Grammar1Tags.scala
    axioms=on
    userdefined="--userdefined"
    dir=testcases/popl18/synthesis
elif [ $grammararg == 2 ]
then
    grammar=testcases/popl18/Grammar2.scala
    axioms=off
    userdefined="--userdefined"
    dir=testcases/popl18/synthesis
elif [ $grammararg == 0 ]
then
    grammar=testcases/popl18/GrammarEmpty.scala
    axioms=on
    userdefined=""
    dir=testcases/synt2016/synthesis
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
    if [ $print == "print" ] 
    then
        echo $cmd
    else
        echo "Running " $cmd
        echo "------------------------------------------------------------------------------------------------------------------"
        $cmd;
    fi
}

echo "==================================================================================================================" >> synthesis-report.txt
if [ $print != "print" ] 
then
    echo "Config: $manualarg $modearg $grammararg" >> synthesis-report.txt
fi
echo "==================================================================================================================" >> synthesis-report.txt

# List
run "$rule" $dir/List/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/List/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule $dir/List/Union.scala
run 4,0,$rule,1,0,0,$rule $dir/List/Diff.scala
run 3,0,0,1,0,0,0,0,$rule $dir/List/Split.scala
run 3,0,0,1,0,0,$rule     $dir/List/ListOfSize.scala

# SortedList
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/SortedList/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/SortedList/InsertAlways.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/SortedList/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule $dir/SortedList/Union.scala
run 4,0,$rule,1,0,0,$rule $dir/SortedList/Diff.scala
run 3,0,0,1,0,0,$rule     $dir/SortedList/InsertionSort.scala

# StrictSortedList
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/StrictSortedList/Insert.scala
run 4,0,$rule,1,0,0,3,0,$rule,1,$rule,2,$rule $dir/StrictSortedList/Delete.scala
              # $rule
run 3,0,$rule,1,0,0,$rule $dir/StrictSortedList/Union.scala

# UnaryNumerals
run 3,0,$rule,1,0,0,$rule $dir/UnaryNumerals/Add.scala
run $rule                 $dir/UnaryNumerals/Distinct.scala
run 3,0,$rule,1,0,0,$rule $dir/UnaryNumerals/Mult.scala

# BatchedQueue
run 0,0,3,0,$rule,1,$rule             $dir/BatchedQueue/Enqueue.scala
run 0,0,3,0,$rule,1,3,0,$rule,1,$rule $dir/BatchedQueue/Dequeue.scala

# AddressBook
run 3,0,0,1,0,0,0,0,0,0,3,0,$rule,1,$rule $dir/AddressBook/Make.scala
run 0,0,$rule                             $dir/AddressBook/Merge.scala

# RunLength
run 3,0,0,1,0,0,4,0,$rule,1,0,0,3,0,$rule,1,$rule $dir/RunLength/RunLength.scala

# Diffs
run 3,0,0,1,0,0,5,0,$rule,1,$rule $dir/Diffs/Diffs.scala

