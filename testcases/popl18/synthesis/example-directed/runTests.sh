#!/bin/bash

manualarg=${1:?"Error: expected manual 'm' or 'a'"}
grammararg=${2:?"Error: expected grammar 0 1 or 2"}
print=${3:-"no"}

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

if [ $manualarg == "m" ]
then
    mode="manual"
else
    mode="probwise"
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
    echo "Config: $manualarg $grammararg" >> synthesis-report.txt
fi
echo "==================================================================================================================" >> synthesis-report.txt

dir=testcases/popl18/synthesis/example-directed

run 0 $dir/Add.scala
run 0 $dir/Append.scala
run 0 $dir/BInsert.scala
run 0 $dir/Calc.scala
run 0 $dir/Compress.scala
run 0 $dir/CountLeaves.scala
run 0 $dir/Dequeue.scala
run 0 $dir/DictContains.scala
run 0 $dir/DictFind.scala
run 0 $dir/Diffs.scala
run 0 $dir/FreeVars.scala
run 0 $dir/IsEven.scala
run 0 $dir/Max.scala
run 0 $dir/Mult.scala
run 0 $dir/NodesAtLevel.scala
run 0 $dir/Nth.scala
run 0 $dir/Postorder.scala
run 0 $dir/Reverse.scala
run 0 $dir/RunLength.scala
run 0 $dir/Take.scala
run 0 $dir/Unzip.scala

