#!/bin/bash

# test one file
function testFile {
    outFile=memoOut/src/$1
    leon --memo=$outFile $1
    out=$?
    if [ $out -eq 0 ] ; then
        scalac -classpath memoOut/bin -d memoOut/bin $outFile
        out=$?
        if [ $out -eq 0 ] ; then
            echo "$1 compiled successfully"
        else 
            echo "$1 failed"
        fi
    else 
        echo "$1 failed"
    fi

}


if [ $# -eq 0 ] ; then 
    echo "No arguments"
    echo "Please give file list or --all"
    exit 1
fi

# Make output folders 
if ! [ -a memoOut/src ] ; then
    mkdir memoOut/src
fi
if ! [ -a memoOut/bin ] ; then
    mkdir memoOut/bin
fi

if [ $1 == "--all" ] ; then
    # if -all is given, test all *.scala files
    echo "Testing all testcases in this directory..."
    echo ""
    files=*.scala
else
    # otherwise, test given files
    files=$@
fi
for file in $files ; do 
    echo "===== Testing $file ====="
    testFile $file
    echo "======================================"
done

