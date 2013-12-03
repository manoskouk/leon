#!/bin/bash

for file in *.scala ; do
    scalac -d memoOut/bin -classpath ~/Documents/Leon/library/target/scala-2.10/classes $file
done

