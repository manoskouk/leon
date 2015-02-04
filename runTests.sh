#!/bin/bash
log=repairs.last
summaryLog=repairs.log
fullLog=fullLog.log

echo -n "" > $log;


echo "################################" >> $summaryLog
echo "#" `hostname` >> $summaryLog
echo "#" `date +"%d.%m.%Y %T"` >> $summaryLog
echo "#" `git log -1 --pretty=format:"%h - %cd"` >> $summaryLog
echo "################################" >> $summaryLog
echo "#           Category,                 File,             function, p.S, fuS, foS,   Tms,   Fms,   Rms, verif?" >> $summaryLog

#All benchmarks:
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar1.scala     | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar2.scala     | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar3.scala     | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=desugar  testcases/repair/Desugar/Desugar4.scala     | tee -a $fullLog

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort3.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort4.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort5.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort6.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=merge    testcases/repair/HeapSort/HeapSort7.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=insert   testcases/repair/HeapSort/HeapSort8.scala   | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=makeN    testcases/repair/HeapSort/HeapSort9.scala   | tee -a $fullLog

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic1.scala | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic2.scala | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic3.scala | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic4.scala | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=nnf      testcases/repair/PropLogic/PropLogic5.scala | tee -a $fullLog

./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_pad     testcases/repair/List/List1.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_++      testcases/repair/List/List2.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_ap      testcases/repair/List/List3.scala           | tee -a $fullLog
#./leon --repair --timeout=30                       --functions=_drop    testcases/repair/List/List4.scala           | tee -a $fullLog
./leon --repair --timeout=30                       --functions=_replace testcases/repair/List/List5.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_count   testcases/repair/List/List6.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_find    testcases/repair/List/List7.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_find    testcases/repair/List/List8.scala           | tee -a $fullLog
./leon --repair --timeout=30                       --functions=_find    testcases/repair/List/List9.scala           | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=_size    testcases/repair/List/List10.scala          | tee -a $fullLog
./leon --repair --timeout=30 --solvers=fairz3:enum --functions=sum      testcases/repair/List/List11.scala          | tee -a $fullLog

# Average results
cat $log >> $summaryLog
awk '{ total1 += $7; total2 += $8; total3 += $9; count++ } END { printf "#%74s Avg: %5d, %5d, %5d\n\n", "", total1/count, total2/count, total3/count }' $log >> $summaryLog

