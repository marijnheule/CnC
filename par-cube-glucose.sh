CNF=$1
PAR=4
DIR=~/CnC/
OUT=/tmp

rm $OUT/output*.txt
$DIR/march_cu/march_cu $CNF -o $OUT/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9

while [ 1 ]
do
  cat $OUT/output*.txt | grep "SAT" | awk '{print $1}' | sort | uniq -c | tr "\n" "\t";
  SAT=`cat $OUT/output*.txt | grep "^SAT" | awk '{print $1}' | uniq`
  if [[ $SAT == "SAT" ]]
  then
    echo "DONE"
    pkill -TERM -P $$
  fi
  UNSAT=`cat $OUT/output*.txt | grep "^UNSAT" | wc |awk '{print $1}'`
  if [[ $UNSAT == $PAR ]]
  then
    echo "DONE"
    pkill -TERM -P $$
  fi
  sleep 1;
done &

for (( CORE=0; CORE<$PAR; CORE++ ))
do
  echo "p inccnf" > $OUT/formula$$-$CORE.icnf
  cat $CNF | grep -v c >> $OUT/formula$$-$CORE.icnf
  awk 'NR % '$PAR' == '$CORE'' $OUT/cubes$$ >> $OUT/formula$$-$CORE.icnf
  $DIR/iglucose/core/iglucose $OUT/formula$$-$CORE.icnf $OUT/output-$CORE.txt -verb=0 &
done
wait

rm $OUT/cubes$$
for (( CORE=0; CORE<$PAR; CORE++ ))
do
  rm $OUT/formula$$-$CORE.icnf
done
