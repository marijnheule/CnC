CNF=$1
DIR=~/CnC/
OUT=/tmp
#~/Folkman/vdW/march_cu/march_cu $CNF -o $DIR/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9
$DIR/march_cu/march_cu $CNF -o $OUT/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9
echo "p inccnf" > $DIR/formula$$.icnf
cat $CNF | grep -v c >> $OUT/formula$$.icnf
cat $OUT/cubes$$ >> $OUT/formula$$.icnf
rm  $OUT/cubes$$
$DIR/iglucose/core/iglucose $OUT/formula$$.icnf -verb=0
#./iglucose/core/iglucose $DIR/formula$$.icnf -verb=0 -certified -certified-output=proof | grep -v bound
rm $OUT/formula$$.icnf

