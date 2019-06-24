CNF=$1
DIR=/tmp
#~/Folkman/vdW/march_cu/march_cu $CNF -o $DIR/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9
./march_cu/march_cu $CNF -o $DIR/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9
echo "p inccnf" > $DIR/formula$$.icnf
cat $CNF | grep -v c >> $DIR/formula$$.icnf
cat $DIR/cubes$$ >> $DIR/formula$$.icnf
rm  $DIR/cubes$$
./iglucose/core/iglucose $DIR/formula$$.icnf -verb=0
#./iglucose/core/iglucose $DIR/formula$$.icnf -verb=0 -certified -certified-output=proof | grep -v bound
rm $DIR/formula$$.icnf

