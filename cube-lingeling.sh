DIR=/tmp
CNF=$1
./march_cu/march_cu $CNF -o $DIR/cubes$$ $2 $3 $4 $5 $6 $7 $8 $9
echo "p inccnf" > $DIR/formula$$.icnf
cat $CNF | grep -v c >> $DIR/formula$$.icnf
cat $DIR/cubes$$ >> $DIR/formula$$.icnf
time ./lingeling/ilingeling $DIR/formula$$.icnf -b 8
rm $DIR/formula$$.icnf
