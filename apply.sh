CNF=$1
CUBES=$2
LINE=$3

EXTRA=`head -n $LINE $CUBES | tail -n 1 | awk '{print NF-2}'`
cat $CNF | awk '/ 0/ {print $0} /cnf/ {print "p cnf " $3 " " $4 + '$EXTRA'}'
head -n $LINE $CUBES | tail -n 1 | sed 's|a ||' | sed 's|[-]*[0-9]* |&0X|g' | tr "X" "\n" | awk '{if (NF == 2) print $0}'
