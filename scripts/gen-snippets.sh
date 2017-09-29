gen_snippets() {



FILE=$1
OUT_SRC=$2
IN_SRC=$3
EXT="agda"

STRIP_SRC=${FILE#$IN_SRC\/}
STRIP_EXT=${STRIP_SRC%.$EXT}

FILE_PREFIX="$OUT_SRC/${STRIP_EXT//\//.}"

SNIPPETS=`egrep -n '{- SNIPPET (\w|-)* -}$' $FILE \
  | awk 'BEGIN {FS=":"} NR % 2 {$2 = gensub(/^[ \t]*|[ \t]*$/,"","g",$2);\
                                split($2,a," ");
                                printf "%s %s ",$1,a[3];
                                getline;
                                print $1}END{}'`

IFS=$'\n' SNIPPET_ARRAY=($SNIPPETS)

for i in ${SNIPPET_ARRAY[*]}
do
  IFS=$' ' F=($i)
  VAR=`sed -n $((${F[0]} + 1)),$((${F[2]}-1))p $1`
  FILEV="$FILE_PREFIX.${F[1]}"
  touch $FILE
  echo "\begin{code}" >> $FILEV
  echo "$VAR"         >> $FILEV
  echo "\end{code}" >> $FILEV
done
}

$*
