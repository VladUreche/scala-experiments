#!/bin/bash


if [ "$1" == "vimdiff" ]
then
    echo "Performing vimdiff for each difference"
else
    echo "To perform vimdiff for each difference, use \"$0 vimdiff\""
fi  

rm -f *.class *.icode
$SCALA_BUILD/scalac -optimise -Ydebug -Xprint-icode TestInlineExceptionHandlersSmall.scala #-Ylog:inlineExceptionHandlers
for a in `ls *.icode.check`
do
    echo $a:
    diff $a ${a/\.check/} &> result
    if [ $? -ne 0 -a "$1" == "vimdiff" ]
    then        
         echo vimdiff $a ${a/\.check/}
         vimdiff $a ${a/\.check/}
    else
         head -n 5 result
    fi
    rm -rf result
done
