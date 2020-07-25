#!/bin/bash

touch "./asp/res.csv";
for file in $(ls -t "./asp/test/");
do
	k=$(cat "./asp/test/$file" | grep "#const k = " | sed -e 's/#const k = //g' | sed 's/.$//');
	n=$(cat "./asp/test/$file" | grep "#const n = " | sed -e 's/#const n = //g' | sed 's/.$//');
	d=$(cat "./asp/test/$file" | grep "#const d = " | sed -e 's/#const d = //g' | sed 's/.$//');
    opt=$(clingo -t 4 "./asp/test/$file" "./asp/model.lp" --time-limit=300 | grep 'Optimization : ' | sed -e 's/Optimization : //g');
    printf "%s\t%s\t%s\t%s\t%s\t%s\n" $k $n $d $opt >> "./asp/res.csv";
done
