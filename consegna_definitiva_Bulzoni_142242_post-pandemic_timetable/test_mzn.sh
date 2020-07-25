#!/bin/bash
touch "./mzn/res.csv";
for file in $(ls -t "./mzn/test/");
do
	# Per ognuno dei file va eseguito il solver Gecode con time limit di 5 minuti
	# I risultati delle soluzioni dovrebbero essere salvati in un file result.txt
	# ogni riga di tale file dovrebbe avere come identificatore il file corrispondente
	# e come colonne i parametri K e N, ed infine il tempo di sanificazione e lo sbilancio tra
	# studenti soddisfatti nei diversi dipartimenti.
    minizinc -p 4 --time-limit 300000 "./mzn/model.mzn" "./mzn/test/$file" | tail -2 | head -n 1 >> "./mzn/res.csv";
    # minizinc -p 4 --time-limit 300000 "./mzn/model.mzn" "./mzn/test/$file" >> "./mzn/res.csv"
done

# touch "./asp/res.csv";
# for file in $(ls -t "./asp/test/");
# do
# 	k=$(cat "./asp/test/$file" | grep "#const k = " | sed -e 's/#const k = //g' | sed 's/.$//');
# 	n=$(cat "./asp/test/$file" | grep "#const n = " | sed -e 's/#const n = //g' | sed 's/.$//');
#     opt=$(clingo -t 4 "./asp/test/$file" "./asp/model.lp" --time-limit=300 | grep 'Optimization : ' | sed -e 's/Optimization : //g');
#     printf "%s\t%s\t%s\t%s\t%s\n" $k $n $opt >> "./asp/res.csv";
# done
