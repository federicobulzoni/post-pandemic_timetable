#!/bin/bash
PATH_TEST="test";
PATH_RES="res";

cd $PATH_TEST;
for i in $(ls -t *.dzn);
do
	# Per ognuno dei file va eseguito il solver Gecode con time limit di 5 minuti
	# I risultati delle soluzioni dovrebbero essere salvati in un file result.txt
	# ogni riga di tale file dovrebbe avere come identificatore il file corrispondente
	# e come colonne i parametri K e N, ed infine il tempo di sanificazione e lo sbilancio tra
	# studenti soddisfatti nei diversi dipartimenti.
	cp "$i" "../$PATH_RES/res_$i";
	minizinc --time-limit 300000 "../model.mzn" "$i" >> "../$PATH_RES/res_$i";
done;