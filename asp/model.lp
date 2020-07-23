#const g = 4.
% k is in input
room(1..k*g).
% capacity(r, c | room(r)) in input
% n in input
coorte(1..n).
% nStudents(c, n | coorte(c)) in input
% year(c, y | coorte(c)) in input
% d in input
dep(1..d). 
% department(c, d | coorte(c), dep(d)) in input
#const timeunit_x_day = 22.
timeunit(1 .. timeunit_x_day).
#const n_days = 5.
day(1..n_days).
% requiredTime(c, t | coorte(c)) in input.

occupant(0..n).

% Specifiche per limitare i domini.
#const min_cap = 30.
#const max_cap = 60.
cap(min_cap .. max_cap).

#const min_stud = 50.
#const max_stud = 300.
stud(min_stud .. max_stud).

y(1..3).
day(1..n_days).
#const min_reqT = 40.
#const max_reqT = 60.
reqT(min_reqT .. max_reqT).

tAss(0..timeunit_x_day*n_days*g*k).

% esiste uno e solo un occupant associato ad ogni R,D,T.
1 {scheduling(R,D,T,O) : occupant(O)} 1 :- room(R), day(D), timeunit(T).

sameGroup(R1, R2) :- R1 \ g = R2 \ g,
					 room(R1), room(R2).
sameDep(C1, C2) :- department(C1) = department(C2), 
				   dep(C1), dep(C2).

sanificationTime(K) :- K = #count{R,D,T : scheduling(R,D,T,0), room(R), day(D), timeunit(T)}.

% in un gruppo di stanze ad un certo istante temporale devono essere presenti solamente coorti dello stesso dipartimento.
:- day(D), timeunit(T),
   scheduling(R1, D, T, C1), scheduling(R2, D, T, C2), 
   C1 != C2,
   not sameDep(C1, C2), sameGroup(R1, R2),
   room(R1), room(R2), coorte(C1), coorte(C2).


lecPreviousBad(R, D, T, C) :- T != 1, not sanificationSlot(R, D, T-2), not lectureSlot(R,D,T-4,C),
                              room(R), day(D), timeunit(T), coorte(C).

lecFollowingBad(R, D, T, C) :- T + 4 <= timeunit_x_day, not sanificationSlot(R, D, T+4), not lectureSlot(R, D, T+4, C),
                               room(R), day(D), timeunit(T), coorte(C).

lectureSlot(R, D, T, C) :- scheduling(R, D, T, C), scheduling(R, D, T + 1, C), scheduling(R, D, T + 2, C), scheduling(R, D, T + 3, C),
                           not lecPreviousBad(R, D, T, C),
                           not lecFollowingBad(R, D, T, C),
                           room(R), day(D), timeunit(T), coorte(C).

sanificationSlot(R, D, T) :- scheduling(R, D, T, 0), scheduling(R, D, T + 1, 0),
                             lectureSlot(R, D, T - 4, C1),
                             lectureSlot(R, D, T + 2, C2),
                             C1 != C2,
                             coorte(C1), coorte(C2),
                             room(R), day(D), timeunit(T).

% Aiutino.
1 {scheduling(R, 1, 1, C) : coorte(C), department(C,R)} 1 :- room(R), dep(R).

%scheduling(1,1,1,1).

% vincolo di regolarità, basta questo.
:- room(R), day(D), not lectureSlot(R,D,1,C) : coorte(C).

% vincolo sulle coorti al primo anno.
:- coorte(C), year(C,1), nStudents(C,Y),
   #sum{Z, R,D,T : lectureSlot(R,D,T,C), capacity(R,Z), cap(Z), room(R), day(D), timeunit(T)} < Y.

% Troppo costoso dal punto di vista computazionale.
% :~ coorte(C), nStudents(C, X),
%    #sum{Z, R,D,T : lectureSlot(R,D,T,C), capacity(R,Z), cap(Z), room(R), day(D), timeunit(T)} = Y,
%    RES = | (X - Y)*100/X |. [RES@2, C]

timeAssigned(C, X) :- X = #count{R,D,T : scheduling(R,D,T,C), room(R), day(D), timeunit(T)},
                      coorte(C).

unsatisfied(C) :- coorte(C), requiredTime(C,Y), reqT(Y), #count{R,D,T : scheduling(R,D,T,C), room(R), day(D), timeunit(T)} < Y.

%:~ Z = #count{C : coorte(C), timeAssigned(C,X), tAss(X), requiredTime(C,Y), reqT(Y), X < Y}. [Z@3]
nUnsat(Z) :- Z = #count{C : coorte(C), unsatisfied(C)}.
:~ nUnsat(Z). [Z@3]
:~ coorte(C), timeAssigned(C,X), tAss(X), requiredTime(C,Y), reqT(Y),
   X < Y,
   RES = (Y-X)*100/Y. [RES@2]

% preparazione alla funzione di costo.
depWithNextYears(D) :- 1 {coorteNextYear(C) : department(C,D)} , dep(D).
coorteNextYear(C) :- coorte(C), year(C,X), y(X), X > 1.

totRequiredTimeDep(DI, Z) :- Z = #sum{Y, C : coorteNextYear(C), requiredTime(C,Y), reqT(Y), department(C, DI)},
                          depWithNextYears(DI).

timeAssignedDep(DI, Z) :- Z = #count{C, R,D,T : coorteNextYear(C), department(C,DI), scheduling(R,D,T,C), room(R), day(D), timeunit(T)},
                      depWithNextYears(DI). 

:- depWithNextYears(DI1), depWithNextYears(DI2), DI1 != DI2,
   totRequiredTimeDep(DI1, X1), totRequiredTimeDep(DI2, X2),
   timeAssignedDep(DI1, Y1), timeAssignedDep(DI2, Y2),
   Y1 < X1, Y2 < X2, 
   | (Y1*100 / X1) - (Y2*100 / X2) | > 10.


:~ sanificationTime(K). [K@1]

%% OUTPUT :
#show sanificationTime/1.
#show nUnsat/1.

#show timeAssigned/2.
#show totRequiredTimeDep/2.
#show timeAssignedDep/2.
#show sanificationTime/1.

#show coorteNextYear/1.
#show depWithNextYears/1.
% #show timeAssignedFirstYears/1.

#show lectureSlot/4.
#show sanificationSlot/3.