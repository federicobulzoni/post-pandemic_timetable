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

% esiste uno e solo un occupant associato ad ogni R,D,T.
1 {scheduling(R,D,T,O) : occupant(O)} 1 :- room(R), day(D), timeunit(T).

sameGroup(R1, R2) :- R1 \ g = R2 \ g,
					 room(R1), room(R2).
sameDep(C1, C2) :- department(C1) = department(C2), 
				   dep(C1), dep(C2).

timeAssigned(O, K) :- K = #count{R,D,T : scheduling(R,D,T,O), room(R), day(D), timeunit(T)},
					  occupant(O). 

:- coorte(C), timeAssigned(C, X), requiredTime(C, Y), X < Y.
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
% vincolo di regolarità, basta questo.
:- room(R), day(D), not lectureSlot(R,D,1,C) : coorte(C).

auxSatStud(C, X) :- X = #sum{Y, R,D,T : lectureSlot(R,D,T,C), capacity(C,Y), room(R), day(D), timeunit(T)},
                    coorte(C).

satisfiedStudents(C, X) :- auxSatStud(C, X),
                           nStudents(C, Z),
                           X <= Z,
                           coorte(C).
satisfiedStudents(C, Z) :- auxSatStud(C, X),
                           nStudents(C, Z),
                           X > Z,
                           coorte(C).


% vincolo sulle coorti al primo anno.
:- coorte(C), year(C,1), satisfiedStudents(C,X), nStudents(C,Y), X != Y.

% preparazione alla funzione di costo.
depWithNextYears(D) :- 1 {coorteNextYear(C) : department(C,D), coorte(C)} , dep(D).
coorteNextYear(C) :- coorte(C), year(C,X), X > 1.

satisfiedStudentsDep(D,X) :- X = #sum{Y, C : coorteNextYear(C), satisfiedStudents(C,Y), department(C,D)}, 
                             depWithNextYears(D).

totStudentsDep(D,X) :- X = #sum{Y, C : coorteNextYear(C), nStudents(C,Y), department(C,D)},
                       depWithNextYears(D).

% Target 0.
:~ depWithNextYears(D), totStudentsDep(D, X), satisfiedStudentsDep(D, Y), Z = | X - Y | . [Z@1,D] 
#minimize{K : timeAssigned(0,K)}.


#show satisfiedStudents/2.
% #show satisfiedStudentsDep/2.
% #show totStudentsDep/2.
% #show sameDep/2.
% #show sameGroup/2.
% #show timeAssigned/2.
% #show scheduling/4.
#show lectureSlot/4.
#show sanificationSlot/3.
#show depWithNextYears/1.
#show coorteNextYear/1.
#show satisfiedStudentsDep/2.
#show totStudentsDep/2.
% #show nextCoorte/4.