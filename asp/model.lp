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
% sanification
sanification(R,D,T) :- scheduling(R,D,T,0), room(R), day(D), timeunit(T).
sameGroup(R1, R2) :- R1 \ g = R2 \ g, room(R1), room(R2).
sameDep(C1, C2) :- department(C1) = department(C2), dep(C1), dep(C2).
timeAssigned(O, K) :- K = #count{scheduling(R,D,T,O) : room(R), day(D), timeunit(T)}, occupant(O). 

satisfiedStudents(C, R, K) :- K = (X * Y) / 4, coorte(C), room(R), timeAssigned(C,X), capacity(C,Y).

satisfiedStudents(C, X) :- #sum{ Y,C,R : satisfiedStudents(C,R,Y),room(R)} >= X, coorte(C), nStudents(C,X).
satisfiedStudents(C, K) :- K = #sum{ X,C,R : satisfiedStudents(C,R,X),room(R)}, K < Y, nStudents(C,Y), coorte(C).

satisfiedStudentsDep(D, K) :- K = #sum{X,C : satisfiedStudents(C,X), coorte(C), department(C,D)}, dep(D).

totStudentsDep(D,K) :- K = #sum{X,C : nStudents(C,X), coorte(C), department(C,D)}, dep(D).



#show satisfiedStudents/2.
#show satisfiedStudentsDep/2.
#show totStudentsDep/2.