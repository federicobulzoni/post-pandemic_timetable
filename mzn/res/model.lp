g = 4.
% k is in input
room(1..g*k).
% capacity(r, c | room(r)) in input
% n in input
coorte(1..n).
% nStudents(c, n | coorte(c)) in input
% year(c, y | coorte(c)) in input
% d in input
dep(1..d). 
% department(c, d | coorte(c), dep(d)) in input
timeunit_x_day = 22.
timeunit(1 .. timeunit_x_day).
n_days = 5.
day(1..n_days).
% requiredTime(c, t | coorte(c)) in input.

occupant(0..n).

% sanification
% sanification(R,D,T) :- scheduling(R,D,T,0), coorte(C), day(D), timeunit(T).
% sameGroup(R1, R2) :- R1 \ g = R2 \ g, room(R1), room(R2).
% sameDep(C1, C2) :- department(C1) = department(C2), dep(C1), dep(C2).
% timeAssigned(O, K) :- #count {scheduling(R,D,T,O) : room(R), day(D), timeunit(T), occupant(O)} = K. 