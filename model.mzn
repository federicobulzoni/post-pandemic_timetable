% post-pandemic_timetable.mzn
% parameters:
%  K number of classroom for each of the four groups available,
%  l_i for i in [1,4K] is the capacity of classroom i,
%  N number of different coorti,
%  c_i for i in [1, N] is the number of students in coorte i,
%  year(c_i) = j, for i in [1, N] and j in [1,3]; meaning that coorte i is associated to the j-th year of study,
%  D number of distinct departments,
%  d(c_i) = d_j for i in [1,N], j in [1,D]; meaning that coorte i belongs to department d_j,
%  T available time units, a time unit consists of 30 minutes. H is fixed to 22 since the university is open from 8:00 to 19:00.
%  st = 1 u.t., the sanification time that is fixed to a time unit, this time is spent every time that a coorte leaves a classroom.
%  lst = 4 u.t, the lesson's slot time that is fixed to four time unit,
%  o(c_i) = x u.t, for i in [1, N] and x integer, is the time unit amount required by coorte c_i each week.

int : K;
set of int : ROOM = 1 .. 2*K;
array[ROOM] of int : capacity;

int : N;
set of int : COORTE = 1 .. N;
array[COORTE] of int : nStudents;
array[COORTE] of 1 .. 3 : year;

int : D;
set of int : DEPARTMENT = 1 .. D;
array[COORTE] of DEPARTMENT : department;

int : AVAILABLE_TIME = 22*5; 
int : ST = 1; % Sanification time.
int : LST = 4; % Lecture slot time.

array[COORTE] of int : requiredTime;

% decision variables:
% a table where the rows are the classroom, the columns are the time units and the entry are the coorte which occupies the classroom at the specified time unit.
array[ROOM, 1 .. AVAILABLE_TIME] of var COORTE : scheduling;
array[ROOM, 1 .. AVAILABLE_TIME, COORTE] of var bool : assignment;

% Tunneling constraint.
constraint
forall(room in ROOM, time in 1 .. AVAILABLE_TIME, coorte in COORTE)(
  assignment[room,time,coorte] <-> scheduling[room, time] = coorte
);

include "globals.mzn";

predicate sameGroup(ROOM : room1, ROOM : room2) = 
  room1 mod 2 == room2 mod 2;

predicate sameDep(var COORTE : coorte1, var COORTE : coorte2) =
  department[coorte1] == department[coorte2];

% Simmetry breaking
% Le coorti dello stesso dipartimento sono allocate nella stessa zona (contigua).
% constraint 
% forall(time in 1 .. AVAILABLE_TIME, dep in DEPARTMENT, room in ROOM)(
%   let 
%   {var COORTE : coorte = scheduling[room, time]}
%   in department[coorte] = dep
%   ->
%   not exists(room2 in ROOM)
%   (
%     let 
%     {var COORTE : coorte2 = scheduling[room2, time]}
%     in sameDep(coorte, coorte2) /\ 
%     not sameGroup(room, room2)
%   )
% );

% ogni coorte necessita di un certo numero di ore alla settimana requiredTime[corte].
% constraint 
% forall(coorte in COORTE)(
%   sum(room in ROOM, time in 1 .. AVAILABLE_TIME)(
%     bool2int(assignment[room, time, coorte])
%   ) >= requiredTime[coorte]
% );


solve satisfy;    

output 
[
  "K = \(K)\n" ++ 
  "capacity = \(capacity)\n" ++
  "N = \(N)\n" ++
  "nStudents = \(nStudents)\n" ++
  "year = \(year)\n" ++
  "department = \(department)\n" ++
  "requiredTime = \(requiredTime)\n"
]
++ ["\nAssignment matrix monday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. 22])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 1 .. 22])
    | room in ROOM]
++ ["\nAssignment matrix tuesday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. 22])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 22+1 .. 22*2])
    | room in ROOM]
++ ["\nAssignment matrix wednesday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. 22])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 22*2+1 .. 22*3])
    | room in ROOM]
++ ["\nAssignment matrix thursday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. 22])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 22*3+1 .. 22*4])
    | room in ROOM]
++ ["\nAssignment matrix friday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. 22])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 22*4+1 .. 22*5])
    | room in ROOM]
;






