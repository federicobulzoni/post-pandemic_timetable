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

int : G = 4;
int : K;
set of int : ROOM = 1 .. G*K;
array[ROOM] of int : capacity;

int : N;
set of int : COORTE = 1 .. N; 
array[COORTE] of int : nStudents;
array[COORTE] of 1 .. 3 : year;

int : D;
set of int : DEPARTMENT = 1 .. D;
array[COORTE] of DEPARTMENT : department;

int : DAY_HOURS = 22;
int : DAYS = 5;
int : AVAILABLE_TIME = DAY_HOURS*DAYS; 
int : ST = 1; % Sanification time.
int : LST = 4; % Lecture slot time.

array[COORTE] of int : requiredTime;

% decision variables:
% a table where the rows are the classroom, the columns are the time units and the entry are the coorte which occupies the classroom at the specified time unit.
array[ROOM, 1 .. AVAILABLE_TIME] of var 0 .. N : scheduling;
array[ROOM, 1 .. AVAILABLE_TIME, 0 .. N] of var bool : assignment;


include "globals.mzn";
include "inverse.mzn";

% Tunneling constraint.
constraint
forall(room in ROOM, time in 1 .. AVAILABLE_TIME, occupant in 0 .. N)(
  assignment[room,time,occupant] <-> scheduling[room, time] = occupant
);

predicate sameGroup(ROOM : room1, ROOM : room2) = 
  room1 mod G == room2 mod G;

predicate sameDep(var COORTE : coorte1, var COORTE : coorte2) =
  department[coorte1] == department[coorte2];

predicate sanification(var 0 .. N : occupant) =
  occupant == 0;

predicate endOfDay(1 .. AVAILABLE_TIME : time) = 
  time mod DAY_HOURS == 0;
  
  
enum SHIFT = {coorte1, sanification, coorte2};
int : S = card(SHIFT);

int : Q = 2;
int : q0 = 1;
set of int : STATE = 1 .. Q;

array[STATE, SHIFT] of int : t =
  [| 1, 2, 0
   | 1, 0, 1|];

constraint 
forall(time in 1 .. AVAILABLE_TIME, room in ROOM)(
  % Ogni volta che una coorte lascia un'aula c'è bisogno di una sanificazione
  % a meno che non sia l'ultima ora del giorno.
  (
    not endOfDay(time) /\ not sanification(scheduling[room,time]) /\ scheduling[room, time] != scheduling[room, time+1]
    -> sanification(scheduling[room, time+1])
  )
  /\
  % Le coorti dello stesso dipartimento sono allocate nella stessa zona (contigua).
  forall(dep in DEPARTMENT)(
    let 
    {var 0 .. N : occupant = scheduling[room, time]} in 
    not sanification(occupant) /\ department[occupant] = dep
    ->
    not exists(room2 in ROOM)
    (
      let 
      {var 0 .. N : occupant2 = scheduling[room2, time]}
      in not sanification(occupant2) /\ sameGroup(room, room2) /\ not sameDep(occupant, occupant2)
    )
  )
  % /\
  % Gli slot delle lezioni sono sempre di LST unità di tempo.
  % Linguaggio regolare, potrebbe anche incorporare il vincolo sulla sanificazione.
  
);
  
% ogni coorte necessita di un certo numero di ore alla settimana requiredTime[corte].
function var int : totTimeAssigned (COORTE : coorte) =
  sum(room in ROOM, time in 1 .. AVAILABLE_TIME)(
    bool2int(assignment[room, time, coorte])
  );

  
constraint 
forall(coorte in COORTE)(
  totTimeAssigned(coorte) >= requiredTime[coorte]
);

solve :: bool_search(assignment, dom_w_deg, indomain_random) satisfy;    

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
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. DAY_HOURS])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in 1 .. DAY_HOURS])
    | room in ROOM]
++ ["\nAssignment matrix tuesday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. DAY_HOURS])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in DAY_HOURS+1 .. DAY_HOURS*2])
    | room in ROOM]
++ ["\nAssignment matrix wednesday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. DAY_HOURS])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in DAY_HOURS*2+1 .. DAY_HOURS*3])
    | room in ROOM]
++ ["\nAssignment matrix thursday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. DAY_HOURS])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in DAY_HOURS*3+1 .. DAY_HOURS*4])
    | room in ROOM]
++ ["\nAssignment matrix friday (room/schedule):"]
++ ["\n    " ++ show([8.0 + (i*0.5) | i in 1 .. DAY_HOURS])]
++ ["\n" ++ show(room) ++ "   " ++ show([(scheduling[room,time]) | time in DAY_HOURS*4+1 .. DAY_HOURS*5])
    | room in ROOM]
++ ["\n\nTotal time assigned:"]
++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(sum(room in ROOM, time in 1 .. AVAILABLE_TIME)(bool2int(assignment[room, time, coorte]))) ++ " u.t." | coorte in COORTE];







