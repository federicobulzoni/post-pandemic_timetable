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

int : TIMEUNIT_X_DAY = 22;
set of int : TIMEUNIT = 1 .. TIMEUNIT_X_DAY;
int : N_DAYS = 5;
set of int : DAY = 1 .. N_DAYS;

array[COORTE] of int : requiredTime;

% decision variables:
% a table where the rows are the classroom, the columns are the time units and the entry are the coorte which occupies the classroom at the specified time unit.
set of int : OCCUPANT = 0 .. N; % 0 is the sanification.
array[ROOM, DAY, TIMEUNIT] of var OCCUPANT : scheduling;
array[ROOM, DAY, TIMEUNIT, OCCUPANT] of var bool : assignment;


include "globals.mzn";
include "inverse.mzn";

% Tunneling constraint.
constraint
forall(room in ROOM, day in DAY, timeunit in TIMEUNIT, occupant in OCCUPANT)(
  assignment[room,day,timeunit,occupant] <-> scheduling[room,day,timeunit] = occupant
);


predicate sameGroup(ROOM : room1, ROOM : room2) = 
  room1 mod G == room2 mod G;

predicate sameDep(var COORTE : coorte1, var COORTE : coorte2) =
  department[coorte1] == department[coorte2];

predicate sanification(var OCCUPANT : occupant) =
  occupant == 0;
  
% Costruzione automa per il riconoscimento dei pattern:
  % 1. Gli slot delle lezioni sono da 4 unità di tempo,
  % 2. quando una coorte lascia l'aula si ha una sanificazione, tale sanificazione
  %    dura una unità di tempo.

int : Q = 5;
int : q0 = 1;
set of int : STATE = 1 .. Q;

% enum SHIFT = {sanification, sameCoorte, diffCoorte};
set of int : SHIFT = {1,2,3}; 
int : S = card(SHIFT);
array[STATE, SHIFT] of int : t =
  [| 5, 2, 0 % state 1
   | 0, 3, 0 % state 2
   | 0, 4, 0 % state 3
   | 0, 1, 0 % state 4
   | 0, 2, 2 % state 5
  |];

set of int : FINAL = {1, 5};

array [ROOM, DAY, TIMEUNIT] of var SHIFT : shift;


% inizializzazione tensore shift.
constraint
  forall(room in ROOM, day in DAY)(
    ( shift[room, day, 1] = 1 <-> sanification(scheduling[room, day, 1]) )
    /\
    ( not sanification(scheduling[room, day, 1]) -> shift[room, day, 1] = 2 ) % deve essere così per via della funzione di transizione.
  );
  
constraint
  forall(room in ROOM, day in DAY, timeunit in 1 .. TIMEUNIT_X_DAY - 1)(
    ( (shift[room, day, timeunit + 1] = 1) <-> sanification(scheduling[room, day, timeunit + 1]) )
    /\
    ( (shift[room, day, timeunit + 1] = 2) <-> ( scheduling[room, day, timeunit + 1] = scheduling[room, day, timeunit] ) )
  );

% vincolo di regolarità.
constraint
  forall (room in ROOM, day in DAY)(
     % Riga di cui bisogna controllare la regolarità.
     % tuttavia dovrebbe essere sotto forma di shift.
     regular([shift[room, day, timeunit] | timeunit in TIMEUNIT], Q, S, t, q0, FINAL) 
  );

constraint
  % Le coorti dello stesso dipartimento sono allocate nella stessa zona (contigua).
  forall(room in ROOM, day in DAY, timeunit in TIMEUNIT, dep in DEPARTMENT)(
    let 
    {var OCCUPANT : occupant = scheduling[room, day, timeunit]} in 
    not sanification(occupant) /\ department[occupant] = dep
    ->
    not exists(room2 in ROOM)
    (
      let 
      {var OCCUPANT : occupant2 = scheduling[room2, day, timeunit]}
      in not sanification(occupant2) /\ sameGroup(room, room2) /\ not sameDep(occupant, occupant2)
    )
  );
  
% ogni coorte necessita di un certo numero di ore alla settimana requiredTime[corte].
function var int : totTimeAssigned (COORTE : coorte) =
  sum(room in ROOM, day in DAY, timeunit in TIMEUNIT)(
    bool2int(assignment[room, day, timeunit, coorte])
  );

  
constraint 
  forall(coorte in COORTE)(
    totTimeAssigned(coorte) >= requiredTime[coorte]
  );

solve :: bool_search(assignment, dom_w_deg, indomain_random) satisfy;    

array[TIMEUNIT] of float : humanTU :: output_only = 
  [8.0 + 0.5*timeunit | timeunit in TIMEUNIT];

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
++ ["\nAssignment matrix Monday (room/schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([scheduling[room, 1, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]
++ ["\n"]
++ ["\nShift matrix Monday (room, schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([shift[room, 1, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]

++ ["\nAssignment matrix Tuesday (room/schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([scheduling[room, 2, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]
++ ["\n"]

++ ["\nAssignment matrix Wednesday (room/schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([scheduling[room, 3, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]
++ ["\n"]

++ ["\nAssignment matrix Thursday (room/schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([scheduling[room, 4, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]
++ ["\n"]

++ ["\nAssignment matrix Friday (room/schedule):"]
++ ["\n"]
++ ["  " ++ show(time) | time in humanTU]
++ ["\n" ++ show(room) ++ " " ++ show([scheduling[room, 5, timeunit] | timeunit in TIMEUNIT]) | room in ROOM]
++ ["\n"]

++ ["\n\nTotal time assigned:"]
++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(sum(room in ROOM, day in DAY, timeunit in TIMEUNIT)(bool2int(assignment[room, day, timeunit, coorte]))) ++ " u.t." | coorte in COORTE]

