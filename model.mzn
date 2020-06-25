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

include "globals.mzn";

predicate sanification(var OCCUPANT : occupant) =
  occupant == 0;


function int : buildState (int : s, int : o) =
  (s - 1)*(N + 1) + (o + 1);
  
% Se gli shift fossero direttamente gli occupant?
int : Q = 6 * (N + 1);
% stateF = (state - 1)*(N+1) + (occ + 1)
int : q0 = (1 - 1)*(N+1) + (0 + 1);  % Stato 1, occ 0
set of int : STATE = 1 .. Q;
int : S = N+1;

% Costruzione automa per il riconoscimento dei pattern:
  % 1. Gli slot delle lezioni sono da 4 unità di tempo,
  % 2. quando una coorte lascia l'aula si ha una sanificazione, tale sanificazione
  %    dura due unità di tempo.
  % 3. si noti che non è permesso fare due sanificazioni di fila in un aula, questo non potrebbe in alcun modo offrire un vantaggio. 
  % 4. imponiamo che non ci siano sanificazioni all'inizio ed alla fine della giornata.
array[STATE, OCCUPANT] of int : t = array2d(STATE, OCCUPANT,
  [
    if state = 1
      then 
      if oldOcc = 0 \/ (occ != 0 /\ oldOcc != occ)
        then buildState(2, occ)
        else 0
      endif
    elseif state > 1 /\ state < 5
      then
      if occ != 0 /\ oldOcc = occ
        then buildState(state+1, oldOcc)
        else 0
      endif
    elseif state = 5
      then
      if occ = 0
        then buildState(6, oldOcc)
      elseif occ != 0 /\ occ = oldOcc
          then buildState(2, oldOcc)
      else 0
      endif
    else % stato 6.
      if occ = 0
        then buildState(1, oldOcc)
        else 0
      endif
    endif
  | state in 1..6, oldOcc in OCCUPANT, occ in OCCUPANT]);

set of int : FINAL = {buildState(5, o) | o in OCCUPANT};

% Vincolo di regolarità.
constraint
  forall (room in ROOM, day in DAY)(
     regular([scheduling[room, day, timeunit] | timeunit in TIMEUNIT], Q, OCCUPANT, t, q0, FINAL) 
  );
  
predicate sameGroup(ROOM : room1, ROOM : room2) = 
  room1 mod G == room2 mod G;

predicate sameDep(var COORTE : coorte1, var COORTE : coorte2) =
  department[coorte1] == department[coorte2];
  
  
% Le coorti dello stesso dipartimento sono allocate nella stessa zona (contigua).
constraint
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
  

function var int : timeAssigned(OCCUPANT : occupant) = 
   count([scheduling[room, day, timeunit] | room in ROOM, day in DAY, timeunit in TIMEUNIT], occupant);
   
function var int : satisfiedStudents(COORTE : coorte) = 
  let {var int : x = sum(room in ROOM)( (count([scheduling[room, day, timeunit] | day in DAY, timeunit in TIMEUNIT], coorte) div 4) * capacity[room] ) } 
  in 
  if x > nStudents[coorte]
    then nStudents[coorte]
    else x
  endif;
  
  
% Ogni coorte ha un certo tempo di lezione minimo da svolgere in presenza ogni settimana.
constraint
  forall(coorte in COORTE)(
    timeAssigned(coorte) >= requiredTime[coorte]
  );
                  
% Organizzare l’orario in modo che ogni studente del primo anno di ogni corso abbia almeno una mattinata o un pomeriggio di lezione in presenza alla settimana.
constraint
  forall(coorte in COORTE)(
    year[coorte] = 1 -> satisfiedStudents(coorte) = nStudents[coorte]
  );

% I corsi del secondo e del terzo anno che non riescono ad avere corsi in presenza dovrebbero essere ben bilanciati tra dipartimenti (la percentuale di quelli soddisfatti deve essere simile, anche se essendo dati discreti non necessariamente uguale)

% Restrizione ai dati di interesse.
set of DEPARTMENT : DEPWITHNEXTYEARS = {dep | dep in DEPARTMENT where exists(coorte in COORTE)(department[coorte] = dep /\ year[coorte] != 1)};

set of COORTE : COORTENEXTYEAR = {coorte | coorte in COORTE, dep in DEPWITHNEXTYEARS where year[coorte] != 1 /\ department[coorte] = dep};

function var int : satisfiedStudentsDep(DEPARTMENT : dep) = 
  sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    satisfiedStudents(coorte)
  );
  
function int : totStudentsDep(DEPARTMENT : dep) = 
  sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    nStudents[coorte]
  );

function var float : percentageUnsatisfiedDep(DEPARTMENT : dep) = 
  1.0 - (satisfiedStudentsDep(dep) / totStudentsDep(dep));
  
% SEARCH
solve :: int_search(scheduling, dom_w_deg, indomain_random)  minimize (timeAssigned(0) / (TIMEUNIT_X_DAY * N_DAYS)) + abs(max(dep in DEPWITHNEXTYEARS)(percentageUnsatisfiedDep(dep)) - min(dep in DEPWITHNEXTYEARS)(percentageUnsatisfiedDep(dep)));

% OUTPUT
array[TIMEUNIT] of float : humanTU :: output_only = 
  [8.0 + 0.5*timeunit | timeunit in TIMEUNIT];

array [COORTE] of int : timeAssignedOut :: output_only = 
  [count([fix(scheduling[room, day, timeunit]) | room in ROOM, day in DAY, timeunit in TIMEUNIT], coorte) | coorte in COORTE];
 
array [COORTE] of int : satisfiedStudentsOut :: output_only = 
  [let {int : x = sum(room in ROOM)( (count([fix(scheduling[room, day, timeunit]) | day in DAY, timeunit in TIMEUNIT], coorte) div 4) * capacity[room] ) } 
  in 
  if x > nStudents[coorte]
    then nStudents[coorte]
    else x
  endif | coorte in COORTE];

  
array [DEPARTMENT] of float : percentageUnsatisfiedOut :: output_only = 
  [
  let {
  int : totStudDep = sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    nStudents[coorte]
  );
  int : totSatStudDep = sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    satisfiedStudentsOut[coorte]
  );
  float : perc = if totStudDep > 0 then 1.0 - totSatStudDep / totStudDep else 0.0 endif;
  } in
  perc | dep in DEPARTMENT];
      
      
int : sanificationTimeOut :: output_only =
  count([fix(scheduling[room, day, timeunit]) | room in ROOM, day in DAY, timeunit in TIMEUNIT], 0);

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
++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(timeAssignedOut[coorte]) ++ " u.t." | coorte in COORTE]
++ ["\n"]

++ ["\nTotal satisfied students:"]
++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(satisfiedStudentsOut[coorte]) ++ " people." | coorte in COORTE]
++ ["\n"]

++ ["\nTotal sanification time: " ++ show(sanificationTimeOut) ++ "u.t."]
++ ["\n"]

++ ["\nDepartments with classes not at their first year: " ++ show(DEPWITHNEXTYEARS) ++ "."]
++ ["\nCoortes not at their first year: " ++ show(COORTENEXTYEAR) ++ "."]
++ ["\nPercentage of students unsatsfied per department: "]
++ ["\nDepartment " ++ show(dep) ++ " = " ++ show(percentageUnsatisfiedOut[dep]) ++ " %." | dep in DEPWITHNEXTYEARS]
++ ["\n"]