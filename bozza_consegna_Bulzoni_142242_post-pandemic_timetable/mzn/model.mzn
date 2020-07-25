% post-pandemic_timetable.mzn
include "globals.mzn";

% Parameters:
int : G = 4; % Number of different groups of rooms.
int : K; % Number of rooms in each group of rooms.
set of int : ROOM = 1 .. G*K;  
array[ROOM] of int : capacity; % Association between a room and its capacity.

int : N; % Number of different coortes
set of int : COORTE = 1 .. N;  
array[COORTE] of 50 .. 300 : nStudents; % Association between a coorte and its number of students.
array[COORTE] of 1 .. 3 : year; % Association between a coorte and the associated year of study.

int : D; % Number of different departments.
set of int : DEPARTMENT = 1 .. D;
array[COORTE] of DEPARTMENT : department; % Association between a coorte and the department to which it belongs.

int : TIMEUNIT_X_DAY = 22; % Number of timeunit in each day, a timeunit corresponds to 0.5 hours.
set of int : TIMEUNIT = 1 .. TIMEUNIT_X_DAY; 
int : N_DAYS = 5; % Number of days considered for the scheduling.
set of int : DAY = 1 .. N_DAYS;

array[COORTE] of 40 .. 60  : requiredTime; % Association between a coorte and the minimum amount of lecture's hours that it requires.

% Decision variables:
set of int : OCCUPANT = 0 .. N; % 0 is the sanification.
% A table where for each room, day and timeunit it associates the occupant of the room in that day and timeunit. The room can be occuped by a coorte or by a sanification.
array[ROOM, DAY, TIMEUNIT] of var OCCUPANT : scheduling;

% Utilities:
predicate sanification(var OCCUPANT : occupant) =
  occupant == 0;
  
predicate sameGroup(ROOM : room1, ROOM : room2) = 
  room1 mod G == room2 mod G;

predicate sameDep(var COORTE : coorte1, var COORTE : coorte2) =
  department[coorte1] == department[coorte2];
  
function var int : timeAssigned(OCCUPANT : occupant) = 
   count([scheduling[room, day, timeunit] | room in ROOM, day in DAY, timeunit in TIMEUNIT], occupant);

      
function var int : satisfiedStudents(COORTE : coorte) = 
  sum(room in ROOM)( (count([scheduling[room, day, timeunit] | day in DAY, timeunit in TIMEUNIT], coorte) div 4) * capacity[room] );
  
% Constraints:
% Automata declaration.
int : Q = 6 * (N + 1);

% Function that given a pseudo-state s and an occupant o gives the actual state of the automata.
function int : buildState (int : s, int : o) =
  (s - 1)*(N + 1) + (o + 1);
  
int : q0 = buildState(1,0);  
set of int : STATE = 1 .. Q;
int : S = N+1;

% Transition function, the following properties are required:
  % 1. A lesson's slot is of 4 time units.
  % 2. When a coorte left a classroom, a sanification is needed. A sanification's slot is of 2 time units.
  % 3. Optimization properties:
    % a. A sanification must be done if and only if there is a change of coorte in the considered classroom.
    % b. Sanification can't be done at the start or at the end of the day, since we assume that after the end of the last lesson of the day a sanification is made by default in eache room.
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

% Regularity constraint: 
constraint
  forall (room in ROOM, day in DAY)(
     regular([scheduling[room, day, timeunit] | timeunit in TIMEUNIT], Q, OCCUPANT, t, q0, FINAL) 
  );
  
% Coortes of the same department must be allocated in the same group of rooms.
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


% All the students at their first year must have a lecture.                  
constraint
  forall(coorte in COORTE)(
    year[coorte] = 1 -> satisfiedStudents(coorte) >= nStudents[coorte]
  );

% Restriction to the coortes at the second and third year, and to the departments with at least one of these coortes.
set of DEPARTMENT : DEPWITHNEXTYEARS = {dep | dep in DEPARTMENT where exists(coorte in COORTE)(department[coorte] = dep /\ year[coorte] != 1)};
set of COORTE : COORTENEXTYEAR = {coorte | coorte in COORTE where year[coorte] > 1};

function int : totRequiredTimeDep(DEPWITHNEXTYEARS : dep) =
  sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    requiredTime[coorte]
  );

function var int : timeAssignedDep(DEPWITHNEXTYEARS: dep) = 
  sum(coorte in COORTENEXTYEAR where department[coorte] = dep)(
    timeAssigned(coorte)
  );
  
function var float : percSatDep(DEPWITHNEXTYEARS : dep) =
  timeAssignedDep(dep) * 100 / totRequiredTimeDep(dep);
  
% Constraint on the percentage of unsatisfied hours between departments.
constraint
  forall(dep1, dep2 in DEPWITHNEXTYEARS where dep1 != dep2 /\ timeAssignedDep(dep1) < requiredTime[dep1] /\ timeAssigned(dep2) < requiredTime[dep2])(
    abs(percSatDep(dep1) - percSatDep(dep2)) < 10
  );
  
% SEARCH:
% Objective function.
% Priorita' 1: tempo di sanificazione (timeAssigned(0)).
% Priorita' 2: percentuale insoddisfazione.
% Priorita' 3: numero di coorti insoddisfatte.
function var float : sanificationTime() = 
  timeAssigned(0);
  
function var int : nCoortiUnsat() =
  length([coorte | coorte in COORTE where timeAssigned(coorte) < requiredTime[coorte]]);

function var float : percUnsat(COORTE : coorte) = 
  if timeAssigned(coorte) >= requiredTime[coorte]
    then 0
    else (requiredTime[coorte] - timeAssigned(coorte)) / requiredTime[coorte]
  endif;
    
solve :: int_search(scheduling, dom_w_deg, indomain_random)  minimize (timeAssigned(0)/(TIMEUNIT_X_DAY * N_DAYS * G * K) + 3*(nCoortiUnsat()/N) + 2*max([percUnsat(coorte) | coorte in COORTE]));

% Output
array [COORTE] of int : timeAssignedOut :: output_only = 
  [count([fix(scheduling[room, day, timeunit]) | room in ROOM, day in DAY, timeunit in TIMEUNIT], coorte) | coorte in COORTE];
 
array [COORTE] of int : satisfiedStudentsOut :: output_only = 
  [let {int : x = sum(room in ROOM)( (count([fix(scheduling[room, day, timeunit]) | day in DAY, timeunit in TIMEUNIT], coorte) div 4) * capacity[room] ) } 
  in 
  if x > nStudents[coorte]
    then nStudents[coorte]
    else x
  endif | coorte in COORTE];
      
      
int : sanificationTimeOut :: output_only =
  count([fix(scheduling[room, day, timeunit]) | room in ROOM, day in DAY, timeunit in TIMEUNIT], 0);

int : nCoortiUnsatOut :: output_only = 
  length([coorte | coorte in COORTE where timeAssignedOut[coorte] < requiredTime[coorte]]);
  
array [COORTE] of float : percUnsatOut :: output_only =
[
  if timeAssignedOut[coorte] >= requiredTime[coorte]
    then 0
    else (requiredTime[coorte] - timeAssignedOut[coorte]) / requiredTime[coorte]
  endif
| coorte in COORTE];
  
int : digs = ceil(log(10.0, int2float(N)));
output
%["K\t" ++ "N\t" ++ "UnsatCoorti\t" ++ "maxUnsatPerc\t" ++ "sanificationTime\n"] ++
[show(K) ++ "\t" ++ show(N) ++ "\t" ++ show(D) ++ "\t" ++ show(nCoortiUnsatOut) ++ "\t" ++ show_float(3,0,100*(max(percUnsatOut))) ++ "\t" ++ show(sanificationTimeOut) ++ "\n"]
 
% output 
% [
%   "K = \(K)\n" ++ 
%   "capacity = \(capacity)\n" ++
%   "N = \(N)\n" ++
%   "nStudents = \(nStudents)\n" ++
%   "year = \(year)\n" ++
%   "department = \(department)\n" ++
%   "requiredTime = \(requiredTime)\n"
% ]
% ++ ["\nAssignment matrix Monday (room/schedule):"]
% ++ ["\n"]
% ++ [show_int(digs, scheduling[room, 1, timeunit]) ++ if timeunit == TIMEUNIT_X_DAY then "\n" else " " endif | room in ROOM, timeunit in TIMEUNIT]
% ++ ["\n"]

% ++ ["\nAssignment matrix Tuesday (room/schedule):"]
% ++ ["\n"]
% ++ [show_int(digs, scheduling[room, 2, timeunit]) ++ if timeunit == TIMEUNIT_X_DAY then "\n" else " " endif | room in ROOM, timeunit in TIMEUNIT]
% ++ ["\n"]

% ++ ["\nAssignment matrix Wednesday (room/schedule):"]
% ++ ["\n"]
% ++ [show_int(digs, scheduling[room, 3, timeunit]) ++ if timeunit == TIMEUNIT_X_DAY then "\n" else " " endif | room in ROOM, timeunit in TIMEUNIT]
% ++ ["\n"]

% ++ ["\nAssignment matrix Thursday (room/schedule):"]
% ++ ["\n"]
% ++ [show_int(digs, scheduling[room, 4, timeunit]) ++ if timeunit == TIMEUNIT_X_DAY then "\n" else " " endif | room in ROOM, timeunit in TIMEUNIT]
% ++ ["\n"]

% ++ ["\nAssignment matrix Friday (room/schedule):"]
% ++ ["\n"]
% ++ [show_int(digs, scheduling[room, 5, timeunit]) ++ if timeunit == TIMEUNIT_X_DAY then "\n" else " " endif | room in ROOM, timeunit in TIMEUNIT]
% ++ ["\n"]

% ++ ["\nTotal time assigned:"]
% ++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(timeAssignedOut[coorte]) ++ " u.t." | coorte in COORTE]
% ++ ["\n"]

% ++ ["\nNumber of coorti unsatisfied = " ++ show(nCoortiUnsatOut) ++ "."]
% ++ ["\n"]

% ++ ["Unsatisfied percentage:"]
% ++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show_float(3,0,100*percUnsatOut[coorte]) ++ "%" | coorte in COORTE]
% ++ ["\n"]

% ++ ["\nTotal satisfied students:"]
% ++ ["\nCoorte " ++ show(coorte) ++ " = " ++ show(satisfiedStudentsOut[coorte]) ++ " people." | coorte in COORTE]
% ++ ["\n"]

% ++ ["\nDepartments with classes not at their first year: " ++ show(DEPWITHNEXTYEARS) ++ "."]
% ++ ["\nCoortes not at their first year: " ++ show(COORTENEXTYEAR) ++ "."]
% ++ ["\n"]

% ++ ["sanificationTime = " ++ show(sanificationTimeOut) ++ " u.t."]