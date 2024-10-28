------------------------------- MODULE GameModel -------------------------------
EXTENDS Naturals

CONSTANTS A, B, C, M
VARIABLES hp, turn, gameStatus

Init ==
    /\ hp = [A |-> 10, B |-> 10, C |-> 10, M |-> 30]
    /\ turn = A
    /\ gameStatus = "in_progress"

Turn_A ==
    /\ turn = A
    /\ hp' = [hp EXCEPT ![M] = @ - 5]
    /\ turn' = B
    /\ gameStatus' = IF hp'[M] = 0 THEN "victory" ELSE gameStatus

Turn_B ==
    /\ turn = B
    /\ hp' = [hp EXCEPT ![M] = @ - 5]
    /\ turn' = C
    /\ gameStatus' = IF hp'[M] = 0 THEN "victory" ELSE gameStatus

Turn_C ==
    /\ turn = C
    /\ hp' = [hp EXCEPT ![M] = @ - 5]
    /\ turn' = A
    /\ gameStatus' = IF hp'[M] = 0 THEN "victory" ELSE gameStatus

Next ==
    \/ Turn_A
    \/ Turn_B
    \/ Turn_C
===============================================================================
