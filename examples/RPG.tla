------------------------------- MODULE RPG -------------------------------
EXTENDS Naturals

CONSTANTS Mago, Druida, Caçador, Monstro

VARIABLES hp

(* Helps

/\ == &&
\/ == ||

*)

Init ==
    hp = [Mago |-> 20, Druida |-> 25, Caçador |-> 30, Monstro |-> 100]

Ataque(personagem, dano) ==
    /\ hp[personagem] > dano
    /\ hp' = [hp EXCEPT ![personagem] = @ - dano]

TurnoMago ==
    Ataque(Mago, 10)

TurnoMonstro ==
    Ataque(Monstro, 15)

Next == TurnoMago \/ TurnoMonstro
Spec == Init /\ [][Next]_<<hp>>

===============================================================================
