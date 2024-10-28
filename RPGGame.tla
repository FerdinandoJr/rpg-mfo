------------------------------- MODULE RPGGame -------------------------------
EXTENDS Randomization, Naturals, Sequences, TLC 

CONSTANTS
    Hunter, 
    Druid, 
    Mage, 
    Monster

VARIABLES
    creatures,
    turns
    
(* 
    Estado inicial:
    - Cada personagem começa com 20 HP, e o monstro com 100 HP.
*)

CreatureOrder == [Hunter |-> 1, Druid |-> 2, Mage |-> 3, Monster |-> 4]

Init ==
    /\ creatures = [ 
		Hunter |-> [
			    hp |-> 20,			
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 10,
                isParalyzed |-> FALSE
		    ], 
		Druid |-> [
			    hp |-> 20,			
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 10,
                isParalyzed |-> FALSE
		    ], 
		Mage |-> [
			    hp |-> 20,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 10,
                isParalyzed |-> FALSE
		    ],
		Monster |-> [
                hp |-> 100,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 20,
                isParalyzed |-> FALSE
		    ]
	    ]   
    /\ turns = SortSeq(<<Hunter, Druid, Mage, Monster>>,
                 LAMBDA x, y: 
                     IF creatures[x].initiative = creatures[y].initiative 
                     THEN CreatureOrder[x] < CreatureOrder[y]
                     ELSE creatures[x].initiative > creatures[y].initiative)
          
(* Verifica se o HP do Monster chegou a 0, indicando vitória dos heróis *)
VictoryHeroes ==
    /\ creatures[Monster].hp <= 0
    /\ UNCHANGED <<creatures, turns>>

(* Verifica se o HP de todos os heróis chegou a 0, indicando vitória do Monster *)
VictoryMonster ==
    /\ creatures[Hunter].hp <= 0
    /\ creatures[Druid].hp <= 0
    /\ creatures[Mage].hp <= 0
    /\ UNCHANGED <<creatures, turns>>

TurnMage ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Mage
    /\ IF creatures[Mage].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Mage].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Mage *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Mage estiver morto *)
             /\ UNCHANGED <<creatures>>

TurnDruid ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Druid
    /\ IF creatures[Druid].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Druid].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Druid *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Druid estiver morto *)
             /\ UNCHANGED <<creatures>>


TurnHunter ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Hunter
    /\ IF creatures[Hunter].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Hunter].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Hunter *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Hunter estiver morto *)
             /\ UNCHANGED <<creatures>>


TurnMonster ==    
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Monster
    /\ creatures' = 
        LET targetHero == CHOOSE h \in {Hunter, Druid, Mage} : creatures[h].hp > 0
        IN [creatures EXCEPT 
                ![targetHero].hp = @ - creatures[Monster].attack
            ]
    /\ turns' = Tail(turns)

ResetTurn == 
    /\ turns = <<>>
    /\ IF creatures[Monster].hp <= 0 
        THEN /\ VictoryHeroes (* Herois ganham *)
        ELSE IF \A h \in {Hunter, Druid, Mage} : creatures[h].hp <= 0
            THEN /\ VictoryMonster (* Monstros ganham *)
            ELSE /\ turns' = SortSeq(
                    SelectSeq(<<Hunter, Druid, Mage, Monster>>, LAMBDA x: creatures[x].hp > 0),
                    LAMBDA x, y: 
                        IF creatures[x].initiative = creatures[y].initiative 
                        THEN CreatureOrder[x] < CreatureOrder[y]
                        ELSE creatures[x].initiative > creatures[y].initiative
                    )
                 /\ UNCHANGED <<creatures>>



(* Transição de turno com condição de parada *)
Next ==
    \/ (turns = <<>> /\ ResetTurn)
    \/ TurnMage
    \/ TurnDruid
    \/ TurnHunter
    \/ TurnMonster

Spec == Init /\ [][Next]_<<creatures, turns>>
    

(* COISAS A FAZER
 
 - Criar Habilidade Ilusão do Mage
 - Criar Habilidade Cegueira do Hunter
 - Criar Habilidade Transformação selvagem do Druid
 - Criar Habilidade paralisia do Monster
 - Criar Maneira dos personagens sair da paralisa

*)

=============================================================================

