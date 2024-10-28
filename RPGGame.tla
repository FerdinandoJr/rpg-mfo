------------------------------- MODULE RPGGame -------------------------------
EXTENDS Randomization, Naturals, Sequences

CONSTANTS
    Hunter, 
    Druid, 
    Mage, 
    Monster

VARIABLES
    creatures,
    currentTurn
(* 
    Estado inicial:
    - Cada personagem começa com 20 HP, e o monstro com 100 HP.
*)

Init ==
    /\ creatures = [ 
		Hunter |-> [
			    hp |-> 20,
			    hasAttacked |-> FALSE,
                attack |-> 5,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                isParalyzed |-> FALSE
		    ], 
		Druid |-> [
			    hp |-> 20,
			    hasAttacked |-> FALSE,
                attack |-> 5,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                isParalyzed |-> FALSE
		    ], 
		Mage |-> [
			    hp |-> 20,
			    hasAttacked |-> FALSE,
                attack |-> 5,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                isParalyzed |-> FALSE
		    ],
		Monster |-> [
                hp |-> 100,
                hasAttacked |-> FALSE,
                attack |-> 5,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                isParalyzed |-> FALSE
		    ]
	    ]    
    /\ currentTurn = Mage


(* Verifica se o HP do Monster chegou a 0, indicando vitória dos heróis *)
VictoryHeroes ==
    /\ creatures[Monster].hp <= 0
    /\ UNCHANGED <<creatures, currentTurn>>

(* Verifica se o HP de todos os heróis chegou a 0, indicando vitória do Monster *)
VictoryMonster ==
    /\ creatures[Hunter].hp <= 0
    /\ creatures[Druid].hp <= 0
    /\ creatures[Mage].hp <= 0
    /\ UNCHANGED <<creatures, currentTurn>>

(* Verifica se ocorreu uma condição de vitória *)
CheckVictory ==
    \/ VictoryHeroes
    \/ VictoryMonster

TurnMage ==
    /\ currentTurn = Mage
    /\ creatures[Mage].hasAttacked = FALSE
    /\ creatures[Monster].hp > 0 (* Só reduz se ainda tiver HP *)
    /\ creatures' = [ creatures EXCEPT 
            ![Monster].hp = @ - creatures[Mage].attack,
            ![Mage].hasAttacked = TRUE
        ]
    /\ currentTurn' = Druid  (* Define o próximo personagem a atacar *)

TurnDruid ==
    /\ currentTurn = Druid
    /\ creatures[Druid].hasAttacked = FALSE
    /\ creatures[Monster].hp > 0 (* Só reduz se ainda tiver HP *)
    /\ creatures' = [ creatures EXCEPT 
            ![Monster].hp = @ - creatures[Druid].attack,
            ![Druid].hasAttacked = TRUE
        ]
    /\ currentTurn' = Hunter  (* Define o próximo personagem a atacar *)

TurnHunter ==
    /\ currentTurn = Hunter
    /\ creatures[Hunter].hasAttacked = FALSE
    /\ creatures[Monster].hp > 0 (* Só reduz se ainda tiver HP *)
    /\ creatures' = [ creatures EXCEPT 
            ![Monster].hp = @ - creatures[Hunter].attack,
            ![Hunter].hasAttacked = TRUE
        ]    
    /\ currentTurn' = Monster  (* Define o próximo personagem a atacar *)

TurnMonster ==    
    /\ currentTurn = Monster  (* verifique se é o turno do monstro *)
    /\ creatures[Monster].hasAttacked = FALSE
    /\ creatures' = [ creatures EXCEPT 
            ![Hunter].hp = @ - creatures[Monster].attack,
            ![Druid].hp = @ - creatures[Monster].attack, 
            ![Mage].hp = @ - creatures[Monster].attack,
            ![Monster].hasAttacked = TRUE
        ]
    /\ currentTurn' = Mage

ResetHasAttacked ==
    /\ currentTurn = Mage  (* Reinicia quando o turno volta ao Mage *)
    /\ \A p \in DOMAIN creatures : creatures[p].hasAttacked = TRUE
    /\ creatures' = [creatures EXCEPT 
            ![Hunter].hasAttacked = FALSE,
            ![Druid].hasAttacked = FALSE,
            ![Mage].hasAttacked = FALSE,
            ![Monster].hasAttacked = FALSE
        ]
    /\ UNCHANGED <<currentTurn>>

(* Transição de turno com condição de parada *)
Next ==
    \/ CheckVictory
    \/ TurnMage
    \/ TurnDruid
    \/ TurnHunter
    \/ TurnMonster
    \/ ResetHasAttacked

Spec == Init /\ [][Next]_<<currentTurn, creatures>>
    

(* COISAS A FAZER
 
 - Vincular as iniciativas aleatórias com a ordem de ataque das criaturas
 - Criar Habilidade Ilusão do Mage
 - Criar Habilidade Cegueira do Hunter
 - Criar Habilidade Transformação selvagem do Druid
 - Criar Habilidade paralisia do Monster
 - Criar Maneira dos personagens sair da paralisa
 - Finalizar de maneira coerente

*)

=============================================================================
