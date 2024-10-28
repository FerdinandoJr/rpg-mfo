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
                attack |-> 5,
                isParalyzed |-> FALSE
		    ], 
		Druid |-> [
			    hp |-> 20,			
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 5,
                isParalyzed |-> FALSE
		    ], 
		Mage |-> [
			    hp |-> 20,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 5,
                isParalyzed |-> FALSE
		    ],
		Monster |-> [
                hp |-> 100,
                initiative |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
                attack |-> 5,
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

(* Verifica se ocorreu uma condição de vitória *)
CheckVictory ==
    \/ VictoryHeroes
    \/ VictoryMonster

TurnMage ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Mage
    /\ creatures[Monster].hp > 0
    /\ creatures' = [creatures EXCEPT 
            ![Monster].hp = @ - creatures[Mage].attack
        ]
    /\ turns' = Tail(turns)
    
TurnDruid ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Druid
    /\ creatures[Monster].hp > 0
    /\ creatures' = [creatures EXCEPT 
            ![Monster].hp = @ - creatures[Druid].attack            
        ]
    /\ turns' = Tail(turns)

TurnHunter ==
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Hunter
    /\ creatures[Monster].hp > 0
    /\ creatures' = [creatures EXCEPT 
            ![Monster].hp = @ - creatures[Hunter].attack
        ]
    /\ turns' = Tail(turns)

TurnMonster ==    
    /\ turns # <<>>                (* Verifica se turns não está vazio *)
    /\ Head(turns) = Monster
    /\ creatures' = [creatures EXCEPT 
            ![Hunter].hp = @ - creatures[Monster].attack,
            ![Druid].hp = @ - creatures[Monster].attack, 
            ![Mage].hp = @ - creatures[Monster].attack
        ]
    /\ turns' = Tail(turns)

NextTurn ==    
    /\ turns = <<>>
    /\ turns'= SortSeq(<<Hunter, Druid, Mage, Monster>>,
                 LAMBDA x, y: 
                     IF creatures[x].initiative = creatures[y].initiative 
                     THEN CreatureOrder[x] < CreatureOrder[y]
                     ELSE creatures[x].initiative > creatures[y].initiative)
    /\ UNCHANGED <<creatures>>


(* Transição de turno com condição de parada *)
Next ==
    \/ CheckVictory
    \/ NextTurn  (* Recarrega turns quando vazio *)
    \/ TurnMage
    \/ TurnDruid
    \/ TurnHunter
    \/ TurnMonster

Spec == Init /\ [][Next]_<<creatures, turns>>
    

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

