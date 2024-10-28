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
                isParalyzed |-> FALSE,
                isBear |-> FALSE,  (* Verifica se o Druida está transformado *)
                originalHP |-> 0   (* Guarda o HP original antes da transformação *)
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

(* ------ Hunter -------*)

TurnHunter ==    
    /\ turns # <<>>
    /\ Head(turns) = Hunter
    /\ IF creatures[Hunter].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Hunter].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Hunter *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Hunter estiver morto *)
             /\ UNCHANGED <<creatures>>

(* ------ Mage -------*)

TurnMage ==
    /\ turns # <<>>
    /\ Head(turns) = Mage
    /\ IF creatures[Mage].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Mage].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Mage *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Mage estiver morto *)
             /\ UNCHANGED <<creatures>>

(* ------ Druid -------*)

TurnDruid ==
    /\ turns # <<>> 
    /\ Head(turns) = Druid
    /\ IF creatures[Druid].hp <= 0                                  (* Druid morreu *)
        THEN 
            IF creatures[Druid].isBear = TRUE                       (* Morreu enquanto estava transformado *)  
            THEN /\ creatures' = [creatures EXCEPT                  (* Reverte a transformação *)
                        ![Druid].hp = creatures[Druid].originalHP,  (* Restaura HP original *)
                        ![Druid].isBear = FALSE,                    (* Remove o status de urso *)
                        ![Druid].originalHP = 0
                    ]
            ELSE /\ UNCHANGED <<creatures>>                         (* Sem transformação ativa, nada muda *)
        ELSE 
            IF creatures[Druid].isBear = TRUE                           (* Druid está em forma de urso e vivo *)
            THEN /\ creatures' = [creatures EXCEPT                      (* Expira a transformação *)
                        ![Druid].hp = creatures[Druid].originalHP,      (* Restaura HP original *)
                        ![Druid].isBear = FALSE,                        (* Remove o status de urso *)
                        ![Druid].originalHP = 0
                    ]
            ELSE 
                IF TRUE                                                 (* Decisão de transformar ou atacar *)
                THEN /\ creatures' = [creatures EXCEPT                  (* Transformação em urso *)
                            ![Druid].hp = 60,                           (* Define HP do urso *)
                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                        ]
                ELSE /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Druid].attack] (* Ataca o monstro *)
    /\ turns' = Tail(turns)                                         (* Remove a vez do Druid *)




(* ------ Monster -------*)
TurnMonster ==    
    /\ turns # <<>>                           (* Verifica se turns não está vazio *)
    /\ Head(turns) = Monster
    /\ creatures' = 
        LET targetHero == 
            IF creatures[Druid].isBear = TRUE (* Preferencia para atacar o Druid Transformado *)
                THEN Druid
                ELSE CHOOSE h \in {Hunter, Druid, Mage} : creatures[h].hp > 0
        IN [creatures EXCEPT ![targetHero].hp = @ - creatures[Monster].attack]
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
 - Criar Habilidade paralisia do Monster
 - Criar Maneira dos personagens sair da paralisa

*)

=============================================================================

