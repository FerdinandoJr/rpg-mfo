------------------------------- MODULE RPGGame -------------------------------
EXTENDS Randomization, Naturals, Sequences, TLC 

CONSTANTS
    Hunter, 
    Druid, 
    Mage, 
    Monster

VARIABLES
    creatures,
    turns,
    countTurns
    
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
                isParalyzed |-> FALSE,   
                isBlind |-> FALSE   (* Atributo para indicar cegueira *)
		    ]
	    ]   
    /\ turns = SortSeq(<<Hunter, Druid, Mage, Monster>>,
                 LAMBDA x, y: 
                     IF creatures[x].initiative = creatures[y].initiative 
                     THEN CreatureOrder[x] < CreatureOrder[y]
                     ELSE creatures[x].initiative > creatures[y].initiative)
    /\ countTurns = 1
          
(* Verifica se o HP do Monster chegou a 0, indicando vitória dos heróis *)
VictoryHeroes ==
    /\ creatures[Monster].hp <= 0
    /\ UNCHANGED <<creatures, turns, countTurns>>

(* Verifica se o HP de todos os heróis chegou a 0, indicando vitória do Monster *)
VictoryMonster ==
    /\ creatures[Hunter].hp <= 0
    /\ creatures[Druid].hp <= 0
    /\ creatures[Mage].hp <= 0
    /\ UNCHANGED <<creatures, turns, countTurns>>

(* ------ Hunter -------*)

TurnHunter ==    
    /\ turns # <<>>
    /\ Head(turns) = Hunter
    /\ IF creatures[Hunter].hp > 0
        THEN IF creatures[Monster].isBlind = FALSE  (* Aplica cegueira apenas se o Monstro não estiver cego *)
                THEN /\ creatures' = [
                            creatures EXCEPT ![Monster].isBlind = TRUE
                        ]
                ELSE /\ creatures' = [
                            creatures EXCEPT ![Monster].hp = @ - creatures[Hunter].attack
                        ]                     
        ELSE /\ UNCHANGED <<creatures>>
    /\ turns' = Tail(turns)        (* Hunter ataca se o Monstro já estiver cego *)
    /\ countTurns' = countTurns + 1

(* ------ Mage -------*)

TurnMage ==
    /\ turns # <<>>
    /\ Head(turns) = Mage
    /\ IF creatures[Mage].hp > 0
        THEN /\ creatures' = [creatures EXCEPT ![Monster].hp = @ - creatures[Mage].attack]
             /\ turns' = Tail(turns)   (* Após atacar, remove a vez do Mage *)
        ELSE /\ turns' = Tail(turns)   (* Apenas remove a vez se o Mage estiver morto *)
             /\ UNCHANGED <<creatures>>
    /\ countTurns' = countTurns + 1

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
                 /\ IF CHOOSE x \in {TRUE, FALSE} : TRUE                    (* 50% de chance de transformar ou atacar *)
                    THEN  /\ creatures' = [creatures EXCEPT 
                                ![Druid].hp = 60,                           (* Define HP do urso *)
                                ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                                ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                            ]
                    ELSE /\ creatures' = [creatures EXCEPT 
                                ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                            ]
            ELSE 
                IF CHOOSE x \in {TRUE, FALSE} : TRUE                    (* 50% de chance de transformar ou atacar *)
                THEN  /\ creatures' = [creatures EXCEPT 
                            ![Druid].hp = 60,                           (* Define HP do urso *)
                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                        ]
                ELSE /\ creatures' = [creatures EXCEPT 
                            ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                        ]
    /\ turns' = Tail(turns)                                         (* Remove a vez do Druid *)
    /\ countTurns' = countTurns + 1

(* ------ Monster -------*)
TurnMonster ==    
    /\ turns # <<>>                           (* Verifica se turns não está vazio *)
    /\ Head(turns) = Monster
    /\ creatures' = 
        LET targetHero == 
            IF creatures[Druid].isBear = TRUE  (* Preferência para atacar o Druid Transformado *)
                THEN Druid
                ELSE CHOOSE h \in {Hunter, Druid, Mage} : creatures[h].hp > 0
        IN IF creatures[Monster].isBlind 
            THEN [creatures EXCEPT ![Monster].isBlind = FALSE] (* Termina a cegueira *)
            ELSE IF CHOOSE x \in {TRUE, FALSE} : TRUE    (* 50% de chance de atacar ou paralisar *)
                THEN 
                    [creatures EXCEPT ![targetHero].isParalyzed = TRUE]   (* Paralisia no alvo *)
                ELSE                                             
                    IF countTurns = 1   (* Verifica se é o primeiro turno para aplicar ataque reduzido *)
                        THEN [ creatures EXCEPT ![targetHero].hp = @ - 10]  (* primeiro turno da partida indeira *)
                        ELSE [ creatures EXCEPT ![targetHero].hp = @ - creatures[Monster].attack ]
    /\ turns' = Tail(turns)
    /\ countTurns' = countTurns + 1

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
                 /\ UNCHANGED <<creatures, countTurns>>



(* Transição de turno com condição de parada *)
Next ==
    \/ (turns = <<>> /\ ResetTurn)
    \/ TurnMage
    \/ TurnDruid
    \/ TurnHunter
    \/ TurnMonster

Spec == Init /\ [][Next]_<<creatures, turns, countTurns>>
    

(* COISAS A FAZER
 
 - Criar Habilidade Ilusão do Mage
 - Criar Habilidade Cegueira do Hunter
 - Criar Habilidade paralisia do Monster
 - Criar Maneira dos personagens sair da paralisa

*)

=============================================================================

