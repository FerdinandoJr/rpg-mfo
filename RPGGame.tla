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
                isParalyzed |-> FALSE,
                illusionExists |-> FALSE,
                illusionHP |-> 0
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
    /\ countTurns' = countTurns + 1
    /\ IF creatures[Druid].isParalyzed = TRUE (* Não pode efetuar ações se estiver paralisado *)    
        THEN /\ UNCHANGED <<creatures>>
        ELSE IF creatures[Hunter].hp > 0
            THEN 
                (* Verifica se há algum herói paralisado *)
                LET paralyzedHeroes == {h \in {Druid, Mage} : creatures[h].isParalyzed = TRUE}
                IN 
                    IF paralyzedHeroes # {}
                    THEN 
                            \/(LET paralyzedHero == CHOOSE h \in paralyzedHeroes : TRUE IN
                                    /\ creatures' = [creatures EXCEPT ![paralyzedHero].isParalyzed = FALSE]
                                    /\ turns' = Tail(turns)   (* Usa o turno para remover a paralisia *)
                                    /\ UNCHANGED <<creatures>>)
                            \/(creatures' = [
                                            creatures EXCEPT ![Monster].isBlind = TRUE
                                        ])
                            \/(creatures' = [
                                            creatures EXCEPT ![Monster].hp = @ - creatures[Hunter].attack
                                        ])
                        ELSE 
                            (* Se nenhum herói estiver paralisado, ataque o Monstro ou Cegue ele*)
                                \/(creatures' = [
                                            creatures EXCEPT ![Monster].isBlind = TRUE
                                        ])
                                \/(creatures' = [
                                            creatures EXCEPT ![Monster].hp = @ - creatures[Hunter].attack
                                        ])                         
            ELSE /\ UNCHANGED <<creatures>>
    /\ turns' = Tail(turns)


(* ------ Mage -------*)
TurnMage ==
    /\ turns # <<>>
    /\ Head(turns) = Mage
    /\ countTurns' = countTurns + 1
    /\ turns' = Tail(turns)
    /\ IF creatures[Mage].isParalyzed = TRUE    
        THEN /\ UNCHANGED <<creatures>>
        ELSE IF creatures[Mage].hp > 0
            THEN 
                LET paralyzedHeroes == {h \in {Druid, Hunter} : creatures[h].isParalyzed = TRUE}
                IN 
                    IF paralyzedHeroes # {}
                    THEN 
                        \/(LET paralyzedHero == CHOOSE h \in paralyzedHeroes : TRUE IN
                                /\ creatures' = [creatures EXCEPT ![paralyzedHero].isParalyzed = FALSE])
                        \/(creatures' = [ creatures EXCEPT  (* Refaz a ilusão *)
                                        ![Mage].illusionExists = TRUE,
                                        ![Mage].illusionHP = 1])
                        \/(creatures' = [ creatures EXCEPT  (* Desfaz a ilusão *)
                                    ![Mage].illusionExists = FALSE,
                                    ![Mage].illusionHP = 0,
                                    ![Monster].hp = @ - creatures[Mage].attack (* Ataca o monstro *)
                                ])
                    ELSE                      
                        IF CHOOSE x \in {TRUE, FALSE} : TRUE    (* 50% de chance de atacar ou criar ilusão *)
                        THEN 
                            /\ creatures' = [ creatures EXCEPT  (* Desfaz a ilusão *)
                                    ![Mage].illusionExists = FALSE,
                                    ![Mage].illusionHP = 0,
                                    ![Monster].hp = @ - creatures[Mage].attack (* Ataca o monstro *)
                                ]
                        ELSE                                             
                            /\ creatures' = [ creatures EXCEPT  (* Refaz a ilusão *)
                                    ![Mage].illusionExists = TRUE,
                                    ![Mage].illusionHP = 1
                                ]    
            ELSE 
                /\ UNCHANGED <<creatures>> (* Mago está morto *)

(* ------ Druid -------*)

TurnDruid ==
    /\ turns # <<>> 
    /\ Head(turns) = Druid
    /\ countTurns' = countTurns + 1
    /\  IF creatures[Druid].isParalyzed = TRUE (* Não pode efetuar ações se estiver paralisado *)    
        THEN /\ UNCHANGED <<creatures>>
        ELSE IF creatures[Druid].hp <= 0                                  (* Druid morreu *)
            THEN 
                IF creatures[Druid].isBear = TRUE                       (* Morreu enquanto estava transformado *)  
                THEN /\ creatures' = [creatures EXCEPT                  (* Reverte a transformação *)
                            ![Druid].hp = creatures[Druid].originalHP,  (* Restaura HP original *)
                            ![Druid].isBear = FALSE,                    (* Remove o status de urso *)
                            ![Druid].originalHP = 0
                        ]
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
                    ELSE /\ UNCHANGED <<creatures>>                         (* Não ta transformado e está morto*)                              
            ELSE 
                IF creatures[Druid].isBear = TRUE                           (* Druid está em forma de urso e vivo *)
                THEN /\ creatures' = [creatures EXCEPT                      (* Expira a transformação *)
                            ![Druid].hp = creatures[Druid].originalHP,      (* Restaura HP original *)
                            ![Druid].isBear = FALSE,                        (* Remove o status de urso *)
                            ![Druid].originalHP = 0
                        ]
                    /\ LET paralyzedHeroes == {h \in {Mage, Hunter} : creatures[h].isParalyzed = TRUE} IN 
                        IF paralyzedHeroes # {}
                        THEN 
                            \/(LET paralyzedHero == CHOOSE h \in paralyzedHeroes : TRUE IN
                                /\ creatures' = [creatures EXCEPT ![paralyzedHero].isParalyzed = FALSE]
                                /\ turns' = Tail(turns)   (* Usa o turno para remover a paralisia *)
                                /\ UNCHANGED <<creatures>>)
                            \/(creatures' = [creatures EXCEPT 
                                            ![Druid].hp = 60,                           (* Define HP do urso *)
                                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                                        ])
                            \/(creatures' = [creatures EXCEPT 
                                            ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                                        ])

                        ELSE /\ IF CHOOSE x \in {TRUE, FALSE} : TRUE                    (* 50% de chance de transformar ou atacar *)
                                THEN  /\ creatures' = [creatures EXCEPT 
                                            ![Druid].hp = 60,                           (* Define HP do urso *)
                                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                                        ]
                                ELSE /\ creatures' = [creatures EXCEPT 
                                            ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                                        ]
                    ELSE 
                        LET paralyzedHeroes == {h \in {Mage, Hunter} : creatures[h].isParalyzed = TRUE}
                        IN 
                            IF paralyzedHeroes # {}
                            THEN 
                                \/(LET paralyzedHero == CHOOSE h \in paralyzedHeroes : TRUE IN
                                    /\ creatures' = [creatures EXCEPT ![paralyzedHero].isParalyzed = FALSE]
                                    /\ turns' = Tail(turns)   (* Usa o turno para remover a paralisia *)
                                    /\ UNCHANGED <<creatures>>)
                                \/(creatures' = [creatures EXCEPT 
                                            ![Druid].hp = 60,                           (* Define HP do urso *)
                                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                                        ])
                                \/(creatures' = [creatures EXCEPT 
                                            ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                                        ])
                            ELSE IF CHOOSE x \in {TRUE, FALSE} : TRUE                    (* 50% de chance de transformar ou atacar *)
                                THEN  /\ creatures' = [creatures EXCEPT 
                                            ![Druid].hp = 60,                           (* Define HP do urso *)
                                            ![Druid].isBear = TRUE,                     (* Marca a transformação *)
                                            ![Druid].originalHP = creatures[Druid].hp   (* Armazena HP original *)
                                        ]
                                ELSE /\ creatures' = [creatures EXCEPT 
                                            ![Monster].hp = @ - creatures[Druid].attack (* Ataca o monstro *)
                                        ]
    /\ turns' = Tail(turns)                                         (* Remove a vez do Druid *)

(* ------ Monster -------*)
TurnMonster ==    
    /\ turns # <<>>                           (* Verifica se turns não está vazio *)
    /\ Head(turns) = Monster
    /\ creatures' = 
        LET targetHero == 
            IF creatures[Druid].isBear = TRUE  (* Preferência para atacar o Druid Transformado *)
                THEN Druid
		ELSE
		IF creature[Mage].illusionExists = TRUE
		THEN Mage
                ELSE 
		CHOOSE h \in {Hunter, Druid, Mage} : creatures[h].hp > 0
        IN IF creatures[Monster].isBlind 
            THEN [creatures EXCEPT ![Monster].isBlind = FALSE] (* Termina a cegueira *)
            ELSE IF CHOOSE x \in {TRUE, FALSE} : TRUE    (* 50% de chance de atacar ou paralisar *)
                THEN 
                    [creatures EXCEPT ![targetHero].isParalyzed = TRUE]   (* Paralisia no alvo *)
                ELSE
		    IF creatures[Mage].illusionExists = TRUE
                    THEN [ creatures EXCEPT ![targetHero].illusionHP = @ - 1]
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

(* invariantes *)
MonstroNaoMorre == creatures[Monster].hp > 0

NenhumPersonagemMorre == /\ creatures[Mage].hp > 0
                         /\ creatures[Druid].hp > 0
                         /\ creatures[Hunter].hp > 0

=============================================================================
