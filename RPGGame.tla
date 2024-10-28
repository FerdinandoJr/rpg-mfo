------------------------------- MODULE RPGGame -------------------------------
EXTENDS Randomization, Naturals, Sequences

CONSTANTS
    Hunter, 
    Druid, 
    Mage, 
    Monster

VARIABLES
    hp,              (* Pontos de vida de cada criatura *)
    paralyzed,       (* Indica se cada criatura está paralisada *)
    initiative,      (* Iniciativa de cada criatura *)    
    hasAttacked,     (* Status de ataque de cada personagem *)
    currentTurn
(* 
    Estado inicial:
    - Cada personagem começa com 20 HP, e o monstro com 100 HP.
*)

Init ==
    /\ hp = [ Hunter |-> 20, Druid |-> 20, Mage |-> 20, Monster |-> 100 ]
    /\ paralyzed = [ Hunter |-> FALSE, Druid |-> FALSE, Mage |-> FALSE, Monster |-> FALSE ]
    /\ initiative = [ (* Define o d20 de cada criatura *)
            Hunter |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE, 
            Druid  |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
            Mage   |-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE,
            Monster|-> CHOOSE x \in RandomSubset(1, 1..20) : TRUE
        ]
    /\ hasAttacked = [ Hunter |-> FALSE, Druid |-> FALSE, Mage |-> FALSE, Monster |-> FALSE ]
    /\ currentTurn = Mage

(* Ação que reduz 5 pontos de vida da próxima criatura na ordem de iniciativa *)
ReduceHP == 
    /\ hp[Monster] > 0 (* Só reduz se ainda tiver HP *)
    /\ hp' = [hp EXCEPT ![Monster] = @ - 5]  (* Reduz 5 de HP do atual *)
    /\ UNCHANGED <<paralyzed, hasAttacked, initiative, currentTurn>>  (* Mantém o estado de paralisia *)

(* Verifica se o HP do Monster chegou a 0, indicando vitória dos heróis *)
VictoryHeroes ==
    hp[Monster] <= 0
    

(* Verifica se o HP de todos os heróis chegou a 0, indicando vitória do Monster *)
VictoryMonster ==
    /\ hp[Hunter] <= 0
    /\ hp[Druid] <= 0
    /\ hp[Mage] <= 0

(* Verifica se ocorreu uma condição de vitória *)
CheckVictory ==
    \/ VictoryHeroes
    \/ VictoryMonster

TurnMage ==
    /\ currentTurn = Mage
    /\ hasAttacked[Mage] = FALSE
    /\ hp[Monster] > 0 (* Só reduz se ainda tiver HP *)
    /\ hp' = [hp EXCEPT ![Monster] = @ - 5]
    /\ hasAttacked' = [hasAttacked EXCEPT ![Mage] = TRUE]
    /\ currentTurn' = Druid  (* Define o próximo personagem a atacar *)
    /\ UNCHANGED <<paralyzed, initiative>>  (* Mantém o estado de paralisia *)

TurnDruid ==
    /\ currentTurn = Druid
    /\ hasAttacked[Druid] = FALSE
    /\ hp[Monster] > 0 (* Só reduz se ainda tiver HP *)
    /\ hp' = [hp EXCEPT ![Monster] = @ - 5]
    /\ hasAttacked' = [hasAttacked EXCEPT ![Druid] = TRUE]
    /\ currentTurn' = Hunter  (* Define o próximo personagem a atacar *)
    /\ UNCHANGED <<paralyzed, initiative>>  (* Mantém o estado de paralisia *)

TurnHunter ==
    /\ currentTurn = Hunter
    /\ hasAttacked[Hunter] = FALSE
    /\ hp[Monster] > 0 (* Só reduz se ainda tiver HP *)
    /\ hp' = [hp EXCEPT ![Monster] = @ - 5]
    /\ hasAttacked' = [hasAttacked EXCEPT ![Hunter] = TRUE]
    /\ currentTurn' = Monster  (* Define o próximo personagem a atacar *)
    /\ UNCHANGED <<paralyzed, initiative>>  (* Mantém o estado de paralisia *)

TurnMonster ==    
    /\ currentTurn = Monster  (* verifique se é o turno do monstro *)
    /\ hasAttacked[Monster] = FALSE
    /\ hp' = [hp EXCEPT ![Hunter] = @ - 5, ![Druid] = @ - 5, ![Mage] = @ - 5]
    /\ currentTurn' = Mage
    /\ hasAttacked' = [hasAttacked EXCEPT ![Monster] = TRUE]    
    /\ UNCHANGED <<paralyzed, initiative>>  (* Mantém o estado de paralisia *)

ResetHasAttacked ==
    /\ currentTurn = Mage  (* Reinicia quando o turno volta ao Mage *)
    /\ \A p \in DOMAIN hasAttacked : hasAttacked[p] = TRUE
    /\ hasAttacked' = [ p \in DOMAIN hasAttacked |-> FALSE ]
    /\ UNCHANGED <<hp, paralyzed, initiative, currentTurn>>

(* Transição de turno com condição de parada *)
Next ==
    \/ TurnMage
    \/ TurnDruid
    \/ TurnHunter
    \/ TurnMonster
    \/ ResetHasAttacked
    \/ CheckVictory

Spec == Init /\ [][Next]_<<hp, paralyzed, initiative, hasAttacked, currentTurn>>

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

