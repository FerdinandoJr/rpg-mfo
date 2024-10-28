------------------------------- MODULE Vida -------------------------------
EXTENDS Naturals

(* Constante *)
CONSTANTS PessoaNome

(* Variável *)
VARIABLES hp

(* Estado inicial: a pessoa começa com 100 de vida *)
Init ==
    /\ hp = 100
    /\ PessoaNome \in STRING  (* Assegura que o nome é uma string *)

(* Transição: Reduz a vida em 10 a cada passo *)
Next ==
    /\ hp > 0
    /\ hp' = hp - 10

(* Condição de Término: o jogo termina quando a vida chega a 0 *)
Terminated ==
    hp = 0

(* Especificação de Segurança *)
Spec ==
    Init /\ [][Next]_<<hp>> /\ <>Terminated

===============================================================================
