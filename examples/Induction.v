(** * Proof by Induction *)
(** We can prove that [0] is a neutral element for [+] on the _left_
using just [reflexivity].  But the proof that it is also a neutral
element on the _right_ ... *)  

Theorem add_0_r_broken_1 : forall n:nat,
    n + 0 = n.
Proof.
    intros n.
    simpl.
Abort.

Theorem add_0_r_broken_2 : forall n:nat, 
    n + 0 = n.
Proof.
    intros n. destruct n as [| n'] eqn:E.
    - (* n = 0 *)  
        reflexivity.
    - (* n = S n' *) 
        simpl.
Abort.

Theorem add_0_r : forall n:nat,
    n + 0 = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - (* n = 0 *)  
        reflexivity.
    - (* n = S n' *) 
        simpl.
        rewrite -> IHn'.
        reflexivity.
Qed.