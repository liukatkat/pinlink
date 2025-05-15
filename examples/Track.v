Require Import List Lia.
Import ListNotations.

Fixpoint alternate (X : Type) (l1 l2 : list X) : list X :=
  match l1, l2 with
  | nil   , _      => l2
  | _     , nil    => l1 
  | h1::t1, h2::t2 => h1 :: h2 :: alternate X t1 t2
  end.

Theorem alternate_length :  
forall (X : Type) (l1 l2: list X), 
  length l1 + length l2 = length (alternate X l1 l2). 
Proof. 
 induction l1; simpl. 
 - auto. 
 - destruct l2; simpl. 
   + admit.
   + rewrite <- IHl1. lia.