Require Import Arith.

Definition var := nat.

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_app  : trm -> trm -> trm
  | trm_abs  : trm -> trm.

(* u is the fresh variable name we use to open t 
   k is the current depth *)
Fixpoint open_rec (k : nat) (u : trm) (t : trm) : trm :=
  match t with
  | trm_bvar i    => if (beq_nat k i) then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_app t1 t2 => trm_app (open_rec k u t1) (open_rec k u t2)
  | trm_abs t1    => trm_abs (open_rec (S k) u t1) 
  end.

Definition open t u := open_rec 0 u t.

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => if beq_nat x z then (trm_bvar k) else (trm_fvar x)
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t1    => trm_abs (close_var_rec (S k) z t1) 
  end.


Definition close_var z t := close_var_rec 0 z t.

Fixpoint locally_closed_rec (k : nat) (t : trm) : Prop :=
  match t with
  | trm_bvar i    => i < k
  | trm_fvar x    => True
  | trm_app t1 t2 => (locally_closed_rec k t1) /\ (locally_closed_rec k t2)
  | trm_abs t1    => (locally_closed_rec (S k) t1)
  end.

Lemma lc_app_k:
  forall c:nat, forall t1:trm, forall t2:trm, locally_closed_rec c (trm_app t1 t2) -> (locally_closed_rec c t1) /\ (locally_closed_rec c t2).
Proof.
  intros.
  simpl in H.
  exact H.
Qed.

Lemma lc_at0:
  forall c:nat, forall t:trm, locally_closed_rec 0 t -> locally_closed_rec c t.
Proof.
(*   intros. *)
(*   induction c. *)
(*   exact H. *)
(*   induction t. *)
(*   unfold locally_closed_rec in IHc. *)
(*   compute. *)
(*   assert (S n < S c). *)
(*   apply lt_n_S. *)
(*   exact IHc. *)
(*   apply lt_le_weak. *)
(*   exact H0. *)
(* - compute. *)
(*   reflexivity. *)
(* - simpl in H. *)
(*   simpl in IHc. *)
(*   simpl. *)
(*   split. *)
(*   apply IHt1. *)
(*   elim H. *)
(*   intros. *)
(*   exact H0. *)
(*   elim IHc. *)
(*   intros. *)
(*   exact H0. *)
(*    apply IHt2. *)
(*   elim H. *)
(*   intros. *)
(*   exact H1. *)
(*   elim IHc. *)
(*   intros. *)
(*   exact H1. *)
(* -  *)
   
  
  
    
   
Qed.

Definition locally_closed t := locally_closed_rec 0 t.

Example closed_ex1:
  locally_closed (trm_abs (trm_bvar 0)).
Proof.
  compute. reflexivity.
Qed.

