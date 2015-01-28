Require Import Arith.
Require Import List.


Definition var := nat.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_app  : trm -> trm -> trm
| trm_abs  : trm -> trm.

(* u is the fresh variable name we use to open t 
   k is the current depth *)
Fixpoint open_rec (k : nat) (x : var) (t : trm) : trm :=
  match t with
    | trm_bvar i    => if (beq_nat k i) then trm_fvar x else (trm_bvar i)
    | trm_fvar y    => trm_fvar y 
    | trm_app t1 t2 => trm_app (open_rec k x t1) (open_rec k x t2)
    | trm_abs t1    => trm_abs (open_rec (S k) x t1) 
  end.

Definition open t x := open_rec 0 x t.


Fixpoint close_var_rec (k : nat) (x : var) (t : trm) : trm :=
  match t with
    | trm_bvar i    => trm_bvar i 
    | trm_fvar y    => if beq_nat x y then (trm_bvar k) else (trm_fvar y)
    | trm_app t1 t2 => trm_app (close_var_rec k x t1) (close_var_rec k x t2)
    | trm_abs t1    => trm_abs (close_var_rec (S k) x t1) 
  end.

Definition close_var x t := close_var_rec 0 x t.

Fixpoint locally_closed_at_rec (k : nat) (t : trm) : Prop :=
  match t with
    | trm_bvar i    => i < k
    | trm_fvar x    => True
    | trm_app t1 t2 => (locally_closed_at_rec k t1) /\ (locally_closed_at_rec k t2)
    | trm_abs t1    => (locally_closed_at_rec (S k) t1)
  end.

Definition locally_closed (t:trm) : Prop := locally_closed_at_rec 0 t.

Fixpoint free_variables (t:trm) : list var :=
   match t with
    | trm_bvar i    => nil
    | trm_fvar x    => x :: nil
    | trm_app t1 t2 => (free_variables t1)++(free_variables t2)
    | trm_abs t1    => (free_variables t1)
  end.

Definition fresh (x:var) (t:trm) : Prop :=
  ~(In x (free_variables t)).

Lemma lc_at_app:
  forall c:nat, forall t1:trm, forall t2:trm, locally_closed_at_rec c (trm_app t1 t2) -> (locally_closed_at_rec c t1) /\ (locally_closed_at_rec c t2).
Proof.
  intros.
  simpl in H.
  exact H.
Qed.



Lemma close_open_var :
  forall t:trm, forall k:nat, exists u:var, fresh u t -> (close_var_rec k u (open_rec k u t)) = t.
Proof.
  intros.
  induction t.
  - induction k.
    
    
  (*   induction n. *)
  (*   case (n=0). *)
  (*   simpl. *)
  (*   assert (forall u0:var, beq_nat u0 u0 = true).   *)
  (*   intros. *)
  (*   induction u0.  *)
  (*   reflexivity. *)
  (*   simpl. *)
  (*   exact IHu0. *)
    


    
  (*   induction k. *)
  (*   simpl. *)
  (*   induction n. *)
  (*   simpl. *)
  (*   assert (forall u:var, beq_nat u u = true).   *)
  (*   intros. *)
  (*   induction u0.  *)
  (*   reflexivity. *)
  (*   simpl. *)
  (*   exact IHu0. *)
  (*   rewrite H. *)
  (*   reflexivity. *)
  (*   simpl. *)
  (*   reflexivity. *)
  (*   induction n. *)
  (*   simpl. *)
  (*   reflexivity. *)
  (*   simpl. *)
  (*   simpl. *)








  (*   induction t. *)
  (*   induction u. *)
  (*   induction n.  *)
  (* -simpl. *)
  (*  simpl. *)
  (*  reflexivity. *)
  (* - simpl. *)
  (*   reflexivity. *)
  (* - destruct n. *)
  (*   simpl. *)
  (*   assert (forall u:var, beq_nat u u = true).   *)
  (*   intros. *)
  (*   induction u0. *)
    
  (*   reflexivity. *)
  (*   simpl. *)
  (*   exact IHu0. *)
  (*   rewrite H. *)
  (*   reflexivity. *)
  (*   simpl. *)
  (*   reflexivity.     *)
  (* -  *)


  (*   simpl close_var_rec. *)
  (*   induction v. *)
  (*   induction u. *)
  (*   simpl. *)
  (*   simpl      *)



Qed.

Lemma open_close_var :
  forall u:var, forall t:trm, (open_rec 0 u (close_var_rec 0 u t)) = t.
Proof.
  intros.
  
Qed.



Lemma lc_from_lc_at:
  forall c:nat, forall t:trm, locally_closed_at_rec 0 t -> locally_closed c t.
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

