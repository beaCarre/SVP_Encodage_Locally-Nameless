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
    | trm_bvar i    => if (eq_nat_dec k i) then trm_fvar x else (trm_bvar i)
    | trm_fvar y    => trm_fvar y 
    | trm_app t1 t2 => trm_app (open_rec k x t1) (open_rec k x t2)
    | trm_abs t1    => trm_abs (open_rec (S k) x t1) 
  end.

Definition open t x := open_rec 0 x t.


Fixpoint close_var_rec (k : nat) (x : var) (t : trm) : trm :=
  match t with
    | trm_bvar i    => trm_bvar i 
    | trm_fvar y    => if eq_nat_dec x y then (trm_bvar k) else (trm_fvar y)
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

Definition closed (t:trm) : Prop :=
  (free_variables t) = nil.

Lemma close_open_var_rec :
  forall t:trm, forall u:var,forall k:nat, fresh u t -> (close_var_rec k u (open_rec k u t)) = t.
Proof.
  intros t u.
  induction t.
  intro k.
  unfold fresh.
  unfold free_variables.
  unfold close_var_rec.
  unfold open_rec.
  intro.
  destruct (eq_nat_dec k n).
  destruct (eq_nat_dec u u).
  rewrite e.
  reflexivity.
  contradict n0.
  reflexivity.
  reflexivity.
  destruct (eq_nat_dec u v).
  rewrite e.
  simpl.
  unfold fresh.
  unfold free_variables.
  intros.  
  contradict H.
  simpl.
  left.
  reflexivity.
  unfold fresh.
  unfold free_variables.
  simpl.
  intros.
  destruct (eq_nat_dec u v).
  contradict H.
  left.
  rewrite e.
  reflexivity.
  reflexivity.
  intros.
  unfold fresh  in *.
  simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.  
  contradict H.
  simpl.
  SearchPattern ( In _ ( _ ++ _ )).  
  apply in_or_app.
  right.
  exact H.
  simpl in H.
  contradict H.
  apply in_or_app.
  left.
  exact H.
  intros.
  simpl.
  unfold fresh in H.
  unfold fresh in IHt.
  simpl in H.
  rewrite IHt.
  reflexivity.
  exact H.

Qed.

Lemma close_open_var :
  forall t:trm, forall u:var, 
    fresh u t -> (close_var u (open t u)) = t.
Proof.
  intros.
  apply close_open_var_rec.
  exact H.
Qed.

Lemma incl_nil : 
  forall (A : Set) (l : list A), incl nil l.
Proof.
  intros A l.
  unfold incl in |- *.
  unfold In in |- *; contradiction.
Qed.


Lemma elim_incl_cons : forall (A : Type) (x : A) (xs zs : list A),
                         incl (x :: xs) zs ->
                         In x zs /\ incl xs zs.
Proof. unfold incl. auto with datatypes. Qed.



Lemma elim_incl_app : forall (A : Type) (xs ys zs : list A),
                        incl (xs ++ ys) zs ->
                        incl xs zs /\ incl ys zs.
Proof. unfold incl. auto with datatypes. Qed.


Lemma incl_app_comm :
  forall (A : Type) (x:A) (xs ys zs : list A),
    incl xs (x::ys++zs) ->  incl xs (x::zs++ys).
Proof.
  intros A x xs ys zs.
  unfold incl. 
  intros.
  apply in_inv with (b:=a) in H.
  rewrite app_comm_cons.
  apply in_or_app.
  
  elim H.
  intro.
  rewrite H1.
  simpl.
  left.  
  left.  
  reflexivity.
  intro.
  apply in_app_or in H1.
  elim H1.
  intro.
  right.
  exact H2.
  intro.
  left.
  apply in_cons.
  exact H2.
  exact H0.
Qed.


Lemma open_var_fv:
  forall x:var, forall t:trm, forall k:nat, incl (free_variables (open_rec k x t)) (x::(free_variables t)).
Proof.
  intros x t.
  


  induction t.
  simpl.
  intro k.
  destruct (eq_nat_dec k n).
  simpl.
  SearchPattern (incl _ _ ).

  apply incl_refl.
  simpl.
  apply incl_nil.
  intro k.
  simpl.
  apply incl_tl.
  apply incl_refl.
  intro k.
  simpl.
  apply incl_app.

  rewrite app_comm_cons.
  apply incl_appl.
  apply IHt1.
  apply incl_app_comm.
  rewrite app_comm_cons.
  apply incl_appl.
  apply IHt2.

  simpl.
  intro k.
  apply IHt.
Qed.


Fixpoint remove_var (x:var) (l:list var) : list var :=
  match l with
  | nil => nil
  | h::tl => if (eq_nat_dec x h) then remove_var x tl else h::(remove_var x tl) 
  end.

Lemma remove_cons:
  forall (x:var) (l1:list var) (l2:list var),
    (remove_var x (l1++l2)) = (remove_var x l1)++(remove_var x l2).
Proof.
  intros.
  induction l1.
  - simpl. 
    reflexivity.
  - induction l2.
    * simpl.
      remember (eq_nat_dec x a) as cond.
      simpl in IHl1.
      rewrite IHl1.
      induction cond.
      + reflexivity.
      + simpl.
        reflexivity.
    * simpl.
      remember (eq_nat_dec x a) as cond1.
      induction cond1. 
      Admitted.



Lemma fv_abs:
  forall t:trm, 
    free_variables t = free_variables (trm_abs t).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma close_var_fv:
  forall (x:var), forall (t:trm),
    (free_variables (close_var x t)) = (remove_var x (free_variables t)).
Proof.
  intros.
  induction t.
  - simpl.
    reflexivity.
    
  - unfold close_var.
    simpl.
    remember (eq_nat_dec x v) as e. 
    induction e.
    * simpl. 
      reflexivity.
    * simpl.
      reflexivity.

  - simpl.
    rewrite remove_cons.
    inversion IHt1.
    inversion IHt2.
    unfold close_var.
    reflexivity.

  - 







Fixpoint subst (x:var) (u:trm) (t:trm) : trm :=
  match t with
    | trm_bvar i    => trm_bvar i
    | trm_fvar y    => if (eq_nat_dec x y) then u else trm_fvar y 
    | trm_app t1 t2 =>  trm_app (subst x u t1) (subst x u t2)
    | trm_abs t1    =>  trm_abs (subst x u t1)
  end.


Lemma subst_lc :
  forall (t:trm) (u:trm) (x:var) (k:nat),
    locally_closed_at_rec k t /\ locally_closed_at_rec k u -> locally_closed_at_rec k (subst x u t).
Proof.
(*   intros t u x. *)
(*   induction t. *)

(*   simpl. *)
(*   intros. *)
(*   elim H. *)
(*   intros. *)
(*   exact H0. *)
(*   unfold subst. *)
(*   simpl. *)
(*   intros.   *)
(*   destruct (eq_nat_dec x v). *)
(*   elim H. *)
(*   intros. *)
(*   exact H1. *)
(*   simpl. *)
(*   reflexivity. *)
  
(*   intros. *)
(*   simpl. *)

(*   simpl in H. *)
(*   elim H. *)
(*   intros. *)
(*   elim H0. *)
(*   intros. *)
(*   split. *)
(*   apply IHt1. *)
(*   split. *)
(*   exact H2. *)
(*   exact H1. *)
(*   apply IHt2. *)
(*   split. *)
(*   exact H3. *)
(*   exact H1. *)
  (* induction u. *)
  
  (* simpl. *)
  (* intros. *)
  (* apply IHt.  *)
  (* elim H. *)
  (* intros. *)
  (* split. *)
  (* exact H0. *)
  (* simpl. *)
  (* SearchPattern ( _ < S _ ). *)
  (* apply lt_S. *)
  (* exact H1. *)
  
  (* intros. *)
  (* simpl. *)
  (* apply IHt. *)
  (* split. *)
  (* elim H. *)
  (* intros. *)
  (* simpl in *. *)
  (* exact H0. *)
  (* elim H. *)
  (* intros. *)
  (* simpl in *. *)
  (* reflexivity. *)

  (* simpl in *. *)
  (* intros. *)
  (* apply IHt.   *)
  (* split. *)
  (* elim H. *)
  (* intros. *)
  (* exact H0. *)
  (* simpl. *)
  (* split. *)
  (* elim H. *)
  (* simpl in *. *)
  (* intros.   *)
  (* elim H1. *)
  (* intros. *)
  Admitted.



Lemma subst_open_var : 
  forall (x:var) (y:var) (u:trm) (t:trm), forall (k:nat),
    x <> y -> locally_closed_at_rec k u -> subst x u (open_rec k x t) = open_rec k y (subst x u t).
Proof. 
  Admitted.





Lemma subst_close_var : 
  forall (x:var) (y:var) (u:trm) (t:trm), forall (k:nat),
    x <> y -> fresh k u -> subst x u (close_var_rec k x t) = close_var_rec k y (subst x u t).
Proof. 
  Admitted.


