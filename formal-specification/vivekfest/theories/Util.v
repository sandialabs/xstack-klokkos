(******************************************************************************)
(*                            DECIDABLE EQUALITY                              *)
(******************************************************************************)
Class EqDec (A : Type) :=
  { eqb : A -> A -> bool 
  ; eqb_refl : forall x, eqb x x = true
  ; eqb_leibniz : forall x y, eqb x y = true -> x = y
  ; eqb_false : forall x y, eqb x y = false -> x <> y }.

Lemma nat_eqb_leibniz : forall x y, Nat.eqb x y = true -> x = y.
Proof.
  intro x. induction x; intro y; induction y; intros; simpl in *; auto;
    try (inversion H).
Qed.

Lemma nat_eqb_refl : forall x, Nat.eqb x x = true.
Proof.
  intros. induction x; simpl; auto.
Qed.

Lemma nat_eqb_false : forall x y, Nat.eqb x y = false -> x <> y.
Proof.
  intros. induction x.
  - intro. induction y.
    + rewrite nat_eqb_refl in H. inversion H.
    + inversion H0.
  - intro. rewrite <- H0 in H. simpl in H. rewrite nat_eqb_refl in H.
    inversion H.
Qed.

Instance nat_EqDec : EqDec nat :=
  { eqb := Nat.eqb
  ; eqb_refl := nat_eqb_refl
  ; eqb_leibniz := nat_eqb_leibniz 
  ; eqb_false := nat_eqb_false }.

Notation "x <- M ;; N" :=
  (match M with
   | None => None
   | Some x => N
   end)
    (right associativity, at level 84, M at next level).


(******************************************************************************)
(*                                ENSEMBLES                                   *)
(******************************************************************************)
Definition Ensemble (ElemTy : Type) := ElemTy -> Prop.

Section EnsembleSection.

Context {ElemTy : Type}.

(* Constructing Ensembles *)
Definition In (A : Ensemble ElemTy) (x : ElemTy) : Prop := A x.
Definition Empty_Ensemble : Ensemble ElemTy := fun x => False.
Inductive Singleton (x : ElemTy) : Ensemble ElemTy :=
  In_singleton : In (Singleton x) x.
Definition Union (A B : Ensemble ElemTy) : Ensemble ElemTy :=
  fun x => In A x \/ In B x.
Definition Add (B : Ensemble ElemTy) (x : ElemTy) : Ensemble ElemTy :=
  Union B (Singleton x).
Definition Intersection (A B : Ensemble ElemTy) : Ensemble ElemTy :=
  fun x => In A x /\ In B x.
Definition Setminus (B C : Ensemble ElemTy) : Ensemble ElemTy :=
  fun x => In B x /\ ~ In C x.
Definition Subtract (B : Ensemble ElemTy) (x : ElemTy) : Ensemble ElemTy :=
  Setminus B (Singleton x).
Definition Included (B C : Ensemble ElemTy) : Prop :=
  forall x, In B x -> In C x.
Definition Disjoint (B C : Ensemble ElemTy) : Prop :=
  forall x, ~ In (Intersection B C) x.
Definition Equal (B C : Ensemble ElemTy) : Prop :=
  Included B C /\ Included C B.

Fixpoint list_to_ensemble (xs : list ElemTy) : Ensemble ElemTy :=
  match xs with
  | nil => Empty_Ensemble
  | cons x xs' => Add (list_to_ensemble xs') x
  end.

End EnsembleSection.

Ltac union_try :=
  match goal with
  | H : ?P |- ?P => exact H
  | |- In (Union _ _) _ => unfold In; unfold Union; left; union_try
  | |- In (Union _ _) _ => unfold In; unfold Union; right; union_try
  | |- forall x, _ => intro; union_try
  | |- _ -> _ => intro; union_try
  end.

Ltac auto_ensemble :=
  repeat
    match goal with
    | [ H : ?P |- ?P ] => exact P

    | [ H : In (Intersection _ _) _ |- _ ] =>
        unfold In in H;
        unfold Intersection in H;
        destruct H
    | [ H : In (Union _ _) _ |- _ ] =>
        unfold In in H;
        unfold Union in H;
        destruct H
    | [ H : Included _ _ |- _ ] => unfold Included in H
    | [ H : Disjoint _ _ |- _ ] => unfold Included in H
    | [ H : Equal _ _ |- _ ] =>
        unfold Equal;
        destruct H as [[X Y]]
    | [ H : In Empty_set _ |- _ ] => unfold In in H; intuition

    | [ |- Included _ _ ] => unfold Included
    | [ |- Disjoint _ _ ] => unfold Disjoint; intros
    | [ |- Equal _ _ ] => unfold Equal; constructor
    | [ |- In (Intersection _ _) _] => unfold In; unfold Intersection; intros; split
    | [ |- In (Union ?A _) ?x ] => union_try

    | [ |- forall x, _ ] => intro
    | [ |- _ -> _ ] => intro
    | [ |- ~ _ ] => intro
    | [ H0 : forall x, In ?A x -> _, H1 : In ?A ?X |- _ ] =>
        specialize (H0 X H1)
    | [ H : context[~ In ?A _] |- False ] =>
        eapply H; auto_ensemble; eauto
    end;
  try assumption.

Lemma union_com : forall ElemTy A B (x : ElemTy), In (Union A B) x -> In (Union B A) x.
  auto_ensemble.
Qed.

Lemma intersection_com : forall ElemTy A B (x : ElemTy),
    In (Intersection A B) x -> In (Intersection B A) x.
  auto_ensemble.
Qed.

Lemma included_refl : forall ElemTy A, Included (ElemTy := ElemTy) A A.
  auto_ensemble.
Qed.

Lemma included_trans : forall ElemTy A B C,
  Included (ElemTy := ElemTy) A B -> Included B C -> Included A C.
  auto_ensemble.
Qed.

Lemma disjoint_com : forall ElemTy A B,
  Disjoint (ElemTy := ElemTy) A B -> Disjoint B A.
  auto_ensemble. unfold Disjoint. intros. unfold Disjoint in H.
  specialize (H x). intro. apply intersection_com in H0. exact (H H0).
Qed.

Lemma equal_refl : forall ElemTy A, Equal (ElemTy := ElemTy) A A.
  auto_ensemble.
Qed.

Lemma equal_sym : forall ElemTy A B, Equal (ElemTy := ElemTy) A B -> Equal B A.
  auto_ensemble; unfold Equal in H; destruct H; auto_ensemble.
Qed.

Lemma equal_trans : forall ElemTy A B C,
  Equal (ElemTy := ElemTy) A B -> Equal A C -> Equal A C.
  auto_ensemble; unfold Equal in H,H0; destruct H, H0; auto_ensemble.
Qed.

Lemma union_not_in : forall ElemTy A B (x : ElemTy),
  ~ In (Union A B) x -> ~ In A x /\ ~ In B x.
  constructor; auto_ensemble.
Qed.

Lemma disjoint_union : forall ElemTy A B C,
  Disjoint (ElemTy := ElemTy) (Union A B) C ->  Disjoint A C /\ Disjoint B C.
  auto_ensemble. unfold Disjoint in *. split; intros; intro; specialize (H x);
  assert (In (Intersection (Union A B) C) x). unfold In. unfold Intersection.
  split. left. unfold In in H0. unfold Intersection in H0. destruct H0.
  assumption. unfold In in H0. unfold Intersection in H0. destruct H0.
  assumption. exact (H H1). unfold In. unfold Intersection. split. right.
  unfold In in H0. unfold Intersection in H0. destruct H0. assumption.
  unfold In in H0. unfold Intersection in H0. destruct H0. assumption.
  exact (H H1).
Qed.

Lemma same_set_union_right : forall ElemTy A B C,
  Equal (ElemTy := ElemTy) A B -> Equal (Union C A) (Union C B).
  intros. unfold Equal in *. destruct H. unfold Included in *. split.
  intros. unfold In. unfold Union. destruct H1. left; assumption.
  pose proof (H x H1). right; assumption. intros. destruct H1.
  left; assumption. right. exact (H0 x H1).
Qed.

Lemma same_set_union_left : forall ElemTy A B C,
  Equal (ElemTy := ElemTy) A B -> Equal (Union A C) (Union B C).
  intros. unfold Equal in *. destruct H. unfold Included in *. split.
  intros. unfold In. unfold Union. destruct H1. left. exact (H x H1).
  right; assumption. intros. destruct H1. left. exact (H0 x H1).
  right; assumption.
Qed.

Lemma empty_included_all : forall ElemTy A,
  Included (ElemTy := ElemTy) Empty_Ensemble A.
  auto_ensemble. unfold In in H. unfold Empty_Ensemble in H. contradiction.
Qed.

Lemma included_empty_false : forall ElemTy A (x : ElemTy),
    In A x ->
    Included A Empty_Ensemble ->
    False.
  auto_ensemble.
Qed.

Lemma union_empty_set : forall ElemTy A (x : ElemTy),
    In (Union Empty_Ensemble A) x -> In A x.
  auto_ensemble. apply included_empty_false in H. contradiction.
  apply empty_included_all.
Qed.

Lemma intersection_sym : forall ElemTy A B (x : ElemTy),
  In (Intersection A B) x -> In (Intersection B A) x.
  auto_ensemble.
Qed.

Lemma intersection_self : forall ElemTy A (x : ElemTy),
    In A x -> In (Intersection A A) x.
  auto_ensemble.
Qed.

(******************************************************************************)
(*                                   MAPS                                     *)
(******************************************************************************)

Record Map (A B : Type) := { get : A -> option B }.
Notation "M #[ x ]" := (get _ _ M x) (at level 70).

Definition empty_Map {A B : Type} : Map A B := {| get := fun _ => None |}.
Definition update {A B : Type} {_ : EqDec A} (M : Map A B) (x : A) (v : B) : Map A B :=
  {| get := fun y => if eqb x y then Some v else M#[y]
  |}.
Notation "M [ x |-> v ]" := (update M x v) (at level 70).

Definition bar : Map nat nat := empty_Map.
Definition bar1 : Map nat nat := bar[0 |-> 42].
Lemma bar1_test : bar1[0 |-> 43]#[0] = Some 43.
Proof.
  unfold update. simpl. reflexivity.
Qed.
Lemma bar1_test1 : bar1[0 |-> 43]#[0] <> Some 42.
  unfold update. simpl. congruence.
Qed.

Definition update2 {A B C : Type} {_ : EqDec A} {_ : EqDec B}
  (M : Map A (Map B C)) (x : A) (y : B) (z : C)
  : Map A (Map B C) :=
  {| get := 
      fun x' => 
        if eqb x' x
        then match M#[x'] with
             | Some M' => Some (M'[y |-> z])
             | None => Some (empty_Map[y |-> z])
             end
        else M#[x']
  |}.
Notation "M [ x , y |-> v ]" := (update2 M x y v) (at level 70).
Notation "M #[ x , y ]" := (M' <- M#[x] ;; M'#[y]) (at level 70).

Definition bar_nest : Map nat (Map nat nat) := empty_Map.
Definition bar_nest1 := bar_nest[0 |-> empty_Map].
Definition bar_nest2 := bar_nest[0,0 |-> 1].
Lemma bar_nest_test : bar_nest2#[0, 0] = Some 1.
Proof.
  auto.
Qed.

Definition update3 {A B C D : Type} {_ : EqDec A} {_ : EqDec B} {_ : EqDec C}
  (M : Map A (Map B (Map C D))) (w : A) (x : B) (y : C) (z : D)
  : Map A (Map B (Map C D)) :=
  {| get := 
      fun w' => 
        if eqb w' w
        then match M#[w'] with
             | Some M' => Some (M'[x,y |-> z])
             | None => Some (empty_Map[x,y |-> z])
             end
        else M#[w']
  |}.

Notation "M [ x , y , z |-> v ]" := (update3 M x y z v) (at level 70).
Notation "M #[ x , y , z ]" := (M' <- M#[x] ;; M'#[y,z]) (at level 70).

Require Import Coq.Lists.ListSet.

Definition restrict {A B : Type} {_ : EqDec A}
  (M : Map A B)
  (Pdec : A -> bool)
  : Map A B :=
  {| get := fun a => if Pdec a then M#[a] else None
  |}.

Definition join {A B : Type} {_ : EqDec A}
  (M N : Map A B)
  : Map A B :=
  {| get := fun a =>
              match M#[a] with
              | None => N#[a]
              | Some b => Some b
              end
  |}.

(******************************************************************************)
(*                          FIRST-IN-FIRST-OUT QUEUE                          *)
(******************************************************************************)
Module Type FifoType.
  Parameter Fifo : Type -> Type.
  Parameter empty_Fifo : forall {A}, Fifo A.
  Parameter peek : forall [A], Fifo A -> option A.
  Parameter pop : forall [A], Fifo A -> Fifo A.
  Parameter push : forall [A], Fifo A -> A -> Fifo A.
  Parameter peek_empty_Fifo : forall {A}, peek (empty_Fifo (A := A)) = None.
  Parameter dec_empty_Fifo : forall {A} (ff : Fifo A), {ff = empty_Fifo} + {ff <> empty_Fifo}.
  Parameter peek_empty_None_only : forall {A} (ff : Fifo A), peek ff = None -> ff = empty_Fifo.
  Parameter Forall_Fifo : forall [A] (P : A -> Prop), Fifo A -> Prop.
  Parameter Forall_Fifo_pop : forall [A] (P : A -> Prop) (ff : Fifo A),
      Forall_Fifo P ff -> Forall_Fifo P (pop ff).
  Parameter Forall_Fifo_peek : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> peek ff = Some a -> P a.
  Parameter Forall_Fifo_push : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> P a -> Forall_Fifo P (push ff a).
  Parameter Forall_Fifo_weaken : forall [A] (P Q : A -> Prop) (ff : Fifo A),
      Forall_Fifo P ff -> (forall a, P a -> Q a) -> Forall_Fifo Q ff. 
  Parameter Forall_Fifo_empty_Fifo : forall [A] (P : A -> Prop),
      Forall_Fifo P empty_Fifo.
  Parameter Forall_Fifo_replaceh : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> P a -> Forall_Fifo P (push (pop ff) a). 
End FifoType.

Module FifoList <: FifoType.
  Definition Fifo := list.
  Definition empty_Fifo {A : Type} := nil (A := A).
  Definition peek [A : Type] (ff : list A) : option A :=
    match ff with
    | nil => None
    | cons x _ => Some x
    end.
  Fixpoint pop [A : Type] (ff : list A) : list A :=
    match ff with
    | nil => nil
    | cons x nil => nil
    | cons x ff' => cons x (pop ff')
    end.
  Definition push [A : Type] (ff : list A) (x : A) : list A :=
    cons x ff.

  Lemma peek_empty_Fifo : forall {A}, peek (empty_Fifo (A := A)) = None.
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Lemma dec_empty_Fifo : forall {A} (ff : Fifo A), {ff = empty_Fifo} + {ff <> empty_Fifo}.
  Proof.
    intros. destruct ff; simpl; unfold empty_Fifo.
    - left. reflexivity.
    - right. intro. inversion H.
  Qed.

  Lemma peek_empty_None_only : forall {A} (ff : Fifo A), peek ff = None -> ff = empty_Fifo.
  Proof.
    intros. induction ff; simpl in *; auto. inversion H.
  Qed.

  Fixpoint Forall_Fifo [A : Type] (P : A -> Prop) (ff : Fifo A) : Prop :=
    match ff with
    | nil => True
    | cons x ff' => P x /\ Forall_Fifo P ff'
    end.

  Lemma Forall_Fifo_pop : forall [A] (P : A -> Prop) (ff : Fifo A),
      Forall_Fifo P ff -> Forall_Fifo P (pop ff).
  Proof.
    intros. induction ff; auto.
    simpl in H. destruct H. specialize (IHff H0). simpl. destruct ff; simpl; auto.
  Qed.

  Lemma Forall_Fifo_peek : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> peek ff = Some a -> P a.
  Proof.
    intros. destruct ff; simpl in *.
    - inversion H0.
    - inversion H0. subst. destruct H. assumption.
  Qed.

  Lemma Forall_Fifo_push : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> P a -> Forall_Fifo P (push ff a).
  Proof.
    intros. simpl. split; auto.
  Qed.

  Lemma Forall_Fifo_weaken : forall [A] (P Q : A -> Prop) (ff : Fifo A),
      Forall_Fifo P ff -> (forall a, P a -> Q a) -> Forall_Fifo Q ff. 
  Proof.
    intros. induction ff; simpl; auto.
    split.
    - simpl in H. destruct H. apply H0. apply H.
    - apply IHff. destruct H. assumption.
  Qed.

  Lemma Forall_Fifo_empty_Fifo : forall [A] (P : A -> Prop),
      Forall_Fifo P empty_Fifo.
  Proof.
    intros. simpl. constructor.
  Qed.

  Lemma Forall_Fifo_replaceh : forall [A] (P : A -> Prop) (ff : Fifo A) (a : A),
      Forall_Fifo P ff -> P a -> Forall_Fifo P (push (pop ff) a). 
  Proof.
    intros. simpl. split; auto. apply Forall_Fifo_pop. assumption.
  Qed.
End FifoList.

(******************************************************************************)
(*                                 NAMES                                      *)
(******************************************************************************)
Module Type NameType.
  Parameter name : Set.
  Parameter eqb_name : name -> name -> bool.
  Parameter name_eq_dec : forall (n m : name), {n = m} + {n <> m}.
  Parameter eqb_name_refl : forall (n : name), eqb_name n n = true.
  Parameter eqb_name_true : forall (n m : name), eqb_name n m = true -> n = m.
  Parameter eqb_name_false : forall (n m : name), eqb_name n m = false -> n <> m.

  Instance name_EqDec : EqDec name :=
    { eqb := eqb_name
    ; eqb_refl := eqb_name_refl
    ; eqb_leibniz := eqb_name_true 
    ; eqb_false := eqb_name_false }.
End NameType.
