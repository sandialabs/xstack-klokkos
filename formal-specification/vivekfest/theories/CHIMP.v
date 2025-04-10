Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Lists.ListSet.
Require Import Lia.
Require Import CHIMP.Util.
Declare Module Import Name : NameType.
Declare Module Import Fifo : FifoType.

(******************************************************************************)
(*                       EXECUTORS, SPACES, & FRAMES                          *)
(******************************************************************************)
Variant executor (BX : Set) : Set :=
  | XBase : BX -> executor BX
  | XVar  : name -> executor BX.

Definition Closed_executor {BX : Set} (X : executor BX) : Prop :=
  match X with
  | XBase _ _ => True
  | XVar _ _  => False
  end.

Definition subst_executor {BX : Set} (X : executor BX) (M : Map name BX) : executor BX :=
  match X with
  | XBase _ bx => XBase _ bx
  | XVar _ x  =>
      match M#[x] with
      | Some bx => XBase _ bx
      | None    => XVar _ x
      end
  end.

Variant MemSpace (BMs : Set) := 
  | MsBase : BMs -> MemSpace BMs
  | MsVar  : name -> MemSpace BMs.

Definition Closed_MemSpace {BMs : Set} (S : MemSpace BMs) : Prop :=
  match S with
  | MsBase _ _ => True
  | MsVar _ _  => False
  end.

Definition subst_MemSpace {BMs : Set} (S : MemSpace BMs) (M : Map name BMs) : MemSpace BMs :=
  match S with
  | MsBase _ bm => MsBase _ bm
  | MsVar _ s  =>
      match M#[s] with
      | Some bm => MsBase _ bm
      | None    => MsVar _ s
      end
  end.

Record Frame :=
  { BX : Set
  ; BX0 : BX
  ; BX_EqDec : EqDec BX
  ; BX_elems : list BX
  ; BX_elems_full : forall bx, List.In bx BX_elems
  ; BMs : Set
  ; BMs_EqDec : EqDec BMs
  ; BMs_elems : list BMs
  ; BMs_elems_full : forall bms, List.In bms BMs_elems
  ; comp_acc_rel : BX -> BMs -> bool
  ; Bt : Set -> Prop
  ; Bt_nat : Bt nat
  (* TODO *)
  (* ; Bt_op : forall (A : Set), Bt A -> (A -> A -> A) -> Prop *)
  }.

(* These are the example executors and memory spaces found in the Vivekfest paper. *)
Variant Vivekfest_Baseexecutor : Set :=
  | BExHost    : Vivekfest_Baseexecutor
  | BExThreads : Vivekfest_Baseexecutor
  | BExOpenMP  : Vivekfest_Baseexecutor
  | BExCuda    : Vivekfest_Baseexecutor.

Definition BX_elems_Vivekfest :=
  cons BExHost (cons BExThreads (cons BExOpenMP (cons BExCuda nil))).

Lemma Vivekfest_BX_elems_full : forall bx, List.In bx BX_elems_Vivekfest.
Proof.
  intros. destruct bx; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. left. reflexivity.
Qed.

Definition eqb_Vivekfest_Baseexecutor x y :=
  match x,y with
  | BExHost,BExHost => true
  | BExThreads,BExThreads => true
  | BExOpenMP,BExOpenMP => true
  | BExCuda,BExCuda => true
  | _,_ => false
  end.

Lemma eqb_Vivekfest_Baseexecutor_true : forall x y,
    eqb_Vivekfest_Baseexecutor x y = true -> x = y.
Proof.
  intros. destruct x,y; simpl in *; auto; try (inversion H).
Qed.

Lemma eqb_Vivekfest_Baseexecutor_refl : forall x,
    eqb_Vivekfest_Baseexecutor x x = true.
Proof.
  intros. destruct x; simpl in *; auto.
Qed.

Lemma eqb_Vivekfest_Baseexecutor_false : forall x y,
    eqb_Vivekfest_Baseexecutor x y = false -> x <> y.
Proof.
  intros. destruct x,y; simpl in *; auto; try (inversion H); intro; try (inversion H0).
Qed.

Instance Vivekfest_Baseexecutor_EqDec : EqDec Vivekfest_Baseexecutor :=
  { eqb := eqb_Vivekfest_Baseexecutor
  ; eqb_refl := eqb_Vivekfest_Baseexecutor_refl
  ; eqb_leibniz := eqb_Vivekfest_Baseexecutor_true
  ; eqb_false := eqb_Vivekfest_Baseexecutor_false }.


Variant Vivekfest_BaseMemSpace : Set :=
  | BMsHost    : Vivekfest_BaseMemSpace
  | BMsCudaUVM : Vivekfest_BaseMemSpace
  | BMsCuda    : Vivekfest_BaseMemSpace.

Definition eqb_Vivekfest_BaseMemSpace x y :=
  match x,y with
  | BMsHost,BMsHost => true
  | BMsCudaUVM,BMsCudaUVM => true
  | BMsCuda,BMsCuda => true
  | _,_ => false
  end.

Lemma eqb_Vivekfest_BaseMemSpace_true : forall x y,
    eqb_Vivekfest_BaseMemSpace x y = true -> x = y.
Proof.
  intros. destruct x,y; simpl in *; auto; try (inversion H).
Qed.

Lemma eqb_Vivekfest_BaseMemSpace_refl : forall x,
    eqb_Vivekfest_BaseMemSpace x x = true.
Proof.
  intros. destruct x; simpl in *; auto.
Qed.

Lemma eqb_Vivekfest_BaseMemSpace_false : forall x y,
    eqb_Vivekfest_BaseMemSpace x y = false -> x <> y.
Proof.
  intros. destruct x,y; simpl in *; auto; try (inversion H); intro; try (inversion H0).
Qed.

Instance Vivekfest_BaseMemSpace_EqDec : EqDec Vivekfest_BaseMemSpace :=
  { eqb := eqb_Vivekfest_BaseMemSpace
  ; eqb_refl := eqb_Vivekfest_BaseMemSpace_refl
  ; eqb_leibniz := eqb_Vivekfest_BaseMemSpace_true
  ; eqb_false := eqb_Vivekfest_BaseMemSpace_false }.

Definition BMs_elems_Vivekfest :=
  cons BMsHost (cons BMsCudaUVM (cons BMsCuda nil)).

Lemma Vivekfest_BMs_elems_full : forall bms, List.In bms BMs_elems_Vivekfest.
Proof.
  intros. destruct bms; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
Qed.

Definition Vivekfest_comp_acc_rel : Vivekfest_Baseexecutor ->  Vivekfest_BaseMemSpace -> bool :=
  fun X S =>
    match S,X with
    | BMsHost,BExHost    => true
    | BMsHost,BExThreads => true
    | BMsHost,BExOpenMP  => true
    | BMsCuda,BExCuda    => true
    | BMsCudaUVM,_       => true
    | _,_ => false
    end.

Definition Vivekfest_Frame : Frame
  :=
  {| BX := Vivekfest_Baseexecutor
  ; BX0 := BExHost
  ; BX_elems := BX_elems_Vivekfest
  ; BX_elems_full := Vivekfest_BX_elems_full
  ; BMs := Vivekfest_BaseMemSpace
  ; BMs_elems := BMs_elems_Vivekfest
  ; BMs_elems_full := Vivekfest_BMs_elems_full
  ; comp_acc_rel := Vivekfest_comp_acc_rel
  ; Bt := fun B => B = nat
  ; Bt_nat := eq_refl
  |}.

Section FRAME_CONTEXT.
  Context (F : Frame).
  Definition XInstantiation := Map name (BX F).
  Definition MsInstantiation := Map name (BMs F).

  (****************************************************************************)
  (*                                 SYNTAX                                   *)
  (****************************************************************************)
  Inductive Expr : Type :=
  | EVar : name -> Expr
  | EAccess : name -> Expr -> Expr
  | EConst : forall bty, Bt F bty -> forall (c : bty), Expr
  | EOp : Expr -> Expr -> Expr.

  Fixpoint FV_Expr (E : Expr) : Ensemble name :=
    match E with
    | EVar v => Singleton v
    | EAccess v E0 => Union (Singleton v) (FV_Expr E0)
    | EConst _ _ _ => Empty_Ensemble
    | EOp E0 E1 => Union (FV_Expr E0) (FV_Expr E1)
    end.
  
  (* TODO Add while-loops *)
  Inductive Cmd : Type :=
  | CSetVar : name -> Expr -> Cmd
  | CSetView : name -> Expr -> Expr -> Cmd
  | CFence : executor (BX F) -> Cmd
  | CDeepCopy : Expr -> Expr -> Cmd
  | CKernel : executor (BX F) -> list name -> Stmt -> Cmd
  with Stmt : Type :=
  | SCom : Cmd -> Stmt -> Stmt
  | SRet : Stmt
  | SDeclVar : name -> Expr -> Stmt -> Stmt
  | SDeclView : name -> MemSpace (BMs F) -> Expr -> Stmt -> Stmt.
  (* TODO : Had to add a default initionalizer to declaring a view. *)

  Scheme Cmd_Stmt_ind := Induction for Cmd Sort Prop
      with Stmt_Cmd_ind := Induction for Stmt Sort Prop.

  Fixpoint FV_Cmd (C : Cmd) : Ensemble name :=
    match C with
    | CSetVar x E => Union (Singleton x) (FV_Expr E)
    | CSetView x E0 E1 => Union (Singleton x) (Union (FV_Expr E0) (FV_Expr E1))
    | CFence _ => Empty_Ensemble
    | CDeepCopy E0 E1 => Union (FV_Expr E0) (FV_Expr E1)
    | CKernel _ binds S0 => Union (list_to_ensemble binds) (FV_Stmt S0)
    end
    with FV_Stmt (S : Stmt) : Ensemble name :=
           match S with
           | SCom C S0 => Union (FV_Cmd C) (FV_Stmt S0)
           | SRet => Empty_Ensemble
           | SDeclVar x E S0 => Union (FV_Expr E) (Subtract (FV_Stmt S0) x)
           | SDeclView x _ E S0 => Union (FV_Expr E) (Subtract (FV_Stmt S0) x)
           end.

  Fixpoint Based_Cmd (C : Cmd) : Prop :=
    match C with
    | CKernel (XBase _ _) _ S' => Based_Stmt S'
    | CKernel (XVar _ x) _ _ => False
    | CFence (XVar _ x) => False
    | _ => True
    end
    with Based_Stmt (S : Stmt) : Prop :=
           match S with
           | SCom C S' => Based_Cmd C /\ Based_Stmt S'
           | SRet => True
           | SDeclVar _ _ S' => Based_Stmt S'
           | SDeclView _ (MsBase _ _) _ S' => Based_Stmt S'
           | SDeclView _ (MsVar _ _) _ _ => False
           end.

  Fixpoint FX_Cmd (C : Cmd) : Ensemble name :=
    match C with
    | CKernel (XBase _ _) _ S0 => FX_Stmt S0
    | CKernel (XVar _ x) _ S0 => Union (Singleton x) (FX_Stmt S0)
    | CFence (XVar _ x) => Singleton x
    | _ => Empty_Ensemble
    end
    with FX_Stmt (S : Stmt) : Ensemble name :=
           match S with
           | SCom C S0 => Union (FX_Cmd C) (FX_Stmt S0)
           | SRet => Empty_Ensemble
           | SDeclVar _ _ S0 => FX_Stmt S0
           | SDeclView _ _ _ S0 => FX_Stmt S0
           end.

  Fixpoint FMs_Cmd (C : Cmd) : Ensemble name :=
    match C with
    | CKernel _ _ S0 => FMs_Stmt S0
    | _ => Empty_Ensemble
    end
    with FMs_Stmt (S : Stmt) : Ensemble name :=
           match S with
           | SCom C S0 => Union (FMs_Cmd C) (FMs_Stmt S0)
           | SRet => Empty_Ensemble
           | SDeclVar _ _ S0 => FMs_Stmt S0
           | SDeclView _ (MsBase _ _) _ S0 => FMs_Stmt S0
           | SDeclView _ (MsVar _ v) _ S0 => Union (Singleton v) (FMs_Stmt S0)
           end.

  Fixpoint XInstantiate_Cmd (C : Cmd) (IX : XInstantiation) : Cmd :=
    match C with
    | CSetVar x E => CSetVar x E
    | CSetView x E0 E1 => CSetView x E0 E1
    | CFence X => CFence (subst_executor X IX)
    | CDeepCopy E0 E1 => CDeepCopy E0 E1
    | CKernel X xs S' => CKernel (subst_executor X IX) xs (XInstantiate_Stmt S' IX)
    end
    with XInstantiate_Stmt (S : Stmt) (IX : XInstantiation) : Stmt :=
           match S with
           | SCom C S' => SCom (XInstantiate_Cmd C IX) (XInstantiate_Stmt S' IX)
           | SRet => SRet
           | SDeclVar x E S' => SDeclVar x E (XInstantiate_Stmt S' IX)
           | SDeclView x Ms E S' => SDeclView x Ms E (XInstantiate_Stmt S' IX)
           end.

  Fixpoint MsInstantiate_Cmd (C : Cmd) (IMs : MsInstantiation) : Cmd :=
    match C with
    | CSetVar x E => CSetVar x E
    | CSetView x E0 E1 => CSetView x E0 E1
    | CFence X => CFence X
    | CDeepCopy E0 E1 => CDeepCopy E0 E1
    | CKernel X xs S' => CKernel X xs (MsInstantiate_Stmt S' IMs)
    end
    with MsInstantiate_Stmt (S : Stmt) (IMs : MsInstantiation) : Stmt :=
           match S with
           | SCom C S' => SCom (MsInstantiate_Cmd C IMs) (MsInstantiate_Stmt S' IMs)
           | SRet => SRet
           | SDeclVar x E S' => SDeclVar x E (MsInstantiate_Stmt S' IMs)
           | SDeclView x Ms E S' => SDeclView x (subst_MemSpace Ms IMs) E (MsInstantiate_Stmt S' IMs)
           end.

  Lemma Instantiate_Stmt_Based : forall IX IMs (S : Stmt),
    (forall (x : name), In (FX_Stmt S) x -> exists bx, IX#[x] = Some bx) ->
    (forall (x : name), In (FMs_Stmt S) x -> exists bms, IMs#[x] = Some bms) ->
    Based_Stmt (MsInstantiate_Stmt (XInstantiate_Stmt S IX) IMs).
  Proof using Type.
    intros IX IMs.
    apply (Stmt_Cmd_ind 
                  (fun C => (forall (x : name), In (FX_Cmd C) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
                            (forall (x : name), In (FMs_Cmd C) x -> exists bms, IMs#[x] = Some bms) ->
                            Based_Cmd (MsInstantiate_Cmd (XInstantiate_Cmd C IX) IMs))
                  (fun S => (forall (x : name), In (FX_Stmt S) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
                            (forall (x : name), In (FMs_Stmt S) x -> exists bms, IMs#[x] = Some bms) ->
                            Based_Stmt (MsInstantiate_Stmt (XInstantiate_Stmt S IX) IMs)));
      intros; simpl; auto.
    - destruct e; simpl in *; auto.
      assert (In (Singleton n) n) by constructor.
      destruct (H n H1). rewrite H2. constructor.
    - destruct e; simpl in *; auto.
      assert (In (Union (Singleton n) (FX_Stmt s)) n) by (left; constructor).
      destruct (H0 n H2). rewrite H3. apply H; intros y H4;
        [apply H0; right| apply H1]; assumption.
    - split; [apply H | apply H0]; intros.
      + apply H1. simpl. left. assumption.
      + apply H2. simpl. left. assumption.
      + apply H1. right. assumption.
      + apply H2. right. assumption.
    - destruct m; simpl in *; auto.
      assert (In (Union (Singleton n0) (FMs_Stmt s)) n0) by (left; constructor).
      destruct (H1 n0 H2) as [bms]. rewrite H3.
      apply H; intros; [apply H0; assumption|apply H1; right; assumption].
  Qed.

  (****************************************************************************)
  (*                                 TYPING                                   *)
  (****************************************************************************)
  Inductive Typ : Type :=
  | Base : forall bty, Bt F bty -> Typ
  | View : MemSpace (BMs F) -> forall bty, Bt F bty -> Typ.

  Definition FMs_Typ (typ : Typ) : Ensemble name :=
    match typ with
    | View (MsVar _ m) _ _ => Singleton m
    | _ => Empty_Ensemble
    end.

  Definition Based_Typ (typ : Typ) : Prop :=
    match typ with
    | View (MsVar _ v) _ _ => False
    | _ => True
    end.

  Definition MsInstantiate_Typ (t : Typ) (IMs : MsInstantiation) : Typ :=
    match t with
    | Base bty btyP => Base bty btyP
    | View M bty btyP => View (subst_MemSpace M IMs) bty btyP
    end.

  Inductive context : Type :=
  | empty    : context
  | cons_ex  : name -> context -> context
  | cons_mem : name -> context -> context
  | cons_var : name -> Typ -> context -> context.
  
  Fixpoint In_context_ex (G : context) (x : name) : Prop :=
    match G with
    | empty => False
    | cons_ex y G' => x = y \/ In_context_ex G' x
    | cons_mem _ G' => In_context_ex G' x
    | cons_var _ _ G' => In_context_ex G' x
    end.

  Fixpoint In_context_mem (G : context) (x : name) : Prop :=
    match G with
    | empty => False
    | cons_ex _ G' => In_context_mem G' x
    | cons_mem y G' => x = y \/ In_context_mem G' x
    | cons_var _ _ G' => In_context_mem G' x
    end.

  Fixpoint In_context_var (G : context) (x : name) (typ : Typ) : Prop :=
    match G with
    | empty => False
    | cons_ex _ G' => In_context_var G' x typ
    | cons_mem _ G' => In_context_var G' x typ
    | cons_var y typ' G' => 
        (x = y /\ typ = typ') \/ (x <> y /\ In_context_var G' x typ)
    end.

  Definition context_less (G G' : context) : Prop :=
    (forall x, In_context_ex G x -> In_context_ex G' x)
    /\ (forall m, In_context_mem G m -> In_context_mem G' m)
    /\ (forall x t, In_context_var G x t -> In_context_var G' x t).

  Lemma context_less_refl : forall G, context_less G G.
  Proof using Type.
    intros. split; [|split]; intros; auto.
  Qed.

  Lemma context_less_trans : forall G0 G1 G2,
      context_less G0 G1 ->
      context_less G1 G2 ->
      context_less G0 G2.
  Proof using Type.
    intros. destruct H as [H []]. destruct H0 as [H0 []].
    split; [| split]; intros.
    - apply H0. apply H. assumption.
    - apply H3. apply H1. assumption.
    - apply H4. apply H2. assumption.
  Qed.

  Lemma context_less_empty : forall G, context_less empty G.
  Proof using Type.
    intros. split; [| split]; intros; inversion H.
  Qed.

  Fixpoint lookup_context_var (G : context) (x : name) : option Typ :=
    match G with
    | empty => None
    | cons_ex _ G' => lookup_context_var G' x
    | cons_mem _ G' => lookup_context_var G' x
    | cons_var y typ G' => 
        if eqb_name x y then Some typ else lookup_context_var G' x
    end.

  Lemma context_less_ex_compat : forall G G' x,
      context_less G G' ->
      context_less (cons_ex x G) (cons_ex x G').
  Proof using Type.
    intros. split; [| split]; intros y; intros.
    - destruct H as [H _]. simpl in *. destruct H0.
      + left. assumption.
      + right. apply H. assumption.
    - destruct H as [_ [H _]]. simpl in *. apply H. assumption.
    - destruct H as [_ [_ H]]. simpl in *. apply H. assumption.
  Qed.

  Lemma context_less_mem_compat : forall G G' x,
      context_less G G' ->
      context_less (cons_mem x G) (cons_mem x G').
  Proof using Type.
    intros. split; [| split]; intros y; intros.
    - destruct H as [H _]. simpl in *. apply H. assumption.
    - destruct H as [_ [H _]]. simpl in *. destruct H0. 
      + left. assumption.
      + right. apply H. assumption.
    - destruct H as [_ [_ H]]. simpl in *. apply H. assumption.
  Qed.

  Lemma context_less_var_compat : forall G G' x t,
      context_less G G' ->
      context_less (cons_var x t G) (cons_var x t G').
  Proof using Type.
    intros. split; [| split]; intros y; intros.
    - destruct H as [H _]. simpl in *. apply H. assumption.
    - destruct H as [_ [H _]]. simpl in *. apply H. assumption.
    - destruct H as [_ [_ H]]. simpl in *. destruct H0. 
      + left. assumption.
      + right. destruct H0. split; auto. 
  Qed.

  Lemma In_context_var_lookup : forall G x typ,
      In_context_var G x typ <-> lookup_context_var G x = Some typ.
  Proof using Type.
    intros. induction G; simpl; auto.
    - split; intros; [contradiction|inversion H].
    - split; intros.
      + remember (eqb_name x n). destruct b.
        * simpl in H. destruct H.
          -- destruct H. subst. reflexivity.
          -- exfalso. destruct H. apply H. symmetry in Heqb. apply eqb_name_true in Heqb.
             assumption.
        * simpl in H. destruct H.
          -- exfalso. destruct H. subst. rewrite eqb_name_refl in Heqb. inversion Heqb.
          -- destruct H. apply IHG. assumption.
      + remember (eqb_name x n). destruct b.
        * left. inversion H. subst. symmetry in Heqb. apply eqb_name_true in Heqb.
          subst. split; auto.
        * right. symmetry in Heqb. apply eqb_name_false in Heqb.
          destruct IHG. specialize (H1 H). split; auto.
  Qed.

  Lemma Deterministic_context :
    forall G x t0 t1, In_context_var G x t0 -> In_context_var G x t1 -> t0 = t1.
  Proof using Type.
    intros. induction G; simpl in *; auto.
    - inversion H.
    - destruct H, H0; destruct H, H0.
      + subst. reflexivity.
      + subst. exfalso. apply H0. reflexivity.
      + subst. exfalso. apply H. reflexivity.
      + apply IHG; auto.
  Qed.

  Fixpoint Based_context (G : context) : Prop :=
    match G with
    | empty => True
    | cons_ex _ G' => False
    | cons_mem _ G' => False
    | cons_var _ typ' G' => Based_Typ typ' /\ Based_context G'
    end.

  Lemma Based_context_implies_Based_Typ : forall G x t, Based_context G -> In_context_var G x t -> Based_Typ t.
  Proof using Type.
    intros. induction G; simpl in *; try contradiction. 
    destruct H0.
    - destruct H0. subst. destruct H. assumption.
    - destruct H,H0. apply IHG; auto.
  Qed.

  Variant Wf_executor (G : context) : executor (BX F) -> Prop :=
    | Wf_executor_XBase : forall (X : BX F), Wf_executor G (XBase _ X)
    | Wf_executor_XVar  : forall (x : name),
        In_context_ex G x ->
        Wf_executor G (XVar _ x).
  
  Variant Wf_MemSpace (G : context) : MemSpace (BMs F) -> Prop :=
    | Wf_MemSpace_MsBase : forall (S : BMs F), Wf_MemSpace G (MsBase _ S)
    | Wf_MemSpace_MsVar  : forall (s : name),
        In_context_mem G s ->
        Wf_MemSpace G (MsVar _ s).

  (* Instantiating a context will remove all of the declared free executors and
  memory spaces. *)
  Fixpoint Instantiate_context (G : context) (IMs : MsInstantiation) : context :=
    match G with
    | empty => empty
    | cons_ex X G' => Instantiate_context G' IMs
    | cons_mem Ms G' => Instantiate_context G' IMs
    | cons_var x typ G' => cons_var x (MsInstantiate_Typ typ IMs) (Instantiate_context G' IMs)
    end.

  Lemma Instantiate_context_preserves_In_context_var : forall G IMs x t,
      In_context_var G x t ->
      In_context_var (Instantiate_context G IMs) x (MsInstantiate_Typ t IMs).
  Proof using Type.
    intros. induction G; simpl in *; auto.
    destruct H as [[]|[]]; subst; [left|right]; split; auto.
  Qed.

  Definition Accessible (G : context) (X : executor (BX F)) (Ms : MemSpace (BMs F)) : Prop :=
    Wf_executor G X 
    /\ Wf_MemSpace G Ms 
    /\ forall IX IMs,
        (forall x, X = XVar _ x -> exists bx, IX#[x] = Some bx) ->
        (forall m, Ms = MsVar _ m -> exists bms, IMs#[m] = Some bms) ->
          exists bx bms,
            XBase _ bx = subst_executor X IX 
            /\ MsBase _ bms = subst_MemSpace Ms IMs
            /\ comp_acc_rel F bx bms = true.
  
  Lemma Accessible_base : forall G bx bms,
      Accessible G (XBase (BX F) bx) (MsBase (BMs F) bms) ->
      comp_acc_rel F bx bms = true.
  Proof using Type. 
    intros. unfold Accessible in H.
    assert (forall x : name, In_context_ex G x -> exists bx0 : BX F, ({| get := fun _ : name => Some bx |} #[ x]) = Some bx0).
    { intros. exists bx. simpl. reflexivity. }
    assert (forall m : name, In_context_mem G m -> exists bms0 : BMs F, ({| get := fun _ : name => Some bms |} #[ m]) = Some bms0).
    { intros. exists bms. simpl. reflexivity. }
    destruct H as [H []].
    specialize (H3 {| get := fun _ => Some bx |} {| get := fun _ => Some bms |}).
    simpl in H3.
    assert (forall x : name,
                XBase (BX F) bx = XVar (BX F) x -> exists bx0 : BX F, Some bx = Some bx0)
      by (intros; inversion H4).
    assert (forall m : name,
        MsBase (BMs F) bms = MsVar (BMs F) m -> exists bms0 : BMs F, Some bms = Some bms0)
      by (intros; inversion H5).
    specialize (H3 H4 H5).
    destruct H3 as [bx0 [bms0 [H6 []]]]. inversion H6. inversion H3. subst. assumption.
  Qed.

  Inductive ExprTyping (G : context) : Expr -> Typ -> executor (BX F) -> Prop :=
  | TVar : forall x t X,
      In_context_var G x t ->
      ExprTyping G (EVar x) t X
  | TViewDeref : forall x E S bty btyP X,
      In_context_var G x (View S bty btyP) ->
      Accessible G X S ->
      ExprTyping G E (Base nat (Bt_nat F)) X ->
      ExprTyping G (EAccess x E) (Base bty btyP) X
  | TConst : forall bty (btyP : Bt F bty) (c : bty) X,
      ExprTyping G (EConst bty btyP c) (Base bty btyP) X
  | TOp : forall E0 E1 bty (btyP : Bt F bty) X,
      ExprTyping G E0 (Base bty btyP) X ->
      ExprTyping G E1 (Base bty btyP) X ->
      ExprTyping G (EOp E0 E1) (Base bty btyP) X.

  Lemma ExprTyping_with_Based_context_implies_Based_Typ :
    forall G E t X,
      Based_context G -> ExprTyping G E t X -> Based_Typ t.
  Proof using Type.
    intros. induction H0; simpl; auto.
    eapply Based_context_implies_Based_Typ; eauto.
  Qed.

  Lemma Instantiation_preserves_ExprTyping : forall G E typ X IX IMs,
      ExprTyping G E typ X ->
      (forall x : name, X = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
      (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) ->
          exists bms : BMs F, (IMs #[ m]) = Some bms) ->
      ExprTyping (Instantiate_context G IMs) E (MsInstantiate_Typ typ IMs) (subst_executor X IX).
  Proof using Type.
    intros. induction H.
    - apply TVar. apply Instantiate_context_preserves_In_context_var; auto.
    - eapply TViewDeref; eauto.
      + apply Instantiate_context_preserves_In_context_var with (IMs := IMs) in H.
        simpl in H. eapply H.
      + clear IHExprTyping. destruct H2 as [H2 []].
        split; [| split].
        * inversion H2; simpl in *; [apply Wf_executor_XBase|]. symmetry in H7.
          specialize (H0 x0 H7). destruct H0 as [bx]. rewrite H0.
          apply Wf_executor_XBase.
        * inversion H4; simpl in *; [apply Wf_MemSpace_MsBase|]. subst.
          assert (exists (x : name) (t : Typ), In_context_var G x t /\ In (FMs_Typ t) s).
          { exists x. eexists. split; [eapply H|]. simpl. constructor. }
          specialize (H1 s H7). destruct H1 as [bms]. rewrite H1.
          apply Wf_MemSpace_MsBase.
        * intros.
          assert (forall m : name, S = MsVar (BMs F) m -> exists bms : BMs F, (IMs #[ m]) = Some bms).
          { intros. subst. apply H1. exists x. eexists. split; [eapply H|]. simpl. constructor. }
          specialize (H5 IX IMs H0 H8). destruct H5 as [bx [bms [H5 []]]].
          exists bx, bms. rewrite <- H5. rewrite <- H9. simpl. split; auto.
    - apply TConst.
    - apply TOp; [apply IHExprTyping1; auto| apply IHExprTyping2; auto].
  Qed.

  Fixpoint build_new_kernel_context (G : context) (xs : list name) : context :=
    match G with
    | empty => empty
    | cons_ex x G' => cons_ex x (build_new_kernel_context G' xs)
    | cons_mem m G' => cons_mem m (build_new_kernel_context G' xs)
    | cons_var x typ G' =>
        match List.find (fun y => eqb_name x y) xs with
        | None => build_new_kernel_context G' xs
        | Some _ => cons_var x typ (build_new_kernel_context G' xs)
        end
    end.

  Lemma Based_build_new_kernel_context : forall G xs,
      Based_context G ->
      Based_context (build_new_kernel_context G xs).
  Proof using Type.
    intros G xs.
    induction G; intros; simpl in *; try contradiction.
    - subst. simpl. constructor.
    - destruct H.
      remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
      + simpl. split; auto.
      + apply IHG; auto.
  Qed.

  Lemma build_new_kernel_context_less : forall (G : context) (xs : list name),
    context_less (build_new_kernel_context G xs) G.
  Proof using Type.
    intros. split; [|split].
    - induction G; intros; simpl in *.
      + contradiction.
      + destruct H; [left; auto|]. 
        right. apply IHG; auto.
      + apply IHG. assumption.
      + remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
        * simpl in *. eapply IHG; eauto.
        * eapply IHG; eauto.
    - induction G; intros; simpl in *.
      + contradiction.
      + apply IHG; auto. 
      + destruct H; [left; auto|]. right. apply IHG; auto.
      + remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
        * simpl in *. eapply IHG; eauto.
        * eapply IHG; eauto.
    - induction G; intros.
      + simpl in H. contradiction.
      + simpl in *. eapply IHG; eauto.
      + simpl in *. eapply IHG; eauto.
      + simpl in H.
        remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
        * simpl in *. destruct H; [left; auto|right]. destruct H. split; auto.
        * symmetry in Heqo. pose proof (List.find_none _ _ Heqo). clear Heqo.
          simpl. assert (List.In x xs).
          { clear H0 IHG n t. induction G; simpl in *; auto; [contradiction|].
            remember (List.find (fun y : name => eqb_name n y) xs). destruct o; auto.
            simpl in *. destruct H; auto.
            - destruct H. subst. symmetry in Heqo. apply List.find_some in Heqo.
              destruct Heqo. apply eqb_name_true in H0. subst. assumption.
            - destruct H. apply IHG. assumption. }
          specialize (H0 x H1). simpl in H0. apply eqb_name_false in H0. right.
          split; auto.
  Qed.

  Inductive WfCmd (G : context) : Cmd -> executor (BX F) -> Prop :=
  | TSetVar : forall x t E X,
      In_context_var G x t ->
      ExprTyping G E t X ->
      WfCmd G (CSetVar x E) X
  | TSetView : forall x E0 E1 S bty btyP X,
      In_context_var G x (View S bty btyP) ->
      Accessible G X S ->
      ExprTyping G E0 (Base nat (Bt_nat F)) X ->
      ExprTyping G E1 (Base bty btyP) X ->
      WfCmd G (CSetView x E0 E1) X
  | TFence : forall X, WfCmd G (CFence X) (XBase _ (BX0 F))
  | TDeepCopy : forall E0 E1 S0 S1 bty btyP,
      ExprTyping G E0 (View S0 bty btyP) (XBase _ (BX0 F)) ->
      ExprTyping G E1 (View S1 bty btyP) (XBase _ (BX0 F)) ->
      WfCmd G (CDeepCopy E0 E1) (XBase _ (BX0 F))
  | TKernel : forall X (xs : list name) S,
      (forall x, List.In x xs -> exists t, In_context_var G x t) ->
      List.NoDup xs ->
      X <> (XBase _ (BX0 F)) ->
      WfStmt (build_new_kernel_context G xs) S X ->
      WfCmd G (CKernel X xs S) (XBase _ (BX0 F))
  with
    WfStmt (G : context) : Stmt -> executor (BX F) -> Prop :=
  | TCom : forall C S X,
      WfCmd G C X ->
      WfStmt G S X ->
      WfStmt G (SCom C S) X
  | TRet : forall X,
      WfStmt G SRet X
  | TDeclVar : forall x t E S X,
      ExprTyping G E t X ->
      WfStmt (cons_var x t G) S X ->
      WfStmt G (SDeclVar x E S) X
  | TDeclView : forall x M E bty btyP S,
      WfStmt (cons_var x (View M bty btyP) G) S (XBase _ (BX0 F)) ->
      ExprTyping G E (Base bty btyP) (XBase _ (BX0 F)) ->
      WfStmt G (SDeclView x M E S) (XBase _ (BX0 F)).

  Scheme WfCmd_WfStmt_ind := Induction for WfCmd Sort Prop
      with WfStmt_WfCmd_ind := Induction for WfStmt Sort Prop.

  Lemma Instantiation_preserves_WfStmt : forall IX IMs,
      (forall (x : name), ~ IX#[x] = Some (BX0 F)) ->
      forall G S X,
        (forall x : name, In (FX_Stmt S) x \/ X = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
        (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Stmt S) m ->
                          exists bms : BMs F, (IMs #[ m]) = Some bms) ->
        WfStmt G S X ->
        WfStmt (Instantiate_context G IMs)
          (MsInstantiate_Stmt (XInstantiate_Stmt S IX) IMs)
          (subst_executor X IX).
  Proof using Type.
    intros.
    generalize dependent H0.
    generalize dependent H1.
    generalize dependent H2.
    generalize dependent X.
    generalize dependent S.
    generalize dependent G.
    apply (WfStmt_WfCmd_ind
             (fun G C X (_ : WfCmd G C X) =>
                (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Cmd C) m ->
                                  exists bms : BMs F, (IMs #[ m]) = Some bms) ->
                (forall x : name, In (FX_Cmd C) x \/ X = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
                WfCmd (Instantiate_context G IMs) (MsInstantiate_Cmd (XInstantiate_Cmd C IX) IMs) 
                  (subst_executor X IX))
             (fun G S X (_ : WfStmt G S X) =>
                (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Stmt S) m ->
                                  exists bms : BMs F, (IMs #[ m]) = Some bms) ->
                (forall x : name, In (FX_Stmt S) x \/ X = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
                WfStmt (Instantiate_context G IMs) (MsInstantiate_Stmt (XInstantiate_Stmt S IX) IMs)
                  (subst_executor X IX)));
      auto; intros.
    - apply Instantiation_preserves_ExprTyping with (IX := IX) (IMs := IMs) in e; auto.
      apply TSetVar with (t := MsInstantiate_Typ t IMs); auto.
      apply Instantiate_context_preserves_In_context_var; auto.
    - eapply Instantiation_preserves_ExprTyping in e; eauto.
      eapply Instantiation_preserves_ExprTyping in e0; eauto.
      apply Instantiate_context_preserves_In_context_var with (IMs := IMs) in i as i'.
      apply TSetView with (S := subst_MemSpace S IMs) (bty := bty) (btyP := btyP); auto.
      destruct a as [a [a0]]. simpl in *.
      assert (forall x : name, X = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx)
        by (intros; apply H1; right; assumption).
      assert (forall m : name, S = MsVar (BMs F) m -> exists bms : BMs F, (IMs #[ m]) = Some bms).
      { intros. apply H0. left. subst. exists x. eexists. split; [eapply i|]. simpl. constructor. }
      specialize (H2 IX IMs H3 H4). clear H3 H4. destruct H2 as [bx [bms [H2 []]]]. rewrite <- H2.
      rewrite <- H3.
      split; [constructor|]. split; [constructor|].
      intros. exists bx, bms. auto.
    - apply TFence.
    - eapply TDeepCopy.
      + eapply Instantiation_preserves_ExprTyping in e; eauto.
      + eapply Instantiation_preserves_ExprTyping in e0; eauto.
    - simpl.
      apply TKernel; auto; intros.
      + clear H1 H0 w n0 n S X H2 H IX.
        specialize (e x H3). clear H3.
        induction G; intros; simpl in *; auto. destruct e as [t']. destruct H; destruct H.
        * subst. eexists. left. split; eauto.
        * assert (exists t : Typ, In_context_var G x t) by (exists t'; auto). 
          specialize (IHG H1). destruct IHG as [t''].
          exists t''. right. split; auto.
      + intro. destruct X; simpl in *.
        * apply n0. assumption.
        * remember (IX#[n1]). destruct o.
          -- inversion H3. subst. apply (H n1). symmetry. assumption.
          -- inversion H3.
      + fold MsInstantiate_Stmt. fold XInstantiate_Stmt.
        assert (build_new_kernel_context (Instantiate_context G IMs) xs
                = Instantiate_context (build_new_kernel_context G xs) IMs).
        { clear H1 H0 w n0 n e S X H2 H IX.
          induction G; simpl in *; auto.
          remember (List.find (fun y : name => eqb_name n y) xs).
          symmetry in Heqo. destruct o; simpl in *;
            rewrite IHG; reflexivity. }
        rewrite H3. apply H0; auto; intros.
        * apply H1. simpl. destruct H4.
          -- destruct H4 as [y [ty []]]. left. exists y, ty. split; auto.
             pose proof (build_new_kernel_context_less G xs) as C_less. destruct C_less as [_ [_ H6]].
             apply H6. assumption.
          -- right. assumption.
        * apply H2. simpl. destruct X; destruct H4; auto.
          -- inversion H4.
          -- left. right. assumption.
          -- inversion H4. left. left. constructor.
    - apply TCom.
      + fold MsInstantiate_Cmd. fold XInstantiate_Cmd. apply H0; intros.
        * apply H2. simpl. destruct H4; [left| right; left]; assumption.
        * apply H3. simpl. destruct H4; [left;left|right]; assumption.
      + fold MsInstantiate_Stmt. fold XInstantiate_Stmt. apply H1; intros.
        * apply H2. simpl. destruct H4; [left| right;right]; assumption.
        * apply H3. simpl. destruct H4; [left;right|right]; assumption.
    - apply TRet.
    - eapply Instantiation_preserves_ExprTyping in e as e'; eauto.
      apply TDeclVar with (t := MsInstantiate_Typ t IMs); auto.
      fold MsInstantiate_Stmt. fold XInstantiate_Stmt.
      assert (Instantiate_context (cons_var x t G) IMs = cons_var x (MsInstantiate_Typ t IMs) (Instantiate_context G IMs)).
      { clear e e' H2 H1 H0 w X S E H IX. induction G; intros; simpl in *; auto. }
      rewrite <- H3. apply H0; auto. intros.
      simpl in *. apply H1. destruct H4.
      + destruct H4 as [y [ty []]]. left. destruct H4; destruct H4.
        * subst. destruct t; simpl in *; [inversion H5|]. destruct m0; [inversion H5|].
          inversion H5. subst. inversion e. subst. exists x0. eexists. split; [eapply H4|].
          simpl. constructor.
        * exists y, ty. auto.
      + right; auto.
    - eapply Instantiation_preserves_ExprTyping in e as e'; eauto.
      apply TDeclView with (bty := bty) (btyP := btyP); auto.
      fold MsInstantiate_Stmt. fold XInstantiate_Stmt.
      assert (Instantiate_context (cons_var x (View M bty btyP) G) IMs = 
                cons_var x (View (subst_MemSpace M IMs) bty btyP) (Instantiate_context G IMs)).
      { clear e' e H2 H1 H0 w S E H IX. induction G; intros; simpl in *; auto. }
      rewrite <- H3. apply H0; auto.
      intros. apply H1. destruct H4.
      + destruct H4 as [y [ty []]]. simpl in H4. destruct H4; destruct H4.
        * subst. destruct M; simpl in *; [inversion H5|]. inversion H5. subst.
          right. left. constructor.
        * left. exists y, ty. auto.
      + right. simpl. destruct M; auto. right. assumption.
  Qed.

  Section MINIMAL_CONTEXT.
    (***********************************************)
    (* Finding the mimimal context for portability *)
    (***********************************************)
    (* Our portability theorem states that any well-typed program closed with
    respect to only variables (i.e. can have free executors and memory spaces)
    will be safe when the free variables are instantiated with any variables. An
    example of such a program is the following: *)

    (* decl x in DefaultMS; *)
    (* kernel (DefaultX, x, x(0) := 1; ret); *)
    (* ret; *)

    (* A non-example is the following: *)

    (* kernel (DefaultX, x, x(0) := 1; ret); *)
    (* ret; *)

    (* Though, the latter can be well-typed in a context containing x : View _
    _,

     The definition of portability refers to the free executor and memory space
     variables, but the *)


    Fixpoint filter_context_ex (G : context) (xs : list name) : context :=
      match G with
      | empty => empty
      | cons_ex x G' =>
          match List.find (fun y => eqb x y) xs with
          | Some _ => cons_ex x (filter_context_ex G' xs)
          | None => filter_context_ex G' xs
          end
      | cons_mem x G' => cons_mem x (filter_context_ex G' xs)
      | cons_var x t G' => cons_var x t (filter_context_ex G' xs)
      end.

    Lemma filter_context_ex_var : forall G x t xs,
        In_context_var G x t 
        <->
        In_context_var (filter_context_ex G xs) x t.
    Proof using Type.
      intros; split; intro.
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; apply IHG; assumption.
        - destruct H; [left; auto|]. destruct H. right.
          split; auto. }
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; apply IHG; assumption.
        - destruct H; [left; auto|]. destruct H. right.
          split; auto. }
    Qed.

    Lemma filter_context_ex_empty : forall G x,
        ~ In_context_ex (filter_context_ex G nil) x.
    Proof using Type.
      intros. induction G; intro; simpl in H; auto.
    Qed.

    Lemma filter_context_ex_elim : forall G xs m,
        In_context_ex (filter_context_ex G xs) m 
        <-> In_context_ex G m /\ List.In m xs.
    Proof using Type.
      intros. split; intro.
      { induction G.
        - exfalso. simpl in H. assumption. 
        - simpl in *. 
          remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
          + simpl in *. destruct H.
            * symmetry in Heqo. apply List.find_some in Heqo. destruct Heqo.
              apply eqb_name_true in H1. symmetry in H1. subst. split; auto.
            * apply IHG in H. destruct H. split; auto.
          + apply IHG in H. destruct H. split; auto.
        - simpl in *. apply IHG. assumption. 
        - simpl in *. apply IHG. assumption. 
      }
      { destruct H. induction G; simpl in *.
        - assumption.
        - destruct H.
          + subst. remember (List.find (fun y : name => eqb_name n y) xs) . destruct o.
            * simpl. left. reflexivity.
            * symmetry in Heqo. apply List.find_none with (x := n) in Heqo; auto.
              exfalso. apply eqb_name_false in Heqo. apply Heqo. reflexivity.
          + remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
            * simpl. right. apply IHG. assumption.
            * apply IHG. assumption.
        - apply IHG. assumption.
        - apply IHG. assumption.
      }
    Qed.

    Lemma filter_context_ex_less : forall G xs, 
        context_less (filter_context_ex G xs) G.
    Proof using Type.
      intros. induction G; simpl.
      - split; [|split]; intros; auto.
      - destruct IHG as [H0 []].
        remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
        + symmetry in Heqo. apply List.find_some in Heqo. destruct Heqo.
          apply eqb_name_true in H3 as H4. symmetry in H4. subst.
          split; [|split]; intros; simpl in *.
          * destruct H4; [left; auto| right]. apply H0. assumption.
          * apply H. assumption.
          * apply H1. assumption.
        + split; [|split]; intros; simpl in *.
          * right. apply H0. assumption.
          * apply H; auto.
          * apply H1; auto.
      - destruct IHG as [H0 []].
        split; [|split]; intros; simpl in *.
        + apply H0. assumption.
        + destruct H2; [left; assumption|]. right.
          apply H. assumption.
        + apply H1. assumption.
      - destruct IHG as [H0 []].
        split; [|split]; intros; simpl in *.
        + apply H0. assumption.
        + apply H. assumption.
        + destruct H2; [left; assumption|]. right.
          destruct H2. split; auto.
    Qed.

    Fixpoint filter_context_mem (G : context) (xs : list name) : context :=
      match G with
      | empty => empty
      | cons_ex x G' => cons_ex x (filter_context_mem G' xs)
      | cons_mem x G' => 
          match List.find (fun y => eqb x y) xs with
          | Some _ => cons_mem x (filter_context_mem G' xs)
          | None => filter_context_mem G' xs
          end
      | cons_var x t G' => cons_var x t (filter_context_mem G' xs)
      end.

    Lemma filter_context_mem_var : forall G x t xs,
        In_context_var G x t 
        <->
        In_context_var (filter_context_mem G xs) x t.
    Proof using Type.
      intros; split; intro.
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; apply IHG; assumption.
        - destruct H; [left; auto|]. destruct H. right.
          split; auto. }
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; apply IHG; assumption.
        - destruct H; [left; auto|]. destruct H. right.
          split; auto. }
    Qed.

    Lemma filter_context_mem_empty : forall G x,
        ~ In_context_mem (filter_context_mem G nil) x.
    Proof using Type.
      intros. induction G; intro; simpl in H; auto.
    Qed.

    Lemma filter_context_mem_elim : forall G xs m,
        In_context_mem (filter_context_mem G xs) m 
        <-> In_context_mem G m /\ List.In m xs.
    Proof using Type.
      intros. split; intro.
      { induction G.
        - exfalso. simpl in H. assumption. 
        - simpl in *. apply IHG. assumption. 
        - simpl in *. 
          remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
          + simpl in *. destruct H.
            * symmetry in Heqo. apply List.find_some in Heqo. destruct Heqo.
              apply eqb_name_true in H1. symmetry in H1. subst. split; auto.
            * apply IHG in H. destruct H. split; auto.
          + apply IHG in H. destruct H. split; auto.
        - simpl in *. apply IHG. assumption. 
      }
      { destruct H. induction G; simpl in *.
        - assumption.
        - apply IHG. assumption.
        - destruct H.
          + subst. remember (List.find (fun y : name => eqb_name n y) xs) . destruct o.
            * simpl. left. reflexivity.
            * symmetry in Heqo. apply List.find_none with (x := n) in Heqo; auto.
              exfalso. apply eqb_name_false in Heqo. apply Heqo. reflexivity.
          + remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
            * simpl. right. apply IHG. assumption.
            * apply IHG. assumption.
        - apply IHG. assumption.
      }
    Qed.

    Lemma filter_context_mem_less : forall G xs, 
        context_less (filter_context_mem G xs) G.
    Proof using Type.
      intros. induction G; simpl.
      - split; [|split]; intros; auto.
      - destruct IHG as [H0 []].
        split; [|split]; intros; simpl in *.
        + destruct H2; [left; assumption|]. right.
          apply H0. assumption.
        + apply H. assumption.
        + apply H1. assumption.
      - destruct IHG as [H0 []].
        remember (List.find (fun y : name => eqb_name n y) xs). destruct o.
        + symmetry in Heqo. apply List.find_some in Heqo. destruct Heqo.
          apply eqb_name_true in H3 as H4. symmetry in H4. subst.
          split; [|split]; intros; simpl in *.
          * apply H0. assumption.
          * destruct H4; [left; auto| right]. apply H. assumption.
          * apply H1. assumption.
        + split; [|split]; intros; simpl in *.
          * apply H0; auto.
          * right. apply H. assumption.
          * apply H1; auto.
      - destruct IHG as [H0 []].
        split; [|split]; intros; simpl in *.
        + apply H0. assumption.
        + apply H. assumption.
        + destruct H2; [left; assumption|]. right.
          destruct H2. split; auto.
    Qed.

    Lemma filter_context_ex_ex : forall G (x : name) xs,
        List.In x xs ->
        In_context_ex G x ->
        In_context_ex (filter_context_ex G xs) x.
    Proof using Type.
      intros. induction G; simpl in *; auto.
      remember (List.find (fun y : name => eqb_name n y) xs).
      destruct o.
      - simpl. destruct H0; [left; assumption|right; apply IHG; assumption].
      - destruct H0.
        + exfalso. symmetry in Heqo. apply List.find_none with (x:=x) in Heqo; auto.
          apply eqb_name_false in Heqo. apply Heqo. symmetry. assumption.
        + symmetry in Heqo. apply List.find_none with (x:=x) in Heqo; auto.
    Qed.

    Lemma filter_context_ex_mem : forall G x mss,
        In_context_ex (filter_context_mem G mss) x 
        <->
        In_context_ex G x.
    Proof using Type.
      intros. split; intro.
      { intros. induction G; simpl in *; auto.
        - destruct H; [left; auto | right; apply IHG; auto].
        - remember (List.find (fun y : name => eqb_name n y) mss).
          destruct o; simpl; apply IHG; auto. }
      { intros. induction G; simpl in *; auto.
        - destruct H; [left; auto | right; apply IHG; auto].
        - remember (List.find (fun y : name => eqb_name n y) mss).
          destruct o; simpl; apply IHG; auto. }
    Qed.

    Lemma filter_context_mem_ex : forall G ms xs,
        In_context_mem (filter_context_ex G xs) ms 
        <->
        In_context_mem G ms.
    Proof using Type.
      intros; split; intro.
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; simpl; apply IHG; auto.
        - destruct H; [left; auto | right; apply IHG; auto]. }
      { intros. induction G; simpl in *; auto.
        - remember (List.find (fun y : name => eqb_name n y) xs).
          destruct o; simpl; apply IHG; auto.
        - destruct H; [left; auto | right; apply IHG; auto]. }
    Qed.

    Fixpoint FX_Cmd_listset (C : Cmd) : set name :=
      match C with
      | CKernel (XBase _ _) _ S0 => FX_Stmt_listset S0
      | CKernel (XVar _ x) _ S0 => set_add name_eq_dec x (FX_Stmt_listset S0)
      | CFence (XVar _ x) => set_add name_eq_dec x (empty_set _)
      | _ => empty_set _
      end
    with FX_Stmt_listset (S : Stmt) : set name :=
           match S with
           | SCom C S0 => set_union name_eq_dec (FX_Cmd_listset C) (FX_Stmt_listset S0)
           | SRet => empty_set _
           | SDeclVar _ _ S0 => FX_Stmt_listset S0
           | SDeclView _ _ _ S0 => FX_Stmt_listset S0
           end.

    Lemma FX_Stmt_listset_iff_FX_Stmt : forall x S,
        List.In x (FX_Stmt_listset S) <-> In (FX_Stmt S) x.
    Proof using Type.
      intros.
      split; intros.
      - generalize dependent H.
        pattern S.
        apply Stmt_Cmd_ind with 
          (P0 := fun s =>
                   List.In x (FX_Stmt_listset s) ->
                   In (FX_Stmt s) x)
          (P := fun c =>
                  List.In x (FX_Cmd_listset c) ->
                  In (FX_Cmd c) x); intros; auto.
        + simpl in *. destruct e; inversion H.
          * subst. constructor.
          * inversion H0.
        + simpl in *. destruct e.
          * apply H. assumption.
          * destruct (name_eq_dec x n).
            -- left. subst. constructor.
            -- right.
               pose proof (set_add_elim2 _ _ H0 n0). apply H. assumption.
        + simpl in *. apply set_union_elim in H1. 
          destruct H1.
          * left. apply H. assumption.
          * right. apply H0. assumption.
      - generalize dependent H.
        pattern S.
        apply Stmt_Cmd_ind with 
          (P0 := fun s =>
                   In (FX_Stmt s) x ->
                   List.In x (FX_Stmt_listset s))
          (P := fun c =>
                  In (FX_Cmd c) x ->
                  List.In x (FX_Cmd_listset c)); intros; auto.
        + simpl in *. destruct e; inversion H.
          subst. simpl. left. reflexivity.
        + simpl in *. destruct e.
          * apply H. assumption.
          * destruct H0.
            -- inversion H0. apply set_add_intro2. reflexivity.
            -- apply set_add_intro1. apply H. assumption.
        + simpl in *. destruct H1.
          * apply set_union_intro1. apply H. assumption.
          * apply set_union_intro2. apply H0. assumption.
    Qed.

    Lemma FX_Cmd_listset_iff_FX_Cmd : forall x C,
        List.In x (FX_Cmd_listset C) <-> In (FX_Cmd C) x.
    Proof using Type.
      intros.
      split; intros.
      - generalize dependent H.
        pattern C.
        apply Cmd_Stmt_ind with 
          (P0 := fun s =>
                   List.In x (FX_Stmt_listset s) ->
                   In (FX_Stmt s) x)
          (P := fun c =>
                  List.In x (FX_Cmd_listset c) ->
                  In (FX_Cmd c) x); intros; auto.
        + simpl in *. destruct e; inversion H.
          * subst. constructor.
          * inversion H0.
        + simpl in *. destruct e.
          * apply H. assumption.
          * destruct (name_eq_dec x n).
            -- left. subst. constructor.
            -- right.
               pose proof (set_add_elim2 _ _ H0 n0). apply H. assumption.
        + simpl in *. apply set_union_elim in H1. 
          destruct H1.
          * left. apply H. assumption.
          * right. apply H0. assumption.
      - generalize dependent H.
        pattern C.
        apply Cmd_Stmt_ind with 
          (P0 := fun s =>
                   In (FX_Stmt s) x ->
                   List.In x (FX_Stmt_listset s))
          (P := fun c =>
                  In (FX_Cmd c) x ->
                  List.In x (FX_Cmd_listset c)); intros; auto.
        + simpl in *. destruct e; inversion H.
          subst. simpl. left. reflexivity.
        + simpl in *. destruct e.
          * apply H. assumption.
          * destruct H0.
            -- inversion H0. apply set_add_intro2. reflexivity.
            -- apply set_add_intro1. apply H. assumption.
        + simpl in *. destruct H1.
          * apply set_union_intro1. apply H. assumption.
          * apply set_union_intro2. apply H0. assumption.
    Qed.
    
    Fixpoint FMs_Cmd_listset (C : Cmd) : set name :=
      match C with
      | CKernel _ _ S0 => FMs_Stmt_listset S0
      | _ => empty_set _
      end
    with FMs_Stmt_listset (S : Stmt) : set name :=
           match S with
           | SCom C S0 => set_union name_eq_dec (FMs_Cmd_listset C) (FMs_Stmt_listset S0)
           | SRet => empty_set _
           | SDeclVar _ _ S0 => FMs_Stmt_listset S0
           | SDeclView _ (MsBase _ _) _ S0 => FMs_Stmt_listset S0
           | SDeclView _ (MsVar _ v) _ S0 => set_add name_eq_dec v (FMs_Stmt_listset S0)
           end.

    Lemma FMs_Stmt_listset_implies_FMs_Stmt : forall x S,
        List.In x (FMs_Stmt_listset S) <-> In (FMs_Stmt S) x.
    Proof using Type.
      intros.
      split; intros.
      - generalize dependent H.
        pattern S.
        apply Stmt_Cmd_ind with 
          (P0 := fun s =>
                   List.In x (FMs_Stmt_listset s) ->
                   In (FMs_Stmt s) x)
          (P := fun c =>
                  List.In x (FMs_Cmd_listset c) ->
                  In (FMs_Cmd c) x); intros; auto.
        + simpl in *. apply set_union_elim in H1. 
          destruct H1.
          * left. apply H. assumption.
          * right. apply H0. assumption.
        + simpl in *. destruct m.
          * apply H. assumption.
          * destruct (name_eq_dec x n0).
            -- left. subst. constructor.
            -- right.
               pose proof (set_add_elim2 _ _ H0 n1). apply H. assumption.
      - generalize dependent H.
        pattern S.
        apply Stmt_Cmd_ind with 
          (P0 := fun s =>
                   In (FMs_Stmt s) x ->
                   List.In x (FMs_Stmt_listset s))
          (P := fun c =>
                  In (FMs_Cmd c) x ->
                  List.In x (FMs_Cmd_listset c)); intros; auto.
        + simpl in *. destruct H1.
          * apply set_union_intro1. apply H. assumption.
          * apply set_union_intro2. apply H0. assumption.
        + simpl in *. destruct m.
          * apply H. assumption.
          * destruct H0.
            -- inversion H0. apply set_add_intro2. reflexivity.
            -- apply set_add_intro1. apply H. assumption.
    Qed.

    Lemma FMs_Cmd_listset_implies_FMs_Cmd : forall x C,
        List.In x (FMs_Cmd_listset C) <-> In (FMs_Cmd C) x.
    Proof using Type.
      intros.
      split; intros.
      - generalize dependent H.
        pattern C.
        apply Cmd_Stmt_ind with 
          (P0 := fun s =>
                   List.In x (FMs_Stmt_listset s) ->
                   In (FMs_Stmt s) x)
          (P := fun c =>
                  List.In x (FMs_Cmd_listset c) ->
                  In (FMs_Cmd c) x); intros; auto.
        + simpl in *. apply set_union_elim in H1. 
          destruct H1.
          * left. apply H. assumption.
          * right. apply H0. assumption.
        + simpl in *. destruct m.
          * apply H. assumption.
          * destruct (name_eq_dec x n0).
            -- left. subst. constructor.
            -- right.
               pose proof (set_add_elim2 _ _ H0 n1). apply H. assumption.
      - generalize dependent H.
        pattern C.
        apply Cmd_Stmt_ind with 
          (P0 := fun s =>
                   In (FMs_Stmt s) x ->
                   List.In x (FMs_Stmt_listset s))
          (P := fun c =>
                  In (FMs_Cmd c) x ->
                  List.In x (FMs_Cmd_listset c)); intros; auto.
        + simpl in *. destruct H1.
          * apply set_union_intro1. apply H. assumption.
          * apply set_union_intro2. apply H0. assumption.
        + simpl in *. destruct m.
          * apply H. assumption.
          * destruct H0.
            -- inversion H0. apply set_add_intro2. reflexivity.
            -- apply set_add_intro1. apply H. assumption.
    Qed.

    Lemma Accessible_minimal_context : forall G X S xs mss,
        (forall x : name, X = XVar _ x -> List.In x xs) ->
        (forall m : name, S = MsVar _ m -> List.In m mss) ->
       Accessible G X S ->
       Accessible (filter_context_ex (filter_context_mem G mss) xs) X S.
    Proof using Type.
      intros. destruct H1 as [H2 [H5 H4]].
      split; [| split].
      - intros.
        inversion H2; [apply Wf_executor_XBase|apply Wf_executor_XVar].
        apply filter_context_ex_elim. split.
        + apply filter_context_ex_mem. assumption.
        + apply H. symmetry. assumption.
      - intros. inversion H5; [apply Wf_MemSpace_MsBase| apply Wf_MemSpace_MsVar].
        apply filter_context_mem_ex. apply filter_context_mem_elim. auto.
      - intros. apply H4; intros; auto.
    Qed.

    Lemma ExprTyping_minimal_context : forall G E t X xs mss,
        (forall x, X = XVar _ x -> List.In x xs) ->
        (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) -> List.In m mss) ->
        ExprTyping G E t X ->
        ExprTyping (filter_context_ex (filter_context_mem G mss) xs) E t X.
    Proof using Type.
      intros. induction H1.
      - apply TVar. apply filter_context_ex_var.
        apply filter_context_mem_var. assumption.
      - apply TViewDeref with (S := S); auto.
        + apply filter_context_ex_var.
          apply filter_context_mem_var.
          assumption.
        + apply Accessible_minimal_context; auto.
          intros. apply H0. exists x. subst. eexists. split; [eapply H1|]. simpl.
          constructor.
      - apply TConst.
      - apply TOp; auto.
    Qed.

    Lemma WfStmt_minimal_context' : forall G S X xs mss,
        (forall x, In (FX_Stmt S) x \/ X = XVar _ x -> List.In x xs) ->
        (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Stmt S) m -> List.In m mss) ->
        WfStmt G S X ->
        WfStmt (filter_context_ex (filter_context_mem G mss) xs) S X.
    Proof using Type.
      intros.
      generalize dependent H0.
      generalize dependent H.
      generalize dependent H1.
      generalize dependent X.
      generalize dependent S.
      generalize dependent G.
      apply (WfStmt_WfCmd_ind
               (fun G C X (_ : WfCmd G C X) =>
                  (forall x, In (FX_Cmd C) x \/ X = XVar _ x -> List.In x xs) ->
                  (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Cmd C) m -> List.In m mss) ->
                  WfCmd (filter_context_ex (filter_context_mem G mss) xs) C X)
               (fun G S X (_ : WfStmt G S X) =>
                  (forall x, In (FX_Stmt S) x \/ X = XVar _ x -> List.In x xs) ->
                  (forall m : name, (exists x t, In_context_var G x t /\ In (FMs_Typ t) m) \/ In (FMs_Stmt S) m -> List.In m mss) ->
                  WfStmt (filter_context_ex (filter_context_mem G mss) xs) S X));
        intros.
      - apply TSetVar with (t := t).
        + apply filter_context_ex_var. apply filter_context_mem_var. assumption.
        + apply ExprTyping_minimal_context; auto.
      - apply TSetView with (S := S) (bty := bty) (btyP := btyP); try (apply ExprTyping_minimal_context; auto).
        + apply filter_context_ex_var. apply filter_context_mem_var. assumption.
        + apply Accessible_minimal_context; auto.
          intros. apply H0. left. exists x. eexists. split; [eapply i|]. simpl. rewrite H1.
          constructor.
      - apply TFence.
      - eapply TDeepCopy; eapply ExprTyping_minimal_context; eauto.
      - apply TKernel; auto.
        + intros. specialize (e x H2). destruct e as [t]. exists t.
          clear H w n0 n H2 H0 xs0 S H1 X.
          induction G; simpl in *; auto.
          * remember (List.find (fun y : name => eqb_name n y) xs). symmetry in Heqo.
            destruct o; apply IHG; auto.
          * remember (List.find (fun y : name => eqb_name n y) mss). symmetry in Heqo.
            destruct o; apply IHG; auto.
          * destruct H3 as [[] | []].
            -- subst. left. split; auto.
            -- right. split; auto.
        + assert (forall x : name, In (FX_Stmt S) x \/ X = XVar (BX F) x -> List.In x xs).
          { clear H1 H w n mss e. intros. apply H0. clear H0.
             simpl in *. destruct X.
             - destruct H; [left; auto|]. inversion H.
             - destruct H; [left;right;auto|]. inversion H.
               left. left. constructor. }
          specialize (H H2). clear H2.
          assert (forall m : name, (exists (x : name) (t : Typ), In_context_var (build_new_kernel_context G xs0) x t /\ In (FMs_Typ t) m) \/ In (FMs_Stmt S) m -> List.In m mss).
          { intros. apply H1. simpl. destruct H2; auto. destruct H2 as [x [t []]]. left.
            exists x, t. split; auto. destruct (build_new_kernel_context_less G xs0) as [_ [_ H4]]. apply H4.
            assumption. }
          specialize (H H2).
          enough (build_new_kernel_context (filter_context_ex (filter_context_mem G mss) xs) xs0
                  = filter_context_ex (filter_context_mem (build_new_kernel_context G xs0) mss) xs)
            by (rewrite H3; assumption).
          clear H2 H1 H0 H w n0 n e S.
          induction G; simpl in *; auto.
           * remember (List.find (fun y : name => eqb_name n y) xs). destruct o; auto.
             simpl. congruence.
           * remember (List.find (fun y : name => eqb_name n y) mss). destruct o; auto.
             simpl. congruence.
           * rewrite IHG.
             remember (List.find (fun y : name => eqb_name n y) xs0). destruct o; simpl; auto.
      - apply TCom; auto.
        + apply H; auto; intros.
          * apply H1. simpl. destruct H3; [left; left | right]; assumption.
          * apply H2. simpl. destruct H3; [left|right;left]; assumption.
        + apply H0; auto; intros.
          * apply H1. simpl. destruct H3; [left; right|]; auto.
          * apply H2. simpl. destruct H3; [left|right;right]; auto.
      - apply TRet.
      - apply TDeclVar with (t := t); auto.
        apply ExprTyping_minimal_context; auto.
        assert (filter_context_ex (filter_context_mem (cons_var x t G) mss) xs =
                  cons_var x t (filter_context_ex (filter_context_mem G mss) xs)).
        { clear H1 H0 H w e X S E. induction G; simpl in *; auto. }
        rewrite <- H2. apply H; auto. intros. apply H1.
        simpl. destruct H3; auto. destruct H3 as [y [ty []]]. simpl in H3. 
        destruct H3; destruct H3.
        + destruct ty; [subst; inversion H4|].  subst. simpl in *. destruct m0; [inversion H4|].
          inversion H4. subst. clear H2 H1 H0 H w H4. left. inversion e; subst.
          exists x0. eexists. split; [eapply H|]. simpl. constructor.
        + left. exists y, ty. auto.
      - eapply ExprTyping_minimal_context in e; eauto.
        apply TDeclView with (bty := bty) (btyP := btyP); auto.
        assert (cons_var x (View M bty btyP) (filter_context_ex (filter_context_mem G mss) xs)
                = filter_context_ex (filter_context_mem (cons_var x (View M bty btyP) G) mss) xs).
        { clear e H1 H0 H w S E. induction G; simpl in *; auto. }
        rewrite H2. apply H; auto. intros. apply H1. simpl. destruct H3.
        + destruct H3 as [y [ty []]]. simpl in H3. destruct H3; destruct H3.
          * subst. destruct M.
            -- simpl in *. inversion H4.
            -- simpl in *. inversion H4. right. left. constructor.
          * left. exists y, ty. auto.
        + destruct M; right; auto. right. assumption.
    Qed.

    Lemma WfStmt_Cmd_minimal_context : forall G S IX IMs,
        ~ (exists (x : name) (t : Typ), In_context_var G x t) ->
        WfStmt G S (XBase _ (BX0 F)) ->
        (forall x : name, In (FX_Stmt S) x -> exists bx : BX F, (IX #[ x]) = Some bx) ->
        (forall m : name, In (FMs_Stmt S) m -> exists bms : BMs F, (IMs #[ m]) = Some bms) ->
        WfStmt (filter_context_ex (filter_context_mem G (FMs_Stmt_listset S))
                  (FX_Stmt_listset S))
          S (XBase _ (BX0 F)).
    Proof using Type.
      intros. apply WfStmt_minimal_context'; auto; intros.
      - apply FX_Stmt_listset_iff_FX_Stmt. destruct H3; auto.
        inversion H3.
      - apply FMs_Stmt_listset_implies_FMs_Stmt. destruct H3; auto.
        exfalso. apply H. destruct H3 as [x [t []]].
        exists x, t. assumption.
    Qed. 
  End MINIMAL_CONTEXT.

  (****************************************************************************)
  (*                          OPERATIONAL SEMANTICS                           *)
  (****************************************************************************)

  Definition Pointer := name.
  (* Note that unlike the language, which may vary over executors and memory
  spaces, the machines only operate over the instantiations thereof, i.e. base
  exectors and memory spaces. *)
  Inductive MachVal : Type :=
  | BaseVal : forall bty, Bt F bty -> forall (c : bty), MachVal
  | ViewVal : BMs F -> Pointer -> MachVal.
  Definition MachMemSpaces : Type := Map (BMs F) (Map Pointer (Map nat MachVal)).
  Axiom MachMemSpaces_extensible : forall (MM : MachMemSpaces) Ms, exists p, MM#[Ms,p] = None.
  Definition LocalMem : Type := Map name MachVal.
  Definition EsConf : Type := MachMemSpaces * LocalMem * Expr.

  Lemma sub_MM : forall (MM : MachMemSpaces) M p n V,
      MM#[M,p,n] = Some V ->
      exists q, MM#[M,p] = Some q.
  Proof using Type.
    intros. 
    destruct MM. simpl in *. remember (get M). destruct o.
    - destruct m. simpl in *. remember (get0 p). destruct o.
      + exists m. reflexivity.
      + inversion H.
    - inversion H.
  Qed.

  Inductive ExprEval : EsConf -> MachVal -> Prop :=
  | EvalVar : forall MM L x v,
      L#[x] = Some v ->
      ExprEval (MM,L,EVar x) v
  | EvalViewDeref : forall MM L M x E n p v,
      ExprEval (MM,L,E) (BaseVal nat (Bt_nat F) n) ->
      L#[x] = Some (ViewVal M p) ->
      MM#[M,p,n] = Some v ->
      ExprEval (MM,L,EAccess x E) v
  | EvalConst : forall MM L bty (btyP : Bt F bty) (c : bty),
      ExprEval (MM,L,EConst bty btyP c) (BaseVal bty btyP c)
  | EvalOp : forall MM L E0 E1 bty (btyP : Bt F bty) (v0 v1 : bty),
      ExprEval (MM,L,E0) (BaseVal bty btyP v0) ->
      ExprEval (MM,L,E1) (BaseVal bty btyP v1) ->
      ExprEval (MM,L,EOp E0 E1) (BaseVal bty btyP v0). (* TODO actually perform an operation *)

  Definition Safe_EsConf (Conf : EsConf) : Prop :=
    exists V, ExprEval Conf V.

  Lemma Deterministic_ExprEval : forall conf v, ExprEval conf v -> forall w, ExprEval conf w -> v = w.
  Proof using Type.
    intros conf v H. induction H; intros; simpl in *.
    - inversion H0. subst. rewrite -> H in H5. inversion H5. reflexivity.
    - inversion H2. subst. specialize (IHExprEval _ H8). inversion IHExprEval.
      apply EqdepTheory.inj_pair2 in H4. subst. rewrite -> H0 in H9. inversion H9.
      subst. rewrite -> H1 in H10. inversion H10. reflexivity.
    - inversion H. subst. apply EqdepTheory.inj_pair2 in H4. subst.
      pose proof proof_irrelevance (Bt F bty) btyP btyP1. subst. reflexivity.
    - inversion H1. subst. exact (IHExprEval1 _ H7).
  Qed.

  Definition BXState : Type := MachMemSpaces * LocalMem * Stmt.
  Definition Final_BXState (s : BXState) : Prop :=
    exists MM L, s = (MM,L,SRet).

  #[local] Instance edm : EqDec (BMs F) := BMs_EqDec F.
  #[local] Instance edx : EqDec (BX F) := BX_EqDec F.

  Inductive BXStep : BXState -> BXState -> Prop :=
  | XDeclVar : forall MM L x E S v,
      ExprEval (MM,L,E) v ->
      BXStep (MM,L,SDeclVar x E S) (MM,L[x |-> v],S)
  | XSetVar : forall MM L x E S v_new,
      (exists v_old, L#[x] = Some v_old) ->
      ExprEval (MM,L,E) v_new ->
      BXStep (MM,L,SCom (CSetVar x E) S) (MM,L[x |-> v_new],S)
  | XSetView : forall MM L x E0 E1 S M p n v,
      L#[x] = Some (ViewVal M p) ->
      (exists v_old, MM#[M,p,n] = Some v_old) ->
      ExprEval (MM,L,E0) (BaseVal nat (Bt_nat F) n) ->
      ExprEval (MM,L,E1) v ->
      BXStep (MM,L,SCom (CSetView x E0 E1) S) (MM[M,p,n |-> v],L,S).

  Lemma Final_BXState_is_stuck : forall s, Final_BXState s -> (exists t, BXStep s t) -> False.
  Proof using Type.
    intros. destruct H0 as [t H0]. destruct H as [MM [L H]]. subst.
    inversion H0; subst.
  Qed.

  Inductive Reachable {A : Type} (R : A -> A -> Prop) (x : A) : nat -> A -> Prop :=
  | Refl  : Reachable R x 0 x
  | Trans : forall y z n, Reachable R x n y -> R y z -> Reachable R x (S n) z.

  Definition Safe_BXState (s : BXState) : Prop :=
    forall step t, Reachable BXStep s step t -> Final_BXState t \/ exists t', BXStep t t'.

  Lemma Deterministic_BXStep : forall s t0, BXStep s t0 -> forall t1, BXStep s t1 -> t0 = t1.
  Proof using Type.
    intros s t0 H. destruct H; intros; simpl in *.
    - inversion H0; subst. pose proof (Deterministic_ExprEval _ _ H _ H7). subst. reflexivity.
    - inversion H1; subst. pose proof (Deterministic_ExprEval _ _ H0 _ H9). subst. reflexivity.
    - inversion H3; subst. rewrite -> H in H11. inversion H11; subst.
      pose proof (Deterministic_ExprEval _ _ H1 _ H13).
      inversion H4. apply EqdepTheory.inj_pair2 in H6. subst.
      pose proof (Deterministic_ExprEval _ _ H2 _ H14). subst.
      reflexivity.
  Qed.

  Definition BXSpaceQueues := Map (BX F) (Fifo (LocalMem * Stmt)).

  Definition BX0State : Type := MachMemSpaces * BXSpaceQueues * LocalMem * Stmt.

  Definition Initial_BX0State (s : BX0State) : Prop :=
    exists MM SS S, s = (MM,SS,empty_Map,S) /\ (forall (X : BX F), SS#[X] = Some empty_Fifo).

  Definition MkInit (S : Stmt) : BX0State :=
    (empty_Map,
      List.fold_right (fun bx SS => SS[bx |-> empty_Fifo]) empty_Map (BX_elems F),
      empty_Map, S).

  Definition Final_BX0State (s : BX0State) : Prop :=
    exists MM SS L, s = (MM,SS,L,SRet) /\ (forall (X : BX F), SS#[X] = Some empty_Fifo).

  Fixpoint build_new_kernel_L (L : LocalMem) (xs : list name) : option LocalMem :=
    match xs with
    | nil => Some empty_Map
    | cons x xs' =>
        match L#[x] with
        | None => None
        | Some V => L_new <- build_new_kernel_L L xs';; Some (L_new[x |-> V])
        end
    end.

  Definition default_Map (V : MachVal) : Map nat MachVal :=
    {| get := fun _ => Some V |}.

  Inductive BX0Step : BX0State -> BX0State -> Prop :=
  | X0Step : forall MM MM_BX0' SS L L' S S',
      BXStep (restrict MM (comp_acc_rel F (BX0 F)),L,S) (MM_BX0',L',S') ->
      BX0Step (MM,SS,L,S)
        (join (restrict MM (fun Ms => negb (comp_acc_rel F (BX0 F) Ms))) MM_BX0',SS,L',S')
  | HDeclView : forall MM SS L E S x M p V,
      MM#[M,p] = None ->
      ExprEval (restrict MM (comp_acc_rel F (BX0 F)),L,E) V ->
      BX0Step
        (MM,SS,L,SDeclView x (MsBase (BMs F) M) E S)
        (MM[M,p |-> default_Map V],SS,L[x |-> ViewVal M p],S)
  | HKernel : forall MM SS L L_new X ff xs S S',
      SS#[X] = Some ff ->
      build_new_kernel_L L xs = Some L_new ->
      BX0Step 
        (MM,SS,L,SCom (CKernel (XBase (BX F) X) xs S) S')
        (MM,SS[X |-> push ff (L_new,S)],L,S')
  | HFence : forall MM SS L X S,
      SS#[X] = Some empty_Fifo ->
      BX0Step (MM,SS,L,SCom (CFence (XBase (BX F) X)) S) (MM,SS,L,S)
  | HDeepCopy : forall MM SS L S E0 M0 p0 E1 M1 p1 bm,
      ExprEval (restrict MM (comp_acc_rel F (BX0 F)),L,E0) (ViewVal M0 p0) ->
      ExprEval (restrict MM (comp_acc_rel F (BX0 F)),L,E1) (ViewVal M1 p1) ->
      MM#[M0,p0] = Some bm ->
      BX0Step
        (MM,SS,L,SCom (CDeepCopy E0 E1) S)
        (MM[M1,p1 |-> bm],SS,L,S)
  | HXPop : forall MM SS L S X ff,
      SS#[X] = Some ff ->
      (exists L', peek ff = Some (L',SRet)) ->
      BX0Step (MM,SS,L,S) (MM,SS[X |-> pop ff],L,S)
  | HXStep : forall MM SS L S X L' S' ff L'' S'' MM_X',
      SS#[X] = Some ff ->
      peek ff = Some (L',S') ->
      BXStep (restrict MM (comp_acc_rel F X),L',S') (MM_X',L'',S'') ->
      BX0Step
        (MM,SS,L,S)
        (join (restrict MM (fun Ms => negb (comp_acc_rel F X Ms))) MM_X',
          SS[X |-> push (pop ff) (L'',S'')],L,S).

  Lemma Final_BX0State_is_stuck : forall s, Final_BX0State s -> (exists t, BX0Step s t) -> False.
  Proof using Type.
    intros. destruct H0 as [t H0]. destruct H as [MM [SS [L []]]]. subst.
    inversion H0; simpl; subst.
    - inversion H6.
    - destruct H7. specialize (H1 X). rewrite -> H1 in H6. inversion H6.
      pose proof peek_empty_Fifo (A := (LocalMem * Stmt)).
      subst. rewrite -> H2 in H. inversion H.
    - specialize (H1 X). rewrite -> H1 in H6. inversion H6.
      pose proof peek_empty_Fifo (A := (LocalMem * Stmt)).
      subst. rewrite -> H in H7. inversion H7.
  Qed.

  Definition Safe_BX0State (s : BX0State) : Prop :=
    forall step t, Reachable BX0Step s step t -> Final_BX0State t \/ exists t', BX0Step t t'.

  (****************************************************************************)
  (*                              REALIZABILITY                               *)
  (****************************************************************************)
  (***********************)
  (* Memory space typing *)
  (***********************)
  (* This is one part of the Kirpke world. (The other is a step index.) It
  tracks the types of all of the objects of the memory spaces. *)
  Definition MemSpaceTypings : Type := Map (BMs F) (Map Pointer { bty & Bt F bty }).

  Definition Acc (T T' : MemSpaceTypings) : Prop :=
    forall Ms p B, T#[Ms,p] = Some B -> T'#[Ms,p] = Some B.

  Lemma Acc_refl : forall T, Acc T T.
  Proof using Type.
    intros. intros Ms p B H. assumption.
  Qed.

  Lemma Acc_trans : forall T0 T1 T2, Acc T0 T1 -> Acc T1 T2 -> Acc T0 T2.
  Proof using Type.
    intros. intros Ms p B H1. apply H0. apply H. assumption.
  Qed.

  Lemma Acc_extend : forall T Ms p B,
      T#[Ms,p] = None ->
      Acc T (T [Ms, p |-> B]).
  Proof using Type.
    intros. intros Ms' p' B' H0.
    simpl. remember (eqb Ms' Ms). destruct b.
    - remember (T#[Ms']). destruct o.
      + simpl. remember (eqb_name p p'). destruct b.
        * symmetry in Heqb,Heqb0. apply eqb_leibniz in Heqb.
          subst. apply eqb_name_true in Heqb0. subst.
          rewrite <- Heqo in H. rewrite -> H0 in H.
          inversion H.
        * assumption.
      + inversion H0.
    - assumption.
  Qed.
  
  (****************************************)
  (* Semantics of types of machine values *)
  (****************************************)
  Definition ValSem (T : MemSpaceTypings) (typ : Typ) (V : MachVal) : Prop :=
    match typ,V with
    | Base bty _, BaseVal bty' _ _ => bty = bty'
    | View (MsBase _ M) bty _, ViewVal M' p =>
        M = M' /\ exists W, T#[M, p] = Some W /\ projT1 W = bty
    | _,_ => False
    end.

  Lemma ValSem_extension_closed : forall T t V T',
      ValSem T t V ->
      Acc T T' ->
      ValSem T' t V.
  Proof using Type.
    intros. destruct t,V; simpl; auto.
    destruct m; auto. inversion H.
    subst. split; auto. destruct H2 as [B []].
    exists B. split; auto.
  Qed. 
  
  (********************************)
  (* Semantics of typing contexts *)
  (********************************)
  Definition ContextSem
    (T : MemSpaceTypings) (G : context) (L : LocalMem) : Prop :=
    forall x typ,
      In_context_var G x typ ->
      exists V, L#[x] = Some V /\ ValSem T typ V.

  Lemma ContextSem_extension_closed : forall T G L T',
      ContextSem T G L ->
      Acc T T' ->
      ContextSem T' G L.
  Proof using Type.
    intros T G L T' H H0 x t H1.
    destruct (H x t H1) as [V []].
    exists V. split; auto.
    eapply ValSem_extension_closed; eauto.
  Qed.

  Lemma ContextSem_kernel : forall T G L xs,
      ContextSem T G L ->
      (forall x : name, List.In x xs -> exists t : Typ, In_context_var G x t) ->
      exists L', build_new_kernel_L L xs = Some L'
                 /\ ContextSem T (build_new_kernel_context G xs) L'.
  Proof using Type.
    intros.
    generalize dependent G.
    induction xs; intros.
    - exists empty_Map. simpl. split; auto. intro. intros.
      exfalso. clear H H0. induction G; auto.
    - assert ((forall x : name, List.In x xs -> exists t : Typ, In_context_var G x t))
        by (intros; apply H0; right; assumption).
      specialize (IHxs _ H H1). clear H1. destruct IHxs as [L' []].
      simpl in *. remember (L#[a]). symmetry in Heqo. destruct o.
      + rewrite H1. exists (L'[a|->m]). split; auto. intro. intros.
        simpl in *.  remember (eqb_name a x). symmetry in Heqb. destruct b.
        * apply eqb_name_true in Heqb. subst. 
          specialize (H0 x (or_introl eq_refl)) as H5. destruct H5 as [t'].
          exists m. split; auto. specialize (H x t' H4). destruct H as [V []].
          rewrite H in Heqo. inversion Heqo. subst. 
          assert (In_context_var G x typ).
          { clear H H5 H4 Heqo m t' H2 H1 L L' H0. induction G; simpl in *; auto.
            remember (eqb_name n x). symmetry in Heqb. destruct b. 
            - simpl in *. apply eqb_name_true in Heqb.
              destruct H3; destruct H.
              + subst. left. split; auto.
              + exfalso. apply H. symmetry. assumption.
            - apply eqb_name_false in Heqb. right. split; auto. apply IHG.
              remember (List.find (fun y : name => eqb_name n y) xs).
              symmetry in Heqo. destruct o; simpl in *; auto.
              apply List.find_some in Heqo. destruct Heqo.
              apply eqb_name_true in H0. symmetry in H0. subst. destruct H3.
              + exfalso. destruct H0. apply Heqb. symmetry. assumption.
              + destruct H0. assumption. }
          pose proof Deterministic_context _ _ _ _ H4 H6. subst. assumption.
        * apply H2. clear Heqo m H0 H H2 H1 L'. induction G; simpl in *; auto.
          remember (eqb_name n a). symmetry in Heqb0. destruct b.
          -- remember (List.find (fun y : name => eqb_name n y) xs).
             symmetry in Heqo. destruct o.
             ++ apply List.find_some in Heqo. destruct Heqo. apply eqb_name_true in H0.
                symmetry in H0. subst. simpl in *. apply eqb_name_true in Heqb0.
                subst. destruct H3. 
                ** destruct H0. apply eqb_name_false in Heqb. exfalso. apply Heqb.
                   symmetry. assumption.
                ** destruct H0. right. split; auto.
             ++ simpl in *. apply eqb_name_true in Heqb0. subst. apply eqb_name_false in Heqb.
                destruct H3.
                ** destruct H. exfalso. apply Heqb. symmetry. assumption.
                ** destruct H. apply IHG. assumption.
          -- remember (List.find (fun y : name => eqb_name n y) xs).
             symmetry in Heqo. destruct o.
             ++ simpl in *. apply List.find_some in Heqo. destruct Heqo.
                apply eqb_name_true in H0. symmetry in H0. subst. apply eqb_name_false in Heqb0.
                destruct H3.
                ** destruct H0. subst. left. split; auto.
                ** destruct H0. right. split; auto.
             ++ apply IHG. assumption.
      + exfalso. specialize (H0 a (or_introl eq_refl)). destruct H0.
        specialize (H a x H0). destruct H as [V []].  rewrite H in Heqo.
        inversion Heqo.
  Qed.

  Lemma ContextSem_extend : forall T G L x t V,
      ContextSem T G L ->
      In_context_var G x t ->
      ValSem T t V ->
      ContextSem T G (L[x |-> V]).
  Proof using Type.
    intros. intros y t' H3. destruct (name_eq_dec x y).
    - subst. assert (t = t') by (eapply Deterministic_context; eauto).
      subst. exists V. simpl. rewrite eqb_name_refl. split; auto.
    - destruct (H y t' H3) as [W [H5 H4]].
      exists W. simpl. remember (eqb_name x y). destruct b.
      + exfalso. symmetry in Heqb. apply eqb_name_true in Heqb. subst. apply n.
        reflexivity.
      + split; auto.
  Qed.

  (*************************************)
  (* Well-formed machine memory spaces *)
  (*************************************)
  (* There is a definition of a global view of these objects and local to a
  particular base executor. *)
  Definition GlobalMachMemSpaces
    (T : MemSpaceTypings) (MM : MachMemSpaces) : Prop :=
    (forall M p, MM#[M,p] = None -> T#[M,p] = None)
    /\ (forall M p B,
           T#[M,p] = Some B ->
           forall n, exists V,
             MM#[M,p,n] = Some V /\ ValSem T (Base (projT1 B) (projT2 B)) V).
  (* INVESTIGATE : Note Amal's thesis may have an error in this case. She says
   (definition 3.5) that Dom(Psi) incl Dom(S) and they need not be
   equal. However, in the case of new allocations, we must show that l not in
   Dom(S) implies l not in Dom(Psi). In Lemma 3.23 part 7, Amal gets l not in
   Dom(Psi) without proof, but it may need to be done here. Her thesis defines
   this same concept in CiC in Figure 5.3. Below is how I would expect it to be
   defined given definition 3.5.

   Here are two separate definitions, one with Dom(MM) incl Dom(T) and the other
   with Dom(T) incl Dom(MM)

    forall M p n V, MM#[M,p,n] = Some V -> exists B, T#[M,p] = Some B /\ ValSem
        T (Base (projT1 B) (projT2 B)) V.

    forall M p n B, T#[M,p] = Some B -> exists V, MM#[M,p,n] = Some V /\ ValSem
      T (Base (projT1 B) (projT2 B)) V.

   *)
  (* TODO : Fix error in definition in the appendix of Vivekfest; the value
  relation needs to occur for a specific world. *)

  Lemma GlobalMachMemSpaces_join_restriction : forall T MM P,
      GlobalMachMemSpaces T MM ->
      GlobalMachMemSpaces T
        (join (restrict MM (fun M : BMs F => negb (P M)))
           (restrict MM (fun M : BMs F => P M))).
  Proof using Type.
    intros. split; intros.
    - destruct H. apply H. simpl in H0.
      remember (P M). destruct b; simpl in H0; auto.
      remember (MM#[M]). destruct o; auto.
    - destruct H. specialize (H1 M p B H0 n).
      destruct H1 as [V []]. exists V. simpl.
      remember (P M). destruct b; simpl; split; auto.
      destruct (MM#[M]); auto.
  Qed.

  Lemma GlobalMachMemSpaces_extension :
    forall T MM Ms p (B : {bty : Set & Bt F bty}) (c : projT1 B),
      GlobalMachMemSpaces T MM ->
      GlobalMachMemSpaces
        (T [Ms, p |-> B])
        (MM [Ms, p |-> default_Map (BaseVal (projT1 B) (projT2 B) c)]).
  Proof using Type.
    intros. split.
    - intros Ms' p' H0. simpl in H0.
      remember (eqb Ms' Ms). destruct b.
      + symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
        remember (MM#[Ms]). destruct o.
        * simpl in *. rewrite eqb_refl. remember (T#[Ms]). destruct o.
          -- simpl. remember (eqb_name p p'). destruct b; [inversion H0|].
             apply proj1 in H. specialize (H Ms p'). rewrite <- Heqo in H.
             specialize (H H0). rewrite <- Heqo0 in H. assumption.
          -- simpl. remember (eqb_name p p'). destruct b; [inversion H0|].
             reflexivity.
        * simpl in *. rewrite eqb_refl. remember (T#[Ms]). destruct o.
          -- simpl. remember (eqb_name p p'). destruct b; [inversion H0|].
             apply proj1 in H. specialize (H Ms p'). rewrite <- Heqo in H.
             specialize (H H0). rewrite <- Heqo0 in H. assumption.
          -- simpl. remember (eqb_name p p'). destruct b; [inversion H0|].
             reflexivity.
      + simpl. symmetry in Heqb. rewrite Heqb. destruct H. apply H.
        assumption.
    - intros Ms' p' B' H0 n. simpl in *.
      remember (eqb Ms' Ms). destruct b.
      + symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
        remember (MM#[Ms]). destruct o; simpl.
        * remember (eqb_name p p'). destruct b; simpl.
          -- exists (BaseVal (projT1 B) (projT2 B) c). split; auto.
             remember (T#[Ms]). destruct o; simpl in *; rewrite <- Heqb in H0; inversion H0; reflexivity.
          -- remember (T#[Ms]). destruct o; simpl in *; rewrite <- Heqb in H0.
             ++ apply proj2 in H. specialize (H Ms p' B').
                rewrite <- Heqo0 in H. specialize (H H0 n). destruct H as [V []]. exists V.
                rewrite <- Heqo in H. split; auto.
             ++ apply proj2 in H. specialize (H Ms p' B').
                rewrite <- Heqo0 in H. specialize (H H0 n). destruct H as [V []]. exists V.
                rewrite <- Heqo in H. split; auto.
        * remember (eqb_name p p'). destruct b; simpl.
          -- exists (BaseVal (projT1 B) (projT2 B) c). split; auto.
             remember (T#[Ms]). destruct o; simpl in *; rewrite <- Heqb in H0; inversion H0; reflexivity.
          -- remember (T#[Ms]). destruct o; simpl in *; rewrite <- Heqb in H0.
             ++ apply proj2 in H. specialize (H Ms p' B').
                rewrite <- Heqo0 in H. specialize (H H0 n). destruct H as [V []]. exists V.
                rewrite <- Heqo in H. split; auto.
             ++ apply proj2 in H. specialize (H Ms p' B').
                rewrite <- Heqo0 in H. specialize (H H0 n). destruct H as [V []]. exists V.
                rewrite <- Heqo in H. split; auto.
      + destruct H. apply H1. assumption.
  Qed.

  Definition LocalMachMemSpaces
    (T : MemSpaceTypings) (MM : MachMemSpaces) (X : BX F) : Prop :=
    (forall M p,
        comp_acc_rel F X M = true ->
        MM#[M,p] = None ->
        T#[M,p] = None)
    /\ (forall M p B,
           T#[M,p] = Some B ->
           comp_acc_rel F X M = true ->
           forall n, exists V,
             MM#[M,p,n] = Some V /\ ValSem T (Base (projT1 B) (projT2 B)) V).

  Lemma GlobalMachMemSpaces_restriction : forall T MM X,
      GlobalMachMemSpaces T MM ->
      LocalMachMemSpaces T (restrict MM (fun M : BMs F => comp_acc_rel F X M)) X.
  Proof using Type.
    intros. split; intros.
    - simpl in H1. rewrite H0 in H1. apply (proj1 H); auto.
    - apply proj2 in H. specialize (H M p B H0 n).
      destruct H as [V []]. exists V. split; auto.
      simpl. rewrite -> H1. assumption.
  Qed.

  Lemma LocalMachMemSpaces_update_with_well_behavied : forall T MM X M p B n V,
      LocalMachMemSpaces T MM X ->
      T#[M,p] = Some B ->
      ValSem T (Base (projT1 B) (projT2 B)) V ->
      LocalMachMemSpaces T (MM [M, p, n |-> V]) X.
  Proof using Type.
    intros. split.
    - intros M' p' H2 H3. simpl in H3.
      remember (eqb M' M). destruct b.
      + symmetry  in Heqb. apply eqb_leibniz in Heqb. subst.
        remember (MM#[M]). destruct o.
        * simpl in H3. remember (eqb_name p' p). destruct b.
          -- symmetry in Heqb. apply eqb_name_true in Heqb. subst.
             remember (m#[p]). destruct o; inversion H3.
          -- apply proj1 in H. specialize (H M p' H2).
             rewrite <- Heqo in H. apply H. assumption.
        * simpl in H3. remember (eqb_name p' p). destruct b; inversion H3.
          pose proof (proj1 H M p' H2). rewrite <- Heqo in H4. apply H4.
          reflexivity.
      + apply (proj1 H); auto.
    - intros M' p' B' H2 H3 n'.
      simpl. remember (eqb M' M). destruct b.
      + symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
        remember (MM#[M]). destruct o; simpl.
        * remember (eqb_name p' p). destruct b.
          -- symmetry in Heqb. apply eqb_name_true in Heqb. subst.
             rewrite H0 in H2. inversion H2. subst.
             remember (m#[p]). destruct o; simpl.
             ++ remember (Nat.eqb n n'). destruct b.
                ** exists V. split; auto.
                ** pose proof (proj2 H M p B' H0 H3 n').
                   rewrite <- Heqo in H4. rewrite <- Heqo0 in H4.
                   apply H4.
             ++ remember (Nat.eqb n n'). destruct b.
                ** exists V. split; auto.
                ** pose proof (proj2 H M p B' H0 H3 n').
                   rewrite <- Heqo in H4. rewrite <- Heqo0 in H4.
                   apply H4.
          -- pose proof (proj2 H M p' B' H2 H3 n').
             rewrite <- Heqo in H4. apply H4.
        * remember (eqb_name p' p). destruct b.
          -- symmetry in Heqb. apply eqb_name_true in Heqb. subst.
              simpl. remember (Nat.eqb n n'). destruct b.
             ++ exists V. split; auto. rewrite H0 in H2. inversion H2.
                subst. destruct V; [|contradiction]. destruct B'. simpl in *.
                assumption. 
             ++ pose proof (proj2 H M p B' H2 H3 n').
                rewrite <- Heqo in H4. destruct H4 as [V' []]. inversion H4.
          -- pose proof (proj2 H M p' B' H2 H3 n').
             rewrite <- Heqo in H4. destruct H4 as [V' []]. inversion H4.
      + apply (proj2 H); auto.
  Qed.

  (*******************************)
  (* Expression meaning of types *)
  (*******************************)
  Definition ExprSem
    (T : MemSpaceTypings) (typ : Typ) (L : LocalMem) (E : Expr) (X : BX F) : Prop :=
    forall T' MM,
      Acc T T' ->
      LocalMachMemSpaces T' MM X ->
      exists V, ExprEval (MM,L,E) V /\ ValSem T' typ V.

  Lemma ExprSem_extension_closed : forall T t L E X T',
      ExprSem T t L E X ->
      Acc T T' ->
      ExprSem T' t L E X.
  Proof using Type.
    intros. intro T''. intros.
    assert (Acc T T'') by (eapply Acc_trans; eauto).
    apply H; auto.
  Qed. 

  (*************************************)
  (* Meaning of well-behaved statments *)
  (*************************************)
  Fixpoint StmtSem
    (n : nat) (T : MemSpaceTypings) (L : LocalMem) (S : Stmt) (X : BX F) : Prop :=
    forall T' MM,
      Acc T T' ->
      LocalMachMemSpaces T' MM X ->
      Final_BXState (MM,L,S)
      \/ exists MM' L' S',
          BXStep (MM,L,S) (MM',L',S')
          /\ LocalMachMemSpaces T' MM' X
          /\ (match n with | 0 => True | S n' => StmtSem n' T' L' S' X end).

  Lemma StmtSem_extension_closed : forall n T L S X T',
      StmtSem n T L S X ->
      Acc T T' ->
      StmtSem n T' L S X.
  Proof using Type.
    intros. induction n; simpl; intros T''; intros; apply H; auto;
      eapply Acc_trans; eauto.
  Qed. 
  
  (* This is also Kripke property *)
  Lemma StmtSem_fewer_steps : forall n T L St X,
      StmtSem (S n) T L St X ->
      StmtSem n T L St X.
  Proof using Type.
    intros n. induction n; intros.
    - intros T' MM HAcc H0. specialize (H T' MM HAcc H0). destruct H.
      + left. assumption.
      + right. destruct H as [MM' [L' [S' []]]]. destruct H1.
        exists MM'. exists L'. exists S'. split; auto.
    - intros T' MM HAcc H0. specialize (H T' MM HAcc H0). destruct H.
      + left. assumption.
      + right. destruct H as [MM' [L' [S' []]]]. destruct H1.
        exists MM'. exists L'. exists S'. split; auto.
  Qed.

  Lemma StmtSem_step_closed : forall n T L St X MM t,
      StmtSem (S n) T L St X ->
      LocalMachMemSpaces T MM X ->      
      BXStep (MM,L,St) t ->
      exists MM' L' St',
        t = (MM',L',St')
        /\ LocalMachMemSpaces T MM' X
        /\ StmtSem n T L' St' X.
  Proof using Type.
    intros. destruct (H T MM (Acc_refl T) H0).
    - exfalso. inversion H2. destruct H3. inversion H3. subst. inversion H1.
    - destruct H2 as [MM' [L' [S' [H2 H3]]]].
      pose proof Deterministic_BXStep _ _ H1 _ H2. destruct t. destruct p. inversion H4.
      subst. destruct H3. exists MM'. exists L'. exists S'. split; auto.
  Qed.

  (* Safe_kernel_pop and Safe_kernel_step are the concurrent machine
     transitions that may occur at any time in the BX0 machine. *)
  Lemma StmtSem_step_preserves_GlobalMachMemspaces : forall n T X L St MM MM' L' St',
      GlobalMachMemSpaces T MM ->
      StmtSem (S n) T L St X ->
      BXStep (restrict MM (comp_acc_rel F X),L,St) (MM',L',St') ->
      GlobalMachMemSpaces T (join (restrict MM (fun M : BMs F => negb (comp_acc_rel F X M))) MM').
  Proof using Type.
    intros step T X L St MM MM' L' St' H H0 H1.
    split.
    - intros.
      pose proof GlobalMachMemSpaces_restriction T MM X H.
      eapply StmtSem_step_closed in H1; eauto.
      destruct H1 as [MM'' [L'' [St'' [H1 []]]]].
      symmetry in H1. inversion H1. subst. clear H1.
      simpl in H2. remember (comp_acc_rel F X M). destruct b; simpl in H2.
      + apply proj1 in H4. symmetry in Heqb.
        exact (H4 M p Heqb H2).
      + remember (MM#[M]). destruct o.
        * apply proj1 in H. pose proof (H M p). rewrite <- Heqo in H1.
          exact (H1 H2).
        * apply proj1 in H. specialize (H M p). rewrite <- Heqo in H.
          apply H. reflexivity.
    - intros M p n B H2.
      pose proof GlobalMachMemSpaces_restriction T MM X H.
      eapply StmtSem_step_closed in H0; eauto.
      destruct H0 as [MM'' [L'' [St'' [H5 [H6 H7]]]]]. symmetry in H5. inversion H5. subst.
      remember (comp_acc_rel F X M). symmetry in Heqb.
      destruct b.
      + simpl. destruct (proj2 H6 M p n B Heqb H2). exists x. simpl in H0. rewrite -> Heqb. simpl. assumption.
      + simpl. rewrite -> Heqb. simpl. pose proof (proj2 H M p n B H2). destruct H0. destruct H0.
        exists x. remember (MM#[M]). destruct o. split; auto. inversion H0.
  Qed.

  (**************************)
  (* Meaning of work queues *)
  (**************************)
  Definition SSSem
    (T : MemSpaceTypings) (SS : BXSpaceQueues) : Prop :=
    forall X, (exists ff, SS#[X] = Some ff)
              /\ (forall ff n, SS#[X] = Some ff -> Forall_Fifo (fun W => StmtSem n T (fst W) (snd W) X) ff).

  Lemma SSSem_extension_closed : forall T SS T',
      SSSem T SS ->
      Acc T T' ->
      SSSem T' SS.
  Proof using Type.
    intros. intro. destruct (H X).
    split; auto. intros. specialize (H2 ff n H3).
    assert (forall (W : LocalMem * Stmt),
               (fun W : LocalMem * Stmt => StmtSem n T (fst W) (snd W) X) W ->
               (fun W : LocalMem * Stmt => StmtSem n T' (fst W) (snd W) X) W)
      by (intros; eapply StmtSem_extension_closed; eauto).
    exact (Forall_Fifo_weaken _ _ ff H2 H4).
  Qed. 

  Lemma SSSem_pop_closed : forall T SS X ff,
      SSSem T SS ->
      SS#[X] = Some ff ->
      SSSem T (SS[X |-> pop ff]).
  Proof using Type.
    intros. intro X'. specialize (H X'). destruct H as [[ff']].
    remember (eqb X X').
    destruct b; simpl in *; rewrite <- Heqb; split; intros; auto.
    - exists (pop ff). reflexivity.
    - inversion H2. subst. apply Forall_Fifo_pop. symmetry in Heqb. apply eqb_leibniz in Heqb.
      subst. apply H1. assumption.
    - exists ff'. assumption.
  Qed.

  Lemma SSSem_step_closed : forall T SS X ff L St MM MM' L' St',
      SSSem T SS ->
      SS#[X] = Some ff ->
      peek ff = Some (L,St) ->
      LocalMachMemSpaces T MM X ->
      BXStep (MM,L,St) (MM',L',St') ->
      SSSem T (SS[X |-> push (pop ff) (L',St')]).
  Proof using Type.
    intros. intro X'.
    remember (eqb X X').
    destruct b; split; simpl in *; intros.
    - rewrite <- Heqb. exists (push (pop ff) (L', St')). reflexivity.
    - rewrite <- Heqb in H4. inversion H4.
      symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
      specialize (H X'). destruct H. specialize (H5 ff (S n) H0).
      apply Forall_Fifo_push; [apply Forall_Fifo_pop; auto|].
      + apply Forall_Fifo_weaken
          with (P := fun W : LocalMem * Stmt => StmtSem (S n) T (fst W) (snd W) X')
               (Q := fun W : LocalMem * Stmt => StmtSem n T (fst W) (snd W) X'); auto.
        intros. apply StmtSem_fewer_steps. assumption.
      + pose proof (Forall_Fifo_peek _ _ _ H5 H1). simpl in H6.
        destruct (H6 T MM (Acc_refl T) H2).
        * exfalso. eapply Final_BXState_is_stuck; eauto.
        * simpl. destruct H7 as [MM'' [L'' [S'' []]]].
          destruct H8. pose proof Deterministic_BXStep _ _ H7 _ H3. inversion H10.
          subst. assumption.
    - rewrite <- Heqb. destruct (H X'). assumption.
    - rewrite <- Heqb in H4. destruct (H X'). apply H6; auto.
  Qed.

  Fixpoint find_work (ffs : list (Fifo (LocalMem * Stmt))) : option (LocalMem * Stmt) :=
    match ffs with
    | nil => None
    | cons ff ffs' =>
        match find_work ffs' with
        | None => peek ff
        | Some W => Some W
        end
    end.

  Lemma SS_decide_remaining_work :
    forall T (SS : BXSpaceQueues),
      SSSem T SS ->
      (exists (X : BX F) ff L S,
          SS#[X] = Some ff /\ peek ff = Some (L,S))
      \/ (forall X, SS#[X] = Some empty_Fifo).
  Proof using Type.
    intros.
    assert (forall X, {SS#[X] = Some empty_Fifo} + {~ SS#[X] = Some empty_Fifo}).
    { intros. destruct (SS#[X]).
      -  pose proof (dec_empty_Fifo f). destruct H0.
         + subst. left. reflexivity.
         + right. intro. apply n. inversion H0. reflexivity.
      - right. intro. inversion H0. }
    pose proof (List.Forall_Exists_dec _ H0 (BX_elems F)). clear H0.
    destruct H1.
    - right. intros.
      destruct (List.Forall_forall (fun X : BX F => (SS #[ X]) = Some empty_Fifo) (BX_elems F)).
      clear H1. specialize (H0 f X).
      apply H0. apply BX_elems_full.
    - left. apply List.Exists_exists in e. destruct e as [X []]. exists X. 
      remember (SS#[X]). destruct o as [ff|].
      + exists ff. remember (peek ff). destruct o as [[L S]|].
        * exists L, S. split; auto.
        * exfalso. symmetry in Heqo0. pose proof (peek_empty_None_only ff Heqo0).
          subst. apply H1. reflexivity.
      + exfalso. destruct (H X). destruct H2 as [ff'].
        rewrite <- Heqo in H2. inversion H2.
  Qed.

  (*******************************************************)
  (* Meaning of well-behavied initial executor statments *)
  (*******************************************************)
  Fixpoint BX0StmtSem
    (n : nat) (T : MemSpaceTypings) (L : LocalMem) (S : Stmt) : Prop :=
    forall MM SS,
      GlobalMachMemSpaces T MM ->
      SSSem T SS ->
      Final_BX0State (MM,SS,L,S)
      \/ (forall MM' SS' L' S',
             BX0Step (MM,SS,L,S) (MM',SS',L',S') ->
             exists T',
               Acc T T'
               /\ GlobalMachMemSpaces T' MM'
               /\ SSSem T' SS'
               /\ (match n with | 0 => True | S n' => BX0StmtSem n' T' L' S' end))
         /\ (exists s, BX0Step (MM,SS,L,S) s).

  Lemma BX0StmtSem_step_closed : forall n T L St MM SS t,
      BX0StmtSem (S n) T L St ->
      GlobalMachMemSpaces T MM ->
      SSSem T SS ->
      BX0Step (MM,SS,L,St) t ->
      exists T' MM' SS' L' St',
        t = (MM',SS',L',St')
        /\ Acc T T'
        /\ GlobalMachMemSpaces T' MM'
        /\ SSSem T' SS'
        /\ BX0StmtSem n T' L' St'.
  Proof using Type.
    intros. destruct (H MM SS H0 H1).
    - exfalso. eapply Final_BX0State_is_stuck; eauto.
    - fold BX0StmtSem in H3. destruct H3.
      destruct t as [[[MM' SS'] L'] S'].
      specialize (H3 MM' SS' L' S' H2). destruct H3 as [T' [Ac [Gl [SSSS]]]].
      exists T', MM', SS', L', S'. split; auto.
  Qed.

  (*******************************)
  (* Meaning of Typing Judgments *)
  (*******************************)
  Definition Expr_sem_entail
    (G : context) (E : Expr) (typ : Typ) (X : BX F) : Prop :=
    forall T L,
      ContextSem T G L ->
      ExprSem T typ L E X.

  (* TODO, the following two definitions are different than Vivekfest in
  that we know extra information for BX0, not less. *)
  Definition Stmt_sem_entail
    (G : context) (S : Stmt) (X : BX F) : Prop :=
    forall n T L,
      ContextSem T G L ->
      (X <> BX0 F -> StmtSem n T L S X) /\
        (X = BX0 F -> BX0StmtSem n T L S).

  Definition Cmd_sem_entail
    (G : context) (C : Cmd) (X : BX F) : Prop :=
    forall S,
      Stmt_sem_entail G S X ->
      Stmt_sem_entail G (SCom C S) X.

  (****************************************************************************)
  (*                              Type Soundess                               *)
  (****************************************************************************)
  Theorem ExprTyping_soundness : forall G E typ (X : BX F),
      Based_context G ->
      Based_Typ typ ->
      ExprTyping G E typ (XBase _ X) ->
      Expr_sem_entail G E typ X.
  Proof using Type.
    intros. remember (XBase (BX F) X) as atX.
    induction H1; unfold Expr_sem_entail; intros; unfold ExprSem; intros.
    - destruct (H2 x t H1) as [V []].
      exists V. split; [|eapply ValSem_extension_closed; eauto].
      apply EvalVar. assumption.
    - assert (Based_Typ (Base nat (Bt_nat F))) by (simpl; constructor).
      destruct (IHExprTyping H7 HeqatX T L H4 T' MM H5 H6) as [Vn []].
      assert (exists M, S = MsBase _ M).
      + clear H9 Vn H7 MM H8 H6 H5 MM H4 L T IHExprTyping H3 H2.
        induction G; simpl in *; try contradiction. destruct H1.
        * destruct H1. subst. destruct H. destruct S; simpl in *; try contradiction.
          exists b. reflexivity.
        * apply IHG.
          -- destruct H. assumption.
          -- destruct H1. assumption.
      + destruct H10 as [M H10]. destruct (H4 x _ H1) as [Vv []].
        unfold ValSem in H12. rewrite -> H10 in H12.
        destruct Vv; try (subst; contradiction). destruct H12. symmetry in H12. subst.
        destruct Vn; try (subst; contradiction). simpl in H9. subst.
        assert (comp_acc_rel F X M = true) by (eapply Accessible_base; eauto).
        destruct H13 as [typ []]. subst.
        assert ((T' #[ M, p]) = Some typ) by (apply H5; auto).
        destruct ((proj2 H6) M p typ H12 H9 c) as [V [H14 H15]].
        (* destruct (H6 M p c typ H12 H9) as [V [H14 H15]]. *)
        exists V. split.
        * eapply EvalViewDeref; eauto.
          assert (b = Bt_nat F) by (apply proof_irrelevance).
          rewrite -> H13 in H8. apply H8.
        * assert (btyP = projT2 typ) by (apply proof_irrelevance).
          rewrite -> H13. assumption.
    - exists (BaseVal bty btyP c). split.
      + apply EvalConst.
      + simpl. reflexivity.
    - destruct (IHExprTyping1 H0 HeqatX T L H1 T' MM H2 H3) as [V0 []].
      destruct (IHExprTyping2 H0 HeqatX T L H1 T' MM H2 H3) as [V1 []].
      exists V0. split; auto. destruct V0,V1; simpl in *; try contradiction.
      subst. pose proof proof_irrelevance (Bt F bty1) b b0. subst.
      eapply EvalOp; eauto.
  Qed.

  Theorem WfStmt_WfCmd_soundess : forall G S (X : BX F),
      WfStmt G S (XBase (BX F) X) ->
      Based_context G ->
      Based_Stmt S ->
      Stmt_sem_entail G S X.
  Proof using Type.
    intros G S X H.
    remember (XBase (BX F) X) as atX.
    generalize dependent HeqatX.
    generalize dependent X.
    generalize dependent atX.
    generalize dependent S.
    generalize dependent G.
    intros G S E H.
    apply WfStmt_WfCmd_ind with
      (P := (fun (c : context) (cmd : Cmd) (e : executor (BX F)) (_ : WfCmd c cmd e) =>
               forall X, e = XBase (BX F) X -> Based_context c -> Based_Cmd cmd -> Cmd_sem_entail c cmd X))
      (P0 := (fun (c : context) (s : Stmt) (e : executor (BX F)) (_ : WfStmt c s e) =>
                forall X, e = XBase (BX F) X -> Based_context c -> Based_Stmt s -> Stmt_sem_entail c s X));
      auto; subst; clear H E S G; intros; subst.

    (* CSetVar *)
    - pose proof (Based_context_implies_Based_Typ G x t H0 i).
      apply ExprTyping_soundness in e; auto.
      intros S H3 step T L H4.
      split; intros.
      + induction step; simpl; intros; right;
          exists MM;
          destruct (e T L H4 T' MM H5 H6) as [V []];
          exists (L[x |-> V]);
          exists S; (split; [|split]); auto.
        * apply XSetVar; auto. destruct (H4 x t i) as [W []].
          eexists; eauto.
        * apply XSetVar; auto. destruct (H4 x t i) as [W []].
          eexists; eauto.
        * apply H3; auto. eapply ContextSem_extend; eauto.
          eapply ContextSem_extension_closed; eauto.
      + induction step; simpl; intros; right; split; intros.
        * exists T. split; [apply Acc_refl|]. subst. inversion H7; subst.
          -- inversion H8; subst. split; [|split]; auto.
             apply GlobalMachMemSpaces_join_restriction; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H6 X) as [SSexists SSany].
                specialize (SSany ff 1).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed with (5 := H17); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
            by (apply GlobalMachMemSpaces_restriction; auto).
          subst.
          specialize (e T L H4 _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H7).
          destruct e as [V []].
          exists (join (restrict MM (fun Ms : BMs F => negb (comp_acc_rel F (BX0 F) Ms)))
            (restrict MM (comp_acc_rel F (BX0 F))),SS,L[x |-> V],S).
          apply X0Step. apply XSetVar; auto.
          destruct (H4 x t i) as [V_old [H14 H15]].
          exists V_old; assumption.
        * exists T. split; [apply Acc_refl|]. subst. inversion H7; subst.
          -- inversion H8; subst. split; [|split]; auto.
             apply GlobalMachMemSpaces_join_restriction; auto.
             apply H3; auto. eapply ContextSem_extend; eauto.
             assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
               by (apply GlobalMachMemSpaces_restriction; auto).
             specialize (e T L H4 _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H2).
             destruct e as [V []]. 
             pose proof (Deterministic_ExprEval _ _ H9 _ H17). subst. assumption.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H6 X) as [SSexists SSany].
                specialize (SSany ff 1).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed with (5 := H17); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
            by (apply GlobalMachMemSpaces_restriction; auto).
          subst.
          specialize (e T L H4 _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H7).
          destruct e as [V []].
          exists (join (restrict MM (fun Ms : BMs F => negb (comp_acc_rel F (BX0 F) Ms)))
            (restrict MM (comp_acc_rel F (BX0 F))),SS,L[x |-> V],S).
          apply X0Step. apply XSetVar; auto.
          destruct (H4 x t i) as [V_old [H14 H15]].
          exists V_old; assumption.

    (* CSetView *)
    - apply ExprTyping_soundness in e0; auto.
      apply ExprTyping_soundness in e; auto.
      rename S into Ms.
      intro S. intros H3 step T L H4. split; intro.
      + induction step; simpl; intros; right.
        * destruct (e T L H4 _ MM H2 H5) as [V0 [E0_eval E0_valsem]].
          simpl in E0_valsem. destruct V0 as [natty nattyP n|]; [| contradiction]. subst.
          destruct (e0 T L H4 _ MM H2 H5) as [V1 [E1_eval E1_valsem]].
          simpl in E1_valsem. destruct V1 as [bty' bty'P c|]; [| contradiction]. subst.
          destruct (H4 x _ i) as [Vp [x_lookup x_valsem]].
          simpl in x_valsem. destruct Ms; [| contradiction].
          destruct Vp as [|BMs']; [contradiction|].
          destruct x_valsem as [Eqb [B [T_lookup Eq_proj]]]. subst.
          exists (MM[BMs',p,n |-> BaseVal _ btyP c]), L, S. split; [|split]; auto.
          -- apply XSetView; auto.
             ++ assert (comp_acc_rel F X0 BMs' = true) by (eapply Accessible_base; eauto).
                assert (T'#[ BMs', p] = Some B) as T'_lookup by (apply H2; auto).
                destruct ((proj2 H5) BMs' p B T'_lookup H6 n) as [Vb []]. exists Vb. assumption.
             ++ assert (nattyP = Bt_nat F) by (apply proof_irrelevance).
                subst. assumption.
             ++ assert (btyP = bty'P) by (apply proof_irrelevance).
                subst. assumption.
          -- eapply LocalMachMemSpaces_update_with_well_behavied; eauto. simpl. reflexivity.
        * destruct (e T L H4 _ MM H2 H5) as [V0 [E0_eval E0_valsem]].
          simpl in E0_valsem. destruct V0 as [natty nattyP n|]; [| contradiction]. subst.
          destruct (e0 T L H4 _ MM H2 H5) as [V1 [E1_eval E1_valsem]].
          simpl in E1_valsem. destruct V1 as [bty' bty'P c|]; [| contradiction]. subst.
          destruct (H4 x _ i) as [Vp [x_lookup x_valsem]].
          simpl in x_valsem. destruct Ms; [| contradiction].
          destruct Vp as [|BMs']; [contradiction|].
          destruct x_valsem as [Eqb [B [T_lookup Eq_proj]]]. subst.
          exists (MM[BMs',p,n |-> BaseVal _ btyP c]), L, S. split; [|split]; auto.
          -- apply XSetView; auto.
             ++ assert (comp_acc_rel F X0 BMs' = true) by (eapply Accessible_base; eauto).
                assert (T'#[ BMs', p] = Some B) as T'_lookup by (apply H2; auto).
                destruct ((proj2 H5) BMs' p B T'_lookup H6 n) as [Vb []]. exists Vb. assumption.
             ++ assert (nattyP = Bt_nat F) by (apply proof_irrelevance).
                subst. assumption.
             ++ assert (btyP = bty'P) by (apply proof_irrelevance).
                subst. assumption.
          -- eapply LocalMachMemSpaces_update_with_well_behavied; eauto. simpl. reflexivity.
          -- apply H3; auto. eapply ContextSem_extension_closed; eauto.
      + subst. induction step; simpl; intros; right.
        * destruct (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T))
            as [V0 [H13 H14]]; [apply GlobalMachMemSpaces_restriction; auto|].
          simpl in H14. destruct V0 as [nat' natP n|]; [|contradiction]. subst.
          destruct (e0 T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T))
            as [V1 [H15 H16]]; [apply GlobalMachMemSpaces_restriction; auto|].
          simpl in H16. destruct V1 as [bty' bty'P c|]; [|contradiction]. subst.
          destruct (H4 x _ i) as [Vp [H16 H17]]. simpl in H17.
          destruct Ms as [|BMs']; [|contradiction]. destruct Vp as [| BMs]; [contradiction|].
          destruct H17. destruct H6 as [W []]. subst.
          assert (comp_acc_rel F (BX0 F) BMs = true) by (eapply Accessible_base; eauto).
          split.
          -- intros. exists T. split; [apply Acc_refl|]. inversion H7; subst.
             ++ inversion H9; subst.
                pose proof (Deterministic_ExprEval _ _ H23 _ H13). inversion H8.
                apply EqdepTheory.inj_pair2 in H11. subst.
                pose proof (Deterministic_ExprEval _ _ H24 _ H15). subst.
                rewrite H16 in H14. inversion H14. subst.
                split; [|split]; auto.
                assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                  by (apply GlobalMachMemSpaces_restriction; auto).
                remember (BaseVal (projT1 W) bty'P c) as V.
                assert (ValSem T (Base (projT1 W) (projT2 W)) V).
                { unfold ValSem. destruct V; inversion HeqV; auto. }
                pose proof (LocalMachMemSpaces_update_with_well_behavied T
                              (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F) M p0 W n
                              V H10 H6 H11).
                split.
                ** intros BMs' p' H30.
                   pose proof (proj1 H12 BMs' p').
                   simpl in H30.
                   remember (comp_acc_rel F (BX0 F) BMs'). destruct b; simpl in H30.
                   --- specialize (H17 eq_refl). simpl in H17. rewrite <- Heqb in H17.
                       specialize (H17 H30). assumption.
                   --- apply (proj1 H BMs' p'). remember (MM#[BMs']). destruct o; auto. 
                ** intros BMs' p' B' H30 n'.
                   remember (comp_acc_rel F (BX0 F) BMs').
                   destruct b; simpl.
                   --- symmetry in Heqb. pose proof ((proj2 H12) BMs' p' B' H30 Heqb n').
                       simpl in H17. rewrite Heqb in H17. rewrite Heqb. simpl.
                       assumption.
                   --- symmetry in Heqb. rewrite Heqb. simpl.
                       pose proof ((proj2 H) BMs' p' B' H30 n'). destruct H17 as [V' []].
                       exists V'. split; auto.
                       destruct (MM #[ BMs']); auto. inversion H17.
             ++ split; auto. split; [apply SSSem_pop_closed; auto|auto].
             ++ split; [|split]; auto.
                ** eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                   destruct (H2 X) as [ffexists ffany].
                   specialize (ffany ff 1 H11).
                   apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
                ** eapply SSSem_step_closed with (5 := H21); eauto.
                   apply GlobalMachMemSpaces_restriction; auto.
          -- eexists. eapply X0Step. eapply XSetView; eauto.
             ++ pose proof (proj2 H BMs p W H6 n). destruct H7 as [V []].
                exists V. simpl. rewrite H5. apply H7.
             ++ assert (natP = Bt_nat F) by (apply proof_irrelevance).
                subst. assumption.
        * destruct (e T L H4 _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T))
            as [V0 [H13 H14]]; [apply GlobalMachMemSpaces_restriction; auto|].
          simpl in H14. destruct V0 as [nat' natP n|]; [|contradiction]. subst.
          destruct (e0 T L H4 _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T))
            as [V1 [H15 H16]]; [apply GlobalMachMemSpaces_restriction; auto|].
          simpl in H16. destruct V1 as [bty' bty'P c|]; [|contradiction]. subst.
          destruct (H4 x _ i) as [Vp [H16 H17]]. simpl in H17.
          destruct Ms as [|BMs']; [|contradiction]. destruct Vp as [| BMs]; [contradiction|].
          destruct H17. destruct H6 as [W []]. subst.
          assert (comp_acc_rel F (BX0 F) BMs = true) by (eapply Accessible_base; eauto).
          split.
          -- intros. exists T. split; [apply Acc_refl|]. inversion H7; subst.
             ++ inversion H9; subst.
                pose proof (Deterministic_ExprEval _ _ H23 _ H13). inversion H8.
                apply EqdepTheory.inj_pair2 in H11. subst.
                pose proof (Deterministic_ExprEval _ _ H24 _ H15). subst.
                rewrite H16 in H14. inversion H14. subst.
                split; [|split]; auto.
                assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                  by (apply GlobalMachMemSpaces_restriction; auto).
                remember (BaseVal (projT1 W) bty'P c) as V.
                assert (ValSem T (Base (projT1 W) (projT2 W)) V).
                { unfold ValSem. destruct V; inversion HeqV; auto. }
                pose proof (LocalMachMemSpaces_update_with_well_behavied T
                              (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F) M p0 W n
                              V H10 H6 H11).
                split.
                ** intros BMs' p' H30.
                   pose proof (proj1 H12 BMs' p').
                   simpl in H30.
                   remember (comp_acc_rel F (BX0 F) BMs'). destruct b; simpl in H30.
                   --- specialize (H17 eq_refl). simpl in H17. rewrite <- Heqb in H17.
                       specialize (H17 H30). assumption.
                   --- apply (proj1 H BMs' p'). remember (MM#[BMs']). destruct o; auto. 
                ** intros BMs' p' B' H30 n'.
                   remember (comp_acc_rel F (BX0 F) BMs').
                   destruct b; simpl.
                   --- symmetry in Heqb. pose proof ((proj2 H12) BMs' p' B' H30 Heqb n').
                       simpl in H17. rewrite Heqb in H17. rewrite Heqb. simpl.
                       assumption.
                   --- symmetry in Heqb. rewrite Heqb. simpl.
                       pose proof ((proj2 H) BMs' p' B' H30 n'). destruct H17 as [V' []].
                       exists V'. split; auto.
                       destruct (MM #[ BMs']); auto. inversion H17.
                ** apply H3; auto.
             ++ split; auto. split; [apply SSSem_pop_closed; auto|auto].
             ++ split; [|split]; auto.
                ** eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                   destruct (H2 X) as [ffexists ffany].
                   specialize (ffany ff 1 H11).
                   apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
                ** eapply SSSem_step_closed with (5 := H21); eauto.
                   apply GlobalMachMemSpaces_restriction; auto.
          -- eexists. eapply X0Step. eapply XSetView; eauto.
             ++ pose proof (proj2 H BMs p W H6 n). destruct H7 as [V []].
                exists V. simpl. rewrite H5. apply H7.
             ++ assert (natP = Bt_nat F) by (apply proof_irrelevance).
                subst. assumption.

    (* CFence *)
    - simpl in H1. destruct X as [X_F|]; [|contradiction].
      inversion H. intros S H5 step T L H6. split; intro.
      + exfalso. apply H2. reflexivity.
      + subst. clear H H2.
        induction step; simpl; intros;
          right; split; intros.
        * exists T. split; [apply Acc_refl|]. inversion H3; subst.
          -- inversion H7.
          -- split; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H2 X) as [ffexists ffany].
                specialize (ffany ff 1 H9).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H16); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (SS_decide_remaining_work T SS H2).
          -- destruct H3 as [X [ff [L_X [S_X [H7 H8]]]]].
             assert (S_X = SRet \/ S_X <> SRet)
               by (destruct S_X eqn : S_X'; [right|left; auto|right|right];
                   intro; subst; inversion H3).
             destruct H3.
             ++ subst. eexists. apply HXPop; eauto.
             ++ destruct (H2 X). specialize (H9 ff 1 H7).
                eapply Forall_Fifo_peek in H9; eauto. simpl in H9.
                assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F X)) X)
                  by (apply GlobalMachMemSpaces_restriction; auto).
                destruct (H9 T _ (Acc_refl T) H10).
                ** exfalso. destruct H11. destruct H11. inversion H11. subst. apply H3.
                   reflexivity.
                ** destruct H11 as [MM' [L' [S' []]]]. 
                   eexists. eapply HXStep; eauto.
          -- exists (MM, SS, L, S).
             apply HFence. apply H3.
        * exists T. split; [apply Acc_refl|]. inversion H3; subst.
          -- inversion H7.
          -- split; auto. split; auto. apply H5; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H2 X) as [ffexists ffany].
                specialize (ffany ff 1 H9).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H16); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (SS_decide_remaining_work T SS H2).
          -- destruct H3 as [X [ff [L_X [S_X [H7 H8]]]]].
             assert (S_X = SRet \/ S_X <> SRet)
               by (destruct S_X eqn : S_X'; [right|left; auto|right|right];
                   intro; subst; inversion H3).
             destruct H3.
             ++ subst. eexists. eapply HXPop; eauto.
             ++ destruct (H2 X). specialize (H9 ff 1 H7).
                eapply Forall_Fifo_peek in H9; eauto. simpl in H9.
                assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F X)) X)
                  by (apply GlobalMachMemSpaces_restriction; auto).
                destruct (H9 T _ (Acc_refl T) H10).
                ** exfalso. destruct H11. destruct H11. inversion H11. subst. apply H3.
                   reflexivity.
                ** destruct H11 as [MM' [L' [S' []]]]. 
                   eexists. eapply HXStep; eauto.
          -- exists (MM, SS, L, S).
             apply HFence. apply H3.

    (* CDeepCopy *)
    - intros S H3 step T L H4. split; intro.
      + exfalso. apply H2. inversion H. reflexivity.
      + subst. clear H. induction step; simpl; auto; intros; right; split.
        * assert (Based_Typ (View S0 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e; auto.
          assert (Based_Typ (View S1 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e0; auto.
          intros. exists T. split; [apply Acc_refl|].
          inversion H7; subst.
          -- inversion H9.
          -- split; [|split]; auto.
             split; intros.
             ++ simpl in H8. remember (eqb M M1). destruct b.
                ** symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
                   remember (MM#[M1]).
                   destruct o; simpl in H8; remember (eqb_name p1 p); destruct b.
                   --- inversion H8.
                   --- apply (proj1 H M1 p). destruct MM. simpl in Heqo. simpl.
                       remember (get M1). destruct o; auto. inversion Heqo.
                       symmetry in H10. subst. assumption.
                   --- inversion H8.
                   --- apply (proj1 H M1 p). destruct MM. simpl in Heqo. simpl.
                       remember (get M1). destruct o; auto. inversion Heqo.
                ** exact (proj1 H M p H8).
             ++ destruct B as [bty' btyp'P]. simpl in *. destruct S0; [|contradiction].
                destruct S1; [|contradiction]. clear H1 H5 H6.
               assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                  as LocalMM
                  by (apply GlobalMachMemSpaces_restriction; auto).
                specialize (e T L' H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMM).
                destruct e as [V0 []]. simpl in H5. destruct V0 as [|M0' p0']; [contradiction|]. 
                destruct H5. subst. destruct H6 as [W []]. destruct W as [bty0 bty0P]. simpl in *. subst.
                specialize (e0 T L' H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMM).
                destruct e0 as [V1 []]. simpl in H9. destruct V1 as [|M'' p'']; [contradiction|]. 
                destruct H9. subst. destruct H10 as [W' []].  destruct W' as [bty1 bty1P].
                simpl in H10. subst.
                pose proof (Deterministic_ExprEval _ _ H1 _ H11). inversion H10. subst. clear H10.
                pose proof (Deterministic_ExprEval _ _ H6 _ H19). inversion H10. subst. clear H10.
                assert (bty0P = btyP) by (apply proof_irrelevance).
                assert (bty1P = btyP) by (apply proof_irrelevance).
                subst. clear LocalMM.
                destruct (proj2 H M p _ H8 n) as [V []]. simpl in H12.
                destruct V; [|contradiction]. subst.
                remember (eqb M M1). destruct b0.
                ** symmetry in Heqb0. apply eqb_leibniz in Heqb0.
                   subst. remember (MM#[M1]). destruct o.
                   --- simpl. remember (eqb_name p1 p). destruct b0.
                       +++ symmetry in Heqb0. apply eqb_name_true in Heqb0. symmetry in Heqb0. subst.
                           remember (eqb M1 M0). destruct b0.
                           *** symmetry in Heqb0. apply eqb_leibniz in Heqb0. symmetry in Heqb0.
                               subst. rewrite <- Heqo in H20.
                               remember (eqb_name p1 p0). destruct b0.
                               ---- symmetry in Heqb0. apply eqb_name_true in Heqb0. subst.
                                    symmetry in Heqo. rewrite H20 in H10. exists (BaseVal bty0 b c). split; auto.
                               ---- pose proof (proj2 H M1 p0 _ H5 n).
                                    destruct H12 as [V' []].
                                    rewrite <- Heqo in H12. rewrite H20 in H12.
                                    exists V'. split; auto. simpl in H13. destruct V'; [|contradiction].
                                    subst. rewrite H9 in H8. inversion H8. subst. reflexivity.
                           *** pose proof (proj2 H M0 p0 _ H5 n). destruct H12 as [V []].
                               simpl in *. destruct V; [|contradiction]. subst.
                               destruct MM. simpl in H20. simpl in H12. remember (get M0). destruct o.
                               ---- rewrite H20 in H12. exists (BaseVal bty1 b0 c0).
                                    split; auto. rewrite H8 in H9. inversion H9. subst. reflexivity.
                               ---- inversion H12.
                       +++ exists (BaseVal bty0 b c). split; auto.
                   --- inversion H10.
                ** exists (BaseVal bty0 b c). split; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H2 X) as [SSexists SSany].
                specialize (SSany ff 1 H11).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed; eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
            by (apply GlobalMachMemSpaces_restriction; auto).
          assert (Based_Typ (View S0 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e; auto.
          assert (Based_Typ (View S1 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e0; auto.
          destruct (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H5) as [V []].
          simpl in H9. destruct S0; try contradiction. destruct V; try contradiction.
          destruct H9. symmetry in H9. subst.
          destruct (e0 T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H5) as [W []].
          simpl in H11. destruct S1; try contradiction. destruct W; try contradiction.
          destruct H11. subst. destruct H10 as [Pack []].
          destruct H12 as [Pack' []]. rewrite <- H11 in H13. destruct Pack as [btyView btyViewP].
          destruct Pack' as [btyView' btyViewP']. simpl in H13. subst.
          assert (btyViewP' = btyViewP) by (apply proof_irrelevance). subst. simpl in *.
          pose proof (proj2 H b p _ H10 0). destruct H11 as [Vn []].
          apply sub_MM in H11. destruct H11.
          eexists. eapply HDeepCopy; eauto.
        * assert (Based_Typ (View S0 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e; auto.
          assert (Based_Typ (View S1 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e0; auto.
          intros. exists T. split; [apply Acc_refl|].
          inversion H7; subst.
          -- inversion H9.
          -- split; [|split]; auto.
             split; intros.
             ++ simpl in H8. remember (eqb M M1). destruct b.
                ** symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
                   remember (MM#[M1]).
                   destruct o; simpl in H8; remember (eqb_name p1 p); destruct b.
                   --- inversion H8.
                   --- apply (proj1 H M1 p). destruct MM. simpl in Heqo. simpl.
                       remember (get M1). destruct o; auto. inversion Heqo.
                       symmetry in H10. subst. assumption.
                   --- inversion H8.
                   --- apply (proj1 H M1 p). destruct MM. simpl in Heqo. simpl.
                       remember (get M1). destruct o; auto. inversion Heqo.
                ** exact (proj1 H M p H8).
             ++ destruct B as [bty' btyp'P]. simpl in *. destruct S0; [|contradiction].
                destruct S1; [|contradiction]. clear H1 H5 H6.
               assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                  as LocalMM
                  by (apply GlobalMachMemSpaces_restriction; auto).
                specialize (e T L' H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMM).
                destruct e as [V0 []]. simpl in H5. destruct V0 as [|M0' p0']; [contradiction|]. 
                destruct H5. subst. destruct H6 as [W []]. destruct W as [bty0 bty0P]. simpl in *. subst.
                specialize (e0 T L' H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMM).
                destruct e0 as [V1 []]. simpl in H9. destruct V1 as [|M'' p'']; [contradiction|]. 
                destruct H9. subst. destruct H10 as [W' []].  destruct W' as [bty1 bty1P].
                simpl in H10. subst.
                pose proof (Deterministic_ExprEval _ _ H1 _ H11). inversion H10. subst. clear H10.
                pose proof (Deterministic_ExprEval _ _ H6 _ H19). inversion H10. subst. clear H10.
                assert (bty0P = btyP) by (apply proof_irrelevance).
                assert (bty1P = btyP) by (apply proof_irrelevance).
                subst. clear LocalMM.
                destruct (proj2 H M p _ H8 n) as [V []]. simpl in H12.
                destruct V; [|contradiction]. subst.
                remember (eqb M M1). destruct b0.
                ** symmetry in Heqb0. apply eqb_leibniz in Heqb0.
                   subst. remember (MM#[M1]). destruct o.
                   --- simpl. remember (eqb_name p1 p). destruct b0.
                       +++ symmetry in Heqb0. apply eqb_name_true in Heqb0. symmetry in Heqb0. subst.
                           remember (eqb M1 M0). destruct b0.
                           *** symmetry in Heqb0. apply eqb_leibniz in Heqb0. symmetry in Heqb0.
                               subst. rewrite <- Heqo in H20.
                               remember (eqb_name p1 p0). destruct b0.
                               ---- symmetry in Heqb0. apply eqb_name_true in Heqb0. subst.
                                    symmetry in Heqo. rewrite H20 in H10. exists (BaseVal bty0 b c). split; auto.
                               ---- pose proof (proj2 H M1 p0 _ H5 n).
                                    destruct H12 as [V' []].
                                    rewrite <- Heqo in H12. rewrite H20 in H12.
                                    exists V'. split; auto. simpl in H13. destruct V'; [|contradiction].
                                    subst. rewrite H9 in H8. inversion H8. subst. reflexivity.
                           *** pose proof (proj2 H M0 p0 _ H5 n). destruct H12 as [V []].
                               simpl in *. destruct V; [|contradiction]. subst.
                               destruct MM. simpl in H20. simpl in H12. remember (get M0). destruct o.
                               ---- rewrite H20 in H12. exists (BaseVal bty1 b0 c0).
                                    split; auto. rewrite H9 in H8. inversion H8. subst. reflexivity.
                               ---- inversion H12.
                       +++ exists (BaseVal bty0 b c). split; auto.
                   --- inversion H10.
                ** exists (BaseVal bty0 b c). split; auto.
             ++ apply H3; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H2 X) as [SSexists SSany].
                specialize (SSany ff 1 H11).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed; eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
            by (apply GlobalMachMemSpaces_restriction; auto).
          assert (Based_Typ (View S0 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e; auto.
          assert (Based_Typ (View S1 bty btyP)) by
            (eapply ExprTyping_with_Based_context_implies_Based_Typ; eauto).
          apply ExprTyping_soundness in e0; auto.
          destruct (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H5) as [V []].
          simpl in H9. destruct S0; try contradiction. destruct V; try contradiction.
          destruct H9. symmetry in H9. subst.
          destruct (e0 T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) H5) as [W []].
          simpl in H11. destruct S1; try contradiction. destruct W; try contradiction.
          destruct H11. subst. destruct H10 as [Pack []].
          destruct H12 as [Pack' []]. rewrite <- H11 in H13. destruct Pack as [btyView btyViewP].
          destruct Pack' as [btyView' btyViewP']. simpl in H13. subst.
          assert (btyViewP' = btyViewP) by (apply proof_irrelevance). subst. simpl in *.
          pose proof (proj2 H b p _ H10 0). destruct H11 as [Vn []].
          apply sub_MM in H11. destruct H11.
          eexists. eapply HDeepCopy; eauto.


    (* CKernel *)
    - intros S' H4 step T L H5. split; intro.
      + exfalso. apply H3. inversion H0. reflexivity.
      + subst. simpl in H2. destruct X as [X_K|]; [|contradiction].
        pose proof (Based_build_new_kernel_context G xs H1) as Based_G'.
        specialize (H X_K eq_refl Based_G' H2). clear H0.
        induction step; simpl; intros; right; intros; split; intros.
        * exists T. split; [apply Acc_refl|]. inversion H6; subst.
          -- inversion H8.
          -- split; auto. split; [|constructor].
             intro. split.
             ++ simpl. destruct (eqb X_K X).
                ** exists (push ff (L_new, S)). reflexivity.
                ** apply (H3 X).
             ++ intros. simpl in H7. remember (eqb X_K X). destruct b.
                ** inversion H7. subst. clear H7. destruct (H3 X).
                   destruct H7 as [ff_X]. specialize (H8 ff_X n1 H7).
                   symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
                   rewrite H7 in H9. inversion H9. subst.
                   apply Forall_Fifo_push; auto. simpl. apply H.
                   --- destruct (ContextSem_kernel T G L' xs H5 e) as [L'' []].
                       rewrite -> H19 in H10. inversion H10. subst. assumption.
                   --- intro. subst. apply n0. reflexivity.
                ** apply H3. assumption.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H3 X) as [SSexists SSany].
                specialize (SSany ff 1 H10).
                apply Forall_Fifo_peek with (a := (L'0,S'1)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed; eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (H3 X_K). destruct H6 as [X_K_ff].
          destruct (ContextSem_kernel T G L xs H5 e) as [L'' []]. 
          eexists. apply HKernel; eauto.
        * exists T. split; [apply Acc_refl|]. inversion H6; subst.
          -- inversion H8.
          -- split; auto. split.
             ++ intro. split.
                ** simpl. destruct (eqb X_K X).
                   --- exists (push ff (L_new, S)). reflexivity.
                   --- apply (H3 X).
                ** intros. simpl in H7. remember (eqb X_K X). destruct b.
                   --- inversion H7. subst. clear H7. destruct (H3 X).
                       destruct H7 as [ff_X]. specialize (H8 ff_X n1 H7).
                       symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
                       rewrite H7 in H9. inversion H9. subst.
                       apply Forall_Fifo_push; auto. simpl. apply H.
                       +++ destruct (ContextSem_kernel T G L' xs H5 e) as [L'' []].
                           rewrite -> H19 in H10. inversion H10. subst. assumption.
                       +++ intro. subst. apply n0. reflexivity.
                   --- apply H3. assumption.
             ++ apply H4; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H3 X) as [SSexists SSany].
                specialize (SSany ff 1 H10).
                apply Forall_Fifo_peek with (a := (L'0,S'1)) in SSany; auto. apply SSany.
             ++ eapply SSSem_step_closed; eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (H3 X_K). destruct H6 as [X_K_ff].
          destruct (ContextSem_kernel T G L xs H5 e) as [L'' []]. 
          eexists. apply HKernel; eauto.

    (* SCom *)
    - simpl in *. destruct H3. apply H; auto.

    (* SRet *)
    - intros step T L H3. split; intros.
      + induction step; simpl; intros; left; exists MM, L; reflexivity.
      + induction step; simpl; intros; destruct (SS_decide_remaining_work T SS H4).
        * destruct H5 as [X' [ff_X [L' [S' [H6]]]]]. right. split.
          -- intros. exists T. split; [apply Acc_refl|]. inversion H7; subst.
             ++ inversion H9.
             ++ split; auto. split; [apply SSSem_pop_closed; auto|auto].
             ++ split; [|split]; auto.
                ** eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                   destruct (H4 X) as [SSexists SSany].
                   specialize (SSany ff 1 H11).
                   apply Forall_Fifo_peek with (a := (L'1,S'1)) in SSany; auto. apply SSany.
                ** eapply SSSem_step_closed; eauto.
                   apply GlobalMachMemSpaces_restriction; auto.
          -- destruct (H4 X'). specialize (H8 ff_X 1 H6).
             eapply Forall_Fifo_peek in H8; eauto. simpl in H8.
             assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F X')) X')
                      by (apply GlobalMachMemSpaces_restriction; auto).
             destruct (H8 T (restrict MM (comp_acc_rel F X')) (Acc_refl T) H9).
             ++ assert (S' = SRet \/ S' <> SRet)
                  by (destruct S' eqn : S_X'; [right|left; auto|right|right];
                      intro; subst; inversion H11).
                destruct H11.
                ** subst. eexists. eapply HXPop; eauto.
                ** exfalso. inversion H10. destruct H12. inversion H12. subst.
                   apply H11. reflexivity.
             ++ destruct H10 as [MM_X' [L_X' [S_X' []]]].
                eexists. eapply HXStep; eauto.
        * left. unfold Final_BX0State. exists MM, SS, L. split; auto.
        * destruct H5 as [X' [ff_X [L' [S' [H6]]]]]. right. split.
          -- intros. exists T. split; [apply Acc_refl|]. inversion H7; subst.
             ++ inversion H9.
             ++ split; auto. split; [apply SSSem_pop_closed; auto|auto].
             ++ split; [|split]; auto.
                ** eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                   destruct (H4 X) as [SSexists SSany].
                   specialize (SSany ff 1 H11).
                   apply Forall_Fifo_peek with (a := (L'1,S'1)) in SSany; auto. apply SSany.
                ** eapply SSSem_step_closed; eauto.
                   apply GlobalMachMemSpaces_restriction; auto.
          -- destruct (H4 X'). specialize (H8 ff_X 1 H6).
             eapply Forall_Fifo_peek in H8; eauto. simpl in H8.
             assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F X')) X')
                      by (apply GlobalMachMemSpaces_restriction; auto).
             destruct (H8 T (restrict MM (comp_acc_rel F X')) (Acc_refl T) H9).
             ++ assert (S' = SRet \/ S' <> SRet)
               by (destruct S' eqn : S_X'; [right|left; auto|right|right];
                      intro; subst; inversion H11).
                destruct H11.
                ** subst. eexists. eapply HXPop; eauto.
                ** exfalso. inversion H10. destruct H12. inversion H12. subst.
                   apply H11. reflexivity.
             ++ destruct H10 as [MM_X' [L_X' [S_X' []]]].
                eexists. eapply HXStep; eauto.
        * left. unfold Final_BX0State. exists MM, SS, L. split; auto.

    (* SDeclVar *)
    - pose proof (ExprTyping_with_Based_context_implies_Based_Typ G E t _ H1 e).
      assert (Based_context (cons_var x t G)). simpl. split; auto. simpl in H2.
      specialize (H X0 eq_refl H3 H2).
      apply ExprTyping_soundness in e; auto.
      intros step T L ctxt_Sem. split; intros.
      + induction step; simpl; intros; right.
        * destruct (e T L ctxt_Sem _ MM H5 H6) as [V []].
          exists MM, (L[x |-> V]), S.
          split; [apply XDeclVar; auto|]. split; auto.
        * destruct (e T L ctxt_Sem _ MM H5 H6) as [V []].
          exists MM, (L[x |-> V]), S.
          split; [apply XDeclVar; auto|]. split; auto.
          apply H; auto. intros y t' H11.
          remember (eqb_name x y). destruct b; simpl; rewrite <- Heqb.
          -- exists V. split; auto. symmetry in Heqb. apply eqb_name_true in Heqb.
             subst. destruct H11; [|exfalso; destruct H9; apply H9; reflexivity].
             destruct H9. subst. assumption.
          -- eapply ContextSem_extension_closed in ctxt_Sem; eauto.  
             apply ctxt_Sem; auto. destruct H11.
             ++ exfalso. destruct H9. subst. rewrite eqb_name_refl in Heqb.
                inversion Heqb.
             ++ destruct H9. assumption.
      + induction step; simpl; intros; right; subst;
          assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
          as LocalMM
            by (apply GlobalMachMemSpaces_restriction; auto);
          destruct (e T L ctxt_Sem _ (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMM) as [V []];
          split; intros.
        * exists T. split; [apply Acc_refl|]. inversion H8; subst.
          -- inversion H10; subst. split; [|split]; auto.
             apply GlobalMachMemSpaces_join_restriction; auto.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H6 X) as [ffexists ffany].
                specialize (ffany ff 1 H12).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H19); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * pose proof (XDeclVar (restrict MM (comp_acc_rel F (BX0 F))) L x E S V H4).
          exists (join (restrict MM (fun Ms => negb (comp_acc_rel F (BX0 F) Ms)))
                    (restrict MM (comp_acc_rel F (BX0 F))),SS,L[x |-> V],S).
          eapply X0Step. assumption.
        * exists T. split; [apply Acc_refl|]. inversion H8; subst.
          -- inversion H10; subst. split; [|split]; auto.
             ++ apply GlobalMachMemSpaces_join_restriction; auto.
             ++ apply H; auto. intros y t' H14.
                remember (eqb_name x y). destruct b; simpl; rewrite <- Heqb.
                ** symmetry in Heqb. apply eqb_name_true in Heqb.
                   subst. destruct H14; [| exfalso; destruct H9; apply H9; reflexivity].
                   destruct H9. subst.
                   pose proof (Deterministic_ExprEval _ _ H4 _ H11). subst. exists v.
                   split; auto.
                ** apply ctxt_Sem; auto. destruct H14; destruct H9; subst; auto.
                   exfalso. rewrite eqb_name_refl in Heqb. inversion Heqb.
          -- split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H6 X) as [ffexists ffany].
                specialize (ffany ff 1 H12).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H19); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * pose proof (XDeclVar (restrict MM (comp_acc_rel F (BX0 F))) L x E S V H4).
          exists (join (restrict MM (fun Ms => negb (comp_acc_rel F (BX0 F) Ms)))
                    (restrict MM (comp_acc_rel F (BX0 F))),SS,L[x |-> V],S).
          eapply X0Step. assumption.

    (* SDeclView *)
    - intros step T L H4. split; intros.
      + exfalso. apply H3. inversion H0. reflexivity.
      + subst. simpl in H2. destruct M as [Ms|]; try contradiction.
        assert (Based_context (cons_var x (View (MsBase (BMs F) Ms) bty btyP) G))
               as Based_extended
                 by (simpl; split; auto).
        specialize (H (BX0 F) eq_refl Based_extended H2). clear H0.
        pose proof (ExprTyping_with_Based_context_implies_Based_Typ G E _ _ H1 e).
        apply ExprTyping_soundness in e; auto. clear H0.
        induction step; simpl; auto; intros; right; split; intros.
        * inversion H5; subst.
          -- inversion H7.
          -- exists (T[Ms,p |-> existT _ bty btyP]).
             assert (Acc T (T[Ms,p |-> existT _ bty btyP]))
                      by (apply Acc_extend; apply (proj1 H0); auto).
             split; [|split; [| split; auto]].
             ++ apply H6.
             ++ assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                  as LocalMem
                    by (apply GlobalMachMemSpaces_restriction; auto).
                specialize (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMem).
                destruct e as [V' [V'eval V'sem]].
                pose proof (Deterministic_ExprEval _ _ V'eval _ H18). subst.
                unfold ValSem in V'sem. destruct V; [|contradiction]. subst.
                assert (btyP = b) by (apply proof_irrelevance; auto). subst.
                apply GlobalMachMemSpaces_extension; auto.
             ++ eapply SSSem_extension_closed; eauto.
          -- exists T. split; [apply Acc_refl|].
             split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- exists T. split; [apply Acc_refl|].
             split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H3 X) as [ffexists ffany].
                specialize (ffany ff 1 H9).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H16); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (MachMemSpaces_extensible MM Ms) as [p].
          pose proof (proj1 H0 Ms p H5).
          assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                   as LocalMem
                     by (apply GlobalMachMemSpaces_restriction; auto).
          specialize (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMem).
          destruct e as [V [Veval Vsem]].
          exists (MM [Ms, p |-> default_Map V], SS, L[x |-> ViewVal Ms p], S).
          apply HDeclView; auto.
        * inversion H5; subst.
          -- inversion H7.
          -- exists (T[Ms,p |-> existT _ bty btyP]).
             assert (Acc T (T[Ms,p |-> existT _ bty btyP]))
                      by (apply Acc_extend; apply (proj1 H0); auto).
             assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
               as LocalMem
                 by (apply GlobalMachMemSpaces_restriction; auto).
             specialize (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMem).
             destruct e as [V' [V'eval V'sem]].
             pose proof (Deterministic_ExprEval _ _ V'eval _ H18). subst.
             unfold ValSem in V'sem. destruct V; [|contradiction]. subst.
             assert (btyP = b) by (apply proof_irrelevance; auto). subst.
             assert (GlobalMachMemSpaces (T [Ms, p |-> existT (Bt F) bty0 b]) (MM [Ms, p |-> default_Map (BaseVal bty0 b c)]))
               as GLE
               by (apply GlobalMachMemSpaces_extension; auto).
             split; [|split; [| split; auto]].
             ++ apply H6.
             ++ assumption.
             ++ eapply SSSem_extension_closed; eauto.
             ++ apply H; auto.
                eapply ContextSem_extension_closed in H4; eauto.
                intros y typ H10. simpl in H10. destruct H10 as [[]|[]].
                --- subst. simpl. rewrite eqb_name_refl. exists (ViewVal Ms p).
                    split; auto. split; auto. rewrite eqb_refl.
                    exists (existT (Bt F) bty0 b).
                    destruct (T #[ Ms]); simpl; rewrite eqb_name_refl; split; auto.
                --- destruct (H4 y typ H9) as [V' []]. exists V'.
                    split; auto. simpl. remember (eqb_name x y). destruct b0; auto.
                    exfalso. apply H7. symmetry. apply eqb_name_true. symmetry. assumption.
          -- exists T. split; [apply Acc_refl|].
             split; auto. split; [apply SSSem_pop_closed; auto|auto].
          -- exists T. split; [apply Acc_refl|].
             split; [|split]; auto.
             ++ eapply StmtSem_step_preserves_GlobalMachMemspaces; eauto.
                destruct (H3 X) as [ffexists ffany].
                specialize (ffany ff 1 H9).
                apply Forall_Fifo_peek with (a := (L'0,S'0)) in ffany; auto. apply ffany.
             ++ eapply SSSem_step_closed with (5 := H16); eauto.
                apply GlobalMachMemSpaces_restriction; auto.
        * destruct (MachMemSpaces_extensible MM Ms) as [p].
          pose proof (proj1 H0 Ms p H5).
          assert (LocalMachMemSpaces T (restrict MM (comp_acc_rel F (BX0 F))) (BX0 F))
                   as LocalMem
                     by (apply GlobalMachMemSpaces_restriction; auto).
          specialize (e T L H4 T (restrict MM (comp_acc_rel F (BX0 F))) (Acc_refl T) LocalMem).
          destruct e as [V [Veval Vsem]].
          exists (MM [Ms, p |-> default_Map V], SS, L[x |-> ViewVal Ms p], S).
          apply HDeclView; auto.
  Qed.

  (****************************************************************************)
  (*                               Type Safety                                *)
  (****************************************************************************)
  Lemma Reachability_preserves_BX0StmtSem : forall T MM SS step L S steps t,
      GlobalMachMemSpaces T MM ->
      SSSem T SS ->
      BX0StmtSem step T L S ->
      step > steps ->
      Reachable BX0Step (MM, SS, L, S) steps t ->
      exists T' MM' SS' L' S',
        Acc T T'
        /\ t = (MM',SS',L',S')
        /\ GlobalMachMemSpaces T' MM'
        /\ SSSem T' SS'
        /\ BX0StmtSem (step - steps)  T' L' S'.
  Proof using Type.
    intros. induction H3.
    - exists T, MM, SS, L, S. split; [apply Acc_refl|]. split; [reflexivity|].
      split; [assumption|]. split; [assumption|].
      assert (step - 0 = step) by lia. rewrite H3.
      assumption.
    - destruct y as [[[MM_y SS_y] L_y] S_y].
      assert (step > n) by lia. specialize (IHReachable H5).
      destruct IHReachable as [T' [MM' [SS' [L' [S' [Ac [EqS [GL [SSSS ]]]]]]]]].
      inversion EqS. subst. clear EqS.
      assert (Datatypes.S (step - Datatypes.S n) = step - n) by lia. rewrite <- H7 in H6.
      pose proof (BX0StmtSem_step_closed (step - Datatypes.S n) T' L' S' MM' SS' z H6 GL
                    SSSS H4).
      destruct H8 as [T_z [MM_z [SS_z [L_z [S_z [H9 [H10 [H11 []]]]]]]]].
      exists T_z, MM_z, SS_z, L_z, S_z. split; [|split; [|split; [|split]]].
      + eapply Acc_trans; eauto.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
  Qed.

  Lemma Init_GlobalMachMemSpaces : GlobalMachMemSpaces empty_Map empty_Map.
  Proof using Type.
    split; intros; simpl in *; auto. inversion H.
  Qed.

  Lemma Init_SSSem : 
    SSSem empty_Map
      (List.fold_right (fun bx SS => SS [bx |-> empty_Fifo]) empty_Map (BX_elems F)).
  Proof using Type.
    remember (BX_elems F).
    pose proof (BX_elems_full F).
    rewrite <- Heql in H. clear Heql.
    split.
    - intros. specialize (H X). induction l.
      + inversion H.
      + simpl in H. destruct H.
        * subst. exists empty_Fifo.
          simpl. rewrite -> eqb_refl. reflexivity.
        * specialize (IHl H). destruct IHl as [ff].
          simpl. remember (eqb a X). destruct b.
          -- symmetry in Heqb. apply eqb_leibniz in Heqb. subst.
             exists empty_Fifo. reflexivity.
          -- exists ff. assumption.
    - intros. specialize (H X). induction l.
      + simpl in H0. inversion H0.
      + simpl in *. remember (eqb a X). destruct b.
        * subst. inversion H0. apply Forall_Fifo_empty_Fifo.
        * apply IHl; auto. symmetry in Heqb. apply eqb_false in Heqb.
          destruct H; [exfalso; apply Heqb; auto|auto].
  Qed.

  Theorem Type_safety : forall S,
      Based_Stmt S ->
      WfStmt empty S (XBase _ (BX0 F)) ->
      Safe_BX0State (MkInit S).
  Proof using Type.
    intros. apply WfStmt_WfCmd_soundess in H0; simpl; auto.
    - intros step t H1.
      assert (ContextSem empty_Map empty empty_Map)
        by (intros x t' H2; inversion H2).
      assert (forall n, BX0StmtSem n empty_Map empty_Map S).
      { intro. destruct (H0 n empty_Map empty_Map H2). apply H4. reflexivity. }
      clear H0 H H2.
      unfold MkInit in H1.
      remember (List.fold_right (fun bx SS => SS [bx |-> empty_Fifo]) empty_Map (BX_elems F)) as SS.
      destruct t as [[[MM' SS'] L'] S'].
      pose proof Init_GlobalMachMemSpaces. 
      assert (SSSem empty_Map SS) by (subst; apply Init_SSSem).
      assert (Datatypes.S step > step) as Foo by lia.
      pose proof (Reachability_preserves_BX0StmtSem empty_Map empty_Map SS (Datatypes.S step)
                    empty_Map S step (MM', SS', L', S') H H0 (H3 (Datatypes.S step)) Foo H1).
      destruct H2 as [T' [MM'' [SS'' [L'' [S'' [H5 [H6 [H7 []]]]]]]]].
      symmetry in H6. inversion H6. subst.
      assert (Datatypes.S step - step = 1) by lia.
      rewrite H8 in H4.
      destruct (H4 MM' SS' H7 H2).
      + left. assumption.
      + destruct H9. right. assumption.
  Qed.
End FRAME_CONTEXT.

Definition Portable (F : Frame) (S : Stmt F) : Prop := 
  forall  (IX : XInstantiation F) (IMs : MsInstantiation F),
    (forall x, (IX #[ x]) <> Some (BX0 F)) ->
    (forall x, In (FX_Stmt _ S) x -> exists bx, IX#[x] = Some bx) ->
    (forall m, In (FMs_Stmt _ S) m -> exists bms, IMs#[m] = Some bms) ->
    Safe_BX0State _ (MkInit _ (MsInstantiate_Stmt _ (XInstantiate_Stmt _ S IX) IMs)).

Theorem TypingEnsuresPortability : forall F G S,
    (~ exists x t, In_context_var F G x t) ->
    WfStmt F G S (XBase _ (BX0 F)) ->
    Portable F S.
Proof.
  intros. intros IX IMs H1 H2 H3 t.
  remember (MsInstantiate_Stmt F (XInstantiate_Stmt F S IX) IMs) as BS.
  assert (Based_Stmt F BS) by (subst; apply Instantiate_Stmt_Based; auto).
  apply Type_safety; auto. subst.
  eapply WfStmt_Cmd_minimal_context in H0 as New; eauto.
  assert (forall x : name, In (FX_Stmt F S) x \/ XBase (BX F) (BX0 F) = XVar (BX F) x -> exists bx : BX F, (IX #[ x]) = Some bx)
    as Thing.
  { intros. apply H2. destruct H5; auto; inversion H5. }
  pose proof (filter_context_mem_less F G (FMs_Stmt_listset F S)).
  pose proof (filter_context_ex_less F (filter_context_mem F G (FMs_Stmt_listset F S)) (FX_Stmt_listset F S)).
  pose proof (context_less_trans F _ _ _ H6 H5). destruct H7 as [_ [_ CVar]].
  clear H5 H6.
  assert (forall m : name,
             (exists (x : name) (t : Typ F), In_context_var F (filter_context_ex F (filter_context_mem F G (FMs_Stmt_listset F S)) (FX_Stmt_listset F S)) x t /\ In (FMs_Typ F t) m) \/ In (FMs_Stmt F S) m ->
             exists bms : BMs F, (IMs #[ m]) = Some bms).
  { intros. apply H3. destruct H5; auto. destruct H5 as [x [tx []]].
    exfalso. apply H. exists x, tx. apply CVar. assumption. }
  pose proof (Instantiation_preserves_WfStmt F IX IMs H1 (filter_context_ex F (filter_context_mem F G (FMs_Stmt_listset F S)) (FX_Stmt_listset F S))
    S (XBase _ (BX0 F)) Thing H5 New).
  assert (Instantiate_context F (filter_context_ex F (filter_context_mem F G (FMs_Stmt_listset F S)) (FX_Stmt_listset F S)) IMs = empty F).
  { clear H6 H5 Thing New H4 t.
    induction (filter_context_ex F (filter_context_mem F G (FMs_Stmt_listset F S)) (FX_Stmt_listset F S)); simpl; auto.
    assert (In_context_var F (cons_var F n t c) n t) by (simpl; left; split; auto).
    exfalso. apply H. apply CVar in H4. exists n, t. assumption. }
  rewrite <- H7. apply H6; auto.
Qed.
