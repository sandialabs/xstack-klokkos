(** * Kokkos Semantics *)

(** This is basically the semantics of Kokkos, in as much detail as
  possible.  Attention is focused towards the memory spaces, views,
  and differences between host and device. *)

(** Zach's project: Giving a type system to MiniKokkos, and proving
  type safety to show some class of bugs do not exist. Namely:

  - Kokkos is more expressive than data parallel primitives

  - Host/Device introduces new classes of bugs

  - The MiniKokkos type system can eliminate certain (but not all)
    classes of bugs that are made available with the extra
    expressivity. *)

Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

(** Questions that writing this brings up:

   1. What happens if you pass negative numbers into ExecPolicy? *)

(** First, we need some preliminary definitions *)

(** In general, if it's upper-case, that's what Kokkos calls it. If it's
    lower-case, that's a custom structure *)

(** Name is unused except for logging *)
Definition Name := string.

(** We leave variables uninterpreted *)
Definition var := string.
Definition memory_space_var := string.
(** Same with C++ Types. Building a C++ type checker is beyond the
    scope of what any reasonable human should write in Coq, so instead
    of dealing with the complex type compatibilty, we just store as a
    string and require equality *)
(** NOTE: We will distinguish between CppType and a Kokkos type *)
Definition CppBaseType := string.
Inductive  CppType : Type :=
| CppData (t : CppBaseType)
| CppBinFun (t1 : CppBaseType) (t2 : CppBaseType) (tr : CppBaseType)
.

(** Kokkos supports arrays of dimension at most 8 *)
Definition tuple1 : Type := nat.
Definition tuple2 : Type := nat * nat.
Definition tuple3 : Type := nat * nat * nat.
Definition tuple4 : Type := nat * nat * nat * nat.
Definition tuple5 : Type := nat * nat * nat * nat * nat.
Definition tuple6 : Type := nat * nat * nat * nat * nat * nat.
Definition tuple7 : Type := nat * nat * nat * nat * nat * nat * nat.
Definition tuple8 : Type := nat * nat * nat * nat * nat * nat * nat * nat.

(** ** Execution Policies *)
(** Execution policies describes the iteration space. We put the range
    checks here so that you don't do anything nonsensical like trying
    to have an iteration from $[10,0)$. *)
Definition rangeOK1 (b : tuple1) (e : tuple1) : Prop :=
  b <= e.

Definition rangeOK2 (b : tuple2) (e : tuple2) : Prop :=
  let '(b1, b2) := b in
  let '(e1, e2) := e in
  b1 <= e1 /\ b2 <= e2.

Definition rangeOK3 (b : tuple3) (e : tuple3) : Prop :=
  let '(b1, b2, b3) := b in
  let '(e1, e2, e3) := e in
  b1 <= e1 /\ b2 <= e2 /\ b3 <= e3.

Definition rangeOK4 (b : tuple4) (e : tuple4) : Prop :=
  let '(b1, b2, b3, b4) := b in
  let '(e1, e2, e3, e4) := e in
  b1 <= e1 /\ b2 <= e2 /\ b3 <= e3 /\ b4 <= e4.

(**  ... etc up to rangeOK8 *)

(**  Define this later, refers to nested parallelism. *)
Definition in_parallel_region : Prop := True.

(** Execution Policy *)
Inductive ExecPolicy : Type :=
| IntegerType (e : nat) : ExecPolicy
| RangePolicy (* half-open interval *)
    (b : nat) (e : nat) (R : rangeOK1 b e) : ExecPolicy
| MDRangePolicy1
    (b : tuple1) (e : tuple1) (R : rangeOK1 b e) : ExecPolicy
| MDRangePolicy2
    (b : tuple2) (e : tuple2) (R : rangeOK2 b e) : ExecPolicy
| MDRangePolicy3
    (b : tuple3) (e : tuple3) (R : rangeOK3 b e) : ExecPolicy
| MDRangePolicy4
    (b : tuple4) (e : tuple4) (R : rangeOK4 b e) : ExecPolicy
(* .. This continue up to size 8 *)
(* Team policy specifies how to split up the work. Presumably
   these have some additional requirements on size, but I don't
   know what they are. *)
| TeamPolicy
    (league_size : nat) (team_size : nat) (vector_length : nat)
    (P : in_parallel_region) : ExecPolicy
(* Team Thread Range and ThreadVectoRange can be specified either with
 * [0,e) or [b,e) *)
| TeamThreadRange
    (b : nat) (e : nat) (R : rangeOK1 b e)
    (P : in_parallel_region) : ExecPolicy
| TeamThreadRange'
    (e : nat)
    (P : in_parallel_region) : ExecPolicy
| ThreadVectorRange
    (b : nat) (e : nat) (R : rangeOK1 b e)
    (P : in_parallel_region) : ExecPolicy
| ThreadVectorRange'
    (e : nat)
    (P : in_parallel_region) : ExecPolicy
.
(*
  (* IntegerType n is equivalent to RangePolicy 0 n *)
  Definition IntegerType (n : nat) : ExecPolicy :=
    RangePolicy 0 n (le_0_n n).
*)

(** ** Memory Layouts and Spaces *)
(**
 - LayoutLeft is Column-Major

 - LayoutRight Row-Major,

 - LayoutStride describes how far apart entries whose indices differ
   by one in only one dimension are.

 - LayoutTiled gives tiles of compile-time dimensions stored
   contiguously in LayoutLeft or LayoutRight.
*)

Inductive Layout :=
  LayoutLeft | LayoutRight | LayoutStride | LayoutTiled.

(** Where the code executes *)
Inductive ExecSpace :=
| Cuda | HIP
| HPX | OpenMP | OpenMPTarget
| Serial | ExecutionSpaceConcept
| DefaultExecutionSpace | DefaultHostExecutionSpace
.

(** Where data lives *)
(** SharedSpace, SharedHostPinnedSpace since Kokkos 4.0 *)
(** We do not cover the following for simplicity
<<
  | SharedSpace | SharedHostPinnedSpace  (* Is sort of "both" *)
  | MemorySpaceConcept (* User-defined, could be either *)
>>
*)
Inductive MemorySpace :=
| CudaSpace | CudaHostPinnedSpace | CudaUVMSpace
| HIPSpace | HIPHostPinnedSpace | HIPManagedSpace
| HostSpace
| DefaultMemorySpace
.

(** Kokkos makes a broad distinction between host and device
    MemorySpaces. *)
Inductive space := Host | Device.
Definition memory_space_type (m : MemorySpace) : space :=
  match m with
  | CudaSpace | CudaHostPinnedSpace | CudaUVMSpace  => Device
  | HIPSpace | HIPHostPinnedSpace | HIPManagedSpace => Device
  | HostSpace | DefaultMemorySpace                  => Host
  end.

(** Template parameters are bit-combinations of these flags. We
    represent as a list when making a view. *)
Inductive MemoryTrait :=
| Unmanaged | Atomic | RandomAccess | Restrict.

(** Runtime and static dimensions. Kokkos may have at most 8
    dimensions, with run-time dimensions appearing before compile-time
    dimensions.  In either case, the shape of the view is known
    statically. *)
Definition dynamic_D := nat.
Definition static_D := list nat.
Definition rank : Type := dynamic_D * static_D.

(** The type of the elements. In theory you can use any C++ type,
   however it is strongly recommended you use only base types and
   structs. *)
Definition element_t : Type := CppBaseType.

(** Whether the view itself is constant *)
Definition is_const := bool.

(** A DataType determines the fundamental scalar type of View and its
    dimensionality *)
Inductive DataType : Type := 
| mk_DataType (c : is_const) (e : element_t)
  (d : dynamic_D) (s : static_D) (le8 : d + length s <= 8) 
.
Inductive View : Type :=
| mk_View (d : DataType) (l : Layout) (ms : MemorySpace)
          (mt : list MemoryTrait) : View
.

(** Mirror Views
    Kokkos::create_mirror_view

    If you have a view on the device - the actual data is put on the
    device.  The host keeps the metadata on the host, but the host has
    no idea that the device writes happens.

    Another confusion is the mirror_view where both views are on the
    host and device. If you have a copy from host-host to host-device,
    one is correct and one is incorrect. Therefore it is not portable.
*)

(** Functor is a Kokkos structure that "tells" the execution policy
   what to do. It is a more structured extension from the C++ concept
   of a "functor" which is any class that has a custom operator()
   (that is, a functor can be called. The signature must match the
   execution policy. *)
(** I don't know what the signature of functor should be, so I'll just say
   it's some function from ExecPolicy (the indices) to void *)
(* TODO: Figure out if a functor is different for, e.g., parallel_for
   vs reduce. It seems to be, since for parallel reduce, you also pass in
   the reducers *)
(* TODO: make it so is_const is a predicate, not a bool *)
Definition Functor : Type := is_const -> ExecPolicy -> unit.

(** Kokkos Lambda is the second way to specify the parallel loop body.
  There is some subtlety here, since we want to always capture by
  value, using [[=]]. This is written using a macro
  [KOKKOS_INLINE_FUNCTIION], which does something special for CUDA.
  Capture by reference [[&]] is incorrect. *)
Definition KokkosLambda : Type := ExecPolicy -> unit.

(** A reducer, broadly speaking, is a way to convert an array of
   things into a single element. The default reducer is to add up all
   the elements (Sum). *)
(** Note that, even though a Reducer may return multiple values
   (e.g. MinMaxLoc), it is still a "scalar" since it is "just"
   plain-old-data *)
Inductive Reducer : Type :=
| BAnd      (t : CppBaseType) (v : var)
| BOr       (t : CppBaseType) (v : var)
| LAnd      (t : CppBaseType) (v : var)
| LOr       (t : CppBaseType) (v : var)
| Max       (t : CppBaseType) (v : var)
(* Returns 2 values: maximum value and location of maximum *)
| MaxLoc    (t : CppBaseType) (v : var)
| Min       (t : CppBaseType) (v : var)
| MinLoc    (t : CppBaseType) (v : var)
| MinMax    (t : CppBaseType) (v : var)
(* Returns 4 values: Min, MinLoc, Max, MaxLoc *)
| MinMaxLoc (t : CppBaseType) (v : var)
| Prod      (t : CppBaseType) (v : var)
(* The default reducer *)
| Sum       (t : CppBaseType) (v : var)
(* For the CustomReducer, there is also a final() functon, which if
   it exists, the result is passed to as well. We ignore this
   because it is really only a side-effect. *)
(* TODO: Well, I can't just write a join : t -> t -> t *)
| CustomReducer
  (t : CppBaseType) (init : CppType) (join : CppType) (v : var)
  (initOK : init = CppData t)
  (joinOK : join = CppBinFun t t t)
  (* These two are labeled in Kokkos as "Result" instead of Reducer, but
     effectively they are the same thing in that they are varargs. In
     these cases, the reducer is Sum. *)
  (* C++ "plain old data" that matches the signature of the functor *)
| PODReducer (t : CppBaseType) (v : var)
| ViewReducer (n : Name) (view : View)
.

(** At the end of the function, you may provide either a variable (POD
    or View), to store the resulting sum, or describe the reducer _and_
    put its variable to store. You have to put at least one, though, so
    we encode this as a record as a simple way of saying "nonempty
    list" *)
Record ReduceL :=
  build_ReduceL { rhd : Reducer ; rtl : list Reducer }.

Inductive kokkos_stmt : Type :=
| initialize
| finalize
| fence
| parallel_reduce :
    Name -> ExecPolicy -> Functor -> ReduceL -> kokkos_stmt
    (* For every functor, there is a thread local and thread global variables *)
| parallel_for :
    Name -> ExecPolicy -> Functor -> kokkos_stmt
| parallel_scan (* TODO *)
| deep_copy (* TODO *)
| new_view : View -> kokkos_stmt
| skip
.

(* TODO: Put in PDF *)
(** [parallel_reduce] example
<<
   double acc, arr_max;
   // acc does not need to be initialized
   // parallel_reduce is synchronous _only when_ reducers are scalars
   // if one reducer is a view, then parallel_reduce is asynchronous
   // writes to &acc, &arr_max
   // reads from data in functor
   // inside of f, you may only access element i, unless const (look into this)
   parallel_reduce("test", 100, f, acc, MAX(arr_max))
   //      sum
   //     /    \
   //    /      \
   //   x01     x23
   //  /  \    /  \
   // x0  x1  x2  x3
   Kokkos::parallel_reduce("Loop1", N,
     KOKKOS_LAMBDA (const int& i, double& lsum, double& lmin ) {
       lsum += 1.0*i; // Do not have to do any locking mechanism
       lmin = lmin < 1.0*i ? lmin : 1.0*i;
     },
   sum,Min<double>(min));
>>
*)
(** A kokkos program is just a list of statements *)
Definition kokkos_program := list kokkos_stmt.

(* Try 1; In theory they are equivalent.
Inductive valid_kokkos_program : kokkos_program -> Prop :=
| trivial_kokkos_program :
  valid_kokkos_program (initialize :: [finalize])
| kokkos_program_cons :
  forall (k : kokkos_program) (s : kokkos_stmt) (ss : kokkos_program),
  valid_kokkos_program k ->
  (s <> initialize /\ s <> finalize) ->
  (k = (initialize :: ss) ++ [finalize]) ->
  valid_kokkos_program (initialize :: s :: ss ++ [finalize]).
*)

Inductive valid_kokkos_program : kokkos_program -> Prop :=
| mk_valid_kokkos_program :
  forall k k',
  k = initialize :: k' ++ [finalize]
  -> ~ In initialize k'
  -> ~ In finalize k'
  -> valid_kokkos_program k.

Lemma kokkos_program_ge_2 : forall k,
 valid_kokkos_program k -> length k >= 2.
Proof. 
  intros.
  inversion H.
  rewrite H0.
  (* Helpful things:
     Locate "::". (* Locate a notation, giving you the desugaring of it *)
     Search app length. (* Searches all terms that contain app _and_ length *)
  *)
  pose proof (app_length (initialize :: k') [finalize]) as L.
  (* (* Searches which may be helpful *)
    Search (?x :: ?y) "++".
    Search app cons.
  *)
  rewrite <- app_comm_cons in L.
  rewrite L.
  simpl.
  lia.
Defined.

(** * Synchronization *)
(** We must distinguish the various definitions. In concurrency,
 any enforcement of some sort of ordering between operations.

 - A barrier is defined as a point in which every thread must reach
   before continuing beyond it.
 
 - A fence, on the other hand, simply means that all reads and
   writes before that fence have been committed.
 
 - In memory models, there is the notion of other fences
   (e.g. release-write and acquire-read fences); that is, everything after
   the lock must stay between (things which are outside of the lock may
   be ordered inside of the lock). This is all very complex but is
   fortunatley not something we have to deal with. There are notions
   of atomics in Kokkos.
*)
(* TODO: Synchronization *)
(** * Introspection of Kokkos *)
(** We define a predicate to describe whether a Kokkos statement is
   asynchronous *)
(** A reducer is asynchronous when any one of its reducer arguments
   is not a scalar *)

Definition reducer_is_async (r : ReduceL) : bool :=
  match rhd r with
  | ViewReducer _ _ => true
  | _ =>
    List.existsb
    (fun x =>
       match x with
       | ViewReducer _ _ => true
       | _ => false
       end)
    (rtl r)
  end.

Definition is_async (s : kokkos_stmt) : bool :=
  match s with
  | initialize => false
  | finalize => false
  | fence => false
  | parallel_reduce _ _ _ r => reducer_is_async r
  | parallel_for _ _ _ => true
  | parallel_scan => false (* TODO: fix after actually specifying *)
  | deep_copy => false (* TODO: Host-Host, Host-Dev, Dev-Host *)
  | new_view _  => false
  | skip => false
  end.

(** The default Layout depends on execution space. *)
Definition default_layout (e : ExecSpace) : Layout :=
  match e with
  | Cuda     => LayoutLeft
  | OpenMP   => LayoutRight
  (* TODO: Fill in *)
  | _ => LayoutRight
  end.

(* TODO: Have a ViewsTouched list for the kokkos lambda *)

(** * Data Race *)

(** Here, we define a data race. The true definition of a data race is,
 broadly speaking, when the result of an operation may differ because of a
 potential scheduling of an operation. However, this is too broad for our
 purposes, especially when considering a parallel programming language; for
 example, with reductions, operations are assumed to be associative, when
 in reality, floating-point summation is one example where a reduction may
 be different depending on the thread schedule.

 For more examples about the subtleties of data races, see
 https://dl.acm.org/doi/10.1145/2076450.2076465

 And so, we use a more strict definition as follows: A data race is when
 a location is read or written by a thread which has been written to
 by a different thread, and it is possible these occur at the same time.
*)
     
(** A quick check for whether the code has enough fences.  A code has
 too few fences if there are multiple asynchronous statements which
 interact with the same view. A code has too many fences if
 there is a fence when everything is synchronous. *)
Definition correctly_fenced (p : kokkos_program) : bool := true.

Definition data_race (x : kokkos_stmt) : bool :=
  match x with
  | parallel_for _ _ f       =>
    (* We want to capture which indices the functor accesses; essentially,
       a data race for parallel_for is one where. *)
    false
  | parallel_reduce _ _ _ _  => false
  | _                        => false
  end.

(** * Theorem: Portability *)
(** Valid kokkos program is more complex than it just is syntactically
   correct. The key property we want to express here is that
   regardless of the assignments of memory spaces (generally described
   as host or device spaces), the result should not change, modulo
   floating-point arithmetic errors from assuming associativity. *)
(** Definition; Regardless of host or device architecture (i.e. number
    of threads, number of devices, memory model of hosts and devices,
    then the result is the same. *)
(* We don't have the tools to write this in Coq yet *)
(* We need to definite some notion of a Context, but for memory spaces:
  that is, a mapping from memory space variables (not yet defined) into
  concrete MemorySpace values. The reason this is important is that
  Kokkos behaves differently depending on the MemorySpace (in particular,
  Host vs Device)

  I'm not sure the best way to do this yet. One way may be to make an
  abstraction of a Kokkos program where all MemorySpace terms are
  replaced with a variable. Another may be to say "forall assignments
  of MemorySpaces for the views." A third may be to re-write Views (or
  other things that take in MemorySpace terms) and replace them with
  variables representing memory spaces. In any case, I roughly put
  what I mean here.

  Note that the "compat" function is carrying a lot of weight. I don't
  think the right way to do this is to make a full interpreter for a
  kokkos program, since this would make the types of programs we
  support rather limited. I had originally intended this to more of an
  "everything but the computation" specification.
*)
Fail Definition portability (k : kokkos_program) : forall
  (Gamma : list memory_space_var)
  (m : map (memory_space_var -> MemorySpace) Gamma)
  (a : abstract_memory_spaces k)
  (k' : assign_memory_spaces k a),
  (compat k k').

Definition portability (k : kokkos_program) := True.

Theorem kokkos_portability (k : kokkos_program)
  (v : valid_kokkos_program k) : portability k.
Proof.
  Admitted.
