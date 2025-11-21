From Coq Require Import List Arith Lia.
Import ListNotations.
From Paco Require Import paco.

(* ================================================== *)
(* 1) Syntax: smaller language (dependent + NatRec)   *)
(*    with universe hierarchy Type__ i / VType i      *)
(* ================================================== *)

Inductive term : Type :=
  | Type__ : nat -> term                (* universe levels: Type__ i *)
  | Nat  : term
  | Pi : term -> term -> term
  | Zero : term
  | Succ : term -> term
  | Var : nat -> term
  | Lam : term -> term -> term
  | App : term -> term -> term
  | NatRec : term -> term -> term -> term -> term  (* P z s n *)
  | Vec : term -> term -> term                (* Vec A n  *)
  | Nil : term -> term                        (* Nil A     *)
  | Cons : term -> term -> term -> term -> term     (* Cons A n x xs *)
  | VecRec : term -> term -> term -> term -> term -> term.

Inductive whnf : Type :=
| VType  : nat -> whnf                    (* new: universe values VType i *)
| VNat   : whnf
| VPi    : whnf -> closure -> whnf
| VLam   : whnf -> closure -> whnf
| VZero  : whnf
| VSucc  : whnf -> whnf
| VNeutral : neutral -> whnf
| VVec  : whnf -> whnf -> whnf              (* VVec vA vn *)
| VNil  : whnf -> whnf                      (* VNil vA *)
| VCons : whnf -> whnf -> whnf -> whnf -> whnf    (* VCons vA vn vx vxs *)

with neutral : Type :=
| NVar : nat -> neutral
| NApp : neutral -> whnf -> neutral
| NNatRec : whnf -> whnf -> whnf -> neutral -> neutral
| NVecRec : whnf -> whnf -> whnf -> whnf -> neutral -> neutral

with closure : Type :=
| Cl : list whnf -> term -> closure
.

Coercion VNeutral : neutral >-> whnf.

Section ManualMutualInduction_Prop.

  Variable Pw : whnf -> Prop.
  Variable Pn : neutral -> Prop.
  Variable Pc : closure -> Prop.

  (* Hypotheses for each constructor (one hypothesis per constructor) *)
  Hypotheses
    (H_VType    : forall i, Pw (VType i))
    (H_VNat     : Pw VNat)
    (H_VPi      : forall A B, Pw A -> Pc B -> Pw (VPi A B))
    (H_VLam     : forall A cl, Pw A ->  Pc cl -> Pw (VLam A cl))
    (H_VZero    : Pw VZero)
    (H_VSucc    : forall n, Pw n -> Pw (VSucc n))
    (H_VNeutral : forall n, Pn n -> Pw (VNeutral n))

    (* --- vector WHNFs --- *)
    (H_VVec  : forall vA vn, Pw vA -> Pw vn -> Pw (VVec vA vn))
    (H_VNil  : forall vA, Pw vA -> Pw (VNil vA))
    (H_VCons : forall vA vn vx vxs,Pw vA -> Pw vn -> Pw vx -> Pw vxs -> Pw (VCons vA vn vx vxs))

    (H_NVar    : forall i, Pn (NVar i))
    (H_NApp    : forall n v, Pn n -> Pw v -> Pn (NApp n v))
    (H_NNatRec : forall P z s n, Pw P -> Pw z -> Pw s -> Pn n -> Pn (NNatRec P z s n))
    (H_NVecRec : forall vP vnil vcons vinx nn, Pw vP -> Pw vnil -> Pw vcons -> Pw vinx -> Pn nn -> Pn (NVecRec vP vnil vcons vinx nn))

    (H_Cl     : forall ρ t, Forall Pw ρ -> Pc (Cl ρ t)).

  (* Helper: build a Forall Pw ρ by structural recursion over the list ρ,
     using the mutual whnf_proof function for elements. *)

  Fixpoint whnf_proof (v : whnf) {struct v} : Pw v :=
    match v with
    | VType i         => H_VType i
    | VNat            => H_VNat
    | VPi A B         => H_VPi A B (whnf_proof A) (closure_proof B)
    | VLam A cl       => H_VLam A cl (whnf_proof A) (closure_proof cl)
    | VZero           => H_VZero
    | VSucc n         => H_VSucc n (whnf_proof n)
    | VNeutral n      => H_VNeutral n (neutral_proof n)
    | VVec vA vn      => H_VVec vA vn (whnf_proof vA) (whnf_proof vn)
    | VNil vA         => H_VNil vA (whnf_proof vA)
    | VCons vA vn vx vxs => H_VCons vA vn vx vxs (whnf_proof vA) (whnf_proof vn) (whnf_proof vx) (whnf_proof vxs)
    end

  with neutral_proof (n : neutral) {struct n} : Pn n :=
    match n with
    | NVar i           => H_NVar i
    | NApp n' v        => H_NApp n' v (neutral_proof n') (whnf_proof v)
    | NNatRec P z s n' => H_NNatRec P z s n' (whnf_proof P) (whnf_proof z) (whnf_proof s) (neutral_proof n')
    | NVecRec P z s vinx n' => H_NVecRec P z s vinx n' (whnf_proof P) (whnf_proof z) (whnf_proof s) (whnf_proof vinx) (neutral_proof n')
    end

  with closure_proof (c : closure) {struct c} : Pc c :=
    match c with
    | Cl ρ t =>
        (* local structural recursion over ρ that may call whnf_proof for each head *)
        let fix build (ρ0 : list whnf) : Forall Pw ρ0 :=
            match ρ0 with
            | []     => @Forall_nil whnf Pw
            | v :: r => @Forall_cons whnf Pw v r (whnf_proof v) (build r)
            end
        in H_Cl ρ t (build ρ)
    end.


  Theorem whnf_mutind :
    (forall v, Pw v) /\ (forall n, Pn n) /\ (forall c, Pc c).
  Proof.
    split.
    - intro v; exact (whnf_proof v).
    - split.
      + intro n; exact (neutral_proof n).
      + intro c; exact (closure_proof c).
  Qed.

End ManualMutualInduction_Prop.

(* ----------------------------------------------------------------- *)
(*  Runtime application and evaluation (Option 1: types -> VType i)   *)
(* ----------------------------------------------------------------- *)

(* ----------------------------------------------------------------- *)
(*  Runtime application and evaluation (Option: structured WHNFs)    *)
(*  Keep Pi/Vec as structured WHNFs (VPi/VVec) and universes as VType *)
(* ----------------------------------------------------------------- *)

(* vapp: only two runtime shapes: real lambda closures, or neutral app *)
Inductive vapp : whnf -> whnf -> whnf -> Prop :=
| VApp_Lam_sharp : forall vA clρ body ρ arg vres,
    (* apply a real lambda closure: evaluate body in arg :: env_of_cl cl *)
    clρ = Cl ρ body ->
    eval' (arg :: ρ) body vres ->
    vapp (VLam vA clρ) arg vres

| VApp_Pi_sharp : forall vA ρ body arg vres,
    eval' (arg :: ρ) body vres ->
    vapp (VPi vA (Cl ρ body)) arg vres
    
| VApp_Neut_sharp : forall n v,
    vapp (VNeutral n) v (VNeutral (NApp n v))

(* evaluation for natrec (observational, using vapp which only inspects VLam/VNeutral) *)
with eval_natrec : whnf -> whnf -> whnf -> whnf -> whnf -> Prop :=
| ENR_Zero : forall vP vz vs,
    eval_natrec vP vz vs VZero vz
| ENR_Succ : forall vP vz vs vn vrec v1 v,
    eval_natrec vP vz vs vn vrec ->
    vapp vs vn v1 ->
    vapp v1 vrec v ->
    eval_natrec vP vz vs (VSucc vn) v
| ENR_Neut : forall vP vz vs nn,
    eval_natrec vP vz vs (VNeutral nn) (VNeutral (NNatRec vP vz vs nn))

(* evaluation for vecrec (observational, using vapp) *)
with eval_vecrec : whnf -> whnf -> whnf -> whnf -> whnf -> whnf -> Prop :=
| EVR_Nil : forall vP vnil vcons vindex vA,
    eval_vecrec vP vnil vcons vindex (VNil vA) vnil

| EVR_Cons : forall vP vnil vcons vindex vA vn vx vxs vrec v1 v2 v3 v,
    eval_vecrec vP vnil vcons vindex vxs vrec ->
    vapp vcons vindex v1 ->      (* apply cons to k (index) *)
    vapp v1 vx v2 ->            (* then to head *)
    vapp v2 vxs v3 ->           (* then to tail *)
    vapp v3 vrec v ->           (* then to recursive result *)
    eval_vecrec vP vnil vcons vindex (VCons vA vn vx vxs) v

(* | EVR_Cons : forall vP vnil vcons vindex vA vn vx vxs vrec v1 v2 v,
    eval_vecrec vP vnil vcons vindex vxs vrec ->
    vapp vcons vx v1 ->
    vapp v1 vxs v2 ->
    vapp v2 vrec v ->
    eval_vecrec vP vnil vcons vindex (VCons vA vn vx vxs) v *)

| EVR_Neut : forall vP vnil vcons vindex nn,
    eval_vecrec vP vnil vcons vindex (VNeutral nn) (VNeutral (NVecRec vP vnil vcons vindex nn))

(* ----------------------------------------------------------------- *)
(*  eval' : big-step evaluator to WHNF                                *)
(*  - Type__ i  --> VType i                                             *)
(*  - Nat       --> VNat (a structured WHNF for the Nat constant)       *)
(*  - Pi        --> VPi vA (Cl ρ B)  (structured, preserves closure)    *)
(*  - Vec A n   --> VVec vA vn (structured)                             *)
(* ----------------------------------------------------------------- *)
with eval' : list whnf -> term -> whnf -> Prop :=
| E'_Type : forall ρ i, eval' ρ (Type__ i) (VType i)

(* Nat is a primitive type value (VNat). Universe classification will be done
   by value_is_type_at below. *)
| E'_Nat : forall ρ, eval' ρ Nat VNat

| E'_Var_Some : forall ρ x v,
    nth_error ρ x = Some v ->
    eval' ρ (Var x) v

| E'_Var_None : forall ρ x,
    nth_error ρ x = None ->
    eval' ρ (Var x) (VNeutral (NVar (x - length ρ)))

(* Pi is kept as structured WHNF: evaluate domain to vA, and the Pi value is
   the VPi whose closure captures the syntactic codomain B along with the
   current runtime environment ρ. This preserves the closure so application
   can instantiate the codomain at runtime. *)
| E'_Pi : forall ρ A B vA,
    eval' ρ A vA ->
    eval' ρ (Pi A B) (VPi vA (Cl ρ B))

(* Lambdas evaluate to runtime closures (VLam) capturing the annotation value vA
   and the body closure Cl ρ b. *)
| E'_Lam : forall ρ A vA b,
    eval' ρ A vA ->
    eval' ρ (Lam A b) (VLam vA (Cl ρ b))

| E'_App : forall ρ t u vt vu v,
    eval' ρ t vt ->
    eval' ρ u vu ->
    vapp vt vu v ->
    eval' ρ (App t u) v

| E'_Zero : forall ρ, eval' ρ Zero VZero

| E'_Succ : forall ρ n vn,
    eval' ρ n vn ->
    eval' ρ (Succ n) (VSucc vn)

| E'_NatRec : forall ρ P z s n vP vz vs vn v,
    eval' ρ P vP ->
    eval' ρ z vz ->
    eval' ρ s vs ->
    eval' ρ n vn ->
    eval_natrec vP vz vs vn v ->
    eval' ρ (NatRec P z s n) v

(* Vec is kept as structured WHNF: evaluate element type to vA and index to vn,
   then the Vec type value is VVec vA vn. Universe classification is handled
   by value_is_type_at. *)
| E'_Vec : forall ρ A n vA vn,
    eval' ρ A vA ->
    eval' ρ n vn ->
    eval' ρ (Vec A n) (VVec vA vn)

| E'_Nil : forall ρ A vA,
    eval' ρ A vA ->
    eval' ρ (Nil A) (VNil vA)

| E'_Cons : forall ρ A n x xs vA vn vx vxs,
    eval' ρ A vA ->
    eval' ρ n vn ->
    eval' ρ x vx ->
    eval' ρ xs vxs ->
    eval' ρ (Cons A n x xs) (VCons vA vn vx vxs)

| E'_VecRec : forall ρ P nil cons n t vt vP vnil vcons vn vres,
    eval' ρ P vP ->
    eval' ρ nil vnil ->
    eval' ρ cons vcons ->
    eval' ρ n vn ->
    eval' ρ t vt ->
    eval_vecrec vP vnil vcons vn vt vres ->
    eval' ρ (VecRec P nil cons n t) vres.

Scheme eval'_rect := Induction for eval' Sort Prop
with vapp_rect := Induction for vapp Sort Prop
with eval_natrec_rect := Induction for eval_natrec Sort Prop
with eval_vecrec_rect := Induction for eval_vecrec Sort Prop.

Combined Scheme evals_mutind from eval'_rect, vapp_rect, eval_natrec_rect, eval_vecrec_rect.

(* ----------------------------------------------------------------- *)
(* Classify WHNFs as types at a universe level: value_is_type_at v i    *)
(* ----------------------------------------------------------------- *)

Definition env_of_cl (cl : closure) : list whnf :=
  match cl with Cl rho _ => rho end.

Definition body_of_cl (cl : closure) : term :=
  match cl with Cl _ t => t end.

Inductive value_is_type_at : whnf -> nat -> Prop :=
| VIT_VType : forall i, value_is_type_at (VType i) i
| VIT_VNat  : value_is_type_at VNat 0
| VIT_VVec  : forall a n i, value_is_type_at a i -> value_is_type_at (VVec a n) i
| VIT_VPi : forall a cl i j,
    value_is_type_at a i ->
    (forall r arg : whnf,
      eval' (arg :: env_of_cl cl) (body_of_cl cl) r ->
      value_is_type_at r j) ->
    value_is_type_at (VPi a cl) (Nat.max i j)
| VIT_cumul : forall v j i, value_is_type_at v j -> (j <= i)%nat -> value_is_type_at v i.

Definition value_is_type_at_upto (v : whnf) (k : nat) : Prop :=
  exists i, value_is_type_at v i /\ (i <= k)%nat.

Inductive conv_tag : Type :=
| TNe : neutral -> conv_tag
| TV  : whnf -> conv_tag
| TC  : closure -> conv_tag.

(* convF_cumul: like convF but universes use <= *)
Definition convF_cumul
  (r : conv_tag -> conv_tag -> Prop)
  (x y : conv_tag) : Prop :=
  match x, y with
  | TV (VType i), TV (VType j) => (i <= j)%nat
  (* otherwise the same structure as your convF, using r on subparts *)
  | TNe (NVar i), TNe (NVar j) => i = j
  | TNe (NApp n1 v1), TNe (NApp n2 v2) => r (TNe n1) (TNe n2) /\ r (TV v1) (TV v2)
  | TNe (NNatRec P1 z1 s1 n1), TNe (NNatRec P2 z2 s2 n2) =>
      r (TV P1) (TV P2) /\ r (TV z1) (TV z2) /\ r (TV s1) (TV s2) /\ r (TNe n1) (TNe n2)
  | TNe (NVecRec P1 nil1 cons1 idx1 n1), TNe (NVecRec P2 nil2 cons2 idx2 n2) =>
      r (TV P1) (TV P2) /\ r (TV nil1) (TV nil2) /\ r (TV cons1) (TV cons2) /\
      r (TV idx1) (TV idx2) /\ r (TNe n1) (TNe n2)
  | TV VNat,  TV VNat  => True
  | TV VZero, TV VZero => True
  | TV (VSucc n1), TV (VSucc n2) => r (TV n1) (TV n2)
  | TV (VNeutral n1), TV (VNeutral n2) => r (TNe n1) (TNe n2)
  | TV (VVec a1 n1), TV (VVec a2 n2) => r (TV a1) (TV a2) /\ r (TV n1) (TV n2)
  | TV (VNil a1), TV (VNil a2) => r (TV a1) (TV a2)
  | TV (VCons a1 n1 x1 xs1), TV (VCons a2 n2 x2 xs2) =>
      r (TV a1) (TV a2) /\ r (TV n1) (TV n2) /\ r (TV x1) (TV x2) /\ r (TV xs1) (TV xs2)
  | TV (VLam vA1 cl1), TV (VLam vA2 cl2) =>
      r (TV vA1) (TV vA2) /\ r (TC cl1) (TC cl2)
  | TV (VPi vA1 cl1), TV (VPi vA2 cl2) =>
      r (TV vA1) (TV vA2) /\ r (TC cl1) (TC cl2)
  | TV v_any, TV (VType k) => exists i, value_is_type_at v_any i /\ i <= k
  | TC (Cl ρ1 t1), TC (Cl ρ2 t2) =>
      Forall2 (fun x y => r (TV x) (TV y)) ρ1 ρ2 /\
      (forall (arg : whnf) (r1 : whnf),
         eval' (arg :: ρ1) t1 r1 ->
         exists r2, eval' (arg :: ρ2) t2 r2 /\ r (TV r1) (TV r2)) /\
      (forall (arg : whnf) (r2 : whnf),
         eval' (arg :: ρ2) t2 r2 ->
         exists r1, eval' (arg :: ρ1) t1 r1 /\ r (TV r1) (TV r2))
  | _, _ => False
  end.

(* paco wrapper *)
Definition vcumul (x y : conv_tag) : Prop := paco2 convF_cumul bot2 x y.

(* handy: value-level view of vcumul *)
Definition vcumul_v (v1 v2 : whnf) := vcumul (TV v1) (TV v2).
Definition vcumul_n (n1 n2 : neutral) := vcumul (TNe n1) (TNe n2).
Definition vcumul_cl (c1 c2 : closure) := vcumul (TC c1) (TC c2).

(* ---------------------------
   Bidirectional typing
   --------------------------- *)

(* Context: list of whnf (value-types) *)
Definition ctx := list whnf.

(* Helper: lookup in ctx *)
Definition ctx_lookup (Γ : ctx) (n : nat) : option whnf := nth_error Γ n.

Reserved Notation "Γ ⊢ₛ t ⇑ A" (at level 70).
Reserved Notation "Γ ⊢𝚌 t ⇓ A" (at level 70).

Inductive synth : ctx -> term -> whnf -> Prop :=

  (* variables: types are stored as WHNFs in the context *)
| S_Var : forall Γ x A,
    nth_error Γ x = Some A ->
    synth Γ (Var x) A

  (* universes / base types: Type__ i synthesizes to VType i; Nat synthesizes to VNat *)
| S_Type : forall Γ i, synth Γ (Type__ i) (VType i)
| S_Nat  : forall Γ, synth Γ Nat VNat

  (* Pi formation: domain evaluates to vA and must be a type at some level i;
     the codomain is checked under (vA :: Γ) producing some vB which must be a type at level j.
     We return a structured Pi WHNF capturing the codomain closure. *)
| S_Pi : forall Γ A B vA vB i j,
    eval' Γ A vA ->
    value_is_type_at vA i ->
    check (vA :: Γ) B vB ->
    value_is_type_at vB j ->
    synth Γ (Pi A B) (VPi vA (Cl Γ B))

  (* Application: synthesize t to something *cumulative* to VPi vdom clB,
     evaluate argument u to vu, evaluate the codomain by instantiating the closure
     and return that as the synthesized type. *)
| S_App : forall Γ t u vt vu vdom clB ρB Bterm vres,
    synth Γ t vt ->
    eval' Γ u vu ->
    vcumul (TV vt) (TV (VPi vdom clB)) ->    (* <-- use vcumul, not vconv *)
    clB = Cl ρB Bterm ->
    eval' (vu :: ρB) Bterm vres ->
    synth Γ (App t u) vres

  (* Zero & Succ: these synthesize to the Nat type (VNat) *)
| S_Zero : forall Γ, synth Γ Zero VNat

| S_Succ : forall Γ n,
    check Γ n VNat ->
    synth Γ (Succ n) VNat

  (* NatRec (term-level eliminator): synth to whatever eval_natrec gives.
     Here we preserve the use of vconv for the final comparison if you require strict
     convertibility for eliminators; otherwise you may relax it to vcumul as needed. *)
| S_NatRec_term : forall Γ P z s n vP vz vs vn v,
    eval' Γ P vP ->
    eval' Γ z vz ->
    eval' Γ s vs ->
    eval' Γ n vn ->
    eval_natrec vP vz vs vn v ->
    synth Γ (NatRec P z s n) v

  (* Vec formation: element type must be a type at some level; index must be Nat.
     Use cumulative comparison for index -> Nat as well (vcumul_v). *)
| S_Vec : forall Γ A n vA vn i,
    eval' Γ A vA ->
    value_is_type_at vA i ->
    eval' Γ n vn ->
    vcumul_v vn VNat ->                       (* <-- use vcumul_v for Nat index *)
    synth Γ (Vec A n) (VVec vA vn)

  (* Nil / Cons synthesize the *type* of the vector, not the vector value *)
| S_Nil : forall Γ A vA,
    eval' Γ A vA ->
    (exists i, value_is_type_at vA i) ->
    synth Γ (Nil A) (VVec vA VZero)

| S_Cons : forall Γ A n x xs vA vn,
    eval' Γ A vA ->
    (exists i, value_is_type_at vA i) ->
    eval' Γ n vn ->
    vcumul_v vn VNat ->                       (* <-- vcumul_v *)
    check Γ x vA ->                           (* x : A *)
    check Γ xs (VVec vA vn) ->                (* xs : Vec A n *)
    synth Γ (Cons A n x xs) (VVec vA (VSucc vn))

  (* VecRec term-level synthesizer *)
| S_VecRec_term : forall Γ P nil cons n t vt vP vnil vcons vn vres,
    eval' Γ P vP ->
    eval' Γ nil vnil ->
    eval' Γ cons vcons ->
    eval' Γ n vn ->
    eval' Γ t vt ->
    eval_vecrec vP vnil vcons vn vt vres ->
    synth Γ (VecRec P nil cons n t) vres

  (* Annotated lambda (synthesizes a Pi based on annotation). We require the annotation
     to synthesize to a WHNF vdom that is a type at some level; the body checks under
     (vdom :: Γ). The produced WHNF is the Pi whose closure captures the body term. *)
| S_Lam_Ann : forall Γ annA b vdom vB i,
    synth Γ annA vdom ->
    value_is_type_at vdom i ->
    check (vdom :: Γ) b vB ->
    synth Γ (Lam annA b) (VPi vdom (Cl Γ b))

where "Γ ⊢ₛ t ⇑ A" := (synth Γ t A)

with check : ctx -> term -> whnf -> Prop :=

(* checking by synth + cumulative subsumption (use vcumul here) *)
| C_Synth : forall Γ t A' A,
    synth Γ t A' ->
    vcumul (TV A') (TV A) ->      (* <-- use vcumul, not vconv *)
    check Γ t A

(* check lambda against expected Pi: expected A cumulative to Pi vdom clB,
   evaluate the expected codomain under clB's env to get vB, check the lambda body
   under its own static environment (vdom :: Γ) against that vB, then require
   the runtime closure produced by the lambda be observationally convertible to clB. *)
| C_Lam : forall Γ (A : whnf) annA b vdom clB ρB Bterm vB,
    synth Γ annA vdom ->                 (* annotation synthesizes the domain *)
    (exists i, value_is_type_at vdom i) -> (* annotation must be a type at some level *)
    vcumul (TV A) (TV (VPi vdom clB)) ->    (* <-- use vcumul, not vconv *)
    clB = Cl ρB Bterm ->
    eval' (vdom :: ρB) Bterm vB ->       (* evaluate codomain under clB's runtime env *)
    check (vdom :: Γ) b vB ->            (* check the lambda body in its own static env *)
    vcumul_cl (Cl Γ b) clB ->         (* closures must be observationally convertible *)
    check Γ (Lam annA b) A

(* NatRec checked against an expected A: evaluate elim components and require the
   evaluation of the elimination be *cumulative* to A (use vcumul or vconv depending on intent).
   Using vcumul is the conservative/cumulative choice. *)
| C_NatRec_check : forall Γ P z s n A vP vz vs vn v,
    eval' Γ P vP ->
    eval' Γ z vz ->
    eval' Γ s vs ->
    eval' Γ n vn ->
    eval_natrec vP vz vs vn v ->
    vcumul_v v A ->                     (* <-- vcumul_v (was vconv v A) *)
    check Γ (NatRec P z s n) A

(* VecRec checked against expected A *)
| C_VecRec_check : forall Γ P nil cons n A t vt vP vnil vcons vn vres,
    eval' Γ P vP ->
    eval' Γ nil vnil ->
    eval' Γ cons vcons ->
    eval' Γ n vn ->
    eval' Γ t vt ->
    eval_vecrec vP vnil vcons vn vt vres ->
    vcumul_v vres A ->                  (* <-- vcumul_v (was vconv vres A) *)
    check Γ (VecRec P nil cons n t) A
(* Generalize: if t synthesizes to some value v, and that v is a type at level k,
   then t checks against VType k. *)
| C_Synth_as_Type : forall Γ t v k,
    synth Γ t v ->
    value_is_type_at v k ->
    check Γ t (VType k).

(* syntactic shape predicate for type-level terms (useful in progress hypotheses) *)
Inductive is_type_shape : term -> Prop :=
| ITS_Type : forall i, is_type_shape (Type__ i)
| ITS_Nat  : is_type_shape Nat
| ITS_Var  : forall x, is_type_shape (Var x)
| ITS_App : forall t u, is_type_shape t -> is_type_shape (App t u)
| ITS_Pi   : forall A B, is_type_shape A -> is_type_shape B -> is_type_shape (Pi A B)
| ITS_Vec  : forall A n, is_type_shape A -> is_type_shape (Vec A n)
| ITS_NatRec : forall P z s n, is_type_shape P -> is_type_shape (NatRec P z s n)
| ITS_VecRec : forall P nil cons n t, is_type_shape P -> is_type_shape (VecRec P nil cons n t).

Scheme synth_rect := Induction for synth Sort Prop
with check_rect := Induction for check Sort Prop.

Combined Scheme typing_mutind from synth_rect, check_rect.

Lemma conv_refl: forall v, vcumul v v.
Proof. pcofix CIH.
       intro v.
       induction v; intros.
       - pfold. simpl. destruct n.
         + lia.
         + split. right. apply CIH. right. apply CIH.
         + split. right. apply CIH.
           split. right. apply CIH.
           split. right. apply CIH.
           right. apply CIH.
         + split. right. apply CIH.
           split. right. apply CIH.
           split. right. apply CIH.
           split. right. apply CIH.
           right. apply CIH.
       - pfold. simpl.
         destruct w; try easy.
         + split. right. apply CIH.
           right. apply CIH.
         + split. right. apply CIH.
           right. apply CIH.
         + right. apply CIH.
         + right. apply CIH.
         + split. right. apply CIH.
           right. apply CIH.
         + right. apply CIH.
         + split. right. apply CIH.
           split. right. apply CIH.
           split. right. apply CIH.
           right. apply CIH.
       - pfold. simpl.
         destruct c.
         split.
         induction l; intros.
         + constructor.
         + constructor. right. apply CIH.
           apply IHl.
         + intros. split.
           intros. exists r1. split. easy.
           right. apply CIH.
           intros.
           exists r2. split. easy.
           right. apply CIH.
Qed.

Lemma Forall2_conv_sym: forall l s r,
  (forall v1 v2 : conv_tag, vcumul v1 v2 -> r v2 v1) -> 
  Forall2 (fun x y : whnf => upaco2 convF_cumul bot2 (TV x) (TV y)) l s ->
  Forall2 (fun x y : whnf => upaco2 convF_cumul r (TV x) (TV y)) s l.
Proof. intro l.
       induction l; intros.
       - inversion H0. constructor.
       - inversion H0. subst.
         constructor.
         right. apply H.
         destruct H3; easy.
         apply IHl; easy.
Qed.

Lemma Forall2_conv_trans: forall l s u r,
  (forall v1 v2 v3: conv_tag, vcumul v1 v2 -> vcumul v2 v3 -> r v1 v3) -> 
  Forall2 (fun x y : whnf => upaco2 convF_cumul bot2 (TV x) (TV y)) l s ->
  Forall2 (fun x y : whnf => upaco2 convF_cumul bot2 (TV x) (TV y)) s u ->
  Forall2 (fun x y : whnf => upaco2 convF_cumul r (TV x) (TV y)) l u.
Proof. intro l.
       induction l; intros.
       - inversion H0. subst. inversion H1. subst. constructor.
       - inversion H0. subst. inversion H1. subst.
         constructor.
         right. apply H with (v2 := (TV y)).
         destruct H4; easy.
         destruct H5; easy.
         apply IHl with (s := l'); easy.
Qed.

Lemma Forall2_LE: forall l s r r',
  (forall x0 x1 : conv_tag, r x0 x1 -> r' x0 x1) ->
  Forall2 (fun x y : whnf => r (TV x) (TV y)) l s ->
  Forall2 (fun x y : whnf => r' (TV x) (TV y)) l s.
Proof. intro l.
       induction l; intros.
       - inversion H0. constructor.
       - inversion H0. subst.
         constructor. apply H; easy.
         apply IHl with (r := r); easy.
Qed.

Lemma mon_convF: monotone2 convF_cumul.
Proof. unfold monotone2.
       intro v1.
       induction v1; intros.
       - case_eq x1; intros.
         + subst. simpl in IN.
           destruct n, n0; try easy.
           simpl.
           split. apply LE; easy. apply LE; easy.
           simpl.
           split. apply LE; easy. split. apply LE; easy.
           split. apply LE; easy. apply LE; easy.
           simpl.
           split. apply LE; easy. split. apply LE; easy.
           split. apply LE; easy. split. apply LE; easy.
           apply LE; easy.
         + subst.
           simpl in IN. destruct n; easy.
         + subst.
           simpl in IN. destruct n; easy.
        - case_eq x1; intros.
          + subst.
            simpl in IN. destruct w; easy.
          + subst.
            simpl in IN. destruct w, w0; try easy.
            * simpl.
              split. apply LE; easy. apply LE; easy.
            * simpl.
              split. apply LE; easy. apply LE; easy.
            * simpl. apply LE; easy.
            * simpl. apply LE; easy.
            * simpl. 
              split. apply LE; easy. apply LE; easy.
            * simpl. apply LE; easy.
            * simpl. 
              split. apply LE; easy. split. apply LE; easy.
              split. apply LE; easy. apply LE; easy.
          + subst.
            simpl in IN. destruct w; easy.
        - case_eq x1; intros.
          + subst.
            simpl in IN. destruct c; easy.
          + subst.
            simpl in IN. destruct c; easy.
          + subst.
            simpl in IN. simpl.
            destruct c, c0.
            destruct IN as (Ha,(Hb,Hc)).
            split.
            apply Forall2_LE with (r := r); easy.
            split.
            intros.
            apply Hb in H.
            destruct H as (res2,(Hr2,Hr3)).
            exists res2. split. easy.
            apply LE; easy.
            intros.
            apply Hc in H.
            destruct H as (res2,(Hr2,Hr3)).
            exists res2. split. easy.
            apply LE; easy.
Qed.

Lemma vcumul_preserves_value_is_type_at_upto :
  forall v v1 k,
    value_is_type_at v k ->
    vcumul_v v1 v ->
    exists j, value_is_type_at v1 j /\ (j <= k)%nat.
Proof. intros.
       revert H0. revert v1.
       induction H; intros.
       - punfold H0. simpl in H0.
         destruct v1; try easy.
         exists n. split. constructor. easy.
         apply mon_convF.
       - punfold H0. simpl in H0.
         destruct v1; try easy.
         exists 0. split. constructor. easy.
         apply mon_convF.
       - punfold H0. simpl in H0.
         destruct v1; try easy.
         destruct H0 as (Ha,Hb).
         destruct Ha as [Ha | Ha].
         apply IHvalue_is_type_at in Ha.
         destruct Ha as (j,(Ha,Hc)).
         exists j.
         split. constructor. easy. easy.
         easy.
         apply mon_convF.
       - punfold H2. simpl in H2.
         destruct v1; try easy.
         destruct H2 as (Ha,Hb).
         destruct Ha as [Ha | Ha].
         apply IHvalue_is_type_at in Ha.
         destruct Ha as (j1,(Ha,Hc)).
         destruct Hb as [Hb | Hb].
         punfold Hb. simpl in Hb.
         destruct c, cl.
         destruct Hb as (Hb,(Hd,He)).
         simpl in *.
         exists (Nat.max j1 j).
         split. constructor.
         easy.
         intros. simpl in H2, H0, H1.
         apply Hd in H2.
         destruct H2 as (r2,(H2a,H2b)).
         destruct H2b as [H2b | H2b].
         pose proof H2a as H2ss.
         apply H0 in H2a.
         specialize(H1 _ _ H2ss r H2b).
         destruct H1 as (j3,(H1a,H1b)).
         apply VIT_cumul with (j := j3); easy.
         easy. lia.
         apply mon_convF.
         easy. easy.
         apply mon_convF.
       - apply IHvalue_is_type_at in H1.
         destruct H1 as (j1,(H1a,H1b)).
         exists j1. split. easy. lia.
Qed.

Lemma vcumul_n_to_v :
  forall n1 n2,
    vcumul_n n1 n2 ->                 (* vcumul (TNe n1) (TNe n2) *)
    vcumul_v (VNeutral n1) (VNeutral n2).  (* vcumul (TV (VNeutral n1)) (TV (VNeutral n2)) *)
Proof. (* pcofix CIH.
       intro n1. *)
       induction n1; intros.
       - punfold H. simpl in H.
         destruct n2; try easy.
         subst. pfold. simpl. left.
         apply conv_refl.
         apply mon_convF.
       - punfold H. simpl in H.
         destruct n2; try easy.
         subst. pfold. simpl.
         left. pfold. simpl. easy.
         apply mon_convF.
       - punfold H. simpl in H.
         destruct n2; try easy.
         subst. pfold. simpl.
         left. pfold. simpl. easy.
         apply mon_convF.
       - punfold H. simpl in H.
         destruct n2; try easy.
         subst. pfold. simpl.
         left. pfold. simpl. easy.
         apply mon_convF.
Qed.

Lemma vcumul_preserves_value_is_type_at_upto_n :
  forall n1 n2 k,
    value_is_type_at (VNeutral n2) k ->
    vcumul_n n1 n2 ->
    exists j, value_is_type_at (VNeutral n1) j /\ (j <= k)%nat.
Proof.
  intros n1 n2 k H_type H_cumul_n.
  (* Turn neutral-level cumul into value-level cumul on VNeutral *)
  pose proof (vcumul_n_to_v n1 n2 H_cumul_n) as H_cumul_v.
  (* Now apply the value-level preservation lemma *)
  eapply vcumul_preserves_value_is_type_at_upto in H_cumul_v; eauto.
Qed.


Lemma aa: forall v v1 k,
value_is_type_at v k ->
vcumul_v v1 v ->
vcumul_v v1 (VType k).
Proof. intros.
       revert H0. revert v1.
       induction H; intros.
       - easy.
       - punfold H0. simpl in H0.
         destruct v1; try easy.
         pfold. simpl. exists 0. split. constructor. lia.
         apply mon_convF.
       - punfold H0. simpl in H0.
         destruct v1; try easy.
         pfold. simpl.
         destruct H0 as (Ha,Hb).
         destruct Ha as [Ha | Ha].
         apply vcumul_preserves_value_is_type_at_upto with (k := i) in Ha.
         destruct Ha as (j,(Ha1,Ha2)).
         exists j. split. constructor. easy. lia.
         easy.
         easy.
         apply mon_convF.
       - punfold H2. simpl in H2.
         destruct v1; try easy.
         destruct H2 as (Ha,Hb).
         destruct Ha as [Ha | Ha].
         destruct Hb as [Hb | Hb].
         pfold. simpl.
         apply vcumul_preserves_value_is_type_at_upto with (k := i) in Ha.
         destruct Ha as (j1,(Ha1,Ha2)).
         punfold Hb. simpl in Hb.
         destruct c, cl.
         destruct Hb as (Hb1,(Hb2,Hb3)).
         exists (Nat.max j1 j).
         split. constructor.
         easy.
         intros. simpl in H2, H0, H1.
         apply Hb2 in H2.
         destruct H2 as (r2,(H2a,H2b)).
         destruct H2b as [H2b | H2b].
         pose proof H2a as H2ss.
         apply H0 in H2a.
         specialize(H1 _ _ H2ss r H2b).
         apply vcumul_preserves_value_is_type_at_upto with (k := j) in H1.
         destruct H1 as (j3,(H1a,H1b)).
         apply VIT_cumul with (j := j3); easy.
         constructor.
         easy. lia.
         apply mon_convF.
         easy. easy. easy.
         apply mon_convF.
       - apply IHvalue_is_type_at in H1.
         apply VIT_cumul with (i := i) in H. 
         punfold H1. simpl in H1.
         pfold. simpl.
         destruct v1; try easy. lia.
         
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         destruct H1 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
         apply mon_convF. lia.
Qed.

Lemma evals_deterministic :
  (forall ρ t v1, eval' ρ t v1 -> forall v2, eval' ρ t v2 -> v1 = v2)
  /\
  (forall vt arg r1, vapp vt arg r1 -> forall r2, vapp vt arg r2 -> r1 = r2)
  /\
  (forall vP vz vs n r1, eval_natrec vP vz vs n r1 -> forall r2, eval_natrec vP vz vs n r2 -> r1 = r2)
  /\
  (forall vP vnil vcons vindex t r1,
     eval_vecrec vP vnil vcons vindex t r1 ->
     forall r2, eval_vecrec vP vnil vcons vindex t r2 -> r1 = r2).
Proof.
  apply evals_mutind; intros.
   23:{
   intros.
   inversion H. subst. easy.
   }
   22:{
   intros.
   inversion H4. subst.
   apply H in H9.
   apply H0 in H14.
   subst.
   apply H1 in H16.
   subst.
   apply H2 in H17.
   subst.
   apply H3 in H18.
   easy.
   }
   21:{
   inversion H. subst. easy.
   }
   20:{
   inversion H. subst. easy.
   }
   19:{
   inversion H2. subst.
   apply H in H4.
   apply H0 in H5. subst.
   apply H1 in H9.
   easy.
   }
   18:{
   inversion H. easy.
   }
   17:{
   inversion H. easy.
   }
   16:{
   inversion H0. subst.
   apply H. (* inversion H3. *) easy.
   }
   15:{
   inversion H0. subst.
   apply H. inversion H3. easy.
   }
   14:{
   inversion H5. subst.
   apply H in H11.
   apply H0 in H13.
   apply H1 in H15.
   apply H2 in H16.
   apply H3 in H17. subst.
   apply H4 in H18. easy.
   }
   13:{
   inversion H3. subst.
   apply H in H9.
   apply H0 in H11.
   apply H1 in H12.
   apply H2 in H13.
   subst. easy.
   }
   12:{
   inversion H0. subst.
   apply H in H3.
   subst. easy.
   }
   11:{
   inversion H1. subst.
   apply H in H5.
   apply H0 in H7. subst.
   easy.
   }
   10:{
   inversion H4. subst.
   apply H in H9.
   apply H0 in H11.
   apply H1 in H13.
   apply H2 in H14.
   subst.
   apply H3 in H15. easy.
   }
   9:{
   inversion H0. subst.
   apply H in H3. subst. easy.
   }
   8:{
   inversion H. easy.
   }
   7:{
   inversion H2. subst.
   apply H in H5.
   apply H0 in H7. subst.
   apply H1 in H9.
   easy.
   }
   6:{
   inversion H0. subst.
   apply H in H5. subst. easy.
   }
   5:{
   inversion H0. subst.
   apply H in H5. subst.
   easy.
   }
   4:{
   inversion H.
   + subst. rewrite e in H2. easy.
   + subst. easy.
   }
   3:{
   inversion H. 
   + subst. rewrite e in H2. inversion H2. easy.
   + subst. rewrite e in H2. easy.
   }
   2:{
   inversion H. easy.
   }
   1:{
   inversion H. easy.
   }
Qed.

Definition eval'_det :
  forall ρ t v1 v2,
    eval' ρ t v1 -> eval' ρ t v2 -> v1 = v2.
Proof. destruct evals_deterministic as [H _]. eauto. Qed.

Definition vapp_det :
  forall vt arg r1 r2,
    vapp vt arg r1 -> vapp vt arg r2 -> r1 = r2.
Proof.
  destruct evals_deterministic as [_ [H _]].
  eauto.
Qed.

Definition eval_natrec_det :
  forall vP vz vs n r1 r2,
    eval_natrec vP vz vs n r1 -> eval_natrec vP vz vs n r2 -> r1 = r2.
Proof.
  destruct evals_deterministic as [_ [_ [H _]]].
  eauto.
Qed.

Definition eval_vecrec_det :
  forall vP vnil vcons vindex t r1 r2,
    eval_vecrec vP vnil vcons vindex t r1 ->
    eval_vecrec vP vnil vcons vindex t r2 ->
    r1 = r2.
Proof.
  destruct evals_deterministic as [_ [_ [_ H]]].
  eauto.
Qed.

Lemma conv_trans: forall v1 v2 v3, vcumul v1 v2 -> vcumul v2 v3 -> vcumul v1 v3.
Proof. pcofix CIH.
       intro v1.
       induction v1; intros.
       3:{
       case_eq v2; intros.
       - subst. punfold H0. simpl in H0.
         destruct c. easy.
         apply mon_convF.
       - subst. punfold H0. simpl in H0.
         destruct c. easy.
         apply mon_convF.
       - subst.
         case_eq v3; intros.
         + subst. punfold H1. simpl in H1.
           destruct c0. easy.
           apply mon_convF.
         + subst. punfold H1. simpl in H1.
           destruct c0. easy.
           apply mon_convF.
         + subst.
           punfold H0. punfold H1.
           simpl in H0, H1.
           destruct c0, c, c1.
           pfold. simpl.
           destruct H1 as (H1a,(H1b,H1c)).
           destruct H0 as (H2a,(H2b,H2c)).
           split.
           apply Forall2_conv_trans with (s := l); easy.
           split.
           intros.
           apply H2b in H.
           destruct H as (res2,(Hm,Hn)).
           apply H1b in Hm.
           destruct Hm as (res3,(Hm,Ho)).
           exists res3. split. easy.
           right. apply CIH with (v2 := (TV res2)).
           destruct Hn; easy.
           destruct Ho; easy.
           intros.
           apply H1c in H.
           destruct H as (res2,(Hm,Hn)).
           apply H2c in Hm.
           destruct Hm as (res3,(Hm,Ho)).
           exists res3. split. easy.
           right. apply CIH with (v2 := (TV res2)).
           destruct Ho; easy.
           destruct Hn; easy.
           apply mon_convF.
           apply mon_convF.
         }
         - case_eq v2; intros.
           + subst.
             case_eq v3; intros.
             ++ subst.
                pfold. punfold H0. punfold H1. simpl in *.
                destruct n, n0, n1; try easy.
                * subst. easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TNe n0)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TV w0)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * destruct H1 as (Ha,(Hb,(Hc,Hd))).
                  destruct H0 as (He,(Hf,(Hg,Hh))).
                  split.
                  right. apply CIH with (v2 := (TV w2)).
                  destruct He; easy.
                  destruct Ha; easy.
                  split.
                  right. apply CIH with (v2 := (TV w3)).
                  destruct Hf; easy.
                  destruct Hb; easy.
                  split.
                  right. apply CIH with (v2 := (TV w4)).
                  destruct Hg; easy.
                  destruct Hc; easy.
                  right. apply CIH with (v2 := (TNe n0)).
                  destruct Hh; easy.
                  destruct Hd; easy.
                * destruct H1 as (Ha,(Hb,(Hc,(Hd,He)))).
                  destruct H0 as (Hf,(Hg,(Hh,(Hi,Hj)))).
                  split.
                  right. apply CIH with (v2 := (TV w3)).
                  destruct Hf; easy.
                  destruct Ha; easy.
                  split.
                  right. apply CIH with (v2 := (TV w4)).
                  destruct Hg; easy.
                  destruct Hb; easy.
                  split.
                  right. apply CIH with (v2 := (TV w5)).
                  destruct Hh; easy.
                  destruct Hc; easy.
                  split.
                  right. apply CIH with (v2 := (TV w6)).
                  destruct Hi; easy.
                  destruct Hd; easy.
                  right. apply CIH with (v2 := (TNe n0)).
                  destruct Hj; easy.
                  destruct He; easy.
                * apply mon_convF.
                * apply mon_convF.
             ++ subst.
                punfold H1. simpl in H1. destruct n0; easy.
                apply mon_convF.
             ++ subst.
                punfold H1. simpl in H1. destruct n0; easy.
                apply mon_convF.
           + subst. 
             punfold H0. simpl in H0. destruct n; easy.
             apply mon_convF.
           + subst. 
             punfold H0. simpl in H0. destruct n; easy.
             apply mon_convF.
         - case_eq v2; intros.
           + subst. 
             punfold H0. simpl in H0. destruct w; easy.
             apply mon_convF.
           + subst.
             case_eq v3; intros.
             ++ subst.
                punfold H1. simpl in H1. destruct w0; easy.
                apply mon_convF.
             ++ subst.
                pfold. punfold H0. punfold H1. simpl in *.
                destruct w, w0, w1; try (subst; easy).
                * lia.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as (Ha,Hb).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  assert(vcumul (TV (VPi w c)) (TV (VPi w0 c0))).
                  { pfold. simpl. split. left. easy. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(Hc,Hd)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy. easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TC c0)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as (Ha,Hb).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  assert(vcumul (TV (VLam w c)) (TV (VLam w0 c0))).
                  { pfold. simpl. split. left. easy. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(Hc,Hd)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy. easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TC c0)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as [Ha | Ha].
                  assert(vcumul (TV (VSucc w)) (TV (VSucc w0))).
                  { pfold. simpl. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(Hc,Hd)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy.
                * right. apply CIH with (v2 := (TV w0)).
                  destruct H0; easy.
                  destruct H1; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as [Ha | Ha].
                  punfold Ha. simpl in Ha.
                  destruct n, n0; try easy.
                  subst. easy.
                  inversion Hu1.
                  destruct Ha as (Ha,Hb).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  assert(vcumul (TNe (NApp n w)) (TNe (NApp n0 w0))).
                  { pfold. simpl. split. left. easy. left. easy. }
                  subst.
                  apply vcumul_preserves_value_is_type_at_upto_n with (k := u) in H3.
                  destruct H3 as (j1,(Hc,Hd)).
                  apply VIT_cumul with (j := j1).
                  easy. easy. easy. easy.
                  easy.
                  destruct Ha as (Ha,(Hb,(Hc,Hd))).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  destruct Hc as [Hc | Hc].
                  destruct Hd as [Hd | Hd].
                  assert(vcumul (TNe (NNatRec w w0 w1 n)) (TNe (NNatRec w2 w3 w4 n0))).
                  { pfold. simpl. split. left. easy. split. left. easy. split. left. easy. left. easy. }
                  subst.
                  apply vcumul_preserves_value_is_type_at_upto_n with (k := u) in H.
                  destruct H as (j,(He,Hf)).
                  apply VIT_cumul with (j := j).
                  easy. easy. easy. easy.
                  easy. easy. easy.
                  destruct Ha as (Ha,(Hb,(Hc,(Hd,He)))).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  destruct Hc as [Hc | Hc].
                  destruct Hd as [Hd | Hd].
                  destruct He as [He | He].
                  assert(vcumul (TNe (NVecRec w w0 w1 w2 n)) (TNe (NVecRec w3 w4 w5 w6 n0))).
                  { pfold. simpl. split. left. easy. split. left. easy. split. left. easy. split. left. easy. left. easy. }
                  subst.
                  apply vcumul_preserves_value_is_type_at_upto_n with (k := u) in H.
                  destruct H as (j,(Hf,Hg)).
                  apply VIT_cumul with (j := j).
                  easy. easy. easy. easy.
                  easy. easy. easy. easy.
                  apply mon_convF.
                  easy. easy.
                * right. apply CIH with (v2 := (TNe n0)).
                  destruct H0; easy.
                  destruct H1; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as (Ha,Hb).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  assert(vcumul (TV (VVec w2 w3)) (TV (VVec w0_1 w0_2))).
                  { pfold. simpl. split. left. easy. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(Hc,Hd)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy. easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0_1)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TV w0_2)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as [Ha | Ha].
                  assert(vcumul (TV (VNil w)) (TV (VNil w0))).
                  { pfold. simpl. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(Hc,Hd)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy.
                * right. apply CIH with (v2 := (TV w0)).
                  destruct H0; easy.
                  destruct H1; easy.
                * destruct H0 as (u,(Hu1,Hu2)). exists u. split. easy. lia.
                * destruct H1 as (u,(Hu1,Hu2)). exists u. split.
                  destruct H0 as (Ha,(Hb,(Hc,Hd))).
                  destruct Ha as [Ha | Ha].
                  destruct Hb as [Hb | Hb].
                  destruct Hc as [Hc | Hc].
                  destruct Hd as [Hd | Hd].
                  assert(vcumul (TV (VCons w2 w3 w4 w5)) (TV (VCons w0_1 w0_2 w0_3 w0_4))).
                  { pfold. simpl. split. left. easy. split. left. easy. split. left. easy. left. easy. }
                  apply vcumul_preserves_value_is_type_at_upto with (k := u) in H.
                  destruct H as (j,(He,Hf)).
                  apply VIT_cumul with (j := j); easy.
                  easy. easy. easy. easy. easy. easy.
                * destruct H1 as (Ha,(Hb,(Hc,Hd))).
                  destruct H0 as (He,(Hf,(Hg,Hh))).
                  split.
                  right. apply CIH with (v2 := (TV w0_1)).
                  destruct He; easy.
                  destruct Ha; easy.
                  split.
                  right. apply CIH with (v2 := (TV w0_2)).
                  destruct Hf; easy.
                  destruct Hb; easy.
                  split.
                  right. apply CIH with (v2 := (TV w0_3)).
                  destruct Hg; easy.
                  destruct Hc; easy.
                  right. apply CIH with (v2 := (TV w0_4)).
                  destruct Hh; easy.
                  destruct Hd; easy.
                * apply mon_convF.
                * apply mon_convF.
             ++ subst.
                punfold H1. simpl in H1. destruct w0; easy.
                apply mon_convF.
           + subst.
             punfold H0. simpl in H0. destruct w; easy.
             apply mon_convF.
Qed.

Lemma synth_preserve_eval_for_types :
  (forall Γ t A (He : synth Γ t A),
    forall v, is_type_shape t -> eval' Γ t v -> vcumul_v v A)
  /\
  (forall Γ t A (He : check Γ t A),
     forall v, is_type_shape t -> eval' Γ t v -> vcumul_v v A).
Proof.
  eapply (typing_mutind
    (fun (Γ : ctx) (t : term) (A : whnf) (He : synth Γ t A) =>
       forall v, is_type_shape t -> eval' Γ t v -> vcumul_v v A)
    (fun (Γ : ctx) (t : term) (A : whnf) (He : check Γ t A) =>
       forall v, is_type_shape t -> eval' Γ t v -> vcumul_v v A)).
  18:{ intros. apply H in H1. apply aa with (k := k) in H1. easy. easy. easy. }
  17:{ intros. inversion H0. subst. 
       assert(v0 = vres).
       { specialize(eval'_det  _ _ _ _ e H6); intro HHa.
         specialize(eval'_det  _ _ _ _ e0 H8); intro HHb.
         specialize(eval'_det  _ _ _ _ e1 H10); intro HHc.
         specialize(eval'_det  _ _ _ _ e2 H11); intro HHd.
         specialize(eval'_det  _ _ _ _ e3 H12); intro HHe.
         subst.
         specialize(eval_vecrec_det _ _ _ _ _ _ _ e4 H13); intro HHf.
         easy.
       }
      subst. easy.
  }
  16:{ intros. inversion H0. subst.
       assert(v = v1).
       { specialize(eval'_det  _ _ _ _ e H5); intro HHa.
         specialize(eval'_det  _ _ _ _ e0 H7); intro HHb.
         specialize(eval'_det  _ _ _ _ e1 H9); intro HHc.
         specialize(eval'_det  _ _ _ _ e2 H10); intro HHd.
         subst.
         specialize(eval_natrec_det _ _ _ _ _ _ e3 H11); intro HHf.
         easy.
       }
       subst. easy.
     }
  15:{ intros. inversion H1. }
  14:{ intros. apply H in H1.
       apply conv_trans with (v2 := (TV A')); easy. easy. }
  13:{ intros. inversion H1. }
  12:{ intros. inversion H0. subst.
       assert(v = vres).
       { specialize(eval'_det  _ _ _ _ e H6); intro HHa.
         specialize(eval'_det  _ _ _ _ e0 H8); intro HHb.
         specialize(eval'_det  _ _ _ _ e1 H10); intro HHc.
         specialize(eval'_det  _ _ _ _ e2 H11); intro HHd.
         specialize(eval'_det  _ _ _ _ e3 H12); intro HHe.
         subst.
         specialize(eval_vecrec_det _ _ _ _ _ _ _ e4 H13); intro HHf.
         easy.
       }
       subst. apply conv_refl.
     }
  11:{ intros. inversion H1. }
  10:{ intros. inversion H. }
  9:{ intros. inversion H0. subst.
      pfold. simpl.
      assert(vA = vA0).
      { specialize(eval'_det  _ _ _ _ e H4); intro HHa.
      specialize(eval'_det  _ _ _ _ e0 H6); intro HHb.
      subst.
      easy.
      }
      assert(vn = vn0).
      { specialize(eval'_det  _ _ _ _ e0 H6); intro HHb.
      subst. easy.
      }
      subst. split. left.
      apply conv_refl.
      left.
      apply conv_refl.
      }
  8:{ intros. inversion H0. subst.
      assert(v0 = v).
      { specialize(eval'_det  _ _ _ _ e H5); intro HHa.
      specialize(eval'_det  _ _ _ _ e0 H7); intro HHb.
      specialize(eval'_det  _ _ _ _ e1 H9); intro HHc.
      specialize(eval'_det  _ _ _ _ e2 H10); intro HHd.
      subst.
      specialize(eval_natrec_det _ _ _ _ _ _ e3 H11); intro HHf.
      easy.
      }
      subst. apply conv_refl.
    }
  7:{ intros. inversion H0. }
  6:{ intros. inversion H. }
  5:{ intros. inversion H0. subst.
      inversion H1. subst.
      assert(vu = vu0).
      { specialize(eval'_det  _ _ _ _ e H7); intro HHa. easy. }
      subst.
      apply H in H5.
      assert(vcumul_v vt0 (VPi vdom (Cl ρB Bterm))).
      { apply conv_trans with (v2 := (TV vt)); easy. }
      punfold H2. simpl in H2.
      destruct vt0; try easy.
      inversion H9.
      + subst.
        destruct H2 as (Ha,Hb).
        destruct Hb as [Hb | Hb].
        punfold Hb. simpl in Hb.
        destruct Hb as (Hb,(Hc,Hd)).
        apply Hd in e1.
        destruct e1 as (r2,(e1,e2)).
        assert(v0 = r2).
        { specialize(eval'_det  _ _ _ _ e1 H11); intro HHa. easy. }
        subst.
        destruct e2; easy.
        apply mon_convF.
        easy.
      + apply mon_convF.
      + easy. 
     }
   4:{ intros. inversion H0. subst.
       inversion H1. subst.
       assert(vA = vA0).
       { specialize(eval'_det  _ _ _ _ e H8); intro HHa. easy. }
        subst.
       pfold. simpl.
       split. left. apply conv_refl. left. apply conv_refl.
     }
   3:{ intros. inversion H0. subst.
      pfold. simpl. easy. }
   2:{ intros. inversion H0. subst. pfold. simpl. lia. }
   1:{ intros. inversion H0.
       + subst. rewrite e in H3. inversion H3.
          apply conv_refl.
       + subst. rewrite e in H3. easy. }
Qed.

Lemma synth_preserve_eval :
  forall Γ t A v,
    is_type_shape t ->
    eval' Γ t v ->
    synth Γ t A ->
    vcumul_v v A.
Proof.
  intros Γ t A v Hclosed Heval Hs.
  specialize (synth_preserve_eval_for_types); intros (Ha, Hb).
  specialize(Ha Γ t).
  apply Ha; easy.
Qed.

Lemma check_preserve_eval :
  forall Γ t A v,
    is_type_shape t ->
    eval' Γ t v ->
    check Γ t A ->
    vcumul_v v A.
Proof.
  intros Γ t A v Hclosed Heval Hc.
  eapply (proj2 synth_preserve_eval_for_types); eauto.
Qed.

Lemma progress_mut :
  (forall Γ t A (Hs : synth Γ t A),  Γ = [] -> is_type_shape t -> exists v, eval' [] t v)
  /\
  (forall Γ t A (Hc : check Γ t A),  Γ = [] -> is_type_shape t ->  exists v, eval' [] t v).
Proof.
  (* use predicates that mention Γ so typing_mutind can accept them,
     but require Γ = [] inside the predicate *)
  eapply (typing_mutind
    (fun (Γ : ctx) (t : term) (A : whnf) (He : synth Γ t A) =>
       Γ = [] -> is_type_shape t -> exists v, eval' [] t v)
    (fun (Γ : ctx) (t : term) (A : whnf) (He : check Γ t A) =>
       Γ = [] -> is_type_shape t -> exists v, eval' [] t v)
  ).
  4:{
  intros.
  subst.
  exists (VPi vA (Cl [] B)).
  apply E'_Pi.
  exact e.
  }
  4:{
  intros. subst.
  specialize(H eq_refl).
  inversion H1. subst. apply H in H2.
  destruct H2 as (vta, Hvta).
  punfold v.
  simpl in v.
  destruct vt; try easy.
  destruct v as (Ha,Hb).
  destruct Ha as [Ha | Ha].
  assert(vcumul_v vta (VPi vt c)).
  { inversion H1. subst.
    specialize(synth_preserve_eval _ _ _ _ H2 Hvta s); intro HH.
    easy.
  }
  punfold H0. simpl in H0.
  destruct vta; try easy.
  destruct H0 as (Hc,Hd).
  destruct Hc as [Hc | Hc].

  inversion Hvta.
  + subst.
    rewrite nth_error_nil in H0. easy.
  + subst.
    assert(ρB = []).
    { destruct Hb as [Hb | Hb].
      punfold Hb. simpl in Hb.
      destruct c.
      destruct Hb. 
      destruct Hd as [Hd | Hd].
      punfold Hd. simpl in Hd.
      destruct Hd.
      inversion H3. subst.
      inversion H0. easy.
      apply mon_convF.
      easy.
      apply mon_convF.
      easy.
    }
    subst.
    assert(HCC: paco2 convF_cumul bot2 (TC (Cl [] B)) (TC (Cl [] Bterm))).
    { destruct Hd as [Hd | Hd].
      destruct Hb as [Hb | Hb].
      apply conv_trans with (v2 := (TC c)); easy.
      easy. easy.
    }
    punfold HCC. simpl in HCC.
    destruct HCC as (Hc1,(Hc2,Hc3)).
    apply Hc3 in e1.
    destruct e1 as (res1,(He1,He2)).
    exists res1.
    apply E'_App with (vt := (VPi vta (Cl [] B))) (vu := vu); try easy.
    apply VApp_Pi_sharp with (body := B).
    easy.
    apply mon_convF.
  + subst.
    destruct c0.
    assert(HCC: paco2 convF_cumul bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
    { destruct Hd as [Hd | Hd].
      destruct Hb as [Hb | Hb].
      apply conv_trans with (v2 := (TC c)); easy.
      easy. easy.
    }
    punfold HCC. simpl in HCC.
    destruct HCC as (Hc1,(Hc2,Hc3)).
    apply Hc3 in e1.
    destruct e1 as (res1,(He1,He2)).
    exists res1.
    apply E'_App with (vt := (VPi vta (Cl l t))) (vu := vu); try easy.
    eapply VApp_Pi_sharp. easy.
    apply mon_convF.
   + subst.
     destruct c0.
     assert(HCC: paco2 convF_cumul bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
    { destruct Hd as [Hd | Hd].
      destruct Hb as [Hb | Hb].
      apply conv_trans with (v2 := (TC c)); easy.
      easy. easy.
    }
     punfold HCC. simpl in HCC.
     destruct HCC as (Hc1,(Hc2,Hc3)).
     apply Hc3 in e1.
     destruct e1 as (res1,(He1,He2)).
     exists res1.
     apply E'_App with (vt := (VPi vta (Cl l t))) (vu := vu); try easy.
     eapply VApp_Pi_sharp. easy.
     apply mon_convF.
   + subst.
     destruct c0.
     assert(HCC: paco2 convF_cumul bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
    { destruct Hd as [Hd | Hd].
      destruct Hb as [Hb | Hb].
      apply conv_trans with (v2 := (TC c)); easy.
      easy. easy.
    }
     punfold HCC. simpl in HCC.
     destruct HCC as (Hc1,(Hc2,Hc3)).
     apply Hc3 in e1.
     destruct e1 as (res1,(He1,He2)).
     exists res1.
     apply E'_App with (vt := (VPi vta (Cl l t))) (vu := vu); try easy.
     eapply VApp_Pi_sharp. easy.
     apply mon_convF.
   + easy.
   + apply mon_convF.
   + easy.
   + apply mon_convF.
  }
  15:{
  intros.
  subst.
  exists vres.
  apply E'_VecRec with (vt:=vt) (vP:=vP) (vnil:=vnil) (vcons:=vcons) (vn:=vn).
  all: auto.
  }
  14:{
  intros.
  subst.
  exists v.
  eapply E'_NatRec; eauto.
  }
  13:{
  intros.
  inversion H2.
  }
  12:{
  intros.
  subst. specialize(H eq_refl).
  apply H in H1.
  destruct H1 as (v1,H1).
  exists v1. easy.
  }
  11:{
  intros.
  inversion H2.
  }
  10:{
  intros. subst.
  exists vres.
  apply E'_VecRec with (vt:=vt) (vP:=vP) (vnil:=vnil) (vcons:=vcons) (vn:=vn); easy.
  }
  9:{
  intros.
  inversion H2.
  }
  8:{
  intros.
  inversion H0.
  }
  7:{
  intros. subst.
  exists (VVec vA vn).
  apply E'_Vec; easy.
  }
  6:{
  intros.
  subst.
  exists v.
  eapply E'_NatRec; eauto.
  }
  5:{
  intros.
  inversion H1.
  }
  4:{
  intros.
  inversion H0.
  }
  3:{
  intros.
  subst.
  exists VNat. 
  apply E'_Nat.
  }
  3:{
  intros.
  subst. specialize(H eq_refl).
  apply H in H1.
  destruct H1 as (v1,H1).
  exists v1. easy.
  }
  2:{
  intros.
  subst.
  exists (VType i).
  apply E'_Type.
  }
  1:{
  intros.
  subst.
  rewrite nth_error_nil in e.
  easy.
  }
Qed.

Lemma synth_progress :
  forall t A,
    synth [] t A ->
    is_type_shape t ->
    exists v, eval' [] t v.
Proof. 
  intros t A Heq Hclosed.
  eapply (proj1 progress_mut); eauto.
Qed.

Lemma check_progress :
  forall t A,
    check [] t A ->
    is_type_shape t ->
    exists v, eval' [] t v.
Proof.
  intros t A Heq Hclosed.
  eapply (proj2 progress_mut); eauto.
Qed.

Theorem type_safety_mut :
  (forall t A, synth [] t A -> is_type_shape t -> exists v, eval' [] t v /\ vcumul_v v A)
  /\
  (forall t A, check [] t A -> is_type_shape t -> exists v, eval' [] t v /\ vcumul_v v A).
Proof.
  split.
  - intros t A Hs Hclosed.
    (* progress for synth gives a value *)
    destruct (synth_progress t A Hs Hclosed) as [v Hev].
    (* preservation (synth_preserve_eval) gives convertibility of A and v *)
    specialize (synth_preserve_eval [] t A v Hclosed Hev Hs).
    exists v; split; auto.
  - intros t A Hc Hclosed.
    destruct (check_progress t A Hc Hclosed) as [v Hev].
    specialize (check_preserve_eval [] t A v Hclosed Hev Hc).
    exists v; split; auto.
Qed.

Lemma synth_type_safety :
  forall t A,
    synth [] t A ->
    is_type_shape t ->
    exists v, eval' [] t v /\ vcumul_v v A.
Proof.
  intros t A Heq Hclosed.
  eapply (proj1 type_safety_mut); eauto.
Qed.

Lemma check_type_safety :
  forall t A,
    check [] t A ->
    is_type_shape t ->
    exists v, eval' [] t v /\ vcumul_v v A.
Proof.
  intros t A Heq Hclosed.
  eapply (proj2 type_safety_mut); eauto.
Qed.



(* === Mutual fuelled evaluator (corrected vecrec application order) === *)

Fixpoint fuel_eval (fuel : nat) (ρ : list whnf) (t : term) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match t with
    | Type__ i => Some (VType i)
    | Nat => Some VNat
    | Var x =>
        match nth_error ρ x with
        | Some v => Some v
        | None => Some (VNeutral (NVar (x - length ρ)))
        end
    | Pi A B =>
        match fuel_eval fuel' ρ A with
        | Some vA => Some (VPi vA (Cl ρ B))
        | None => None
        end
    | Lam A b =>
        match fuel_eval fuel' ρ A with
        | Some vA => Some (VLam vA (Cl ρ b))
        | None => None
        end
    | App t1 t2 =>
        match fuel_eval fuel' ρ t1, fuel_eval fuel' ρ t2 with
        | Some vt, Some vu => fuel_vapp fuel' vt vu
        | _, _ => None
        end
    | Zero => Some VZero
    | Succ n =>
        match fuel_eval fuel' ρ n with
        | Some vn => Some (VSucc vn)
        | None => None
        end
    | NatRec P z s n =>
        match fuel_eval fuel' ρ P, fuel_eval fuel' ρ z, fuel_eval fuel' ρ s, fuel_eval fuel' ρ n with
        | Some vP, Some vz, Some vs, Some vn => fuel_natrec fuel' vP vz vs vn
        | _, _, _, _ => None
        end
    | Vec A n =>
        match fuel_eval fuel' ρ A, fuel_eval fuel' ρ n with
        | Some vA, Some vn => Some (VVec vA vn)
        | _, _ => None
        end
    | Nil A =>
        match fuel_eval fuel' ρ A with
        | Some vA => Some (VNil vA)
        | None => None
        end
    | Cons A n x xs =>
        match fuel_eval fuel' ρ A, fuel_eval fuel' ρ n, fuel_eval fuel' ρ x, fuel_eval fuel' ρ xs with
        | Some vA, Some vn, Some vx, Some vxs => Some (VCons vA vn vx vxs)
        | _, _, _, _ => None
        end
    | VecRec P nl cns n t =>
        match fuel_eval fuel' ρ P, fuel_eval fuel' ρ nl, fuel_eval fuel' ρ cns, fuel_eval fuel' ρ n, fuel_eval fuel' ρ t with
        | Some vP, Some vnil, Some vcons, Some vn, Some vt => fuel_vecrec fuel' vP vnil vcons vn vt
        | _, _, _, _, _ => None
        end
    end
  end

with fuel_vapp (fuel : nat) (vf arg : whnf) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vf with
    | VLam _ cl =>
        let ρbody := env_of_cl cl in
        let body := body_of_cl cl in
        fuel_eval fuel' (arg :: ρbody) body
    | VPi _ cl =>
        let ρbody := env_of_cl cl in
        let body := body_of_cl cl in
        fuel_eval fuel' (arg :: ρbody) body
    | VNeutral n => Some (VNeutral (NApp n arg))
    | _ => None
    end
  end

with fuel_natrec (fuel : nat) (vP vz vs vn : whnf) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vn with
    | VZero => Some vz
    | VSucc vn' =>
        match fuel_natrec fuel' vP vz vs vn' with
        | None => None
        | Some vrec =>
            match fuel_vapp fuel' vs vn' with
            | None => None
            | Some v1 =>
                match fuel_vapp fuel' v1 vrec with
                | None => None
                | Some v => Some v
                end
            end
        end
    | VNeutral n => Some (VNeutral (NNatRec vP vz vs n))
    | _ => None
    end
  end

with fuel_vecrec (fuel : nat)
     (vP vnil vcons vindex vt : whnf) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vt with
    | VNil _ => Some vnil
    | VCons vA vn' vx vxs =>
        match fuel_vecrec fuel' vP vnil vcons vindex vxs with
        | None => None
        | Some vrec =>
            (* NEW: apply vcons to vindex (k), then to vx, then to vxs, then to vrec *)
            match fuel_vapp fuel' vcons vindex with
            | None => None
            | Some v1 =>
                match fuel_vapp fuel' v1 vx with
                | None => None
                | Some v2 =>
                    match fuel_vapp fuel' v2 vxs with
                    | None => None
                    | Some v3 =>
                        match fuel_vapp fuel' v3 vrec with
                        | None => None
                        | Some v => Some v
                        end
                    end
                end
            end
        end
    | VNeutral n => Some (VNeutral (NVecRec vP vnil vcons vindex n))
    | _ => None
    end
  end.


(* ---------- small helpers & wrappers over the mutual fuelled evaluator ---------- *)

(* wrapper that runs the mutual fuelled evaluator with an explicit fuel *)
Definition evalk (fuel : nat) (ρ : list whnf) (t : term) : option whnf :=
  fuel_eval fuel ρ t.

(* convenient default-evaluator with a moderate fuel (you may set this as you like) *)
Definition default_fuel := 200%nat.
Definition eval (ρ : list whnf) (t : term) : option whnf := evalk default_fuel ρ t.

(* ---------- small motives and helpers used in your definitions ---------- *)

(* constant motive P : Nat -> Star  represented as a (term-level) lambda that
   ignores its argument and returns Nat at runtime *)
Definition PconstNat : term := Lam Nat Nat.

(* ---------- arithmetic (add, mult) using NatRec --- exactly as you wrote, adapted ---------- *)

Definition add_term : term :=
  Lam Nat (                             (* m : Nat (de Bruijn: Var 1 inside) *)
    Lam Nat (                           (* n : Nat (Var 0 inside) *)
      NatRec
        PconstNat                       (* P : Nat -> Star, here constant Nat *)
        (Var 1)                         (* base: m  (note Var 1 because two nested lambdas) *)
        (Lam Nat                        (* step: λ k:Nat. λ acc:Nat. Succ acc *)
          (Lam (App PconstNat (Var 0))  (* annotation of acc; runtime ignores it - matches shape *)
               (Succ (Var 0))))
        (Var 0)                         (* recurse on n *)
  )).

Definition mult_term : term :=
  Lam Nat (                             (* m *)
    Lam Nat (                           (* n *)
      NatRec
        PconstNat                       (* motive: Nat *)
        Zero                            (* base: 0 *)
        (Lam Nat
          (Lam (App PconstNat (Var 0))  (* acc : Nat *)
               (App (App add_term (Var 2))   (* add n acc ; n is Var 2 here (due to lambdas) *)
                    (Var 0))))
        (Var 1)                         (* recurse on m *)
  )).

(* ---------- wrappers to test add / mult using the fuelled evaluator ---------- *)

Compute (evalk 200 [] (App (App add_term (Succ (Succ (Succ Zero)))) (Succ Zero))).

Compute (evalk 200 [] (App (App add_term (Succ (Succ Zero))) (Succ Zero))).  (* 2 + 1 = 3 *)

Compute (evalk 200 [] (App (App mult_term (Succ Zero)) (Succ (Succ (Succ (Succ Zero)))))). (* 1 * 4 = 4 *)

(* ---------- numerals (object language) ---------- *)

Definition one  : term := Succ Zero.
Definition two  : term := Succ one.
Definition three: term := Succ two.
Definition four : term := Succ three.
Definition five  : term := Succ four.
Definition six   : term := Succ five.
Definition seven  : term := Succ six.
Definition eighth : term := Succ seven.
Definition nine : term := Succ eighth.

Compute (evalk 200 [] (App (App add_term two) one)).   (* expect 3 *)

Compute (evalk 200 [] (App (App mult_term one) four)). (* expect 4 *)

(* ---------- Vector append example (uses Vec / Nil / Cons / VecRec) ---------- *)

(* plus k m := m + k, via add *)
Definition tm_plus (k m : term) : term := App (App add_term k) m.

(* step function for VecRec:
   λ k:Nat. λ a:A. λ xs:Vec k A. λ ih:Vec (plus k m) A.
      Cons A (plus k m) a ih
*)
Definition tm_s_cons (A m : term) : term :=
  Lam Nat
    (Lam A
      (Lam (Vec (Var 1) A)
        (Lam (Vec (tm_plus (Var 2) m) A)
             (Cons A (tm_plus (Var 3) m) (Var 2) (Var 0))))).

(* Motive just to satisfy typing; runtime eval doesn't depend on it *)
Definition tm_vec_motive (A m : term) : term :=
  Lam Nat (Lam (Vec (Var 0) A) (Vec (tm_plus (Var 1) m) A)).

(* append A n xs m ys := VecRec (tm_vec_motive A m) ys (tm_s_cons A m) n xs *)
Definition tm_append (A n xs m ys : term) : term :=
  VecRec (tm_vec_motive A m)  (* P  : motive *)
         ys                   (* nil: base *)
         (tm_s_cons A m)      (* cons: step *)
         n                    (* n  : index *)
         xs.                  (* t  : vector to recurse on *)

(* [1]  and  [1;2]  as terms -- use term-level constructors Nil / Cons, not WHNF VNil/VCons *)
Definition tm_vnil_nat : term := Nil Nat.
Definition tm_v1 : term :=
  Cons Nat Zero (Succ Zero) tm_vnil_nat.                 (* [1] *)

Definition tm_v12 : term :=
  Cons Nat (Succ Zero) (Succ Zero)                       (* head 1, index = 1 *)
        (Cons Nat Zero (Succ (Succ Zero)) tm_vnil_nat).  (* tail [2] *)

Definition tm_v3 : term :=
  Cons Nat Zero (Succ (Succ (Succ Zero))) tm_vnil_nat.

Definition tm_append_v12_v3 : term :=
  tm_append Nat (Succ (Succ Zero)) tm_v12 (Succ Zero) tm_v3.

Definition bigfuel := 500%nat.

Compute (evalk bigfuel [] tm_append_v12_v3).


(* Put this after your whnf/neutral/closure/eval' definitions. *)

Section ConvFuelCorrected.

  (* supply a fuelled term evaluator: nat -> env -> term -> option whnf *)
  Variable eval_term_fuel : nat -> list whnf -> term -> option whnf.

  (* non-recursive helper to evaluate a closure with one arg using the fuelled evaluator *)
  Definition eval_closure_with_arg_fuel (fuel : nat) (cl : closure) (arg : whnf)
    : option whnf :=
    match cl with Cl rho t => eval_term_fuel fuel (arg :: rho) t end.

  (* Mutual Fixpoint: conv_fuel, conv_neutral_fuel, envs_conv_b, conv_closure_b.
     Each function matches on fuel as the first argument so recursive calls
     are on a strictly smaller fuel (S f' -> use f'). *)
  Fixpoint conv_fuel (fuel : nat) (v w : whnf) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S f' =>
      match v, w with
      | VType i, VType j => Nat.eqb i j
      | VNat, VNat => true
      | VPi a cl, VPi a' cl' =>
          andb (conv_fuel f' a a') (conv_closure_b f' cl cl')
      | VLam a cl, VLam a' cl' =>
          andb (conv_fuel f' a a') (conv_closure_b f' cl cl')
      | VZero, VZero => true
      | VSucc n1, VSucc n2 => conv_fuel f' n1 n2
      | VNeutral n1, VNeutral n2 => conv_neutral_fuel f' n1 n2
      | VVec a n, VVec a' n' =>
          andb (conv_fuel f' a a') (conv_fuel f' n n')
      | VNil a, VNil a' => conv_fuel f' a a'
      | VCons a n x xs, VCons a' n' x' xs' =>
          andb (conv_fuel f' a a')
               (andb (conv_fuel f' n n')
                     (andb (conv_fuel f' x x') (conv_fuel f' xs xs')))
      | _, _ => false
      end
    end

  with conv_neutral_fuel (fuel : nat) (n n' : neutral) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S f' =>
      match n, n' with
      | NVar i, NVar j => Nat.eqb i j
      | NApp n1 v1, NApp n2 v2 =>
          andb (conv_neutral_fuel f' n1 n2) (conv_fuel f' v1 v2)
      | NNatRec P z s nn, NNatRec P' z' s' nn' =>
          andb (conv_fuel f' P P')
               (andb (conv_fuel f' z z')
                     (andb (conv_fuel f' s s') (conv_neutral_fuel f' nn nn')))
      | NVecRec P nl cns idx nn, NVecRec P' nil' cons' idx' nn' =>
          andb (conv_fuel f' P P')
               (andb (conv_fuel f' nl nil')
                     (andb (conv_fuel f' cns cons')
                           (andb (conv_fuel f' idx idx')
                                 (conv_neutral_fuel f' nn nn'))))
      | _, _ => false
      end
    end

  with envs_conv_b (fuel : nat) (ρ1 ρ2 : list whnf) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S f' =>
      match ρ1, ρ2 with
      | [], [] => true
      | v1 :: r1, v2 :: r2 => andb (conv_fuel f' v1 v2) (envs_conv_b f' r1 r2)
      | _, _ => false
      end
    end

  with conv_closure_b (fuel : nat) (cl1 cl2 : closure) {struct fuel} : bool :=
    match fuel with
    | 0 => false
    | S f' =>
      match cl1, cl2 with
      | Cl ρ1 t1, Cl ρ2 t2 =>
          let env_ok := envs_conv_b f' ρ1 ρ2 in
          if env_ok then
            let witness := VNeutral (NVar 0) in
            match eval_closure_with_arg_fuel f' cl1 witness,
                  eval_closure_with_arg_fuel f' cl2 witness with
            | Some r1, Some r2 => conv_fuel f' r1 r2
            | _, _ => false
            end
          else false
      end
    end.

End ConvFuelCorrected.

















From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Paco Require Import paco.

(* --- assume previous definitions from the user: conv_tag, value_is_type_at,
       env_of_cl, body_of_cl, eval', vcumul, etc. --- *)

(* A small boolean helper for nat <= check returning bool *)
Definition leb_bool (n m : nat) : bool := Nat.leb n m.

(* syntactic equality for terms (separate, non-recursive) *)
Fixpoint term_eqb (t1 t2 : term) : bool :=
  match t1, t2 with
  | Type__ i1, Type__ i2 => Nat.eqb i1 i2
  | Nat, Nat => true
  | Pi a1 b1, Pi a2 b2 => andb (term_eqb a1 a2) (term_eqb b1 b2)
  | Zero, Zero => true
  | Succ n1, Succ n2 => term_eqb n1 n2
  | Var x1, Var x2 => Nat.eqb x1 x2
  | Lam A1 b1, Lam A2 b2 => andb (term_eqb A1 A2) (term_eqb b1 b2)
  | App f1 a1, App f2 a2 => andb (term_eqb f1 f2) (term_eqb a1 a2)
  | NatRec P1 z1 s1 n1, NatRec P2 z2 s2 n2 =>
      andb (andb (term_eqb P1 P2) (term_eqb z1 z2)) (andb (term_eqb s1 s2) (term_eqb n1 n2))
  | Vec A1 n1, Vec A2 n2 => andb (term_eqb A1 A2) (term_eqb n1 n2)
  | Nil A1, Nil A2 => term_eqb A1 A2
  | Cons A1 n1 x1 xs1, Cons A2 n2 x2 xs2 =>
      andb (andb (term_eqb A1 A2) (term_eqb n1 n2)) (andb (term_eqb x1 x2) (term_eqb xs1 xs2))
  | VecRec P1 nl1 c1 n1 t1, VecRec P2 nl2 c2 n2 t2 =>
      andb (andb (term_eqb P1 P2) (term_eqb nl1 nl2))
           (andb (andb (term_eqb c1 c2) (term_eqb n1 n2)) (term_eqb t1 t2))
  | _, _ => false
  end.

(* --- Mutual Fixpoint where fuel is the structural argument for ALL functions --- *)
Fixpoint fuel_vcumul (fuel : nat) (x y : conv_tag) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match x, y with
    | TV (VType i), TV (VType j) => Some (leb_bool i j)

    (* Do NOT accept arbitrary values as VType *)
    | TV _ , TV (VType _) => Some false

    | TV VNat, TV VNat => Some true
    | TV VZero, TV VZero => Some true

    | TV (VSucc n1), TV (VSucc n2) =>
        (* pass fuel' as first arg everywhere *)
        match fuel_vcumul fuel' (TV n1) (TV n2) with
        | None => None | Some b => Some b
        end

    | TV (VNeutral n1), TV (VNeutral n2) =>
        fuel_vcumul_neutral fuel' n1 n2

    | TV (VVec a1 n1), TV (VVec a2 n2) =>
        match fuel_vcumul fuel' (TV a1) (TV a2) with
        | None => None
        | Some true =>
            match fuel_vcumul fuel' (TV n1) (TV n2) with
            | None => None | Some b => Some b end
        | Some false => Some false
        end

    | TV (VNil a1), TV (VNil a2) =>
        fuel_vcumul fuel' (TV a1) (TV a2)

    | TV (VCons a1 n1 x1 xs1), TV (VCons a2 n2 x2 xs2) =>
        match fuel_vcumul fuel' (TV a1) (TV a2) with
        | None => None
        | Some true =>
            match fuel_vcumul fuel' (TV n1) (TV n2) with
            | None => None
            | Some true =>
                match fuel_vcumul fuel' (TV x1) (TV x2) with
                | None => None
                | Some true => fuel_vcumul fuel' (TV xs1) (TV xs2)
                | Some false => Some false
                end
            | Some false => Some false
            end
        | Some false => Some false
        end

    | TV (VLam vA1 cl1), TV (VLam vA2 cl2) =>
        match fuel_vcumul fuel' (TV vA1) (TV vA2) with
        | None => None
        | Some true => fuel_vcumul_closure fuel' cl1 cl2
        | Some false => Some false
        end

    | TV (VPi vA1 cl1), TV (VPi vA2 cl2) =>
        match fuel_vcumul fuel' (TV vA1) (TV vA2) with
        | None => None
        | Some true => fuel_vcumul_closure fuel' cl1 cl2
        | Some false => Some false
        end

    | TNe n1, TNe n2 => fuel_vcumul_neutral fuel' n1 n2

    | TC (Cl ρ1 t1), TC (Cl ρ2 t2) =>
        if Nat.eqb (length ρ1) (length ρ2) then
          if term_eqb t1 t2 then
            (* pass fuel' as first arg to satisfy structural decrease on 'fuel' *)
            fuel_vcumul_envlist fuel' ρ1 ρ2
          else Some false
        else Some false

    | _, _ => Some false
    end
  end

with fuel_vcumul_neutral (fuel : nat) (n1 n2 : neutral) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match n1, n2 with
    | NVar i1, NVar i2 => Some (Nat.eqb i1 i2)
    | NApp n1' v1, NApp n2' v2 =>
        match fuel_vcumul_neutral fuel' n1' n2' with
        | None => None
        | Some true => fuel_vcumul fuel' (TV v1) (TV v2)
        | Some false => Some false
        end
    | NNatRec P1 z1 s1 n1', NNatRec P2 z2 s2 n2' =>
        match fuel_vcumul fuel' (TV P1) (TV P2) with
        | None => None
        | Some true =>
            match fuel_vcumul fuel' (TV z1) (TV z2) with
            | None => None
            | Some true =>
                match fuel_vcumul fuel' (TV s1) (TV s2) with
                | None => None
                | Some true => fuel_vcumul_neutral fuel' n1' n2'
                | Some false => Some false
                end
            | Some false => Some false
            end
        | Some false => Some false
        end
    | NVecRec P1 nil1 cons1 idx1 n1', NVecRec P2 nil2 cons2 idx2 n2' =>
        match fuel_vcumul fuel' (TV P1) (TV P2) with
        | None => None
        | Some true =>
            match fuel_vcumul fuel' (TV nil1) (TV nil2) with
            | None => None
            | Some true =>
                match fuel_vcumul fuel' (TV cons1) (TV cons2) with
                | None => None
                | Some true =>
                    match fuel_vcumul fuel' (TV idx1) (TV idx2) with
                    | None => None
                    | Some true => fuel_vcumul_neutral fuel' n1' n2'
                    | Some false => Some false
                    end
                | Some false => Some false
                end
            | Some false => Some false
            end
        | Some false => Some false
        end
    | _, _ => Some false
    end
  end

with fuel_vcumul_envlist (fuel : nat) (ρ1 ρ2 : list whnf) {struct fuel} : option bool :=
  (* structural argument is fuel. On each recursive step we use a smaller fuel. *)
  match fuel with
  | 0 => None
  | S fuel' =>
    match ρ1, ρ2 with
    | [], [] => Some true
    | v1::r1, v2::r2 =>
        match fuel_vcumul fuel' (TV v1) (TV v2) with
        | None => None
        | Some true => fuel_vcumul_envlist fuel' r1 r2
        | Some false => Some false
        end
    | _, _ => Some false
    end
  end

with fuel_vcumul_closure (fuel : nat) (cl1 cl2 : closure) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match cl1, cl2 with
    | Cl ρ1 t1, Cl ρ2 t2 =>
        if term_eqb t1 t2 then fuel_vcumul_envlist fuel' ρ1 ρ2 else Some false
    end
  end.

(* ---------------------------
   Helpful local notations
   --------------------------- *)
Notation "'TV' v" := (TV v) (at level 0).
Notation "'TNe' n" := (TNe n) (at level 0).
Notation "'TC' c" := (TC c) (at level 0).

(* small convenience WHNF values *)
Definition vt0 := VType 0.
Definition vt1 := VType 1.
Definition vnat := VNat.
Definition vzero := VZero.
Definition vsucc1 := VSucc VZero.    (* succ 0 *)
Definition vsucc2 := VSucc vsucc1.   (* succ (succ 0) *)

(* neutrals *)
Definition nvar0 := NVar 0.
Definition nvar1 := NVar 1.
Definition napp_vnat_on_var0 := NApp (NVar 0) VNat.

(* closures for testing *)
Definition cl_empty_var0 := Cl [] (Var 0).
Definition cl_empty_var1 := Cl [] (Var 1).
Definition cl_oneenv_var0 := Cl [VNat] (Var 0).
Definition cl_oneenv_var1 := Cl [VNat] (Var 1).

(* some vec-like values *)
Definition vvec_nat_1 := VVec VNat (VSucc VZero).   (* Vec Nat 1 *)
Definition vvec_nat_2 := VVec VNat (VSucc (VSucc VZero)). (* Vec Nat 2 *)
Definition vnil_nat := VNil VNat.
Definition vcons_nat_1 := VCons VNat (VSucc VZero) VZero (VNil VNat).

(* ---------------------------
   Basic universe / simple cases
   --------------------------- *)

(* VType i <= VType j uses nat-le *)
Eval compute in (fuel_vcumul 5 (TV vt0) (TV vt1)).
(* = Some true     -- because 0 <= 1 *)

Eval compute in (fuel_vcumul 5 (TV vt1) (TV vt0)).
(* = Some false    -- because 1 <= 0 is false *)

(* non-VType -> VType is explicitly rejected by the algorithm *)
Eval compute in (fuel_vcumul 5 (TV vnat) (TV vt0)).
(* = Some false    -- VNat -> VType disallowed by design *)

(* identical VNat values *)
Eval compute in (fuel_vcumul 5 (TV vnat) (TV vnat)).
(* = Some true *)

(* VZero vs VZero *)
Eval compute in (fuel_vcumul 5 (TV vzero) (TV vzero)).
(* = Some true *)

(* VSucc structural comparison (recursive) *)
Eval compute in (fuel_vcumul 5 (TV vsucc1) (TV vsucc1)).
(* = Some true *)
Eval compute in (fuel_vcumul 5 (TV vsucc1) (TV vsucc2)).
(* = Some false *)

(* Out-of-fuel example: tiny fuel for a VSucc comparison that needs recursion *)
Eval compute in (fuel_vcumul 0 (TV vsucc1) (TV vsucc1)).
(* = None *)

(* ---------------------------
   Neutral cases
   --------------------------- *)

(* NVar equality *)
Eval compute in (fuel_vcumul 5 (TNe nvar0) (TNe nvar0)).
(* = Some true *)

Eval compute in (fuel_vcumul 5 (TNe nvar0) (TNe nvar1)).
(* = Some false *)

(* NApp: NApp n v : compare n and v structurally *)
Eval compute in (fuel_vcumul 6 (TNe (NApp nvar0 vnat)) (TNe (NApp nvar0 vnat))).
(* = Some true *)

Eval compute in (fuel_vcumul 6 (TNe (NApp nvar0 vnat)) (TNe (NApp nvar0 vzero))).
(* = Some false *)

(* NNatRec / NVecRec follow the same recursive pattern (need enough fuel) *)

(* ---------------------------
   Vec & Cons cases
   --------------------------- *)

Eval compute in (fuel_vcumul 6 (TV vvec_nat_1) (TV vvec_nat_1)).
(* = Some true *)

Eval compute in (fuel_vcumul 6 (TV vvec_nat_1) (TV vvec_nat_2)).
(* = Some false *)

Eval compute in (fuel_vcumul 6 (TV vnil_nat) (TV vnil_nat)).
(* = Some true *)

Eval compute in (fuel_vcumul 10 (TV vcons_nat_1) (TV vcons_nat_1)).
(* = Some true *)

(* ---------------------------
   Closure corner cases
   --------------------------- *)

(* 1) identical closures (same body, same env) -> should be true *)
Eval compute in (fuel_vcumul 10 (TC cl_oneenv_var0) (TC cl_oneenv_var0)).
(* = Some true
   Explanation: term_eqb sees Var 0 = Var 0 and envlist compares [VNat] vs [VNat] giving Some true.
   fuel must be large enough to traverse the envlist. *)

(* 2) closures with same body but envs differ in length -> false *)
Eval compute in (fuel_vcumul 10 (TC cl_empty_var0) (TC cl_oneenv_var0)).
(* = Some false
   Explanation: lengths 0 vs 1 differ; we immediately return false. *)

(* 3) closures with different bodies -> false even if envs equal *)
Eval compute in (fuel_vcumul 10 (TC cl_empty_var0) (TC cl_empty_var1)).
(* = Some false
   Explanation: term_eqb (Var 0) (Var 1) = false. *)

(* 4) closures with equal bodies and pairwise-convertible environments:
      Example: two closures both with body Var 0 and envs [VNat] vs [VNat] *)
Eval compute in (fuel_vcumul 6 (TC cl_oneenv_var0) (TC cl_oneenv_var0)).
(* = Some true *)

(* 5) closure vs non-closure tags: always false (no mixing) *)
Eval compute in (fuel_vcumul 6 (TC cl_empty_var0) (TV vt0)).
(* = Some false *)

(* 6) out-of-fuel for closure env traversal:
   try very small fuel that can't even check the env element *)
Eval compute in (fuel_vcumul 1 (TC cl_oneenv_var0) (TC cl_oneenv_var0)).
(* = None
   Explanation: fuel=1 may be consumed by the top-level match; envlist recursion needs additional fuel. *)

(* ---------------------------
   Combined tricky case: neutral closure-like shape
   --------------------------- *)

(* build neutral that wraps NatRec or VecRec and check conversion *)
Definition nneut_natrec1 := NNatRec vnat vzero (VLam VNat (Cl [] (Var 0))) (NVar 0).
Definition nneut_natrec2 := NNatRec vnat vzero (VLam VNat (Cl [] (Var 0))) (NVar 0).

Eval compute in (fuel_vcumul 12 (TNe nneut_natrec1) (TNe nneut_natrec2)).


(* ---------------------------
   fuel_whnf_eqb and friends (strict structural equality, fuel-bounded)
   --------------------------- *)

Fixpoint fuel_whnf_eqb (fuel : nat) (v1 v2 : whnf) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match v1, v2 with
    | VType i1, VType i2 => Some (Nat.eqb i1 i2)
    | VNat, VNat => Some true
    | VZero, VZero => Some true
    | VSucc n1, VSucc n2 => fuel_whnf_eqb fuel' n1 n2
    | VNeutral n1, VNeutral n2 => fuel_neutral_eqb fuel' n1 n2
    | VVec a1 n1, VVec a2 n2 =>
        match fuel_whnf_eqb fuel' a1 a2 with
        | None => None | Some false => Some false | Some true => fuel_whnf_eqb fuel' n1 n2
        end
    | VNil a1, VNil a2 => fuel_whnf_eqb fuel' a1 a2
    | VCons a1 n1 x1 xs1, VCons a2 n2 x2 xs2 =>
        match fuel_whnf_eqb fuel' a1 a2 with
        | None => None | Some false => Some false
        | Some true =>
            match fuel_whnf_eqb fuel' n1 n2 with
            | None => None | Some false => Some false
            | Some true =>
                match fuel_whnf_eqb fuel' x1 x2 with
                | None => None | Some false => Some false
                | Some true => fuel_whnf_eqb fuel' xs1 xs2
                end
            end
        end
    | VLam a1 cl1, VLam a2 cl2 =>
        match fuel_whnf_eqb fuel' a1 a2 with
        | None => None | Some false => Some false | Some true => fuel_closure_eqb fuel' cl1 cl2
        end
    | VPi a1 cl1, VPi a2 cl2 =>
        match fuel_whnf_eqb fuel' a1 a2 with
        | None => None | Some false => Some false | Some true => fuel_closure_eqb fuel' cl1 cl2
        end
    | _, _ => Some false
    end
  end

with fuel_neutral_eqb (fuel : nat) (n1 n2 : neutral) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match n1, n2 with
    | NVar i1, NVar i2 => Some (Nat.eqb i1 i2)
    | NApp n1' v1, NApp n2' v2 =>
        match fuel_neutral_eqb fuel' n1' n2' with
        | None => None | Some false => Some false | Some true => fuel_whnf_eqb fuel' v1 v2
        end
    | NNatRec P1 z1 s1 n1', NNatRec P2 z2 s2 n2' =>
        match fuel_whnf_eqb fuel' P1 P2 with
        | None => None | Some false => Some false
        | Some true =>
            match fuel_whnf_eqb fuel' z1 z2 with
            | None => None | Some false => Some false
            | Some true =>
                match fuel_whnf_eqb fuel' s1 s2 with
                | None => None | Some false => Some false
                | Some true => fuel_neutral_eqb fuel' n1' n2'
                end
            end
        end
    | NVecRec P1 nl1 c1 idx1 n1', NVecRec P2 nl2 c2 idx2 n2' =>
        match fuel_whnf_eqb fuel' P1 P2 with
        | None => None | Some false => Some false
        | Some true =>
            match fuel_whnf_eqb fuel' nl1 nl2 with
            | None => None | Some false => Some false
            | Some true =>
                match fuel_whnf_eqb fuel' c1 c2 with
                | None => None | Some false => Some false
                | Some true =>
                    match fuel_whnf_eqb fuel' idx1 idx2 with
                    | None => None | Some false => Some false
                    | Some true => fuel_neutral_eqb fuel' n1' n2'
                    end
                end
            end
        end
    | _, _ => Some false
    end
  end

with fuel_closure_eqb (fuel : nat) (cl1 cl2 : closure) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match cl1, cl2 with
    | Cl ρ1 t1, Cl ρ2 t2 =>
        if term_eqb t1 t2 then fuel_env_eqb fuel' ρ1 ρ2 else Some false
    end
  end

with fuel_env_eqb (fuel : nat) (ρ1 ρ2 : list whnf) {struct fuel} : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match ρ1, ρ2 with
    | [], [] => Some true
    | v1::r1, v2::r2 =>
        match fuel_whnf_eqb fuel' v1 v2 with
        | None => None | Some false => Some false | Some true => fuel_env_eqb fuel' r1 r2
        end
    | _, _ => Some false
    end
  end.

(* (* ---------------------------
   fuel_synth / fuel_check (with strict Lam annotation check)
   --------------------------- *)

Definition fuel_vcumul_whnf (fuel : nat) (v1 v2 : whnf) : option bool :=
  fuel_vcumul fuel (TV v1) (TV v2).

Definition fuel_as_vpi (fuel : nat) (v : whnf) : option (whnf * closure) :=
  match v with
  | VPi vA cl => Some (vA, cl)
  | _ => None
  end.

Fixpoint fuel_value_is_type_bool (fuel : nat) (v : whnf) {struct fuel} : option nat :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match v with
    | VType i => Some i
    | VNat => Some 0
    | VVec a _ => fuel_value_is_type_bool fuel' a
    | VNil a => fuel_value_is_type_bool fuel' a
    | VCons a _ _ _ => fuel_value_is_type_bool fuel' a
    | _ => None
    end
  end.

Fixpoint fuel_synth (fuel : nat) (Γ : ctx) (t : term) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match t with
    | Var x =>
        match nth_error Γ x with
        | Some A => Some A
        | None => Some (VNeutral (NVar (x - length Γ)))
        end

    | Type__ i => Some (VType i)
    | Nat => Some VNat

    | Pi A B =>
        match evalk fuel Γ A with
        | None => None
        | Some vA => Some (VPi vA (Cl Γ B))
        end

    | Lam annA b =>
        match fuel_synth fuel' Γ annA with
        | None => None
        | Some vdom => Some (VPi vdom (Cl Γ b))
        end

    | App t1 t2 =>
        match fuel_synth fuel' Γ t1 with
        | None => None
        | Some vt =>
            match evalk fuel Γ t2 with
            | None => None
            | Some vu =>
                match fuel_as_vpi fuel vt with
                | None => None
                | Some (_vdom, clB) =>
                    let ρB := env_of_cl clB in
                    let Bterm := body_of_cl clB in
                    evalk fuel (vu :: ρB) Bterm
                end
            end
        end

    | Zero => Some VZero

    | Succ n =>
        match fuel_check fuel' Γ n VNat with
        | None => None
        | Some _ => Some VNat
        end

    | NatRec P z s n =>
        match evalk fuel Γ P, evalk fuel Γ z, evalk fuel Γ s, evalk fuel Γ n with
        | Some vP, Some vz, Some vs, Some vn => fuel_natrec fuel vP vz vs vn
        | _, _, _, _ => None
        end

    | Vec A n =>
        match evalk fuel Γ A, evalk fuel Γ n with
        | Some vA, Some vn =>
            match fuel_value_is_type_bool fuel vA, fuel_vcumul_whnf fuel vn VNat with
            | Some _, Some true => Some (VVec vA vn)
            | _, _ => None
            end
        | _, _ => None
        end

    | Nil A =>
        match evalk fuel Γ A with
        | Some vA =>
            match fuel_value_is_type_bool fuel vA with
            | Some _ => Some (VVec vA VZero)
            | None => None
            end
        | None => None
        end

    | Cons A n x xs =>
        match evalk fuel Γ A, evalk fuel Γ n, evalk fuel Γ x, evalk fuel Γ xs with
        | Some vA, Some vn, Some vx, Some vxs =>
            match fuel_value_is_type_bool fuel vA, fuel_vcumul_whnf fuel vn VNat with
            | Some _, Some true =>
                match fuel_check fuel' Γ x vA with
                | None => None
                | Some _ =>
                    match fuel_check fuel' Γ xs (VVec vA vn) with
                    | None => None
                    | Some _ => Some (VVec vA (VSucc vn))
                    end
                end
            | _, _ => None
            end
        | _, _, _, _ => None
        end

    | VecRec P nl cns n t =>
        match evalk fuel Γ P, evalk fuel Γ nl, evalk fuel Γ cns, evalk fuel Γ n, evalk fuel Γ t with
        | Some vP, Some vnil, Some vcons, Some vn, Some vt => fuel_vecrec fuel vP vnil vcons vn vt
        | _, _, _, _, _ => None
        end
    end
  end

with fuel_check (fuel : nat) (Γ : ctx) (t : term) (A : whnf) {struct fuel} : option unit :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match t with
    | Zero =>
        match A with VNat => Some tt | _ => None end

    | Succ n =>
        match fuel_check fuel' Γ n VNat with
        | None => None
        | Some _ => match A with VNat => Some tt | _ => None end
        end

    | Lam annA b =>
        (* 1) synth the annotation (vann)
           2) expect A to be a VPi vdom clB
           3) require strict equality vann == vdom (fuel_whnf_eqb)
           4) evaluate the codomain closure Cl to a value vB with evalk using full fuel
           5) recursively check the body under (vdom :: Γ) against vB
        *)
        match fuel_synth fuel' Γ annA with
        | None => None
        | Some vann =>
            match fuel_as_vpi fuel A with
            | None => None
            | Some (vdom, clB) =>
                match fuel_whnf_eqb fuel vann vdom with
                | None => None
                | Some false => None
                | Some true =>
                    let ρB := env_of_cl clB in
                    let Bterm := body_of_cl clB in
                    match evalk fuel (vdom :: ρB) Bterm with
                    | None => None
                    | Some vB => fuel_check fuel' (vdom :: Γ) b vB
                    end
                end
            end
        end

    | NatRec P z s n as trm =>
        match fuel_synth fuel' Γ trm with
        | None => None
        | Some A' =>
            match fuel_vcumul_whnf fuel A' A with
            | Some true => Some tt
            | _ => None
            end
        end

    | VecRec P nl cns n t as trm =>
        match fuel_synth fuel' Γ trm with
        | None => None
        | Some A' =>
            match fuel_vcumul_whnf fuel A' A with
            | Some true => Some tt
            | _ => None
            end
        end

    | _ =>
        (* fallback: synth + strict equality (we keep strict equality for other cases) *)
        match fuel_synth fuel' Γ t with
        | None => None
        | Some A' =>
            match fuel_whnf_eqb fuel A' A with
            | None => None
            | Some true => Some tt
            | Some false => None
            end
        end
    end
  end.




(* convenience wrappers using default_fuel *)
Definition check_fuel := fuel_check.
Definition synth_fuel := fuel_synth.





(* ------------------------------------------------------------------ *)
(* Quick examples (use the same helper definitions you had earlier)   *)
(* ------------------------------------------------------------------ *)

(* Use the same small values used earlier: vt0 vt1 vnat etc. *)

(* Example 1: synthesize Nat *)
Example ex1_synth_nat :
  fuel_synth 5 [] Nat = (Some VNat).
Proof. reflexivity. Qed.

(* Example 2: synthesize variable from context *)
Example ex2_synth_var :
  fuel_synth 5 [VNat; VType 0] (Var 0) = (Some VNat).
Proof. reflexivity. Qed.

(* Example 3: check Succ 0 against Nat *)
Example ex3_check_succ :
  fuel_check 8 [] (Succ Zero) VNat = Some tt.
Proof. simpl. reflexivity. Qed.

(* Example 4: lam annotated: Lam annA b synthesizes to a Pi when annA synthesizes *)
Example ex4_synth_lam :
  (* \x : Nat. x  with annotation Nat *)
  fuel_synth 10 [] (Lam Nat (Var 0)) = (Some (VPi VNat (Cl [] (Var 0)))).
Proof. reflexivity. Qed.

(* wrappers with the names you used earlier *)
Definition infer_fuel := fun (fuel : nat) (Γ : ctx) (t : term) => fuel_synth fuel Γ t.

(* --- your example Compute lines adapted --- *)

(* Please make sure that `add`, `mult`, `tm_vec_motive`, `tm_append_v12_v3`, etc.
   are actual `term` definitions present in your file; otherwise Coq will complain
   that those identifiers are unbound. *)

Compute infer_fuel 1000 [] add_term.

Compute (fuel_synth 2000 [] add_term).
Compute (fuel_synth 2000 [] mult_term).

Compute (fuel_synth 100 [] add_term).
Compute (fuel_synth 100 [] (Pi Nat (Pi Nat Nat))).   (* sanity: can we synth a simple Pi? *)
Compute (evalk 100 [] (App (App add_term two) one)).  (* does evalk itself succeed for add_term application? *)


Compute check_fuel 1000 [] add_term  (VPi VNat (Cl [] (Pi Nat Nat))).
Compute check_fuel 8    [] mult_term (VPi VNat (Cl [] (Pi Nat (Type__ 0)))).

Definition xs1 := VCons VNat VZero (VSucc VZero) (VNil VNat).  (* [1] *)
Definition ys1' := VCons VNat VZero VZero (VNil VNat).        (* [0] *)

Compute check_fuel 1000 []
  (tm_vec_motive Nat (Succ Zero))
  (VPi VNat (Cl [] (VPi (Vec (Var 0) Nat) (VType 0)))).
  (* I replaced `Star` by `VType 0` because your WHNF uses VType for universes.
     If you actually have a `Star` constructor in your development, swap back. *)

Compute infer_fuel 100 [] ys1'.
Compute infer_fuel 100 [] tm_append_v12_v3.

Compute check_fuel 1000 []
  tm_append_v12_v3
  (VVec (VSucc (VSucc (VSucc VZero))) VNat).

 *)




