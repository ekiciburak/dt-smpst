From Coq Require Import List Arith Lia.
Import ListNotations.
From Paco Require Import paco.

(* ================================================== *)
(* 1) Syntax: smaller language (dependent + NatRec)   *)
(* ================================================== *)

Inductive term : Type :=
  | Star : term
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
| VStar  : whnf
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
| Cl : list whnf -> term -> closure.

Coercion VNeutral : neutral >-> whnf.

Section ManualMutualInduction_Prop.

  Variable Pw : whnf -> Prop.
  Variable Pn : neutral -> Prop.
  Variable Pc : closure -> Prop.

  (* Hypotheses for each constructor (one hypothesis per constructor) *)
  Hypotheses
    (H_VStar    : Pw VStar)
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
    | VStar            => H_VStar
    | VNat             => H_VNat
    | VPi A B          => H_VPi A B (whnf_proof A) (closure_proof B)
    | VLam A cl        => H_VLam A cl (whnf_proof A) (closure_proof cl)
    | VZero            => H_VZero
    | VSucc n          => H_VSucc n (whnf_proof n)
    | VNeutral n       => H_VNeutral n (neutral_proof n)
    | VVec vA vn       => H_VVec vA vn (whnf_proof vA) (whnf_proof vn)
    | VNil vA          => H_VNil vA (whnf_proof vA)
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
(*  Runtime application and evaluation (no dependency on vconv/closure_conv) *)
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

| EVR_Cons : forall vP vnil vcons vindex vA vn vx vxs vrec v1 v2 v,
    eval_vecrec vP vnil vcons vindex vxs vrec ->
    vapp vcons vx v1 ->
    vapp v1 vxs v2 ->
    vapp v2 vrec v ->
    eval_vecrec vP vnil vcons vindex (VCons vA vn vx vxs) v

| EVR_Neut : forall vP vnil vcons vindex nn,
    eval_vecrec vP vnil vcons vindex (VNeutral nn) (VNeutral (NVecRec vP vnil vcons vindex nn))

(* ----------------------------------------------------------------- *)
(*  eval' : big-step evaluator to WHNF (no use of closure_conv/vconv) *)
(* ----------------------------------------------------------------- *)
with eval' : list whnf -> term -> whnf -> Prop :=
| E'_Star : forall ρ, eval' ρ Star VStar
| E'_Nat : forall ρ, eval' ρ Nat VNat

| E'_Var_Some : forall ρ x v,
    nth_error ρ x = Some v ->
    eval' ρ (Var x) v

| E'_Var_None : forall ρ x,
    nth_error ρ x = None ->
    eval' ρ (Var x) (VNeutral (NVar (x - length ρ)))

| E'_Pi : forall ρ A B vA,
    eval' ρ A vA ->
    eval' ρ (Pi A B) (VPi vA (Cl ρ B))

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
   inversion H3. subst.
   apply H in H12.
   apply H0 in H14.
   subst.
   apply H1 in H15.
   subst.
   apply H2 in H16.
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

Inductive conv_tag : Type :=
| TNe : neutral -> conv_tag
| TV  : whnf -> conv_tag
| TC  : closure -> conv_tag.

Definition env_of_cl (cl : closure) : list whnf :=
  match cl with Cl rho _ => rho end.

Definition body_of_cl (cl : closure) : term :=
  match cl with Cl _ t => t end.

(* ------------------------------------------------------------------ *)
(* The functor F: (conv_tag -> conv_tag -> Prop) -> conv_tag -> conv_tag -> Prop
   It describes one unfolding step of the mutually coinductive relations.
   We write it so recursive occurrences refer to "r x y".               *)
(* ------------------------------------------------------------------ *)

Definition convF
  (r : conv_tag -> conv_tag -> Prop)
  (x y : conv_tag) : Prop :=

  match x, y with

  (* neutral cases *)
  | TNe (NVar i), TNe (NVar j) =>
      (* only equal when same var index *)
      i = j

  | TNe (NApp n1 v1), TNe (NApp n2 v2) =>
      (* n1 ~ n2 as neutrals, and v1 ~ v2 as values (use r on TV) *)
      r (TNe n1) (TNe n2) /\ r (TV v1) (TV v2)

  | TNe (NNatRec P1 z1 s1 n1), TNe (NNatRec P2 z2 s2 n2) =>
      r (TV P1) (TV P2) /\ r (TV z1) (TV z2) /\ r (TV s1) (TV s2) /\ r (TNe n1) (TNe n2)

  | TNe (NVecRec P1 nil1 cons1 idx1 n1), TNe (NVecRec P2 nil2 cons2 idx2 n2) =>
      r (TV P1) (TV P2) /\ r (TV nil1) (TV nil2) /\ r (TV cons1) (TV cons2) /\ r (TV idx1) (TV idx2) /\ r (TNe n1) (TNe n2)

  (* value cases *)
  | TV VStar, TV VStar => True
  | TV VNat,  TV VNat  => True
  | TV VZero, TV VZero => True

(*   (* make Nat and Star convertible (Nat : Star) *)
  | TV VNat, TV VStar => True
  | TV VStar, TV VNat => True *)

  | TV (VSucc n1), TV (VSucc n2) =>
      r (TV n1) (TV n2)

  | TV (VNeutral n1), TV (VNeutral n2) =>
      r (TNe n1) (TNe n2)

  | TV (VVec a1 n1), TV (VVec a2 n2) =>
      r (TV a1) (TV a2) /\ r (TV n1) (TV n2)

  | TV (VNil a1), TV (VNil a2) =>
      r (TV a1) (TV a2)

  | TV (VCons a1 n1 x1 xs1), TV (VCons a2 n2 x2 xs2) =>
      r (TV a1) (TV a2) /\ r (TV n1) (TV n2) /\ r (TV x1) (TV x2) /\ r (TV xs1) (TV xs2)

  (* Lam-Lam and Pi-Pi via closure_conv (use r on TC) *)
  | TV (VLam vA1 cl1), TV (VLam vA2 cl2) =>
      r (TV vA1) (TV vA2) /\ r (TC cl1) (TC cl2)

  | TV (VPi vA1 cl1), TV (VPi vA2 cl2) =>
      r (TV vA1) (TV vA2) /\ r (TC cl1) (TC cl2)

  (* Eta/extensionality: relate Lam and Pi by observing evaluations of bodies.
     We encode the observational clause operationally: for all args, whenever
     both bodies evaluate in their respective extended envs to r1,r2, those results
     must be related by r (as TV). *)
(*   | TV (VLam vA1 cl1), TV (VPi vA2 cl2) =>
      r (TV vA1) (TV vA2) /\
      (forall (arg : whnf) (r1 r2 : whnf),
         eval' (arg :: env_of_cl cl1) (body_of_cl cl1) r1 ->
         eval' (arg :: env_of_cl cl2) (body_of_cl cl2) r2 ->
         r (TV r1) (TV r2))

  | TV (VPi vA1 cl1), TV (VLam vA2 cl2) =>
      r (TV vA1) (TV vA2) /\
      (forall (arg : whnf) (r1 r2 : whnf),
         eval' (arg :: env_of_cl cl1) (body_of_cl cl1) r1 ->
         eval' (arg :: env_of_cl cl2) (body_of_cl cl2) r2 ->
         r (TV r1) (TV r2)) *)

  (* closure case *)
  | TC (Cl ρ1 t1), TC (Cl ρ2 t2) =>
      Forall2 (fun x y => r (TV x) (TV y)) ρ1 ρ2 /\
      (forall (arg : whnf) (r1 : whnf),
         eval' (arg :: ρ1) t1 r1 ->
         exists r2, eval' (arg :: ρ2) t2 r2 /\ r (TV r1) (TV r2)) /\
      (forall (arg : whnf) (r2 : whnf),
         eval' (arg :: ρ2) t2 r2 ->
         exists r1, eval' (arg :: ρ1) t1 r1 /\ r (TV r1) (TV r2))

  (* other combinations are false (different shapes cannot be related by one step) *)
  | _, _ => False
  end.

Definition conv := paco2 convF bot2.

Lemma conv_refl: forall v, conv v v.
Proof. pcofix CIH.
       intro v.
       induction v; intros.
       - pfold. simpl. destruct n.
         + easy.
         + split. right. apply CIH.
           right. apply CIH.
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
  (forall v1 v2 : conv_tag, conv v1 v2 -> r v2 v1) -> 
  Forall2 (fun x y : whnf => upaco2 convF bot2 (TV x) (TV y)) l s ->
  Forall2 (fun x y : whnf => upaco2 convF r (TV x) (TV y)) s l.
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
  (forall v1 v2 v3: conv_tag, conv v1 v2 -> conv v2 v3 -> r v1 v3) -> 
  Forall2 (fun x y : whnf => upaco2 convF bot2 (TV x) (TV y)) l s ->
  Forall2 (fun x y : whnf => upaco2 convF bot2 (TV x) (TV y)) s u ->
  Forall2 (fun x y : whnf => upaco2 convF r (TV x) (TV y)) l u.
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

Lemma mon_convF: monotone2 convF.
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

Lemma conv_sym: forall v1 v2, conv v1 v2 -> conv v2 v1.
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
       - subst. punfold H0. simpl in H0.
         destruct c, c0.
         destruct H0 as (Ha,(Hb,Hc)).
         pfold. simpl. split.
         apply Forall2_conv_sym; easy.
         split.
         intros.
         apply Hc in H.
         destruct H as (res,H).
         exists res. split. easy.
         right.
         apply CIH. 
         destruct H as (Hn,Hm).
         destruct Hm as [Hm |Hm]. easy. easy.
         intros.
         apply Hb in H.
         destruct H as (res,H).
         exists res. split. easy.
         right.
         apply CIH. 
         destruct H as (Hn,Hm).
         destruct Hm as [Hm |Hm]. easy. easy.
         apply mon_convF.
       }
       - case_eq v2; intros.
         + subst. punfold H0. pfold.
           simpl in *.
           destruct n.
           ++ destruct n0. easy.
              easy.
              easy.
              easy.
           ++ destruct n0; try easy.
              destruct H0 as (Ha,Hb).
              split.
              * unfold upaco2 in Ha.
                destruct Ha as [Ha | Ha].
                ** right. apply CIH. easy.
                ** easy.
              * destruct Hb as [Hb | Hb].
                ** right. apply CIH. easy.
                ** easy.
           ++ destruct n0; try easy.
              destruct H0 as (Ha,(Hb,(Hc,Hd))).
              split.
              right. apply CIH.
              destruct Ha; easy.
              split.
              right. apply CIH.
              destruct Hb; easy.
              split.
              right. apply CIH.
              destruct Hc; easy.
              right. apply CIH.
              destruct Hd; easy.
           ++ destruct n0; try easy.
              destruct H0 as (Ha,(Hb,(Hc,(Hd,He)))).
              split.
              right. apply CIH.
              destruct Ha; easy.
              split.
              right. apply CIH.
              destruct Hb; easy.
              split.
              right. apply CIH.
              destruct Hc; easy.
              split.
              right. apply CIH.
              destruct Hd; easy.
              right. apply CIH.
              destruct He; easy.
            ++ apply mon_convF.
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
           punfold H0. simpl in H0. pfold. simpl.
           destruct w, w0; try easy.
           ++ destruct H0 as (Ha,Hb).
              split.
              right. apply CIH.
              destruct Ha; easy.
              right. apply CIH.
              destruct Hb; easy.
           ++ destruct H0 as (Ha,Hb).
              split.
              right. apply CIH.
              destruct Ha; easy.
              right. apply CIH.
              destruct Hb; easy.
           ++ right. apply CIH.
              destruct H0; easy.
           ++ right. apply CIH.
              destruct H0; easy.
           ++ destruct H0 as (Ha,Hb).
              split.
              right. apply CIH.
              destruct Ha; easy.
              right. apply CIH.
              destruct Hb; easy.
           ++ right. apply CIH.
              destruct H0; easy.
           ++ destruct H0 as (Ha,(Hb,(Hc,Hd))).
              split.
              right. apply CIH.
              destruct Ha; easy.
              split.
              right. apply CIH.
              destruct Hb; easy.
              split.
              right. apply CIH.
              destruct Hc; easy.
              right. apply CIH.
              destruct Hd; easy.
           ++ apply mon_convF.
         + subst.
           punfold H0. simpl in H0. destruct w; easy.
           apply mon_convF.
Qed.

Lemma conv_trans: forall v1 v2 v3, conv v1 v2 -> conv v2 v3 -> conv v1 v3.
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
                destruct w, w0, w1; try easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TC c0)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TC c0)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * right. apply CIH with (v2 := (TV w0)).
                  destruct H0; easy.
                  destruct H1; easy.
                * right. apply CIH with (v2 := (TNe n0)).
                  destruct H0; easy.
                  destruct H1; easy.
                * destruct H1 as (Ha,Hb).
                  destruct H0 as (Hc,Hd).
                  split.
                  right. apply CIH with (v2 := (TV w0_1)).
                  destruct Hc; easy.
                  destruct Ha; easy.
                  right. apply CIH with (v2 := (TV w0_2)).
                  destruct Hd; easy.
                  destruct Hb; easy.
                * right. apply CIH with (v2 := (TV w0)).
                  destruct H0; easy.
                  destruct H1; easy.
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

Definition neutral_conv (n1 n2 : neutral) : Prop := conv (TNe n1) (TNe n2).
Definition vconv (v1 v2 : whnf) : Prop := conv (TV v1) (TV v2).
Definition closure_conv (c1 c2 : closure) : Prop := conv (TC c1) (TC c2).


Section BidirectionalTyping.

(* Context: list of whnf (value-types) *)
Definition ctx := list whnf.

(* Helper: lookup in ctx *)
Definition ctx_lookup (Γ : ctx) (n : nat) : option whnf := nth_error Γ n.


Reserved Notation "Γ ⊢ₛ t ⇑ A" (at level 70).
Reserved Notation "Γ ⊢𝚌 t ⇓ A" (at level 70).

(* syntactic shape predicate for type-level terms (useful in progress hypotheses) *)
Inductive is_type_shape : term -> Prop :=
| ITS_Star : is_type_shape Star
| ITS_Nat  : is_type_shape Nat
| ITS_Var  : forall x, is_type_shape (Var x)
| ITS_App : forall t u, is_type_shape t -> is_type_shape (App t u)
| ITS_Pi   : forall A B, is_type_shape A -> is_type_shape B -> is_type_shape (Pi A B)
| ITS_Vec  : forall A n, is_type_shape A -> is_type_shape (Vec A n)
| ITS_NatRec : forall P z s n, is_type_shape P -> is_type_shape (NatRec P z s n)
| ITS_VecRec : forall P nil cons n t, is_type_shape P -> is_type_shape (VecRec P nil cons n t).

(* ---------------------------
   Bidirectional typing
   --------------------------- *)

Fixpoint make_neutral_env_from (start : nat) (Γ : list whnf) : list whnf :=
  match Γ with
  | [] => []
  | _ :: Γ' => VNeutral (NVar start) :: make_neutral_env_from (S start) Γ'
  end.

Definition make_neutral_env (Γ : list whnf) : list whnf :=
  make_neutral_env_from 0 Γ.


Inductive synth : ctx -> term -> whnf -> Prop :=
  (* variables: types are stored as whnf in the context *)
| S_Var : forall Γ x A,
    nth_error Γ x = Some A ->
    synth Γ (Var x) A

  (* universes / base types *)
| S_Star : forall Γ,
    synth Γ Star VStar

| S_Nat : forall Γ,
    synth Γ Nat VNat

  (* Pi formation: domain must evaluate to a type, and codomain must check as a type
     under the extended static context (vdom :: Γ).  The produced WHNF is the Pi
     whose closure captures the *syntactic* codomain term in context Γ. *)
| S_Pi : forall Γ A B vA,
    eval' Γ A vA ->                (* evaluate domain annotation *)
    vconv vA VStar ->               (* domain is a type *)
    check (vA :: Γ) B VStar ->      (* codomain is a type under the extended static context *)
    synth Γ (Pi A B) (VPi vA (Cl Γ B))

  (* Application: synthesize t to something convertible to VPi vdom clB,
     evaluate u to vu, and evaluate the body under the closure to get result type *)
| S_App : forall Γ t u vt vu vdom clB ρB Bterm vres,
    synth Γ t vt ->
    eval' Γ u vu ->
    vconv vt (VPi vdom clB) ->
    clB = Cl ρB Bterm ->
    eval' (vu :: ρB) Bterm vres ->
    synth Γ (App t u) vres

  (* Zero & Succ *)
| S_Zero : forall Γ, synth Γ Zero VNat

| S_Succ : forall Γ n,
    check Γ n VNat ->
    synth Γ (Succ n) VNat

  (* NatRec (term-level eliminator): result is whatever eval_natrec returns *)
| S_NatRec_term : forall Γ P z s n vP vz vs vn v,
    eval' Γ P vP ->
    eval' Γ z vz ->
    eval' Γ s vs ->
    eval' Γ n vn ->
    eval_natrec vP vz vs vn v ->
    synth Γ (NatRec P z s n) v

  (* Vec formation: components must be types (A : VStar) and index a Nat *)
| S_Vec : forall Γ A n vA vn,
    eval' Γ A vA ->
    vconv vA VStar ->
    eval' Γ n vn ->
    vconv vn VNat ->
    synth Γ (Vec A n) (VVec vA vn)

  (* Nil / Cons synthesize the *type* of the vector, not the value *)
| S_Nil : forall Γ A vA,
    eval' Γ A vA ->
    vconv vA VStar ->
    synth Γ (Nil A) (VVec vA VZero)

| S_Cons : forall Γ A n x xs vA vn,
    eval' Γ A vA ->
    vconv vA VStar ->
    eval' Γ n vn ->
    vconv vn VNat ->
    check Γ x vA ->                       (* x : A *)
    check Γ xs (VVec vA vn) ->            (* xs : Vec A n *)
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

| S_Lam_Ann : forall Γ annA b vdom vB,
    synth Γ annA vdom ->
    vconv vdom VStar ->
    check (vdom :: Γ) b vB ->
    synth Γ (Lam annA b) (VPi vdom (Cl Γ b))

  (* Annotated lambda (synthesizes a Pi based on annotation). We require the annotation
(*      to synthesize to a type (vdom) and that the lambda body checks under the extended
     static context (vdom :: Γ) to some vB; the produced Pi closure captures the
     body-as-term with Γ. *)
| S_Lam_Ann : forall Γ annA b vdom vB,
    synth Γ annA vdom ->
    vconv vdom VStar ->
    check (vdom :: Γ) b vB ->
    synth Γ (Lam annA b) (VPi vdom (Cl Γ b)) *)

where "Γ ⊢ₛ t ⇑ A" := (synth Γ t A)

with check : ctx -> term -> whnf -> Prop :=
(* checking by synth + convert *)
| C_Synth : forall Γ t A' A,
    synth Γ t A' ->
    vconv A' A ->
    check Γ t A

| C_Lam : forall Γ (A : whnf) annA b vdom clB ρB Bterm vB,
    synth Γ annA vdom ->                 (* annotation synthesizes the domain *)
    vconv vdom VStar ->                  (* annotation must be a type *)
    vconv A (VPi vdom clB) ->            (* expected type convertible to Pi vdom clB *)
    clB = Cl ρB Bterm ->
    eval' (vdom :: ρB) Bterm vB ->       (* evaluate codomain under clB's runtime env *)
    check (vdom :: Γ) b vB ->            (* check the lambda body in its own static env *)
    closure_conv (Cl Γ b) clB ->
    check Γ (Lam annA b) A

(* (* check lambda against expected Pi: expected A convertible to Pi vdom clB,
   evaluate the expected codomain under clB's env to get vB, check the lambda body
   under its own static environment (vdom :: Γ) against that vB, then require
   the runtime closure produced by the lambda be observationally convertible to clB. *)
| C_Lam : forall Γ (A : whnf) annA b vdom clB ρB Bterm vB,
    synth Γ annA vdom ->                 (* annotation synthesizes the domain *)
    vconv vdom VStar ->                  (* annotation must be a type *)
    vconv A (VPi vdom clB) ->            (* expected type convertible to Pi vdom clB *)
    clB = Cl ρB Bterm ->
    eval' (vdom :: ρB) Bterm vB ->       (* evaluate codomain under clB's runtime env *)
    check (vdom :: Γ) b vB ->            (* check the lambda body in its own static env *)
    closure_conv (Cl Γ b) clB ->         (* closures must be observationally convertible *)
    check Γ (Lam annA b) A
 *)
(* NatRec checked against an expected A: evaluate elim components and require the
   evaluation of the elimination be convertible to A *)
| C_NatRec_check : forall Γ P z s n A vP vz vs vn v,
    eval' Γ P vP ->
    eval' Γ z vz ->
    eval' Γ s vs ->
    eval' Γ n vn ->
    eval_natrec vP vz vs vn v ->
    vconv v A ->
    check Γ (NatRec P z s n) A

(* VecRec checked against expected A *)
| C_VecRec_check : forall Γ P nil cons n A t vt vP vnil vcons vn vres,
    eval' Γ P vP ->
    eval' Γ nil vnil ->
    eval' Γ cons vcons ->
    eval' Γ n vn ->
    eval' Γ t vt ->
    eval_vecrec vP vnil vcons vn vt vres ->
    vconv vres A ->
    check Γ (VecRec P nil cons n t) A

where "Γ ⊢𝚌 t ⇓ A" := (check Γ t A).

Scheme synth_rect := Induction for synth Sort Prop
with check_rect := Induction for check Sort Prop.

Combined Scheme typing_mutind from synth_rect, check_rect.

(* Lemma typing_unique_mut :
  (forall Γ t A (He : synth Γ t A) A' (He' : synth Γ t A'), vconv A A')  /\
  (forall Γ t A (He : check Γ t A) A' (He' : synth Γ t A'), vconv A A').
Proof.
  eapply (typing_mutind
    (fun Γ t A (He : synth Γ t A) => forall A' (He' : synth Γ t A'), vconv A A')
    (fun Γ t A (He : check Γ t A) => forall A' (He' : synth Γ t A'), vconv A A')
  ).
  17:{
  intros.
  inversion He'. subst.
  assert(vres = A') by admit.
  subst.
  admit.
  }
Admitted. *)

Lemma synth_preserve_eval_for_types :
  (forall Γ t A (He : synth Γ t A),
    forall v, is_type_shape t -> eval' Γ t v -> vconv A v)
  /\
  (forall Γ t A (He : check Γ t A),
     forall v, is_type_shape t -> eval' Γ t v -> vconv A v).
Proof.
  eapply (typing_mutind
    (fun (Γ : ctx) (t : term) (A : whnf) (He : synth Γ t A) =>
       forall v, is_type_shape t -> eval' Γ t v -> vconv A v)
    (fun (Γ : ctx) (t : term) (A : whnf) (He : check Γ t A) =>
       forall v, is_type_shape t -> eval' Γ t v -> vconv A v)
  ).
  17:{
  intros.
  inversion H0. subst.
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
  subst.
  apply conv_sym. easy.
  }
  16:{
  intros.
  inversion H0. subst.
  assert(v = v1).
  { specialize(eval'_det  _ _ _ _ e H5); intro HHa.
    specialize(eval'_det  _ _ _ _ e0 H7); intro HHb.
    specialize(eval'_det  _ _ _ _ e1 H9); intro HHc.
    specialize(eval'_det  _ _ _ _ e2 H10); intro HHd.
    subst.
    specialize(eval_natrec_det _ _ _ _ _ _ e3 H11); intro HHf.
    easy.
  }
  subst.
  apply conv_sym. easy.
  }
  15:{
  intros.
  inversion H2. subst.
  inversion H1.
  }
  14:{
  intros.
  apply H with (v := v0) in H0.
  apply conv_sym in v.
  apply conv_trans with (v2 := (TV A')); easy.
  easy.
  }
  13:{
  intros.
  inversion H1.
  }
  12:{
  intros.
  inversion H0. subst.
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
  subst.
  apply conv_refl.
  }
  11:{
  intros. inversion H1.
  }
  10:{
  intros. inversion H.
  }
  9:{
  intros. inversion H0. subst.
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
  subst. 
  apply conv_refl.
  }
  8:{
  intros.
  inversion H0. subst.
  assert(v0 = v).
  { specialize(eval'_det  _ _ _ _ e H5); intro HHa.
    specialize(eval'_det  _ _ _ _ e0 H7); intro HHb.
    specialize(eval'_det  _ _ _ _ e1 H9); intro HHc.
    specialize(eval'_det  _ _ _ _ e2 H10); intro HHd.
    subst.
    specialize(eval_natrec_det _ _ _ _ _ _ e3 H11); intro HHf.
    easy.
  }
  subst.
  apply conv_refl.
  }
  7:{
  intros. inversion H0.
  }
  6:{
  intros. inversion H.
  }
  5:{
  intros.
  inversion H0. subst.
  inversion H1. subst.
  specialize(H vt0 H3 H5).
  assert(vconv vt0 (VPi vdom (Cl ρB Bterm))).
  { apply conv_sym in H.
    apply conv_trans with (v2 := (TV vt)); easy.
  }
  punfold H2. simpl in H2.
  destruct vt0; try easy.
  destruct H2 as (Ha,Hb).
  destruct Ha as [Ha | Ha].
  punfold H.
  simpl in H.
  destruct vt; try easy.
  destruct H as (Hc,Hd).
  inversion H9.
  subst.
  destruct Hb as [Hb | Hb].
  punfold Hb. simpl in Hb.
  destruct Hb as (Hb1,Hb2).
  assert(vu = vu0).
  { specialize(eval'_det  _ _ _ _ e H7); intro HHa.
    easy.
  }
  subst.
  destruct Hb2 as (Hb21,Hb22).
  apply Hb22 in e1.
  destruct e1 as (res1,(He1,He2)).
  apply Hb21 in H8.
  destruct H8 as (res2,(He3,He4)).
  inversion H9. subst.
  assert(v0 = res1).
  { specialize(eval'_det  _ _ _ _ He1 H10); intro HHa.
    easy.
  }
  subst.
  destruct He2 as [He2 | He2].
  apply conv_sym in He2.
  easy.
  easy.
  apply mon_convF.
  easy.
  apply mon_convF.
  easy.
  apply mon_convF.
 }
 4:{
 intros.
 inversion H0. subst.
 inversion H1. subst.
 assert(vA = vA0).
 { specialize(eval'_det  _ _ _ _ e H8); intro HHa.
   easy.
  }
 subst.
 pfold. simpl.
 split. left. apply conv_refl.
 left. apply conv_refl.
 }
 3:{
 intros.
 inversion H0. subst.
 apply conv_refl.
 }
 2:{
 intros.
 inversion H0. apply conv_refl.
 }
 1:{
 intros.
 inversion H0.
 + subst. rewrite e in H3. inversion H3. apply conv_refl.
 + subst. rewrite e in H3. easy.
 }
Qed.

Lemma synth_preserve_eval :
  forall Γ t A v,
    is_type_shape t ->
    eval' Γ t v ->
    synth Γ t A ->
    vconv A v.
Proof.
  intros Γ t A v Hclosed Heval Hs.
  eapply (proj1 synth_preserve_eval_for_types); eauto.
Qed.

Lemma check_preserve_eval :
  forall Γ t A v,
    is_type_shape t ->
    eval' Γ t v ->
    check Γ t A ->
    vconv A v.
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
  assert(vconv vta (VPi vt c)).
  { inversion H1. subst.
    specialize(synth_preserve_eval _ _ _ _ H2 Hvta s); intro HH.
    apply conv_sym. easy.
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
    assert(HCC: paco2 convF bot2 (TC (Cl [] B)) (TC (Cl [] Bterm))).
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
    assert(HCC: paco2 convF bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
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
     assert(HCC: paco2 convF bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
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
     assert(HCC: paco2 convF bot2 (TC (Cl l t)) (TC (Cl ρB Bterm))).
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
  2:{
  intros.
  subst.
  exists VStar.
  apply E'_Star.
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
  (forall t A, synth [] t A -> is_type_shape t -> exists v, eval' [] t v /\ vconv A v)
  /\
  (forall t A, check [] t A -> is_type_shape t -> exists v, eval' [] t v /\ vconv A v).
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
    exists v, eval' [] t v /\ vconv A v.
Proof.
  intros t A Heq Hclosed.
  eapply (proj1 type_safety_mut); eauto.
Qed.

Lemma check_type_safety :
  forall t A,
    check [] t A ->
    is_type_shape t ->
    exists v, eval' [] t v /\ vconv A v.
Proof.
  intros t A Heq Hclosed.
  eapply (proj2 type_safety_mut); eauto.
Qed.

Lemma closure_conv_bisim_exists :
  forall (ρ1 ρ2 : list whnf) (t1 t2 : term) (arg r2 : whnf),
    upaco2 convF bot2 (TC (Cl ρ1 t1)) (TC (Cl ρ2 t2)) ->
    eval' (arg :: ρ2) t2 r2 ->
    exists r1, eval' (arg :: ρ1) t1 r1 /\ upaco2 convF bot2 (TV r1) (TV r2).
Proof. intros.
       destruct H as [H | H].
       punfold H.
       simpl in H.
       destruct H as (Ha,(Hb,Hc)).
       apply Hc in H0.
       destruct H0 as (res1,(Hc1,Hc2)).
       exists res1. easy.
       apply mon_convF.
       easy.
Qed.

Definition add_term : term :=
  Lam Nat
    ( Lam Nat
        ( NatRec
            (Lam Nat Nat)                     (* P = λ_. Nat *)
            (Var 0)                           (* z = y *)
            (Lam Nat (Lam Nat (Succ (Var 0))))(* s = λn. λrec. Succ rec *)
            (Var 1)                           (* n = x *)
        )
    ).

