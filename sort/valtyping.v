Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure sort.typecheck sort.soundness sort.monotonicity sort.completeness.

(* Value typing and neutral typing (corrected) *)
Inductive vty (Γ : list whnf) : whnf -> whnf -> Prop :=
| VT_StarTy  : vty Γ VStar VStar
| VT_NatTy   : vty Γ VNat  VStar

(* Π-formation: codomain is checked by instantiating the closure at fresh *)
| VT_PiTy : forall A B vB,
    vty Γ A VStar ->
    clos_eval' B fresh vB ->
    vty (A :: Γ) vB VStar ->
    vty Γ (VPi A B) VStar

(* Σ-formation, same “fresh” trick; codomain lives under the extended context *)
| VT_SigmaTy : forall A B vB,
    vty Γ A VStar ->
    clos_eval' B fresh vB ->
    vty (A :: Γ) vB VStar ->
    vty Γ (VSigma A B) VStar

(* λ : instantiate both the body-closure and codomain at fresh;
   body must be typed under the extended context *)
| VT_Lam : forall A B cl r vB,
    vty Γ (VPi A B) VStar ->
    clos_eval' cl fresh r ->
    clos_eval' B  fresh vB ->
    vty (A :: Γ) r vB ->      (* <-- corrected: body types under A :: Γ *)
    vty Γ (VLam cl) (VPi A B)

(* Pair at a Σ-type: a : A and b : (B·a) *)
| VT_Pair : forall (A : whnf) (Bcl : closure) (a b vB : whnf),
    vty Γ A VStar ->
    vty Γ a A ->
    clos_eval' Bcl a vB ->
    vty Γ b vB ->
    vty Γ (VPair A vB a b) (VSigma A Bcl)

| VT_Zero  : vty Γ VZero VNat
| VT_Succ  : forall n, vty Γ n VNat -> vty Γ (VSucc n) VNat

(* Neutrals lift to values with the same type *)
| VT_Neutral : forall nx A, nty Γ nx A -> vty Γ (VNeutral nx) A

with nty (Γ : list whnf) : neutral -> whnf -> Prop :=
| NT_Var  : forall i A,
    nth_error Γ i = Some A ->
    nty Γ (NVar i) A

| NT_App  : forall n A B v vB,
    nty Γ n (VPi A B) ->
    vty Γ v A ->
    clos_eval' B v vB ->
    nty Γ (NApp n v) vB

| NT_Fst  : forall n A B,
    nty Γ n (VSigma A B) ->
    nty Γ (NFst n) A

| NT_Snd  : forall n A B vB,
    nty Γ n (VSigma A B) ->
    clos_eval' B (VNeutral (NFst n)) vB ->
    nty Γ (NSnd n) vB

| NT_NatRec : forall P z s nx cP vTy,
    vty Γ P (VPi VNat cP) ->
    nty Γ nx VNat ->
    clos_eval' cP (VNeutral nx) vTy ->
    nty Γ (NNatRec P z s nx) vTy

| NT_VecRec : forall A P z s n nx cP c2 vTy,
    vty Γ A VStar ->
    vty Γ P (VPi VNat cP) ->
    nty Γ nx (VVec n A) ->
    clos_eval' cP n (VPi (VVec n A) c2) ->
    clos_eval' c2 (VNeutral nx) vTy ->
    nty Γ (NVecRec A P z s n nx) vTy.

(* Theorem preservation_infer_bigstep :
  forall k Γ t A v,
     infer_fuel k Γ t = Some A ->
     evalk k (sem_env_of_ctx Γ) t = Some v ->
     exists B, vty Γ v B /\ conv A B
with preservation_check_bigstep:
  forall k Γ t A v,
     check_fuel k Γ t A = true ->
     evalk k (sem_env_of_ctx Γ) t = Some v ->
     exists B, vty Γ v B /\ conv A B.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H, H0.
         case_eq t; intros.
         * subst. inversion H. subst. inversion H0. subst.
           exists VStar. split. constructor.
           constructor.
         * subst. inversion H. subst. inversion H0. subst.
           exists VStar. split. constructor.
           constructor.
         * subst.
           case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H1 in H0.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           case_eq w0; intros; subst; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H3 in H.
           case_eq(infer_fuel k (w0 :: Γ) t1); intros.
           rewrite H4 in H.
           case_eq w1; intros; subst; try easy.
           inversion H0. subst. inversion H. subst.
           rewrite H1 in H3. inversion H3. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1, HB2)).
           inversion HB2. subst.
           exists VStar. split.
           apply VT_PiTy with (vB := VStar).
           easy. simpl.
           apply infer_fuel_sound in H4.
           inversion H4. subst.
           constructor. unfold env_cons. unfold sem_env_of_ctx. simpl.
           simpl. exists VStar. intros.
           constructor. constructor.
           rewrite H4 in H. easy.
           rewrite H3 in H. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy. *)
