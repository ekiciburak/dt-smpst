Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure sort.typecheck sort.soundness sort.monotonicity sort.completeness.


(* Corrected vty / nty: neutrals use type `neutral` where needed *)

Inductive vty (Γ : list whnf) : whnf -> whnf -> Prop :=
| VT_StarTy  : vty Γ VStar VStar
| VT_NatTy   : vty Γ VNat  VStar

(* Pi formation *)
| VT_Pi : forall (Aterm Bterm : term) (vA : whnf),
    infer Γ Aterm VStar ->
    eval' (sem_env_of_ctx Γ) Aterm vA ->
    infer (vA :: Γ) Bterm VStar ->
    vty Γ (VPi vA (Cl (sem_env_of_ctx Γ) Bterm)) VStar

(* Sigma formation *)
| VT_Sigma : forall (Aterm Bterm : term) (vA : whnf),
    infer Γ Aterm VStar ->
    eval' (sem_env_of_ctx Γ) Aterm vA ->
    infer (vA :: Γ) Bterm VStar ->
    vty Γ (VSigma vA (Cl (sem_env_of_ctx Γ) Bterm)) VStar

(* Lambda *)
| VT_Lam : forall (Aterm Bterm : term) (cl : closure) (r vB vA : whnf),
    vty Γ (VPi vA (Cl (sem_env_of_ctx Γ) Bterm)) VStar ->
    clos_eval' cl fresh r ->
    clos_eval' (Cl (sem_env_of_ctx Γ) Bterm) fresh vB ->
    vty (vA :: Γ) r vB ->
    vty Γ (VLam cl) (VPi vA (Cl (sem_env_of_ctx Γ) Bterm))

(* Pair *)
| VT_Pair : forall (Aterm Bterm : term) (a b vA vBsnd : whnf),
    infer Γ Aterm VStar ->
    eval' (sem_env_of_ctx Γ) Aterm vA ->
    vty Γ a vA ->
    clos_eval' (Cl (sem_env_of_ctx Γ) Bterm) a vBsnd ->
    vty Γ b vBsnd ->
    vty Γ (VPair vA vBsnd a b) (VSigma vA (Cl (sem_env_of_ctx Γ) Bterm))

| VT_Zero  : vty Γ VZero VNat
| VT_Succ  : forall n, vty Γ n VNat -> vty Γ (VSucc n) VNat

(* VEC: formation and constructors *)
(* VVec n A is a type when A is a type and n is Nat *)
| VT_Vec : forall (Aterm : term) (vA vn : whnf),
    infer Γ Aterm VStar ->                       (* Aterm : ⋆ *)
    eval' (sem_env_of_ctx Γ) Aterm vA ->        (* Aterm ⇓ vA *)
    vty Γ vn VNat ->                             (* vn is a natural WHNF *)
    vty Γ (VVec vn vA) VStar

(* empty vector at A : Vec 0 A *)
| VT_VNil : forall (Aterm : term) (vA : whnf),
    infer Γ Aterm VStar ->
    eval' (sem_env_of_ctx Γ) Aterm vA ->
    vty Γ (VNilV vA) (VVec VZero vA)

(* cons: A, n, x, xs are already semantic WHNFs *)
| VT_VCons : forall (vA vn vx vxs : whnf),
    vty Γ vA VStar ->                         (* A is a type *)
    vty Γ vn VNat ->                          (* n : Nat (semantic) *)
    vty Γ vx vA ->                            (* x : A *)
    vty Γ vxs (VVec vn vA) ->                 (* xs : Vec n A *)
    vty Γ (VConsV vA vn vx vxs) (VVec (VSucc vn) vA)

| VT_Neutral : forall nx A, nty Γ nx A -> vty Γ (VNeutral nx) A

with nty (Γ : list whnf) : neutral -> whnf -> Prop :=
| NT_Var  : forall i A,
    nth_error Γ i = Some A ->
    nty Γ (NVar i) A

| NT_App : forall (n : neutral) (vA : whnf) (Bcl : closure) (v vB : whnf),
    nty Γ n (VPi vA Bcl) ->
    vty Γ v vA ->
    clos_eval' Bcl v vB ->
    nty Γ (NApp n v) vB

| NT_Fst  : forall (n : neutral) (vA : whnf) (Bcl : closure),
    nty Γ n (VSigma vA Bcl) ->
    nty Γ (NFst n) vA

| NT_Snd : forall (n : neutral) (vA : whnf) (Bcl : closure) (vB : whnf),
    nty Γ n (VSigma vA Bcl) ->
    clos_eval' Bcl (VNeutral (NFst n)) vB ->
    nty Γ (NSnd n) vB

| NT_NatRec : forall (vP : whnf) z s (nx : neutral) (cP : closure) vTy,
    vty Γ vP (VPi VNat cP) ->
    nty Γ nx VNat ->                               (* nx is a neutral *)
    clos_eval' cP (VNeutral nx) vTy ->
    nty Γ (NNatRec vP z s nx) vTy

| NT_VecRec : forall (vA vP vz vs vn : whnf) (nx : neutral) (cP c2 : closure) vTy,
    vty Γ vA VStar ->
    vty Γ vP (VPi VNat cP) ->
    nty Γ nx (VVec vn vA) ->
    clos_eval' cP vn (VPi (VVec vn vA) c2) ->
    clos_eval' c2 (VNeutral nx) vTy ->
    nty Γ (NVecRec vA vP vz vs vn nx) vTy.

Lemma clos_evalk_sound :
  forall k cl v, clos_evalk k cl = Some v -> clos_eval' cl fresh v.
Proof.
  intros; simpl in *.
  unfold clos_evalk in *.
  destruct cl.
  eapply evalk_sound in H. easy.
Qed.

(* Lemma evfp1: forall k Γ t1 t2 t3 t4,
  evalk k Γ (Pair t1 t2 t3 t4) = Some VStar -> False.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H.
         case_eq(evalk k Γ t1); intros.
         rewrite H0 in H.
         case_eq(evalk k Γ t2); intros.
         rewrite H1 in H.
         case_eq(evalk k Γ t3); intros.
         rewrite H in H.
         eapply IHk. 
 *)
Lemma peq1: forall k Γ t w0 w1 w2 w3 v,
  evalk k Γ t = Some (VPair w1 w2 w3 v) ->
  evalk k Γ (TFst t) = Some w0 ->
  w0 = w3.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H, H0.
         destruct t; try easy.
         * case_eq(evalk k Γ t1); intros.
           rewrite H1 in H.
           easy.
           rewrite H1 in H. easy.
         * case_eq(evalk k Γ t1); intros.
           rewrite H1 in H.
           easy.
           rewrite H1 in H. easy.
         * case_eq(evalk k Γ t); intros.
           rewrite H1 in H.
           easy.
           rewrite H1 in H. easy.
         * case_eq(evalk k Γ t1); intros.
           rewrite H1 in H.
           case_eq(evalk k Γ t2); intros.
           rewrite H2 in H.
           case_eq(evalk k Γ t3); intros.
           rewrite H3 in H.
           case_eq(evalk k Γ t4); intros.
           rewrite H4 in H.
           inversion H. subst.
           case_eq(evalk k Γ (Pair t1 t2 t3 t4) ); intros.
           rewrite H5 in H0. 
           destruct w; try easy.
           apply evalk_sound in H5.
          
(*            inversion H5.
           subst.
           
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
          
           apply evalk_sound in H5. *)
           inversion H5. subst.
           apply evalk_sound in H3.
           specialize (eval'_det _ _ _ _ H3 H17); intros. subst. inversion H0. easy.

(*            apply evalk_sound in H5.
           inversion H5. *)
(*            apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5.
           apply evalk_sound in H5.
           inversion H5. *)
           
           rewrite H5 in H0. easy.
           rewrite H4 in H. easy.
           rewrite H3 in H. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H. easy.
         * case_eq(evalk k Γ t); intros.
           rewrite H1 in H.
           destruct w; try easy.
           case_eq(evalk k Γ (TFst t)); intros.
           rewrite H2 in H0.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           apply evalk_sound in H2.
           inversion H2. subst.
           apply evalk_sound in H1.
           specialize (eval'_det _ _ _ _ H1 H5); intros.
           inversion H3.
           subst. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H. easy.
         * case_eq(evalk k Γ t); intros.
           rewrite H1 in H.
           destruct w; try easy.
           case_eq(evalk k Γ (TSnd t)); intros.
           rewrite H2 in H0.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           apply evalk_sound in H2.
           inversion H2.
           subst.
           apply evalk_sound in H1.
           specialize (eval'_det _ _ _ _ H1 H5); intros.
           inversion H3.
           subst. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H. easy.
Admitted.

Corollary conv_complete_clo :
  forall B B',
    conv_clo B B' ->
    exists k v v',
      clos_eval_fuel k B  fresh = Some v /\
      clos_eval_fuel k B' fresh = Some v' /\
      conv_fuel k v v' = true.
Proof. destruct conv_complete as [_ H]. exact H. Qed.

(* Lemma conv_clo_app :
  forall c1 c2 x v1 v2,
    conv_clo c1 c2 ->
    clos_eval' c1 x v1 ->
    clos_eval' c2 x v2 ->
    conv v1 v2.
Proof. intros.
       apply conv_complete_clo in H.
       destruct H as (k,(va,(vb,(Ha,(Hb,Hc))))).
       apply clos_eval_fuel_sound in Ha.
       apply clos_eval_fuel_sound in Hb.
       unfold clos_eval' in *.
       destruct c1, c2.
       
       induction c1; intros.
       case_eq c2; intros.
       subst.
       inversion H. subst. *)

Theorem preservation_infer_bigstep :
  forall k Γ t A v,
     infer_fuel k Γ t = Some A ->
     evalk k (sem_env_of_ctx Γ) t = Some v ->
     exists B, vty Γ v B /\ exists k', conv_fuel k' A B = true
with preservation_check_bigstep:
  forall k Γ t A v,
     check_fuel k Γ t A = true ->
     evalk k (sem_env_of_ctx Γ) t = Some v ->
     exists B, vty Γ v B /\ exists k', conv_fuel k' A B = true.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H, H0.
         case_eq t; intros.
         * subst. inversion H. subst. inversion H0. subst.
           exists VStar. split. constructor.
           exists 1. easy.
         * subst. inversion H. subst. inversion H0. subst.
           exists VStar. split. constructor.
           exists 1. easy.
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
           exists VStar. split.
           apply VT_Pi with (Aterm := t0) (Bterm := t1).
           apply infer_fuel_sound with (k:=k). easy.
           apply evalk_sound with (k:=k). easy.
           apply infer_fuel_sound with (k:=k). easy.
           exists 1. easy.
           rewrite H4 in H. easy.
           rewrite H3 in H. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy.
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
           exists VStar. split.
           apply VT_Sigma with (Aterm := t0) (Bterm := t1).
           apply infer_fuel_sound with (k:=k). easy.
           apply evalk_sound with (k:=k). easy.
           apply infer_fuel_sound with (k:=k). easy.
           exists 1. easy.
           rewrite H4 in H. easy.
           rewrite H3 in H. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy.
         * subst. inversion H. subst. inversion H0. subst.
           exists VNat. split. constructor. exists 1. easy.
         * subst.
           case_eq( evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H1 in H0.
           case_eq(check_fuel k Γ t0 VNat); intros.
           rewrite H2 in H. inversion H. subst. inversion H0. subst.
           specialize(preservation_check_bigstep _ _ _ _ _ H2 H1).
           destruct preservation_check_bigstep as (B, (HB1,HB2)).
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           exists VNat. split. constructor. easy.
           exists 1. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy.
         * subst. easy.
         * subst.
           case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.

           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
(*            
           
           rewrite H2 in H. easy.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w0; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w0; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst. *)
           exists w1. split. easy.
           apply conv_complete_conv in H6.
           easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy.
         * subst.
           case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) (TFst t0)); intros.
           rewrite H3 in H.
           case_eq( clos_eval_fuel k c w0); intros.
           rewrite H4 in H.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           exists w2. split. easy.
           
(*            rewrite H2 in H. easy.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst. easy.
           rewrite H2 in H. easy.
           
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w0; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w0; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           rewrite H2 in H.
           destruct w; try easy.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst. easy.
           rewrite H2 in H. easy.

           case_eq(infer_fuel k Γ t0); intros.
           subst.
           rewrite H2 in H.
           destruct w0; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) (TFst t0)); intros.
           rewrite H3 in H.
           case_eq(clos_eval_fuel k c w); intros.
           rewrite H4 in H.
           inversion H. subst. inversion H0. subst.
           specialize(IHk _ _ _ _ H2 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           exists w1. split. easy. *)
           apply clos_eval_fuel_sound in H4.
           specialize(peq1 _ _ _ _ _ _ _ _ H1 H3); intros.
           subst.
           
           inversion H15. subst.
           specialize(H5 _ _ _ H4 H13).
           apply conv_complete in H5. easy.
           
           rewrite H4 in H. easy.
           rewrite H3 in H. easy.
           rewrite H2 in H. easy.
           rewrite H1 in H0. easy.
         * subst.
           admit.
         * subst.
           easy.
         * subst.
           case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
           rewrite H1 in H0.
           case_eq( evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H2 in H0.
           case_eq(infer_fuel k Γ t0); intros.
           rewrite H3 in H.
           destruct w1; try easy.
           rewrite H2 in H.
           case_eq(check_fuel k Γ t1 w1); intros.
           rewrite H4 in H.
           case_eq(clos_eval_fuel k c w0 ); intros.
           rewrite H5 in H.
           inversion H. subst.
           apply vappk_sound in H0.
           inversion H0. subst.
           specialize(IHk _ _ _ _ H3 H1).
           destruct IHk as (B, (HB1,HB2)).
           inversion HB1. subst.
           destruct HB2 as (k2, HB2).
           apply conv_fuel_sound in HB2.
           inversion HB2. subst.
           inversion H16. subst.
           unfold clos_eval' in H9.
           admit.
           
Admitted.

