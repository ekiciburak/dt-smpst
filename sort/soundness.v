Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure sort.typecheck.


Lemma det_quintet :
  (forall ρ t v1, eval' ρ t v1 -> forall v2, eval' ρ t v2 -> v1 = v2) /\
  (forall f a r1, vapp f a r1 -> forall r2, vapp f a r2 -> r1 = r2) /\
  (forall vP vz vs vn r1, eval_natrec vP vz vs vn r1 -> forall r2, eval_natrec vP vz vs vn r2 -> r1 = r2) /\
  (forall f as_ r1, vapps f as_ r1 -> forall r2, vapps f as_ r2 -> r1 = r2) /\
  (forall vA vP vz vs vn vxs r1, eval_vecrec vA vP vz vs vn vxs r1 -> forall r2, eval_vecrec vA vP vz vs vn vxs r2 -> r1 = r2).
Proof.
  apply evalsys_mutind; intros.
- inversion H. easy.
- inversion H. easy.
- inversion H. subst. rewrite H2 in e. inversion e. easy.
  subst. rewrite H2 in e. easy.
- inversion H. subst. rewrite H2 in e. easy.
  subst. easy.
- inversion H0. subst.
  f_equal. apply H. easy.
- inversion H0. subst.
  f_equal. apply H. easy.
- inversion H. easy.
- inversion H2. subst.
  apply H in H5. subst.
  apply H0 in H7. subst.
  apply H1. easy.
- inversion H3. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in H12. subst.
  apply H2 in H13. subst. easy.
- inversion H0. subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H3 A B va vb). reflexivity.
- inversion H0. subst.
  apply H in H3. easy.
  subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H5 n). reflexivity.
- inversion H0. subst.
  apply H in H3. subst.
  exfalso. apply (n A B v2 vb). reflexivity.
  subst. apply H in H3. subst.
  exfalso. apply (n0 n1). reflexivity.
  subst. apply H. easy.
- inversion H0. subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H3 A B va vb). reflexivity.
- inversion H0. subst.
  apply H in H3. easy.
  subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H5 n). reflexivity.
- inversion H0. subst.
  apply H in H3. subst.
  exfalso. apply (n A B va v2). reflexivity.
  subst. apply H in H3. subst.
  exfalso. apply (n0 n1). reflexivity.
  subst. apply H. easy.
- inversion H. easy.
- inversion H0. subst.
  apply H in H3. subst. easy.
- inversion H4. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in H13. subst.
  apply H2 in H14. subst.
  apply H3 in H15. subst. easy.
- inversion H1. subst.
  apply H in H5.
  apply H0 in H7. subst.
  easy.
- inversion H0; subst.
  apply H in H3. subst. easy.
- inversion H3. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in e1. subst.
  apply H2 in e2. subst.
  apply H2 in H13. subst.
  apply H1 in H12. subst. easy.
- inversion H6. subst.
  apply H5.
  apply H in H13. subst.
  apply H0 in H15. subst.
  apply H1 in H17. subst.
  apply H2 in H18. subst.
  apply H3 in H19. subst.
  apply H4 in H20. subst.
  apply H5 in H21. subst. easy.
- inversion H0; subst.
 + (* VApp_Lam *) eapply H; eauto.
 + exfalso. apply (H1 ρ' b). reflexivity.
- inversion H. easy.
  exfalso. apply (H1 n). reflexivity.
- inversion H.
  + subst. exfalso. apply (n ρ' b). reflexivity.
  + subst. exfalso. apply (n0 n1). reflexivity.
  + subst. easy.
- inversion H. easy.
  easy.
- inversion H2. subst.
  apply H in H4. subst.
  apply H0 in H5. subst.
  apply H1 in H9. easy.
  subst. exfalso. apply (H3 vn). easy.
- inversion H. subst.
  easy.
  subst. exfalso. apply (H2 nn). easy.
- inversion H. subst.
  easy. 
  subst. exfalso. apply (n vn0). easy.
  subst. exfalso. apply (n1 nn). easy.
  easy.
- inversion H.
  easy.
- inversion H1. subst. apply H0. apply H in H5. subst. easy.
- inversion H. easy. easy.
- inversion H1. subst.
  apply H0.
  apply H in H12. subst. easy.
  subst.
  exfalso. apply (H3 vw vn' va vxs). easy.
 - inversion H. subst.
   easy.
   subst. exfalso.
   apply (H2 nx). easy.
- inversion H.
  subst. easy. subst.
  exfalso. apply (n0 vw vn' va vxs0). easy.
  subst.
  exfalso.
  apply (n1 nx). easy.
  easy.
Qed.

(* Determinism corollaries for the three relations *)
Theorem eval'_det :
  forall ρ t v1 v2, eval' ρ t v1 -> eval' ρ t v2 -> v1 = v2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Ha with (ρ := ρ) (t := t); easy.
Qed.

Theorem vapp_det :
  forall f a r1 r2, vapp f a r1 -> vapp f a r2 -> r1 = r2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Hb with (f := f) (a := a); easy.
Qed.

Theorem eval_natrec_det :
  forall vP vz vs vn r1 r2,
    eval_natrec vP vz vs vn r1 -> eval_natrec vP vz vs vn r2 -> r1 = r2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Hc with (vP := vP) (vz := vz) (vs := vs) (vn := vn); easy.
Qed.

Lemma eval'_Lam_inv ρ A b v: eval' ρ (Lam A b) v -> v = VLam (Cl ρ b).
Proof. intros H. inversion H; subst; reflexivity. Qed.

Lemma eval'_Pi_inv ρ A B v: eval' ρ (Pi A B) v -> exists vA, v = VPi vA (Cl ρ B) /\ eval' ρ A vA.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma eval'_Sigma_inv ρ A B v: eval' ρ (Sigma A B) v -> exists vA, v = VSigma vA (Cl ρ B) /\ eval' ρ A vA.
Proof. intros H; inversion H; subst; eauto. Qed.


Lemma clos_eval'_det (c:closure) (v x y:whnf) :
  clos_eval' c v x -> 
  clos_eval' c v y -> 
  x = y.
Proof.
  destruct c as [ρ body]; simpl; eauto using eval'_det.
Qed.


Theorem evalk_sound: forall k ρ t v,
  evalk k ρ t = Some v ->
  eval' ρ t v
with vappk_sound: forall k vf vu r,
  vappk k vf vu = Some r ->
  vapp vf vu r
with vnatreck_sound: forall k vP vz vs vn r,
  vnatreck k vP vz vs vn = Some r ->
  eval_natrec vP vz vs vn r
with vappsk_sound: forall k f args r,
  vappsk k f args = Some r ->
  vapps f args r
with vvecreck_sound: forall k vA vP vz vs vn vxs v,
  vvecreck k vA vP vz vs vn vxs = Some v ->
  eval_vecrec vA vP vz vs vn vxs v.
Proof. intro k.
       induction k; intros.
       - simpl in H. easy.
       - simpl in H. 
         case_eq t; intros.
         + subst. inversion H. constructor.
         + subst. inversion H. constructor.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst. inversion H. constructor.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         inversion H. constructor; easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst.
           destruct (evalk k ρ t0) eqn:Ep; try discriminate.
           case_eq w; intros.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TFst_Other. easy.
             easy.
             easy.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TFst_Other. easy.
             easy.
             easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. subst.
             apply IHk in Ep. 
             apply E'_TFst_Pair with (A := w0) (B := w1) (vb:= w3). easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
         + subst.
           destruct (evalk k ρ t0) eqn:Ep; try discriminate.
           case_eq w; intros.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TSnd_Other. easy.
             easy.
             easy.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TSnd_Other. easy.
             easy.
             easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. subst.
             apply IHk in Ep. 
             apply E'_TSnd_Pair with (A := w0) (B := w1) (va:= w2). easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
         + subst.
           case_eq(nth_error ρ n); intros.
           * rewrite H0 in H. inversion H. subst.
             constructor. easy.
           * rewrite H0 in H.
             inversion H. subst.
             apply E'_Var_None. easy.
         + subst. inversion H. constructor.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H. 
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                apply IHk in H0, H1.
                apply vappk_sound in H.
                apply E'_App with (vt := w) (vu := w0); easy.
              ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         apply vnatreck_sound in H.
                         apply E'_NatRec with (vP := w) (vz := w0) (vs := w1) (vn := w2); easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
            * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H. 
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                apply IHk in H0, H1. inversion H. subst.
                apply E'_Vec; easy.
              ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0; try lia.
             inversion H. subst.
             constructor. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         inversion H. subst.
                         constructor; easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
            * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H.
                         case_eq(evalk k ρ t4); intros.
                         ***** rewrite H4 in H.
                               case_eq(evalk k ρ t5); intros.
                               ****** rewrite H5 in H.
                                      apply IHk in H0; try lia.
                                      apply IHk in H1; try lia.
                                      apply IHk in H2; try lia.
                                      apply IHk in H3; try lia.
                                      apply IHk in H4; try lia.
                                      apply IHk in H5; try lia.
                                      apply vvecreck_sound in H.
                                      econstructor; eauto.
                               ****** rewrite H5 in H. easy.
                         ***** rewrite H4 in H. easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
       - intro k. 
         induction k; intros. 
         + simpl in H. easy.
         + simpl in H.
           destruct vf.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. destruct c. apply evalk_sound in H.
             constructor. easy.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
       - intro k.
         induction k; intros.
         + simpl in H. easy.
         + simpl in H.
           case_eq vn; intros; subst.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H. subst.
             constructor.
           * case_eq(vnatreck k vP vz vs w); intros.
             ** rewrite H0 in H.
                apply IHk in H0.
                case_eq(vappk k vs w); intros.
                *** rewrite H1 in H.
                    apply vappk_sound in H, H1.
                    apply ENR_Succ with (vrec := w0) (v1 := w1); easy.
                *** rewrite H1 in H. easy.
             ** rewrite H0 in H. easy.
           * inversion H. subst.
             constructor.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
       - intro k.
         induction k; intros.
         + simpl in H. easy.
         + simpl in H.
           case_eq args; intros; subst.
           * inversion H. subst.
             constructor.
           * case_eq(vappk k f w); intros.
             ** rewrite H0 in H.
                apply IHk in H.
                apply vapps_cons with (r := w0).
                apply vappk_sound with (k := k). easy. easy.
             ** rewrite H0 in H. easy.
       - intro k. 
         induction k; intros. 
         + simpl in H. easy.
         + simpl in H.
           case_eq vxs; intros; subst; try easy.
           * inversion H. subst.
             constructor. easy. easy. easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * case_eq(vvecreck k vA vP vz vs w0 w2); intros.
             ** rewrite H0 in H.
                simpl.
                apply IHk in H0.
                apply EVR_Cons with (vrec := w3).
                easy. apply vappsk_sound in H. easy.
             ** rewrite H0 in H. easy.
Qed.

Lemma clos_eval_fuel_sound :
  forall k B x v,
    clos_eval_fuel k B x = Some v ->
    clos_eval' B x v.
Proof.
  intros k B x v H.
  destruct k as [|k']; [inversion H|].
  simpl in H.
  unfold clos_eval'.
  destruct B as [ρ t]; simpl in H.
  (* now H : evalk k' (x :: ρ) t = Some v *)
  apply evalk_sound in H.
  apply H.
Qed.

Lemma conv_fuel_sound :
  forall k v w,
    conv_fuel k v w = true ->
    conv v w
with conv_neutral_fuel_sound :
  forall k n n',
    conv_neutral_fuel k n n' = true ->
    conv (VNeutral n) (VNeutral n').
Proof.
  (* === conv_fuel_sound === *)
  intros k; induction k as [|k IH] using nat_ind; intros; simpl in H; try discriminate.
  - (* k = S k, main cases on v,w *)

    destruct v; destruct w; simpl in H; try discriminate.

    + (* VStar, VStar *)
      now constructor.

    + (* VNat, VNat *)
      now constructor.

    + (* VPi ... *)
      cbn in H.
      destruct (conv_fuel k v w) eqn:HA; try discriminate.
      apply IH in HA as HAA.
      destruct (clos_eval_fuel k c fresh) eqn:HB; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
      apply clos_eval_fuel_sound in HB.
      apply clos_eval_fuel_sound in HB'.
      apply IH in H as HBB.
      eapply CoV_Pi; [exact HAA|].
      apply ConvClo with (v := w0) (v' := w1).
      easy. easy. easy.
      
      
(*       intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy. *)
    + (* VSigma ... *)
      cbn in H.
      destruct (conv_fuel k v w) eqn:HA; try discriminate.
      apply IH in HA as HAA.
      destruct (clos_eval_fuel k c fresh) eqn:HB; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
      apply clos_eval_fuel_sound in HB.
      apply clos_eval_fuel_sound in HB'.
      apply IH in H as HBB.
      eapply CoV_Sigma; [exact HAA|].
      apply ConvClo with (v := w0) (v' := w1).
      easy. easy. easy.
(*       intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy. *)

    + (* VLam cl1, VLam cl2 *)
      cbn in H.
      destruct (clos_eval_fuel k c fresh) eqn:HC; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HC'; try discriminate.
      apply clos_eval_fuel_sound in HC.
      apply clos_eval_fuel_sound in HC'.
      apply IH in H.
      constructor.
      apply ConvClo with (v := w) (v' := w0).
      easy. easy. easy.
(*       intros.
      destruct c, c0. simpl in *.
      specialize (eval'_det _ _ _ _ H0 HC); intros. subst.
      specialize (eval'_det _ _ _ _ H1 HC'); intros. subst.
      easy. *)

    + (* VPair ... *)
      apply Bool.andb_true_iff in H as [H12 H34].
      apply Bool.andb_true_iff in H34 as [H1 H2].
      apply Bool.andb_true_iff in H2 as [H3 H4].
      apply IH in H12.
      apply IH in H1.
      apply IH in H3.
      apply IH in H4.
      constructor; easy.

    + (* VZero, VZero *)
      now constructor.

    + (* VSucc n, VSucc n' *)
      now constructor; apply IH.

    + (* VNeutral n, VNeutral n' *)
      now apply conv_neutral_fuel_sound with (k := k).
    + apply Bool.andb_true_iff in H as [H1 H2].
      apply IH in H2.
      apply IH in H1.
     constructor; easy.
    
    + constructor. apply IH. easy.
    + apply Bool.andb_true_iff in H as [H1 H2].
      apply Bool.andb_true_iff in H2 as [H2 H3].
      apply Bool.andb_true_iff in H3 as [H3 H4].
      constructor. apply IH. easy.
      apply IH. easy.
      apply IH. easy.
      apply IH. easy.

  (* === conv_neutral_fuel_sound === *)
  - (* start neutral branch *)
    intros k; induction k as [|k IH] using nat_ind; intros; simpl in H; try discriminate.
    destruct n; destruct n'; simpl in H; try discriminate.

    + (* NVar *)
      apply Nat.eqb_eq in H. subst.
      constructor.

    + (* NApp *)
      apply Bool.andb_true_iff in H as [Hh Ha].
      specialize (IH _ _ Hh).
      apply conv_fuel_sound in Ha.
      econstructor; eauto.

    + (* NFst *)
      now constructor; eauto using IH.

    + (* NSnd *)
      now constructor; eauto using IH.

    + (* NNatRec *)
     apply Bool.andb_true_iff in H as [H Htail].
     apply Bool.andb_true_iff in Htail as [Hs Htail].
     apply Bool.andb_true_iff in Htail as [Hn Htail].
      apply conv_fuel_sound in H.
      apply conv_fuel_sound in Hs.
      apply conv_fuel_sound in Hn.
      (* Order was P, z, s, then n; adjust if your andb nesting differs *)
      econstructor; eauto.
    +  apply Bool.andb_true_iff in H as [H Htail].
     apply Bool.andb_true_iff in Htail as [Hs Htail].
     apply Bool.andb_true_iff in Htail as [Hn Htail].
     apply Bool.andb_true_iff in Htail as [Hu Htail].
     apply Bool.andb_true_iff in Htail as [Hv Htail].
      apply conv_fuel_sound in H.
      apply conv_fuel_sound in Hs.
      apply conv_fuel_sound in Hn.
      apply conv_fuel_sound in Hu.
      apply conv_fuel_sound in Hv. 
      (* Order was P, z, s, then n; adjust if your andb nesting differs *)
      econstructor; eauto.
Qed.

Theorem infer_fuel_sound :
  forall k Γ t A, infer_fuel k Γ t = Some A -> infer Γ t A
with check_fuel_sound :
  forall k Γ t A, check_fuel k Γ t A = true -> check Γ t A.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H.
         case_eq t; intros; subst.
         + inversion H. subst. constructor.
         + inversion H. subst. constructor.
         + (* Pi A B *)
           destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
           destruct (infer_fuel k (w :: Γ) t1) eqn:HB; try discriminate.
           destruct w0; try discriminate.
           inversion H; subst.
           apply I_Pi with (vA := w).
           * eapply IHk; eauto.
           * apply evalk_sound with (k := k). easy.
           * eapply IHk; eauto.
         + (* Sigma A B *)
           destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
           destruct (infer_fuel k (w :: Γ) t1) eqn:HB; try discriminate.
           destruct w0; try discriminate.
           inversion H; subst.
           apply I_Sigma with (vA := w).
           * eapply IHk; eauto.
           * apply evalk_sound with (k := k). easy.
           * eapply IHk; eauto.
         + inversion H. subst. constructor.
         + case_eq(check_fuel k Γ t0 VNat); intros.
           * rewrite H0 in H. inversion H. constructor.
             apply check_fuel_sound with (k := k). easy.
           * rewrite H0 in H. easy.
         + (* Pair does not synthesize *)
           discriminate.
         + destruct (infer_fuel k Γ t0) eqn:Hp; try discriminate.
           destruct w; try discriminate.
           inversion H; subst.
           eapply I_Fst.
           eapply IHk; eauto.
         + (* TSnd p *)
           destruct (infer_fuel k Γ t0) eqn:Hp; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) (TFst t0)) eqn:Ef; try discriminate.
           destruct (clos_eval_fuel k c w0) eqn:EB; try discriminate.
           inversion H; subst.
           apply I_Snd with (A:=w) (B:=c) (vfst:=w0) (vB:=A).
           * eapply IHk; eauto.
           * eapply evalk_sound; eauto.
           * eapply clos_eval_fuel_sound; eauto.
         + constructor. easy.
         + discriminate. 
                           
         + (* App t u *)
           destruct (infer_fuel k Γ t0) eqn:Ht; try discriminate.
           destruct w; try discriminate.
           destruct (check_fuel k Γ t1 w) eqn:Hu; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t1) eqn:Eu; try discriminate.
           destruct (clos_eval_fuel k c w0) eqn:EB; try discriminate.
           inversion H; subst.
(*            eapply I_App. *)
           apply I_App with (A:=w) (B:=c) (vu:=w0) (vB:=A).
           * eapply IHk; eauto.
           * eapply check_fuel_sound; eauto.
           * eapply evalk_sound; eauto.
           * eapply clos_eval_fuel_sound; eauto.
         + (* t = NatRec t0 t1 t2 t3, and H is the big match you showed *)
            simpl in H.
            destruct (check_fuel k Γ t0 (VPi VNat (Cl (sem_env_of_ctx Γ) Star))) eqn:HCp; try discriminate H.
            destruct (evalk k (sem_env_of_ctx Γ) t0) as [vP|] eqn:HP; try discriminate H.
            destruct (fn_closure_of vP) as [cP|] eqn:HcP; try discriminate H.
            destruct (evalk k (sem_env_of_ctx Γ) t3) as [vn|] eqn:Hn; try discriminate H.
            destruct (clos_eval_fuel k cP vn) as [vTy|] eqn:HTy; try discriminate H.
            destruct (clos_eval_fuel k cP VZero) as [vP0|] eqn:HP0; try discriminate H.
            (* split the final andb *)
            case_eq((check_fuel k Γ t1 vP0 && check_fuel k Γ t3 VNat)%bool); intros.
            rewrite H0 in H.
            apply Bool.andb_true_iff in H0.
            destruct H0 as [Hz HnNat]. inversion H. subst. clear H.
            (* the branch returns Some vTy, so A = vTy *)
(*             assert (A = vTy) by reflexivity. subst A. *)

            (* Now discharge premises of I_NatRec *)
            eapply I_NatRec.
            * (* check Γ P expP *)
              eapply check_fuel_sound; eauto.
            * (* eval' P vP *)
              eapply evalk_sound; eauto.
            * (* fn_closure_of vP = Some cP *)
              exact HcP.
            * (* clos_eval' cP VZero vP0 *)
              eapply clos_eval_fuel_sound; eauto.
            * (* check Γ z vP0 *)
              eapply check_fuel_sound; eauto.
            * (* check Γ n Nat *)
              eapply check_fuel_sound; eauto.
            * (* eval' n vn *)
              eapply evalk_sound; eauto.
            * (* clos_eval' cP vn vTy *)
              eapply clos_eval_fuel_sound; eauto.
            * rewrite H0 in H. easy.
        + (* Vec n A : ★ (relaxed) *)
          destruct (infer_fuel k Γ t1) eqn:HA; try discriminate.
          destruct w; try discriminate.
          inversion H; subst. constructor. eapply IHk; eauto.

        + (* VNil A *)
          destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
          destruct w; try discriminate.
          destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
          inversion H; subst.
          eapply I_VNil; eauto.
          * eapply evalk_sound; eauto.
    + (* VCons A n x xs *)
      destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
      destruct w; try discriminate.
      destruct (check_fuel k Γ t1 VNat) eqn:Hn; try discriminate.
      destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
      destruct (evalk k (sem_env_of_ctx Γ) t1) eqn:EN; try discriminate.
      destruct (check_fuel k Γ t2 w) eqn:Hx; try discriminate.
      destruct (check_fuel k Γ t3 (VVec w0 w)) eqn:Hxs; try discriminate.
      simpl in H.
      inversion H; subst.
      eapply I_VCons with (vA:=w) (vn:=w0); eauto.
      * eapply evalk_sound; eauto.          (* vA *)
      * eapply evalk_sound; eauto.          (* vn *)
    +


      revert H.
      simpl.  (* unfold the VecRec branch of infer_fuel *)

      (* 1) A : ⋆, and its WHNF *)
      destruct (infer_fuel k Γ t0) as [ATy|] eqn:HA0; [| now discriminate].
      destruct ATy; try now discriminate.
      pose proof (IHk Γ t0 VStar HA0) as I_A.  (* infer Γ t0 ⋆ *)

      destruct (evalk k (sem_env_of_ctx Γ) t0) as [vA|] eqn:EA; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ EA) as EvA.

      (* 2) Motive P has the expected type (checked, not inferred) *)
      destruct (check_fuel k Γ t1
                 (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) t0) Star))))
               eqn:HP; [| now discriminate].
      pose proof (check_fuel_sound _ _ _ _ HP) as C_P.

      (* 3) Evaluate P, n, xs *)
      destruct (evalk k (sem_env_of_ctx Γ) t1) as [vP|] eqn:EP ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ EP) as EvP.

      destruct (evalk k (sem_env_of_ctx Γ) t4) as [vn|] eqn:En ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ En) as Evn.

      destruct (evalk k (sem_env_of_ctx Γ) t5) as [vxs|] eqn:Exs ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ Exs) as Evxs.


      (* name the two boolean checks *)
      remember (check_fuel k Γ t4 VNat)                 as bn  eqn:Hbn.
      remember (check_fuel k Γ t5 (VVec vn vA))         as bxs eqn:Hbxs.

      intros H.
      (* split the two boolean checks; kill the false branches using [H] *)
      destruct bn  eqn:Ebn  ; [| now discriminate H].
      destruct bxs eqn:Ebxs ; [| now discriminate H].
      simpl in H.

      (* from the booleans = true we get declarative checks *)
      assert (C_t4 : check Γ t4 VNat).
      { subst bn. apply check_fuel_sound with (k := k). easy. }
      assert (C_t5 : check Γ t5 (VVec vn vA)).
      { subst bxs. apply check_fuel_sound with (k := k). easy. }

      (* first semantic application of the motive: P n *)
      set (app1 :=
             match vP with
             | VPi _ c  => clos_eval_fuel k c  vn
             | VLam cl  => clos_eval_fuel k cl vn
             | _        => None
             end) in *.
      destruct app1 as [vPn|] eqn:Happ1 ; [| now discriminate H].


      (* only function shapes can yield a final [Some A] *)
      destruct vPn as
             [ | | dom c1 | dom c1 | cl1
               | | | | | | | ] ; try (simpl in H; now discriminate H).
      * (* vPn = VPi dom c1 *)
        destruct (clos_eval_fuel k c1 vxs) as [vTy|] eqn:Happ2 ; [| now discriminate H].
        inversion H; subst A; clear H.
          (* figure out which closure was used in the first app, and convert to [clos_eval'] *)
        destruct vP as
               [ | | A0 c0 | A0 c0 | cl0
                 | | | | | | |  ] ; try (simpl in Happ1; discriminate Happ1).
       
         ** (* vP = VPi A0 c0, so app1 = clos_eval_fuel k c0 vn *)
          simpl in Happ1.
          (* clos_eval' (first step) *)
          assert (CE1 : clos_eval' c0 vn (VPi dom c1)).
          { destruct (clos_eval_fuel k c0 vn) eqn:HP1 ;
              inversion Happ1; subst; eauto using clos_eval_fuel_sound. }
          (* clos_eval' (second step) *)
          assert (CE2 : clos_eval' c1 vxs vTy)
            by (eapply clos_eval_fuel_sound; exact Happ2).

          (* build the intended typing derivation *)
          eapply I_VecRec
            with (vA:=vA) (vP:=VPi A0 c0) (vn:=vn) (vxs:=vxs)
                 (vPn:=VPi dom c1) (vTy_res:=vTy); eauto.
            simpl. easy. simpl. easy.
        ** eapply I_VecRec
            with (vA:=vA) (vP:=(VLam cl0)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VPi dom c1) (vTy_res:=vTy) (cP := cl0) (c2 := c1); eauto.
            unfold app1 in *.
            apply clos_eval_fuel_sound with (k := k). easy.
            simpl.
            apply clos_eval_fuel_sound with (k := k). easy.
            
      * destruct cl1 as [ρ b].
        destruct (clos_eval_fuel k (Cl ρ b) vxs) as [vTy|] eqn:Happ2 ; [| now discriminate H].
        inversion H; subst A; clear H.

        (* again, find which closure produced [app1] and convert it to [clos_eval'] *)
        destruct vP as
               [ | | | | cl0
                 | | | | | | | ] ; try (simpl in Happ1; discriminate Happ1).
         ** (* vP = VLam cl0, so app1 = clos_eval_fuel k cl0 vn *)
          simpl in Happ1.
          unfold app1 in *.
          assert (CE1 : clos_eval' c vn (VLam (Cl ρ b))).
          { destruct (clos_eval_fuel k c vn) eqn:HP1 ;
              inversion Happ1; subst; eauto using clos_eval_fuel_sound. }
          assert (CE2 : clos_eval' (Cl ρ b) vxs vTy)
            by (eapply clos_eval_fuel_sound; exact Happ2).

          eapply I_VecRec
            with (vA:=vA) (vP:=(VPi vP c)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VLam (Cl ρ b)) (vTy_res:=vTy); eauto.
           simpl. easy. simpl. easy.
        ** eapply I_VecRec
            with (vA:=vA) (vP:=(VLam cl0)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VLam (Cl ρ b)) (vTy_res:=vTy) (cP := cl0); eauto.
           unfold app1 in *.
           apply clos_eval_fuel_sound with (k := k). easy.
           simpl. easy.
           apply clos_eval_fuel_sound with (k := k). easy.
           
      - intro k.
        induction k; intros.
        + easy.
        + simpl in H.
          case_eq t; intros; subst.
          17:{ 
          case_eq(infer_fuel k Γ (VecRec t0 t1 t2 t3 t4 t5)); intros.
          rewrite H0 in H.
      eapply C_FromInfer.
      - (* from the synthesis boolean to declarative inference *)
        eapply infer_fuel_sound; eauto.      (* uses H0 : infer_fuel k Γ (VecRec …) = Some w *)
      - (* from the conversion boolean to declarative convertibility *)
        eapply conv_fuel_sound; eauto.
      - rewrite H0 in H. easy.
      }
        12:{
        case_eq(infer_fuel k Γ (App t0 t1)); intros.
        rewrite H0 in H.
        apply C_FromInfer with (A := A) (A' := w).
        apply infer_fuel_sound with (k := k). easy.
        apply conv_fuel_sound with (k := k). easy.
        rewrite H0 in H. easy.
      }

      11:{ 
      case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
      rewrite H0 in H.
      destruct A; try easy.
      case_eq( conv_fuel k w A); intros.
      rewrite H1 in H.
      case_eq(clos_eval_fuel k c fresh); intros.
      rewrite H2 in H.
      apply C_Lam with (vA := w) (vBodyTy := w0).
      apply evalk_sound with (k := k). easy.
      apply conv_fuel_sound with (k := k). easy.
      apply clos_eval_fuel_sound with (k := k). simpl.
      unfold fresh in *. easy.
      apply IHk. easy.
      rewrite H2 in H. easy.
      rewrite H1 in H. easy.
      rewrite H0 in H. easy.
      }

      7:{
          destruct A; try easy.
          case_eq(check_fuel k Γ t0 VStar); intros.
          rewrite H0 in H.
          case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
          rewrite H1 in H.
          case_eq(conv_fuel k w A); intros.
          rewrite H2 in H.
          case_eq(check_fuel k Γ t2 w); intros.
          rewrite H3 in H.
          case_eq(evalk k (sem_env_of_ctx Γ) t2 ); intros.
          rewrite H4 in H.
          case_eq(clos_eval_fuel k c w0); intros.
          rewrite H5 in H.
      eapply C_Pair with (va:=w0) (vBsnd:=w1) (Bcl:=c) (vA_eval := w).
      apply IHk. easy.
      apply evalk_sound with (k := k). easy.
      apply IHk. easy.
      apply evalk_sound with (k := k). easy.
      apply clos_eval_fuel_sound with (k := k). easy.
      apply IHk. easy.
      apply conv_fuel_sound with (k := k). easy.
      rewrite H5 in H. easy.
      rewrite H4 in H. easy.
      rewrite H3 in H. easy.
      rewrite H2 in H. easy.
      rewrite H1 in H. easy.
      rewrite H0 in H. easy.
      }

      9:{ case_eq( infer_fuel k Γ (Var n) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
          apply infer_fuel_sound with (k := k). easy.
          apply conv_fuel_sound with (k := k). easy.
          rewrite H0 in H. easy.
        }

      3:{ case_eq(infer_fuel k Γ (Pi t0 t1)); intros.
          + rewrite H0 in H.
            apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
       }
       
          

      2:{ destruct (infer_fuel k Γ Nat) eqn:Hinfer
        ; try (rewrite Hinfer in H; discriminate).

      eapply C_FromInfer.
      - eapply infer_fuel_sound; eauto.            (* infer Γ Nat w          *)
      - eapply conv_fuel_sound;  eauto.
      - easy.            (* conv  w       A        *)
          }

      2:{ case_eq(infer_fuel k Γ (Sigma t0 t1)); intros.
          + rewrite H0 in H.
            apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
       }

      5:{ case_eq(infer_fuel k Γ (TSnd t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      4:{ case_eq(infer_fuel k Γ (TFst t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (Vec t0 t1)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (VNil t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (VCons t0 t1 t2 t3)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      4:{ case_eq(infer_fuel k Γ (NatRec t0 t1 t2 t3)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      3:{ case_eq(infer_fuel k Γ (Succ t0)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      2:{ case_eq(infer_fuel k Γ Zero); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      case_eq(infer_fuel k Γ Star); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
            rewrite H0 in H. easy.
Qed.
