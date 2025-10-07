Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure sort.typecheck sort.soundness.

Lemma evalk_monotone: forall k k' ρ t v,
  k' >= k ->
  evalk k ρ t = Some v ->
  evalk k' ρ t = Some v
with vappk_step_mono: forall k k' vf vu r,
  k' >= k ->
  vappk k vf vu = Some r ->
  vappk k' vf vu = Some r
with vnatreck_step_mono: forall k k' vP vz vs vn r,
  k' >= k ->
  vnatreck k vP vz vs vn = Some r ->
  vnatreck k' vP vz vs vn = Some r
with vappsk_step_mono: forall k k' vf vu r,
  k' >= k ->
  vappsk k vf vu = Some r ->
  vappsk k' vf vu = Some r
with vvecreck_monotone: forall k k' vA vP vz vs vn vxs r,
  k' >= k ->
  vvecreck k vA vP vz vs vn vxs = Some r ->
  vvecreck k' vA vP vz vs vn vxs = Some r.
Proof. intro k.
       induction k; intros.
       - simpl in *. easy.
       - simpl in H0.
         case_eq t; intros.
         + subst. inversion H0.
           destruct k'. easy.
           simpl. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl. easy.
         + subst. simpl in *.
           destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy. simpl. easy.
         + subst. destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. simpl. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. 
             apply IHk with (k' := k') in H1; try lia.
             rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. 
             apply IHk with (k' := k') in H1; try lia.
             rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl. easy.
         + subst. destruct k'. easy. simpl. easy.
         + subst. 
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                apply IHk with (k' := k') in H1; try lia.
                apply IHk with (k' := k') in H2; try lia.
                simpl. rewrite H1, H2. 
                apply vappk_step_mono with (k' := k') in H0; try lia. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4.
                         apply vnatreck_step_mono with (k' := k') in H0; try lia. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                apply IHk with (k' := k') in H1; try lia.
                apply IHk with (k' := k') in H2; try lia.
                simpl. rewrite H1, H2. 
                easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             apply IHk with (k' := k') in H1; try lia.
             simpl. rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4.
                         easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0.
                         case_eq(evalk k ρ t4); intros.
                         ***** rewrite H5 in H0.
                               case_eq(evalk k ρ t5); intros.
                               ****** rewrite H6 in H0.
                                      apply IHk with (k' := k') in H1; try lia.
                                      apply IHk with (k' := k') in H2; try lia.
                                      apply IHk with (k' := k') in H3; try lia.
                                      apply IHk with (k' := k') in H4; try lia.
                                      apply IHk with (k' := k') in H5; try lia.
                                      apply IHk with (k' := k') in H6; try lia.
                                      simpl.
                                      rewrite H1, H2, H3, H4, H5, H6.
                                      apply vvecreck_monotone with (k' := k') in H0; try lia. easy.
                               ****** rewrite H6 in H0. easy.
                         ***** rewrite H5 in H0. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H. easy.
       + destruct k'. easy.
         simpl in *.
         case_eq vf; intros; subst; try easy.
         destruct c.  
         apply evalk_monotone with (k' := k') in H0; try lia. easy.
     - intro k.
       induction k; intros.
       + simpl in H0. easy.
       + destruct k'. easy.
         simpl in H0. simpl.
         case_eq vn; intros; subst; try easy.
         case_eq(vnatreck k vP vz vs w ); intros.
         * rewrite H1 in H0.
           case_eq(vappk k vs w); intros.
           ** rewrite H2 in H0.
              apply IHk with (k' := k') in H1; try lia.
              rewrite H1.
              apply vappk_step_mono with (k' := k') in H2; try lia. 
              rewrite H2. 
              apply vappk_step_mono with (k' := k') in H0; try lia. 
              easy.
           ** rewrite H2 in H0. easy.
        * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H. easy.
       + destruct k'. easy.
         simpl in *.
         case_eq vu; intros; subst; try easy.
         case_eq(vappk k vf w); intros.
         * rewrite H1 in H0. 
           apply vappk_step_mono with (k' := k') in H1; try lia.
           rewrite H1.
           apply IHk; try lia. easy.
         * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H0. easy.
       + destruct k'. easy.
         simpl in H0. simpl.
         case_eq vxs; intros; subst; try easy.
         case_eq(vvecreck k vA vP vz vs w0 w2 ); intros.
         * rewrite H1 in H0.
           apply IHk with (k' := k') in H1; try lia.
           rewrite H1.
           apply vappsk_step_mono with (k := k); try lia.
           easy.
         * rewrite H1 in H0. easy.
Qed.

Lemma clos_eval_fuel_monotone :
  forall k k' B x v,
    k' >= k ->
    clos_eval_fuel k B x = Some v ->
    clos_eval_fuel k' B x = Some v.
Proof.
   intros.
   unfold clos_eval_fuel in *. destruct k. easy.
   destruct k'. easy.
   destruct B. 
   apply evalk_monotone with (k := k); try lia.
   easy.
Qed.

Lemma conv_fuel_monotone :
  forall k k' v w,
    k' >= k ->
    conv_fuel k v w = true ->
    conv_fuel k' v w = true
with conv_neutral_fuel_monotone :
  forall k k' n n',
    k' >= k ->
    conv_neutral_fuel k n n' = true ->
    conv_neutral_fuel k' n n' = true.
Proof. intro k.
       induction k; intros.
       + easy.
       + (* k = S k *)
        destruct k' as [|k'']; [lia|].
        rename H0 into Ht.
        simpl in Ht |- *.
        destruct v; destruct w; try discriminate; cbn in *.

        * (* VStar, VStar *) exact Ht.
        * (* VNat, VNat   *) exact Ht.

        * (* VPi A B, VPi A' B' *)
          destruct (conv_fuel k v w)   eqn:HA; try discriminate.
          destruct (clos_eval_fuel k c  fresh) eqn:HB; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
          (* from Ht we know conv_fuel k v0 v1 = true *)
          apply IHk with (k' := k'') in HA; try lia.
          rewrite HA.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w1); try lia.
          apply IHk; try lia. easy. easy. easy.

        * (* VPi A B, VPi A' B' *)
          destruct (conv_fuel k v w)   eqn:HA; try discriminate.
          destruct (clos_eval_fuel k c  fresh) eqn:HB; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
          (* from Ht we know conv_fuel k v0 v1 = true *)
          apply IHk with (k' := k'') in HA; try lia.
          rewrite HA.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w1); try lia.
          apply IHk; try lia. easy. easy. easy.
        * (* VLam cl1, VLam cl2 *)
          destruct (clos_eval_fuel k c  fresh) eqn:HC; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HC'; try discriminate.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          apply IHk; try lia. easy. easy. easy.

        * (* VPair A B a b, VPair A' B' a' b' *)
          apply Bool.andb_true_iff in Ht as [HAB Hab].
          apply Bool.andb_true_iff in Hab as [Ha Hb].
          apply Bool.andb_true_iff in Hb  as [Ha' Hb'].
          apply IHk with (k' := k'') in HAB; try lia.
          apply IHk with (k' := k'') in Ha; try lia.
          apply IHk with (k' := k'') in Ha'; try lia.
          apply IHk with (k' := k'') in Hb'; try lia.
          rewrite HAB, Ha, Ha', Hb'. easy.
        * easy.

        * apply IHk; try lia. (* VZero, VZero *) exact Ht.

        * (* VNeutral n, VNeutral n' *)
          apply conv_neutral_fuel_monotone with (k := k); try lia. exact Ht.

        * (* VVec n A, VVec n' A' *)
          apply Bool.andb_true_iff in Ht as [Hn HA].
          apply IHk with (k' := k'') in Hn; try lia.
          apply IHk with (k' := k'') in HA; try lia.
          rewrite Hn, HA. easy.

        * (* VNilV A, VNilV A' *)
          eapply (IHk k''); [lia| exact Ht].

        * (* VConsV A n x xs, VConsV A' n' x' xs' *)
          apply Bool.andb_true_iff in Ht as [HA Hrest].
          apply Bool.andb_true_iff in Hrest as [Hn Htail].
          apply Bool.andb_true_iff in Htail as [Hx Hxs].
          apply IHk with (k' := k'') in HA; try lia.
          apply IHk with (k' := k'') in Hn; try lia.
          apply IHk with (k' := k'') in Hx; try lia.
          apply IHk with (k' := k'') in Hxs; try lia.
          rewrite HA, Hn, Hx, Hxs. easy.

    (* ===== neutral lemma ===== *)
    + intros k; induction k as [|k IH] using nat_ind; intros k' n n' Hge Ht.
      ++ simpl in Ht; discriminate.
      ++ destruct k' as [|k'']; [lia|].
        simpl in Ht |- *.
        destruct n; destruct n'; try discriminate; cbn in *.

        * (* NVar *) (* Nat.eqb i j = true remains true at higher fuel trivially *)
          exact Ht.

        * (* NApp *)
          apply Bool.andb_true_iff in Ht as [Hh Ha].
          apply IH with (k' := k'') in Hh; try lia.
          apply conv_fuel_monotone with (k' := k'') in Ha; try lia.
          rewrite Hh, Ha. easy.
          
        * (* NFst *)
          eapply IH; [lia| exact Ht].

        * (* NSnd *)
          eapply IH; [lia| exact Ht].

        * (* NNatRec *)
          apply Bool.andb_true_iff in Ht as [HP Htail].
          apply Bool.andb_true_iff in Htail as [Hz Htail'].
          apply Bool.andb_true_iff in Htail' as [Hs Hn].
          apply conv_fuel_monotone with (k' := k'') in HP; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hz; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hs; try lia.
          apply IH with (k' := k'') in Hn; try lia.
          rewrite HP, Hz, Hs, Hn. reflexivity.

        * (* VVecRec *)
          apply Bool.andb_true_iff in Ht as [HP Htail].
          apply Bool.andb_true_iff in Htail as [Hz Htail'].
          apply Bool.andb_true_iff in Htail' as [Hs Hn].
          apply Bool.andb_true_iff in Hn as [Hu Hn].
          apply Bool.andb_true_iff in Hn as [Hv Hn].
          apply conv_fuel_monotone with (k' := k'') in HP; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hz; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hs; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hu; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hv; try lia.
          apply IH with (k' := k'') in Hn; try lia.
          rewrite HP, Hz, Hs, Hn, Hv, Hu. reflexivity.
Qed.

Lemma clos_evalk_monotone :
  forall k k' cl v,
    k' >= k ->
    clos_evalk k cl = Some v ->
    clos_evalk k' cl = Some v.
Proof.
  intros k k' [ρ body] v Hge H; simpl in *.
  eauto using evalk_monotone.
Qed.

Theorem infer_check_fuel_monotone:
  forall k k' Γ t A, 
  k' >= k ->
  infer_fuel k Γ t = Some A -> 
  infer_fuel k' Γ t = Some A
with check_fuel_monotone:
  forall k k' Γ t A, 
  k' >= k ->
  check_fuel k Γ t A = true -> 
  check_fuel k' Γ t A = true.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H0.
         destruct t; subst.
         + destruct k'. easy. simpl. easy.
         + destruct k'. easy. simpl. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t1); intros.
           rewrite H1 in H0. 
           destruct w; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H2 in H0.
           case_eq(infer_fuel k (w :: Γ) t2); intros.
           rewrite H3 in H0. destruct w0; try easy.
           inversion H0. subst.
           simpl.
           apply IHk with (k' := k') in H1; try lia.
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia.
           rewrite H2.
           apply IHk with (k' := k') in H3; try lia.
           rewrite H3. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t1); intros.
           rewrite H1 in H0. 
           destruct w; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H2 in H0.
           case_eq(infer_fuel k (w :: Γ) t2); intros.
           rewrite H3 in H0. destruct w0; try easy.
           inversion H0. subst.
           simpl.
           apply IHk with (k' := k') in H1; try lia.
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia.
           rewrite H2.
           apply IHk with (k' := k') in H3; try lia.
           rewrite H3. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + inversion H0. 
           destruct k'. easy.
           simpl. easy.
         + case_eq(check_fuel k Γ t VNat ); intros.
           destruct k'. easy.
           simpl. rewrite H1 in H0.
           apply check_fuel_monotone with (k' := k') in H1; try lia.
           rewrite H1. easy.
           rewrite H1 in H0. easy.
         + easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t ); intros.
           rewrite H1 in H0.
           destruct w; try easy. inversion H0. subst.
           apply IHk with (k' := k') in H1; try lia.
           simpl. rewrite H1. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t ); intros.
           rewrite H1 in H0.
           destruct w; try easy. 
           case_eq(evalk k (sem_env_of_ctx Γ) (TFst t)); intros.
           rewrite H2 in H0.
           case_eq(clos_eval_fuel k c w0 ); intros.
           rewrite H3 in H0.
           inversion H0. subst.
           apply IHk with (k' := k') in H1; try lia.
           simpl. rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia.
           rewrite H2.
           apply clos_eval_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           simpl. easy.
         + easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t1); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(check_fuel k Γ t2 w); intros.
           rewrite H2 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t2); intros.
           rewrite H3 in H0.
           case_eq(clos_eval_fuel k c w0); intros.
           rewrite H4 in H0.
           inversion H0. subst.
           apply IHk with (k' := k') in H1; try lia.
           simpl. rewrite H1.
           apply check_fuel_monotone with (k' := k') in H2; try lia.
           rewrite H2.
           apply evalk_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply clos_eval_fuel_monotone with (k' := k') in H4; try lia.
           rewrite H4. easy.
           rewrite H4 in H0. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(check_fuel k Γ t1 (VPi VNat (Cl (sem_env_of_ctx Γ) Star))); intros.
           rewrite H1 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H2 in H0.
           case_eq (fn_closure_of w); intros.
           rewrite H3 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t4); intros.
           rewrite H4 in H0.
           case_eq(clos_eval_fuel k c w0 ); intros.
           rewrite H5 in H0.
           case_eq(clos_eval_fuel k c VZero); intros.
           rewrite H6 in H0.
           case_eq(check_fuel k Γ t2 w2); intros.
           rewrite H7 in H0.
           case_eq(check_fuel k Γ t4 VNat); intros.
           rewrite H8 in H0. simpl in H0. inversion H0. subst. simpl.
           apply check_fuel_monotone with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia.
           rewrite H2.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply clos_eval_fuel_monotone with (k' := k') in H5; try lia.
           rewrite H5.
           apply clos_eval_fuel_monotone with (k' := k') in H6; try lia.
           rewrite H6. 
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7.
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. easy.
           rewrite H8 in H0. easy.
           rewrite H7 in H0. easy.
           rewrite H6 in H0. easy.
           rewrite H5 in H0. easy.
           rewrite H4 in H0. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t2); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           inversion H0. subst. simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) t); intros.
           rewrite H2 in H0. inversion H0. subst. simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia.
           rewrite H2. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t1); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(check_fuel k Γ t2 VNat); intros.
           rewrite H2 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H3 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t2); intros.
           rewrite H4 in H0.
           case_eq(check_fuel k Γ t3 w); intros.
           rewrite H5 in H0.
           case_eq(check_fuel k Γ t4 (VVec w0 w)); intros.
           rewrite H6 in H0.
           simpl in H0. inversion H0. subst. simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply check_fuel_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply evalk_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply check_fuel_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply check_fuel_monotone with (k' := k') in H6; try lia. 
           rewrite H6. simpl. easy.
           rewrite H6 in H0. easy.
           rewrite H5 in H0. easy.
           rewrite H4 in H0. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
         + destruct k'. easy.
           case_eq(infer_fuel k Γ t1); intros.
           rewrite H1 in H0.
           destruct w; try easy.
           case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
           rewrite H2 in H0.
           case_eq(check_fuel k Γ t2 (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) t1) Star)))); intros.
           rewrite H3 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t2); intros.
           rewrite H4 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t5); intros.
           rewrite H5 in H0.
           case_eq(evalk k (sem_env_of_ctx Γ) t6); intros.
           rewrite H6 in H0.
           case_eq(check_fuel k Γ t5 VNat); intros.
           rewrite H7 in H0.
           case_eq(check_fuel k Γ t6 (VVec w1 w)); intros.
           rewrite H8 in H0. simpl in H0.
           case_eq w0; intros; subst; try easy.
           case_eq(clos_eval_fuel k c w1); intros.
           rewrite H9 in H0.
           destruct w3; try easy. simpl.
           
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           case_eq w0; intros; subst; try easy.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           case_eq w0; intros; subst; try easy.
           simpl.

           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           case_eq w0; intros; subst; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           rewrite H9 in H0. easy.
           
           
           case_eq(clos_eval_fuel k c w1); intros.
           rewrite H9 in H0.
           destruct w0; try easy.
           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.

           simpl.
           apply IHk with (k' := k') in H1; try lia. 
           rewrite H1.
           apply evalk_monotone with (k' := k') in H2; try lia. 
           rewrite H2.
           apply check_fuel_monotone with (k' := k') in H3; try lia.
           rewrite H3.
           apply evalk_monotone with (k' := k') in H4; try lia.
           rewrite H4.
           apply evalk_monotone with (k' := k') in H5; try lia. 
           rewrite H5.
           apply evalk_monotone with (k' := k') in H6; try lia. 
           rewrite H6.
           apply check_fuel_monotone with (k' := k') in H7; try lia.
           rewrite H7. 
           apply check_fuel_monotone with (k' := k') in H8; try lia.
           rewrite H8. simpl.
           apply clos_eval_fuel_monotone with (k' := k') in H9; try lia.
           rewrite H9.
           apply clos_eval_fuel_monotone with (k' := k') in H0; try lia. easy.
           
           rewrite H9 in H0. easy.
           rewrite H8 in H0. easy.
           rewrite H7 in H0. easy.
           rewrite H6 in H0. easy.
           rewrite H5 in H0. easy.
           rewrite H4 in H0. easy.
           rewrite H3 in H0. easy.
           rewrite H2 in H0. easy.
           rewrite H1 in H0. easy.
       - intro k.
         induction k; intros.
         + easy.
         + simpl in H0.
           destruct t; subst.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ Star); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ Nat); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (Pi t1 t2)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (Sigma t1 t2)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ Zero); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (Succ t)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq A; intros; subst; try easy.
             case_eq(check_fuel k Γ t1 VStar); intros.
             rewrite H1 in H0.
             case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
             rewrite H2 in H0.
             case_eq(conv_fuel k w0 w); intros.
             rewrite H3 in H0.
             case_eq(check_fuel k Γ t3 w0); intros.
             rewrite H4 in H0.
             case_eq(evalk k (sem_env_of_ctx Γ) t3); intros.
             rewrite H5 in H0.
             case_eq(clos_eval_fuel k c w1); intros.
             rewrite H6 in H0.
             simpl.
             apply IHk with (k' := k') in H1; try lia. 
             rewrite H1.
             apply evalk_monotone with (k' := k') in H2; try lia. 
             rewrite H2.
             apply conv_fuel_monotone with (k' := k') in H3; try lia. 
             rewrite H3.
             apply IHk with (k' := k') in H4; try lia. 
             rewrite H4.
             apply evalk_monotone with (k' := k') in H5; try lia. 
             rewrite H5.
             apply clos_eval_fuel_monotone with (k' := k') in H6; try lia. 
             rewrite H6.
             apply IHk; try lia. easy.
             rewrite H6 in H0. easy.
             rewrite H5 in H0. easy.
             rewrite H4 in H0. easy.
             rewrite H3 in H0. easy.
             rewrite H2 in H0. easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (TFst t)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (TSnd t)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (Var n)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(evalk k (sem_env_of_ctx Γ) t1); intros.
             rewrite H1 in H0.
             case_eq A; intros; subst; try easy.
             case_eq(conv_fuel k w w0); intros.
             rewrite H2 in H0.
             case_eq(clos_eval_fuel k c fresh); intros.
             rewrite H3 in H0. simpl.
             apply evalk_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H2; try lia. 
             rewrite H2.
             apply clos_eval_fuel_monotone with (k' := k') in H3; try lia. 
             rewrite H3.
             apply IHk; try lia. easy.
             rewrite H3 in H0. easy.
             rewrite H2 in H0. easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (App t1 t2)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (NatRec t1 t2 t3 t4)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (Vec t1 t2)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (VNil t)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (VCons t1 t2 t3 t4)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
           * destruct k'. easy.
             case_eq(infer_fuel k Γ (VecRec t1 t2 t3 t4 t5 t6)); intros.
             rewrite H1 in H0. simpl.
             apply infer_check_fuel_monotone with (k' := k') in H1; try lia. 
             rewrite H1.
             apply conv_fuel_monotone with (k' := k') in H0; try lia. 
             easy.
             rewrite H1 in H0. easy.
Qed.

Theorem infer_fuel_monotone:
  (forall Γ t A k k', 
     k' >= k ->
     infer_fuel k Γ t = Some A -> 
     infer_fuel k' Γ t = Some A).
Proof. intros.
       eapply infer_check_fuel_monotone with (k' := k') (k := k); try lia.
       easy.
Qed.
