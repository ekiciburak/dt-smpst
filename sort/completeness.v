Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure sort.typecheck sort.soundness sort.monotonicity.

Lemma vvecreck_other_complete :
  forall vA vP vz vs vn vxs,
    (forall vw,               vxs <> VNilV vw) ->
    (forall vw vn' va xs,     vxs <> VConsV vw vn' va xs) ->
    (forall nx : neutral,     vxs <> VNeutral nx) ->
    exists k, vvecreck k vA vP vz vs vn vxs = Some vz.
Proof.
  intros vA vP vz vs vn vxs Hnil Hcons Hneu.
  exists 1%nat. cbn.               (* unfold one fuel *)
  destruct vxs; try reflexivity.
  - (* VNilV _ *)    exfalso. eapply Hneu; reflexivity.
  - (* VConsV _ _ _ _ *) exfalso. eapply Hcons; reflexivity.
Qed.

Lemma evalk_complete:
  (* eval' *)
  (forall ρ t v, eval' ρ t v -> exists k, evalk k ρ t = Some v) /\
  (* vapp *)
  (forall f a r, vapp f a r -> exists k, vappk k f a = Some r) /\
  (* natrec *)
  (forall vP vz vs vn r, eval_natrec vP vz vs vn r -> exists k, vnatreck k vP vz vs vn = Some r) /\
  (* vapps completeness *)
  (forall f as_ r, vapps f as_ r -> exists k, vappsk k f as_ = Some r)
  /\
  (* vec recursor completeness *)
  (forall vA vP vz vs vn vxs v, eval_vecrec vA vP vz vs vn vxs v -> exists k, vvecreck k vA vP vz vs vn vxs = Some v).
Proof.
  eapply (evalsys_mutind
    (* motives *)
    (fun ρ t v           _ => exists k, evalk   k ρ t = Some v)            (* eval' *)
    (fun f a r           _ => exists k, vappk   k f a = Some r)            (* vapp *)
    (fun vP vz vs vn r   _ => exists k, vnatreck k vP vz vs vn = Some r)   (* eval_natrec *)
    (fun f as_ r         _ => exists k, vappsk  k f as_ = Some r)          (* vapps *)
    (fun vA vP vz vs vn vxs v _ => exists k, vvecreck k vA vP vz vs vn vxs = Some v)  (* eval_vecrec *)
  ); intros.
  (* ===== evalk_complete ===== *)
    + exists 1. simpl. easy.
    + exists 1. simpl. easy.

    + exists 1. simpl. rewrite e. easy.
    + exists 1. simpl. rewrite e. easy.


    + (* Pi *)
      destruct H as [kA HA].
      exists (S kA). simpl. now rewrite HA.

    + (* Sigma *)
      destruct H as [kA HA].
      exists (S kA). simpl. now rewrite HA.
      
    + exists 1. simpl. easy.

    + (* App *)
      destruct H as [kt Ht].
      destruct H0 as [ku Hu].
      destruct H1 as [ka Ha].
      set (K := S (Nat.max kt (Nat.max ku ka))).
      exists K. simpl.
      assert (K >= kt) by (unfold K; lia).
      assert (K >= ku) by (unfold K; lia).
      assert (K >= ka) by (unfold K; lia).
      
      rewrite evalk_monotone with (k := kt) (v := vt); try lia.
      rewrite evalk_monotone with (k := ku) (v := vu); try lia.
      rewrite vappk_step_mono with (k := ka) (r := v); try lia.
      easy. easy. easy. easy.

    + (* Pair *)
      destruct H as [kA HA].
      destruct H0 as [kB HB].
      destruct H1 as [ka Ha].
      destruct H2 as [kb Hb].
      set (K := S (Nat.max kA (Nat.max kB (Nat.max ka kb)))).
      exists K. simpl.
      assert (K >= kA) by (unfold K; lia).
      assert (K >= kB) by (unfold K; lia).
      assert (K >= ka) by (unfold K; lia).
      assert (K >= kb) by (unfold K; lia).

      rewrite evalk_monotone with (k := kA) (v := vA); try lia.
      rewrite evalk_monotone with (k := kB) (v := vB); try lia.
      rewrite evalk_monotone with (k := ka) (v := va); try lia.
      rewrite evalk_monotone with (k := kb) (v := vb); try lia.
      easy. easy. easy. easy. easy.

    + (* TFst Pair *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TFst Neut *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TFst Other/stuck *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp.
      (* side-conditions guarantee scrutinee isn’t Pair/Neutral, so the [match] picks [Some vp] *)
      destruct vp; try reflexivity; try (exfalso; eapply H1; reflexivity); try (exfalso; eapply H2; reflexivity).
      exfalso.
      apply(n vp1 vp2 vp3 vp4). easy.
      exfalso.
      apply(n0 n1). easy.

    + (* TSnd Pair *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TSnd Neut *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TSnd Other/stuck *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp.
      (* side-conditions guarantee scrutinee isn’t Pair/Neutral, so the [match] picks [Some vp] *)
      destruct vp; try reflexivity; try (exfalso; eapply H1; reflexivity); try (exfalso; eapply H2; reflexivity).
      exfalso.
      apply(n vp1 vp2 vp3 vp4). easy.
      exfalso.
      apply(n0 n1). easy.

    + exists 1. simpl. easy.
    
    + (* Succ *)
      destruct H as [kn Hn].
      exists (S kn). simpl in Hn. simpl. rewrite Hn. easy.

    + (* NatRec *)
      destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      destruct H3 as [kr Hr].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks (Nat.max kn kr))))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).
      assert (K >= kr) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vP); try lia.
      rewrite evalk_monotone with (k := kz) (v := vz); try lia.
      rewrite evalk_monotone with (k := ks) (v := vs); try lia.
      rewrite evalk_monotone with (k := kn) (v := vn); try lia.
      rewrite vnatreck_step_mono with (k := kr) (r := v); try lia.
      easy. easy. easy. easy. easy. easy.

    + destruct H as [k He].
      destruct H0 as [kz Hz].
      set (K := S (Nat.max k kz)).
      exists K. simpl.
      rewrite evalk_monotone with (k := k) (v := vn); try lia.
      rewrite evalk_monotone with (k := kz) (v := vA); try lia.
      easy. easy. easy.

    + destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks kn)))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vA); try lia.
      rewrite evalk_monotone with (k := kz) (v := vn); try lia.
      rewrite evalk_monotone with (k := ks) (v := vx); try lia.
      rewrite evalk_monotone with (k := kn) (v := vxs); try lia.
      easy. easy. easy. easy. easy.
    
    + destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      destruct H3 as [kr Hr].
      destruct H4 as [kv Hv].
      destruct H5 as [ku Hu].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks (Nat.max kn (Nat.max kr (Nat.max kv ku))))))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).
      assert (K >= kr) by (unfold K; lia).
      assert (K >= kv) by (unfold K; lia).
      assert (K >= ku) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vA); try lia.
      rewrite evalk_monotone with (k := kz) (v := vP); try lia.
      rewrite evalk_monotone with (k := ks) (v := vz); try lia.
      rewrite evalk_monotone with (k := kn) (v := vs); try lia.
      rewrite evalk_monotone with (k := kr) (v := vn); try lia.
      rewrite evalk_monotone with (k := kv) (v := vxs); try lia.
      rewrite vvecreck_monotone with (k := ku) (r := v); try lia.
      easy. easy. easy. easy. easy. easy. easy. easy.
      
    + (* Lam: β-step *)
      destruct H as [k He].
      exists (S k). simpl. now rewrite He.
    + (* Neutral: extend spine *)
      exists 1%nat. reflexivity.
    
    
    + (* Other: fallback *)
      exists 1%nat. simpl.
      destruct w; try easy.
      destruct c. exfalso. apply (n l t). easy.
      exfalso. apply (n0 n1). easy.

    + (* Zero *)
      exists 1%nat. reflexivity.
    + (* Succ *)
      destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      destruct H1 as [k3 Hr3].
      set (K := S (Nat.max k1 (Nat.max k2 k3))).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      assert (K >= k3) by (unfold K; lia).
      Check vnatreck_step_mono.
      rewrite vnatreck_step_mono with (k := k1) (r := vrec); try lia.
      rewrite vappk_step_mono with (k := k2) (r := v1); try lia.
      rewrite vappk_step_mono with (k := k3) (r := v); try lia.
      easy. easy. easy. easy.
    + (* Neutral *)
      exists 1%nat. reflexivity.
    + (* Other/stuck *)
      exists 1%nat. simpl.
      destruct vn; try easy. 
      exfalso. apply (n vn). easy.
      exfalso. apply (n1 n2). easy.
    + exists 1%nat. reflexivity.
    + destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      set (K := S (Nat.max k1 k2)).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      rewrite vappk_step_mono with (k := k1) (r := r); try lia.
      rewrite vappsk_step_mono with (k := k2) (r := res); try lia.
      easy. easy. easy.
    + exists 1%nat. reflexivity.
    + destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      set (K := S (Nat.max k1 k2)).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      rewrite vvecreck_monotone with (k := k1) (r := vrec); try lia.
      rewrite vappsk_step_mono with (k := k2) (r := v); try lia.
      easy. easy. easy.
    + exists 1%nat. simpl. reflexivity.
    + apply vvecreck_other_complete; easy.
Qed.

Corollary vappk_complete: forall f a r, 
  vapp f a r -> exists k, vappk k f a = Some r.
Proof. intros. 
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Hb. easy. 
Qed.

Corollary vnatreck_complete: forall vP vz vs vn r, 
  eval_natrec vP vz vs vn r -> exists k, vnatreck k vP vz vs vn = Some r.
Proof. intros. 
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Hc. easy. 
Qed.

Corollary evalk_complete_: forall ρ t v, 
  eval' ρ t v -> exists k, evalk k ρ t = Some v.
Proof. intros.
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Ha. easy. 
Qed.

(* A convenient equivalence to use in tests and proofs *)
Corollary evalk_eval'_iff :
  forall ρ t v, (exists k, evalk k ρ t = Some v) <-> eval' ρ t v.
Proof.
  split; [intros [k Hk]; eapply evalk_sound; eauto|].
  intros He. 
  specialize(evalk_complete); intros (Ha, (Hb, Hc)).
  apply Ha. easy.
Qed.

Lemma clos_eval_fuel_complete :
  forall B x v,
    clos_eval' B x v ->
    exists K, forall k, k >= K -> clos_eval_fuel k B x = Some v.
Proof.
  intros [ρ t] x v H; cbn in *.
  destruct evalk_complete as (Ha,(Hb,Hc)).
  destruct (Ha (env_cons x ρ) t v H) as [K HK].
  exists (S K). intros.
  unfold clos_eval_fuel.
  destruct k. 
  inversion H0. subst. simpl in HK.
  apply evalk_monotone with (k := K); try lia.
  easy.
Qed.

Lemma clos_evalk_complete :
  forall cl v, clos_eval' cl fresh v -> exists k, clos_evalk k cl = Some v.
Proof.
  intros [ρ body] v H; simpl in *.
  now eapply evalk_complete in H.
Qed.

Lemma conv_complete :
  (forall v w, conv v w -> exists k, conv_fuel k v w = true) /\
  (forall B B', conv_clo B B' -> exists k v v', clos_eval_fuel k B  fresh = Some v /\ clos_eval_fuel k B' fresh = Some v' /\ conv_fuel k v v' = true).
Proof.
  apply (conv_mutind
    (* P: depends on the derivation (3rd arg). *)
    (fun v w _ =>
       exists k, conv_fuel k v w = true)
    (* Q: ***also*** depends on the derivation h *)
    (fun B B' h =>
       exists k, exists v v',
         clos_eval_fuel k B  fresh = Some v /\
         clos_eval_fuel k B' fresh = Some v' /\
         conv_fuel k v v' = true)); intros.
   10:{
     destruct H as (kA, HA).
     destruct H0 as (kB, HB).
     exists (S (S (Nat.max kA kB))).
     simpl.
     destruct kA. easy.
     rewrite conv_neutral_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. simpl in HA. easy.
     }
     9:{ exists 2. simpl. apply Nat.eqb_refl. }
     9:{ destruct H as (k, H).
         destruct k. easy.
         exists (S (S k)). simpl.
         simpl in H. easy.
     }
     15:{ intros.
          destruct H as (k3, H).

          destruct (clos_eval_fuel_complete B  fresh v  c) as [k1 HK1].
          destruct (clos_eval_fuel_complete B' fresh v' c0) as [k2 HK2].

          (* pick a large enough fuel *)
          set (K := Nat.max k3 (Nat.max k1 k2)).
          exists K, v, v'. repeat split.

          rewrite clos_eval_fuel_monotone with (k := k1) (v := v); try lia.
          easy. apply HK1. lia. apply HK2. lia.
          rewrite conv_fuel_monotone with (k := k3); try lia. easy.
     }
   - exists 1. easy.
   - exists 1. easy.
   - destruct H as (kA, HA).
     destruct H0 as (kB, (v1, (v2, (Hb1, (Hb2, Hc))))).
     exists (S (Nat.max kA kB)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v1); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v2); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, HA).
     destruct H0 as (kB, (v1, (v2, (Hb1, (Hb2, Hc))))).
     exists (S (Nat.max kA kB)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v1); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v2); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, (v1, (v2, (Ha1, (Ha2,Ha3))))).
     exists (S kA). simpl.
     rewrite Ha1, Ha2. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     exists (S (Nat.max kA (Nat.max ka (Nat.max kb kc)))).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     rewrite conv_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - exists 1. easy.
   - destruct H as (k, H).
     exists (S k). simpl. easy.
   - destruct H as (k, H).
     destruct k. easy.
     exists (S (S k)). simpl. simpl in H. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     destruct kc. easy.
     exists (S (S (Nat.max kA (Nat.max ka (Nat.max kb kc))))). simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     simpl. simpl in Hc.
     rewrite conv_neutral_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     exists (S (Nat.max kA ka)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     easy. easy.
   - destruct H as (k, H).
     exists (S k). simpl. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     exists (S ((Nat.max kA (Nat.max ka (Nat.max kb kc))))). simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     rewrite conv_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - destruct H as (k1, HA).
     destruct H0 as (k2, HP).
     destruct H1 as (k3, Hz).
     destruct H2 as (k4, Hs).
     destruct H3 as (k5, Hn).
     destruct H4 as (k6, Hnx).
    
     destruct k6. easy.
     exists (S (S (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 k6))))))). simpl.
     rewrite conv_fuel_monotone with (k := k1); try lia.
     rewrite conv_fuel_monotone with (k := k2); try lia.
     rewrite conv_fuel_monotone with (k := k3); try lia.
     rewrite conv_fuel_monotone with (k := k4); try lia.
     rewrite conv_fuel_monotone with (k := k5); try lia.
     rewrite conv_neutral_fuel_monotone with (k := k6); try lia.
     simpl in Hnx. easy. easy. easy. easy. easy. easy.
Qed.

Corollary conv_complete_conv: forall v w, conv v w -> exists k, conv_fuel k v w = true.
Proof. destruct conv_complete as [H _]. exact H. Qed.

Corollary conv_complete_clo :
  forall B B',
    conv_clo B B' ->
    exists k v v',
      clos_eval_fuel k B  fresh = Some v /\
      clos_eval_fuel k B' fresh = Some v' /\
      conv_fuel k v v' = true.
Proof. destruct conv_complete as [_ H]. exact H. Qed.

Lemma max_ge_s_k5 :
  forall k k0 k1 k2 k3 k4 k5,
    Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2
      (match Nat.max k4 (S k5) with
       | 0 => S k3
       | S m' => S (Nat.max k3 m')
       end)))) >= S k5.
Proof.
  intros k k0 k1 k2 k3 k4 k5.
  set (n := Nat.max k4 (S k5)).
  assert (Hn : n >= S k5) by (unfold n; apply Nat.le_max_r).
  destruct n as [|m'] eqn:En.
  - (* impossible: n = 0 but n >= S k5 *)
    simpl in Hn; lia.
  - (* n = S m' *)
    simpl.
    lia.
Qed.

Lemma max_ge_k4 :
  forall k k0 k1 k2 k3 k4 k5,
    Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2
      (match Nat.max k4 (S k5) with
       | 0 => S k3
       | S m' => S (Nat.max k3 m')
       end)))) >= k4.
Proof.
  intros k k0 k1 k2 k3 k4 k5.
  set (n := Nat.max k4 (S k5)).
  assert (Hn : n >= k4) by (unfold n; apply Nat.le_max_l).

  destruct n as [|m'] eqn:En.
  - (* n = 0 *)
    simpl.                        (* match yields S k3 *)
    repeat (apply Nat.le_trans with (m := Nat.max _ _); try apply Nat.le_max_l).
    apply Nat.le_trans with (m := S k3).
    + lia.
    + (* S k3 >= k4 (but here n = 0 so k4 = 0) *)
      simpl in Hn; lia.
  - (* n = S m' *)
    simpl. lia.
Qed.

Lemma max_ge_s_k2 :
  forall k k1 k2 k3,
    Nat.max k (Nat.max k1
      (match k3 with
       | 0 => S k2
       | S m' => S (Nat.max k2 m')
       end)) >= S k2.
Proof.
  intros k k1 k2 k3.
  destruct k3 as [| m']; simpl.
  - lia.
  - lia.
Qed.

Lemma max_ge_k3 :
  forall k k1 k2 k3,
    Nat.max k (Nat.max k1
      (match k3 with
       | 0 => S k2
       | S m' => S (Nat.max k2 m')
       end)) >= k3.
Proof.
  intros k k1 k2 k3.
  destruct k3 as [| m']; simpl.
  - lia.
  - lia.
Qed.

Theorem infer_fuel_complete :
  (forall Γ t A, infer Γ t A -> exists k, infer_fuel k Γ t = Some A) /\
  (forall Γ t A, check Γ t A -> exists k, check_fuel k Γ t A = true).
Proof.
  eapply typing_rect; intros.
  - exists 1. simpl. easy.
  - exists 1. simpl. easy.
  - exists 1. simpl. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    exists (S (Nat.max k (Nat.max k0 k1))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite infer_fuel_monotone with (k := k0) (A := VStar); try lia.
    easy.
    easy. easy. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    exists (S (Nat.max k (Nat.max k0 k1))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite infer_fuel_monotone with (k := k0) (A := VStar); try lia.
    easy.
    easy. easy. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c0.
    destruct c0 as (k2, c0).

    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (S k2))))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vu); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := (VPi A (Cl l t0))); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := A); try lia.
    simpl.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vB); try lia.
    easy. unfold clos_eval_fuel. easy.
    easy. easy. easy.
  - destruct H as (k, H).
    exists (S k). simpl.
    rewrite H. easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c.
    destruct c as (k2, c).
    exists (S (Nat.max k (Nat.max k1 (S k2)))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := (VSigma A (Cl l t))); try lia.
    rewrite evalk_monotone with (k := k1) (v := vfst); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vB); try lia.
    easy. easy. easy. easy.
  - exists 1. easy.
  - destruct H as (k, H).
    exists (S k). simpl. rewrite H. easy.
  - destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H as (k, H).
    unfold clos_eval' in *.
    destruct cP.
    apply evalk_complete in e.
    destruct e as (k2, e).
    apply evalk_complete in c0.
    destruct c0 as (k3, c0).
    apply evalk_complete in e1.
    destruct e1 as (k4, e1).
    apply evalk_complete in c3.
    destruct c3 as (k5, c3).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max (S k3) (Nat.max k4 (S k5)))))))). simpl.
    rewrite check_fuel_monotone with (k := k) (A := (VPi VNat (Cl (sem_env_of_ctx Γ) Star))); try lia.
    rewrite evalk_monotone with (k := k2) (v := vP); try lia.
    rewrite e0.
    rewrite evalk_monotone with (k := k4) (v := vn); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k5) (v := vTy); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k3) (v := vP0); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := vP0); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := VNat); try lia.
    simpl. easy. easy. easy.
    destruct (Nat.max k4 (S k5)); lia. simpl. easy.
    apply max_ge_s_k5. simpl. easy.
    apply max_ge_k4. easy. easy. easy.
  - destruct H as (k, H).
    exists (S k). simpl. rewrite H.
    easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    exists (S (Nat.max k k1)). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    easy. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H2 as (k2, H2).
    apply evalk_complete in e, e0.
    destruct e as (k3, e).
    destruct e0 as (k4, e0).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 k4)))))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := VNat); try lia.
    rewrite evalk_monotone with (k := k3) (v := vA); try lia.
    rewrite evalk_monotone with (k := k4) (v := vn); try lia.
    rewrite check_fuel_monotone with (k := k2) (A := (VVec vn vA)); try lia.
    rewrite check_fuel_monotone with (k := k1) (A :=vA); try lia. 
    simpl. easy. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H2 as (k2, H2).
    apply evalk_complete in e, e0, e1, e2.
    destruct e as (k3, e).
    destruct e0 as (k4, e0).
    destruct e1 as (k5, e1).
    destruct e2 as (k6, e2).
    unfold clos_eval' in *.
    destruct cP, c2.
    apply evalk_complete in c3, c4.
    destruct c3 as (k7, c3).
    destruct c4 as (k8, c4).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 (Nat.max k6 (Nat.max (S k7) (S k8))))))))))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite evalk_monotone with (k := k3) (v := vA); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) A) Star)))); try lia.
    rewrite evalk_monotone with (k := k4) (v := vP); try lia.
    rewrite evalk_monotone with (k := k5) (v := vn); try lia.
    rewrite evalk_monotone with (k := k6) (v := vxs); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := VNat); try lia.
    rewrite check_fuel_monotone with (k := k2) (A := (VVec vn vA)); try lia.
    simpl.
    destruct vP; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k7) (v := vPn); try lia. 
    destruct vPn; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. 
    simpl in e4. inversion e4. easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. simpl in e4. inversion e4. easy.
    simpl. simpl in e3. inversion e3. easy.
    rewrite clos_eval_fuel_monotone with (k := S k7) (v := vPn); try lia. 
    destruct vPn; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. 
    simpl in e4. inversion e4. easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. simpl in e4. inversion e4. easy.
    simpl. simpl in e3. inversion e3. easy.
    easy. easy. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c0.
    destruct c0 as (k2, c0).
    apply conv_complete_conv in c.
    destruct c as (k3, c).
    exists (S (Nat.max k (Nat.max k1 (Nat.max (S k2) k3)))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite conv_fuel_monotone with (k := k3); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vBodyTy); try lia.
    rewrite check_fuel_monotone with (k := k) (A := vBodyTy); try lia.
    easy.
    apply max_ge_s_k2. simpl. easy.
    apply max_ge_k3. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    apply evalk_complete in e, e0.
    destruct e as (k2, e).
    destruct e0 as (k3, e0).
    apply conv_complete_conv in c3.
    destruct c3 as (k4, c3).
    unfold clos_eval' in *.
    destruct Bcl.
    apply evalk_complete in c1.
    destruct c1 as (k5, c1).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (S k5)))))))).
    simpl.
    rewrite check_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite evalk_monotone with (k := k2) (v := vA_eval); try lia.
    rewrite conv_fuel_monotone with (k := k4); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := vA_eval); try lia.
    rewrite evalk_monotone with (k := k3) (v := va); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k5) (v := vBsnd); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := vBsnd); try lia.
    easy. simpl. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    inversion i.
    + subst. exists 2. simpl. rewrite H0. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
  - destruct H as (k, H).
    inversion i.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H2.
      destruct H2 as (k1, H2).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      unfold clos_eval' in *.
      destruct B. 
      apply evalk_complete in H3.
      destruct H3 as (k3, H3).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (S k3))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      unfold clos_eval' in *.
      destruct B. 
      apply evalk_complete in H2.
      destruct H2 as (k3, H2).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (S k3))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VNat); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VNat); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1, H6.
      destruct H1 as (k1, H1).
      destruct H6 as (k2, H6).
      apply conv_complete_conv in c.
      destruct c as (k3, c).
      unfold clos_eval' in *.
      destruct cP.
      apply evalk_complete in H3, H7.
      destruct H3 as (k4, H3).
      destruct H7 as (k5, H7).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max (S k4) (S k5))))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k3); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := (VVec VZero vA)); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H2, H3.
      destruct H2 as (k1, H2).
      destruct H3 as (k2, H3).
      apply conv_complete_conv in c.
      destruct c as (k3, c).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 k3)))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := (VVec (VSucc vn) vA)); try lia.
      rewrite conv_fuel_monotone with (k := k3); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1, H3, H5, H7.
      destruct H1 as (k1, H1).
      destruct H3 as (k2, H3).
      destruct H5 as (k3, H5).
      destruct H7 as (k4, H7).
      apply conv_complete_conv in c.
      destruct c as (k5, c).
      unfold clos_eval' in *.
      destruct cP, c2.
      apply evalk_complete in H9, H11.
      destruct H9 as (k6, H9).
      destruct H11 as (k7, H11).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 (Nat.max (S k6) (S k7))))))))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k5); try lia. easy. easy.
Qed.
