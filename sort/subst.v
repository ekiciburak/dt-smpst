Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.sort.

(* Proper de Bruijn substitution with lifting *)
Fixpoint lift (d k : nat) (t : term) : term :=
  match t with
  | Var n => 
      if Nat.ltb n k then Var n 
      else Var (n + d)
  | Lam A b => Lam (lift d k A) (lift d (S k) b)
  | Pi A B => Pi (lift d k A) (lift d (S k) B)
  | Sigma A B => Sigma (lift d k A) (lift d (S k) B)
  | Succ n => Succ (lift d k n)
  | Pair A B a b => Pair (lift d k A) (lift d k B) (lift d k a) (lift d k b)
  | Fst p => Fst (lift d k p)
  | Snd p => Snd (lift d k p)
  | App f a => App (lift d k f) (lift d k a)
  | NatRec P z s n =>
      NatRec (lift d (S k) P)
             (lift d k z)
             (lift d k s)
             (lift d k n)
(* | NatRec P z s n =>
       NatRec (lift d (S k) P) 
              (lift d k z) 
              (lift d (S (S k)) s) 
              (lift d k n) *)
  | _ => t
  end.

(* === Substitution (capture-avoiding) === *)
Fixpoint subst (j : nat) (s t : term) : term :=
  match t with
  | Star => Star
  | Pi A B => Pi (subst j s A) (subst (S j) (lift 1 0 s) B)
  | Sigma A B => Sigma (subst j s A) (subst (S j) (lift 1 0 s) B)
  | Nat => Nat
  | Zero => Zero
  | Succ u => Succ (subst j s u)
  | Var x =>
      match Nat.compare x j with
      | Eq => s
      | Gt => Var (x - 1)       (* one binder removed *)
      | Lt => Var x
      end
  | Pair A B a b =>
      Pair (subst j s A)  (* substitute in type of first component *)
           (subst j s B)  (* substitute in type of second component under new binder *)
           (subst j s a)  (* substitute in first component *)
           (subst j s b)  (* substitute in second component *)

  | Fst p => Fst (subst j s p)
  | Snd p => Snd (subst j s p)

  | Lam A t1  => Lam (subst j s A) (subst (S j) (lift 1 0 s) t1)
  | App t1 t2 => App (subst j s t1) (subst j s t2)
  | NatRec P z step n =>
      NatRec (subst (S j) (lift 1 0 s) P)
             (subst j s z)
             (subst j s step)
             (subst j s n)

(*   | NatRec P z step n0 =>
      NatRec (subst (S j) (lift 1 0 s) P)
             (subst j s z)
             (subst (S (S j)) (lift 2 0 s) step)
             (subst j s n0) *)
  end.


  (* Lift over lift composition *)
Lemma lift_lift : forall t n m k, lift n k (lift m k t) = lift (n + m) k t.
Proof.
  intro t.
  induction t;  intros.
  - simpl. easy.
  - simpl. easy.
  - simpl. rewrite IHt1, IHt2; auto.
  - simpl. rewrite IHt1, IHt2; auto.
  - simpl. easy.
  - simpl. rewrite IHt. easy.
  - simpl. rewrite IHt1, IHt2, IHt3, IHt4; auto.
  - simpl. rewrite IHt. easy.
  - simpl. rewrite IHt. easy.
  - simpl. 
    case_eq(n <? k); intros.
    + simpl. rewrite H. easy.
    + simpl.
      assert(n + m <? k = false).
      { apply Nat.leb_gt.
        apply Nat.leb_gt in H. lia.
      }
      rewrite H0.
      assert((n + m + n0) = (n + (n0 + m))) by lia.
      rewrite H1. easy.
  - simpl. rewrite IHt1, IHt2; auto.
  - simpl. rewrite IHt1, IHt2; auto.
  - simpl. rewrite IHt1, IHt2, IHt3, IHt4; auto.
Qed.

(** Lift identity *)
Lemma lift_0 : forall t k, lift 0 k t = t.
Proof.
  intro t.
  induction t; intros; simpl;
  try(reflexivity);
  try (rewrite IHt1, IHt2, IHt3, IHt4; auto);
  try (rewrite IHt1, IHt2; auto);
  try (rewrite IHt; auto).
  - destruct (Nat.ltb n k); try easy.
    assert(n + 0 = n) by lia.
    rewrite H. easy.
Qed.

Lemma lift_commute: forall t d e k, lift d (e + k) (lift e k t) = lift e k (lift d k t).
Proof.
  induction t; intros d e k; simpl.
  - (* Star *) reflexivity.
  - (* Nat *) reflexivity.
  - (* Pi A B *)
    rewrite IHt1.
    specialize (IHt2 d e (S k)). 
    f_equal.
    assert((S (e + k)) = (e + S k)) by lia. rewrite H.
    rewrite IHt2. easy.
  - (* Sigma A B *)
    rewrite IHt1.
    specialize (IHt2 d e (S k)).
    f_equal.
    assert((S (e + k)) = (e + S k)) by lia. rewrite H.
    rewrite IHt2. easy.
  - (* Zero *) reflexivity.
  - (* Succ n *)
    rewrite IHt. reflexivity.
  - (* Pair A B a b *)
    rewrite IHt1, IHt2, IHt3, IHt4. reflexivity.
  - (* Fst p *)
    rewrite IHt. reflexivity.
  - (* Snd p *)
    rewrite IHt. reflexivity.
  - (* Var n *)
    simpl.
    destruct (Nat.ltb n k) eqn:Hnk.
    + (* n <= k *)
      (* inner lift leaves Var n; then outer lifts at (e+k) leaves Var n as well.
         RHS: lift d k (Var n) = Var n, then lift e k leaves Var n. *)
(*       apply Nat.leb_le in Hnk. *)
      simpl. rewrite Hnk.
      apply Nat.leb_le in Hnk.
      assert( n <? e + k = true).
      { apply Nat.leb_le. lia. }
      rewrite H. easy.
    + (* n > k *)
      apply Nat.leb_gt in Hnk. (* gives k < n *)
      simpl.
      (* LHS = lift d (e+k) (Var (n+e)).  Since n > k we know n+e <=? e+k is false. *)
      destruct (Nat.ltb (n + e) (e + k)) eqn:Hne.
      * apply Nat.leb_le in Hne. lia.  (* n+e <= e+k -> n <= k contradicts k < n *)
      * simpl. (* so (n+e <=? e+k) = false, LHS = Var (n+e+d) *)
        (* RHS: lift d k (Var n) = Var (n + d) because n > k; then lift e k on that:
           (n + d) <=? k must be false (else contradicts n>k), so RHS = Var (n + d + e). *)
        destruct (Nat.ltb (n + d) k) eqn:Hndk.
        -- apply Nat.leb_le in Hndk. lia. (* n + d <= k contradicts k < n *)
        -- (* both outer-if branches are false, compare results *)
           simpl.
           (* Var (n + e + d) = Var (n + d + e) by commutativity of + *)
           rewrite <- Nat.add_assoc.
           rewrite (Nat.add_comm e d).
           rewrite Nat.add_assoc.
           reflexivity.
  - (* Lam A b *)
    rewrite IHt1.
    specialize (IHt2 d e (S k)).
    f_equal.
    assert((S (e + k)) = (e + S k)) by lia. rewrite H.
    rewrite IHt2. easy.
  - (* App f a *)
    rewrite IHt1, IHt2. reflexivity.
  - (* NatRec P z s n *)
    rewrite IHt2, IHt4.
    f_equal.
    specialize (IHt1 d e (S k)).
    simpl in IHt1.
    assert((S (e + k)) = (e + S k)) by lia. rewrite H.
    rewrite IHt1.
    easy.
(*     specialize (IHt3 d e (S (S k))).
    simpl in IHt3.
    assert(S(S (e + k)) = (e + S (S k))) by lia. rewrite H. *)
    rewrite IHt3.
    easy.
Qed.

Lemma lift_commute_general : forall t d e k m, m <= k -> lift d (e + k) (lift e m t) = lift e m (lift d k t).
Proof. intro t.
       induction t; intros.
       10:{
    simpl.
    case_eq(n <? m); case_eq(n <? k); intros.
    + simpl.
      rewrite H1. 
      assert(n <? e + k = true).
      { apply Nat.ltb_lt in H0.
        apply Nat.ltb_lt. lia.
      } rewrite H2. easy.
    + simpl.
      case_eq(n <? e + k); case_eq(n + d <? m); intros.
      ++ apply Nat.ltb_lt in H1.
         apply Nat.leb_gt in H0.
         lia.
      ++ apply Nat.ltb_lt in H1.
         apply Nat.leb_gt in H0.
         lia.
      ++ apply Nat.ltb_lt in H1.
         apply Nat.leb_gt in H0.
         lia.
      ++ apply Nat.ltb_lt in H1.
         apply Nat.leb_gt in H0.
         lia.
    + simpl. rewrite H1.
      assert(n + e <? e + k = true).
      { apply Nat.ltb_lt.
        apply Nat.ltb_lt in H0. lia.
      } rewrite H2. easy.
    + apply Nat.leb_gt in H0.
      apply Nat.leb_gt in H1.
      simpl.
      case_eq(n + e <? e + k); case_eq (n + d <? m); intros.
      ++ apply Nat.ltb_lt in H2.
         apply Nat.ltb_lt in H3. lia.
      ++ apply Nat.ltb_lt in H3. lia.
      ++ apply Nat.ltb_lt in H2. lia.
      ++ assert((n + e + d) = (n + d + e)) by lia.
         rewrite H4. easy.
   }
   - simpl. easy.
   - simpl. easy.
   - simpl. rewrite IHt1.
     specialize(IHt2 d e (S k) (S m)).
     assert((e + S k) = S (e + k)) by lia.
     rewrite <- H0. rewrite IHt2. easy.
     lia. easy.
   - simpl. rewrite IHt1.
     specialize(IHt2 d e (S k) (S m)).
     assert((e + S k) = S (e + k)) by lia.
     rewrite <- H0. rewrite IHt2. easy.
     lia. easy.
   - simpl. easy.
   - simpl. rewrite IHt. easy. easy.
   - simpl. rewrite IHt1, IHt2, IHt3, IHt4. easy. easy. easy. easy. easy.
   - simpl. rewrite IHt. easy. easy.
   - simpl. rewrite IHt. easy. easy.
   - simpl. rewrite IHt1.
     specialize(IHt2 d e (S k) (S m)).
     assert((e + S k) = S (e + k)) by lia.
     rewrite <- H0. rewrite IHt2. easy.
     lia. easy.
   - simpl. rewrite IHt1. rewrite IHt2. easy.
     easy. easy.
   - simpl. rewrite IHt2, IHt3, IHt4.
     specialize(IHt1 d e (S k) (S m)).
     assert((e + S k) = S (e + k)) by lia.
     rewrite <- H0. rewrite IHt1. easy.
     lia. easy. easy. easy.
Qed.

Lemma subst_lift_simple : forall t s j, subst j s (lift 1 j t) = t.
Proof.
  intro t.
  induction t; intros s j; simpl.
  - (* Star *) reflexivity.
  - easy.
  - (* Pi *) 
    rewrite IHt1, IHt2. reflexivity.
  - (* Sigma *)
    rewrite IHt1, IHt2. reflexivity.
  - (* Nat *) reflexivity.
  - (* Succ *)
    rewrite IHt. reflexivity.
  - (* Pair *)
    rewrite IHt1, IHt2, IHt3, IHt4. reflexivity.
  - (* Fst *) rewrite IHt; reflexivity.
  - (* Snd *) rewrite IHt; reflexivity.
  - (* Var x *)
    case (Nat.compare_spec n j) as [H | H | H].
    + (* x = j *)
      simpl. subst.
      assert(j <? j = false).
      { apply Nat.leb_gt. lia. }
       rewrite H.
      simpl. 
      assert(j + 1 ?= j = Gt).
      { apply Nat.compare_gt_iff. lia. }
      rewrite H0.
      assert((j + 1 - 1) = j) by lia.
      rewrite H1. easy.
    + (* x < j *)
      simpl.
      assert(n <? j = true).
      { apply Nat.ltb_lt. lia. }
      rewrite H0. simpl.
      assert(n ?= j = Lt).
      { apply Nat.compare_lt_iff. lia. }
      rewrite H1. easy.
    + (* x > j *)
      simpl.
      assert(n <? j = false).
      { apply Nat.ltb_ge. lia. }
      rewrite H0. simpl.
      assert(n + 1 ?= j = Gt).
      { apply Nat.compare_gt_iff. lia. }
      rewrite H1.
      assert((n + 1 - 1) = n) by lia.
      rewrite H2. easy.
  - (* Lam *)
    rewrite IHt1, IHt2. reflexivity.
  - (* App *)
    rewrite IHt1, IHt2. reflexivity.
  - (* NatRec *)
    rewrite IHt2, IHt4. simpl.
    specialize(IHt1 (lift 1 0 s) (S j)).
    rewrite IHt1.
(*     specialize(IHt3 (lift 2 0 s) (S (S j))).
    assert((j + 2) = S (S j)) by lia.
    rewrite H. *)
    rewrite IHt3. easy.
Qed.

Lemma lift_after_subst : forall t s j d k, k <= j -> lift d k (subst j s t) = subst (j + d) (lift d k s) (lift d k t).
Proof. intro t.
       induction t; intros.
       10:{
       simpl.
       case_eq(n ?= j);  case_eq(n <? k); intros.
       + apply Nat.compare_eq in H1. subst.
         rewrite Nat.ltb_lt in H0. lia.
       + simpl.
         apply Nat.compare_eq in H1. subst.
         rewrite Nat.ltb_ge in H0.
         assert(j + d ?= j + d = Eq).
         { apply Nat.compare_refl. }
         rewrite H1. easy.
       + simpl. rewrite H0.
         apply Nat.compare_lt_iff in H1.
         rewrite Nat.ltb_lt in H0.
         assert(n ?= j + d = Lt).
         { apply Nat.compare_lt_iff. lia. }
         rewrite H2. easy.
       + simpl. rewrite H0.
         apply Nat.compare_lt_iff in H1.
         assert(n + d ?= j + d = Lt).
         { apply Nat.compare_lt_iff. lia. }
         rewrite H2. easy.
       + simpl.
         apply Nat.ltb_lt in H0.
         apply Nat.compare_gt_iff in H1.
         lia.
       + simpl.
         apply Nat.compare_gt_iff in H1.
         rewrite Nat.ltb_ge in H0.
         assert(n - 1 <? k = false).
         { rewrite Nat.ltb_ge. lia. }
         rewrite H2.
         assert(n + d ?= j + d = Gt).
         { apply Nat.compare_gt_iff. lia. }
         rewrite H3.
         assert((n - 1 + d) = (n + d - 1)) by lia.
         rewrite H4. easy.
        }
       simpl. easy.
       simpl. easy.
       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       specialize(lift_commute_general s d 1 k 0); intro Ha.
       simpl in Ha. rewrite Ha. easy.
       lia. lia. easy.

       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       specialize(lift_commute_general s d 1 k 0); intro Ha.
       simpl in Ha. rewrite Ha. easy.
       lia. lia. easy.
       
       simpl. easy.
       simpl. rewrite IHt. easy. easy.
       
       simpl. rewrite IHt1, IHt2, IHt3, IHt4.
       f_equal. f_equal.
       easy. easy. easy. easy.

       simpl. rewrite IHt. easy. easy.
       simpl. rewrite IHt. easy. easy.

       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       specialize(lift_commute_general s d 1 k 0); intro Ha.
       simpl in Ha. rewrite Ha. easy.
       lia. lia. easy.

       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal. easy. easy.

       simpl. rewrite IHt1, IHt2, IHt3, IHt4.
       f_equal. f_equal.
       specialize(lift_commute_general s d 1 k 0); intro Ha.
       simpl in Ha. rewrite Ha. easy.
       lia. easy. easy. easy. lia.
Qed.

Lemma subst_subst: forall t s u j k, j <= k -> subst k u (subst j s t) = subst j (subst k u s) (subst (S k) (lift 1 j u) t).
Proof. intro t.
       induction t; intros.
       10:{
       simpl.
       case_eq(n ?= j); case_eq(n ?= S k); intros.
       - simpl.
         apply Nat.compare_eq_iff in H1, H0.
         subst. lia.
       - apply Nat.compare_eq_iff in H1. subst.
         simpl.
         rewrite Nat.compare_refl. easy.
       - apply Nat.compare_eq_iff in H1. subst.
         apply Nat.compare_gt_iff in H0. lia.
       - apply Nat.compare_eq_iff in H0. subst.
         apply Nat.compare_lt_iff in H1. lia.
       - apply Nat.compare_lt_iff in H0, H1.
         simpl.
         assert(n ?= k = Lt).
         { apply Nat.compare_lt_iff. lia. }
         rewrite H2.
         assert(n ?= j = Lt).
         { apply Nat.compare_lt_iff. lia. }
         rewrite H3. easy.
       - apply Nat.compare_gt_iff in H0. 
         apply Nat.compare_lt_iff in H1. lia.
       - apply Nat.compare_eq_iff in H0. subst. 
         apply Nat.compare_gt_iff in H1.
         simpl. 
         assert(k - 0 ?= k = Eq).
         { apply Nat.compare_eq_iff. lia. }
         rewrite H0. simpl.
         rewrite subst_lift_simple. easy.
       - apply Nat.compare_lt_iff in H0.
         apply Nat.compare_gt_iff in H1.
         simpl.
         assert(n - 1 ?= k = Lt).
         { apply Nat.compare_lt_iff. lia. }
         rewrite H2.
         assert(n ?= j = Gt).
         { apply Nat.compare_gt_iff. lia. }
         rewrite H3. easy.
       - apply Nat.compare_gt_iff in H0, H1.
         simpl.
         assert(n - 1 ?= k = Gt).
         { apply Nat.compare_gt_iff. lia. }
         rewrite H2.
         assert(n - 1 ?= j = Gt).
         { apply Nat.compare_gt_iff. lia. }
         rewrite H3. easy.
       }
       simpl. easy.
       simpl. easy.
       
       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       rewrite lift_after_subst.
       assert((k + 1) = S k) by lia.
       rewrite H0. easy.
       lia.
       f_equal.
       specialize (lift_commute_general u 1 1 j 0); intro Ha.
       simpl in Ha. rewrite Ha. easy. lia. lia. easy.
       
       
       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       rewrite lift_after_subst.
       assert((k + 1) = S k) by lia.
       rewrite H0. easy.
       lia.
       f_equal.
       specialize (lift_commute_general u 1 1 j 0); intro Ha.
       simpl in Ha. rewrite Ha. easy. lia. lia. easy.
       
       simpl. easy.
       simpl. rewrite IHt. easy. easy.
       
       simpl. rewrite IHt1, IHt2, IHt3, IHt4. easy. easy. easy. easy. easy.
       simpl. rewrite IHt. easy. easy.
       simpl. rewrite IHt. easy. easy.

       simpl. rewrite IHt1, IHt2.
       f_equal. f_equal.
       rewrite lift_after_subst.
       assert((k + 1) = S k) by lia.
       rewrite H0. easy.
       lia.
       f_equal.
       specialize (lift_commute_general u 1 1 j 0); intro Ha.
       simpl in Ha. rewrite Ha. easy. lia. lia. easy.
       
       simpl. rewrite IHt1, IHt2. easy. easy. easy.
       simpl. rewrite IHt1, IHt2, IHt3, IHt4.
       f_equal. f_equal.
       rewrite lift_after_subst.
       assert((k + 1) = S k) by lia.
       rewrite H0. easy. lia.
       f_equal.
       specialize (lift_commute_general u 1 1 j 0); intro Ha.
       simpl in Ha. rewrite Ha. easy. lia. easy. easy. easy. lia.
Qed.
