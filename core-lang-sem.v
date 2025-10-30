From Coq Require Import List Arith Lia.
Import ListNotations.

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
  | NatRec : term -> term -> term -> term -> term.  (* P z s n *)

Inductive whnf : Type :=
| VStar  : whnf
| VNat   : whnf
| VPi    : whnf -> closure -> whnf
| VLam   : whnf -> closure -> whnf
| VZero  : whnf
| VSucc  : whnf -> whnf
| VNeutral : neutral -> whnf

with neutral : Type :=
| NVar : nat -> neutral
| NApp : neutral -> whnf -> neutral
| NNatRec : whnf -> whnf -> whnf -> neutral -> neutral

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

    (H_NVar    : forall i, Pn (NVar i))
    (H_NApp    : forall n v, Pn n -> Pw v -> Pn (NApp n v))
    (H_NNatRec : forall P z s n, Pw P -> Pw z -> Pw s -> Pn n -> Pn (NNatRec P z s n))

    (H_Cl     : forall ρ t, Forall Pw ρ -> Pc (Cl ρ t)).

  (* Helper: build a Forall Pw ρ by structural recursion over the list ρ,
     using the mutual whnf_proof function for elements. *)

(* ---- mutual Fixpoint: whnf_proof, neutral_proof, closure_proof ---- *)
  Fixpoint whnf_proof (v : whnf) {struct v} : Pw v :=
    match v with
    | VStar            => H_VStar
    | VNat             => H_VNat
    | VPi A B          => H_VPi A B (whnf_proof A) (closure_proof B)
    | VLam A cl          => H_VLam A cl (whnf_proof A) (closure_proof cl)
    | VZero            => H_VZero
    | VSucc n          => H_VSucc n (whnf_proof n)
    | VNeutral n       => H_VNeutral n (neutral_proof n)
    end

  with neutral_proof (n : neutral) {struct n} : Pn n :=
    match n with
    | NVar i           => H_NVar i
    | NApp n' v        => H_NApp n' v (neutral_proof n') (whnf_proof v)
    | NNatRec P z s n' => H_NNatRec P z s n' (whnf_proof P) (whnf_proof z) (whnf_proof s) (neutral_proof n')
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

Reserved Notation "n1 ≡ₙ n2" (at level 70).
Reserved Notation "v1 ≡ v2" (at level 70).
Reserved Notation "cl1 ≡𝚌 cl2" (at level 70).

Inductive neutral_conv : neutral -> neutral -> Prop :=
| NC_Var : forall i,
    neutral_conv (NVar i) (NVar i)
| NC_App : forall n1 n2 v1 v2,
    neutral_conv n1 n2 ->
    vconv v1 v2 ->
    neutral_conv (NApp n1 v1) (NApp n2 v2)
| NC_NatRec : forall vP1 vz1 vs1 n1 vP2 vz2 vs2 n2,
    vconv vP1 vP2 ->
    vconv vz1 vz2 ->
    vconv vs1 vs2 ->
    neutral_conv n1 n2 ->
    neutral_conv (NNatRec vP1 vz1 vs1 n1) (NNatRec vP2 vz2 vs2 n2)
where "n1 ≡ₙ n2" := (neutral_conv n1 n2)

with vconv : whnf -> whnf -> Prop :=
| VC_Zero: vconv VZero VZero
| VC_Star: vconv VStar VStar
| VC_Nat: vconv VNat VNat
| VC_Succ : forall v1 v2, vconv v1 v2 -> vconv (VSucc v1) (VSucc v2)
| VC_Neutral : forall n1 n2, neutral_conv n1 n2 -> vconv (VNeutral n1) (VNeutral n2)
| VC_Lam : forall vA1 vA2 cl1 cl2, 
    vconv vA1 vA2 -> 
    closure_conv cl1 cl2 -> 
    vconv (VLam vA1 cl1) (VLam vA2 cl2)
| VC_Pi : forall vA1 vA2 cl1 cl2,
    vconv vA1 vA2 ->
    closure_conv cl1 cl2 ->
    vconv (VPi vA1 cl1) (VPi vA2 cl2)
 | VC_LamPi_l : forall cl cl' A A',
    vconv A A' ->
    closure_conv cl cl' ->
    vconv (VLam A cl) (VPi A' cl') 
 | VC_LamPi_r : forall cl cl' A A',
     vconv A A' ->
    closure_conv cl' cl ->
    vconv (VPi A cl') (VLam A' cl) 

where "v1 ≡ v2" := (vconv v1 v2)

with closure_conv : closure -> closure -> Prop :=
| Cl_conv_syn :
     forall ρ1 ρ2 t1 t2,
      Forall2 vconv ρ1 ρ2 ->
      t1 = t2 ->
      closure_conv (Cl ρ1 t1) (Cl ρ2 t2) 

where "cl1 ≡𝚌 cl2" := (closure_conv cl1 cl2).

Definition env_of_cl cl :=
  match cl with
    | Cl rho b => rho
  end.

Definition body_of_cl cl :=
  match cl with
    | Cl rho b => b
  end.

Inductive vapp : whnf -> whnf -> whnf -> Prop :=
| VApp_Lam : forall ρ' b ρB b2 A arg vres,
    closure_conv (Cl ρ' b) (Cl ρB b2) ->
    eval' (arg :: ρ') b vres ->
    vapp (VPi A (Cl ρB b2)) arg vres
| VApp_Neut : forall n v, vapp (VNeutral n) v (VNeutral (NApp n v))
| VApp_Other_Pi : forall A cl arg,
    (forall ρ' b, ~ closure_conv (Cl ρ' b) cl) ->  (* no convertible lambda exists *)
    vapp (VPi A cl) arg (VPi A cl)
| VApp_Other_Other : forall w arg,
    (forall A ρ' b, w <> VLam A (Cl ρ' b)) ->
    (forall n, w <> VNeutral n) ->
    (forall A cl, w <> VPi A cl) ->
    vapp w arg w

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
| ENR_Other : forall vP vz vs vn,
    (forall w, vn <> VSucc w) ->
    vn <> VZero ->
    (forall n, vn <> VNeutral n) ->
    eval_natrec vP vz vs vn vz

(* evaluation relation (weak head) *)
with eval' : list whnf -> term -> whnf -> Prop :=
| E'_Star : forall ρ, eval' ρ Star VStar
| E'_Nat : forall ρ, eval' ρ Nat VNat
| E'_Var_Some : forall ρ x v, nth_error ρ x = Some v -> eval' ρ (Var x) v
| E'_Var_None : forall ρ x, nth_error ρ x = None -> eval' ρ (Var x) (VNeutral (NVar (x - length ρ)))
| E'_Pi : forall ρ A B vA, eval' ρ A vA -> eval' ρ (Pi A B) (VPi vA (Cl ρ B))
| E'_Lam : forall ρ A vA b, eval' ρ A vA -> eval' ρ (Lam A b) (VLam vA (Cl ρ b))
| E'_App : forall ρ t u vt vu v, eval' ρ t vt -> eval' ρ u vu -> vapp vt vu v -> eval' ρ (App t u) v

| E'_Zero : forall ρ, eval' ρ Zero VZero
| E'_Succ : forall ρ n vn, eval' ρ n vn -> eval' ρ (Succ n) (VSucc vn)
| E'_NatRec : forall ρ P z s n vP vz vs vn v,
    eval' ρ P vP ->
    eval' ρ z vz ->
    eval' ρ s vs ->
    eval' ρ n vn ->
    eval_natrec vP vz vs vn v ->
    eval' ρ (NatRec P z s n) v.

Scheme eval'_rect := Induction for eval' Sort Prop
with vapp_rect := Induction for vapp Sort Prop
with eval_natrec_rect := Induction for eval_natrec Sort Prop.

Combined Scheme evals_mutind from eval'_rect, vapp_rect, eval_natrec_rect.

Lemma vconv_refl :
  (forall v, vconv v v) /\ 
  (forall n, neutral_conv n n) /\ 
  (forall c, closure_conv c c).
Proof. apply whnf_mutind.
       11:{ intros.
            revert t.
            induction H; intros.
            - constructor. constructor.
              easy.
            - constructor.
              constructor. easy.
              specialize(IHForall t).
              inversion IHForall. subst. easy.
              easy.
          }
        3:{ intros. constructor; easy. }
        3:{ intros. constructor; easy. }
        8:{ intros. constructor; easy. }
        7:{ intros. constructor; easy. }
        6:{ intros. constructor; easy. }
        5:{ intros. constructor; easy. }
        4:{ intros. constructor; easy. }
        3:{ constructor. }
        2:{ constructor. }
        1:{ constructor. }
Qed.

Lemma vconv_sym :
  (forall v1 v2, vconv v1 v2 -> vconv v2 v1) /\ 
  (forall n1 n2, neutral_conv n1 n2 -> neutral_conv n2 n1) /\ 
  (forall c1 c2, closure_conv c1 c2 -> closure_conv c2 c1).
Proof. apply whnf_mutind.
       11:{ intros.
            revert t H0. revert c2.
            induction H; intros.
            - inversion H0. subst. constructor. inversion H2. constructor. easy.
            - inversion H1. subst. constructor.
              inversion H4. subst.
              constructor. apply H. easy.
              specialize(IHForall (Cl l' t2) t2).
              assert(Cl l t2 ≡𝚌 Cl l' t2).
              constructor; easy.
              apply IHForall in H2.
              inversion H2. easy.
              easy.
          }
        3:{ intros. inversion H1. subst. constructor. apply H; easy. apply H0; easy. 
            subst. constructor. apply H. easy.
            apply H0. easy.
        }
        9:{
        intros.
        inversion H3.
        subst.
        apply H in H8.
        apply H0 in H10.
        apply H1 in H11.
        apply H2 in H12.
        constructor; easy.
        }
        8:{
        intros.
        inversion H1.
        subst.
        apply H in H4.
        apply H0 in H6.
        constructor; easy.
        }
        7:{
        intros.
        inversion H. subst. easy.
        }
        6:{
        intros.
        inversion H0. subst.
        apply H in H2. constructor. easy.
        }
        5:{
        intros.
        inversion H0. subst.
        apply H in H2.
        constructor. easy.
        }
        4:{
        intros. inversion H. constructor.
        }
        3:{
        intros.
        inversion H1.
        + subst.
          constructor. apply H. easy.
          apply H0. easy.
        + subst.
          constructor. apply H. easy.
          apply H0. easy.
        }
        2:{
        intros.
        inversion H. constructor.
        }
        1:{
        intros.
        inversion H. constructor.
        }
Qed.


Lemma vconv_trans :
  (forall v1 v2 v3, vconv v1 v2 -> vconv v2 v3 -> vconv v1 v3) /\ 
  (forall n1 n2 n3, neutral_conv n1 n2 -> neutral_conv n2 n3 -> neutral_conv n1 n3) /\ 
  (forall c1 c2 c3, closure_conv c1 c2 -> closure_conv c2 c3 -> closure_conv c1 c3).
Proof. apply whnf_mutind.
       11:{ intros.
            revert t H0 H1. revert c2 c3.
            induction H; intros.
            - inversion H0. subst. inversion H1. subst. constructor. inversion H3. subst. inversion H4. constructor. easy.
            - inversion H1. subst. inversion H2. subst. constructor.
              inversion H5. subst.
              inversion H6. subst.
              constructor. apply H with (v2 := y). easy. easy.
              specialize(IHForall (Cl l' t0) (Cl l'0 t0) t0).
              assert(Cl l t0 ≡𝚌 Cl l' t0).
              constructor; easy.
              assert(Cl l' t0 ≡𝚌 Cl l'0 t0).
              constructor; easy.
              apply IHForall in H3; try easy.
              inversion H3. subst. easy.
              easy.
          }
        3:{ intros.
            inversion H1. subst.
            + inversion H2.
              * subst. constructor.
                apply H with (v2 := vA2); easy.
                apply H0 with (c2 := cl2); easy.
              * subst.
                constructor.
                apply H with (v2 := vA2); easy.
                apply H0 with (c2 := cl2). easy. easy.
            + subst. inversion H2.
              * subst. constructor.
                apply H with (v2 := A'); easy.
                apply H0 with (c2 := cl). easy. easy.
              * subst. constructor.
                apply H with (v2 := A'); easy.
                apply H0 with (c2 := cl). easy. easy.
         }
        9:{
        intros.
        inversion H3. subst.
        inversion H4. subst.
        specialize(H _ _ H9 H10).
        specialize(H0 _ _ H11 H15).
        specialize(H1 _ _ H12 H16).
        specialize(H2 _ _ H13 H17).
        constructor; easy.
        }
        3:{
        intros.
        inversion H1.
        + subst.
          inversion H2.
          ++ subst. constructor. apply H with (v2 := vA2); easy. apply H0 with (c2 := cl2). easy. easy.
          ++ subst. constructor. apply H with (v2 := vA2); easy. apply H0 with (c2 := cl2). easy. easy.
        + subst.
          inversion H2.
          ++ subst. constructor. apply H with (v2 := A'); easy. apply H0 with (c2 := cl'). easy. easy.
          ++ subst. constructor. apply H with (v2 := A'); easy. apply H0 with (c2 := cl'). easy. easy.
        }
        4:{
        intros.
        inversion H0. subst. inversion H1. subst.
        constructor. apply H with (v2 := v0); easy.
        }
        4:{
        intros.
        inversion H0. subst. inversion H1. subst.
        constructor. apply H with (n2 := n2); easy.
        }
        5:{
        intros.
        inversion H1. subst. inversion H2. subst.
        constructor. apply H with (n2 := n0); easy.
        apply H0 with (v2 := v2); easy.
        }
        4:{
        intros.
        inversion H. subst.
        inversion H0. constructor.
        }
        3:{
        intros.
        inversion H. subst.
        inversion H0. constructor.
        }
        2:{
        intros.
        inversion H. subst.
        inversion H0. constructor.
        }
        1:{
        intros.
        inversion H. subst.
        inversion H0. constructor.
        }
Qed.

Lemma vconv_to_succ_inv :
  forall x y,
    vconv x (VSucc y) ->
    exists x', x = VSucc x' /\ vconv x' y.
Proof.
  intros x y H.
  inversion H; try (now inversion H1).
  subst. exists v1; split; auto.
Qed.

Lemma vconv_to_neutral_inv :
  forall x n,
    vconv x (VNeutral n) ->
    exists n', x = VNeutral n' /\ neutral_conv n' n.
Proof.
  intros x n H.
  inversion H; try (now inversion H1).
  subst.
  exists n1; split; auto.
Qed.

Lemma Forall2_nth_error_same_index {A} (R : A -> A -> Prop) :
  forall l1 l2 i x1 x2,
    Forall2 R l1 l2 ->
    nth_error l1 i = Some x1 ->
    nth_error l2 i = Some x2 ->
    R x1 x2.
Proof. intro l1.
       induction l1; intros.
       - inversion H. subst.
         rewrite nth_error_nil in H0. easy.
       - inversion H.
         subst.
         destruct i. simpl in *.
         inversion H0. inversion H1. subst. easy.
         simpl in *.
         apply IHl1 with (l2 := l') (i := i); easy.
Qed.

Lemma nthsome: forall {A: Type} (ρ: list A) x v,
nth_error ρ x = Some v -> x < List.length ρ.
Proof. intros A r.
       induction r; intros.
       - rewrite nth_error_nil in H. easy.
       - simpl.
         destruct x.
         ++ lia.
         ++ simpl in H.
            apply IHr in H. lia.
Qed.

Lemma Forall2_refl {A} (R : A -> A -> Prop) :
  (forall x, R x x) ->
  forall l, Forall2 R l l.
Proof.
  intros Rs l; induction l; constructor; auto.
Qed.

Lemma Forall2_sym {A} (R : A -> A -> Prop) :
  (forall x y, R x y -> R y x) ->
  forall l1 l2, Forall2 R l1 l2 -> Forall2 R l2 l1.
Proof.
  intros Rs l1 l2 H; induction H; constructor; auto.
Qed.

Lemma Forall2_trans {A} (R : A -> A -> Prop) :
  (forall x y z, R x y -> R y z -> R x z) ->
  forall l1 l2 l3, Forall2 R l1 l2 -> Forall2 R l2 l3 -> Forall2 R l1 l3.
Proof.
  intros Rtrans l1.
  revert Rtrans.
  induction l1; intros.
  - inversion H. subst. inversion H0. constructor.
  - inversion H. subst. inversion H0. subst. constructor.
    + apply (Rtrans a y y0); assumption.
    + apply IHl1 with (l2 := l'); easy.
Qed.

Lemma evals_respect_vconv_mut :
  (forall (ρ1 : list whnf) (t : term) (v1 : whnf) (He : eval' ρ1 t v1),
      forall (ρ2 : list whnf) (v2 : whnf),
        Forall2 vconv ρ1 ρ2 ->
        eval' ρ2 t v2 ->
        vconv v1 v2)
  /\
  (forall (w arg res : whnf) (He : vapp w arg res),
      forall (w2 arg2 res2 : whnf),
        vconv w w2 ->
        vconv arg arg2 ->
        vapp w2 arg2 res2 ->
        vconv res res2)
  /\
  (forall (vP vz vs vn v : whnf) (He : eval_natrec vP vz vs vn v),
      forall (vP2 vz2 vs2 vn2 v2 : whnf),
        vconv vP vP2 ->
        vconv vz vz2 ->
        vconv vs vs2 ->
        vconv vn vn2 -> 
        eval_natrec vP2 vz2 vs2 vn2 v2 ->
        vconv v v2).
Proof.
  apply (evals_mutind
    (fun (ρ : list whnf) (t : term) (v : whnf) (He : eval' ρ t v) =>
       forall (ρ2 : list whnf) (v2 : whnf),
         Forall2 vconv ρ ρ2 ->
         eval' ρ2 t v2 ->
         vconv v v2)

    (fun (w arg res : whnf) (He : vapp w arg res) =>
       forall (w2 arg2 res2 : whnf),
         vconv w w2 ->
         vconv arg arg2 ->
         vapp w2 arg2 res2 ->
         vconv res res2)

    (fun (vP vz vs vn v : whnf) (He : eval_natrec vP vz vs vn v) =>
       forall (vP2 vz2 vs2 vn2 v2 : whnf),
         vconv vP vP2 ->
         vconv vz vz2 ->
         vconv vs vs2 ->
         vconv vn vn2 -> 
         eval_natrec vP2 vz2 vs2 vn2 v2 ->
         vconv v v2)
  ); intros.
  18:{
  inversion H3.
  + subst. easy.
  + subst.
    inversion H2. subst.
    specialize(n v0). easy.
  + subst.
    inversion H2. subst.
    specialize(n1 n2). easy.
  + subst. easy.
  }
  
  17:{
  inversion H3.
  + subst. easy.
  + subst. easy.
  + subst. constructor.
    inversion H2.
    constructor; try easy.
  + subst.
    inversion H2. subst.
    specialize(H6 n2). easy.
  }
  
  16:{
  inversion H6.
  + subst.
    inversion H5.
  + subst.
    inversion H5.
    subst.
    apply H1 with (w2 := v4) (arg2 := vrec0); try easy.
    apply H0 with (w2 := vs2) (arg2 := vn0); try easy.
    eapply H; eauto.
  + subst. inversion H5.
  + subst. inversion H5. subst.
    specialize(H7 v5). easy.
   }
   
   15:{
   inversion H3.
   + subst. easy.
   + subst. easy.
   + subst. easy.
   + subst. inversion H2.
     subst.
     easy.
   }
   
   14:{
   inversion H1.
   + subst.
     inversion H.
     ++ subst.
        specialize(n1 vA1 cl1). easy.
        
     ++ subst.
        inversion H8. subst.
        specialize(n A0 ρ1 b2). easy.
   + subst.
     inversion H1.
     ++ subst.
        inversion H. subst.
        specialize(n0 n3). easy.
     ++ subst.
        specialize(H4 (NApp n2 arg2)). easy.
    + subst. easy.
    + subst. easy.
   }
   
   13:{
   inversion H1.
   + subst.
     inversion H. subst. inversion H9. subst.
     specialize(n ρ1 b2). 
     unfold not in *.
     contradiction n.
     apply vconv_refl.
   + subst. easy.
   + subst. easy.
   + subst. easy.
  }
  
  12:{
  inversion H1.
  + subst. easy.
  + subst.
    constructor. inversion H. subst. constructor; easy.
  + subst. easy.
  + subst.
    inversion H. subst.
    specialize(H3 n2). easy.
  }
  
  11:{
  inversion H0. subst.
  inversion H2.
  + subst.
    apply H with (ρ2 := (arg2 :: ρ'0)).
    constructor. easy.
    inversion c. subst.
    inversion H6. subst.
    inversion H7. subst.

    eapply Forall2_trans; [apply vconv_trans | 
    eapply Forall2_trans; [apply vconv_trans | exact H9 | exact H12] |
    eapply Forall2_sym; [apply vconv_sym | exact H11] ].
  
    inversion H6. subst.
    inversion H7. subst.
    inversion c. subst.
    easy.
  + subst.
    inversion H7. subst.
    specialize(H9 ρ2 t2). unfold not in *.
    contradiction H9.
    apply vconv_refl.
  + subst.
    specialize(H6 vA2 cl2). easy.
  + subst.
    inversion H2. subst.
    inversion H7. subst.
    specialize(H3 A' ρ2 t2). easy.
  }
  
  10:{
  inversion H5.
  subst.
  apply H3 with (vP2 := vP0) (vz2 := vz0) (vs2 := vs0) (vn2 := vn0).
  apply H with (ρ2 := ρ2); easy.
  apply H0 with (ρ2 := ρ2); easy.
  apply H1 with (ρ2 := ρ2); easy.
  apply H2 with (ρ2 := ρ2); easy. easy.
  }
  
  9:{
  inversion H1.
  subst.
  constructor. apply H with (ρ2 := ρ2); easy.
  }
  
  8:{
  inversion H0. constructor.
  }
  
  7:{
  inversion H3. subst.
  apply H1 with (w2 := vt0) (arg2 := vu0).
  apply H with (ρ2 := ρ2); easy.
  apply H0 with (ρ2 := ρ2); easy. easy.
  }
  
  6:{
  inversion H1. subst.
  constructor.
  apply H with (ρ2 := ρ2); easy.
  constructor; easy.
  }
  
  5:{
  inversion H1. subst.
  constructor.
  apply H with (ρ2 := ρ2); easy.
  constructor; easy.
  }
  
  4:{
  inversion H0.
  + apply nth_error_None in e.
    apply Forall2_length in H.
    specialize(nthsome _ _ _ H3); intros.
    lia.
  + subst.
    constructor.
    apply Forall2_length in H.
    rewrite H.
    constructor.
  }
  
  3:{
  inversion H0.
  + subst.
    eapply Forall2_nth_error_same_index; eauto.
  + apply nth_error_None in H3.
    apply Forall2_length in H.
    rewrite <- H in H3.
    specialize(nthsome _ _ _ e); intros.
    lia.
  }
  
  2:{ 
  inversion H0.
  constructor.
  }
  
  1:{
  inversion H0.
  constructor.
  }
Qed.

Lemma closure_conv_extensional :
  forall ρ1 ρ2 t1 t2,
    closure_conv (Cl ρ1 t1) (Cl ρ2 t2) ->
    forall v1 v2 v1' v2',
      vconv v1 v2 ->
      eval' (v1 :: ρ1) t1 v1' ->
      eval' (v2 :: ρ2) t2 v2' ->
      vconv v1' v2'.
Proof.
  intros ρ1 ρ2 t1 t2 Hcl v1 v2 v1' v2' Harg Hle He2.
  inversion Hcl as [ρ1' ρ2' t1' t2' Henv Heq]; subst; clear Hcl.
  destruct evals_respect_vconv_mut as [Heval _].
  eapply Heval; eauto.
Qed.

Lemma eval_respect_vconv_imp :
  forall (ρ1 ρ2 : list whnf) (t : term) (v1 v2 : whnf),
    Forall2 vconv ρ1 ρ2 ->
    eval' ρ1 t v1 ->
    eval' ρ2 t v2 ->
    vconv v1 v2.
Proof.
  destruct evals_respect_vconv_mut as [He _].
  intros ρ1 ρ2 t v1 v2 Henv He1 He2.
  apply (He ρ1 t v1 He1 ρ2 v2 Henv He2).
Qed.

Lemma eval_respect_vconv_imp2 :
  forall (ρ : list whnf) (t : term) (v1 v2 : whnf),
    eval' ρ t v1 ->
    eval' ρ t v2 ->
    vconv v1 v2.
Proof.
  destruct evals_respect_vconv_mut as [He _].
  intros ρ t v1 v2 He1 He2.
  apply He with (ρ1 := ρ) (t := t) (ρ2 := ρ); try easy.
  apply Forall2_refl.
  apply vconv_refl.
Qed.

Lemma vapp_respect_vconv_imp :
  forall (w w2 arg arg2 res res2 : whnf),
    vconv w w2 ->
    vconv arg arg2 ->
    vapp w arg res ->
    vapp w2 arg2 res2 ->
    vconv res res2.
Proof.
  destruct evals_respect_vconv_mut as [_ [Hvapp _]].  (* project second component *)
  intros w w2 arg arg2 res res2 Hww Harg Hv1 Hv2.
  apply (Hvapp w arg res Hv1 w2 arg2 res2 Hww Harg Hv2).
Qed.

Lemma eval_natrec_respect_vconv_imp :
  forall (vP vP2 vz vz2 vs vs2 vn vn2 v v2 : whnf),
    vconv vP vP2 ->
    vconv vz vz2 ->
    vconv vs vs2 ->
    vconv vn vn2 ->
    eval_natrec vP vz vs vn v ->
    eval_natrec vP2 vz2 vs2 vn2 v2 ->
    vconv v v2.
Proof.
  destruct evals_respect_vconv_mut as [_ [_ HeNat]].  (* project third component *)
  intros vP vP2 vz vz2 vs vs2 vn vn2 v v2 Hvp Hvz Hvs Hvn He1 He2.
  apply (HeNat vP vz vs vn v He1 vP2 vz2 vs2 vn2 v2 Hvp Hvz Hvs Hvn He2).
Qed.


(* ---------------------------
   Bidirectional typing (synthesis / checking)
   synth : ctx -> term -> whnf -> Prop  (Γ ⊢ t ⇒ A)
   check : ctx -> term -> whnf -> Prop  (Γ ⊢ t ⇐ A)
   Both operate at WHNF-level for types.
   --------------------------- *)

Definition ctx := list whnf.

Reserved Notation "Γ ⊢ₛ t ⇑ A" (at level 70).
Reserved Notation "Γ ⊢𝚌 t ⇓ A" (at level 70).

Inductive synth : ctx -> term -> whnf -> Prop :=
| S_Var : forall Γ x A,
    nth_error Γ x = Some A ->
    synth Γ (Var x) A

| S_Star : forall Γ,                      (* Universe/type of types *)
    synth Γ Star VStar

| S_Nat : forall Γ,                       (* Nat is a type-level WHNF *)
    synth Γ Nat VNat

| S_Pi : forall Γ A B vA,
    eval' Γ A vA ->
    synth Γ (Pi A B) (VPi vA (Cl Γ B))

(* standard App: synth f to a Pi (up to conv), evaluate arg and body to get result type *)
| S_App : forall Γ t u vt vu vdom clB ρB Bterm vres,
    synth Γ t vt ->                 (* synthesize type of t (should be a Pi up to conv) *)
    eval' Γ u vu ->                 (* evaluate argument to WHNF *)
    vconv vt (VPi vdom clB) ->      (* vt convertible to a Pi *)
    clB = Cl ρB Bterm ->            (* expose closure parts *)
    eval' (vu :: ρB) Bterm vres ->  (* compute codomain under argument value *)
    synth Γ (App t u) vres

(* Zero/Succ synthesize Nat as their type *)
| S_Zero : forall Γ, synth Γ Zero VNat

| S_Succ : forall Γ n,
    check Γ n VNat ->               (* check argument n has type Nat *)
    synth Γ (Succ n) VNat

(* NatRec term-level: produces whatever eval_natrec produces (term-level eliminator) *)
| S_NatRec_term : forall Γ P z s n vP vz vs vn v,
    eval' Γ P vP ->
    eval' Γ z vz ->
    eval' Γ s vs ->
    eval' Γ n vn ->
    eval_natrec vP vz vs vn v ->
    synth Γ (NatRec P z s n) v

(* ---------- check: Γ ⊢ t ⇐ A ---------- *)
with check : ctx -> term -> whnf -> Prop :=
| C_Synth : forall Γ t A' A,
    synth Γ t A' ->
    vconv A' A ->
    check Γ t A

| C_Lam : forall Γ (A : whnf) annA b vdom clB ρB Bterm vB,
    synth Γ annA vdom ->                 (* annotation provides domain WHNF vdom *)
    vconv A (VPi vdom clB) ->            (* expected type convertible to Pi vdom clB *)
    clB = Cl ρB Bterm ->
    eval' (vdom :: ρB) Bterm vB ->      (* compute codomain value *)
    check (vdom :: ρB) b vB ->          (* check body under extended context *)
    closure_conv (Cl Γ b) clB ->        (** ATTENTION - link runtime closure and expected closure **)
    check Γ (Lam annA b) A

| C_NatRec_check : forall Γ P z s n A vP vz vs vn v,
    (* evaluate the eliminator components *)
    eval' Γ P vP ->              (* evaluate P *)
    eval' Γ z vz ->              (* evaluate z *)
    eval' Γ s vs ->              (* evaluate s *)
    eval' Γ n vn ->              (* evaluate n *)
    eval_natrec vP vz vs vn v -> (* compute the result v of elimination *)
    vconv v A ->                 (* v must be convertible to the expected A *)
    check Γ (NatRec P z s n) A.

Scheme synth_rect := Induction for synth Sort Prop
with check_rect := Induction for check Sort Prop.

Combined Scheme typing_mutind from synth_rect, check_rect.

Lemma Forall2_refl_from_pointwise_reflexivity :
  (forall w, vconv w w) ->
  forall Γ, Forall2 vconv Γ Γ.
Proof.
  intros H; induction Γ; constructor; auto.
Qed.

Lemma typing_unique_mut :
  (forall Γ t A (He : synth Γ t A) A' (He' : synth Γ t A'), vconv A A')  /\
  (forall Γ t A (He : check Γ t A) A' (He' : synth Γ t A'), vconv A A').
Proof.
  eapply (typing_mutind
    (fun Γ t A (He : synth Γ t A) => forall A' (He' : synth Γ t A'), vconv A A')
    (fun Γ t A (He : check Γ t A) => forall A' (He' : synth Γ t A'), vconv A A')
  ).
    10:{
    intros. inversion He'.
    }
    9:{
    intros.
    apply H in He'.
    specialize(vconv_sym ); intros (Hsym,(_,_)).
    specialize(Hsym _ _ v).
    specialize(vconv_trans ); intros (Htrans,(_,_)).
    specialize(Htrans _ _ _ Hsym He'). easy.
    }
    8:{
    intros.
    inversion He'. subst.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e H3); intro HHa.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e0 H5); intro HHb.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e1 H7); intro HHc.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e2 H8); intro HHd.
    specialize (eval_natrec_respect_vconv_imp _ _ _ _ _ _ _ _ v A' HHa HHb HHc HHd e3 H9); intro HHe.
    easy.
    }
    7:{
    intros.
    inversion He'.
    subst. constructor.
    }
    6:{
    intros.
    inversion He'.
    subst. constructor.
    }
    5:{
    intros.
    inversion He'.
    subst.
    inversion H4. subst.
    apply H in H2.
    inversion H2.
    subst.
    inversion v.
    subst.
    assert(vconv vu vu0).
    { specialize(eval_respect_vconv_imp2 _ _ _ _ e H3); intro HHa. easy. }

    inversion H7. subst.
    inversion H13. subst.
    inversion H10. subst.
    
    assert(Forall2 vconv Γ Γ).
    { apply Forall2_refl. apply vconv_refl. }
    specialize(eval_respect_vconv_imp _ _ _ _ _ H1 e H3); intros.
    assert(Forall2 vconv (vu :: ρB) (vu0 :: ρB0)).
    { constructor. easy.
      apply Forall2_sym in H15.
      assert(Forall2 vconv ρB ρ1).
      { apply Forall2_trans with (l2 := ρ0).
        apply vconv_trans.
        easy. easy.
      }
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
      apply vconv_sym.
    }

    apply(eval_respect_vconv_imp _ _ _ _ _ H12 e1 H8).
    
    subst.
    assert(vconv vu vu0).
    { specialize(eval_respect_vconv_imp2 _ _ _ _ e H3); intro HHa. easy. }
    
    inversion v. subst.
    inversion H7. subst.
    inversion H10. subst.
    inversion H14. subst.
    assert(Forall2 vconv ρB ρ1).
    { apply Forall2_sym in H16. 
      apply Forall2_trans with (l2 := ρ0).
      apply vconv_trans. easy. easy.
      apply vconv_sym.
    }
    assert(Forall2 vconv (vu :: ρB) (vu0 :: ρB0)).
    { constructor. easy.
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
    }
    apply(eval_respect_vconv_imp _ _ _ _ _ H5 e1 H8).

    inversion v. subst.
    apply H in H2.
    inversion H2. subst.
    inversion H7. subst.
    inversion H13. subst.
    inversion H11. subst.
    assert(Forall2 vconv Γ Γ).
    { apply Forall2_refl. apply vconv_refl. }
    specialize(eval_respect_vconv_imp _ _ _ _ _ H0 e H3); intros.
    
    assert(Forall2 vconv (vu :: ρB) (vu0 :: ρB0)).
    { constructor. easy.
      apply Forall2_sym in H14.
      assert(Forall2 vconv ρB ρ1).
      { apply Forall2_trans with (l2 := ρ0).
        apply vconv_trans.
        easy. easy.
      }
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
      apply vconv_sym.
    }
    apply(eval_respect_vconv_imp _ _ _ _ _ H5 e1 H8).
    
    subst.
    apply H in H2.
    inversion H2. subst.
    inversion H7. subst.
    inversion H13. subst.
    inversion H11. subst.
    assert(Forall2 vconv Γ Γ).
    { apply Forall2_refl. apply vconv_refl. }
    specialize(eval_respect_vconv_imp _ _ _ _ _ H0 e H3); intros.
    
    assert(Forall2 vconv (vu :: ρB) (vu0 :: ρB0)).
    { constructor. easy.
      apply Forall2_sym in H14.
      assert(Forall2 vconv ρB ρ1).
      { apply Forall2_trans with (l2 := ρ0).
        apply vconv_trans.
        easy. easy.
      }
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
      apply vconv_sym.
    }
    apply(eval_respect_vconv_imp _ _ _ _ _ H5 e1 H8).
    }
    4:{
    intros.
    inversion He'.
    subst.
    constructor.
    assert(Forall2 vconv Γ Γ).
    { apply Forall2_refl. apply vconv_refl. }
    apply(eval_respect_vconv_imp _ _ _ _ _ H e H3).
    apply vconv_refl.
    }
    3:{
    intros.
    inversion He'. constructor.
    }
    2:{
    intros.
    inversion He'. constructor.
    }
    1:{
    intros.
    inversion He'.
    subst.
    rewrite e in H1. inversion H1.
    subst.
    apply vconv_refl.
    }
    1:{
    intros.
    inversion He'.
    subst.
    
    specialize(eval_respect_vconv_imp2 _ _ _ _ e H3); intro HHa.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e0 H5); intro HHb.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e1 H7); intro HHc.
    specialize(eval_respect_vconv_imp2 _ _ _ _ e2 H8); intro HHd.
    specialize (eval_natrec_respect_vconv_imp _ _ _ _ _ _ _ _ v A' HHa HHb HHc HHd e3 H9); intro HHe.

    specialize(vconv_sym ); intros (Hsym,(_,_)).
    specialize(Hsym _ _ v0).
    specialize(vconv_trans ); intros (Htrans,(_,_)).
    specialize(Htrans _ _ _ Hsym HHe). easy.
    }
Qed.

Lemma synth_unique_up_to_vconv :
  forall Γ t A A',
    synth Γ t A ->
    synth Γ t A' ->
    vconv A A'.
Proof.
  intros Γ t A A' H H'.
  apply (proj1 typing_unique_mut Γ t A H A' H').
Qed.

Lemma check_vsynth_unique_up_to_vconv :
  forall Γ t A A',
    check Γ t A ->
    synth Γ t A' ->
    vconv A A'.
Proof.
  intros Γ t A A' Hc Hs.
  apply (proj2 typing_unique_mut Γ t A Hc A' Hs).
Qed.

(* Inductive type_synth_closed : term -> Prop :=
| TSC_Star  : type_synth_closed Star
| TSC_Nat   : type_synth_closed Nat
| TSC_Pi    : forall A B,     type_synth_closed A -> type_synth_closed (Pi A B)
| TSC_Var   : forall x,       type_synth_closed (Var x)
| TSC_App   : forall t u,     type_synth_closed t -> type_synth_closed (App t u)
| TSC_Lam   : forall A b,     type_synth_closed A -> type_synth_closed (Lam A b)
| TSC_NatRec: forall P z s n, type_synth_closed P -> type_synth_closed (NatRec P z s n).
 *)

Inductive type_synth_closed : term -> Prop :=
| TSC_Star   : type_synth_closed Star
| TSC_Nat    : type_synth_closed Nat
| TSC_Pi     : forall A B,
    type_synth_closed A ->
    type_synth_closed B ->
    type_synth_closed (Pi A B)
| TSC_Var    : forall x,
    type_synth_closed (Var x)
| TSC_App    : forall t u,
    type_synth_closed t ->
    type_synth_closed u ->
    type_synth_closed (App t u)
| TSC_Lam    : forall A b,
    type_synth_closed A ->
    type_synth_closed b ->
    type_synth_closed (Lam A b)
| TSC_NatRec : forall P z s n,
    type_synth_closed P ->
    type_synth_closed z ->
    type_synth_closed s ->
    type_synth_closed n ->
    type_synth_closed (NatRec P z s n).


Lemma synth_preserve_eval_for_types :
  (forall Γ t A (He : synth Γ t A),
    forall v, type_synth_closed t -> eval' Γ t v -> vconv A v)
  /\
  (forall Γ t A (He : check Γ t A),
     forall v, type_synth_closed t -> eval' Γ t v -> vconv A v).
Proof.
  eapply (typing_mutind
    (fun (Γ : ctx) (t : term) (A : whnf) (He : synth Γ t A) =>
       forall v, type_synth_closed t -> eval' Γ t v -> vconv A v)
    (fun (Γ : ctx) (t : term) (A : whnf) (He : check Γ t A) =>
       forall v, type_synth_closed t -> eval' Γ t v -> vconv A v)
  ).
  4:{
  intros.
  inversion H0. subst.
  constructor.
  assert(Forall2 vconv Γ Γ).
  { apply Forall2_refl. apply vconv_refl. }
  specialize(eval_respect_vconv_imp _ _ _ _ _ H1 e H5); intros.
  easy.
  apply vconv_refl.
  }
  4:{
  intros.
  subst.
  inversion H0. subst.
  inversion H1. subst.
  assert(Forall2 vconv Γ Γ).
  { apply Forall2_refl. apply vconv_refl. }
  specialize(eval_respect_vconv_imp _ _ _ _ _ H2 e H8); intros.
  inversion v.
  + subst.
    inversion H10.
    * subst. 
      apply H in H6; try easy.
      inversion H6. subst.
      inversion H13. subst.
      inversion H18. subst.
      inversion H7. subst.
      

    assert(Forall2 vconv (vu :: ρB)(vu0 :: ρ')).
    { constructor. easy.
      assert(Forall2 vconv ρ' ρ1).
      { apply Forall2_trans with (l2 := ρB0).
        apply vconv_trans.
        easy.
        apply Forall2_sym in H19. easy.
        apply vconv_sym.
      }
      apply Forall2_sym in H11, H17.
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
      apply vconv_sym.
      apply vconv_sym.
    }
    apply(eval_respect_vconv_imp _ _ _ _ _ H11 e1 H9).


    * subst.
      apply H in H6; try easy.
    * subst.
      apply H in H6; try easy.
      inversion H6. subst.
      inversion H13. subst.
      inversion H17. subst.
      specialize(H7 ρ2 t2). 
      
      unfold not in *.
      contradiction H7.
      apply vconv_refl.

    * subst.
      apply H in H6; try easy.
      inversion H6. subst.
      ** specialize(H11 vA2 cl2). easy.
      ** subst.
        inversion H13. subst.
        inversion H18. subst.
        specialize(H7 A' ρ2 t2). easy.
  + subst.
    inversion H10. 
    * subst.
      apply H in H6; try easy.
      inversion H6. subst.
      inversion H13. subst.
      inversion H18. subst.
      inversion H7. subst.


    assert(Forall2 vconv (vu :: ρB)(vu0 :: ρ')).
    { constructor. easy.
      assert(Forall2 vconv ρ' ρ1).
      { apply Forall2_trans with (l2 := ρB0).
        apply vconv_trans.
        easy.
        apply Forall2_sym in H19. easy.
        apply vconv_sym.
      }
      apply Forall2_sym in H11, H17.
      apply Forall2_trans with (l2 := ρ1).
      apply vconv_trans.
      easy. easy.
      apply vconv_sym.
      apply vconv_sym.
    }
    apply(eval_respect_vconv_imp _ _ _ _ _ H11 e1 H9).


    * subst.
      apply H in H6; try easy.
    * subst.
      apply H in H6; try easy.
      inversion H6. subst.
      inversion H13. subst.
      inversion H17. subst.
      specialize(H7 ρ2 t2).
      
      unfold not in *.
      contradiction H7.
      apply vconv_refl.
      
    * subst.
      apply H in H6; try easy.
      inversion H6. subst.
      ** subst.
         inversion H13. subst.
         inversion H18. subst.
         specialize(H7 vA2 ρ2 t2). easy.
      ** subst. 
         specialize(H11 A' cl'). easy.
    }

  9:{
  intros.
  inversion H0.
  subst.
  specialize(eval_respect_vconv_imp2 _ _ _ _ e H5); intro HHa.
  specialize(eval_respect_vconv_imp2 _ _ _ _ e0 H7); intro HHb.
  specialize(eval_respect_vconv_imp2 _ _ _ _ e1 H9); intro HHc.
  specialize(eval_respect_vconv_imp2 _ _ _ _ e2 H10); intro HHd.
  specialize (eval_natrec_respect_vconv_imp _ _ _ _ _ _ _ _ v v1 HHa HHb HHc HHd e3 H11); intro HHe.
  apply vconv_sym in v0.
  specialize vconv_trans; intros (Ht,(_,_)).
  apply Ht with (v2 := v); easy.
  }
  
  8:{
  intros.
  inversion H1. subst.
  inversion H2. subst.
  inversion v. 
  + subst.
    apply H in H9; try easy.
    constructor. 
    specialize(vconv_trans); intros (Htrans,(_,_)).
    apply Htrans with (v2 := vdom); easy.
    
    specialize(vconv_sym); intros (_,(_,Hsym)).
    apply Hsym in c0.
    specialize(vconv_trans); intros (_,(_,Htrans)).
    apply Htrans with (c2 := (Cl ρB Bterm)); easy.

  + subst. 
    apply H in H9; try easy.
    constructor. specialize(vconv_trans); intros (Htrans,(_,_)).
    apply Htrans with (v2 := vdom); easy.
    
    specialize(vconv_sym); intros (_,(_,Hsym)).
    apply Hsym in c0.
    specialize(vconv_trans); intros (_,(_,Htrans)).
    apply Htrans with (c2 := (Cl ρB Bterm)); easy.
  }

 7:{
 intros.
 apply H in H1; try easy.

 specialize(vconv_sym); intros (Hsym,(_,_)).
 apply Hsym in v.
 specialize(vconv_trans); intros (Htrans,(_,_)).
 apply Htrans with (v2 := A'); easy.
 }
 
 6:{
 intros.
 inversion H0. subst.
 specialize(eval_respect_vconv_imp2 _ _ _ _ e H5); intro HHa.
 specialize(eval_respect_vconv_imp2 _ _ _ _ e0 H7); intro HHb.
 specialize(eval_respect_vconv_imp2 _ _ _ _ e1 H9); intro HHc.
 specialize(eval_respect_vconv_imp2 _ _ _ _ e2 H10); intro HHd.
 specialize (eval_natrec_respect_vconv_imp _ _ _ _ _ _ _ _ v v0 HHa HHb HHc HHd e3 H11); intro HHe.
 easy.
 }
 5:{
 intros.
 inversion H0.
 }
 4:{
 intros.
 inversion H.
 }
 3:{
 intros.
 inversion H0. constructor.
 }
 2:{
 intros.
 inversion H0. constructor.
 }
 1:{
 intros.
 inversion H0. 
 + subst.
   rewrite e in H3.
   inversion H3.
   subst.
   apply vconv_refl.
 + subst. rewrite e in H3. easy.
 }
Qed.

Lemma synth_preserve_eval :
  forall Γ t A v,
    type_synth_closed t ->
    eval' Γ t v ->
    synth Γ t A ->
    vconv A v.
Proof.
  intros Γ t A v Hclosed Heval Hs.
  eapply (proj1 synth_preserve_eval_for_types); eauto.
Qed.

Lemma check_preserve_eval :
  forall Γ t A v,
    type_synth_closed t ->
    eval' Γ t v ->
    check Γ t A ->
    vconv A v.
Proof.
  intros Γ t A v Hclosed Heval Hc.
  eapply (proj2 synth_preserve_eval_for_types); eauto.
Qed.
