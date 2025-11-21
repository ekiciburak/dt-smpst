From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.

(* ----------------------------- *)
(* Locally-Nameless syntax       *)
(* ----------------------------- *)
Inductive term_ln : Type :=
  | t_bvar : nat -> term_ln        (* bound: de Bruijn index *)
  | t_fvar : string -> term_ln     (* free var (name) *)
  | t_Type : nat -> term_ln
  | t_Pi   : term_ln -> term_ln -> term_ln
  | t_Lam  : term_ln -> term_ln -> term_ln
  | t_App  : term_ln -> term_ln -> term_ln
  | t_Nat  : term_ln
  | t_Zero : term_ln
  | t_Succ : term_ln -> term_ln
  | t_NatRec_ln : term_ln -> term_ln -> term_ln -> term_ln -> term_ln.


(* ----------------------------- *)
(* open_rec / open / close_rec   *)
(* ----------------------------- *)
Fixpoint open_rec_ln (k : nat) (u : term_ln) (t : term_ln) : term_ln :=
  match t with
  | t_bvar n => if Nat.eqb n k then u else t_bvar n
  | t_fvar x => t_fvar x
  | t_Type i => t_Type i
  | t_Pi A B => t_Pi (open_rec_ln k u A) (open_rec_ln (S k) u B)
  | t_Lam A body => t_Lam (open_rec_ln k u A) (open_rec_ln (S k) u body)
  | t_App f a => t_App (open_rec_ln k u f) (open_rec_ln k u a)
  | t_Nat => t_Nat
  | t_Zero => t_Zero
  | t_Succ n => t_Succ (open_rec_ln k u n)
  | t_NatRec_ln P z s n =>
      t_NatRec_ln (open_rec_ln (S k) u P)
                  (open_rec_ln k u z)
                  (open_rec_ln (S (S k)) u s)
                  (open_rec_ln k u n)
  end.

Definition open_ln (t u : term_ln) := open_rec_ln 0 u t.

Fixpoint close_rec_ln (k : nat) (x : string) (t : term_ln) : term_ln :=
  match t with
  | t_bvar n => t_bvar n
  | t_fvar y => if String.eqb x y then t_bvar k else t_fvar y
  | t_Type i => t_Type i
  | t_Pi A B => t_Pi (close_rec_ln k x A) (close_rec_ln (S k) x B)
  | t_Lam A body => t_Lam (close_rec_ln k x A) (close_rec_ln (S k) x body)
  | t_App f a => t_App (close_rec_ln k x f) (close_rec_ln k x a)
  | t_Nat => t_Nat
  | t_Zero => t_Zero
  | t_Succ n => t_Succ (close_rec_ln k x n)
  | t_NatRec_ln P z s n =>
      t_NatRec_ln (close_rec_ln (S k) x P)
                  (close_rec_ln k x z)
                  (close_rec_ln (S (S k)) x s)
                  (close_rec_ln k x n)
  end.

Definition close_ln (x : string) (t : term_ln) := close_rec_ln 0 x t.

(* ----------------------------- *)
(* substitution for free names   *)
(* ----------------------------- *)
Fixpoint subst_ln (x : string) (u : term_ln) (t : term_ln) : term_ln :=
  match t with
  | t_bvar n => t_bvar n
  | t_fvar y => if String.eqb x y then u else t_fvar y
  | t_Type i => t_Type i
  | t_Pi A B => t_Pi (subst_ln x u A) (subst_ln x u B)
  | t_Lam A body => t_Lam (subst_ln x u A) (subst_ln x u body)
  | t_App f a => t_App (subst_ln x u f) (subst_ln x u a)
  | t_Nat => t_Nat
  | t_Zero => t_Zero
  | t_Succ n => t_Succ (subst_ln x u n)
  | t_NatRec_ln P z s n => t_NatRec_ln (subst_ln x u P) (subst_ln x u z) (subst_ln x u s) (subst_ln x u n)
  end.

(* ----------------------------- *)
(* locally-closed predicate       *)
(* ----------------------------- *)
Fixpoint lc_rec_ln (k : nat) (t : term_ln) : Prop :=
  match t with
  | t_bvar n => n < k
  | t_fvar _ => True
  | t_Type _ => True
  | t_Pi A B => lc_rec_ln k A /\ lc_rec_ln (S k) B
  | t_Lam A body => lc_rec_ln k A /\ lc_rec_ln (S k) body
  | t_App f a => lc_rec_ln k f /\ lc_rec_ln k a
  | t_Nat => True
  | t_Zero => True
  | t_Succ n => lc_rec_ln k n
  | t_NatRec_ln P z s n => lc_rec_ln (S k) P /\ lc_rec_ln k z /\ lc_rec_ln (S (S k)) s /\ lc_rec_ln k n
  end.

Definition lc_ln (t : term_ln) := lc_rec_ln 0 t.

Inductive value_ln : term_ln -> Prop :=
| V_Type_ln : forall i, value_ln (t_Type i)
| V_Nat_ln : value_ln t_Nat
| V_Pi_ln : forall A B, value_ln A -> value_ln B -> value_ln (t_Pi A B)
| V_Lam_ln : forall A b, value_ln A -> value_ln (t_Lam A b)  (* body not required *)
| V_Zero_ln : value_ln t_Zero
| V_Succ_ln : forall n, value_ln n -> value_ln (t_Succ n).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step_ln : term_ln -> term_ln -> Prop :=

  (* Beta: only when argument is a value; open the body with the actual value *)
| s_beta_ln : forall A b v,
    value_ln v ->
    step_ln (t_App (t_Lam A b) v) (open_ln b v)

  (* Congruence for application: reduce function part *)
| s_app1_ln : forall t1 t1' t2,
    step_ln t1 t1' ->
    step_ln (t_App t1 t2) (t_App t1' t2)

  (* Congruence for application: reduce argument only when function is a value *)
| s_app2_ln : forall v1 t2 t2',
    value_ln v1 ->
    step_ln t2 t2' ->
    step_ln (t_App v1 t2) (t_App v1 t2')

  (* Allow reduction of the annotation A on lambda if desired (weak semantics) *)
| s_lam_A_ln : forall A A' b,
    step_ln A A' ->
    step_ln (t_Lam A b) (t_Lam A' b)

  (* Succ congruence *)
| s_succ_ln : forall n n',
    step_ln n n' ->
    step_ln (t_Succ n) (t_Succ n')

  (* NatRec iota rules, binder-style for s:
     - t_NatRec_ln P z s t_Zero  --> z
     - t_NatRec_ln P z s (t_Succ n)  --> open_ln (open_ln s n) (t_NatRec_ln P z s n)
     Congruence rules reduce components and the scrutinee.
  *)
| s_rec_zero_ln : forall P z s,
    step_ln (t_NatRec_ln P z s t_Zero) z

| s_rec_succ_ln : forall P z s n,
    value_ln n ->
    step_ln (t_NatRec_ln P z s (t_Succ n))
            (open_ln (open_ln s n) (t_NatRec_ln P z s n))

| s_natrec_P_ln : forall P P' z s n,
    step_ln P P' ->
    step_ln (t_NatRec_ln P z s n) (t_NatRec_ln P' z s n)
| s_natrec_z_ln : forall P z z' s n,
    step_ln z z' ->
    step_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z' s n)
| s_natrec_s_ln : forall P z s s' n,
    step_ln s s' ->
    step_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s' n)
| s_natrec_n_ln : forall P z s n n',
    step_ln n n' ->
    step_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s n')

where "t '-->' t'" := (step_ln t t').

(* Reflexive-transitive closure (multi-step) *)
Inductive step_star_ln : term_ln -> term_ln -> Prop :=
| star_refl_ln : forall t, step_star_ln t t
| star_step_ln : forall t u v, step_ln t u -> step_star_ln u v -> step_star_ln t v.

(* helper: open_many opens innermost-first: open_many [a1;a2;a3] body = open_ln (open_ln (open_ln body a1) a2) a3 *)
Fixpoint open_many (args : list term_ln) (body : term_ln) : term_ln :=
  match args with
  | [] => body
  | a :: args' => open_many args' (open_ln body a)
  end.

(* ----------------------------- *)
(* Head β / iota reduction (LN)  *)
(* ----------------------------- *)
Inductive beta_head_ln : term_ln -> term_ln -> Prop :=
| b_beta_app_ln :
    forall A b s,
      beta_head_ln (t_App (t_Lam A b) s) (open_ln b s)
| b_natrec_zero_ln :
    forall P z s,
      beta_head_ln (t_NatRec_ln P z s t_Zero) z
| b_natrec_succ_ln :
    forall P z s n,
      beta_head_ln (t_NatRec_ln P z s (t_Succ n))
                    (open_ln (open_ln s n) (t_NatRec_ln P z s n)).

Infix "⇝ₕₗₙ" := beta_head_ln (at level 40, no associativity).

(* ----------------------------- *)
(* Full contextual β (LN)        *)
(* ----------------------------- *)
Reserved Notation "t '⇝ₗₙ' t'" (at level 40).

Inductive beta_ln : term_ln -> term_ln -> Prop :=
| beta_head_step_ln : forall t u, beta_head_ln t u -> beta_ln t u
| beta_pi_A_ln : forall A A' B, beta_ln A A' -> beta_ln (t_Pi A B) (t_Pi A' B)
| beta_pi_B_ln : forall A B B', beta_ln B B' -> beta_ln (t_Pi A B) (t_Pi A B')
| beta_lam_A_ln : forall A A' b, beta_ln A A' -> beta_ln (t_Lam A b) (t_Lam A' b)
| beta_lam_b_ln : forall A b b', beta_ln b b' -> beta_ln (t_Lam A b) (t_Lam A b')
| beta_app1_ln : forall t1 t1' t2, beta_ln t1 t1' -> beta_ln (t_App t1 t2) (t_App t1' t2)
| beta_app2_ln : forall t1 t2 t2', beta_ln t2 t2' -> beta_ln (t_App t1 t2) (t_App t1 t2')
| beta_succ_ln : forall n n', beta_ln n n' -> beta_ln (t_Succ n) (t_Succ n')

(* NatRec congruence *)
| beta_natrec_P_ln : forall P P' z s n,
    beta_ln P P' -> beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P' z s n)
| beta_natrec_z_ln : forall P z z' s n,
    beta_ln z z' -> beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z' s n)
| beta_natrec_s_ln : forall P z s s' n,
    beta_ln s s' -> beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s' n)
| beta_natrec_n_ln : forall P z s n n',
    beta_ln n n' -> beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s n')

where "t ⇝ₗₙ t'" := (beta_ln t t').

(* ----------------------------- *)
(* Definitional equality (convertibility)  *)
(* ----------------------------- *)
Definition convertible_ln : term_ln -> term_ln -> Prop :=
  clos_refl_sym_trans term_ln beta_ln.

Infix "≡ₗₙ" := convertible_ln (at level 70, no associativity).

From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* helpers: instantiate P and open bodies                              *)
(* ------------------------------------------------------------------ *)

(* apply P to index m and vector v: P_app P m v = open_many [v; m] P *)
Definition P_app (P : term_ln) (m v : term_ln) : term_ln := open_many [v; m] P.

(* For NatRec: instantiate s with (ih, m) where ih is recursive result, m is predecessor:
     s_inst s m ih = open_many [ih; m] s
   (we open innermost-first so ih substitutes bvar0, m substitutes bvar1)
*)
Definition s_inst (s : term_ln) (m ih : term_ln) : term_ln := open_many [ih; m] s.

(* ------------------------------------------------------------------ *)
(* Contexts (names -> types)                                           *)
(* ------------------------------------------------------------------ *)
Definition ctx_ln := list (string * term_ln).

Fixpoint lookup_ln (Γ : ctx_ln) (x : string) : option term_ln :=
  match Γ with
  | [] => None
  | (y,T)::Γ' => if String.eqb x y then Some T else lookup_ln Γ' x
  end.

Definition extend (Γ : ctx_ln) (x : string) (T : term_ln) : ctx_ln := (x,T) :: Γ.

Definition fresh (x : string) (Γ : ctx_ln) : Prop := ~ In x (map fst Γ).

Definition P_app1 (P : term_ln) (m : term_ln) : term_ln := open_many [m] P.

Definition s_expected_type_for_P (P : term_ln) : term_ln :=
  t_Pi t_Nat (t_Pi (open_ln P (t_bvar 0)) (open_ln P (t_Succ (t_bvar 0)))).

Inductive has_type_ln : ctx_ln -> term_ln -> term_ln -> Prop :=

  (* variable *)
| ty_var : forall Gamma x T,
    lookup_ln Gamma x = Some T ->
    has_type_ln Gamma (t_fvar x) T

  (* universes *)
| ty_Type : forall Gamma i,
    has_type_ln Gamma (t_Type i) (t_Type (S i))

  (* Pi formation *)
| ty_Pi : forall Gamma A B i j,
    has_type_ln Gamma A (t_Type i) ->
    (forall x, fresh x Gamma ->
               has_type_ln ((x, A) :: Gamma) (open_ln B (t_fvar x)) (t_Type j)) ->
    has_type_ln Gamma (t_Pi A B) (t_Type (Nat.max i j))

  (* Lambda *)
| ty_Lam : forall Gamma A b B i,
    has_type_ln Gamma A (t_Type i) ->
    (forall x, fresh x Gamma ->
               has_type_ln ((x, A) :: Gamma) (open_ln b (t_fvar x)) (open_ln B (t_fvar x))) ->
    has_type_ln Gamma (t_Lam A b) (t_Pi A B)

  (* Application *)
| ty_App : forall Gamma t1 t2 A B,
    has_type_ln Gamma t1 (t_Pi A B) ->
    has_type_ln Gamma t2 A ->
    has_type_ln Gamma (t_App t1 t2) (open_ln B t2)

  (* Natural numbers *)
| ty_Nat : forall Gamma,
    has_type_ln Gamma t_Nat (t_Type 0)

| ty_Zero : forall Gamma,
    has_type_ln Gamma t_Zero t_Nat

| ty_Succ : forall Gamma n,
    has_type_ln Gamma n t_Nat ->
    has_type_ln Gamma (t_Succ n) t_Nat

| ty_NatRec : forall Gamma P z s n,
  (* P is a family Nat -> Type_k *)
  (exists k, forall Gprime (m_name:string),
      fresh m_name Gprime ->
        has_type_ln ((m_name, t_Nat) :: Gprime)
                    (open_ln P (t_fvar m_name))
                    (t_Type k)) ->
  (* z : P[Zero] *)
  has_type_ln Gamma z (P_app1 P t_Zero) ->
  (* s : forall m:Nat, forall ih : P[m], P[Succ m] *)
  (forall Gprime (m_name:string),
     fresh m_name Gprime ->
       forall ih_name, fresh ih_name ((m_name, t_Nat) :: Gprime) ->
         has_type_ln
           ((m_name, t_Nat) :: (ih_name, open_ln P (t_fvar m_name)) :: Gprime)
           (open_ln (open_ln s (t_fvar m_name)) (t_fvar ih_name))
           (open_ln P (t_Succ (t_fvar m_name)))) ->
  has_type_ln Gamma n t_Nat ->
  has_type_ln Gamma (t_NatRec_ln P z s n) (P_app1 P n)

| ty_conv :
    forall Γ t A B,
      has_type_ln Γ t A ->
      convertible_ln A B ->
      has_type_ln Γ t B.

Require Import Coq.Program.Equality.

Lemma fresh_commute: forall G1 G2 a y V x U,
  fresh a (G1 ++ (y, V) :: (x, U) :: G2) ->
  fresh a (G1 ++ (x, U) :: (y, V) :: G2).
Proof. intro G1.
       induction G1; intros.
       - simpl. simpl in H.
         case_eq G2; intros.
         + subst. unfold fresh, not in *.
           intro Hfr.
           apply H. inversion Hfr. subst. 
           simpl. right. left. easy.
           inversion H0. subst.
           simpl. left. easy.
           inversion H1. 
         + subst. unfold fresh, not in *.
           intro Hfr. apply H. inversion Hfr.
           subst. simpl. right. left. easy.
           inversion H0. subst. simpl. left. easy.
           inversion H1. simpl. right. right. left. easy.
           simpl. right. right. right. easy.
       - unfold fresh, not in *.
         intro Hfr. apply H.
         inversion Hfr. subst. simpl. left. easy. 
         simpl. right.
         rewrite map_app in H0.
         apply in_app_or in H0.
         destruct H0 as [H0 | H0].
         rewrite map_app.
         apply in_or_app. left. easy.
         rewrite map_app.
         apply in_or_app. right.
         inversion H0. subst. simpl. right. left. easy.
         inversion H1. subst. simpl. left. easy.
         simpl. right. right. easy.
Qed.

Lemma fresh_not: forall G1 G2 a x U y V,
  fresh a (G1 ++ (x, U) :: (y, V) :: G2) ->
  a <> y /\ a <> x /\ ~In a (map fst G1) /\ ~In a (map fst G2).
Proof. intros.
       unfold fresh in *.
       unfold not in *.
       split.
       - intro Hf. apply H. subst.
         rewrite map_app.
         apply in_or_app. right. simpl. right. left.
         easy.
       - split. intro Hf.
         apply H. 
         rewrite map_app.
         apply in_or_app. right. simpl. left.
         easy.
         split.
         + intro Hf. apply H.
           rewrite map_app.
           apply in_or_app. left. easy.
         + intro Hf. apply H.
           rewrite map_app.
           apply in_or_app. right. simpl. right. right. easy.
Qed.

Lemma fresh_not_2: forall G2 a y V,
  fresh a ((y, V) :: G2) ->
  a <> y /\ ~In a (map fst G2).
Proof. intros.
       unfold fresh in *.
       unfold not in *.
       split.
       - intro Hf. apply H. subst. simpl. left. easy.
       - intro Hf. apply H. simpl. right. easy.
Qed.

Lemma fresh_dtop: forall G1 G2 a A y,
  y <> a ->
  fresh y (G1 ++ G2)->
  fresh y (((a, A) :: G1) ++ G2).
Proof. intros.
       unfold fresh, not in *.
       intro Hf. apply H0.
       inversion Hf. simpl in H1. subst. easy.
       easy.
Qed.

Lemma lookup_comm: forall G1 G2 a x U y V T,
  x <> y ->
  lookup_ln (G1 ++ (x, U) :: (y, V) :: G2) a = Some T ->
  lookup_ln (G1 ++ (y, V) :: (x, U) :: G2) a = Some T.
Proof. intro G1.
       induction G1; intros.
       - simpl. simpl in H0.
         case_eq((a =? x)%string); intros.
         + rewrite H1 in H0. inversion H0. subst.
           case_eq((a =? y)%string ); intros.
           * rewrite String.eqb_eq in H1, H2. subst. easy.
           * easy.
         + rewrite H1 in H0. easy.
       - simpl. simpl in H0. destruct a.
         case_eq((a0 =? s)%string); intros.
         + rewrite H1 in H0. easy.
         + rewrite H1 in H0. apply IHG1; easy.
Qed.

Lemma fresh_no_lookup: forall G a T,
  lookup_ln G a = Some T ->
  fresh a G -> False.
Proof. intro G.
       induction G; intros.
       - simpl in H. easy.
       - apply IHG with (a := a0) (T := T).
         simpl in H. destruct a.
         case_eq((a0 =? s)%string); intros.
         rewrite String.eqb_eq in H1. subst.
         apply fresh_not_2 in H0. easy.
         rewrite H1 in H. easy.
         destruct a.
         apply fresh_not_2 in H0. easy.
Qed.

Lemma fresh_commute_middle :
  forall Gamma1 Gamma2 t T x U y V,
    x <> y ->
    fresh x (Gamma1 ++ Gamma2) ->
    fresh y (Gamma1 ++ Gamma2) ->
    has_type_ln (Gamma1 ++ (x, U) :: (y, V) :: Gamma2) t T ->
    has_type_ln (Gamma1 ++ (y, V) :: (x, U) :: Gamma2) t T.
Proof. intros.
       remember (Gamma1 ++ (x, U) :: (y, V) :: Gamma2) as G.
       revert HeqG. revert x U H H0. revert y V H1. revert Gamma1 Gamma2.
       induction H2; intros. 
       4: { apply ty_Lam with (i := i).
            apply IHhas_type_ln; try easy.
            intros.
            assert(fresh x0 (Gamma1 ++ (x, U) :: (y, V) :: Gamma2)).
            { apply fresh_commute. easy. }
            assert(fresh y (((x0, A) :: Gamma1) ++ Gamma2)).
            { apply fresh_not in H6.
              apply fresh_dtop. easy. easy.
            }
            subst.
            specialize(H0 x0 H6 ((x0, A) :: Gamma1) Gamma2 y V H7 x U H3).
            simpl in H0.
            apply H0.
            apply fresh_not in H6.
            apply fresh_dtop. easy. easy.
            easy.
          }
       9: { apply ty_conv with (A := A); try easy.
            apply IHhas_type_ln; try easy.
          }
       8: { subst.
            destruct H as (k, H).
            apply ty_NatRec. unfold P_app1, s_expected_type_for_P in *. simpl in *.
            exists k. subst.
            intros. apply H. easy.
            apply IHhas_type_ln1. easy. easy. easy. easy.
            intros.
            apply H0. easy. easy.
            apply IHhas_type_ln2; easy.
           }
        3: { subst.
             constructor. apply IHhas_type_ln; easy.
             intros.
              assert(fresh x0 (Gamma1 ++ (x, U) :: (y, V) :: Gamma2)).
              { apply fresh_commute. easy. }
              assert(fresh y (((x0, A) :: Gamma1) ++ Gamma2)).
              { apply fresh_not in H6.
                apply fresh_dtop. easy. easy.
              }
              subst.
              specialize(H0 x0 H6 ((x0, A) :: Gamma1) Gamma2 y V H7 x U H3).
              simpl in H0.
              apply H0.
              apply fresh_not in H6.
              apply fresh_dtop. easy. easy. easy.
            }
         2: { constructor. }
         2: { apply ty_App with (A := A).
              apply IHhas_type_ln1; easy.
              apply IHhas_type_ln2; easy.
            }
         1: { constructor. subst.
              erewrite lookup_comm; eauto.
            }
         1: { constructor. }
         1: { constructor. }
         1: { constructor. subst.
              apply IHhas_type_ln; easy.
            }
Qed.

Lemma weakening_fresh :
  forall Γ t T x U,
    fresh x Γ ->
    has_type_ln Γ t T ->
    has_type_ln ((x, U) :: Γ) t T.
Proof. intros. revert x H U.
       induction H0; intros.
       10:{ apply ty_conv with (A := A). apply IHhas_type_ln; try easy. easy. }
       4: { apply ty_Lam with (i := i).
            apply IHhas_type_ln. easy.
            intros.
            specialize (fresh_commute_middle nil Gamma (open_ln b (t_fvar x0)) (open_ln B (t_fvar x0))); intros Ha.
            simpl in Ha. apply Ha.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3. easy. easy.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3. easy.
            apply H1.
            apply fresh_not_2 in H3. easy.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3.
            unfold fresh, not in H2.
            unfold fresh, not.
            intro HH. apply H2.
            simpl in HH. destruct HH; easy.
          }
       8: { constructor.
            destruct H as (k, H). exists k.
            intros. apply H. easy.
            apply IHhas_type_ln1. easy. easy.
            apply IHhas_type_ln2. easy.
          }
       3: { constructor.
            apply IHhas_type_ln; easy.
            intros.
            specialize (fresh_commute_middle nil Gamma (open_ln B (t_fvar x0)) (t_Type j)); intros Ha.
            apply Ha.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3. easy. easy. simpl.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3. easy.
            simpl.
            apply H1.
            apply fresh_not_2 in H3. easy.
            pose proof H3 as H3a.
            apply fresh_not_2 in H3.
            unfold fresh, not in H2.
            unfold fresh, not.
            intro HH. apply H2.
            simpl in HH. destruct HH; easy.
          }
       3: { apply ty_App with (A := A).
            apply IHhas_type_ln1; easy.
            apply IHhas_type_ln2; easy.
          }
       5: { constructor. apply IHhas_type_ln; easy. }
       4: { constructor. }
       3: { constructor. }
       2: { constructor. }
       1: { subst.  constructor.
            case_eq((x =? x0)%string); intros.
            + rewrite String.eqb_eq in H1. subst. simpl.
              apply fresh_no_lookup in H. easy.
              easy.
            + simpl. rewrite H1. easy.
          }
Qed.

