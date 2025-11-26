From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.

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
(*       beta_head_ln (t_NatRec_ln P z s (t_Succ n))
                   (t_App (t_App s n) (t_NatRec_ln P z s n)). *)
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


Lemma convertible_refl : forall x, convertible_ln x x.
Proof. unfold convertible_ln; intros. 
Search clos_refl_sym_trans. apply rst_refl. Qed.

Lemma convertible_sym : forall x y, convertible_ln x y -> convertible_ln y x.
Proof. intros; unfold convertible_ln in *. apply rst_sym. easy. Qed.

Lemma convertible_trans : forall x y z, convertible_ln x y -> convertible_ln y z -> convertible_ln x z.
Proof. intros; unfold convertible_ln in *. apply rst_trans with (y:= y); easy. Qed.


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


(* Definition extend (Γ : ctx_ln) (x : string) (T : term_ln) : ctx_ln := (x,T) :: Γ. *)

Definition shift_open (d : nat) (P x : term_ln) : term_ln :=
  open_rec_ln d x P.

Definition body_of_P (P : term_ln) : term_ln :=
  match P with
  | t_Lam _ body => body
  | _ => open_ln P (t_bvar 0)   (* treat P as if it were abstracted over a Nat *)
  end.

Definition P_open (d : nat) (P : term_ln) (x : term_ln) : term_ln :=
  shift_open d (body_of_P P) x.   (* pseudo; implement with your existing open/shift *)

(* apply P to a numeral m *)
Definition P_app1 (P : term_ln) (m : term_ln) : term_ln :=
  open_ln (body_of_P P) m.

Definition s_expected_type_for_P (P : term_ln) : term_ln :=
  t_Pi t_Nat
    (t_Pi (P_open 1 P (t_bvar 1))  (* ih : P m where m is bvar 1 inside the inner pi *)
          (P_open 1 P (t_Succ (t_bvar 1)))).

(* Definition s_expected_type_for_P (P : term_ln) : term_ln :=
  t_Pi t_Nat
    (t_Pi (open_ln (body_of_P P) (t_bvar 1))    (* ih : P m  -- m is t_bvar 1 here *)
          (open_ln (body_of_P P) (t_Succ (t_bvar 1)))). *)

Fixpoint insert_at {A : Type} (n : nat) (x : A) (Γ : list A) : list A :=
  match n, Γ with
  | 0, _ => x :: Γ
  | S n', g :: Γ' => g :: insert_at n' x Γ'
  | S _, [] => [x]          (* if n is larger than the length, append at end *)
  end.

Definition ctx_ln := list (string * term_ln).

Fixpoint lookup_ln (Γ : ctx_ln) (x : string) : option term_ln :=
  match Γ with
  | [] => None
  | (y,T)::Γ' => if String.eqb x y then Some T else lookup_ln Γ' x
  end.

Definition fresh (x : string) (Γ : ctx_ln) : Prop := ~ In x (map fst Γ).


(* cofinite-style typing judgment *)
Inductive has_type_ln : ctx_ln -> term_ln -> term_ln -> Prop :=

  (* variable *)
| ty_var : forall Gamma x T,
    lookup_ln Gamma x = Some T ->
    has_type_ln Gamma (t_fvar x) T

  (* universes *)
| ty_Type : forall Gamma i,
    has_type_ln Gamma (t_Type i) (t_Type (S i))

  (* Pi formation (cofinite) *)
| ty_Pi : forall Gamma A B i j L,
    has_type_ln Gamma A (t_Type i) ->
    (forall x, ~ In x L ->
               has_type_ln ((x, A) :: Gamma) (open_ln B (t_fvar x)) (t_Type j)) ->
    has_type_ln Gamma (t_Pi A B) (t_Type (Nat.max i j))

  (* Lambda (cofinite) *)
| ty_Lam : forall Gamma A b B i L,
    has_type_ln Gamma A (t_Type i) ->
    (forall x, ~ In x L ->
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

| ty_NatRec_strong : forall Gamma P body z s n k L,
    has_type_ln Gamma P (t_Pi t_Nat (t_Type k)) -> 
    convertible_ln P (t_Lam t_Nat body) ->
    (forall x, ~ In x L ->
               has_type_ln ((x, t_Nat) :: Gamma)
                           (open_ln body (t_fvar x))
                           (open_ln (t_Type k) (t_fvar x))) ->
    (* base: z : P 0 = body[0 := Zero] *) 
    has_type_ln Gamma z (open_rec_ln 0 t_Zero body) -> 
    (* step: s : Π (m:Nat). Π (ih : P m), P (S m) *)
    has_type_ln Gamma s
      (t_Pi t_Nat
            (t_Pi (open_rec_ln 0 (t_bvar 1) body)
                  (open_rec_ln 0 (t_Succ (t_bvar 1)) body))) ->
    has_type_ln Gamma n t_Nat -> 
    has_type_ln Gamma (t_NatRec_ln P z s n) (open_rec_ln 0 n body)

| ty_conv : forall Γ t A B,
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
    ~ In x (map fst (Gamma1 ++ Gamma2)) ->
    ~ In y (map fst (Gamma1 ++ Gamma2)) ->
    has_type_ln (Gamma1 ++ (x, U) :: (y, V) :: Gamma2) t T ->
    has_type_ln (Gamma1 ++ (y, V) :: (x, U) :: Gamma2) t T.
Proof. intros.
       remember (Gamma1 ++ (x, U) :: (y, V) :: Gamma2) as G.
       revert HeqG. revert x U H H0. revert y V H1. revert Gamma1 Gamma2.
       induction H2; intros. 
       4: { apply ty_Lam with (i := i) (L := (x::y::L)).
            apply IHhas_type_ln; try easy.
            
            intros. subst.
            assert(~ In x0 L).
            { unfold not. intros. apply H5. simpl. right. right. easy. }
            specialize(H0 x0 H6 ((x0, A) :: Gamma1) Gamma2).
            simpl in H0. apply H0.
            unfold not. intros.
            destruct H7. subst. apply H5. simpl. right. left. easy.
            easy. easy.
            unfold not. intros. destruct H7. subst.
            apply H5. simpl. left. easy. easy.
            easy. 
          }
       9: { apply ty_conv with (A := A); try easy.
            apply IHhas_type_ln; try easy.
          }
       8: { subst.
            apply ty_NatRec_strong with (k := k) (L := (x::y::L)). unfold P_app1, s_expected_type_for_P in *. cbn in *.
            eapply IHhas_type_ln1. easy. easy. easy. easy. easy.
            intros. 
            specialize(H1 x0).
            assert(~ In x0 L).
            { unfold not. intros. apply H5. simpl. right. right. easy. }
            specialize(H1 H6 ((x0, t_Nat) :: Gamma1) Gamma2).
            simpl in H1.
            apply H1.
            unfold not. intros.
            destruct H7. subst. apply H5. simpl. right. left. easy.
            easy. easy.
            unfold not. intros. destruct H7. subst.
            apply H5. simpl. left. easy. easy.
            easy. 
            apply IHhas_type_ln2. 
            easy. easy. easy. easy.
            intros.
            apply IHhas_type_ln3; easy.
            apply IHhas_type_ln4; easy.
           }
        3: { subst.
             apply ty_Pi with (L := (x::y::L)).
             apply IHhas_type_ln; easy.
             intros.
             assert(~ In x0 L).
             { unfold not. intros. apply H5. simpl. right. right. easy. }
             specialize(H0 x0 H6 ((x0, A) :: Gamma1) Gamma2).
             simpl in H0. apply H0.
             unfold not. intros.
             destruct H7. subst. apply H5. simpl. right. left. easy.
             easy. easy.
             unfold not. intros. destruct H7. subst.
             apply H5. simpl. left. easy. easy.
             easy. 
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

Inductive ctx_sub: ctx_ln -> ctx_ln -> Prop :=
| ctx_sub_refl : forall Γ, ctx_sub Γ Γ
| ctx_sub_insert :
    forall Γ Γ1 Γ2 b,
      ctx_sub Γ (Γ1 ++ Γ2) ->
      fresh (fst b) (Γ1 ++ Γ2) ->
      ctx_sub Γ (Γ1 ++ b :: Γ2).

Lemma ctx_sub_weaken_head :
  forall Γ Γ' x U,
    ctx_sub Γ Γ' ->
    fresh x Γ' ->
    ctx_sub ((x, U) :: Γ) ((x, U) :: Γ').
Proof.
  intros. revert x U H0.
  dependent induction H; intros.
  - (* refl *) constructor.
  - simpl.
    assert(((x, U) :: Γ1 ++ b :: Γ2) = (((x, U) :: Γ1) ++ (b :: Γ2))). easy.
    rewrite H2.
    constructor. apply IHctx_sub.
    admit.
    destruct b.
    simpl in *.
    admit.
Admitted.

Lemma weakening_fresh :
  forall Γ t T x U,
     ~ In x (map fst Γ) ->
    has_type_ln Γ t T ->
    has_type_ln ((x, U) :: Γ) t T.
Proof. intros. revert x H U.
       induction H0; intros.
       10:{ apply ty_conv with (A := A). apply IHhas_type_ln; try easy. easy. }
       4: { apply ty_Lam with (i := i) (L := x::L++(map fst Gamma)).
            apply IHhas_type_ln. easy.
            intros.
            assert( ~ In x0 L).
            { unfold not. intros. apply H3. simpl. right.
              apply in_app_iff. left. easy. }
            specialize(H1 x0 H4 x).
            assert(~ In x (map fst ((x0, A) :: Gamma))).
            { simpl. unfold not. intros. apply H3. simpl.
              destruct H5. left. easy.
              right. apply in_app_iff. right. easy.
            }
            specialize(H1 H5).
            specialize (fresh_commute_middle nil Gamma (open_ln b (t_fvar x0)) (open_ln B (t_fvar x0))); intros Ha.
            simpl in Ha.
            apply Ha.
            unfold not. intros. apply H3. simpl. left. easy. easy.
            unfold not. intros. apply H3. simpl. right.
            apply in_app_iff. right. easy.
            easy.
          }
       8: { apply ty_NatRec_strong with (k := k) (L := x::L++(map fst Gamma)).
            apply IHhas_type_ln1. easy. easy.
            intros.
            assert( ~ In x0 L).
            { unfold not. intros. apply H3. simpl. right.
              apply in_app_iff. left. easy. }
            specialize(H1 x0 H4 x).
            assert( ~ In x (map fst ((x0, t_Nat) :: Gamma))).
            { simpl. unfold not. intros. apply H3. simpl.
              destruct H5. left. easy.
              right. apply in_app_iff. right. easy.
            }
            specialize(H1 H5).
            specialize (fresh_commute_middle nil); intros Ha.
            simpl in Ha.
            apply Ha.
            unfold not. intros. apply H3. simpl. left. easy. easy.
            unfold not. intros. apply H3. simpl. right.
            apply in_app_iff. right. easy.
            easy.
            apply IHhas_type_ln2. easy.
            apply IHhas_type_ln3. easy.
            apply IHhas_type_ln4. easy.
          }
       3: { apply ty_Pi with (i := i) (L := x::L++(map fst Gamma)).
            apply IHhas_type_ln. easy.
            intros.
            assert( ~ In x0 L).
            { unfold not. intros. apply H3. simpl. right.
              apply in_app_iff. left. easy. }
            specialize(H1 x0 H4 x).
            assert(~ In x (map fst ((x0, A) :: Gamma))).
            { simpl. unfold not. intros. apply H3. simpl.
              destruct H5. left. easy.
              right. apply in_app_iff. right. easy.
            }
            specialize(H1 H5).
            specialize (fresh_commute_middle nil); intros Ha.
            apply Ha.
            unfold not. intros. apply H3. simpl. left. easy. easy.
            unfold not. intros. apply H3. simpl. right.
            apply in_app_iff. right. easy. simpl.
            easy.
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

Definition P_const : term_ln := t_Lam t_Nat t_Nat.
Definition s_add : term_ln := t_Lam t_Nat (t_Lam t_Nat (t_Succ (t_bvar 0))).

Definition add_ln : term_ln :=
  t_Lam t_Nat (
    t_Lam t_Nat (
      t_NatRec_ln P_const (t_bvar 0) s_add (t_bvar 1)
    )
  ).

Lemma add_ln_typing :
  has_type_ln [] add_ln (t_Pi t_Nat (t_Pi t_Nat t_Nat)).
Proof.
  unfold add_ln.
  eapply ty_Lam with (L := []).
  - apply ty_Nat.
  - intros n_name Hfresh_n.
    eapply ty_Lam with (L := []).
    + apply ty_Nat.
    + intros m_name Hfresh_m. cbn.
      eapply ty_NatRec_strong
            with (k := 0)
                 (P := t_Lam t_Nat t_Nat)     (* P_const *)
                 (body := t_Nat)              (* the body of P_const *)
                 (z := t_fvar m_name)         (* base case uses the local var m *)
                 (s := s_add)                 (* step function *)
                 (n := t_fvar n_name)
                 (L := []).        (* recursion argument = local var n *)
      cbn.
      apply ty_Lam with (i := 0) (L := []).
      apply ty_Nat.
      intros.
      cbn.
      apply ty_Nat.
      cbn. 
      apply convertible_refl.
      
      intros. cbn.
      apply ty_Nat.
      apply ty_var. simpl. rewrite String.eqb_refl. easy.
      
      intros.
      cbn.
      unfold s_expected_type_for_P. cbn.
      apply ty_Lam with (i := 0) (L := []).
      constructor.
      intros.
      cbn.
      apply ty_Lam with (i := 0) (L := []).
      constructor.
      intros.
      cbn.
      constructor. 
      cbn.
      apply ty_var. simpl. rewrite String.eqb_refl. easy.
      apply ty_var. simpl. rewrite String.eqb_refl.
      destruct((n_name =? m_name)%string); easy.
Qed.

Require Import Lia.

Lemma cl_larger: forall v k u, 
  Nat.le k u -> 
  lc_rec_ln k v -> 
  lc_rec_ln u v.
Proof. intro t.
       induction t; intros.
       10:{ simpl. inversion H0. split.
            apply IHt1 with (k := (S k)). lia. easy.
            split. apply IHt2 with (k := k). lia. easy.
            split. apply IHt3 with (k := (S (S k))). lia. easy.
            apply IHt4 with (k := k). lia. easy.
          }
       9: { apply IHt with (k := k). lia. easy. }
       8: { simpl. easy. }
       7: { simpl. easy. }
       6: { simpl. inversion H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       5: { simpl. inversion H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       4: { simpl. inversion H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       3: { simpl. easy. }
       2: { simpl. easy. }
       1: { simpl. inversion H0. subst. lia. lia. }
Qed.

Lemma open_rec_ln_noop_on_lc :
  forall v k w,
    lc_rec_ln k v ->
    open_rec_ln k w v = v.
Proof.
  intro v.
  induction v; intros; simpl in *; try reflexivity.
  -  destruct (Nat.eqb n k) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia. (* contradicts n < k *)
    + reflexivity.
  - (* t_Pi *) destruct H as [H1 H2]. rewrite IHv1, IHv2; try easy.
  - (* t_Lam *) destruct H as [H1 H2].  rewrite IHv1, IHv2; try easy.
  - (* t_App *) destruct H as [H1 H2].  rewrite IHv1, IHv2; try easy.
  - (* t_Succ *) rewrite IHv; easy.
  - (* t_NatRec_ln *)
    destruct H as [HP [Hz [Hs Hn]]].
    rewrite IHv1, IHv2, IHv3, IHv4; try easy.
Qed.

Lemma open_subst_commute: forall t x u k v,
  lc_rec_ln k u ->
  subst_ln x u (open_rec_ln k v t) =
  open_rec_ln k (subst_ln x u v) (subst_ln x u t).
Proof. intro t.
       induction t; intros.
       10:{ simpl. rewrite IHt1, IHt2, IHt3, IHt4; try easy.
            apply cl_larger with (k := k). lia. easy.
            apply cl_larger with (k := k). lia. easy.
          }
       9: { simpl. rewrite IHt. easy. easy. }
       8: { simpl. easy. }
       7: { simpl. easy. }
       6: { simpl. rewrite IHt1, IHt2. easy. easy. easy. }
       5: { simpl. rewrite IHt1, IHt2. easy.
            apply cl_larger with (k := k). lia. easy. easy.
          }
       4: { simpl. rewrite IHt1, IHt2. easy. 
            apply cl_larger with (k := k). lia. easy. easy. 
          }
       3: { simpl. easy. }
       2: { simpl.
            case_eq((x =? s)%string); intros.
            + simpl.
              rewrite open_rec_ln_noop_on_lc. easy. easy.
            + simpl. easy.
          }
       1: { simpl.
            case_eq( n =? k); intros.
            + easy.
            + simpl. easy.
          }
Qed.

Lemma convertible_subst : forall A B x v,
  lc_rec_ln 0 v ->
  A ≡ₗₙ B -> 
  subst_ln x v A ≡ₗₙ subst_ln x v B.
Proof. intros. revert x v H.
       induction H0; intros.
       - induction H; intros.
         + induction H; intros. simpl. constructor. constructor.
           unfold open_ln. rewrite open_subst_commute; try easy.
           constructor.
           simpl. constructor. constructor. constructor.
           simpl. constructor. constructor. simpl.
           unfold open_ln.
(*            constructor. *)
           rewrite open_subst_commute; try easy.
           rewrite open_subst_commute; try easy.
           constructor.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_pi_A_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_Pi y (subst_ln x0 v B)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_pi_B_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_Pi (subst_ln x0 v A) y); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_lam_A_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_Lam y (subst_ln x0 v b)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_lam_b_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_Lam (subst_ln x0 v A) y); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_app1_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_App y (subst_ln x0 v t2)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_app2_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_App (subst_ln x0 v t1) y); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_succ_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_Succ y); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_natrec_P_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_NatRec_ln y (subst_ln x0 v z) (subst_ln x0 v s) (subst_ln x0 v n)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_natrec_z_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_NatRec_ln (subst_ln x0 v P) y (subst_ln x0 v s) (subst_ln x0 v n)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_natrec_s_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_NatRec_ln (subst_ln x0 v P) (subst_ln x0 v z) y (subst_ln x0 v n)); easy.
         + cbn.
           induction IHbeta_ln; intros.
           ++ simpl. constructor. eapply beta_natrec_n_ln. easy.
           ++ simpl. apply convertible_refl.
           ++ apply convertible_sym. easy.
           ++ apply convertible_trans with (y := t_NatRec_ln (subst_ln x0 v P) (subst_ln x0 v z) (subst_ln x0 v s) y); easy.
       - apply convertible_refl.
       - apply convertible_sym. apply IHclos_refl_sym_trans. easy.
       - apply convertible_trans with (y := subst_ln x0 v y). 
         apply IHclos_refl_sym_trans1. easy.
         apply IHclos_refl_sym_trans2. easy.
Qed.


From Coq Require Import Strings.String Ascii.
From Coq Require Import Lists.List Arith.PeanoNat.
Import ListNotations.
(* Open Scope string_scope. *)

(* ------------------------- *)
(* basic helpers (if absent) *)
(* ------------------------- *)

Fixpoint str_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ t => S (str_length t)
  end.

Fixpoint repeat_ascii (n : nat) (c : ascii) : string :=
  match n with
  | 0 => EmptyString
  | S n' => String c (repeat_ascii n' c)
  end.

(* max length of names in Γ *)
Definition max_len_of_fsts (Γ : list (string * term_ln)) : nat :=
  fold_right (fun '(z, _) acc => Nat.max (str_length z) acc) 0 Γ.

(* candidate that is strictly longer than both the names in Γ and the string x *)
Definition fresh_candidate_not_eq (Γ : list (string * term_ln)) (x : string) : string :=
  let m := Nat.max (max_len_of_fsts Γ) (str_length x) in
  repeat_ascii (S m) (Ascii.ascii_of_nat 97).  (* 'a' *)

(* ------------------------- *)
(* elementary lemmas         *)
(* ------------------------- *)

Lemma str_length_repeat_ascii :
  forall n c, str_length (repeat_ascii n c) = n.
Proof. induction n; simpl; auto. Qed.

Lemma str_length_in_map_le_max :
  forall Γ s,
    In s (map fst Γ) ->
    str_length s <= max_len_of_fsts Γ.
Proof.
  intros Γ s Hin.
  unfold max_len_of_fsts.
  generalize dependent s.
  induction Γ as [| [z U] Γ' IH]; simpl; intros; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + subst s. apply Nat.le_max_l.
    + apply Nat.le_trans with (m := fold_right (fun '(z, _) acc => Nat.max (str_length z) acc) 0 Γ').
      * apply IH; assumption.
      * apply Nat.le_max_r.
Qed.

Lemma candidate_longer_than_any_and_x :
  forall Γ x s,
    In s (map fst Γ) ->
    str_length (fresh_candidate_not_eq Γ x) > str_length s.
Proof.
  intros Γ x s Hin.
  unfold fresh_candidate_not_eq.
  set (m := Nat.max (max_len_of_fsts Γ) (str_length x)).
  rewrite str_length_repeat_ascii.
  simpl.
  apply Nat.lt_succ_r.
  apply Nat.le_trans with (m := max_len_of_fsts Γ).
  - apply str_length_in_map_le_max; assumption.
  - apply Nat.le_max_l.
Qed.

Lemma candidate_not_eq_x :
  forall Γ x,
    str_length (fresh_candidate_not_eq Γ x) > str_length x.
Proof.
  intros Γ x.
  unfold fresh_candidate_not_eq.
  set (m := Nat.max (max_len_of_fsts Γ) (str_length x)).
  rewrite str_length_repeat_ascii.
  simpl.
  apply Nat.lt_succ_r.
  apply Nat.le_max_r.
Qed.

(* ------------------------- *)
(* main existence lemma      *)
(* ------------------------- *)

Lemma exists_fresh_not_eq :
  forall (Γ : list (string * term_ln)) (x : string),
    exists y, ~ In y (map fst Γ) /\ y <> x.
Proof.
  intros Γ x.
  set (y := fresh_candidate_not_eq Γ x).
  exists y.
  split.
  - (* y ∉ map fst Γ *)
    intros Hin.
    eapply Nat.lt_irrefl.
    apply (candidate_longer_than_any_and_x Γ x y).
    exact Hin.
  - (* y <> x because length(y) > length(x) *)
    intro Heq.
    apply (f_equal str_length) in Heq.
    unfold y in *.
    specialize (candidate_not_eq_x Γ x); intros. lia.
Qed.

(* --- free-variable function --- *)
Fixpoint fv_ln (t : term_ln) : list string :=
  match t with
  | t_bvar _ => []
  | t_fvar x => [x]
  | t_Type _ => []
  | t_Pi A B => fv_ln A ++ fv_ln B
  | t_Lam A b => fv_ln A ++ fv_ln b
  | t_App f a => fv_ln f ++ fv_ln a
  | t_Nat => []
  | t_Zero => []
  | t_Succ n => fv_ln n
  | t_NatRec_ln P z s n => fv_ln P ++ fv_ln z ++ fv_ln s ++ fv_ln n
  end.

Definition notin_fv (x : string) (t : term_ln) : Prop := ~ In x (fv_ln t).

(* rename free var x -> y by substituting (t_fvar y) for x *)
Definition rename_ln (x y : string) (t : term_ln) : term_ln :=
  subst_ln x (t_fvar y) t.

Definition rename_ctx (x y : string) (Γ : ctx_ln) : ctx_ln :=
  map (fun '(z, T) => (if String.eqb z x then (y, T) else (z, T))) Γ.

Definition fv_ctx (Γ : ctx_ln) : list string :=
  fold_right (fun '(x, T) acc => x :: (fv_ln T ++ acc)) [] Γ.

Fixpoint subst_ctx (x : string) (v : term_ln) (Γ : list (string * term_ln))
  : list (string * term_ln) :=
  match Γ with
  | [] => []
  | (y, T) :: Γ' =>
      if String.eqb x y
      then (* drop this binding and keep the rest, substituting in the tail *)
         subst_ctx x v Γ'
      else (y, subst_ln x v T) :: subst_ctx x v Γ'
  end. 

Lemma ctx_subst_some: forall G x v x0 T,
     x <> x0 ->
     lookup_ln G x = Some T ->
     lookup_ln (subst_ctx x0 v G) x = Some (subst_ln x0 v T).
Proof. intro G.
       induction G; intros.
       - simpl in H0. easy.
       - simpl. destruct a. 
         case_eq((x0 =? s)%string); intros.
         + rewrite String.eqb_eq in H1. subst.
           apply IHG. easy. simpl in H0.
           apply String.eqb_neq in H. rewrite H in H0. easy.
         + simpl.
           case_eq((x =? s)%string); intros.
           ++ rewrite String.eqb_eq in H2. subst.
              simpl in H0. rewrite String.eqb_refl in H0. inversion H0. easy.
           ++ simpl in H0. rewrite H2 in H0.
              apply IHG with (v := v) (x0 := x0) in H0.
              easy. easy.
Qed.

Lemma subst_ln_notin_fv :
  forall t x v,
    ~ In x (fv_ln t) ->
    subst_ln x v t = t.
Proof. intro t.
       induction t; intros.
       10:{ cbn. rewrite IHt1, IHt2, IHt3, IHt4. easy.
            unfold not in *. intros.
            apply H. simpl. apply in_app_iff.
            right. apply in_app_iff. right. apply in_app_iff.
            right. easy.
            unfold not in *. intros.
            apply H. simpl. apply in_app_iff.
            right. apply in_app_iff. right. apply in_app_iff.
            left. easy.
            unfold not in *. intros.
            apply H. simpl. apply in_app_iff.
            right. apply in_app_iff. left. easy.
            unfold not in *. intros.
            apply H. simpl. apply in_app_iff.
            left. easy.
           }
        1: { simpl. easy. }
        1: { simpl. 
             assert(x <> s).
             { unfold not in *. intros. subst. apply H.
               simpl. left. easy.
             }
             apply String.eqb_neq in H0. rewrite H0. easy.
           }
        1: { simpl. easy. }
        1: { simpl. rewrite IHt1, IHt2. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. right. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. left. easy.
           }
        5: { simpl. rewrite IHt. easy.
             unfold not in *. intros.
             apply H. simpl. easy.
           }
        4: { simpl. easy. }
        3: { simpl. easy. }
        2: { simpl. rewrite IHt1, IHt2. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. right. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. left. easy.
           }
        1: { simpl. rewrite IHt1, IHt2. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. right. easy.
             unfold not in *. intros.
             apply H. simpl. apply in_app_iff. left. easy.
           }
Qed.

Definition swap_name (x y z : string) : string :=
  if String.eqb z x then y else if String.eqb z y then x else z.

Fixpoint swap_ln (x y : string) (t : term_ln) : term_ln :=
  match t with
  | t_bvar n => t_bvar n
  | t_fvar z => t_fvar (swap_name x y z)
  | t_Type i => t_Type i
  | t_Pi A B => t_Pi (swap_ln x y A) (swap_ln x y B)
  | t_Lam A b => t_Lam (swap_ln x y A) (swap_ln x y b)
  | t_App f a => t_App (swap_ln x y f) (swap_ln x y a)
  | t_Nat => t_Nat
  | t_Zero => t_Zero
  | t_Succ n => t_Succ (swap_ln x y n)
  | t_NatRec_ln P z s n => t_NatRec_ln (swap_ln x y P) (swap_ln x y z) (swap_ln x y s) (swap_ln x y n)
  end.

Lemma swap_commutes_open_rec :
  forall t k x y u,
    swap_ln x y (open_rec_ln k u t)
    = open_rec_ln k (swap_ln x y u) (swap_ln x y t).
Proof.
  induction t; intros; simpl; try reflexivity.
  - (* t_bvar *)
    destruct (Nat.eqb n k); reflexivity.
  - (* t_Pi *)  rewrite IHt1, IHt2; reflexivity.
  - (* t_Lam *) rewrite IHt1, IHt2; reflexivity.
  - (* t_App *) rewrite IHt1, IHt2; reflexivity.
  - (* t_Succ *) rewrite IHt; reflexivity.
  - (* t_NatRec_ln *)
    rewrite IHt1, IHt2, IHt3, IHt4.
    reflexivity.
Qed.


Theorem substitution_general :
  forall ΓL ΓR x A t B v,
    ~In x (map fst (ΓL ++ ΓR)) ->
    has_type_ln (ΓL ++ (x, A) :: ΓR) t B ->
    has_type_ln ΓR v A ->
    lc_ln v ->
    has_type_ln (subst_ctx x v (ΓL ++ ΓR)) (subst_ln x v t) (subst_ln x v B).
Proof.
  intros ΓL ΓR x A t B v Hf Ht Hu Hc .
  remember (ΓL ++ (x, A) :: ΓR) as G.
  revert v x A Hf Hu Hc HeqG. revert ΓL ΓR.

  induction Ht; intros.
  10:{
  subst.
  apply ty_conv with (A := (subst_ln x v A)).
  apply IHHt with (A := A0). easy. easy. easy. easy.
  apply convertible_subst. easy. easy.
  }
  9: {
  subst.
  simpl. rewrite open_subst_commute. eapply ty_NatRec_strong with (k := k) (L := x::L).
  simpl in IHHt1.
  apply IHHt1 with (A := A). easy. easy. easy. easy.
  apply convertible_subst with (x := x) (v := v) in H; try easy.
  
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H2. simpl. right. easy. }
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { unfold not. intros. simpl in H4. destruct H4. subst. apply H2. simpl. left. easy. easy. }
  specialize(H1 x0 H3 ((x0, t_Nat) :: ΓL) ΓR v x A H4).
  simpl in H1.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H2. subst. simpl. left. easy. }
  rewrite H5 in H1.
  simpl in H1. unfold open_ln. simpl.
  unfold open_ln in H1.
  rewrite open_subst_commute in H1. simpl in H1.
  rewrite H5 in H1.
  apply H1. easy. easy. easy. easy.
  specialize(IHHt2 ΓL ΓR v x A).
  simpl in IHHt2.
  rewrite  open_subst_commute in IHHt2.
  apply IHHt2; easy.
  easy.
  cbn.
  specialize(IHHt3 ΓL ΓR v x A).
  simpl in IHHt3.
  rewrite  open_subst_commute in IHHt3.
  rewrite  open_subst_commute in IHHt3.
  apply IHHt3; easy.
  easy. easy.
  simpl in IHHt4. apply IHHt4 with (A := A); easy.
  easy.
  }
  8:{
  subst. simpl.
  constructor.
  simpl in IHHt.
  apply IHHt with (A := A); easy.
  }
  7:{
  subst. constructor.
  }
  6:{ subst. constructor. }
  5:{ subst. 
  simpl. unfold open_ln.
  rewrite open_subst_commute.
  apply ty_App with (A := (subst_ln x v A)).
  specialize(IHHt1 ΓL ΓR v x A0).
  simpl in IHHt1.
  apply IHHt1; easy.
  apply IHHt2 with (A := A0); easy.
  easy.
  } 
  4:{ subst. 
  simpl.
  apply ty_Lam with (i := i) (L := x::L).
  simpl in IHHt. apply IHHt with (A := A0); easy.
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H1. simpl. right. easy. }
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { unfold not. intros. simpl in H3. destruct H3. subst. apply H1. simpl. left. easy. easy. }
  specialize(H0 x0 H2 ((x0, A) :: ΓL) ΓR v x A0 H3).
  simpl in H0.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H1. subst. simpl. left. easy. }
  rewrite H4 in H0.
  simpl in H0. unfold open_ln. simpl.
  unfold open_ln in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite H4 in H0. simpl in H0.
  apply H0. easy. easy. easy. easy. easy.
  }
  3:{ subst.
  simpl.
  apply ty_Pi with (i := i) (L := x::L).
  simpl in IHHt. apply IHHt with (A := A0); easy.
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H1. simpl. right. easy. }
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { unfold not. intros. simpl in H3. destruct H3. subst. apply H1. simpl. left. easy. easy. }
  specialize(H0 x0 H2 ((x0, A) :: ΓL) ΓR v x A0 H3).
  simpl in H0.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H1. subst. simpl. left. easy. }
  rewrite H4 in H0.
  simpl in H0. unfold open_ln. simpl.
  unfold open_ln in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite H4 in H0. simpl in H0.
  apply H0. easy. easy. easy. easy.
  }
  2:{ subst.
  simpl.
  constructor.
  }
  1:{ subst. simpl. 
      case_eq((x0 =? x)%string); intros.
      - rewrite String.eqb_eq in H0. subst.
        assert(T = A) by admit. subst.
        admit.
      - apply ty_var. simpl.
        assert(lookup_ln (ΓL ++ ΓR) x = Some T) by admit.
        rewrite ctx_subst_some with (T := T). easy.
        apply String.eqb_neq in H0. easy. easy.
    }
Admitted.

