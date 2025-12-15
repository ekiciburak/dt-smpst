From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String Ascii.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators Lia.

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
      t_NatRec_ln (open_rec_ln k u P)
                  (open_rec_ln k u z)
                  (open_rec_ln k u s)
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
      t_NatRec_ln (close_rec_ln k x P)
                  (close_rec_ln k x z)
                  (close_rec_ln k x s)
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
  | t_NatRec_ln P z s n => lc_rec_ln k P /\ lc_rec_ln k z /\ lc_rec_ln k s /\ lc_rec_ln k n
  end.

Definition lc_ln (t : term_ln) := lc_rec_ln 0 t.

Inductive value_ln : term_ln -> Prop :=
| V_Type_ln : forall i, value_ln (t_Type i)
| V_Nat_ln : value_ln t_Nat
| V_Pi_ln : forall A B, value_ln A -> value_ln B -> value_ln (t_Pi A B)
| V_Lam_ln : forall A b, value_ln A -> value_ln (t_Lam A b)  (* body not required *)
| V_Zero_ln : value_ln t_Zero
| V_Succ_ln : forall n, value_ln n -> value_ln (t_Succ n).

(* numeric values predicate (Nat values) *)
Inductive nat_value : term_ln -> Prop :=
| nv_zero : nat_value t_Zero
| nv_succ : forall n, nat_value n -> nat_value (t_Succ n).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step_ln : term_ln -> term_ln -> Prop :=

  (* Beta: only when argument is a value; open the body with the actual value *)
| s_beta_ln : 
    forall A b s,
      lc_rec_ln 0 A ->                     (* <--- require s closed *)
      lc_rec_ln 1 b ->
      lc_rec_ln 0 s ->                     (* <--- require s closed *)
      step_ln (t_App (t_Lam A b) s) (open_ln b s)
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
| s_rec_zero_ln :
    forall (Pbody sbody z : term_ln),
      (* P = t_Lam t_Nat Pbody  — Pbody sits under 1 binder *)
      lc_rec_ln 1 Pbody ->
      (* s = t_Lam t_Nat (t_Lam t_Nat sbody)  — sbody sits under 2 binders *)
      lc_rec_ln 2 sbody ->
      (* z closed *)
      lc_rec_ln 0 z ->
      step_ln
        (t_NatRec_ln (t_Lam t_Nat Pbody) z
                     (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody))
                     t_Zero)
        z

(* | s_rec_succ_ln : forall P z s n,
    value_ln n ->
    step_ln (t_NatRec_ln P z s (t_Succ n))
            (t_App (t_App s n) (t_NatRec_ln P z s n))  *)

| s_rec_succ_ln : 
    forall (Pbody sbody z n : term_ln),
      (* P = t_Lam t_Nat Pbody *)
      (* P = t_Lam t_Nat Pbody  — Pbody sits under 1 binder *)
      lc_rec_ln 1 Pbody ->
      (* s = t_Lam t_Nat (t_Lam t_Nat sbody)  — sbody sits under 2 binders *)
      lc_rec_ln 2 sbody ->
      (* z closed *)
      lc_rec_ln 0 z ->
      lc_rec_ln 0 n ->
      step_ln
        (t_NatRec_ln (t_Lam t_Nat Pbody) z
                     (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody))
                     (* (t_Lam t_Nat (t_Lam Pbody sbody)) *)
                     (t_Succ n))
        (open_rec_ln 0 (t_NatRec_ln (t_Lam t_Nat Pbody) z (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody)) n) (open_rec_ln 1 n sbody))
        
        
(* | s_rec_succ_ln : forall Pbody z sbody n,
    nat_value n ->
    step_ln
      (t_NatRec_ln (t_Lam t_Nat Pbody)
                   z
                   (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) Pbody) sbody))
                   (t_Succ n))
      (open_rec_ln 0 (t_NatRec_ln (t_Lam t_Nat Pbody)
                                  z
                                  (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) Pbody) sbody))
                                  n)
                   (open_rec_ln 1 n sbody)) *)

(* | s_rec_succ_ln : forall P z s n,
    value_ln n ->
    step_ln (t_NatRec_ln P z s (t_Succ n))
            (t_App (t_App s n) (t_NatRec_ln P z s n)) 
 *)
(* | s_rec_succ_ln : forall P z s n,
    value_ln n ->
    step_ln (t_NatRec_ln P z s (t_Succ n))
            (open_rec_ln 0 (t_NatRec_ln P z s n) (open_rec_ln 1 n s)) *)

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
      lc_rec_ln 0 A ->                     (* <--- require s closed *)
      lc_rec_ln 1 b ->
      lc_rec_ln 0 s ->                     (* <--- require s closed *)
      beta_head_ln (t_App (t_Lam A b) s) (open_ln b s)


| b_natrec_zero_ln_strict :
    forall (Pbody sbody z : term_ln),
      (* P = t_Lam t_Nat Pbody  — Pbody sits under 1 binder *)
      lc_rec_ln 1 Pbody ->
      (* s = t_Lam t_Nat (t_Lam t_Nat sbody)  — sbody sits under 2 binders *)
      lc_rec_ln 2 sbody ->
      (* z closed *)
      lc_rec_ln 0 z ->
      beta_head_ln
        (t_NatRec_ln (t_Lam t_Nat Pbody) z
                     (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody))
                     t_Zero)
        z

| b_natrec_succ_ln_strict :
    forall (Pbody sbody z n : term_ln),
      (* P = t_Lam t_Nat Pbody *)
      (* P = t_Lam t_Nat Pbody  — Pbody sits under 1 binder *)
      lc_rec_ln 1 Pbody ->
      (* s = t_Lam t_Nat (t_Lam t_Nat sbody)  — sbody sits under 2 binders *)
      lc_rec_ln 2 sbody ->
      (* z closed *)
      lc_rec_ln 0 z ->
      lc_rec_ln 0 n ->
      beta_head_ln
        (t_NatRec_ln (t_Lam t_Nat Pbody) z
                     (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody))
                     (* (t_Lam t_Nat (t_Lam Pbody sbody)) *)
                     (t_Succ n))
        (open_rec_ln 0 (t_NatRec_ln (t_Lam t_Nat Pbody) z (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) Pbody) sbody)) n) (open_rec_ln 1 n sbody)).

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

(* Custom induction schema for convertibility (clos_refl_sym_trans of beta_ln) *)
Lemma convertible_ln_ind :
  forall (P : term_ln -> term_ln -> Prop),
    (* reflexive case *)
    (forall x, P x x) ->
    (* one-step beta case *)
    (forall x y, beta_ln x y -> P x y) ->
    (* symmetry closure: if P x y then P y x *)
    (forall x y, P x y -> P y x) ->
    (* transitivity closure: if P x y and P y z then P x z *)
    (forall x y z, P x y -> P y z -> P x z) ->
    forall t u, t ≡ₗₙ u -> P t u.
Proof.
  intros P Hrefl Hstep Hsym Htrans t u H.
  unfold convertible_ln in H.
  (* use the general induction principle for clos_refl_sym_trans *)
  eapply (clos_refl_sym_trans_ind term_ln beta_ln P); eauto.
Qed.

(* A convenient corollary specialized to predicates that don't depend on both
   arguments (often useful): *)
Lemma convertible_ln_ind_left :
  forall (Q : term_ln -> Prop),
    (forall x, Q x) -> (* reflexive *)
    (forall x y, beta_ln x y -> Q x -> Q y) -> (* step lifts Q *)
    forall t u, t ≡ₗₙ u -> Q u.
Proof.
  intros Q HQ Hstep t u H.
  apply (convertible_ln_ind (fun _ y => Q y)) with (t := t).
  - intros; apply HQ.
  - intros x y Hxy. (* from one-step beta we must show Q y; we don't have Q x,
                       so require Hstep to use Q x -> Q y; to be safe, use reflexive HQ *)
    apply Hstep with (x:=x).
    + assumption.
    + apply HQ.
  - intros ? ? Hq. apply HQ.
  - intros ? ? ? Hq1 Hq2. assumption.
  - assumption.
Qed.

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

Print nat_rec.

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
               (~ In x (map fst Gamma) ->
               has_type_ln ((x, A) :: Gamma) (open_ln B (t_fvar x)) (t_Type j))) ->
    has_type_ln Gamma (t_Pi A B) (t_Type (Nat.max i j))

  (* Lambda (cofinite) *)
| ty_Lam : forall Gamma A b B i L,
    has_type_ln Gamma A (t_Type i) ->
    (forall x, ~ In x L ->
               (~ In x (map fst Gamma) ->
               has_type_ln ((x, A) :: Gamma) (open_ln b (t_fvar x)) (open_ln B (t_fvar x)))) ->
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

| ty_NatRec_strong : forall Gamma body z sbody n k L
    (Hclb: lc_rec_ln 1 body) (Hcls: lc_rec_ln 2 sbody),
    has_type_ln Gamma (t_Lam t_Nat body) (t_Pi t_Nat (t_Type k)) ->

    (* body yields a family of types (cofinite) *)
    (forall x, ~ In x L ->
       (~ In x (map fst Gamma) ->
         has_type_ln ((x, t_Nat) :: Gamma)
                     (open_rec_ln 0 (t_fvar x) body)
                     (open_rec_ln 0 (t_fvar x) (t_Type k)))) ->

    (* base: z : P 0 (opened on body) *)
    has_type_ln Gamma z (open_rec_ln 0 t_Zero body) -> 

    (* and the inner body sbody type-checks cofinitely with two distinct fresh names:
       - x is the numeric parameter m
       - y is the recursive hypothesis ih of type P x
    *)
    has_type_ln Gamma (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody))
      (t_Pi t_Nat
            (t_Pi (open_rec_ln 0 (t_bvar 0) body)
                  (open_rec_ln 0 (t_Succ (t_bvar 1)) body))) ->

    (forall x y, x <> y ->
       ~ In x L -> ~ In y L ->
       (~ In x (map fst Gamma) -> ~ In y (map fst Gamma) ->
         has_type_ln ((y, open_rec_ln 0 (t_fvar x) body) :: (x, t_Nat) :: Gamma)
                     (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody))
                     (open_rec_ln 0 (t_Succ (t_fvar x)) body))) ->

    (* scrutinee is a nat *)
    has_type_ln Gamma n t_Nat ->

    (* conclusion: NatRec result has type P n expanded on body *)
    has_type_ln Gamma (t_NatRec_ln (t_Lam t_Nat body) z (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody)) n) (open_rec_ln 0 n body)

| ty_conv : forall Γ t A B,
    has_type_ln Γ t A ->
    convertible_ln A B ->
    has_type_ln Γ t B.

Check nat_rec.

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
    intros.
    eapply ty_Lam with (L := []).
    + apply ty_Nat.
    + intros m_name Hfresh_m. cbn. intros.
      cbn.
      
      eapply ty_NatRec_strong
            with (k := 0)
                 (body := t_Nat)              (* the body of P_const *)
                 (z := t_fvar m_name)         (* base case uses the local var m *)
                 (n := t_fvar n_name)
                 (L := [])
                 (sbody := ((t_Succ (t_bvar 0))) ).        (* recursion argument = local var n *)
      cbn. easy. cbn.  lia.
      apply ty_Lam with (i := 0) (L := []).
      apply ty_Nat.
      intros.
      cbn.
      apply ty_Nat.
      cbn. 
(*       apply convertible_refl. *)
(*       
      easy. *)
      intros. cbn.
      apply ty_Nat.
      apply ty_var. simpl. rewrite String.eqb_refl. easy.
      unfold s_add.
      cbn.
(*       apply convertible_refl. *)
      
      unfold s_add.
      apply ty_Lam with (i := 0) (L := []).
      apply ty_Nat.
      
      intros.
      cbn.
      apply ty_Lam with (i := 0) (L := []).
      apply ty_Nat.
      
      intros.
      cbn.
      apply ty_Succ.
      apply ty_var. simpl.
      rewrite String.eqb_refl. easy.
      
      intros.
      simpl.
      cbn.
      apply ty_Succ.
      apply ty_var. simpl.
      rewrite String.eqb_refl. easy.
      
(*       intros.
      cbn.
      apply ty_Succ.
      apply ty_Lam with (i := 0) (L := []).
      apply ty_Nat. *)
      
      apply ty_var. simpl.
      rewrite String.eqb_refl.
      destruct((n_name =? m_name)%string); easy.
Qed.


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
            assert(HNIN:  ~ In x0 (map fst (Gamma1 ++ (x, U) :: (y, V) :: Gamma2))).
            { unfold not.
              intros.
              apply H6. rewrite map_app. rewrite map_app in H8.
              apply in_app_iff. apply in_app_iff in H8.
              destruct H8. left. easy.
              simpl in H8. destruct H8. simpl. right. right. left. easy.
              destruct H8. right. left. easy.
              right. right. right. easy.
            }
            specialize(H0 x0 H7 HNIN ((x0, A) :: Gamma1) Gamma2).
            simpl in H0. apply H0.
            unfold not. intros.
            destruct H8. subst. apply H6. simpl. rewrite map_app. apply in_app_iff. right. left. easy.
            easy. easy.
            unfold not. intros. destruct H8. subst.
            apply H5. simpl. left. easy. easy.
            easy. 
          }
       9: { apply ty_conv with (A := A); try easy.
            apply IHhas_type_ln; try easy.
          }
       8: { subst.
            eapply ty_NatRec_strong with (k := k) (L := L) (sbody := sbody). unfold P_app1, s_expected_type_for_P in *. cbn in *.
            easy. easy.
            eapply IHhas_type_ln1. easy. easy. easy. easy.
            intros. 
            specialize(H0 x0 H6).
(*             unfold not. intros.
            apply H6.
            rewrite map_app.
            apply in_app_iff. right.
            simpl. simpl in H7. destruct H7. right. left. easy.
            destruct H7. left. easy. *)
            assert(HNIN: (~In x0 (map fst (Gamma1 ++ (x, U) :: (y, V) :: Gamma2)))).
            { unfold not. intros. apply H7.
              rewrite map_app. rewrite map_app in H8.
              simpl in H8. apply in_app_iff in H8.
              apply in_app_iff. destruct H8. left. easy.
              right.
              simpl in H8. destruct H8. simpl. right. left. easy.
              destruct H8. simpl. left. easy.
              simpl. right. right. easy.
            }
            specialize(H0 HNIN ((x0, t_Nat) :: Gamma1) Gamma2).
            cbn in H0. cbn.
            apply H0.
            unfold not. intros.
            destruct H8. subst. apply H7. simpl. rewrite map_app. apply in_app_iff. right. simpl. left. easy.
            easy. easy.
            unfold not. intros. destruct H8. subst.
            apply H7. simpl. rewrite map_app. apply in_app_iff. right. right. left. easy. easy.
            easy. 
            apply IHhas_type_ln2. 
            easy. easy. easy. easy.
            apply IHhas_type_ln3; easy.
            intros.

            specialize(H2 x0 y0 H6 H7 H8).
(*             unfold not. intros.
            apply H6.
            rewrite map_app.
            apply in_app_iff. right.
            simpl. simpl in H7. destruct H7. right. left. easy.
            destruct H7. left. easy. *)
            assert(HNIN: (~In x0 (map fst (Gamma1 ++ (x, U) :: (y, V) :: Gamma2)))).
            { unfold not. intros. apply H9.
              rewrite map_app. rewrite map_app in H11.
              simpl in H11. apply in_app_iff in H11.
              apply in_app_iff. destruct H11. left. easy.
              right.
              simpl in H11. destruct H11. simpl. right. left. easy.
              destruct H11. simpl. left. easy.
              simpl. right. right. easy.
            }
            assert(HNIN2: (~In y0 (map fst (Gamma1 ++ (x, U) :: (y, V) :: Gamma2)))).
            { unfold not. intros. apply H10.
              rewrite map_app. rewrite map_app in H11.
              simpl in H11. apply in_app_iff in H11.
              apply in_app_iff. destruct H11. left. easy.
              right.
              simpl in H11. destruct H11. simpl. right. left. easy.
              destruct H11. simpl. left. easy.
              simpl. right. right. easy.
            }
            specialize(H2 HNIN HNIN2 ((y0, open_rec_ln 0 (t_fvar x0) body) :: (x0, t_Nat) :: Gamma1) Gamma2).
            cbn in H2. cbn.
            apply H2.
            unfold not. intros.
            destruct H11. subst. apply H10. simpl. rewrite map_app. apply in_app_iff. right. simpl. left. easy.
            destruct H11. subst. apply H9. simpl. rewrite map_app. apply in_app_iff. right. simpl. left. easy.
            easy. easy.
            unfold not. intros. destruct H11. subst.
            apply H10. simpl. rewrite map_app. apply in_app_iff. right. right. left. easy.
            destruct H11. subst.
            apply H9. simpl. rewrite map_app. apply in_app_iff. right. right. left. easy.
            easy.
            easy.
           
            apply IHhas_type_ln4; easy.
           }
        3: { subst.
             apply ty_Pi with (L := (x::y::L)).
             apply IHhas_type_ln; easy.
             intros.
             assert(~ In x0 L).
             { unfold not. intros. apply H5. simpl. right. right. easy. }
             assert(HNIN:  ~ In x0 (map fst (Gamma1 ++ (x, U) :: (y, V) :: Gamma2))).
            { unfold not.
              intros.
              apply H6. rewrite map_app. rewrite map_app in H8.
              apply in_app_iff. apply in_app_iff in H8.
              destruct H8. left. easy.
              simpl in H8. destruct H8. simpl. right. right. left. easy.
              destruct H8. right. left. easy.
              right. right. right. easy.
            }
             specialize(H0 x0 H7 HNIN ((x0, A) :: Gamma1) Gamma2).
             simpl in H0. apply H0.
             unfold not. intros.
             destruct H8. subst. apply H6. simpl.  rewrite map_app. apply in_app_iff. right. simpl. left. easy.
             easy. easy.
             unfold not. intros. destruct H8. subst.
             apply H6. simpl. rewrite map_app. apply in_app_iff. right. right. left. easy. easy.
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
            assert(HNIN:  ~ In x0 (map fst Gamma)).
            { simpl in H4. unfold not. intros. apply H4. simpl. right. easy. }
            specialize(H1 x0 H5 HNIN x).
            assert(~ In x (map fst ((x0, A) :: Gamma))).
            { simpl. unfold not. intros. apply H3. simpl.
              destruct H6. left. easy.
              right. apply in_app_iff. right. easy.
            }
            specialize(H1 H6).
            specialize (fresh_commute_middle nil Gamma (open_ln b (t_fvar x0)) (open_ln B (t_fvar x0))); intros Ha.
            simpl in Ha.
            apply Ha.
            unfold not. intros. apply H3. simpl. left. easy. easy.
            unfold not. intros. apply H3. simpl. right.
            apply in_app_iff. right. easy.
            easy.
          }
       8: { apply ty_NatRec_strong with (k := k) (L := L) (sbody := sbody). easy. easy.
            apply IHhas_type_ln1. easy.
            intros.
            assert(HNIN: ~ In x0 (map fst  Gamma)).
            { unfold not. intros. apply H5. simpl. right. easy. }
            specialize(H0 x0 H4 HNIN x).
            assert( ~ In x (map fst ((x0, t_Nat) :: Gamma))).
            { simpl. simpl in H5. unfold not.
              intros. apply H5. destruct H6. left. easy. right. easy.
            }
            apply H0 with (U := U) in H6.

            specialize (fresh_commute_middle nil); intros Ha.
            simpl in Ha.
            apply Ha.
            unfold not. intros. apply H5. simpl. left. easy. easy.
            unfold not. intros. apply H5. simpl. right. easy.
            easy.

            apply IHhas_type_ln2. easy.
            apply IHhas_type_ln3. easy.
            
            intros.
            specialize(H2 x0 y H4 H5 H6).
            assert(HNIN: ~ In x0 (map fst  Gamma)).
            { unfold not. intros. apply H7. simpl. right. easy. }
            assert(HNIN2: ~ In y (map fst  Gamma)).
            { unfold not. intros. apply H8. simpl. right. easy. }
            simpl in H4.
            assert(~ (y = x \/ x0 = x \/ In x (map fst Gamma))).
            { simpl. simpl in H8. unfold not.
              intros. apply H8. destruct H9. left. easy.
              destruct H9. subst. contradict H7. simpl. left. easy.
              right. easy.
            }
            specialize(H2 HNIN HNIN2 x H9). cbn.
            specialize (fresh_commute_middle nil); intros Ha.
            simpl in Ha.
            apply Ha.
            unfold not. intros. apply H8. simpl. left. easy. easy.
            unfold not. intros. apply H8. simpl. right. easy.
            apply Ha; try easy.
            apply Ha with (U := U) in H2.
            specialize (fresh_commute_middle [(y, open_rec_ln 0 (t_fvar x0) body)]); intros Hb.
            simpl in Hb.
            apply Hb.
            unfold not. intros. apply H7. simpl. left. easy.
            unfold not. intros.
            destruct H10. apply H9. simpl. left. easy.
            easy.
            unfold not. intros.
            destruct H10. subst. easy. easy.
            apply H2.
            unfold not. intros. subst. contradict H9. left. easy.
            unfold not. intros.
            apply H7. simpl. simpl in H10. destruct H10. left. easy.
            easy.
            simpl. unfold not. intros.
            destruct H10. subst. easy. easy.
            apply IHhas_type_ln4. easy.
          }
       3: { apply ty_Pi with (i := i) (L := x::L++(map fst Gamma)).
            apply IHhas_type_ln. easy.
            intros.
            assert( ~ In x0 L).
            { unfold not. intros. apply H3. simpl. right.
              apply in_app_iff. left. easy. }
            assert(HNIN:  ~ In x0 (map fst Gamma)).
            { simpl in H4. unfold not. intros. apply H4. simpl. right. easy. }
            specialize(H1 x0 H5 HNIN x).
            assert(~ In x (map fst ((x0, A) :: Gamma))).
            { simpl. unfold not. intros. apply H3. simpl.
              destruct H6. left. easy.
              right. apply in_app_iff. right. easy.
            }
            specialize(H1 H6).
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

Lemma cl_larger: forall v k u, 
  Nat.le k u -> 
  lc_rec_ln k v -> 
  lc_rec_ln u v.
Proof. intro t.
       induction t; intros.
       10:{ simpl. inversion H0. split.
            apply IHt1 with (k := k). lia. easy.
            split. apply IHt2 with (k := k). lia. easy.
            split. apply IHt3 with (k := k). lia. easy.
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
  - destruct (Nat.eqb n k) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.  (* contradicts n < k *)
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
(*             apply cl_larger with (k := k). lia. easy.
            apply cl_larger with (k := k). lia. easy. *)
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

Lemma closedness_preserved:
  forall A m k u, 
  Nat.le m k ->
  lc_rec_ln m A ->
  lc_rec_ln m (open_rec_ln k u A).
Proof. intro t.
       induction t; intros.
       10:{ cbn. simpl in H.
            split. apply IHt1. lia.
            simpl in H0. easy.
            split. apply IHt2. lia.
            simpl in H0. easy.
            split. apply IHt3. lia.
            simpl in H0. easy.
            apply IHt4. lia.
            simpl in H0. easy.
          }
       9: { simpl. apply IHt. lia. simpl in H0. easy. }
       5: { simpl. split. apply IHt1. easy. simpl in H0. easy.
            apply IHt2. lia. simpl in H0. easy.
          }
       4: { simpl. split. apply IHt1. easy. simpl in H0. easy.
            apply IHt2. lia. simpl in H0. easy.
          }
       3: { simpl. easy. }
       3: { simpl. split. apply IHt1. easy. simpl in H0. easy.
            apply IHt2. easy. simpl in H0. easy.
          }
       1: { simpl. simpl in H0.
            assert(n =? k = false).
            { apply Nat.eqb_neq. lia. }
            rewrite H1. simpl. easy.
          }
       2: { simpl. easy. }
       2: { simpl. easy. }
       1: { simpl. easy. }
Qed.

Lemma lc_rec_open_rec :
  forall t u k,
    lc_rec_ln (S k) t ->
    lc_rec_ln 0 u ->
    lc_rec_ln k (open_rec_ln k u t).
Proof. intro t.
       induction t; intros.
       - cbn. simpl in H.
         case_eq(n =? k); intros. 
         + apply cl_larger with (k := 0). lia. easy.
         + simpl.
           apply Nat.eqb_neq in H1.
           lia.
       - cbn. easy.
       - cbn. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - cbn. easy.
       - cbn. easy.
       - cbn. apply IHt. simpl in H. easy. easy.
       - cbn. simpl in H.
         split. apply IHt1. easy. easy.
         split. apply IHt2. easy. easy.
         split. apply IHt3. easy. easy.
         apply IHt4. easy. easy.
Qed.

Lemma lc_rec_open_rec_g :
  forall t u k,
    lc_rec_ln (S k) t ->
    lc_rec_ln 1 u ->
    lc_rec_ln (S k) (open_rec_ln k u t).
Proof. intro t.
       induction t; intros.
       - cbn. simpl in H.
         case_eq(n =? k); intros. 
         + apply cl_larger with (k := 1). lia. easy.
         + simpl. easy.
       - cbn. easy.
       - cbn. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - cbn. easy.
       - cbn. easy.
       - cbn. apply IHt. simpl in H. easy. easy.
       - cbn. simpl in H.
         split. apply IHt1. easy. easy.
         split. apply IHt2. easy. easy.
         split. apply IHt3. easy. easy.
         apply IHt4. easy. easy.
Qed.

Lemma lc_rec_open_rec_g2 :
  forall t u k,
    lc_rec_ln (S k) t ->
    lc_rec_ln 2 u ->
    lc_rec_ln (S (S k)) (open_rec_ln k u t).
Proof. intro t.
       induction t; intros.
       - cbn. simpl in H.
         case_eq(n =? k); intros. 
         + apply cl_larger with (k := 2). lia. easy.
         + simpl. lia.
       - cbn. easy.
       - cbn. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         easy.
         apply IHt2. simpl in H. easy. easy.
       - cbn. easy.
       - cbn. easy.
       - cbn. apply IHt. simpl in H. easy. easy.
       - cbn. simpl in H.
         split. apply IHt1. easy. easy.
         split. apply IHt2. easy. easy.
         split. apply IHt3. easy. easy.
         apply IHt4. easy. easy.
Qed.

Lemma lc_rec_open_rec11 :
  forall t u k,
    lc_rec_ln 1 t ->
    lc_rec_ln 1 u ->
    lc_rec_ln (S k) (open_rec_ln 0 u t).
Proof. intros. 
       apply cl_larger with (k := 1). lia.
       apply lc_rec_open_rec_g. easy. easy.
Qed.

Lemma lc_rec_open_rec12 :
  forall t u k,
    lc_rec_ln 1 t ->
    lc_rec_ln 2 u ->
    lc_rec_ln (S (S k)) (open_rec_ln 0 u t).
Proof. intros. 
       apply cl_larger with (k := 2). lia.
       apply lc_rec_open_rec_g2. easy. easy.
Qed.

Lemma lc_rec_open_open_rec :
  forall t u v k,
    lc_rec_ln (S (S k)) t ->
    lc_rec_ln 0 u ->
    lc_rec_ln 0 v ->
    lc_rec_ln k (open_rec_ln k v (open_rec_ln (S k) u t)).
Proof. intros.
       induction t; intros.
       - cbn. simpl in H.
         case_eq(n =? S k); intros.
         + apply lc_rec_open_rec. 
           apply cl_larger with (k := 0). lia. easy. easy.
         + simpl.
           case_eq( n =? k ); intros.
           * apply cl_larger with (k := 0). lia. easy.
           * simpl. apply Nat.eqb_neq in H2. apply Nat.eqb_neq in H3.
           lia.
       - cbn. easy.
       - cbn. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         apply lc_rec_open_rec. cbn.
         simpl in H.
         apply lc_rec_open_rec. easy. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         apply lc_rec_open_rec. cbn.
         simpl in H.
         apply lc_rec_open_rec. easy. easy. easy.
       - simpl. split. apply IHt1. simpl in H. easy.
         apply IHt2. simpl in H. easy.
       - cbn. easy.
       - cbn. easy.
       - cbn. apply IHt. simpl in H. easy.
       - cbn. simpl in H.
         split. apply IHt1. easy.
         split. apply IHt2. easy.
         split. apply IHt3. easy.
         apply IHt4. easy.
Qed.

Lemma lc_rec_open_rec0 :
  forall t u k,
    lc_rec_ln 1 t ->
    lc_rec_ln 0 u ->
    lc_rec_ln k (open_rec_ln 0 u t).
Proof. intros.
       apply cl_larger with (k := 0). lia.
       apply lc_rec_open_rec. easy. easy.
Qed.

Lemma lc_rec_open_rec1 :
  forall t u v k,
    lc_rec_ln 2 t ->
    lc_rec_ln 0 u ->
    lc_rec_ln 0 v ->
    lc_rec_ln k (open_rec_ln 0 v (open_rec_ln 1 u t)).
Proof. intros.
       apply cl_larger with (k := 0). lia.
       apply lc_rec_open_open_rec. easy. easy. easy.
Qed.


Lemma open_wfree: forall b x,
  lc_rec_ln 1 b ->
  lc_rec_ln 0 (open_rec_ln 0 (t_fvar x) b).
Proof. intros.
       apply lc_rec_open_rec. easy. easy.
Qed.

Lemma subst_preserve_closdness: 
  forall A v x0 k,
  lc_rec_ln k A ->
  lc_rec_ln 0 v ->
  lc_rec_ln k (subst_ln x0 v A).
Proof. intro A.
       induction A; intros.
       - cbn. simpl in H. easy.
       - cbn. simpl in H.
         case_eq((x0 =? s)%string); intros.
         + apply cl_larger with (k := 0). lia. easy.
         + cbn. easy.
       - cbn. easy.
       - cbn. split. apply IHA1. simpl in H. easy. easy.
         apply IHA2. simpl in H. easy. easy.
       - cbn. split. apply IHA1. simpl in H. easy. easy.
         apply IHA2. simpl in H. easy. easy.
       - cbn. split. apply IHA1. simpl in H. easy. easy.
         apply IHA2. simpl in H. easy. easy.
       - cbn. easy.
       - cbn. easy.
       - cbn. apply IHA. easy. easy.
       - cbn.
         split. apply IHA1. simpl in H. easy. easy.
         split. apply IHA2. simpl in H. easy. easy.
         split. apply IHA3. simpl in H. easy. easy.
         apply IHA4. simpl in H. easy. easy.
Qed.

Lemma open_rec_ln_Lam :
  forall k u A b,
    open_rec_ln k u (t_Lam A b)
    = t_Lam (open_rec_ln k u A) (open_rec_ln (S k) u b).
Proof. intros; reflexivity. Qed.

Lemma subst_beta_head_compat :
  forall t u x v,
    lc_rec_ln 0 v ->
    beta_head_ln t u ->
    beta_head_ln (subst_ln x v t) (subst_ln x v u).
Proof.
  intros t u x v Hv H.
  inversion H; subst; clear H.
  - (* b_beta_app_ln *)
    (* t = t_App (t_Lam A b) s *)
    (* We need to show substituted versions satisfy head beta, i.e.
       lc_rec_ln 1 (subst b) and lc_rec_ln 0 (subst s). *)
    simpl in *.
    unfold open_ln.
    rewrite open_subst_commute.
    apply b_beta_app_ln.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy. easy.
  - cbn.
    unfold open_ln.
    rewrite open_subst_commute.
    cbn.
    constructor.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy. easy.
  - simpl.
    unfold open_ln.
    rewrite open_subst_commute.
    rewrite open_subst_commute.
    rewrite open_subst_commute.
    cbn.
    rewrite open_subst_commute.
    apply b_natrec_succ_ln_strict.
(*     cbn.
    assert(open_rec_ln 1 ((t_NatRec_ln (t_Lam t_Nat (subst_ln x v Pbody)) (subst_ln x v z) (t_Lam t_Nat (t_Lam t_Nat (subst_ln x v sbody))) (subst_ln x v n))) t_Nat = t_Nat).
    { simpl. easy. }
    setoid_rewrite <- H at 5.
    rewrite <- open_rec_ln_Lam.
    assert(open_rec_ln 0 (t_NatRec_ln (t_Lam t_Nat (subst_ln x v Pbody)) (subst_ln x v z) (t_Lam t_Nat (t_Lam t_Nat (subst_ln x v sbody)))
             (subst_ln x v n)) t_Nat = t_Nat).
    { simpl. easy. }
    setoid_rewrite <- H4 at 4.
    rewrite <- open_rec_ln_Lam.
    apply b_natrec_succ_ln_strict. *)
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy.
    apply subst_preserve_closdness; easy.
    apply cl_larger with (k := 0). lia. easy.
    apply cl_larger with (k := 0). lia. easy. easy. easy.
(*     easy. easy. *)
Qed.

Lemma subst_beta_compat :
  forall t t' x v,
    lc_rec_ln 0 v ->
    beta_ln t t' ->
    beta_ln (subst_ln x v t) (subst_ln x v t').
Proof.
  intros t t' x v Hv H.
  induction H.
  - (* head step *)
    apply beta_head_step_ln.
    eapply subst_beta_head_compat; eauto.
  - (* pi_A *) apply beta_pi_A_ln.
    apply IHbeta_ln.
  - (* pi_B *) apply beta_pi_B_ln.
    apply IHbeta_ln.
  - (* lam_A *) apply beta_lam_A_ln.
    apply IHbeta_ln.
  - (* lam_b *) apply beta_lam_b_ln.
    apply IHbeta_ln.
  - (* app1 *) apply beta_app1_ln.
    apply IHbeta_ln.
  - (* app2 *) apply beta_app2_ln.
    apply IHbeta_ln.
  - (* succ *) apply beta_succ_ln.
    apply IHbeta_ln.
  - (* natrec P *)
    apply beta_natrec_P_ln; apply IHbeta_ln.
  - (* natrec z *)
    apply beta_natrec_z_ln; apply IHbeta_ln.
  - (* natrec s *)
    apply beta_natrec_s_ln; apply IHbeta_ln.
  - (* natrec n *)
    apply beta_natrec_n_ln; apply IHbeta_ln.
Qed.

Lemma convertible_subst :
  forall A B x v,
    lc_rec_ln 0 v ->
    A ≡ₗₙ B ->
    subst_ln x v A ≡ₗₙ subst_ln x v B.
Proof.
  intros A B x v Hv Hconv.
  induction Hconv.
  - constructor. eapply subst_beta_compat; eauto.
  - (* rst_refl *) apply rst_refl.
  - (* rst_sym *) apply rst_sym; assumption.
  - (* rst_trans *) eapply rst_trans; eauto.
Qed.

(* ------------------------- *)
(* basic helpers *)
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

(* max length of names in a list of strings *)
Definition max_len_of_strings (xs : list string) : nat :=
  fold_right (fun z acc => Nat.max (str_length z) acc) 0 xs.

(* candidate that is strictly longer than both the names in xs and the string x *)
Definition fresh_candidate_not_eq_str (xs : list string) (x : string) : string :=
  let m := Nat.max (max_len_of_strings xs) (str_length x) in
  repeat_ascii (S m) (Ascii.ascii_of_nat 97).  (* 'a' *)


Lemma str_length_in_list_le_max :
  forall xs s,
    In s xs ->
    str_length s <= max_len_of_strings xs.
Proof.
  intros xs s Hin.
  unfold max_len_of_strings.
  generalize dependent s.
  induction xs as [| z xs' IH]; simpl; intros; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + subst s. apply Nat.le_max_l.
    + apply Nat.le_trans with (m := fold_right (fun z acc => Nat.max (str_length z) acc) 0 xs').
      * apply IH; assumption.
      * apply Nat.le_max_r.
Qed.

Lemma candidate_longer_than_any_and_x_str :
  forall xs x s,
    In s xs ->
    str_length (fresh_candidate_not_eq_str xs x) > str_length s.
Proof.
  intros xs x s Hin.
  unfold fresh_candidate_not_eq_str.
  set (m := Nat.max (max_len_of_strings xs) (str_length x)).
  rewrite str_length_repeat_ascii.
  simpl.
  apply Nat.lt_succ_r.
  apply Nat.le_trans with (m := max_len_of_strings xs).
  - apply str_length_in_list_le_max; assumption.
  - apply Nat.le_max_l.
Qed.

Lemma candidate_not_eq_x_str :
  forall xs x,
    str_length (fresh_candidate_not_eq_str xs x) > str_length x.
Proof.
  intros xs x.
  unfold fresh_candidate_not_eq_str.
  set (m := Nat.max (max_len_of_strings xs) (str_length x)).
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

Lemma exists_fresh_not_in_list :
  forall (xs : list string) (x : string),
    exists y, ~ In y xs /\ y <> x.
Proof.
  intros xs x.
  set (y := fresh_candidate_not_eq_str xs x).
  exists y.
  split.
  - (* y ∉ xs *)
    intros Hin.
    eapply Nat.lt_irrefl.
    apply (candidate_longer_than_any_and_x_str xs x y).
    exact Hin.
  - (* y <> x because length(y) > length(x) *)
    intro Heq.
    apply (f_equal str_length) in Heq.
    unfold y in *.
    specialize (candidate_not_eq_x_str xs x).
    lia.
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

Fixpoint subst_ctx (x: string) (v: term_ln) (Γ: list(string*term_ln)) :=
  match Γ with
  | [] => []
  | (y,T) :: Γ' => (y, subst_ln x v T) :: subst_ctx x v Γ'
  end.

Lemma map_fst_app :
  forall A (l1 l2 : list (string * A)),
    map fst (l1 ++ l2) = map fst l1 ++ map fst l2.
Proof. intros. induction l1; simpl; auto. destruct a; f_equal; auto. Qed.

Lemma NoDup_left_disjoint_right :
  forall {A: Type} (ΓL ΓR : list A) (x : A),
    NoDup (ΓL ++ ΓR) ->
    In x ΓL ->
    ~ In x ΓR.
Proof.
  intros A ΓL ΓR x Hnodup Hin.
  induction ΓL as [| a ΓL' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + subst a.
      (* (a :: ΓL') ++ ΓR = a :: (ΓL' ++ ΓR) *)
      simpl in Hnodup.
      inversion Hnodup as [| ? l Hnotin Hnodup']; clear Hnodup.
      (* Hnotin : ~ In a (ΓL' ++ ΓR) *)
      intros HinR. apply Hnotin. apply in_or_app. right. assumption.
    + (* x ∈ ΓL' *)
      simpl in Hnodup.
      inversion Hnodup as [| ? l Hnotin Hnodup']; clear Hnodup.
      (* Hnodup' : NoDup (ΓL' ++ ΓR) *)
      subst.
      apply IH. easy. easy.
Qed.

Lemma ctx_subst_some: forall G x v x0 T,
     x <> x0 ->
     lookup_ln G x = Some T ->
     lookup_ln (subst_ctx x0 v G) x = Some (subst_ln x0 v T).
Proof. intro G.
       induction G; intros.
       - simpl in H0. easy.
       - simpl. destruct a.
         simpl in H0. 
         case_eq((x =? s)%string); intros.
         + rewrite String.eqb_eq in H1. subst.
           rewrite String.eqb_refl in H0. inversion H0. subst.
           simpl. rewrite String.eqb_refl. easy.
         + rewrite H1 in H0. simpl. rewrite H1.
           apply IHG. easy. easy.
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

Lemma lookup_not_in: forall Gamma x T,
  lookup_ln Gamma x = Some T ->
  ~ In x (map fst Gamma) -> False.
Proof. intro G.
       induction G; intros.
       - simpl in H. easy.
       - simpl in H. destruct a.
         case_eq((x =? s)%string ); intros.
         + rewrite String.eqb_eq in H1. subst.
           rewrite String.eqb_refl in H. inversion H. subst.
           simpl in H0. apply H0.
           left. easy.
         + rewrite H1 in H.
           apply IHG with (x := x) (T := T). easy.
           unfold not. intros.
           apply H0. simpl. right. easy.
Qed.

Lemma subst_ctx_app_or: forall G1 G2 x v,
  subst_ctx x v (G1 ++ G2) = subst_ctx x v G1 ++ subst_ctx x v G2.
Proof. intro G.
       induction G; intros.
       - simpl. easy.
       - simpl. destruct a. rewrite IHG. simpl. easy.
Qed.

Lemma subst_fst_id: forall G x v,
  (map fst (subst_ctx x v G)) = (map fst G).
Proof. intro G.
       induction G; intros.
       - simpl. easy.
       - simpl. destruct a. simpl. rewrite IHG. easy.
Qed.

Lemma env_subst :
  forall x v G t T,
    has_type_ln G t T ->
    ~ In x (map fst G) ->
    lc_ln v ->
    has_type_ln (subst_ctx x v G) (subst_ln x v t) (subst_ln x v T).
Proof. intros.
       revert x H0 v H1.
       induction H; intros.
       10:{ apply ty_conv with (A := (subst_ln x v A)).
            apply IHhas_type_ln. easy. easy.
            apply convertible_subst. easy. easy.
          }
       9: { simpl.
(*             destruct (exists_fresh_not_in_list (x::L++(map fst Gamma)) x) as (y,(Hniny,Hy)). *)
            rewrite open_subst_commute.
            rewrite open_subst_commute.
            eapply ty_NatRec_strong with (k := k) (L := x::L) (sbody := (subst_ln x v sbody)). 
            apply subst_preserve_closdness. easy. easy.
            apply subst_preserve_closdness. easy. easy.
            apply IHhas_type_ln1. easy. easy.
(*             apply convertible_subst with (x := x) (v := v) in H0; try easy. *)
            
            intros.
            rewrite subst_fst_id in H10.
            pose proof H10 as HNIN.
            assert(~ In x0 L).
            { unfold not. intros. apply H9. simpl. right. easy. }
            specialize(H1 x0 H11 H10 x).
            assert(~ In x (map fst ((x0, t_Nat) :: Gamma))).
            { unfold not. intros. simpl in H12. destruct H12. subst. 
              apply H9. simpl. left. easy. easy. }
            specialize(H1 H12 v H8).
            cbn in H2. cbn.
            simpl in H2. cbn. unfold open_ln in H1.
            rewrite open_subst_commute in H1.
            simpl in H2.
            assert((x =? x0)%string = false).
            { apply String.eqb_neq. unfold not. intros. subst.
              apply H9. simpl. left. easy. }
            cbn in H1.
            rewrite H13 in H1. cbn in H1. unfold open_ln. cbn. easy.
            easy.
            specialize(IHhas_type_ln2 x H7 v H8).
            cbn in IHhas_type_ln2.
            rewrite  open_subst_commute in IHhas_type_ln2.
(*             rewrite  open_subst_commute in IHhas_type_ln2. *)
            apply IHhas_type_ln2. easy.
            specialize(IHhas_type_ln3 x H7 v H8).
            simpl in IHhas_type_ln3.
            cbn in IHhas_type_ln3.
(*             assert(subst_ln x v s ≡ₗₙ subst_ln x v (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody))).
            { apply convertible_subst. easy. easy. }
            apply convertible_trans with (y := subst_ln x v (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody))).
            easy.
            cbn.
            rewrite  open_subst_commute. cbn.
            apply convertible_refl.
            easy. *)
            cbn in IHhas_type_ln3.
(*             specialize(IHhas_type_ln3 x H9 v H10). *)
            
            rewrite  open_subst_commute in IHhas_type_ln3.
            rewrite  open_subst_commute in IHhas_type_ln3.
(*             rewrite  open_subst_commute in IHhas_type_ln3. *)
            apply IHhas_type_ln3; easy. easy. easy.
            
            intros.
            assert(~ In x0 L).
            { unfold not. intros. apply H10. simpl. right. easy. }
            assert(~ In y L).
            { unfold not. intros. apply H11. simpl. right. easy. }
            rewrite subst_fst_id in H12, H13.
            assert( ~ (y = x \/ x0 = x \/ In x (map fst Gamma))).
            { unfold not. intros. destruct H16.
              subst. contradict H11. simpl. left. easy. 
              destruct H16. subst.
              contradict H10. simpl. left. easy.
              easy.
            }
            specialize(H5 x0 y H9 H14 H15 H12 H13 x H16 v H8).
            cbn in H5.
            rewrite  open_subst_commute in H5.
            rewrite  open_subst_commute in H5.
            cbn in H5.
            assert((x =? x0)%string = false).
            { apply String.eqb_neq. unfold not. intros.
              subst. apply H16. right. left. easy.
            }
            rewrite H17 in H5.
            assert((x =? y)%string = false).
            { apply String.eqb_neq. unfold not. intros.
              subst. apply H16. left. easy.
            }
            rewrite H18 in H5.
            rewrite  open_subst_commute in H5.
            rewrite  open_subst_commute in H5.
            cbn in H5.
            rewrite H17 in H5.
            apply H5. easy.
            
            apply cl_larger with (k := 0). lia.
            easy. easy. easy.
            
            apply IHhas_type_ln4; easy. easy. easy. (* admit. *) (* easy. *)
           }
       1: { simpl.
            case_eq((x0 =? x)%string); intros.
            + rewrite String.eqb_eq in H2. subst.
              apply lookup_not_in in H. easy. easy.
            + apply ty_var. simpl.
              rewrite ctx_subst_some with (T := T). easy. 
              apply String.eqb_neq in H2. easy.
              easy.
           }
        3: { simpl. apply ty_Lam with (i := i) (L :=x::L).
             apply IHhas_type_ln; easy.
             intros.
            assert(~ In x0 L).
            { unfold not. intros. apply H4. simpl. right. easy. }
            rewrite subst_fst_id in H5.
            assert(~ In x (map fst ((x0, A) :: Gamma))).
            { unfold not. intros. simpl in H7. destruct H7. subst. 
              apply H4. simpl. left. easy. easy. }
             specialize(H1 x0 H6 H5 x H7 v H3). cbn in H1.
             unfold open_ln in H1.
             rewrite  open_subst_commute in H1.
             rewrite  open_subst_commute in H1. cbn in H1.
             assert((x =? x0)%string = false).
            { apply String.eqb_neq. unfold not. intros. subst.
              apply H4. simpl. left. easy. }
             rewrite H8 in H1. cbn in H1.
             apply H1. easy. easy.
           }
        2: { simpl. apply ty_Pi with (i := i) (L :=x::L).
             apply IHhas_type_ln; easy.
             intros.
            assert(~ In x0 L).
            { unfold not. intros. apply H4. simpl. right. easy. }
            rewrite subst_fst_id in H5.
            assert(~ In x (map fst ((x0, t_Nat) :: Gamma))).
            { unfold not. intros. simpl in H7. destruct H7. subst. 
              apply H4. simpl. left. easy. easy. }
             specialize(H1 x0 H6 H5 x H7 v H3). cbn in H1.
             unfold open_ln in H1.
             rewrite  open_subst_commute in H1.
             cbn in H1.
             assert((x =? x0)%string = false).
            { apply String.eqb_neq. unfold not. intros. subst.
              apply H7. simpl. left. easy. }
             rewrite H8 in H1. cbn in H1.
             apply H1. easy.
          }
       2: { simpl. unfold open_ln.
            rewrite open_subst_commute.
            apply ty_App with (A := (subst_ln x v A)).
            cbn. 
            apply IHhas_type_ln1; easy.
            apply IHhas_type_ln2; easy.
            easy.
          }
       4: { simpl. apply ty_Succ.
            apply IHhas_type_ln; easy.
          }
       3: { simpl. constructor. }
       2: { simpl. constructor. }
       1: { simpl. constructor. }
Qed.

Lemma fv_open_rec_contains :
  forall (b : term_ln) (k : nat) (u : term_ln) (y : string),
    In y (fv_ln b) ->
    In y (fv_ln (open_rec_ln k u b)).
Proof.
  intros b.
  induction b; intros; simpl in *; try contradiction.
  - easy.
  - (* t_Pi *)
    apply in_app_or in H; destruct H as [HinA | HinB].
    + apply in_or_app. left. now apply IHb1.
    + apply in_or_app. right. now apply IHb2.
  - (* t_Lam *)
    apply in_app_or in H; destruct H as [HinA | HinB].
    + apply in_or_app. left. now apply IHb1.
    + apply in_or_app. right. now apply IHb2.
  - (* t_App *)
    apply in_app_or in H; destruct H as [Hinf | Hina].
    + apply in_or_app. left. now apply IHb1.
    + apply in_or_app. right. now apply IHb2.
  - (* t_Succ *) now apply IHb.
  - (* t_NatRec_ln *)
    simpl in H.
    apply in_app_iff in H.
    destruct H.
    apply in_app_iff. left.
    apply IHb1. easy.
    apply in_app_iff in H.
    destruct H.
    apply in_app_iff. right.
    apply in_app_iff. left.
    apply IHb2. easy.
    apply in_app_iff in H.
    destruct H.
    apply in_app_iff. right.
    apply in_app_iff. right.
    apply in_app_iff. left.
    apply IHb3. easy.
    apply in_app_iff. right.
    apply in_app_iff. right.
    apply in_app_iff. right.
    apply IHb4. easy.
Qed.

Lemma lookup_in: forall Gamma y T,
  lookup_ln Gamma y = Some T ->
  In y (map fst Gamma).
Proof. intro G.
       induction G; intros.
       - simpl in H. easy.
       - simpl. simpl in H.
         destruct a.
         case_eq((y =? s)%string ); intros.
         + rewrite H0 in H. inversion H. subst. simpl.
           apply String.eqb_eq in H0. left. easy.
         + rewrite H0 in H. right. apply IHG with (T := T). easy.
Qed.

Lemma fv_of_typing :
  forall Γ t T y,
    has_type_ln Γ t T ->
    In y (fv_ln t) ->
    In y (map fst Γ).
Proof. intros.
       revert y H0.
       induction H; intros.
       10:{ apply IHhas_type_ln. easy. }
       9: { simpl in H7. 
            apply in_app_iff in H7.
            destruct H7. apply IHhas_type_ln1. simpl. easy.
            apply in_app_iff in H7.
            destruct H7. apply IHhas_type_ln2. easy.
            apply in_app_iff in H7.
            destruct H7. apply IHhas_type_ln3. simpl.
            easy.
            apply IHhas_type_ln4. easy.
          }
       1: { simpl in H0. destruct H0. subst. 
            apply lookup_in with (T := T). easy.
            easy. }
       1: { simpl in H0. easy. }
       6: { simpl in H0. apply IHhas_type_ln. easy. }
       5: { simpl in H0. easy. }
       4: { simpl in H0. easy. }
       3: { simpl in H1.
            apply in_app_iff in H1.
            destruct H1. apply IHhas_type_ln1. easy.
            apply IHhas_type_ln2. easy.
          }
       2: { simpl in H2. apply in_app_iff in H2.
            destruct H2. apply IHhas_type_ln. easy.
            
            specialize(exists_fresh_not_in_list (L++(map fst Gamma)) y); intros.
            destruct H3 as (x,(Hn,H3)).
            assert(HNIN2: ~ In x (map fst Gamma)).
            { unfold not. intros.
              apply Hn. apply in_app_iff. right. easy.
            }
            assert(HNIN1: ~ In x L).
            { unfold not. intros.
              apply Hn. apply in_app_iff. left. easy.
            }
            specialize(H1 x HNIN1 HNIN2 y).
            simpl in H1.
            apply fv_open_rec_contains with (k := 0) (u := (t_fvar x)) in H2.
            apply H1 in H2. destruct H2; easy.
          }
       1: { simpl in H2. apply in_app_iff in H2.
            destruct H2. apply IHhas_type_ln. easy.
            specialize(exists_fresh_not_in_list (L++(map fst Gamma)) y); intros.
            destruct H3 as (x,(Hn,H3)).
            assert(HNIN2: ~ In x (map fst Gamma)).
            { unfold not. intros.
              apply Hn. apply in_app_iff. right. easy.
            }
            assert(HNIN1: ~ In x L).
            { unfold not. intros.
              apply Hn. apply in_app_iff. left. easy.
            }
            specialize(H1 x HNIN1 HNIN2 y).
            simpl in H1.
            apply fv_open_rec_contains with (k := 0) (u := (t_fvar x)) in H2.
            apply H1 in H2. destruct H2; easy.
          }
Qed.

Lemma subst_ln_id_from_typing :
  forall x ΓR v A,
    has_type_ln ΓR v A ->
    ~ In x (map fst ΓR) ->
    lc_ln v ->
    subst_ln x v v = v.
Proof.
  intros x ΓR v A Htyp Hfresh Hlc.
  assert (~ In x (fv_ln v)).
  { intro Hin. apply (fv_of_typing ΓR v A x Htyp) in Hin. contradiction. }
  apply subst_ln_notin_fv; assumption.
Qed.


Lemma in_map_eq: forall G1 G2 x A T,
  ~ In x (map fst G1 ++ map fst G2) ->
  lookup_ln (G1 ++ (x, A) :: G2) x = Some T -> T = A.
Proof. intro G1.
       induction G1; intros.
       - simpl in *. rewrite String.eqb_refl in H0. inversion H0. easy.
       - simpl in *. destruct a.
         case_eq( (x =? s)%string); intros.
         + rewrite String.eqb_eq in H1. subst.
           rewrite String.eqb_refl in H0. inversion H0. subst.
           contradict H. left. simpl. easy.
         + rewrite H1 in H0. apply IHG1 with (G2 := G2) (x := x).
           unfold not. intros.
           apply H. right. easy.
           easy.
Qed.

Lemma in_map_neq: forall G1 G2 x0 x A T,
  x <> x0 ->
  lookup_ln (G1 ++ (x0, A) :: G2) x = Some T ->
  lookup_ln (G1 ++ G2) x = Some T.
Proof. intro G1.
       induction G1; intros.
       - simpl in *.
         apply String.eqb_neq in H.
         rewrite H in H0. easy.
       - simpl. destruct a. simpl in H0.
         case_eq((x =? s)%string); intros.
         + rewrite H1 in H0. easy.
         + rewrite H1 in H0.
           apply IHG1 with (x0 := x0) (A := A); easy.
Qed.

Lemma weakening_ctx :
  forall Δ Γ t T,
    has_type_ln Γ t T ->
    NoDup (map fst Δ) ->
    (forall x, In x (map fst Δ) -> ~ In x (map fst Γ)) ->
    has_type_ln (Δ ++ Γ) t T.
Proof. intro G.
       induction G; intros.
       - simpl. easy.
       - simpl. destruct a. apply weakening_fresh.
         simpl in H0.
         specialize(H1 s).
         simpl in H1. 
         assert(s = s \/ In s (map fst G)).
         { left. easy. }
         specialize(H1 H2). clear H2.
         specialize(NoDup_remove [] ( map fst G)); intro HH. simpl in HH.
         apply HH in H0.
         rewrite map_app.
         unfold not. intros.
         apply in_app_iff in H2.
         destruct H0 as (H0a,H0b).
         destruct H2. apply H0b. easy.
         apply H1. easy. 
         apply IHG. easy.
         simpl in H0.
         specialize(NoDup_remove [] ( map fst G)); intro HH. simpl in HH.
         apply HH in H0. easy.
         intros.
         apply H1. simpl. right. easy.
Qed.

Theorem substitution_general :
  forall ΓL ΓR x A t B v,
    NoDup (map fst (ΓL ++ ΓR)) ->
    ~In x (map fst (ΓL ++ ΓR)) ->
    has_type_ln (ΓL ++ (x, A) :: ΓR) t B ->
    has_type_ln ΓR v A ->
    lc_ln v ->
    has_type_ln (subst_ctx x v (ΓL ++ ΓR)) (subst_ln x v t) (subst_ln x v B).
Proof.
  intros ΓL ΓR x A t B v Hnd Hf Ht Hu Hc .
  remember (ΓL ++ (x, A) :: ΓR) as G.
  revert v x A Hf Hu Hc HeqG. revert ΓL ΓR Hnd.

  induction Ht; intros.
  10:{
  subst.
  apply ty_conv with (A := (subst_ln x v A)).
  apply IHHt with (A := A0). easy. easy. easy. easy. easy.
  apply convertible_subst. easy. easy.
  }
  9: {
  subst.
  simpl. rewrite open_subst_commute. 
  rewrite open_subst_commute.
  eapply ty_NatRec_strong with (k := k) (L := x::L++(map fst (ΓL ++ ΓR))) (sbody := (subst_ln x v sbody)).
  apply subst_preserve_closdness. easy. easy. 
  apply subst_preserve_closdness. easy. easy. 
  simpl in IHHt1.
  apply IHHt1 with (A := A). easy. easy. easy. easy. easy.
(*   apply convertible_subst with (x := x) (v := v) in H; try easy. *)
  
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H3. simpl. right. apply in_app_iff. left. easy. }
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { unfold not. intros. simpl in H6. destruct H6. subst. apply H3. simpl. left. easy. easy. }
  assert(HN: NoDup (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { assert(HNN: ~ In x0 (map fst (ΓL ++ ΓR))).
    { unfold not. intros. apply H3. simpl. right. apply in_app_iff. right. easy. }
    simpl.
    constructor; easy.
  }
  simpl. simpl in H2.
  assert(HN2: ~ In x0 (map fst (ΓL ++ (x, A) :: ΓR))).
  { unfold not. intros. apply H4.
    rewrite map_app in H7.
    apply in_app_iff in H7. simpl.
    rewrite subst_fst_id. rewrite map_app.
    apply in_app_iff. destruct H7. left.
    easy.
    rewrite subst_fst_id in H4.
    simpl in H4. destruct H4. subst. simpl in H7.
    destruct H7. subst.
    contradict H6. left. easy.
    rewrite map_app.
    apply in_app_iff. 
    right. easy.
  }
  specialize(H0 x0 H5 HN2 ((x0, t_Nat) :: ΓL) ΓR HN v x A H6).
  simpl in H0.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H3. subst. simpl. left. easy. }
  simpl in H0.
  (*
  rewrite H5 in H1.
  simpl in H1. unfold open_ln. simpl. *)
  unfold open_ln in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite H7 in H0.
  apply H0. easy. easy. easy. easy.
  specialize(IHHt2 ΓL ΓR Hnd v x A).
  simpl in IHHt2.
(*   rewrite  open_subst_commute in IHHt2. *)
  rewrite  open_subst_commute in IHHt2.
  apply IHHt2; easy.
  easy.
  
   (* easy. *)
  cbn.
(*   assert(subst_ln x v s ≡ₗₙ subst_ln x v (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody))).
  { apply convertible_subst. easy. easy. }
  apply convertible_trans with (y := subst_ln x v (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody))).
  easy.
  cbn.
  rewrite  open_subst_commute. cbn.
  apply convertible_refl. easy.
  *)
  specialize(IHHt3 ΓL ΓR Hnd v x A). 
  simpl in IHHt3.
  rewrite  open_subst_commute in IHHt3.
  rewrite  open_subst_commute in IHHt3.
  apply IHHt3; easy.
  easy. easy.
  simpl in IHHt4.
  
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H4. simpl. right. apply in_app_iff. left. easy. }
  assert(~ In y L).
  { unfold not. intros. apply H5. simpl. right. apply in_app_iff. left. easy. }
  assert(~ In x0 (map fst (ΓL ++ (x, A) :: ΓR))).
  { unfold not. intros. rewrite map_app in H10. apply in_app_iff in H10.
    simpl in H10. destruct H10. subst. apply H4. simpl. right.
    apply in_app_iff. right. rewrite map_app. apply in_app_iff. left. easy.
    destruct H10. subst. apply H4. left. easy.
    apply H4. simpl. right. rewrite map_app. apply in_app_iff. right.
    apply in_app_iff. right. easy.
  }
  assert(~ In y (map fst (ΓL ++ (x, A) :: ΓR))).
  { unfold not. intros. rewrite map_app in H11. apply in_app_iff in H11.
    simpl in H11. destruct H11. subst. apply H5. simpl. right.
    apply in_app_iff. right. rewrite map_app. apply in_app_iff. left. easy.
    destruct H11. subst. apply H5. left. easy.
    apply H5. simpl. right. rewrite map_app. apply in_app_iff. right.
    apply in_app_iff. right. easy.
  }
  assert(HN: NoDup (y :: x0 :: map fst (ΓL ++ ΓR))).
  { constructor.
    simpl. unfold not.
    intros.
    destruct H12. subst. easy.
    apply H7. simpl.
    rewrite subst_fst_id. easy.
    constructor.
    simpl. unfold not.
    intros.
    apply H6. simpl.
    rewrite subst_fst_id. easy.
    easy.
  }
  specialize(H2 x0 y H3 H8 H9 H10 H11
  ((y, open_rec_ln 0 (t_fvar x0) body) :: (x0, t_Nat) :: ΓL) ΓR
  HN v x A).
  cbn in H4.
  rewrite  open_subst_commute in H2.
  rewrite  open_subst_commute in H2.
  rewrite  open_subst_commute in H2.
(*   rewrite  open_subst_commute in H2. *)
  cbn in H2.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros.
    subst. contradict H10.
    rewrite map_app. apply in_app_iff. right.
    simpl. left. easy.
  }
  assert((x =? y)%string = false).
  { apply String.eqb_neq. unfold not. intros.
    subst. contradict H11.
    rewrite map_app. apply in_app_iff. right.
    simpl. left. easy.
  }
  cbn in H2.
  rewrite H12, H13 in H2.
  rewrite  open_subst_commute in H2.
  cbn in H2.
  rewrite H12 in H2.
  apply H2.
  unfold not. intros.
  destruct H14. subst. rewrite String.eqb_refl in H13. easy.
  destruct H14. subst. rewrite String.eqb_refl in H12. easy. easy. easy.
  easy. easy. easy. 
  apply cl_larger with (k := 0). lia. easy. 
  apply cl_larger with (k := 0). lia. easy. 
  easy.
  
  apply IHHt4 with (A := A); easy.
  easy. easy. (* easy. *) (* admit. *) 
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
  specialize(IHHt1 ΓL ΓR Hnd v x A0).
  simpl in IHHt1.
  apply IHHt1; easy.
  apply IHHt2 with (A := A0); easy.
  easy.
  } 
  4:{ subst. 
  simpl.
  apply ty_Lam with (i := i) (L := x::L++(map fst (ΓL ++ ΓR))).
  simpl in IHHt. apply IHHt with (A := A0); easy.
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H1. simpl. right. apply in_app_iff. left. easy. }
  rewrite subst_fst_id in H2.
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { unfold not. intros. simpl in H4. destruct H4. subst. apply H1. simpl. left. easy. easy. }
  assert(HN: NoDup (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { assert(HNN: ~ In x0 (map fst (ΓL ++ ΓR))).
    { unfold not. intros. apply H1. simpl. right. apply in_app_iff. right. easy. }
    simpl.
    constructor; easy.
  }
  assert(HNIN:  ~ In x0 (map fst (ΓL ++ (x, A0) :: ΓR))).
  { unfold not. intros.
    apply H1. rewrite map_app in H5. apply in_app_iff in H5.
    destruct H5. simpl. right.
    apply in_app_iff. right. rewrite map_app.
    apply in_app_iff. left. easy.
    simpl in H5.
    destruct H5.
    simpl. left. easy.
    simpl. right. apply in_app_iff. right. rewrite map_app. 
    apply in_app_iff. right. easy.
  }
  specialize(H0 x0 H3 HNIN ((x0, A) :: ΓL) ΓR HN v x A0 H4).
  simpl in H0.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H1. subst. simpl. left. easy. }
(*   rewrite H4 in H0. *)
  simpl in H0. unfold open_ln. simpl.
  unfold open_ln in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite H5 in H0. simpl in H0.
  apply H0. easy. easy. easy. easy. easy.
  }
  3:{ subst.
  simpl.
  apply ty_Pi with (i := i) (L := x::L++(map fst (ΓL ++ ΓR))).
  simpl in IHHt. apply IHHt with (A := A0); easy.
  intros.
  assert(~ In x0 L).
  { unfold not. intros. apply H1. simpl. right. apply in_app_iff. left. easy. }
  assert(~ In x (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  rewrite subst_fst_id in H2.
  { unfold not. intros. simpl in H4. destruct H4. subst. apply H1. simpl. left. easy. easy. }
  assert(HN: NoDup (map fst (((x0, t_Nat) :: ΓL) ++ ΓR))).
  { assert(HNN: ~ In x0 (map fst (ΓL ++ ΓR))).
    { unfold not. intros. apply H1. simpl. right. apply in_app_iff. right. easy. }
    simpl.
    constructor; easy.
  }
  assert(HNIN:  ~ In x0 (map fst (ΓL ++ (x, A0) :: ΓR))).
  { unfold not. intros.
    apply H1. rewrite map_app in H5. apply in_app_iff in H5.
    destruct H5. simpl. right.
    apply in_app_iff. right. rewrite map_app.
    apply in_app_iff. left. easy.
    simpl in H5.
    destruct H5.
    simpl. left. easy.
    simpl. right. apply in_app_iff. right. rewrite map_app. 
    apply in_app_iff. right. easy.
  }
  specialize(H0 x0 H3 HNIN ((x0, A) :: ΓL) ΓR HN v x A0 H4).
  simpl in H0.
  assert((x =? x0)%string = false).
  { apply String.eqb_neq. unfold not. intros. apply H1. subst. simpl. left. easy. }
(*   rewrite H4 in H0. *)
  simpl in H0. unfold open_ln. simpl.
  unfold open_ln in H0.
  rewrite open_subst_commute in H0. simpl in H0.
  rewrite H5 in H0. simpl in H0.
  apply H0. easy. easy. easy. easy.
  }
  2:{ subst.
  simpl.
  constructor.
  }
  1:{ subst. simpl. 
      case_eq((x0 =? x)%string); intros.
      - rewrite String.eqb_eq in H0. subst.
        assert(T = A).
        { rewrite map_app in Hnd, Hf.
          apply in_map_eq with (G1 := ΓL) (G2 := ΓR) (x := x); easy.
        }
        subst.
        assert((subst_ctx x v (ΓL ++ ΓR)) = (subst_ctx x v ΓL ++ subst_ctx x v ΓR)) by apply subst_ctx_app_or.
        rewrite H0. clear H0.
        apply weakening_ctx. 
        assert((subst_ln x v v) = v).
        { apply subst_ln_id_from_typing with (ΓR := ΓR) (A := A); try easy.
          unfold not. intros. apply Hf.
          rewrite map_app.
          apply in_app_iff. right. easy.
        }
        rewrite <- H0 at 2.
        apply env_subst; try easy.
        { unfold not. intros. apply Hf.
          rewrite map_app.
          apply in_app_iff. right. easy.
        }
        rewrite subst_fst_id.
        rewrite map_app in Hnd.
        apply NoDup_app_remove_r in Hnd. easy.
        intros.
        apply NoDup_left_disjoint_right with (ΓL := (map fst (subst_ctx x v ΓL))).
        rewrite !subst_fst_id.
        rewrite map_app in Hnd.
        easy.
        easy.
      - apply ty_var. simpl.
        assert(lookup_ln (ΓL ++ ΓR) x = Some T).
        { apply in_map_neq with (x0 := x0) (A := A); try easy.
          apply String.eqb_neq. rewrite String.eqb_sym. easy.
        }
        rewrite ctx_subst_some with (T := T). easy.
        apply String.eqb_neq in H0. easy. easy.
    }
Qed.

Corollary substitution_head :
  forall Γ x A t B v,
    NoDup (map fst Γ) ->
    ~ In x (map fst Γ) ->
    lc_ln v ->
    has_type_ln Γ v A ->
    has_type_ln ((x, A) :: Γ) t B ->
    has_type_ln (subst_ctx x v Γ) (subst_ln x v t) (subst_ln x v B).
Proof. intros. specialize (substitution_general []); intro HH.
       simpl in HH. apply HH with (A := A); easy.
Qed.

Lemma step_implies_beta_ln :
  forall t t',
    step_ln t t' ->
    beta_ln t t'.
Proof.
  intros t t' H.
  induction H.
  11:{ apply beta_natrec_n_ln. easy. }
  10:{ apply beta_natrec_s_ln. easy. }
  9: { apply beta_natrec_z_ln. easy. }
  8: { apply beta_natrec_P_ln. easy. }
  7: { apply beta_head_step_ln. apply b_natrec_succ_ln_strict; easy. }
  6: { apply beta_head_step_ln. apply b_natrec_zero_ln_strict; easy. }
  5: { apply beta_succ_ln. easy. }
  4: { apply beta_lam_A_ln. easy. }
  3: { apply beta_app2_ln. easy. }
  2: { apply beta_app1_ln. easy. }
  1: { apply beta_head_step_ln. apply b_beta_app_ln; easy. }
Qed.

Lemma step_implies_convertible_ln :
  forall t t',
    step_ln t t' ->
    convertible_ln t t'.
Proof.
  intros t t' H. 
  constructor.
  apply step_implies_beta_ln. easy.
Qed.


Lemma convertible_natrec_n :
  forall P z s n n',
    convertible_ln n n' ->
    convertible_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s n').
Proof.
  intros P z s n n' H.
  induction H.
  - constructor. apply beta_natrec_n_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_NatRec_ln P z s y). easy.
    easy.
Qed.

Lemma convertible_natrec_s :
  forall P z s s' n,
    convertible_ln s s' ->
    convertible_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z s' n).
Proof.
  intros P z s n n' H.
  induction H.
  - constructor. apply beta_natrec_s_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_NatRec_ln P z y n'). easy.
    easy.
Qed.

Lemma convertible_natrec_z :
  forall P z z' s n,
    convertible_ln z z' ->
    convertible_ln (t_NatRec_ln P z s n) (t_NatRec_ln P z' s n).
Proof.
  intros P z s n n' H.
  induction H.
  - constructor. apply beta_natrec_z_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_NatRec_ln P y n n'). easy.
    easy.
Qed.

Lemma convertible_natrec_P :
  forall P P' z s n,
    convertible_ln P P' ->
    convertible_ln (t_NatRec_ln P z s n) (t_NatRec_ln P' z s n).
Proof.
  intros P z s n n' H.
  induction H.
  - constructor. apply beta_natrec_P_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_NatRec_ln y s n n'). easy.
    easy.
Qed.

Lemma convertible_succ :
  forall u u',
    convertible_ln u u' ->
    convertible_ln (t_Succ u) (t_Succ u').
Proof.
  intros.
  induction H.
  - constructor. apply beta_succ_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_Succ y). easy.
    easy.
Qed.

Lemma convertible_tapp_t1 :
  forall t1 t1' t2 ,
    convertible_ln t1 t1' ->
    convertible_ln (t_App t1 t2) (t_App t1' t2).
Proof.
  intros.
  induction H.
  - constructor. apply beta_app1_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_App y t2). easy.
    easy.
Qed.

Lemma convertible_tapp_t2 :
  forall t1 t2 t2',
    convertible_ln t2 t2' ->
    convertible_ln (t_App t1 t2) (t_App t1 t2').
Proof.
  intros.
  induction H.
  - constructor. apply beta_app2_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_App t1 y). easy.
    easy.
Qed.

Lemma convertible_tlam_t1 :
  forall t1 t1' t2 ,
    convertible_ln t1 t1' ->
    convertible_ln (t_Lam t1 t2) (t_Lam t1' t2).
Proof.
  intros.
  induction H.
  - constructor. apply beta_lam_A_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_Lam y t2). easy.
    easy.
Qed.

Lemma convertible_tlam_t2 :
  forall t1 t2 t2',
    convertible_ln t2 t2' ->
    convertible_ln (t_Lam t1 t2) (t_Lam t1 t2').
Proof.
  intros.
  induction H.
  - constructor. apply beta_lam_b_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_Lam t1 y). easy.
    easy.
Qed.

Lemma convertible_tPi_t1 :
  forall t1 t1' t2 ,
    convertible_ln t1 t1' ->
    convertible_ln (t_Pi t1 t2) (t_Pi t1' t2).
Proof.
  intros.
  induction H.
  - constructor. apply beta_pi_A_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_Pi y t2). easy.
    easy.
Qed.

Lemma convertible_tPi_t2 :
  forall t1 t2 t2',
    convertible_ln t2 t2' ->
    convertible_ln (t_Pi t1 t2) (t_Pi t1 t2').
Proof.
  intros.
  induction H.
  - constructor. apply beta_pi_B_ln. easy.
  - apply rst_refl.
  - apply convertible_sym. easy.
  - apply convertible_trans with (y := t_Pi t1 y). easy.
    easy.
Qed.

Lemma open_rec_ln_monotone_u :
  forall b k (u u' : term_ln),
    u ≡ₗₙ u' ->
    open_rec_ln k u b ≡ₗₙ open_rec_ln k u' b.
Proof.
  induction b; intros.
  10:{
   pose proof (IHb1 k u u' H) as C1.
    pose proof (IHb2 k u u' H) as C2.
    pose proof (IHb3 k u u' H) as C3.
    pose proof (IHb4 k u u' H) as C4.
    apply convertible_trans with (y := t_NatRec_ln
      (open_rec_ln k u b1)
      (open_rec_ln k u b2)
      (open_rec_ln k u b3)
      (open_rec_ln k u' b4)).
    simpl.
    apply convertible_natrec_n.
    easy.
    simpl.
    apply convertible_trans with (y := t_NatRec_ln
      (open_rec_ln k u b1)
      (open_rec_ln k u b2)
      (open_rec_ln k u' b3)
      (open_rec_ln k u' b4)).
    simpl.
    apply convertible_natrec_s.
    easy.
    simpl.
    apply convertible_trans with (y := t_NatRec_ln
      (open_rec_ln k u b1)
      (open_rec_ln k u' b2)
      (open_rec_ln k u' b3)
      (open_rec_ln k u' b4)).
    simpl.
    apply convertible_natrec_z.
    easy.
    simpl.
    apply convertible_trans with (y := t_NatRec_ln
      (open_rec_ln k u' b1)
      (open_rec_ln k u' b2)
      (open_rec_ln k u' b3)
      (open_rec_ln k u' b4)).
    simpl.
    apply convertible_natrec_P.
    easy.
    simpl.
    apply convertible_refl.
  }
  9:{
  simpl.
  apply convertible_succ. apply IHb. easy.
  }
  8:{ simpl. apply convertible_refl. }
  7:{ simpl. apply convertible_refl. }
  6:{ simpl. 
     apply convertible_trans with (y := t_App (open_rec_ln k u b1) (open_rec_ln k u' b2)).
     apply convertible_tapp_t2. apply IHb2. easy.
     apply convertible_tapp_t1. apply IHb1. easy.
    }
  5:{ simpl.
      apply convertible_trans with (y := t_Lam (open_rec_ln k u b1) (open_rec_ln (S k) u' b2)).
      apply convertible_tlam_t2. apply IHb2. easy.
      apply convertible_tlam_t1. apply IHb1. easy.
     }
  4:{ simpl. 
      apply convertible_trans with (y := t_Pi (open_rec_ln k u b1) (open_rec_ln (S k) u' b2)).
      apply convertible_tPi_t2. apply IHb2. easy.
      apply convertible_tPi_t1. apply IHb1. easy.
    }
  3:{ simpl. apply convertible_refl. }
  2:{ simpl. apply convertible_refl. }
  1:{ simpl. destruct (n =? k). easy. apply convertible_refl. }
Qed.

Lemma natrec_inversion_weaker :
  forall Γ P z n s A,
    has_type_ln Γ (t_NatRec_ln P z s n) A ->
    exists k L body sbody,
    lc_rec_ln 1 body /\
    lc_rec_ln 2 sbody /\
    P =  (t_Lam t_Nat body) /\
    s = (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody)) /\
      has_type_ln Γ P (t_Pi t_Nat (t_Type k)) /\
(*       convertible_ln P (t_Lam t_Nat body) /\ *)
      (forall x : string,
          ~ In x L ->
          ~ In x (map fst Γ) ->
          has_type_ln ((x, t_Nat) :: Γ)
              (open_ln body (t_fvar x))
              (open_ln (t_Type k) (t_fvar x))) /\
      (* base case: z : P 0  — using the consistent expanded form *)
       has_type_ln Γ z (open_rec_ln 0 t_Zero body) /\
      (* step case: s : Π (m:Nat). Π (ih : P m), P (S m)  *)
(*       convertible_ln s (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody)) /\ *)
      has_type_ln Γ (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody))
        (t_Pi t_Nat
            (t_Pi (open_rec_ln 0 (t_bvar 0) body)
                  (open_rec_ln 0 (t_Succ (t_bvar 1)) body))) /\
      (forall x y, x <> y ->
       ~ In x L -> ~ In y L ->
       (~ In x (map fst Γ) -> ~ In y (map fst Γ) ->
         has_type_ln ((y, open_rec_ln 0 (t_fvar x) body) :: (x, t_Nat) :: Γ)
                     (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody))
                     (open_rec_ln 0 (t_Succ (t_fvar x)) body)))
      /\
      (* scrutinee typing *)
      has_type_ln Γ n t_Nat /\
      (* result type: P n — consistent expanded form *)
      convertible_ln A
        (open_rec_ln 0 n body).
Proof.
  intros Γ P z n s A Hty.
  remember (t_NatRec_ln P z s n)  as t eqn:Heqt.
  revert Heqt. revert z n P s. 
  induction Hty; intros; try (inversion Heqt).
  - subst.
    cbn in H1.
    exists k, L, body, sbody. repeat split; try assumption.
    apply convertible_refl.
  - subst.
    specialize(IHHty z n P s eq_refl).
    destruct IHHty as (k,(L,(body,(sbody,IHH)))).
    exists k, L, body, sbody.
    split. easy. split. easy. split. easy.
    split. easy. split. easy. split. easy.
    split. easy. split. easy.
    split. easy. split. easy.
(*     split. easy. split. easy. *)
    apply convertible_sym in H.
    apply convertible_trans with (y := A); easy.
Qed.

Lemma natrec_inversion_stronger :
  forall Γ body z n sbody A,
    has_type_ln Γ (t_NatRec_ln (t_Lam t_Nat body) z (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody)) n) A ->
    exists k L,
      has_type_ln Γ (t_Lam t_Nat body) (t_Pi t_Nat (t_Type k)) /\
(*       convertible_ln P (t_Lam t_Nat body) /\ *)
      (forall x : string,
          ~ In x L ->
          ~ In x (map fst Γ) ->
          has_type_ln ((x, t_Nat) :: Γ)
              (open_ln body (t_fvar x))
              (open_ln (t_Type k) (t_fvar x))) /\
      (* base case: z : P 0  — using the consistent expanded form *)
       has_type_ln Γ z (open_rec_ln 0 t_Zero body) /\
      (* step case: s : Π (m:Nat). Π (ih : P m), P (S m)  *)
(*       convertible_ln s (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 1) body) sbody)) /\ *)
      has_type_ln Γ (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody))
        (t_Pi t_Nat
            (t_Pi (open_rec_ln 0 (t_bvar 0) body)
                  (open_rec_ln 0 (t_Succ (t_bvar 1)) body))) /\
      (forall x y, x <> y ->
       ~ In x L -> ~ In y L ->
       (~ In x (map fst Γ) -> ~ In y (map fst Γ) ->
         has_type_ln ((y, open_rec_ln 0 (t_fvar x) body) :: (x, t_Nat) :: Γ)
                     (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody))
                     (open_rec_ln 0 (t_Succ (t_fvar x)) body)))
      /\
      (* scrutinee typing *)
      has_type_ln Γ n t_Nat /\
      (* result type: P n — consistent expanded form *)
      convertible_ln A
        (open_rec_ln 0 n body).
Proof.
  intros Γ body z n sbody A Hty.
  remember (t_NatRec_ln (t_Lam t_Nat body) z (t_Lam t_Nat (t_Lam (open_rec_ln 0 (t_bvar 0) body) sbody))
       n)  as t eqn:Heqt.
  revert Heqt. revert z n body sbody. 
  induction Hty; intros; try (inversion Heqt).
  - subst.
    cbn in H1.
    exists k, L. repeat split; try assumption.
    apply convertible_refl.
  - subst.
    specialize(IHHty z n body sbody eq_refl).
    destruct IHHty as (k,(L,IHH)).
    exists k, L.
    split. easy. split. easy. split. easy.
    split. easy. split. easy. split. easy.
(*     split. easy. split. easy. *)
    apply convertible_sym in H.
    apply convertible_trans with (y := A); easy.
Qed.

Lemma succ_inversion :
  forall Γ n T,
    has_type_ln Γ (t_Succ n) T ->
    has_type_ln Γ n t_Nat /\ convertible_ln T t_Nat.
Proof. intros.
       remember (t_Succ n) as t. revert n Heqt.
       induction H; intros; try easy.
       - inversion Heqt. subst.
         split. easy. apply convertible_refl.
       - apply IHhas_type_ln in Heqt.
         split. easy.
         apply convertible_sym in H0.
         apply convertible_trans with (y := A); easy.
Qed.

Lemma lam_inversion :
  forall Γ A b T,
    has_type_ln Γ (t_Lam A b) T ->
    exists i B L,
      has_type_ln Γ A (t_Type i) /\
      (forall x, ~ In x L -> ~ In x (map fst Γ) ->
         has_type_ln ((x, A) :: Γ)
                      (open_ln b (t_fvar x))
                      (open_ln B (t_fvar x))) /\
      convertible_ln T (t_Pi A B).
Proof. intros.
       remember (t_Lam A b) as t.
       revert A b Heqt.
       induction H; intros; try easy.
       - inversion Heqt. subst.
         exists i. exists B, L.
         split. easy.
         split. intros.
         apply H0; easy.
         apply convertible_refl.
       - apply IHhas_type_ln in Heqt.
         destruct Heqt as (i,(C,(L,(Ha,(Hb,Hc))))).
         exists i, C, L.
         split. easy. split. easy.
         apply convertible_sym in H0.
         apply convertible_trans with (y := A); easy.
Qed.


Lemma pi_inversion :
  forall Γ A B T,
    has_type_ln Γ (t_Pi A B) T ->
    exists i j L,
      has_type_ln Γ A (t_Type i) /\
      (forall x, ~ In x L -> ~ In x (map fst Γ) ->
         has_type_ln ((x, A) :: Γ)
                      (open_ln B (t_fvar x))
                      (t_Type j)) /\
      convertible_ln T (t_Type (Nat.max i j)).
Proof. intros.
       remember (t_Pi A B) as t.
       revert A B Heqt.
       induction H; intros; try easy.
       - inversion Heqt. subst.
         exists i, j. exists L.
         split. easy.
         split. intros.
         apply H0; easy.
         apply convertible_refl.
       - apply IHhas_type_ln in Heqt.
         destruct Heqt as (i,(j,(L,(Ha,(Hb,Hc))))).
         exists i, j, L.
         split. easy. split. easy.
         apply convertible_sym in H0.
         apply convertible_trans with (y := A); easy.
Qed.

Lemma app_inversion :
  forall Γ t1 t2 T,
    has_type_ln Γ (t_App t1 t2) T ->
    exists A B,
      has_type_ln Γ t1 (t_Pi A B) /\
      has_type_ln Γ t2 A /\
      convertible_ln T (open_ln B t2).
Proof. intros.
       remember (t_App t1 t2)  as t.
       revert t1 t2 Heqt.
       induction H; intros; try easy.
       - inversion Heqt. subst.
         exists A, B.
         split. easy. split. easy.
         apply convertible_refl.
       - apply IHhas_type_ln in Heqt.
         destruct Heqt as (U,(V,(Hu,(Hv,Ht)))).
         exists U, V. split. easy.
         split. easy.
         apply convertible_sym in H0.
         apply convertible_trans with (y := A); easy.
Qed.

Lemma in_step: forall G1 G2 x A,
  ~ In x (map fst (G1 ++ G2)) ->
   lookup_ln (G1 ++ (x, A) :: G2) x = Some A.
Proof. intro G1.
       induction G1; intros.
       - simpl. rewrite String.eqb_refl. easy.
       - simpl. destruct a.
         case_eq((x =? s)%string); intros.
         + contradict H.
           simpl. left.
           apply String.eqb_eq in H0. easy.
         + apply IHG1.
           unfold not. intros.
           apply H. simpl. right. easy.
Qed.

Lemma out_step: forall G1 G2 x y A T,
  x <> y ->
  lookup_ln (G1 ++ G2) x = Some T ->
  lookup_ln (G1 ++ (y, A) :: G2) x = Some T.
Proof. intro G1.
       induction G1; intros.
       - simpl. apply String.eqb_neq in H. rewrite H.
         simpl in H0. easy.
       - simpl. destruct a.
         case_eq((x =? s)%string); intros.
         + simpl in H0. rewrite H1 in H0. easy.
         + apply IHG1. easy. simpl in H0.
           rewrite H1 in H0. easy.
Qed.

Lemma context_conversion_general :
  forall ΓL ΓR x A A' t T i,
    (* x must not occur in the left prefix, so the binding we replace is the one we target *)
    ~ In x (map fst (ΓL ++ ΓR)) ->
    convertible_ln A A' ->
    (* A' must be well-typed in the surrounding context where x is absent *)
    has_type_ln (ΓL ++ ΓR) A' (t_Type i) ->
    has_type_ln (ΓL ++ (x, A) :: ΓR) t T ->
    has_type_ln (ΓL ++ (x, A') :: ΓR) t T.
Proof. intros.
       revert H0 H1. revert i H.
       remember (ΓL ++ (x, A) :: ΓR) as G.
       revert x A A' HeqG. revert ΓL ΓR.
       induction H2; intros.
       10:{
       apply ty_conv with (A := A).
       apply IHhas_type_ln with (A := A0) (i := i). subst. easy.
       easy. easy. easy. easy.
       }
       9:{
       subst.
       apply ty_NatRec_strong with (k := k) (L := L) (sbody := sbody).
       easy. easy.
       apply IHhas_type_ln1 with (A := A) (i := i); easy.
(*        easy. *)
       intros.
       assert(HN0: ~ In x0 (map fst (ΓL ++ (x, A) :: ΓR))).
       { unfold not. intros.
         apply H7. rewrite map_app. rewrite map_app in H8.
         apply in_app_iff in H8. apply in_app_iff. 
         destruct H8. left. easy.
         simpl in H8.
         destruct H8. right. simpl. left. easy.
         right. right. easy.
       }
       specialize(H0 x0 H6 HN0 ((x0, t_Nat) :: ΓL) ΓR x A A').
       apply H0 with (i := i). easy.
       unfold not. intros.
       apply H3. simpl in H8.
       destruct H8. subst.
       contradict H7. rewrite map_app.
       apply in_app_iff. right. simpl. left. easy.
       easy.
       easy. simpl.
       apply weakening_fresh.
       unfold not. intros.
       apply HN0. rewrite map_app. rewrite map_app in H8.
       apply in_app_iff in H8. destruct H8.
       simpl.
       apply in_app_iff. left. easy.
       simpl.
       apply in_app_iff. right. right. easy.
       easy.
       apply IHhas_type_ln2 with (A := A) (i := i); easy.
(*        cbn. easy. *)
       
       apply IHhas_type_ln3 with (A := A) (i := i); easy.
       
       intros.
       specialize(H2 x0 y H6 H7 H8).
       assert( ~ In x0 (map fst (ΓL ++ (x, A) :: ΓR))).
       { unfold not. intros.
         apply H9.
         rewrite map_app. rewrite in_app_iff.
         rewrite map_app in H11. apply in_app_iff in H11.
         destruct H11. left. easy.
         right. simpl. simpl in H11. easy.
       }
       assert( ~ In y (map fst (ΓL ++ (x, A) :: ΓR))).
       { unfold not. intros.
         apply H10.
         rewrite map_app. rewrite in_app_iff.
         rewrite map_app in H12. apply in_app_iff in H12.
         destruct H12. left. easy.
         right. simpl. simpl in H11. easy.
       }
       specialize(H2 H11 H12
       ((y, open_rec_ln 0 (t_fvar x0) body) :: (x0, t_Nat) :: ΓL) ΓR
       x A A').
       cbn in H2.
       apply H2 with (i := i). easy.
       unfold not. intros.
       destruct H13. subst. apply H12.
       rewrite map_app. rewrite in_app_iff. right. left. easy.
       destruct H13. subst. apply H11.
       rewrite map_app. rewrite in_app_iff. right. left. easy.
       easy.
       easy. 
       apply weakening_fresh.
       unfold not. intros.
       apply H12. rewrite map_app. rewrite in_app_iff.
       simpl in H13. destruct H13.
       subst. right. left. easy.
       rewrite map_app in H13.
       apply in_app_iff in H13.
       destruct H13. left. easy. right. right. easy.
       apply weakening_fresh.
       unfold not. intros.
       apply H11.
       rewrite map_app in H13.
       apply in_app_iff in H13.
       destruct H13.
       rewrite map_app. rewrite in_app_iff.
       left. easy. 
       rewrite map_app. rewrite in_app_iff.
       right. right. easy. easy.

       apply IHhas_type_ln4 with (A := A) (i := i); easy.
       }
       4:{
       apply ty_Lam with (i := i) (L := L++(map fst Gamma)).
       subst.
       apply IHhas_type_ln with (A := A0) (i := i0); easy.
       intros.
       subst.
       assert(HN0: ~ In x0 L).
       { unfold not. intros.
         apply H5. apply in_app_iff. left. easy.
       }
       assert(HN1: ~ In x0 (map fst (ΓL ++ (x, A0) :: ΓR))).
       { unfold not. intros.
         apply H6.
         rewrite map_app. rewrite map_app in H7.
         apply in_app_iff. apply in_app_iff in H7.
         destruct H7. left. easy.
         simpl in H7. destruct H7. subst.
         contradict H6. rewrite map_app. apply in_app_iff.
         right. left. easy.
         right. right. easy.
       }
       specialize(H0 x0 HN0 HN1 ((x0, A) :: ΓL) ΓR x A0).
       apply H0 with (i := i0).
       easy.
       unfold not. intros.
       apply H1.
       simpl in H7. destruct H7. subst.
       contradict H6.
       simpl. rewrite map_app.
       apply in_app_iff. right. left. easy.
       easy.
       easy. simpl.
       apply weakening_fresh.
       
       unfold not. intros.
       apply H6. rewrite map_app.
       rewrite map_app in H7.
       apply in_app_iff in H7.
       destruct H7. 
       apply in_app_iff. left. easy.
       apply in_app_iff. right. right. easy.
       easy.
       }
       3:{
       apply ty_Pi with (i := i) (L := L++(map fst Gamma)).
       subst.
       apply IHhas_type_ln with (A := A0) (i := i0); easy.
       intros.
       subst.
       assert(HN0: ~ In x0 L).
       { unfold not. intros.
         apply H5. apply in_app_iff. left. easy.
       }
       assert(HN1: ~ In x0 (map fst (ΓL ++ (x, A0) :: ΓR))).
       { unfold not. intros.
         apply H6.
         rewrite map_app. rewrite map_app in H7.
         apply in_app_iff. apply in_app_iff in H7.
         destruct H7. left. easy.
         simpl in H7. destruct H7. subst.
         contradict H6. rewrite map_app. apply in_app_iff.
         right. left. easy.
         right. right. easy.
       }
       specialize(H0 x0 HN0 HN1 ((x0, A) :: ΓL) ΓR x A0).
       apply H0 with (i := i0).
       easy.
       unfold not. intros.
       apply H1.
       simpl in H7. destruct H7. subst.
       contradict H6.
       simpl. rewrite map_app.
       apply in_app_iff. right. left. easy.
       easy.
       easy. simpl.
       apply weakening_fresh.
       unfold not. intros.
       apply H6. rewrite map_app.
       rewrite map_app in H7.
       apply in_app_iff in H7.
       destruct H7. 
       apply in_app_iff. left. easy.
       apply in_app_iff. right. right. easy.
       easy.
       }
       1:{
       subst.
       case_eq(String.eqb x0 x); intros.
       - rewrite String.eqb_eq in H3. subst.
         assert(A = T).
         { apply in_map_eq in H. easy. rewrite map_app in H0. easy. }
         subst.
         apply ty_conv with (A := A').
         apply ty_var.
         apply in_step. easy.
         apply convertible_sym. easy.
       - apply ty_var.
         apply in_map_neq in H.
         apply out_step.
         apply String.eqb_neq in H3. easy. easy.
         apply String.eqb_neq in H3. easy.
       }
       2:{
       apply ty_App with (A := A). 
       apply IHhas_type_ln1 with (A := A0) (i := i). subst. easy.
       easy. easy. easy.
       apply IHhas_type_ln2 with (A := A0) (i := i); easy.
       }
       4:{
       apply ty_Succ.
       apply IHhas_type_ln with (A := A) (i := i); easy.
       }
       3:{ constructor. }
       2:{ constructor. }
       1:{ constructor. }
Qed.

Lemma beta_natrec_cases_full :
  forall P z s n P' z' s' n',
    beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P' z' s' n') ->
    (beta_ln P P' /\ z = z' /\ s = s' /\ n = n')
    \/ (P = P' /\ beta_ln z z' /\ s = s' /\ n = n')
    \/ (P = P' /\ z = z' /\ beta_ln s s' /\ n = n')
    \/ (P = P' /\ z = z' /\ s = s' /\ beta_ln n n')
    \/ (exists u, beta_head_ln (t_NatRec_ln P z s n) u /\ u = t_NatRec_ln P' z' s' n').
Proof.
  intros P z s n P' z' s' n' H.
  inversion H; clear H.
  - (* beta_head_step_ln: the step came from a head-step *)
    right. right. right. right. exists u. subst. split; [assumption | reflexivity].
  - subst. left. easy.
  - subst. right. left. easy.
  - subst. right. right. left. easy.
  - subst. right. right. right. left. easy.
Qed.

(* --- helper: a single beta_ln step yields componentwise convertibility in the closure --- *)
Lemma rst_step_natrec_inv :
  forall P z s n P' z' s' n',
    beta_ln (t_NatRec_ln P z s n) (t_NatRec_ln P' z' s' n') ->
    convertible_ln P P' /\ convertible_ln z z' /\ convertible_ln s s' /\ convertible_ln n n'
    \/
    (exists u : term_ln, beta_head_ln (t_NatRec_ln P z s n) u /\ convertible_ln u (t_NatRec_ln P' z' s' n')).
Proof.
  intros P z s n P' z' s' n' H.
  destruct (beta_natrec_cases_full _ _ _ _ _ _ _ _ H).
  - left. split. constructor. easy.
    destruct H0 as (Ha,(Hb,(Hc,Hd))). subst.
    split. apply convertible_refl.
    split. apply convertible_refl.
    apply convertible_refl.
  - destruct H0.
    destruct H0 as (Ha,(Hb,(Hc,Hd))). subst.
    left. split. apply convertible_refl.
    split. constructor. easy.
    split. apply convertible_refl.
    apply convertible_refl.
    
    destruct H0.
    destruct H0 as (Ha,(Hb,(Hc,Hd))). subst.
    left. split. apply convertible_refl.
    split. apply convertible_refl.
    split. constructor. easy.
    apply convertible_refl.

    destruct H0.
    destruct H0 as (Ha,(Hb,(Hc,Hd))). subst.
    left. split. apply convertible_refl.
    split. apply convertible_refl.
    split. apply convertible_refl.
    constructor. easy.
    
    right.
    destruct H0 as (u,(Ha,Hb)). subst.
    exists(t_NatRec_ln P' z' s' n'). split. easy.
    apply convertible_refl.
Qed.

Lemma app_preserves_open :
  forall n body P
    (Hbody: lc_rec_ln 1 body) (Hn: lc_rec_ln 0 n),
    convertible_ln P (t_Lam t_Nat body) ->
    convertible_ln (t_App P (t_Succ n)) (open_rec_ln 0 (t_Succ n) body).
Proof. intros.
       assert(t_App P (t_Succ n) ≡ₗₙ t_App (t_Lam t_Nat body) (t_Succ n)).
       { induction H.
         - constructor. apply beta_app1_ln. easy.
         - apply convertible_refl.
         - apply convertible_sym. easy.
         - apply convertible_trans with (y :=t_App y (t_Succ n)); easy.
       }
       assert(beta_ln (t_App (t_Lam t_Nat body) (t_Succ n))  (open_rec_ln 0 (t_Succ n) body)).
       { constructor. constructor. simpl. easy. easy. simpl. easy. }
       assert( t_App (t_Lam t_Nat body) (t_Succ n) ≡ₗₙ open_rec_ln 0 (t_Succ n) body).
       { constructor. easy. }
       apply convertible_trans with (y := t_App (t_Lam t_Nat body) (t_Succ n)); easy.
Qed.

Lemma context_id: forall Γ y v,
  ~ In y (map fst Γ) ->
  ~ In y (fv_ctx Γ) ->
  subst_ctx y v Γ = Γ.
Proof. intro G.
       induction G; intros.
       - simpl. easy.
       - simpl. destruct a.
         rewrite IHG.
         simpl in H0.
         assert(~In y (fv_ln t)).
         { unfold not. intros.
           apply H0. right.
           rewrite in_app_iff. left. easy.
         }
         rewrite subst_ln_notin_fv. easy.
         easy.
         unfold not. intros.
         apply H.
         simpl. right. easy.
         unfold not. intros.
         apply H0. simpl. right.
         rewrite in_app_iff. right. easy.
Qed.

(* instantiate a cofinite hypothesis *)
Lemma instantiate_one_binder :
  forall Γ A A0 b B v L (Heq: convertible_ln A A0) i (Hunv: has_type_ln Γ A (t_Type i)),
    NoDup (map fst Γ) ->
    (* cofinite premise: for fresh x, open b at x has type open B at x *)
    (forall x, ~ In x L -> ~ In x (map fst Γ) ->
       has_type_ln ((x,A0)::Γ) (open_ln b (t_fvar x)) (open_ln B (t_fvar x))) ->
    lc_ln v ->
    has_type_ln Γ v A0 ->
    (* conclusion: opening b with v has type opening B with v *)
    has_type_ln Γ (open_ln b v) (open_ln B v).
Proof. intros.
       specialize(exists_fresh_not_in_list (L++(map fst Γ)++(fv_ln b)++(fv_ln B)++fv_ctx Γ) ""); intros.
       destruct H3 as (y,(Hy,_)).
       assert(~ In y L).
       { unfold not. intros.
         apply Hy. rewrite in_app_iff. left. easy. 
       }
       assert(~ In y (map fst Γ)).
       { unfold not. intros.
         apply Hy. rewrite in_app_iff. right.
         rewrite in_app_iff. left. easy.
       } 
       specialize(H0 y H3 H4).
       specialize(substitution_head Γ y A (open_ln b (t_fvar y)) (open_ln B (t_fvar y)) v); intros HH.
       
       unfold open_ln in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       cbn in HH.
       rewrite String.eqb_refl in HH.
       rewrite subst_ln_notin_fv in HH.
       rewrite subst_ln_notin_fv in HH.
       assert((subst_ctx y v Γ) = Γ).
       { rewrite context_id. easy. easy.
         unfold not. intros.
         apply Hy.
         rewrite in_app_iff. right.
         rewrite in_app_iff. right.
         rewrite in_app_iff. right.
         rewrite in_app_iff. right.
         easy.
       }
       rewrite H5 in HH.
       apply HH; try easy.
       apply ty_conv with (A := A0). easy.
       apply convertible_sym. easy.
       specialize(context_conversion_general []); intros.
       simpl in H6.
       apply H6 with (A := A0) (i := i); try easy.
       apply convertible_sym. easy.
       unfold not. intros.
       apply Hy.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right.
       rewrite in_app_iff. left.
       easy.
       unfold not. intros.
       apply Hy.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right.
       rewrite in_app_iff. left.
       easy.
       easy. 
       easy.
Qed.

(* instantiate a cofinite hypothesis *)
Lemma instantiate_one_binder_fine :
  forall Γ A b B v L i (Hunv: has_type_ln Γ A (t_Type i)),
    NoDup (map fst Γ) ->
    (* cofinite premise: for fresh x, open b at x has type open B at x *)
    (forall x, ~ In x L -> ~ In x (map fst Γ) ->
       has_type_ln ((x,A)::Γ) (open_rec_ln 0 (t_fvar x) b) (open_rec_ln 0 (t_fvar x) B)) ->
    lc_ln v ->
    has_type_ln Γ v A ->
    (* conclusion: opening b with v has type opening B with v *)
    has_type_ln Γ (open_rec_ln 0 v b) (open_rec_ln 0 v B).
Proof. intros.
       apply instantiate_one_binder with (A0 := A) (A := A) (L := L) (i := i); try easy.
       apply convertible_refl.
Qed.

Lemma open_open_comm: forall b u n k,
  lc_rec_ln (S k) b ->
  lc_rec_ln k n ->
  open_rec_ln k u (open_rec_ln k n b) = open_rec_ln k n b.
Proof. intro b.
       induction b; intros.
       - simpl. simpl in H.
         case_eq(n =? k); intros.
         + rewrite open_rec_ln_noop_on_lc. easy. easy.
         + cbn. rewrite H1. easy.
       - simpl. easy.
       - simpl. easy.
       - simpl.
         rewrite IHb1, IHb2. easy.
         simpl in H. easy.
         apply cl_larger with (k := k). lia. easy.
         simpl in H. easy.
         easy.
       - simpl.
         rewrite IHb1, IHb2. easy.
         simpl in H. easy.
         apply cl_larger with (k := k). lia. easy.
         simpl in H. easy.
         easy.
       - simpl.
         rewrite IHb1, IHb2. easy.
         simpl in H. easy.
         apply cl_larger with (k := k). lia. easy.
         simpl in H. easy.
         easy.
       - simpl. easy.
       - simpl. easy.
       - simpl. rewrite IHb. easy.
         simpl in H. easy. easy.
       - cbn. rewrite IHb1, IHb2, IHb3, IHb4. easy.
         simpl in H. easy.
         easy.
         simpl in H. easy.
         easy.
         simpl in H. easy.
         easy.
         simpl in H. easy.
         easy.
Qed.

Lemma instantiate_two_binders_strong :
  forall Γ body sbody L v1 v2,
    NoDup (map fst Γ) ->
    (* cofinite hypothesis: for any distinct fresh names x,y ... *)
    (forall x y, x <> y ->
        ~ In x L -> ~ In y L ->
        (~ In x (map fst Γ) -> ~ In y (map fst Γ) ->
           has_type_ln ((y, open_rec_ln 0 (t_fvar x) body) :: (x, t_Nat) :: Γ)
                       (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody))
                       (open_rec_ln 0 (t_Succ (t_fvar x)) body))) ->

    (* arguments to instantiate with *)
    lc_ln v1 -> lc_ln v2 ->
    has_type_ln Γ v1 t_Nat ->
    has_type_ln Γ v2 (open_rec_ln 0 v1 body) ->

    (* conclusion: the double-opened sbody types as expected *)
    has_type_ln Γ (open_rec_ln 0 v2 (open_rec_ln 1 v1 sbody))
                  (open_rec_ln 0 (t_Succ v1) body).
Proof. intros.
       specialize(exists_fresh_not_in_list (L++(map fst Γ)++(fv_ln sbody)++(fv_ln body)++(fv_ln v1)++(fv_ln v2)++fv_ctx Γ) ""); intros.
       destruct H5 as (y,(Hy,_)).
       specialize(exists_fresh_not_in_list (y::L++(map fst Γ)++(fv_ln sbody)++(fv_ln body)++(fv_ln v1)++(fv_ln v2)++fv_ctx Γ) ""); intros.
       destruct H5 as (x,(Hx,_)).

       specialize(substitution_head 
       Γ x t_Nat
       (open_rec_ln 0 v2 (subst_ln x v1 (open_rec_ln 1 (t_fvar x) sbody)))  
       (subst_ln x v1 (open_rec_ln 0 (t_Succ (t_fvar x)) body))
       v1
       ); intro HH2.
       assert(~ In x (map fst Γ)).
       { unfold not. intros. apply Hx. simpl.
         right. rewrite in_app_iff. right.
         rewrite in_app_iff. left. easy.
       }
       specialize(HH2 H H5 H1 H3).
       cbn in HH2.
       unfold open_ln in HH2.
       rewrite  open_subst_commute in HH2.
       rewrite  open_subst_commute in HH2.
       rewrite  open_subst_commute in HH2.
       rewrite  open_subst_commute in HH2.
       rewrite  open_subst_commute in HH2.
       cbn in HH2.
       rewrite String.eqb_refl in HH2.
       setoid_rewrite subst_ln_notin_fv in HH2 at 9.
       setoid_rewrite subst_ln_notin_fv in HH2 at 8.
       setoid_rewrite subst_ln_notin_fv in HH2 at 7.
       setoid_rewrite subst_ln_notin_fv in HH2 at 6.
       setoid_rewrite subst_ln_notin_fv in HH2 at 5.
       setoid_rewrite subst_ln_notin_fv in HH2 at 4.  
       setoid_rewrite subst_ln_notin_fv in HH2 at 3.
       setoid_rewrite subst_ln_notin_fv in HH2 at 2.
       setoid_rewrite subst_ln_notin_fv in HH2 at 1.
       rewrite context_id in HH2.
       apply HH2.
       
       specialize(substitution_head 
       ((x, t_Nat) :: Γ) y (subst_ln x v1 (open_rec_ln 0 (t_fvar x) body) ) 
       (subst_ln x v1 (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody)))
       (subst_ln x v1 (open_rec_ln 0 (t_Succ (t_fvar x)) body))
       v2
       ); intro HH.
       assert(NoDup (map fst ((x, t_Nat) :: Γ))).
       { simpl. constructor. easy. easy. }
       assert(~ In y (map fst ((x, t_Nat) :: Γ))).
       { unfold not. intros.
         simpl in H7. destruct H7.
         subst. apply Hx. simpl. left. easy.
         apply Hy.
         rewrite in_app_iff. right.
         rewrite in_app_iff. left. easy.
       }
       specialize(HH H6 H7 H2).
       cbn in HH.
       unfold open_ln in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       rewrite  open_subst_commute in HH.
       cbn in HH.
       rewrite String.eqb_refl in HH.
(*        rewrite String.eqb_refl in HH. *)
       assert(y <> x).
       { unfold not. intros. subst.
         apply H7. simpl. left. easy.
       }
       apply String.eqb_neq in H8.
       assert ((x =? y)%string = false).
       { rewrite String.eqb_sym. easy. }
       rewrite H9 in HH. cbn in HH.
       rewrite String.eqb_refl in HH.
(*        rewrite String.eqb_refl in HH.
       cbn in HH. *)
       setoid_rewrite subst_ln_notin_fv in HH at 10.
       setoid_rewrite subst_ln_notin_fv in HH at 9.
       setoid_rewrite subst_ln_notin_fv in HH at 8.
       setoid_rewrite subst_ln_notin_fv in HH at 7.
       setoid_rewrite subst_ln_notin_fv in HH at 6.
       setoid_rewrite subst_ln_notin_fv in HH at 5.
       setoid_rewrite subst_ln_notin_fv in HH at 4.
       setoid_rewrite subst_ln_notin_fv in HH at 3.
       setoid_rewrite subst_ln_notin_fv in HH at 2.
       setoid_rewrite subst_ln_notin_fv in HH at 1.
       rewrite context_id in HH.
       apply HH.
       apply weakening_fresh. easy. easy.
       assert(has_type_ln ((y, open_rec_ln 0 (t_fvar x) body) :: (x, t_Nat) :: Γ)
              (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody)) (open_rec_ln 0 (t_Succ (t_fvar x)) body)).
       { apply H0. 
         apply String.eqb_neq. easy.
         unfold not. intros.
         apply Hx. simpl. right. rewrite in_app_iff. left. easy.
         unfold not. intros.
         apply Hy. rewrite in_app_iff. left. easy.
         unfold not. intros.
         apply Hx. simpl. right. rewrite in_app_iff. right. rewrite in_app_iff. left. easy.
         unfold not. intros.
         apply Hy. rewrite in_app_iff. right. rewrite in_app_iff. left. easy.
       }
       assert(NoDup (map fst ([(y, open_rec_ln 0 (t_fvar x) body)] ++ Γ))).
       { simpl. constructor. 
         unfold not. intros.
         apply Hy. rewrite in_app_iff. right. rewrite in_app_iff. left. easy. easy.
       }
       assert(~ In x (map fst ([(y, open_rec_ln 0 (t_fvar x) body)] ++ Γ))).
       { simpl. unfold not. intros.
         destruct H12. subst. apply H7. left. easy.
         unfold not. intros.
         apply Hx. simpl. right. rewrite in_app_iff. right. rewrite in_app_iff. left. easy.
       }
       specialize(substitution_general [(y, open_rec_ln 0 (t_fvar x) body)]
       Γ x t_Nat
       (open_rec_ln 0 (t_fvar y) (open_rec_ln 1 (t_fvar x) sbody))
       (open_rec_ln 0 (t_Succ (t_fvar x)) body)
       v1
       H11 H12
       ); intro HH3.
       simpl in HH3.
       specialize(HH3 H10 H3 H1).
       rewrite  open_subst_commute in HH3.
       rewrite  open_subst_commute in HH3.
       rewrite  open_subst_commute in HH3.
       rewrite  open_subst_commute in HH3.
       cbn in HH3.
       rewrite H9 in HH3.
       rewrite String.eqb_refl in HH3.
       setoid_rewrite subst_ln_notin_fv in HH3 at 3.
       setoid_rewrite subst_ln_notin_fv in HH3 at 2.
       setoid_rewrite subst_ln_notin_fv in HH3 at 1.
       rewrite context_id in HH3.
       specialize(fresh_commute_middle []); intro Ha.
       simpl in Ha.
       apply Ha.
       unfold not. intros.
       subst.
       rewrite String.eqb_refl in H8. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros.
       apply Hy. rewrite in_app_iff. right. rewrite in_app_iff. left. easy.
       apply weakening_fresh.
       simpl.
       unfold not. intros.
       destruct H13. subst.
       apply H7. simpl. left. easy.
       unfold not. intros.
       apply Hx. simpl. right. rewrite in_app_iff. right. rewrite in_app_iff. left. easy.
       apply HH3.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       easy.
       apply cl_larger with (k := 0). lia. easy.
       easy. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hy. simpl.
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       easy.
       apply cl_larger with (k := 0). lia. easy. easy. easy.
       apply cl_larger with (k := 0). lia. easy. easy. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       unfold not. intros. apply Hx. simpl.
       right. rewrite in_app_iff. right.
       rewrite in_app_iff. right. 
       rewrite in_app_iff. right.
       rewrite in_app_iff. left. easy.
       easy.
       apply cl_larger with (k := 0). lia. easy. easy. easy.
       apply cl_larger with (k := 0). lia. easy.
Qed.

Lemma beta_preserve_pi :
  forall A B t',
    beta_ln (t_Pi A B) t' ->
    exists A' B', t' = t_Pi A' B' /\ ((beta_ln A A' /\ B = B') \/ beta_ln B B' /\ A = A').
Proof.
  intros A B t' H.
  remember (t_Pi A B) as t0 eqn:Heqt0.
  revert A B Heqt0.
  induction H; intros.
  - subst.
    inversion H.
  - inversion Heqt0. subst.
    exists A', B0.
    split. easy. left. split. easy. easy.
(*     apply convertible_refl. *)
  - inversion Heqt0. subst.
    exists A0, B'.
    split. easy. right. split. easy. easy. 
(*     apply convertible_refl. *)
(*     constructor. easy. *)
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
Qed.

Lemma beta_preserve_pi2 :
  forall A B t',
    beta_ln (t_Pi A B) t' ->
    exists A' B', t' = t_Pi A' B' /\ convertible_ln A A' /\ convertible_ln B B'.
Proof.
  intros A B t' H.
  remember (t_Pi A B) as t0 eqn:Heqt0.
  revert A B Heqt0.
  induction H; intros.
  - subst.
    inversion H.
  - inversion Heqt0. subst.
    exists A', B0.
    split. easy. split. constructor. easy. 
    apply convertible_refl.
  - inversion Heqt0. subst.
    exists A0, B'.
    split. easy. split.
    apply convertible_refl.
    constructor. easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
  - easy.
Qed.

Lemma beta_convertible_pi :
  forall t A B,
    convertible_ln (t_Pi A B) t ->
    (exists X Y, convertible_ln A X /\ convertible_ln B Y /\ convertible_ln (t_Pi X Y) t).
Proof. intros.
       remember (t_Pi A B) as x.
       revert A B Heqx.
       induction H; intros.
       - subst. 
         exists A, B. 
         split. apply convertible_refl.
         split. apply convertible_refl.
         constructor. easy.
       - subst. exists A, B.
         split. apply convertible_refl.
         split. apply convertible_refl.
         apply convertible_refl.
       - subst. exists A, B.
         split. apply convertible_refl.
         split. apply convertible_refl.
         apply convertible_sym. easy.
       - subst.
         specialize(IHclos_refl_sym_trans1 A B eq_refl).
         destruct IHclos_refl_sym_trans1 as (X,(Y,(Ha,(Hb,Hc)))).
         exists X, Y.
         split. easy. split. easy.
         apply convertible_trans with (y := y); easy.
Qed.


Lemma conv_induct :
  forall (P : term_ln -> term_ln -> Prop),
    (forall t, P t t) ->
    (forall t1 t2, beta_ln t1 t2 -> P t1 t2) ->
    (forall t1 t2, P t1 t2 -> P t2 t1) ->
    (forall t1 t2 t3, P t1 t2 -> P t2 t3 -> P t1 t3) ->
    forall x y, clos_refl_sym_trans term_ln beta_ln x y -> P x y.
Proof.
  intros P Hrefl Hstep Hsym Htrans x y Hxy.
  remember x as x0 eqn:Heqx.
  remember y as y0 eqn:Heqy.
  revert x y Heqx Heqy.
  induction Hxy; intros.
  - subst. apply Hstep. easy.
  - (* sym *)
    apply Hsym. subst. apply Hrefl.
  - subst.
    apply Hsym.
    eapply IHHxy; eauto.
  - subst.
     (* trans *)
    eapply Htrans with (t2 := y).
    eapply IHHxy1; eauto.
    eapply IHHxy2; eauto.
Qed.

Lemma clos_rst_ind_or :
  forall (P : term_ln -> term_ln -> Prop),
    (* reflexive case: easy *)
    (forall t, P t t) ->

    (* one-step case *)
    (forall t1 t2, beta_ln t1 t2 -> P t1 t2) ->

    (* symmetry case *)
    (forall t1 t2, P t1 t2 -> P t2 t1) ->

    (* transitivity case MUST ALLOW THE OR BRANCH: *)
    (forall t1 t2 t3,
        P t1 t2 ->
        P t2 t3 ->
        (P t1 t3 \/ 
          exists u,
          clos_refl_sym_trans term_ln P t1 u /\
          clos_refl_sym_trans term_ln P u t3 /\
          P t1 t3)) ->

    forall x y,
      clos_refl_sym_trans term_ln beta_ln x y ->
      P x y.
Proof.
  intros P Hrefl Hstep Hsym Htrans x y Hxy.
  remember x as x0 eqn:Heqx.
  remember y as y0 eqn:Heqy.
  revert x y Heqx Heqy.
  induction Hxy; intros.
  - subst. apply Hstep. easy.
  - (* sym *)
    apply Hsym. subst. apply Hrefl.
  - subst.
    apply Hsym.
    eapply IHHxy; eauto.
  - subst.
    specialize(IHHxy1 x0 y eq_refl eq_refl).
    specialize(IHHxy2 y y0 eq_refl eq_refl).
    specialize(Htrans _ _ _ IHHxy1 IHHxy2).
    destruct Htrans. easy.
    destruct H as (u, (Ha,(Hb,Hc))).
    specialize(rst_trans _ _ _ _ _ Ha Hb); intros.
    easy.
Qed.

Lemma beta_open_compat :
  forall t t' k u
    (Hu: lc_rec_ln 0 u),
    beta_ln t t' ->
    beta_ln (open_rec_ln k u t) (open_rec_ln k u t').
Proof.
  intros t.
  induction t; intros.
  6: { cbn.
       inversion H.
       - subst. inversion H0.
         subst. unfold open_ln.
         setoid_rewrite open_rec_ln_noop_on_lc at 3.
         setoid_rewrite open_rec_ln_noop_on_lc at 2.
         setoid_rewrite open_rec_ln_noop_on_lc at 1.
         constructor. constructor. easy. easy. easy.
         simpl. split.
         destruct k. easy. apply cl_larger with (k := 0). lia. easy.
         destruct k. easy. apply cl_larger with (k := 1). lia. easy.
         destruct k. easy. apply cl_larger with (k := 0). lia. easy.
         apply lc_rec_open_rec0; easy.
       - subst. cbn.
         apply beta_app1_ln.
         apply IHt1. easy. easy.
       - subst. cbn.
         apply beta_app2_ln.
         apply IHt2. easy. easy.
     }
  1: { inversion H. subst. inversion H0. }
  1: { inversion H. subst. inversion H0. }
  1: { inversion H. subst. inversion H0. }
  1: { inversion H.
       - subst. inversion H0.
       - subst. cbn. apply beta_pi_A_ln.
        apply IHt1. easy. easy.
       - subst. cbn. apply beta_pi_B_ln.
         apply IHt2. easy. easy.
     }
  1: { inversion H.
       - subst. inversion H0.
       - subst. cbn. apply beta_lam_A_ln.
        apply IHt1. easy. easy.
       - subst. cbn. apply beta_lam_b_ln.
         apply IHt2. easy. easy.
     }
  1: { inversion H. subst. inversion H0. }
  1: { inversion H. subst. inversion H0. }
  1: { inversion H. subst. inversion H0. subst.
       apply beta_succ_ln. fold  open_rec_ln.
       apply IHt. easy. easy.
     }
  1: { inversion H.
       - subst. inversion H0.
         + subst.
           constructor.
           cbn. 
           setoid_rewrite open_rec_ln_noop_on_lc at 1.
           setoid_rewrite open_rec_ln_noop_on_lc at 2.
           setoid_rewrite open_rec_ln_noop_on_lc at 3.
           eapply b_natrec_zero_ln_strict. easy. easy.
           fold open_rec_ln. 
           apply closedness_preserved. lia. easy.
           destruct k. easy. apply cl_larger with (k := 2). lia. easy.
           apply lc_rec_open_rec11. easy. simpl. lia.
           assert(lc_rec_ln 2 Pbody).
           apply cl_larger with (k := 1). lia. easy.
           destruct k. easy. apply cl_larger with (k := 2). lia. easy.
         + subst. cbn.
           setoid_rewrite open_rec_ln_noop_on_lc at 7.
           setoid_rewrite open_rec_ln_noop_on_lc at 6.
           setoid_rewrite open_rec_ln_noop_on_lc at 5.
(*            setoid_rewrite open_rec_ln_noop_on_lc at 4. *)
           setoid_rewrite open_rec_ln_noop_on_lc at 3.
           setoid_rewrite open_rec_ln_noop_on_lc at 2.
           setoid_rewrite open_rec_ln_noop_on_lc at 1.
           constructor.
           cbn.

           eapply b_natrec_succ_ln_strict; easy.
           destruct k. easy. apply cl_larger with (k := 1). lia. easy.
           destruct k. easy. apply cl_larger with (k := 0). lia. easy.
           apply lc_rec_open_rec11. easy. simpl. lia.
           destruct k. easy. apply cl_larger with (k := 2). lia. easy.
           destruct k. easy. apply cl_larger with (k := 0). lia. easy.
           apply lc_rec_open_rec1.
           easy. easy.
           unfold open_ln.
           simpl.
           split. easy. split. easy. split. split. easy.
           split.
           apply lc_rec_open_rec11. easy. simpl. lia.
           easy. easy.
       - subst. cbn.
         apply beta_natrec_P_ln.
         apply IHt1. easy. easy.
       - subst. cbn.
         apply beta_natrec_z_ln.
         apply IHt2. easy. easy.
       - subst. cbn.
         apply beta_natrec_s_ln.
         apply IHt3. easy. easy.
       - subst. cbn.
         apply beta_natrec_n_ln.
         apply IHt4. easy. easy.
     }
Qed.

Lemma convertible_open_compat :
  forall t t' k u (Hu: lc_rec_ln 0 u),
    convertible_ln t t' ->
    convertible_ln (open_rec_ln k u t) (open_rec_ln k u t').
Proof.
  intros t t' k u Hu Hconv.
  induction Hconv.
  - constructor. apply beta_open_compat; easy.
      (* rst_refl *)
  -  apply rst_refl.
  - (* rst_sym *)
    apply rst_sym.
    assumption.
  - (* rst_trans *)
    eapply rst_trans; eauto.
Qed.

Theorem preservation :
  forall Γ t t' T (ND: NoDup (map fst Γ)),
    has_type_ln Γ t T ->
    step_ln t t' ->
    has_type_ln Γ t' T.
Proof. intros.
       revert H. revert Γ T ND.
       induction H0; intros.
       11:{
       specialize(natrec_inversion_weaker Γ P z n s T H); intro HH.
       destruct HH as (k,(L,(body,(sbody,(Ha,(Hb,(Hc,(Hd,(He,(Hf,(Hg,(Hi,Hj)))))))))))).
       apply ty_conv with (A :=  open_rec_ln 0 n body); try easy.
       apply step_implies_convertible_ln in H0.
       specialize(open_rec_ln_monotone_u body 0 n n' H0); intro HH.
       apply ty_conv with (A :=  open_rec_ln 0 n' body); try easy.
       subst.
       apply ty_NatRec_strong with (k := k) (L := L); try easy.
       apply IHstep_ln. easy. easy.
       apply convertible_sym. easy.
       apply convertible_sym. easy.
       }
       10:{
       cbn in *.
       specialize(natrec_inversion_weaker Γ P z n s T H); intro HH.
       destruct HH as (k,(L,(body,(sbody,(Ha,(Hb,(Hc,(Hd,(He,(Hf,(Hg,(Hi,Hj)))))))))))).
       apply ty_conv with (A := open_rec_ln 0 n body); try easy.
       subst.
       inversion H0. subst.
       inversion H4.
       apply convertible_sym. easy.
       }
       9:{
       specialize(natrec_inversion_weaker Γ P z n s T H); intro HH.
       destruct HH as (k,(L,(body,(sbody,(Ha,(Hb,(Hc,(Hd,(He,(Hf,(Hg,(Hi,Hj)))))))))))).
       apply ty_conv with (A := open_rec_ln 0 n body); try easy.
       subst.
       apply ty_NatRec_strong with (k := k) (L := L); try easy.
       simpl.
       apply IHstep_ln. easy. easy.
       apply convertible_sym. easy.
       }
       8:{
       specialize(natrec_inversion_weaker Γ P z n s T H); intro HH.
       destruct HH as (k,(L,(body,(sbody,(Ha,(Hb,(Hc,(Hd,(He,(Hf,(Hg,(Hi,Hj)))))))))))).
       apply ty_conv with (A :=  open_rec_ln 0 n body); try easy.
       subst.
       inversion H0. subst. inversion H4.
       apply convertible_sym. easy.
       }
       7:{
       specialize(natrec_inversion_stronger Γ Pbody z (t_Succ n) sbody T H3); intro HH.
       destruct HH as (k,(L,(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg)))))))).
       apply ty_conv with (A := open_rec_ln 0 (t_Succ n) Pbody); try easy.
       cbn.
       unfold open_ln.
       pose proof Hb as Hb1.
       apply lam_inversion in Hd.
       apply instantiate_two_binders_strong with (L := L).
       easy.
       intros. apply He; easy.
       easy.
       unfold lc_ln. simpl.
       split. split. easy. easy.
       split. easy. split. split. easy.
       split.
       apply lc_rec_open_rec11. easy. simpl. lia. easy. easy.
       apply succ_inversion in Hf. easy.
       apply ty_NatRec_strong with (k := k) (L := L); try easy.
       destruct Hd as (i,(B,(LL,(Hd1,(Hd2,Hd3))))).
       apply ty_Lam with (i := 0) (L := L++LL).
       apply ty_Nat.
       intros.
       unfold open_ln.
       unfold open_ln in Hd2.
       assert(HC: lc_rec_ln 0 (t_fvar x)).
       { simpl. easy. }
       assert((t_Pi (open_rec_ln 0 (t_bvar 0) Pbody) (open_rec_ln 0 (t_Succ (t_bvar 1)) Pbody)) ≡ₗₙ B) by admit.
       specialize(convertible_open_compat
       (t_Pi (open_rec_ln 0 (t_bvar 0) Pbody) (open_rec_ln 0 (t_Succ (t_bvar 1)) Pbody))
       B 0 (t_fvar x) HC H6
       ); intro HH.
       
       apply ty_conv with (A := open_rec_ln 0 (t_fvar x) B).
       apply Hd2.
       unfold not. intros.
       apply H4. rewrite in_app_iff. right. easy.
       easy.
       apply convertible_sym. easy.
       apply succ_inversion in Hf. easy.
       apply convertible_sym. easy.
       }
       6:{
       specialize(natrec_inversion_stronger Γ Pbody z t_Zero sbody T H2); intro HH.
       destruct HH as (k,(L,(Ha,(Hb,(Hc,(Hd,(He,(Hf,Hg)))))))).
       apply ty_conv with (A := open_rec_ln 0 t_Zero Pbody); try easy.
       apply convertible_sym. easy.
       }
       5:{
       apply succ_inversion in H.
       destruct H as (Ha,Hb).
       apply IHstep_ln in Ha.
       eapply ty_conv with (A := t_Nat).
       apply ty_Succ. easy.
       apply convertible_sym. easy. easy.
       }
       4:{ 
       apply lam_inversion in H.
       destruct H as (i,(B,(L,(Ha,(Hb,Hc))))).
       apply IHstep_ln in Ha.
       apply step_implies_convertible_ln in H0.
       eapply ty_conv with (A := t_Pi A' B).
       apply ty_Lam with (i := i) (L := L). easy.
       intros.
       specialize(Hb x H H1).
       specialize(context_conversion_general []); intro HH.
       simpl in HH.
       apply HH with (A := A) (i := i); easy.
       apply convertible_tPi_t1 with (t2 := B) in H0.
       apply convertible_sym in H0, Hc.
       apply convertible_trans with (y := t_Pi A B); easy.
       easy.
       }
       3:{
       apply app_inversion in H1.
       destruct H1 as (A,(B,(Ha,(Hb,Hc)))).
       apply ty_conv with (A := open_ln B t2').
       apply ty_App with (A := A). easy.
       apply IHstep_ln. easy. easy.
       apply step_implies_convertible_ln in H0.
       apply open_rec_ln_monotone_u with (b := B) (k := 0) in H0.
       apply convertible_sym in H0, Hc.
       apply convertible_trans with (y := open_rec_ln 0 t2 B); easy.
       }
       2:{
       apply app_inversion in H.
       destruct H as (A,(B,(Ha,(Hb,Hc)))).
       apply ty_conv with (A := open_ln B t2).
       apply ty_App with (A := A).
       apply IHstep_ln. easy.
       easy. easy.
       apply convertible_sym. easy.
       }
       1:{
       apply app_inversion in H2.
       destruct H2 as (A0,(B,(Ha,(Hb,Hc)))).
       apply  lam_inversion in Ha.
       destruct Ha as (i,(B0,(L,(Ha,(Hd,He))))).
       rename s into v.
       apply ty_conv with (A := open_ln B v).
       unfold open_ln. cbn.

       apply instantiate_one_binder_fine with (A := A) (L := L) (i := i); try easy.

       intros.
       apply ty_conv with (A := (open_ln B0 (t_fvar x))).
       apply Hd; easy.
       unfold open_ln.
       apply convertible_open_compat. simpl. easy.
       admit. (**)
       admit.
       apply convertible_sym. easy.
       }
Admitted.





