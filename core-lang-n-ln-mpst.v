From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Strings.String Ascii.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators Lia.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Strings.String.
Require Import Coq.Structures.OrderedTypeEx.

(* Endpoint = (session id, role) *)
Module EndpointOT :=
  PairOrderedType(String_as_OT)(String_as_OT).

Module LM := FMapAVL.Make(EndpointOT).

Definition endpoint := EndpointOT.t.

Inductive term_ln : Type :=
  (* ---------------- Core Dependent Calculus ---------------- *)
  | t_bvar      : nat -> term_ln
  | t_fvar      : string -> term_ln

  | t_Type      : nat -> term_ln
  | t_Pi        : term_ln -> term_ln -> term_ln
  | t_Lam       : term_ln -> term_ln -> term_ln
  | t_App       : term_ln -> term_ln -> term_ln

  | t_Nat       : term_ln
  | t_Zero      : term_ln
  | t_Succ      : term_ln -> term_ln

  | t_NatRec_ln :
      term_ln (* motive P *)
      -> term_ln (* base case z *)
      -> term_ln (* step function s *)
      -> term_ln (* scrutinee n *)
      -> term_ln

  (* ---------------- Session Types ---------------- *)

  | t_Session   : term_ln
  | t_End       : term_ln

  | t_SendTy    :
      string      (* peer role *)
      -> term_ln  (* payload *)
      -> term_ln  (* continuation *)
      -> term_ln

  | t_RecvTy    :
      string
      -> term_ln
      -> term_ln
      -> term_ln

  (* ---------------- Session Operations ---------------- *)

  | t_chan :
      endpoint -> term_ln
  (* linear session endpoint *)
  | t_SendV :
      string      (* peer role *)
      -> term_ln  (* channel *)
      -> term_ln  (* value *)
      -> term_ln  (* continuation *)
      -> term_ln

  | t_Recv :
      string      (* expected peer role *)
      -> term_ln  (* channel *)
      -> term_ln  (* body *)
      -> term_ln

  | t_Close     : term_ln -> term_ln
  | t_Wait      : term_ln -> term_ln
  (* ---------------- Parallelism ---------------- *)
  | t_Fork      : term_ln -> term_ln
  | t_Par       : term_ln -> term_ln -> term_ln

  | t_SelectTy :
      string (* peer *)
      -> list (string * term_ln)
      -> term_ln

  | t_BranchTy :
      string
      -> list (string * term_ln)
      -> term_ln

  | t_Select :
      string      (* peer *)
      -> string   (* label *)
      -> term_ln  (* channel *)
      -> term_ln  (* continuation *)
      -> term_ln

  | t_Branch :
      string      (* peer *)
      -> term_ln  (* channel *)
      -> list (string * term_ln)  (* branches *)
      -> term_ln
.

(*   | t_Data      : term_ln
  | t_Payload   : term_ln. *)


Fixpoint open_rec_ln (k : nat) (u : term_ln) (t : term_ln) : term_ln :=
  match t with

  (* ---------- core ---------- *)

  | t_bvar n =>
      if Nat.eqb n k then u else t_bvar n

  | t_fvar x =>
      t_fvar x

  | t_Type i =>
      t_Type i

  | t_Pi A B =>
      t_Pi (open_rec_ln k u A)
           (open_rec_ln (S k) u B)

  | t_Lam A body =>
      t_Lam (open_rec_ln k u A)
            (open_rec_ln (S k) u body)

  | t_App f a =>
      t_App (open_rec_ln k u f)
            (open_rec_ln k u a)

  | t_Nat =>
      t_Nat

  | t_Zero =>
      t_Zero

  | t_Succ n =>
      t_Succ (open_rec_ln k u n)

  | t_NatRec_ln P z s n =>
      t_NatRec_ln (open_rec_ln k u P)
                  (open_rec_ln k u z)
                  (open_rec_ln k u s)
                  (open_rec_ln k u n)


  (* ---------- session types ---------- *)

  | t_Session =>
      t_Session

  | t_End =>
      t_End

  | t_SendTy r A Se =>
      t_SendTy r (open_rec_ln k u A)
                 (open_rec_ln k u Se)

  | t_RecvTy r A Se =>
      t_RecvTy r
        (open_rec_ln k u A)
        (open_rec_ln (S k) u Se)

  (* ---------- session operations ---------- *)

  | t_chan e =>
      t_chan e

  | t_SendV r c v P =>
      t_SendV r (open_rec_ln k u c)
                (open_rec_ln k u v)
                (open_rec_ln k u P)

  (* 🔴 Binding receive *)
  | t_Recv r c body =>
      t_Recv r (open_rec_ln k u c)
               (open_rec_ln (S k) u body)

  | t_Close c =>
      t_Close (open_rec_ln k u c)

  | t_Wait c =>
      t_Wait (open_rec_ln k u c)

  | t_Fork p =>
      t_Fork (open_rec_ln k u p)

  | t_Par p q =>
      t_Par (open_rec_ln k u p)
            (open_rec_ln k u q)

| t_SelectTy r branches =>
    t_SelectTy r
      (map (fun '(l,Se) =>
              (l, open_rec_ln k u Se))
           branches)

| t_BranchTy r branches =>
    t_BranchTy r
      (map (fun '(l,Se) =>
              (l, open_rec_ln k u Se))
           branches)

| t_Select r l c P =>
    t_Select r l
      (open_rec_ln k u c)
      (open_rec_ln k u P)

| t_Branch r c branches =>
    t_Branch r
      (open_rec_ln k u c)
      (map (fun '(l,b) =>
              (l, open_rec_ln k u b))
           branches)
(*   | t_Data    => t_Data
  | t_Payload => t_Payload *)
  end.


Definition open_ln (t u : term_ln) := open_rec_ln 0 u t.

Fixpoint close_rec_ln (k : nat) (x : string) (t : term_ln) : term_ln :=
  match t with

  (* ---------- core ---------- *)

  | t_bvar n =>
      t_bvar n

  | t_fvar y =>
      if String.eqb x y then t_bvar k else t_fvar y

  | t_Type i =>
      t_Type i

  | t_Pi A B =>
      t_Pi (close_rec_ln k x A)
           (close_rec_ln (S k) x B)

  | t_Lam A body =>
      t_Lam (close_rec_ln k x A)
            (close_rec_ln (S k) x body)

  | t_App f a =>
      t_App (close_rec_ln k x f)
            (close_rec_ln k x a)

  | t_Nat =>
      t_Nat

  | t_Zero =>
      t_Zero

  | t_Succ n =>
      t_Succ (close_rec_ln k x n)

  | t_NatRec_ln P z s n =>
      t_NatRec_ln (close_rec_ln k x P)
                  (close_rec_ln k x z)
                  (close_rec_ln k x s)
                  (close_rec_ln k x n)


  (* ---------- session types ---------- *)

  | t_Session =>
      t_Session

  | t_End =>
      t_End

  | t_SendTy r A Se =>
      t_SendTy r (close_rec_ln k x A)
                 (close_rec_ln k x Se)

  | t_RecvTy r A Se =>
      t_RecvTy r
        (close_rec_ln k x A)
        (close_rec_ln k x Se)


  (* ---------- session operations ---------- *)

  | t_chan e =>
      t_chan e

  | t_SendV r c v P =>
      t_SendV r (close_rec_ln k x c)
                (close_rec_ln k x v)
                (close_rec_ln k x P)

  (* 🔴 Binding receive *)
  | t_Recv r c body =>
      t_Recv r (close_rec_ln k x c)
               (close_rec_ln (S k) x body)

  | t_Close c =>
      t_Close (close_rec_ln k x c)

  | t_Wait c =>
      t_Wait (close_rec_ln k x c)

  | t_Fork p =>
      t_Fork (close_rec_ln k x p)

  | t_Par p q =>
      t_Par (close_rec_ln k x p)
            (close_rec_ln k x q)

| t_SelectTy r branches =>
    t_SelectTy r
      (map (fun '(l,Se) =>
              (l, close_rec_ln k x Se))
           branches)

| t_BranchTy r branches =>
    t_BranchTy r
      (map (fun '(l,Se) =>
              (l, close_rec_ln k x Se))
           branches)

| t_Select r l c P =>
    t_Select r l
      (close_rec_ln k x c)
      (close_rec_ln k x P)

| t_Branch r c branches =>
    t_Branch r
      (close_rec_ln k x c)
      (map (fun '(l,b) =>
              (l, close_rec_ln k x b))
           branches)

(*   | t_Data    => t_Data
  | t_Payload => t_Payload *)
  end.


Definition close_ln (x : string) (t : term_ln) := close_rec_ln 0 x t.


Fixpoint subst_ln (x : string) (u : term_ln) (t : term_ln) : term_ln :=
  match t with

  (* ---------- core ---------- *)

  | t_bvar n =>
      t_bvar n

  | t_fvar y =>
      if String.eqb x y then u else t_fvar y

  | t_Type i =>
      t_Type i

  | t_Pi A B =>
      t_Pi (subst_ln x u A)
           (subst_ln x u B)

  | t_Lam A body =>
      t_Lam (subst_ln x u A)
            (subst_ln x u body)

  | t_App f a =>
      t_App (subst_ln x u f)
            (subst_ln x u a)

  | t_Nat =>
      t_Nat

  | t_Zero =>
      t_Zero

  | t_Succ n =>
      t_Succ (subst_ln x u n)

  | t_NatRec_ln P z s n =>
      t_NatRec_ln (subst_ln x u P)
                  (subst_ln x u z)
                  (subst_ln x u s)
                  (subst_ln x u n)


  (* ---------- session types ---------- *)

  | t_Session =>
      t_Session

  | t_End =>
      t_End

  | t_SendTy r A Se =>
      t_SendTy r (subst_ln x u A)
                 (subst_ln x u Se)

  | t_RecvTy r A Se =>
      t_RecvTy r (subst_ln x u A)
                 (subst_ln x u Se)


  (* ---------- session operations ---------- *)

  | t_chan e =>
      t_chan e
  (* channels are not lambda variables *)

  | t_SendV r c v P =>
      t_SendV r (subst_ln x u c)
                (subst_ln x u v)
                (subst_ln x u P)

  (* 🔴 binding receive *)
  | t_Recv r c body =>
      t_Recv r (subst_ln x u c)
               (subst_ln x u body)

  | t_Close c =>
      t_Close (subst_ln x u c)

  | t_Wait c =>
      t_Wait (subst_ln x u c)

  | t_Fork p =>
      t_Fork (subst_ln x u p)

  | t_Par p q =>
      t_Par (subst_ln x u p)
            (subst_ln x u q)

| t_SelectTy r branches =>
    t_SelectTy r
      (map (fun '(l,Se) =>
              (l, subst_ln x u Se))
           branches)

| t_BranchTy r branches =>
    t_BranchTy r
      (map (fun '(l,Se) =>
              (l, subst_ln x u Se))
           branches)

| t_Select r l c P =>
    t_Select r l
      (subst_ln x u c)
      (subst_ln x u P)

| t_Branch r c branches =>
    t_Branch r
      (subst_ln x u c)
      (map (fun '(l,b) =>
              (l, subst_ln x u b))
           branches)
(*   | t_Data    => t_Data
  | t_Payload => t_Payload *)
  end.


Fixpoint lc_rec_ln (k : nat) (t : term_ln) {struct t} : Prop :=
  match t with

  (* ---------- core ---------- *)

  | t_bvar n =>
      n < k

  | t_fvar _ =>
      True

  | t_Type _ =>
      True

  | t_Pi A B =>
      lc_rec_ln k A /\
      lc_rec_ln (S k) B

  | t_Lam A body =>
      lc_rec_ln k A /\
      lc_rec_ln (S k) body

  | t_App f a =>
      lc_rec_ln k f /\
      lc_rec_ln k a

  | t_Nat =>
      True

  | t_Zero =>
      True

  | t_Succ n =>
      lc_rec_ln k n

  | t_NatRec_ln P z s n =>
      lc_rec_ln k P /\
      lc_rec_ln k z /\
      lc_rec_ln k s /\
      lc_rec_ln k n

  (* ---------- session types ---------- *)

  | t_Session =>
      True

  | t_End =>
      True

  | t_SendTy r A Se =>
      lc_rec_ln k A /\
      lc_rec_ln k Se

  | t_RecvTy r A Se =>
      lc_rec_ln k A /\
      lc_rec_ln (S k) Se

  (* ---------- session operations ---------- *)

  | t_chan _ =>
      True

  | t_SendV r c v P =>
      lc_rec_ln k c /\
      lc_rec_ln k v /\
      lc_rec_ln k P

  | t_Recv r c body =>
      lc_rec_ln k c /\
      lc_rec_ln (S k) body

  | t_Close c =>
      lc_rec_ln k c

  | t_Wait c =>
      lc_rec_ln k c

  | t_Fork p =>
      lc_rec_ln k p

  | t_Par p q =>
      lc_rec_ln k p /\
      lc_rec_ln k q

  (* ---------- branching ---------- *)

  | t_SelectTy r branches =>
      let fix lc_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              lc_rec_ln k b /\ lc_branches bs'
          end
      in lc_branches branches

  | t_BranchTy r branches =>
      let fix lc_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              lc_rec_ln k b /\ lc_branches bs'
          end
      in lc_branches branches

  | t_Select r l c P =>
      lc_rec_ln k c /\
      lc_rec_ln k P

  | t_Branch r c branches =>
      let fix lc_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              lc_rec_ln k b /\ lc_branches bs'
          end
      in lc_rec_ln k c /\ lc_branches branches
  end.

Definition lc_ln (t : term_ln) := lc_rec_ln 0 t.

Inductive value_ln : term_ln -> Prop :=

  (* λ-values *)
  | V_Type_ln :
      forall i,
        value_ln (t_Type i)

  | V_Lam_ln :
      forall A b,
        value_ln A ->
        value_ln (t_Lam A b)

  | V_Nat_ln :
      value_ln t_Nat

  | V_Zero_ln :
      value_ln t_Zero

  | V_Succ_ln :
      forall n,
        value_ln n ->
        value_ln (t_Succ n)

  | V_Chan_ln :
      forall e,
        value_ln (t_chan e).


(* numeric values predicate (Nat values) *)
Inductive nat_value : term_ln -> Prop :=
| nv_zero : nat_value t_Zero
| nv_succ : forall n, nat_value n -> nat_value (t_Succ n).


Fixpoint notin_bvar (k : nat) (t : term_ln) {struct t} : Prop :=
  match t with

  (* ---------- core ---------- *)

  | t_bvar n =>
      n <> k

  | t_fvar _ =>
      True

  | t_Type _ =>
      True

  | t_Pi A B =>
      notin_bvar k A /\
      notin_bvar (S k) B

  | t_Lam A b =>
      notin_bvar k A /\
      notin_bvar (S k) b

  | t_App t1 t2 =>
      notin_bvar k t1 /\
      notin_bvar k t2

  | t_Nat =>
      True

  | t_Zero =>
      True

  | t_Succ n =>
      notin_bvar k n

  | t_NatRec_ln P z s n =>
      notin_bvar k P /\
      notin_bvar k z /\
      notin_bvar k s /\
      notin_bvar k n

  (* ---------- session types ---------- *)

  | t_Session =>
      True

  | t_End =>
      True

  | t_SendTy r A Se =>
      notin_bvar k A /\
      notin_bvar k Se

  | t_RecvTy r A Se =>
      notin_bvar k A /\
      notin_bvar (S k) Se

  (* ---------- session operations ---------- *)

  | t_chan _ =>
      True

  | t_SendV r c v P =>
      notin_bvar k c /\
      notin_bvar k v /\
      notin_bvar k P

  | t_Recv r c body =>
      notin_bvar k c /\
      notin_bvar k body

  | t_Close c =>
      notin_bvar k c

  | t_Wait c =>
      notin_bvar k c

  | t_Fork p =>
      notin_bvar k p

  | t_Par p q =>
      notin_bvar k p /\
      notin_bvar k q

  (* ---------- branching ---------- *)

  | t_SelectTy r branches =>
      let fix nb_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              notin_bvar k b /\ nb_branches bs'
          end
      in nb_branches branches

  | t_BranchTy r branches =>
      let fix nb_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              notin_bvar k b /\ nb_branches bs'
          end
      in nb_branches branches

  | t_Select r l c P =>
      notin_bvar k c /\
      notin_bvar k P

  | t_Branch r c branches =>
      let fix nb_branches (bs : list (string * term_ln)) :=
          match bs with
          | [] => True
          | (_,b)::bs' =>
              notin_bvar k b /\ nb_branches bs'
          end
      in notin_bvar k c /\ nb_branches branches

  end.

(* simple lookup for a local branch body by label *)
Fixpoint lookup_branch (l : string) (bs : list (string * term_ln)) : option term_ln :=
  match bs with
  | [] => None
  | (l0, body) :: bs' =>
      if String.eqb l l0 then Some body else lookup_branch l bs'
  end.

Inductive beta_head_n_ln : term_ln -> term_ln -> Prop :=

(* ---------------- β (application) ---------------- *)

| b_beta_app_n :
    forall A b s,
      lc_rec_ln 1 b ->
      lc_rec_ln 0 s ->
      beta_head_n_ln
        (t_App (t_Lam A b) s)
        (open_ln b s)

(* ---------------- NatRec zero ---------------- *)

| b_natrec_zero_n :
    forall P z s,
      lc_rec_ln 0 P ->
      lc_rec_ln 0 z ->
      lc_rec_ln 0 s ->
      beta_head_n_ln
        (t_NatRec_ln P z s t_Zero)
        z

(* ---------------- NatRec succ ---------------- *)


| b_natrec_succ_n :
    forall P z s n,
      lc_rec_ln 0 P ->
      lc_rec_ln 0 z ->
      lc_rec_ln 0 s ->
      lc_rec_ln 0 n ->
      beta_head_n_ln
        (t_NatRec_ln P z s (t_Succ n))
        (t_App
           (t_App s n)
           (t_NatRec_ln P z s n))

| b_comm_multi :
    forall s r1 r2 v P body,

      value_ln v ->

      beta_head_n_ln
        (t_Par
           (t_SendV r2 (t_chan (s, r1)) v P)
           (t_Recv  r1 (t_chan (s, r2)) body))
        (t_Par
           P
           (open_ln body v))

| b_comm_choice_n :
    forall s p q l branches P branch_body,
      lookup_branch l branches = Some branch_body ->
      beta_head_n_ln
        (t_Par
           (t_Select q l (t_chan (s,p)) P)
           (t_Branch p (t_chan (s,q)) branches))
        (t_Par
           P
           branch_body).

Inductive beta_n_ln : term_ln -> term_ln -> Prop :=

| beta_head_step_n :
    forall t u,
      beta_head_n_ln t u ->
      beta_n_ln t u

(* ---------- core congruence ---------- *)

| beta_app1_n :
    forall t1 t1' t2,
      beta_n_ln t1 t1' ->
      beta_n_ln (t_App t1 t2)
                (t_App t1' t2)

| beta_app2_n :
    forall v1 t2 t2',
      value_ln v1 ->
      beta_n_ln t2 t2' ->
      beta_n_ln (t_App v1 t2)
                (t_App v1 t2')

| beta_succ_n :
    forall n n',
      beta_n_ln n n' ->
      beta_n_ln (t_Succ n)
                (t_Succ n')

| beta_natrec_scrut_n :
    forall P z s n n',
      beta_n_ln n n' ->
      beta_n_ln
        (t_NatRec_ln P z s n)
        (t_NatRec_ln P z s n')


(* ---------- session type congruence ---------- *)

| beta_SendTy_A_n :
    forall r A A' S,
      beta_n_ln A A' ->
      beta_n_ln (t_SendTy r A S)
                (t_SendTy r A' S)

| beta_SendTy_S_n :
    forall r A S S',
      beta_n_ln S S' ->
      beta_n_ln (t_SendTy r A S)
                (t_SendTy r A S')

| beta_RecvTy_A_n :
    forall r A A' S,
      beta_n_ln A A' ->
      beta_n_ln (t_RecvTy r A S)
                (t_RecvTy r A' S)

| beta_RecvTy_S_n :
    forall r A S S',
      beta_n_ln S S' ->
      beta_n_ln (t_RecvTy r A S)
                (t_RecvTy r A S')


(* ---------- session term congruence ---------- *)

| beta_SendV_c_n :
    forall r c c' v P,
      beta_n_ln c c' ->
      beta_n_ln (t_SendV r c v P)
                (t_SendV r c' v P)

| beta_SendV_v_n :
    forall r c v v' P,
      beta_n_ln v v' ->
      beta_n_ln (t_SendV r c v P)
                (t_SendV r c v' P)

| beta_SendV_v_P :
    forall r c v P P',
      beta_n_ln P P' ->
      beta_n_ln (t_SendV r c v P)
                (t_SendV r c v P')

(* 🔴 binding receive *)
| beta_Recv_c_n :
    forall r c c' body,
      beta_n_ln c c' ->
      beta_n_ln (t_Recv r c body)
                (t_Recv r c' body)

| beta_Recv_body_n :
    forall r c body body',
      beta_n_ln body body' ->
      beta_n_ln (t_Recv r c body)
                (t_Recv r c body')


| beta_Close_n :
    forall c c',
      beta_n_ln c c' ->
      beta_n_ln (t_Close c)
                (t_Close c')

| beta_Wait_n :
    forall c c',
      beta_n_ln c c' ->
      beta_n_ln (t_Wait c)
                (t_Wait c')

| beta_Fork_n :
    forall p p',
      beta_n_ln p p' ->
      beta_n_ln (t_Fork p)
                (t_Fork p')

| beta_Par_l_n :
    forall p p' q,
      beta_n_ln p p' ->
      beta_n_ln (t_Par p q)
                (t_Par p' q)

| beta_Par_r_n :
    forall p q q',
      beta_n_ln q q' ->
      beta_n_ln (t_Par p q)
                (t_Par p q')

| beta_Select_c_n :
    forall r l c c' P,
      beta_n_ln c c' ->
      beta_n_ln (t_Select r l c P)
                (t_Select r l c' P)

| beta_Select_P_n :
    forall r l c P P',
      beta_n_ln P P' ->
      beta_n_ln (t_Select r l c P)
                (t_Select r l c P')

| beta_Branch_c_n :
    forall r c c' bs,
      beta_n_ln c c' ->
      beta_n_ln (t_Branch r c bs)
                (t_Branch r c' bs).

Inductive par_conv_n_ln : term_ln -> term_ln -> Prop :=

| par_conv_refl :
    forall t,
      par_conv_n_ln t t

(* β in parallel *)
| par_conv_beta :
    forall t u,
      beta_n_ln t u ->
      par_conv_n_ln t u


(* ---------- core structural recursion ---------- *)

| par_conv_lam :
    forall A A' b b',
      par_conv_n_ln A A' ->
      par_conv_n_ln b b' ->
      par_conv_n_ln (t_Lam A b)
                    (t_Lam A' b')

| par_conv_pi :
    forall A A' B B',
      par_conv_n_ln A A' ->
      par_conv_n_ln B B' ->
      par_conv_n_ln (t_Pi A B)
                    (t_Pi A' B')

| par_conv_app :
    forall t1 t1' t2 t2',
      par_conv_n_ln t1 t1' ->
      par_conv_n_ln t2 t2' ->
      par_conv_n_ln (t_App t1 t2)
                    (t_App t1' t2')

| par_conv_succ :
    forall n n',
      par_conv_n_ln n n' ->
      par_conv_n_ln (t_Succ n)
                    (t_Succ n')

| par_conv_natrec :
    forall P P' z z' s s' n n',
      par_conv_n_ln P P' ->
      par_conv_n_ln z z' ->
      par_conv_n_ln s s' ->
      par_conv_n_ln n n' ->
      par_conv_n_ln (t_NatRec_ln P z s n)
                    (t_NatRec_ln P' z' s' n')


(* ---------- session types ---------- *)

| par_conv_Session :
    par_conv_n_ln t_Session t_Session

| par_conv_End :
    par_conv_n_ln t_End t_End

| par_conv_SendTy :
    forall r A A' S S',
      par_conv_n_ln A A' ->
      par_conv_n_ln S S' ->
      par_conv_n_ln (t_SendTy r A S)
                    (t_SendTy r A' S')

| par_conv_RecvTy :
    forall r A A' S S',
      par_conv_n_ln A A' ->
      par_conv_n_ln S S' ->
      par_conv_n_ln (t_RecvTy r A S)
                    (t_RecvTy r A' S')


(* ---------- session term operations ---------- *)

| par_conv_SendV :
    forall r c c' v v' P P',
      par_conv_n_ln c c' ->
      par_conv_n_ln v v' ->
      par_conv_n_ln P P' ->
      par_conv_n_ln (t_SendV r c v P)
                    (t_SendV r c' v' P')


(* 🔴 binding receive *)
| par_conv_Recv :
    forall r c c' body body',
      par_conv_n_ln c c' ->
      par_conv_n_ln body body' ->
      par_conv_n_ln (t_Recv r c body)
                    (t_Recv r c' body')


| par_conv_Close :
    forall c c',
      par_conv_n_ln c c' ->
      par_conv_n_ln (t_Close c)
                    (t_Close c')

| par_conv_Wait :
    forall c c',
      par_conv_n_ln c c' ->
      par_conv_n_ln (t_Wait c)
                    (t_Wait c')

| par_conv_Fork :
    forall p p',
      par_conv_n_ln p p' ->
      par_conv_n_ln (t_Fork p)
                    (t_Fork p')

| par_conv_Par :
    forall p p' q q',
      par_conv_n_ln p p' ->
      par_conv_n_ln q q' ->
      par_conv_n_ln (t_Par p q)
                    (t_Par p' q')

| par_conv_SelectTy :
    forall r bs bs',
      par_conv_branches bs bs' ->
      par_conv_n_ln
        (t_SelectTy r bs)
        (t_SelectTy r bs')

| par_conv_BranchTy :
    forall r bs bs',
      par_conv_branches bs bs' ->
      par_conv_n_ln
        (t_BranchTy r bs)
        (t_BranchTy r bs')

| par_conv_Select :
    forall r l c c' P P',
      par_conv_n_ln c c' ->
      par_conv_n_ln P P' ->
      par_conv_n_ln
        (t_Select r l c P)
        (t_Select r l c' P')

| par_conv_Branch :
    forall r c c' bs bs',
      par_conv_n_ln c c' ->
      par_conv_branches bs bs' ->
      par_conv_n_ln
        (t_Branch r c bs)
        (t_Branch r c' bs')

with par_conv_branches :
  list (string * term_ln) ->
  list (string * term_ln) ->
  Prop :=

| pcb_nil :
    par_conv_branches [] []

| pcb_cons :
    forall l b b' bs bs',
      par_conv_n_ln b b' ->
      par_conv_branches bs bs' ->
      par_conv_branches ((l,b)::bs)
                        ((l,b')::bs').
                        
(*  | par_conv_Data:
    par_conv_n_ln t_Data t_Data. *)

(* ================================================= *)
(* 4. Declarative conversion (βη-congruence)         *)
(* ================================================= *)

Definition convertible_n_par_ln : term_ln -> term_ln -> Prop :=
  clos_refl_sym_trans term_ln par_conv_n_ln.

Definition ictx := list (string * term_ln).  (* unrestricted *)


Definition lctx := LM.t term_ln.
Definition empty_lctx := LM.empty term_ln.
Definition lookup_l := LM.find.
Definition remove_l := LM.remove.

Definition disjoint (Δ1 Δ2 : lctx) :=
  forall e T1 T2,
    LM.find e Δ1 = Some T1 ->
    LM.find e Δ2 = Some T2 ->
    False.

Definition merge (Δ1 Δ2 : lctx) : lctx :=
  LM.fold (fun e T acc => LM.add e T acc) Δ1 Δ2.

Definition split4
  (Δ ΔP Δz Δs Δn : lctx) : Prop :=
  disjoint ΔP Δz /\
  disjoint ΔP Δs /\
  disjoint ΔP Δn /\
  disjoint Δz Δs /\
  disjoint Δz Δn /\
  disjoint Δs Δn /\
  Δ = merge ΔP (merge Δz (merge Δs Δn)).

(* Fixpoint dual (S : term_ln) : term_ln :=
  match S with
  | t_End         => t_End
  | t_SendTy A S' => t_RecvTy A (dual S')
  | t_RecvTy A S' => t_SendTy A (dual S')
  | _             => S
  end. *)

Inductive gtype :=
| g_end
| g_msg :
    string -> string ->
    term_ln ->
    gtype
    -> gtype
| g_choice :
    string -> string ->
    list (string * gtype)
    -> gtype
| g_natrec :
    term_ln
    -> gtype
    -> gtype
    -> term_ln
    -> gtype
| g_bvar : nat -> gtype.

Fixpoint open_rec_gtype
  (k : nat)
  (U : gtype)
  (G : gtype)
  : gtype :=
  match G with

  | g_end =>
      g_end

  | g_bvar n =>
      if Nat.eqb n k then U else g_bvar n

  | g_msg p q A G' =>
      g_msg p q
        A
        (open_rec_gtype k U G')

| g_choice p q branches =>
    g_choice p q
      (map (fun '(l,G') =>
              (l, open_rec_gtype k U G'))
           branches)

  | g_natrec P z s n =>
      g_natrec
        P
        (open_rec_gtype k U z)
        (open_rec_gtype k U s)
        n
  end.

Definition open_gtype (G U : gtype) :=
  open_rec_gtype 0 U G.

Fixpoint lc_rec_gtype (k : nat) (G : gtype) : Prop :=
  match G with

  | g_end =>
      True

  | g_bvar n =>
      n < k

  | g_msg _ _ A G' =>
      lc_rec_ln k A /\
      lc_rec_gtype k G'

  | g_choice _ _ branches =>
      let fix lc_branches bs :=
          match bs with
          | [] => True
          | (_,G')::bs' =>
              lc_rec_gtype k G' /\ lc_branches bs'
          end
      in lc_branches branches
      
  | g_natrec P z s n =>
      lc_rec_ln k P /\
      lc_rec_gtype k z /\
      lc_rec_gtype k s /\
      lc_rec_ln k n
  end.

Definition lc_gtype G := lc_rec_gtype 0 G.

Fixpoint term_eqb (t1 : term_ln) {struct t1} : term_ln -> bool :=
  fun t2 =>
    match t1, t2 with

    | t_bvar n1, t_bvar n2 =>
        Nat.eqb n1 n2

    | t_fvar x1, t_fvar x2 =>
        String.eqb x1 x2

    | t_Type i1, t_Type i2 =>
        Nat.eqb i1 i2

    | t_Pi A1 B1, t_Pi A2 B2 =>
        term_eqb A1 A2 && term_eqb B1 B2

    | t_Lam A1 b1, t_Lam A2 b2 =>
        term_eqb A1 A2 && term_eqb b1 b2

    | t_App f1 a1, t_App f2 a2 =>
        term_eqb f1 f2 && term_eqb a1 a2

    | t_Nat, t_Nat => true
    | t_Zero, t_Zero => true

    | t_Succ n1, t_Succ n2 =>
        term_eqb n1 n2

    | t_NatRec_ln P1 z1 s1 n1,
      t_NatRec_ln P2 z2 s2 n2 =>
        term_eqb P1 P2 &&
        term_eqb z1 z2 &&
        term_eqb s1 s2 &&
        term_eqb n1 n2

    | t_Session, t_Session => true
    | t_End, t_End => true

    | t_SendTy r1 A1 S1, t_SendTy r2 A2 S2 =>
        String.eqb r1 r2 && term_eqb A1 A2 && term_eqb S1 S2

    | t_RecvTy r1 A1 S1, t_RecvTy r2 A2 S2 =>
        String.eqb r1 r2 && term_eqb A1 A2 && term_eqb S1 S2

    | t_chan (s1,r1), t_chan (s2,r2) =>
        String.eqb s1 s2 && String.eqb r1 r2

    | t_SendV r1 c1 v1 P1, t_SendV r2 c2 v2 P2 =>
        String.eqb r1 r2 && term_eqb c1 c2 && term_eqb v1 v2 && term_eqb P1 P2

    | t_Recv r1 c1 b1, t_Recv r2 c2 b2 =>
        String.eqb r1 r2 && term_eqb c1 c2 && term_eqb b1 b2

    | t_Close c1, t_Close c2 => term_eqb c1 c2
    | t_Wait c1, t_Wait c2   => term_eqb c1 c2
    | t_Fork p1, t_Fork p2   => term_eqb p1 p2
    | t_Par p1 q1, t_Par p2 q2 => term_eqb p1 p2 && term_eqb q1 q2

    | t_SelectTy r1 bs1, t_SelectTy r2 bs2 =>
        String.eqb r1 r2 &&
        (
          let fix branches_eqb
                (bs1' : list (string * term_ln))
                (bs2' : list (string * term_ln))
                {struct bs1'} : bool :=
              match bs1', bs2' with
              | [], [] => true
              | (l1,b1)::bs1'', (l2,b2)::bs2'' =>
                  String.eqb l1 l2 &&
                  term_eqb b1 b2 &&
                  branches_eqb bs1'' bs2''
              | _, _ => false
              end
          in branches_eqb bs1 bs2
        )

    | t_BranchTy r1 bs1, t_BranchTy r2 bs2 =>
        String.eqb r1 r2 &&
        (
            let fix branches_eqb
                  (bs1' : list (string * term_ln))
                  (bs2' : list (string * term_ln))
                  {struct bs1'} : bool :=
                match bs1', bs2' with
                | [], [] => true
                | (l1,b1)::bs1'', (l2,b2)::bs2'' =>
                    String.eqb l1 l2 &&
                    term_eqb b1 b2 &&
                    branches_eqb bs1'' bs2''
                | _, _ => false
                end
            in branches_eqb bs1 bs2
        )

    | t_Select r1 l1 c1 P1, t_Select r2 l2 c2 P2 =>
        String.eqb r1 r2 && String.eqb l1 l2 && term_eqb c1 c2 && term_eqb P1 P2

    | t_Branch r1 c1 bs1, t_Branch r2 c2 bs2 =>
        String.eqb r1 r2 && term_eqb c1 c2 &&
        (
          let fix branches_eqb
                (bs1' : list (string * term_ln))
                (bs2' : list (string * term_ln))
                {struct bs1'} : bool :=
              match bs1', bs2' with
              | [], [] => true
              | (l1,b1)::bs1'', (l2,b2)::bs2'' =>
                  String.eqb l1 l2 &&
                  term_eqb b1 b2 &&
                  branches_eqb bs1'' bs2''
              | _, _ => false
              end
          in branches_eqb bs1 bs2
        )

    | _, _ => false
    end.

Fixpoint gtype_nonemptyb (G : gtype) : bool :=
  match G with
  | g_end => true
  | g_bvar _ => true
  | g_msg _ _ _ G' => gtype_nonemptyb G'
  | g_natrec _ z s _ => andb (gtype_nonemptyb z) (gtype_nonemptyb s)
  | g_choice _ _ branches =>
      match branches with
      | [] => false
      | (_, G') :: bs =>
          let fix go bs' :=
              match bs' with
              | [] => true
              | (_, G'') :: bs'' => andb (gtype_nonemptyb G'') (go bs'')
              end
          in andb (gtype_nonemptyb G') (go bs)
      end
  end.

Definition gtype_nonempty (G : gtype) : Prop := gtype_nonemptyb G = true.

Definition mk_g_choice (p q : string) (bs : list (string * gtype)) : option gtype :=
  match bs with
  | [] => None
  | _ =>
      let fix all_nonempty bs' :=
          match bs' with
          | [] => true
          | (_, G') :: bs'' => andb (gtype_nonemptyb G') (all_nonempty bs'')
          end
      in if all_nonempty bs then Some (g_choice p q bs) else None
  end.

Fixpoint local_session_wfb (t : term_ln) : bool :=
  match t with

  (* -------- Session type constructors -------- *)

  | t_SendTy _ A Se =>
      andb (local_session_wfb A) (local_session_wfb Se)

  | t_RecvTy _ A Se =>
      andb (local_session_wfb A) (local_session_wfb Se)

  | t_SelectTy _ branches =>
      match branches with
      | [] => false
      | (_, Se) :: bs =>
          let fix go bs' :=
              match bs' with
              | [] => true
              | (_, Se') :: bs'' =>
                  andb (local_session_wfb Se') (go bs'')
              end
          in andb (local_session_wfb Se) (go bs)
      end

  | t_BranchTy _ branches =>
      match branches with
      | [] => false
      | (_, Se) :: bs =>
          let fix go bs' :=
              match bs' with
              | [] => true
              | (_, Se') :: bs'' =>
                  andb (local_session_wfb Se') (go bs'')
              end
          in andb (local_session_wfb Se) (go bs)
      end

  (* -------- Type-level structure -------- *)

  | t_Pi A B =>
      andb (local_session_wfb A) (local_session_wfb B)

  | t_Lam A b =>
      andb (local_session_wfb A) (local_session_wfb b)

  | t_App f a =>
      andb (local_session_wfb f) (local_session_wfb a)

  | t_NatRec_ln P z s _ =>
      andb (local_session_wfb P)
           (andb (local_session_wfb z)
                 (local_session_wfb s))

  (* -------- Base constructors -------- *)

  | t_Type _ => true
  | t_Nat => true
  | t_Zero => true
  | t_Succ _ => true
  | t_bvar _ => true
  | t_fvar _ => true
  | t_chan _ => true
  | t_Session => true
  | t_End => true

  (* -------- Process-level terms (ignore) -------- *)

  | t_SendV _ _ _ _ => true
  | t_Recv _ _ _ => true
  | t_Close _ => true
  | t_Wait _ => true
  | t_Fork _ => true
  | t_Par _ _ => true
  | t_Select _ _ _ _ => true
  | t_Branch _ _ _ => true

  end.

Definition local_session_wf (t : term_ln) : Prop :=
  local_session_wfb t = true.

Fixpoint project (r : string) (G : gtype)
  : option term_ln :=
  match G with

  | g_end => Some t_End
  | g_bvar n => Some (t_bvar n)

  | g_msg p q A G' =>
      if String.eqb r p then
        option_map (fun Se => t_SendTy q A Se) (project r G')
      else if String.eqb r q then
        option_map (fun Se => t_RecvTy p A Se) (project r G')
      else
        project r G'

  | g_natrec P z s n =>
      match project r z, project r s with
      | Some Sz, Some Ss =>
          Some (t_NatRec_ln P Sz (t_Lam t_Nat (t_Lam t_Session Ss)) n)
      | _, _ => None
      end

  | g_choice p q branches =>

      let fix go (bs : list (string * gtype))
          : option (list (string * term_ln)) :=
        match bs with
        | [] => Some []
        | (l, G') :: bs' =>
            match project r G', go bs' with
            | Some Se, Some Ss => Some ((l, Se) :: Ss)
            | _, _ => None
            end
        end
      in

      let projected := go branches in

      if String.eqb r p then
        option_map (fun Ss => t_SelectTy q Ss) projected
      else if String.eqb r q then
        option_map (fun Ss => t_BranchTy p Ss) projected
      else
        match projected with
        | Some ((_, Se) :: Ss) =>
            if forallb (fun '(_, S') => term_eqb Se S') Ss
            then Some Se
            else None
        | _ => None
        end
  end.

Fixpoint project_branches
  (r : string)
  (branches : list (string * gtype))
  : option (list (string * term_ln)) :=
  match branches with
  | [] => Some []
  | (l, G') :: bs' =>
      match project r G', project_branches r bs' with
      | Some Se, Some Ss => Some ((l, Se) :: Ss)
      | _, _ => None
      end
  end.

Lemma project_branches_eq :
  forall branches r,
    project_branches r branches =
    (fix go (bs : list (string * gtype)) :=
       match bs with
       | [] => Some []
       | (l,G')::bs' =>
           match project r G', go bs' with
           | Some Se, Some Ss => Some ((l,Se)::Ss)
           | _, _ => None
           end
       end) branches.
Proof. intro br.
       induction br; intros.
       - simpl. easy.
       - simpl. destruct a.
         case_eq(project r g); intros.
         + rewrite IHbr. easy.
         + easy.
Qed.

(* Fixpoint project (r : string) (G : gtype)
  : option term_ln :=
  match G with

  | g_end =>
      Some t_End

  | g_bvar n =>
      Some (t_bvar n)

  | g_msg p q A G' =>
      if String.eqb r p then
        option_map (fun Se => t_SendTy q A Se)
                   (project r G')
      else if String.eqb r q then
        option_map (fun Se => t_RecvTy p A Se)
                   (project r G')
      else
        project r G'

  | g_natrec P z s n =>
      match project r z, project r s with
      | Some Sz, Some Ss =>
          Some
            (t_NatRec_ln
               P
               Sz
               (t_Lam t_Nat
                  (t_Lam t_Session Ss))
               n)
      | _, _ => None
      end

  | g_choice p q branches =>

      (* local helper — structurally recursive on branches *)
      let fix go (bs : list (string * gtype))
          : option (list (string * term_ln)) :=
        match bs with
        | [] => Some []
        | (l, G') :: bs' =>
            match project r G', go bs' with
            | Some Se, Some Ss => Some ((l, Se) :: Ss)
            | _, _ => None
            end
        end
      in

      if String.eqb r p then
        (* selector side *)
        option_map (fun Ss => t_SelectTy q Ss)
                   (go branches)

      else if String.eqb r q then
        (* brancher side *)
        option_map (fun Ss => t_BranchTy p Ss)
                   (go branches)

      else
        (* third-party merging *)
        match go branches with
        | Some ((_, Se) :: Ss) =>
            if forallb (fun '(_, S') => term_eqb Se S') Ss
            then Some Se
            else None
        | _ => None
        end
  end. *)

(* For a g_choice p q branches and role r (either p or q),
   return list of (label, G', Se) where Se = project r G'. *)
Definition project_branches_with_globals (r : string) (G : gtype)
  : option (list (string * gtype * term_ln)) :=
  match G with
  | g_choice p q branches =>
      if String.eqb r p || String.eqb r q then
        let fix go bs :=
            match bs with
            | [] => Some []
            | (lbl, G') :: bs' =>
                match project r G', go bs' with
                | Some Se, Some rest => Some ((lbl, G', Se) :: rest)
                | _, _ => None
                end
            end
        in go branches
      else None
  | _ => None
  end.



Module GM := FMapAVL.Make(String_as_OT).

Definition gctx := GM.t (gtype ).

Definition empty_gctx : gctx := GM.empty (gtype).

Definition lookup_g (Σ : gctx) (s : string) : option (gtype) :=
  GM.find s Σ.

Definition update_g (Σ : gctx) (s : string) (Gpos : gtype) : gctx :=
  GM.add s Gpos Σ.

Definition update_g_safe (Σ : gctx) (s : string) (G : gtype) : option gctx :=
  if gtype_nonemptyb G then Some (GM.add s G Σ) else None.

Fixpoint lookup_ln (Γ : list (string * term_ln)) (x : string) : option term_ln :=
  match Γ with
  | [] => None
  | (y,T)::Γ' => if String.eqb x y then Some T else lookup_ln Γ' x
  end.

Definition gctx_wf (Σ : gctx) : Prop :=
  forall s G,
    lookup_g Σ s = Some G ->
    gtype_nonempty G.


Inductive has_type_ln: ictx -> lctx -> term_ln -> term_ln -> Prop :=

(* ========================= *)
(* Variables                 *)
(* ========================= *)

| ty_var_l :
    forall Γ Δ s r S,
      LM.find (s,r) Δ = Some S ->
      has_type_ln Γ Δ (t_chan (s,r)) S

| ty_Type :
    forall Γ i,
      has_type_ln Γ empty_lctx
        (t_Type i)
        (t_Type (S i))

| ty_Pi :
    forall Γ A B i j L,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln ((x,A)::Γ) empty_lctx
           (open_ln B (t_fvar x))
           (t_Type j)) ->
      has_type_ln Γ empty_lctx
        (t_Pi A B)
        (t_Type (Nat.max i j))

| ty_Lam :
    forall Γ Δ A b B i L,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln ((x,A)::Γ) Δ
           (open_ln b (t_fvar x))
           (open_ln B (t_fvar x))) ->
      has_type_ln Γ Δ
        (t_Lam A b)
        (t_Pi A B)

| ty_App :
    forall Γ Δ t1 t2 A B,
      has_type_ln Γ Δ t1 (t_Pi A B) ->
      has_type_ln Γ empty_lctx t2 A ->
      has_type_ln Γ Δ
        (t_App t1 t2)
        (open_ln B t2)

(* ========================= *)
(* Natural Numbers           *)
(* ========================= *)

| ty_Nat :
    forall Γ Δ,
      has_type_ln Γ Δ t_Nat (t_Type 0)

| ty_Zero :
    forall Γ Δ,
      has_type_ln Γ Δ t_Zero t_Nat

| ty_Succ :
    forall Γ Δ n,
      has_type_ln Γ Δ n t_Nat ->
      has_type_ln Γ Δ (t_Succ n) t_Nat

(* ========================= *)
(* NatRec (linear-safe)      *)
(* ========================= *)

| ty_NatRec_strong :
    forall Γ Δ P z s n k L,

      lc_rec_ln 0 P ->
      lc_rec_ln 0 z ->
      lc_rec_ln 0 s ->
      lc_rec_ln 0 n ->

      (* Motive pure *)
      has_type_ln Γ empty_lctx P
        (t_Pi t_Nat (t_Type k)) ->

      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln 
           ((x, t_Nat) :: Γ)
           empty_lctx
           (t_App P (t_fvar x))
           (t_Type k)) ->

      (* Base case may use Δ *)
      has_type_ln Γ Δ
        z
        (t_App P t_Zero) ->

      (* Step function pure *)
      has_type_ln Γ empty_lctx
        s
        (t_Pi t_Nat
           (t_Pi (t_App P (t_bvar 0))
                 (t_App P (t_Succ (t_bvar 1))))) ->

      (* Instantiated step typing *)
      (forall x y,
         x <> y ->
         ~ In x L ->
         ~ In y L ->
         ~ In x (map fst Γ) ->
         ~ In y (map fst Γ) ->
         has_type_ln 
           ((y, t_App P (t_fvar x))
             :: (x, t_Nat) :: Γ)
           empty_lctx
           (t_App (t_App s (t_fvar x)) (t_fvar y))
           (t_App P (t_Succ (t_fvar x)))) ->

      (* Scrutinee pure *)
      has_type_ln Γ empty_lctx n t_Nat ->

      has_type_ln Γ Δ
        (t_NatRec_ln P z s n)
        (t_App P n)

(* ========================= *)
(* Session Types (pure)      *)
(* ========================= *)

| ty_Session :
    forall Γ,
      has_type_ln Γ empty_lctx t_Session (t_Type 0)

| ty_End :
    forall Γ,
      has_type_ln Γ empty_lctx t_End t_Session

| ty_SendTy :
    forall Γ r A S i,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      has_type_ln Γ empty_lctx S t_Session ->
      has_type_ln Γ empty_lctx
        (t_SendTy r A S)
        t_Session

| ty_RecvTy :
    forall Γ r A S i L,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln ((x,A)::Γ) empty_lctx
           (open_ln S (t_fvar x))
           t_Session) ->
      has_type_ln Γ empty_lctx
        (t_RecvTy r A S)
        t_Session

(* typing for select/branch session *types* (they inhabit t_Session) *)

| ty_SelectTy :
    forall Γ r branches,
      local_session_wf (t_SelectTy r branches) ->
      (forall lbl Se,
         In (lbl, Se) branches ->
         has_type_ln Γ empty_lctx Se t_Session) ->
      has_type_ln Γ empty_lctx
        (t_SelectTy r branches)
        t_Session

| ty_BranchTy :
    forall Γ r branches,
      local_session_wf (t_BranchTy r branches) ->
      (forall lbl Se,
         In (lbl, Se) branches ->
         has_type_ln Γ empty_lctx Se t_Session) ->
      has_type_ln Γ empty_lctx
        (t_BranchTy r branches)
        t_Session

(* ========================= *)
(* Session Terms             *)
(* ========================= *)

| ty_SendV :
    forall Γ Δ s p q A S v P,

      LM.find (s,p) Δ = Some (t_SendTy q A S) ->

      has_type_ln Γ empty_lctx v A ->

      has_type_ln Γ
        (LM.add (s,p) S (LM.remove (s,p) Δ))
        P
        t_End ->

      has_type_ln Γ Δ
        (t_SendV q (t_chan (s,p)) v P)
        t_End

| ty_Recv :
    forall Γ Δ s p q A S body L,

      LM.find (s,p) Δ = Some (t_RecvTy q A S) ->

      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln 
           ((x,A)::Γ)
           (LM.add (s,p) (open_ln S (t_fvar x))
              (LM.remove (s,p) Δ))
           (open_ln body (t_fvar x))
           t_End) ->

      has_type_ln Γ Δ
        (t_Recv q (t_chan (s,p)) body)
        t_End

(* Selector typing: choose label l and continue with P.
   local_cont is the continuation term supplied by the programmer.
   local_cont : term_ln
*)
| ty_Select :
    forall Γ Δ s p q branches l S local_cont,

      LM.find (s,p) Δ =
        Some (t_SelectTy q branches) ->

      In (l, S) branches ->

      has_type_ln Γ
        (LM.add (s,p) S (LM.remove (s,p) Δ))
        local_cont
        t_End ->

      has_type_ln Γ Δ
        (t_Select q l (t_chan (s,p)) local_cont)
        t_End

(* Brancher typing: local_branches is the list of (label * body) supplied by programmer.
   local_branches : list (string * term_ln)
*)
| ty_Branch :
    forall Γ Δ s p q branches local_branches,

      LM.find (s,q) Δ =
        Some (t_BranchTy p branches) ->

      (forall lbl S,
         In (lbl, S) branches ->
         exists body,
           lookup_branch lbl local_branches = Some body /\
           has_type_ln Γ
             (LM.add (s,q) S (LM.remove (s,q) Δ))
             body
             t_End) ->

      has_type_ln Γ Δ
        (t_Branch p (t_chan (s,q)) local_branches)
        t_End

(* ========================= *)
(* Parallel                  *)
(* ========================= *)


| ty_Close :
    forall Γ Δ s r,
      LM.find (s,r) Δ = Some t_End ->
      has_type_ln Γ
        (LM.remove (s,r) Δ)
        (t_Close (t_chan (s,r)))
        t_End

(* | ty_Wait :
    forall Σ Γ Δ s r,

      LM.find (s,r) Δ = Some t_End ->

      has_type_ln Σ Γ
        (LM.remove (s,r) Δ)
        (t_Wait (t_chan (s,r)))
        t_End
 *)
| ty_Par :
    forall Γ Δ1 Δ2 P Q,
      disjoint Δ1 Δ2 ->
      has_type_ln Γ Δ1 P t_End ->
      has_type_ln Γ Δ2 Q t_End ->
      has_type_ln Γ (merge Δ1 Δ2)
        (t_Par P Q)
        t_End

(* | ty_Fork :
    forall Σ Γ Δ P,
      has_type_ln Σ Γ empty_lctx P t_End ->
      has_type_ln Σ Γ Δ (t_Fork P) t_End *)

| ty_conv :
    forall Γ Δ t A B,
      has_type_ln Γ Δ t A ->
      convertible_n_par_ln A B ->
      has_type_ln Γ Δ t B.


(* ================================================= *)
(* Roles extraction (assumed duplicates removed)     *)
(* ================================================= *)

Fixpoint roles_of (G : gtype) : list string :=
  match G with
  | g_end => []
  | g_bvar _ => []
  | g_msg p q _ G' =>
      p :: q :: roles_of G'
  | g_choice p q branches =>
      let branch_roles :=
        fold_left
          (fun acc '(_,G') => acc ++ roles_of G')
          branches
          []
      in
      p :: q :: branch_roles
  | g_natrec _ z s _ =>
      roles_of z ++ roles_of s
  end.

Fixpoint remove_dups (xs : list string) : list string :=
  match xs with
  | [] => []
  | x :: xs' =>
      if existsb (String.eqb x) xs'
      then remove_dups xs'
      else x :: remove_dups xs'
  end.

Definition roles (G : gtype) : list string :=
  remove_dups (roles_of G).

(* ================================================= *)
(* Branch merge consistency                          *)
(* ================================================= *)

Definition branches_agree_for
  (r : string)
  (branches : list (string * gtype)) : Prop :=
  match branches with
  | [] => True
  | (_, G0) :: bs =>
      match project r G0 with
      | None => False
      | Some S0 =>
          forall lbl G',
            In (lbl, G') bs ->
            project r G' = Some S0
      end
  end.

Definition third_party_consistent
  (p q : string)
  (branches : list (string * gtype)) : Prop :=
  forall r,
    r <> p ->
    r <> q ->
(*     In r (roles (g_choice p q branches)) -> *)
    branches_agree_for r branches.

(* ================================================= *)
(* Global Well-Formedness                            *)
(* ================================================= *)

Inductive gtype_wf : gtype -> Prop :=

| wf_end :
    gtype_wf g_end

| wf_bvar :
    forall n,
      gtype_wf (g_bvar n)

| wf_msg :
    forall p q A G,
      p <> q ->
      gtype_wf G ->
      gtype_wf (g_msg p q A G)

| wf_choice :
    forall p q branches,
      p <> q ->
      branches <> [] ->
      NoDup (map fst branches) ->
      (forall lbl G,
         In (lbl, G) branches ->
         gtype_wf G) ->
      third_party_consistent p q branches ->
      gtype_wf (g_choice p q branches)

| wf_natrec :
    forall P z s n,
      gtype_wf z ->
      gtype_wf s ->
      gtype_wf (g_natrec P z s n).

(* ================================================= *)
(* Projection Totality (derived property)            *)
(* ================================================= *)

Definition projection_total (G : gtype) :=
  forall r,
    exists S, project r G = Some S.

(* ================================================= *)
(* Session Initialization                            *)
(* ================================================= *)

Definition init_session
  (s : string)
  (G : gtype)
  : lctx :=
  fold_left
    (fun acc r =>
       match project r G with
       | Some ST => LM.add (s,r) ST acc
       | None    => acc
       end)
    (roles G)
    empty_lctx.


Lemma In_remove_dups :
  forall xs x,
    In x (remove_dups xs) ->
    In x xs.
Proof.
  intros xs.
  induction xs as [| y ys IH].
  - (* xs = [] *)
    simpl.
    intros H.
    contradiction.

  - (* xs = y :: ys *)
    simpl.
    destruct (existsb (String.eqb y) ys) eqn:Hex.

    + (* duplicate case: remove y *)
      intros x H.
      (* remove_dups (y::ys) = remove_dups ys *)
      apply IH in H.
      right.
      exact H.

    + (* keep y case *)
      intros x H.
      simpl in H.
      destruct H as [H | H].

      * (* x = y *)
        left.
        exact H.

      * (* x in remove_dups ys *)
        right.
        apply IH.
        exact H.
Qed.

Lemma In_remove_dups_reverse :
  forall xs x,
    In x xs ->
    In x (remove_dups xs).
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl. simpl in H.
         destruct H as [H | H].
         + subst.
           case_eq(existsb (eqb x) l); intros.
           ++ apply existsb_exists in H.
              destruct H as (y,(Hy1,Hy2)).
              rewrite String.eqb_eq in Hy2. subst.
              apply IHl. easy.
           ++ simpl. left. easy.
         + case_eq(existsb (eqb a) l); intros.
           ++ apply existsb_exists in H0.
              destruct H0 as (y,(Hy1,Hy2)).
              rewrite String.eqb_eq in Hy2. subst.
              apply IHl. easy.
           ++ simpl. right. apply IHl; easy.
Qed.

Lemma In_roles_msg :
  forall r p q A G,
    In r (roles (g_msg p q A G)) ->
    r = p \/ r = q \/ In r (roles G).
Proof.
  intros r p q A G H.
  unfold roles in H.
  (* roles_of (g_msg ...) = p :: q :: roles_of G *)
  apply In_remove_dups in H.
  simpl in H.
  destruct H as [H | [H | H]].
  - subst. left; easy.
  - subst; right; left; easy.
  - subst; right; right. unfold roles.
    apply In_remove_dups_reverse.
    exact H.
Qed.

Lemma branches_agree_tail :
  forall bs r b,
    branches_agree_for r (b :: bs) ->
    branches_agree_for r bs.
Proof. intro bs.
       induction bs; intros.
       - simpl. easy.
       - simpl. simpl in H.
         destruct a, b. simpl in IHbs.
         case_eq(project r g0); intros.
         + rewrite H0 in H.
           specialize(IHbs r (s0,g0)).
           simpl in IHbs.
           rewrite H0 in IHbs.
           pose proof H as HH.
           specialize(H s g).
           assert( (s, g) = (s, g) \/ In (s, g) bs). left; easy.
           apply H in H1. rewrite H1.
           intros. apply HH with (lbl := lbl). right. easy.
         + rewrite H0 in H. easy.
Qed.

Lemma In_roles_iff_roles_of :
  forall G r,
    In r (roles G) <-> In r (roles_of G).
Proof. intros.
       unfold roles.
       split. intros.
       apply In_remove_dups. easy.
       intros. apply In_remove_dups_reverse. easy.
Qed.

Lemma fold_left_append_const :
  forall (A B: Type)
         (l : list B)
         (bs : list A)
         (acc : list B),
    fold_left
      (fun acc x => acc ++ l)
      bs
      acc
    =
    acc ++
    fold_left
      (fun acc x => acc ++ l)
      bs
      [].
Proof.
  intros A B l bs acc.
  revert acc.
  induction bs as [| x xs IH]; intros acc.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- app_assoc. simpl.
    rewrite (IH l).
    easy.
Qed.

Lemma fold_left_append_general :
  forall (A B : Type)
         (f : A -> list B)
         (bs : list A)
         (acc : list B),
    fold_left
      (fun acc x => acc ++ f x)
      bs
      acc
    =
    acc ++
    fold_left
      (fun acc x => acc ++ f x)
      bs
      [].
Proof.
  intros A B f bs acc.
  revert acc.
  induction bs as [| x xs IH]; intros acc.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- app_assoc. simpl.
    rewrite (IH (f x)).
    easy.
Qed.

Lemma fold_left_roles_decompose :
  forall bs g,
    fold_left
      (fun acc (p:(string*gtype)) => acc ++ roles_of (snd p))
      bs
      (roles_of g)
    =
    roles_of g ++
    fold_left
      (fun acc p => acc ++ roles_of (snd p))
      bs
      [].
Proof. intros.
       rewrite fold_left_append_general. easy.
Qed.

Lemma fold_left_roles_general :
  forall bs acc,
    fold_left
      (fun acc (p: string * gtype) =>
        match p with
        | (_, G') => acc ++ roles_of G'
        end)
      bs
      acc
    =
    acc ++
    fold_left
      (fun acc (p: string * gtype) =>
        match p with
        | (_, G') => acc ++ roles_of G'
        end)
      bs
      [].
Proof.
  induction bs as [| [lbl G'] bs IH]; intros acc.
  - (* bs = [] *)
    simpl. rewrite app_nil_r. reflexivity.

  - (* bs = (lbl,G') :: bs *)
    simpl.
    rewrite IH.
    rewrite <- app_assoc.
    rewrite (IH (roles_of G')).
    reflexivity.
Qed.

Lemma fold_left_roles_decompose2 :
  forall bs g,
    fold_left
      (fun acc (p: (string*gtype)) =>
        match p with
        | (_, G') => acc ++ roles_of G'
        end) bs
      (roles_of g)
    =
    roles_of g ++
    fold_left
       (fun acc p =>
        match p with
        | (_, G') => acc ++ roles_of G'
        end)
      bs
      [].
Proof.
  intros bs acc.
  apply fold_left_roles_general.
Qed.



Lemma third_party_tail :
  forall bs p q b,
  third_party_consistent p q (b :: bs) ->
  third_party_consistent p q bs.
Proof. intros.
       unfold third_party_consistent in *.
       intros.
       apply branches_agree_tail with (b := b).
       apply H; try easy.
(*        simpl.
       apply In_roles_iff_roles_of. simpl.
       apply In_roles_iff_roles_of in H2.
       simpl in H2.
       destruct H2. subst. easy.
       destruct H2. subst. easy.
       simpl in H2.
       right. right.
       destruct b. simpl.
       rewrite fold_left_roles_decompose2.
       rewrite in_app_iff. right. easy. *)
Qed.


(* ================================================= *)
(* Linear Context Coherence                          *)
(* ================================================= *)

Definition coherent_session (s : string) (Δ : lctx) : Prop :=
  exists G,
    gtype_wf G /\
    forall r S,
      LM.find (s,r) Δ = Some S ->
      project r G = Some S.

Fixpoint lc_branches_ln (k : nat)
         (bs : list (string * term_ln)) : Prop :=
  match bs with
  | [] => True
  | (_,b)::bs' =>
      lc_rec_ln k b /\ lc_branches_ln k bs'
  end.

Section term_ln_ind_strong.

  Variable P : term_ln -> Prop.

  Hypothesis P_bvar :
    forall n, P (t_bvar n).

  Hypothesis P_fvar :
    forall x, P (t_fvar x).

  Hypothesis P_Type :
    forall i, P (t_Type i).

  Hypothesis P_Pi :
    forall A B,
      P A ->
      P B ->
      P (t_Pi A B).

  Hypothesis P_Lam :
    forall A b,
      P A ->
      P b ->
      P (t_Lam A b).

  Hypothesis P_App :
    forall f a,
      P f ->
      P a ->
      P (t_App f a).

  Hypothesis P_Nat :
    P t_Nat.

  Hypothesis P_Zero :
    P t_Zero.

  Hypothesis P_Succ :
    forall n,
      P n ->
      P (t_Succ n).

  Hypothesis P_NatRec :
    forall P0 z s n,
      P P0 ->
      P z ->
      P s ->
      P n ->
      P (t_NatRec_ln P0 z s n).

  Hypothesis P_Session : P t_Session.
  Hypothesis P_End : P t_End.
  Hypothesis P_chan : forall e, P (t_chan e).
  
  Hypothesis P_SendTy :
    forall r A S,
      P A ->
      P S ->
      P (t_SendTy r A S).

  Hypothesis P_RecvTy :
    forall r A S,
      P A ->
      P S ->
      P (t_RecvTy r A S).

  Hypothesis P_SendV :
    forall r c v P0,
      P c ->
      P v ->
      P P0 ->
      P (t_SendV r c v P0).

  Hypothesis P_Recv :
    forall r c b,
      P c ->
      P b ->
      P (t_Recv r c b).

  Hypothesis P_Close :
    forall c,
      P c ->
      P (t_Close c).

  Hypothesis P_Wait :
    forall c,
      P c ->
      P (t_Wait c).

  Hypothesis P_Fork :
    forall p,
      P p ->
      P (t_Fork p).

  Hypothesis P_Par :
    forall p q,
      P p ->
      P q ->
      P (t_Par p q).

  Hypothesis P_SelectTy :
    forall r branches,
      Forall (fun '(lbl,b) => P b) branches ->
      P (t_SelectTy r branches).

  Hypothesis P_BranchTy :
    forall r branches,
      Forall (fun '(lbl,b) => P b) branches ->
      P (t_BranchTy r branches).

  Hypothesis P_Select :
    forall r l c P0,
      P c ->
      P P0 ->
      P (t_Select r l c P0).

  Hypothesis P_Branch :
    forall r c branches,
      P c ->
      Forall (fun '(lbl,b) => P b) branches ->
      P (t_Branch r c branches).

Fixpoint term_ln_ind_strong t : P t.
Proof.
  destruct t.

  (* ---------------- Core ---------------- *)

  - apply P_bvar.
  - apply P_fvar.
  - apply P_Type.
  - apply P_Pi; apply term_ln_ind_strong.
  - apply P_Lam; apply term_ln_ind_strong.
  - apply P_App; apply term_ln_ind_strong.
  - apply P_Nat.
  - apply P_Zero.
  - apply P_Succ; apply term_ln_ind_strong.
  - apply P_NatRec; repeat apply term_ln_ind_strong.

  (* ---------------- Session Types ---------------- *)

  - apply P_Session.
  - apply P_End.
  - apply P_SendTy; apply term_ln_ind_strong.
  - apply P_RecvTy; apply term_ln_ind_strong.

  (* ---------------- Session Operations ---------------- *)

  - apply P_chan.
  - apply P_SendV; repeat apply term_ln_ind_strong.
  - apply P_Recv; apply term_ln_ind_strong.
  - apply P_Close; apply term_ln_ind_strong.
  - apply P_Wait; apply term_ln_ind_strong.
  - apply P_Fork; apply term_ln_ind_strong.
  - apply P_Par; apply term_ln_ind_strong.

  (* ---------------- Branching ---------------- *)

  - apply P_SelectTy.
    induction l; constructor; auto.
    destruct a; apply term_ln_ind_strong.

  - apply P_BranchTy.
    induction l; constructor; auto.
    destruct a; apply term_ln_ind_strong.

  - apply P_Select; apply term_ln_ind_strong.

  - apply P_Branch.
    + apply term_ln_ind_strong.
    + induction l; constructor; auto.
      destruct a; apply term_ln_ind_strong.
Qed.

End term_ln_ind_strong.

Lemma cl_larger: forall v k u, 
  Nat.le k u -> 
  lc_rec_ln k v -> 
  lc_rec_ln u v.
Proof. intro t.
       induction t using term_ln_ind_strong; intros.
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
       1: { simpl. easy. }
       3: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       5: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       8: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       4: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            split. apply IHt2 with (k := k). lia. easy.
            apply IHt3 with (k := k). lia. easy.
          }
       3: { simpl in H0. simpl.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       8: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       4: { simpl. simpl in H0.
            apply IHt with (k := k). lia. easy.
          }
       3: { simpl in H0. simpl.
            apply IHt with (k := k). lia. easy.
          }
       2: { simpl in H0. simpl. easy. }
       1: { simpl. easy. }
       1: { simpl in H0. simpl.
            apply IHt with (k := k). lia. easy. }
       3: { simpl.
            split.
            apply IHt with (k := k). lia. simpl in H0.
            simpl in H1. easy.
            rewrite Forall_forall in H.
            simpl in H1.
            destruct H1 as (Ha,H1).
            
            induction branches; intros.
            easy.
            destruct a.
            split.
            specialize(H (s, t0)).
            simpl in H.
            apply H with (k := k). left. easy.
            easy.
            easy.
            apply IHbranches.
            intros.
            destruct x. 
            specialize(H (s0,t1)).
            simpl in H.
            apply H. right. easy.
            easy.
          }
       2: { simpl. simpl in H1.
                  
            induction branches; intros.
            easy.
            destruct a.
            split.
            rewrite Forall_forall in H.
            
            specialize(H (s, t)).
            simpl in H.
            apply H with (k := k). left. easy.
            easy.
            easy.
            apply IHbranches.
            intros.
            rewrite Forall_forall.
            intros.
            rewrite Forall_forall in H.
            destruct x. 
            specialize(H (s0,t0)).
            simpl in H.
            apply H. right. easy.
            easy.
          }
       1: { simpl. simpl in H1.
                  
            induction branches; intros.
            easy.
            destruct a.
            split.
            rewrite Forall_forall in H.
            
            specialize(H (s, t)).
            simpl in H.
            apply H with (k := k). left. easy.
            easy.
            easy.
            apply IHbranches.
            intros.
            rewrite Forall_forall.
            intros.
            rewrite Forall_forall in H.
            destruct x. 
            specialize(H (s0,t0)).
            simpl in H.
            apply H. right. easy.
            easy.
          }
Qed.

Section gtype_ind_strong.

  Variable P : gtype -> Prop.

  (* ---------------- Constructors in Exact Order ---------------- *)

  Hypothesis P_end :
    P g_end.

  Hypothesis P_msg :
    forall p q A G,
      P G ->
      P (g_msg p q A G).

  Hypothesis P_choice :
    forall p q branches,
      Forall (fun '(lbl, G) => P G) branches ->
      P (g_choice p q branches).

  Hypothesis P_natrec :
    forall P0 z s n,
      P z ->
      P s ->
      P (g_natrec P0 z s n).

  Hypothesis P_bvar :
    forall n,
      P (g_bvar n).

  Fixpoint gtype_ind_strong (g : gtype) : P g.
  Proof.
    destruct g.

    (* g_end *)
    - apply P_end.

    (* g_msg *)
    - apply P_msg.
      apply gtype_ind_strong.

    (* g_choice *)
    - apply P_choice.
      induction l; constructor; auto.
      destruct a; apply gtype_ind_strong.

    (* g_natrec *)
    - apply P_natrec.
      + apply gtype_ind_strong.
      + apply gtype_ind_strong.

    (* g_bvar *)
    - apply P_bvar.
  Qed.

End gtype_ind_strong.

Lemma gl_larger: forall v k u, 
  Nat.le k u -> 
  lc_rec_gtype k v -> 
  lc_rec_gtype u v.
Proof. intro t.
       induction t using gtype_ind_strong; intros.
       4:{
       simpl in H0.
       simpl.
       split. apply cl_larger with (k := k); easy.
       split. apply IHt1 with (k := k); easy.
       split. apply IHt2 with (k := k); easy.
       apply cl_larger with (k := k); easy.
       }
       2:{
       simpl in H0. simpl.
       split.
       apply cl_larger with (k := k); easy.
       apply IHt with (k := k); easy.
       }
       1:{
       simpl. easy.
       }
       2:{
       simpl. simpl in H0. lia.
       }
       1:{
       simpl. simpl in H0.
       induction branches; intros.
       easy.
       destruct a.
       split.
       simpl in H1.
       rewrite Forall_forall in H.
       specialize(H (s, g)). simpl in H.
       apply H with (k := k). left. easy. easy. easy.
       apply IHbranches.
       rewrite Forall_forall in H.
       rewrite Forall_forall.
       intros.
       destruct x.
       specialize(H (s0, g0)). simpl in H.
       apply H. right. easy.
       simpl  in H1. easy.
      }
Qed.

Fixpoint project_choice_list
  (r : string)
  (branches : list (string * gtype))
  : option (list (string * term_ln)) :=
  match branches with
  | [] => Some []
  | (l, G') :: bs' =>
      match project r G', project_choice_list r bs' with
      | Some Se, Some Ss => Some ((l, Se) :: Ss)
      | _, _ => None
      end
  end.

Lemma lc_choice_branches :
  forall branches k p q,
    lc_rec_gtype k (g_choice p q branches) ->
    Forall (fun '(_,G') => lc_rec_gtype k G') branches.
Proof. intro br.
       induction br; intros.
       - constructor.
       - constructor. simpl in H.
         destruct a. easy.
         apply IHbr with (p := p) (q := q).
         simpl in H. simpl.
         destruct a. easy. 
Qed.

Fixpoint project_choice_go
  (r : string)
  (branches : list (string * gtype))
  : option (list (string * term_ln)) :=
  match branches with
  | [] => Some []
  | (l, G') :: bs' =>
      match project r G', project_choice_go r bs' with
      | Some Se0, Some Ss => Some ((l, Se0) :: Ss)
      | _, _ => None
      end
  end.

Lemma project_choice_go_some :
  forall branches r Ss,
    project_choice_go r branches = Some Ss ->
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project r G = Some Se)
      branches Ss.
Proof. intro br.
       induction br; intros.
       - simpl in H. inversion H. constructor.
       - simpl in H. destruct a.
         case_eq(project r g); intros.
         + rewrite H0 in H.
           case_eq(project_choice_go r br); intros.
           ++ rewrite H1 in H. inversion H.
              constructor. split; easy.
              apply IHbr. easy.
           ++ rewrite H1 in H. easy.
         + rewrite H0 in H. easy.
Qed.

Lemma project_preserves_lc :
  forall G k r S,
    lc_rec_gtype k G ->
    project r G = Some S ->
    lc_rec_ln k S.
Proof. intro G.
       induction G using gtype_ind_strong; intros.
       4:{
       simpl in H0, H.
       destruct H as (Ha,(Hb,(Hc,Hd))).
       case_eq (project r G1); intros.
       - rewrite H in H0.
         case_eq(project r G2); intros.
         + rewrite H1 in H0.
           inversion H0. subst.
           simpl.
           split. easy. split.
           apply IHG1 with (r := r); easy.
           split.
           split. easy. split. easy.
           apply IHG2 with (r := r); try easy.
           apply gl_larger with (k := k). lia. easy. 
           easy.
         + rewrite H1 in H0. easy.
       - rewrite H in H0. easy.
       }
       1:{
       simpl in H0. inversion H0. easy.
       }
       1:{
       simpl in H, H0.
       case_eq((r =? p)%string); intros.
       - rewrite H1 in H0.
         case_eq(project r G); intros.
         + rewrite H2 in H0.
           inversion H0. subst. simpl. split. easy.
           cbn.
           apply IHG with (r := r). easy.
           easy.
         + rewrite H2 in H0. easy.
       - rewrite H1 in H0.
         case_eq((r =? q)%string); intros.
         + rewrite H2 in H0.
           case_eq(project r G); intros.
           ++ rewrite H3 in H0.
              inversion H0. subst. simpl. split. easy.
              cbn.
              apply IHG with (r := r).
              apply gl_larger with (k := k). lia. easy. 
              easy.
            ++ rewrite H3 in H0. easy.
         + rewrite H2 in H0. 
           apply IHG with (r := r); easy.
        }
      2:{
        simpl in H0. inversion H0. subst.
        simpl. simpl in H. lia.
       }
     1:{
     simpl in H1.
     rewrite <- project_branches_eq in H1.
revert p q H k r S H0 H1.
induction branches as [| [lbl G] rest IH]; intros p q HForall k r S Hlc Hproj.
- simpl in Hproj.
  case_eq((r =? p)%string); intros.
  + rewrite H in Hproj. inversion Hproj. simpl. easy.
  + rewrite H in Hproj.
    case_eq((r =? q)%string); intros.
    ++ rewrite H0 in Hproj. inversion Hproj. easy.
    ++ rewrite H0 in Hproj. easy.
- simpl in Hproj.
    case_eq((r =? p)%string); intros.
    + rewrite H in Hproj.
      case_eq( project r G); intros.
      ++ rewrite H0 in Hproj.
         * case_eq( project_branches r rest); intros.
           rewrite H1 in Hproj.
           simpl in Hproj. inversion Hproj. simpl.
           split.
           inversion HForall.
           subst.
           simpl in Hlc.
           apply H5 with (r := r); easy.
           destruct Hlc as [Hlc_head Hlc_tail].
           clear Hproj H H0 H3 IH.
           revert l H1 Hlc_tail.
           induction rest as [| [lbl' G'] rest' IH]; intros.
           ** simpl in H1. inversion H1. easy.
           ** simpl in H1.
              case_eq(project r G'); intros.
              *** rewrite H in H1.
                  case_eq( project_branches r rest'); intros.
                  +++ rewrite H0 in H1.
                      inversion H1. subst.
                      split.
                      inversion HForall. subst.
                      inversion H5. subst.
                      apply H6 with (r := r); easy.
                      apply IH.
                      rewrite Forall_forall. intros.
                      destruct x.
                      simpl in H2. destruct H2.
                      inversion H2. subst.
                      intros.
                      rewrite Forall_forall in HForall.
                      specialize(HForall (s, g)).
                      apply HForall with (r := r0). simpl. left. easy.
                      easy. easy.
                      intros.

                      rewrite Forall_forall in HForall.
                      specialize(HForall (s, g)).
                      apply HForall with (r := r0). simpl. right. right. easy.
                      easy. easy. easy.
                      easy.
                  +++ rewrite H0 in H1. easy.
              *** rewrite H in H1. easy.
           ** rewrite H1 in Hproj. easy.
      ++ rewrite H0 in Hproj. easy.
    + rewrite H in Hproj.
      rename H into Ha.
      case_eq((r =? q)%string); intros.
      ++ rewrite H in Hproj.
         case_eq( project r G); intros.
         +++ rewrite H0 in Hproj.
             * case_eq( project_branches r rest); intros.
               rewrite H1 in Hproj.
               simpl in Hproj. inversion Hproj. simpl.
               split.
               inversion HForall.
               subst.
               simpl in Hlc.
               apply H5 with (r := r); easy.
               destruct Hlc as [Hlc_head Hlc_tail].
               clear Hproj H H0 H3 IH.
               revert l H1 Hlc_tail.
               induction rest as [| [lbl' G'] rest' IH]; intros.
               ** simpl in H1. inversion H1. easy.
               ** simpl in H1.
                  case_eq(project r G'); intros.
                  *** rewrite H in H1.
                      case_eq( project_branches r rest'); intros.
                      ++++ rewrite H0 in H1.
                          inversion H1. subst.
                          split.
                          inversion HForall. subst.
                          inversion H5. subst.
                          apply H6 with (r := r); easy.
                          apply IH.
                          rewrite Forall_forall. intros.
                          destruct x.
                          simpl in H2. destruct H2.
                          inversion H2. subst.
                          intros.
                          rewrite Forall_forall in HForall.
                          specialize(HForall (s, g)).
                          apply HForall with (r := r0). simpl. left. easy.
                          easy. easy.
                          intros.

                          rewrite Forall_forall in HForall.
                          specialize(HForall (s, g)).
                          apply HForall with (r := r0). simpl. right. right. easy.
                          easy. easy. easy.
                          easy.
                      ++++ rewrite H0 in H1. easy.
                  *** rewrite H in H1. easy.
               ** rewrite H1 in Hproj. easy.
         +++ rewrite H0 in Hproj. easy.
      ++ rename H into Hb.
         rewrite Hb in Hproj.
         case_eq( project r G); intros.
         +++ rewrite H in Hproj.
             * case_eq( project_branches r rest); intros.
               rewrite H0 in Hproj.
               simpl in Hproj.
               case_eq(forallb (fun '(_, S') => term_eqb t S') l); intros.
               ** rewrite H1 in Hproj. inversion Hproj.
                  subst.
                  inversion HForall.
                  subst.
                  simpl in Hlc.
                  destruct Hlc as [Hlc_head Hlc_tail].
                  apply H4 with (r := r); easy.
               ** rewrite H1 in Hproj. easy.
               **  rewrite H0 in Hproj. easy.
         +++ rewrite H in Hproj. easy.
     }
Qed.


Lemma term_eqb_refl :
  forall t,
    term_eqb t t = true.
Proof.
  induction t using term_ln_ind_strong; simpl.

  (* t_bvar *)
  - rewrite Nat.eqb_refl.
    reflexivity.

  (* t_fvar *)
  - rewrite String.eqb_refl.
    reflexivity.

  (* t_Type *)
  - rewrite Nat.eqb_refl.
    reflexivity.

  (* t_Pi *)
  - rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_Lam *)
  - rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_App *)
  - rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_Nat *)
  - reflexivity.

  (* t_Zero *)
  - reflexivity.

  (* t_Succ *)
  - rewrite IHt.
    reflexivity.

  (* t_NatRec_ln *)
  - rewrite IHt1.
    rewrite IHt2.
    rewrite IHt3.
    rewrite IHt4.
    reflexivity.

  (* t_Session *)
  - reflexivity.

  (* t_End *)
  - reflexivity.

  (* t_SendTy *)
  - destruct e. rewrite String.eqb_refl. rewrite String.eqb_refl. 
(*     rewrite IHt1.
    rewrite IHt2. *)
    reflexivity.

  (* t_RecvTy *)
  - rewrite String.eqb_refl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_chan *)
  - rewrite String.eqb_refl.
    rewrite IHt1, IHt2.
    reflexivity.

  (* t_SendV *)
  - rewrite String.eqb_refl.
    rewrite IHt1.
    rewrite IHt2.
    rewrite IHt3.
    reflexivity.

  (* t_Recv *)
  - rewrite String.eqb_refl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_Close *)
  - rewrite IHt.
    reflexivity.

  (* t_Wait *)
  - rewrite IHt.
    reflexivity.

  (* t_Fork *)
  - rewrite IHt.
    reflexivity.

  (* t_Par *)
  - rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_SelectTy *)
  - rewrite String.eqb_refl.
    simpl.
    induction branches; intros.
    + reflexivity.
    + simpl.
      destruct a as [lbl Se].
      rewrite String.eqb_refl.
      rewrite IHbranches.
      simpl.
      rewrite Forall_forall in H.
      specialize(H (lbl, Se)).
      assert(In (lbl, Se) ((lbl, Se) :: branches)). left. easy.
      apply H in H0.
      rewrite H0. easy.
      rewrite Forall_forall. intros.
      destruct x.
      rewrite Forall_forall in H.
      specialize(H (s, t)).
      apply H. simpl. right. easy.

  (* t_BranchTy *)
  - rewrite String.eqb_refl. simpl.
    induction branches; intros.
    + reflexivity.
    + simpl.
      destruct a as [lbl Se].
      rewrite String.eqb_refl.
      rewrite IHbranches.
      simpl.
      rewrite Forall_forall in H.
      specialize(H (lbl, Se)).
      assert(In (lbl, Se) ((lbl, Se) :: branches)). left. easy.
      apply H in H0.
      rewrite H0. easy.
      rewrite Forall_forall. intros.
      destruct x.
      rewrite Forall_forall in H.
      specialize(H (s, t)).
      apply H. simpl. right. easy.

  (* t_Select *)
  - rewrite String.eqb_refl.
    rewrite String.eqb_refl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.

  (* t_Branch *)
  - rewrite String.eqb_refl.
    rewrite IHt. simpl.
    induction branches; intros.
    + reflexivity.
    + simpl.
      destruct a as [lbl Se].
      rewrite String.eqb_refl.
      rewrite IHbranches.
      simpl.
      rewrite Forall_forall in H.
      specialize(H (lbl, Se)).
      assert(In (lbl, Se) ((lbl, Se) :: branches)). left. easy.
      apply H in H0.
      rewrite H0. easy.
      rewrite Forall_forall. intros.
      destruct x.
      rewrite Forall_forall in H.
      specialize(H (s, t0)).
      apply H. simpl. right. easy.
Qed.


Lemma projection_total_wf :
  forall G,
    gtype_wf G ->
    projection_total G.
Proof.
  intros G Hwf.
  induction Hwf; unfold projection_total; intros.
  - simpl. exists t_End. easy.
  - simpl. exists  (t_bvar n). easy.
  - simpl.
    case_eq( (r =? p)%string); intros.
    + rewrite String.eqb_eq in H0. subst.
      unfold projection_total in IHHwf.
      destruct (IHHwf p) as (S,Ha).
      exists (t_SendTy q A S).
      rewrite Ha. easy.
    + case_eq( (r =? q)%string); intros.
      ++ rewrite String.eqb_eq in H1. subst.
         unfold projection_total in IHHwf.
         destruct (IHHwf q) as (S,Ha).
         exists (t_RecvTy p A S).
         rewrite Ha. easy.
      ++ easy.
  - cbn.
    case_eq((r =? p)%string); intros.
    + rewrite String.eqb_eq in H5. subst.
      clear H0.
      revert H2 H3 H4.
      induction branches; intros.
      ++ simpl. exists (t_SelectTy q []); easy.
      ++ assert(forall (lbl : string) (G : gtype), In (lbl, G) branches -> gtype_wf G).
         intros.
         apply H2 with (lbl := lbl).
         simpl. right. easy.
         assert((forall (lbl : string) (G : gtype), In (lbl, G) branches -> projection_total G)).
         intros. apply H3 with (lbl := lbl). simpl. right. easy.
         assert(NoDup (map fst branches)).
         simpl in H1. apply NoDup_cons_iff in H1. easy.
         assert(third_party_consistent p q branches).
         { apply third_party_tail with (b := a). easy. }
         
         specialize(IHbranches H6 H0 H5 H7).
         destruct IHbranches as (S,Ha).
         destruct a.
         destruct((fix go (bs : list (string * gtype)) : option (list (string * term_ln)) :=
                match bs with
                | [] => Some []
                | (l, G') :: bs' =>
                    match project p G' with
                    | Some Se => match go bs' with
                                 | Some Ss => Some ((l, Se) :: Ss)
                                 | None => None
                                 end
                    | None => None
                    end
                end)
               branches) as [Ss |] eqn:Hgo. simpl in Ha.
         destruct (H3 s g (or_introl eq_refl) p) as [Se Hproj].
         exists (t_SelectTy q ((s,Se)::Ss)).
         rewrite Hproj. simpl. easy.
         simpl in Ha. easy.
     + rename H5 into HN1.
       case_eq((r =? q)%string); intros.
       ++ rewrite String.eqb_eq in H5. subst.
          clear H0.
          revert H2 H3 H4.
          induction branches; intros.
          ** simpl. exists (t_BranchTy p []); easy.
          ** assert(forall (lbl : string) (G : gtype), In (lbl, G) branches -> gtype_wf G).
             intros.
             apply H2 with (lbl := lbl).
             simpl. right. easy.
             assert((forall (lbl : string) (G : gtype), In (lbl, G) branches -> projection_total G)).
             intros. apply H3 with (lbl := lbl). simpl. right. easy.
             assert(NoDup (map fst branches)).
             simpl in H1. apply NoDup_cons_iff in H1. easy.
             assert(third_party_consistent p q branches).
             { apply third_party_tail with (b := a). easy. }
             
             specialize(IHbranches H6 H0 H5 H7).
             destruct IHbranches as (S,Ha).
             destruct a.
             destruct(  ((fix go (bs : list (string * gtype)) : option (list (string * term_ln)) :=
                match bs with
                | [] => Some []
                | (l, G') :: bs' =>
                    match project q G' with
                    | Some Se => match go bs' with
                                 | Some Ss => Some ((l, Se) :: Ss)
                                 | None => None
                                 end
                    | None => None
                    end
                end))) as [Ss |] eqn:Hgo. simpl in Ha.
             destruct (H3 s g (or_introl eq_refl) q) as [Se Hproj].
             exists (t_BranchTy p ((s,Se)::Ss)).
             rewrite Hproj. simpl. easy.
             simpl in Ha. easy.
       ++ revert H2 H3 H4.
          induction branches; intros.
          ** easy.
          ** destruct branches, a.
             destruct (H3 s g (or_introl eq_refl) r) as [Se Hproj].
             rewrite Hproj.
             cbn. exists Se. easy.
             destruct p0.
          
             assert((forall (lbl : string) (G : gtype), In (lbl, G) ((s0, g0) :: branches) -> gtype_wf G) ).
             intros.
             apply H2 with (lbl := lbl).
             simpl. right. easy.
             assert((forall (lbl : string) (G : gtype), In (lbl, G) ((s0, g0) :: branches) -> projection_total G)).
             intros. apply H3 with (lbl := lbl). simpl. right. easy.
             assert(NoDup (map fst ((s0, g0) :: branches)) ).
             simpl in H1. apply NoDup_cons_iff in H1. simpl. easy.
             assert(third_party_consistent p q ((s0, g0) :: branches)).
             { apply third_party_tail with (b := (s, g)). easy. }
             assert((s0, g0) :: branches <> []). easy.
             specialize(IHbranches H10 H8 H6 H7 H9).
             destruct IHbranches as (S,Ha).
             
             destruct(
              (fix go (bs : list (string * gtype)) : option (list (string * term_ln)) :=
             match bs with
             | [] => Some []
             | (l, G') :: bs' =>
                 match project r G' with
                 | Some Se0 => match go bs' with
                               | Some Ss => Some ((l, Se0) :: Ss)
                               | None => None
                               end
                 | None => None
                 end
             end)
             ) as [Ss |] eqn:Hgo.
             destruct (H3 s g (or_introl eq_refl) r) as [Se Hproj].
             rewrite Hproj. simpl.
             specialize (H3 s0 g0).
             assert(In (s0, g0) ((s, g) :: (s0, g0) :: branches)). right. left. easy.
             apply H3 in H11.
             destruct (H11 r) as [Se2 Hproj2].
             rewrite Hproj2.
             rewrite Hproj2 in Ha.
             simpl in Ha.
             cbn.
             unfold third_party_consistent in H4.
             simpl in H4.
             apply String.eqb_neq in HN1, H5.
             specialize(H4 r HN1 H5).
             rewrite Hproj in H4.
             specialize(H4 s0 g0).
             assert((s0, g0) = (s0, g0) \/ In (s0, g0) branches). left. easy.
             apply H4 in H12. rewrite H12 in Hproj2.
             inversion Hproj2. subst.
             exists Se2.
             case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss); intros.
             simpl.
             rewrite term_eqb_refl. simpl. easy. 
             rewrite H13 in Ha. easy.
             destruct (project r g0); easy.
  - cbn. unfold projection_total in *.
    destruct(IHHwf1 r) as (S1,Ha).
    destruct(IHHwf2 r) as (S2,Hb).
    rewrite Ha, Hb.
    simpl.
    exists (t_NatRec_ln P S1 (t_Lam t_Nat (t_Lam t_Session S2)) n).
    easy.
Qed.


