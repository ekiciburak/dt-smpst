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

(*   | t_Session   : term_ln *)
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
| t_SBind :
    term_ln ->      (* payload type A *)
    term_ln ->      (* continuation S, binds one variable *)
    term_ln.


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

(*   | t_Session =>
      t_Session
 *)
  | t_End =>
      t_End

  | t_SendTy r A Se =>
      t_SendTy r (open_rec_ln k u A)
                 (open_rec_ln (S k) u Se)

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

| t_SBind A body =>
    t_SBind (open_rec_ln k u A)
            (open_rec_ln (S k) u body)

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

(*   | t_Session =>
      t_Session
 *)
  | t_End =>
      t_End

  | t_SendTy r A Se =>
      t_SendTy r (close_rec_ln k x A)
                 (close_rec_ln (S k) x Se)

  | t_RecvTy r A Se =>
      t_RecvTy r
        (close_rec_ln k x A)
        (close_rec_ln (S k) x Se)


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

| t_SBind A body =>
    t_SBind (close_rec_ln k x A)
            (close_rec_ln (S k) x body)
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

(*   | t_Session =>
      t_Session *)

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

| t_SBind A body =>
    t_SBind (subst_ln x u A)
            (subst_ln x u body)

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

(*   | t_Session =>
      True *)

  | t_End =>
      True

  | t_SendTy r A Se =>
      lc_rec_ln k A /\
      lc_rec_ln (S k) Se

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

| t_SBind A Se =>
    lc_rec_ln k A /\
    lc_rec_ln (S k) Se
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

(*   | t_Session =>
      True
 *)
  | t_End =>
      True

  | t_SendTy r A Se =>
      notin_bvar k A /\
      notin_bvar (S k) Se

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

  | t_SBind A b =>
      notin_bvar k A /\
      notin_bvar (S k) b
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

(* | par_conv_Session :
    par_conv_n_ln t_Session t_Session *)

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

| par_conv_SBind :
    forall A A' S S',
      par_conv_n_ln A A' ->
      par_conv_n_ln S S' ->
      par_conv_n_ln
        (t_SBind A S)
        (t_SBind A' S')
        
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
    gtype      (* continuation binds one term variable *)
    -> gtype
| g_choice :
    string -> string ->
    list (string * gtype)
    -> gtype
| g_natrec :
    term_ln    (* scrutinee *)
    -> gtype   (* zero branch *)
    -> gtype   (* successor branch, binds predecessor *)
    -> term_ln    (* scrutinee *)
    -> gtype
| g_bvar : nat -> gtype.

Fixpoint open_rec_gtype
  (k : nat)
  (u : term_ln)
  (G : gtype)
  : gtype :=
  match G with

  | g_end =>
      g_end

  | g_bvar n =>
      g_bvar n

  | g_msg p q A G' =>
      g_msg p q
        (open_rec_ln k u A)
        (open_rec_gtype (S k) u G')

  | g_choice p q branches =>
      g_choice p q
        (map (fun '(lbl, G') =>
                (lbl, open_rec_gtype k u G'))
             branches)

  | g_natrec P G0 Gs n =>
      g_natrec
        (open_rec_ln k u P)
        (open_rec_gtype k u G0)
        (open_rec_gtype (S k) u Gs)
        (open_rec_ln k u n)
  end.
  
Definition open_gtype := open_rec_gtype 0.

Fixpoint subst_term_gtype
  (x : string)
  (u : term_ln)
  (G : gtype)
  : gtype :=
  match G with

  | g_end =>
      g_end

  | g_bvar n =>
      g_bvar n

  | g_msg p q A G' =>
      g_msg p q
        (subst_ln x u A)
        (subst_term_gtype x u G')

  | g_choice p q branches =>
      g_choice p q
        (map (fun '(lbl, G') =>
                (lbl, subst_term_gtype x u G'))
             branches)

  | g_natrec P G0 Gs n =>
      g_natrec
        (subst_ln x u P)
        (subst_term_gtype x u G0)
        (subst_term_gtype x u Gs)
        (subst_ln x u n)
  end.

Fixpoint lc_rec_gtype
  (k : nat)
  (G : gtype)
  : Prop :=
  match G with

  | g_end =>
      True

  | g_bvar n =>
      n < k

  | g_msg _ _ A G' =>
      lc_rec_ln k A /\
      lc_rec_gtype (S k) G'

  | g_choice _ _ branches =>
      let fix go bs :=
          match bs with
          | [] => True
          | (_, G') :: bs' =>
              lc_rec_gtype k G' /\ go bs'
          end
      in go branches

  | g_natrec P G0 Gs n =>
      lc_rec_ln k P /\
      lc_rec_gtype k G0 /\
      lc_rec_gtype (S k) Gs /\
      lc_rec_ln k n
  end.

Definition lc_gtype := lc_rec_gtype 0.

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

(*     | t_Session, t_Session => true *)
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

    | t_SBind A1 b1, t_SBind A2 b2 =>
        term_eqb A1 A2 && term_eqb b1 b2
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
(*   | t_Session => true *)
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
  | t_SBind A Se =>
      andb (local_session_wfb A)
           (local_session_wfb Se) 
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
       option_map (fun Se => t_SBind A Se) (project r G') (*  project r G' *)


  | g_natrec P z s n =>
    match project r z, project r s with
    | Some Sz, Some Ss =>
        Some
          (t_NatRec_ln
             P
             Sz
             (t_Lam t_Nat Ss)
             n)
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

Definition sub_lctx (Δz Δ : lctx) : Prop :=
  forall e T,
    LM.find e Δz = Some T ->
    LM.find e Δ = Some T.

Definition unfold_step P z step x :=
  open_ln
    (open_ln step (t_fvar x))
    (t_NatRec_ln P z step (t_fvar x)).

Definition map_open_ln (u : term_ln) (Δ : lctx) : lctx :=
  LM.fold (fun e T acc => LM.add e (open_ln T u) acc) Δ empty_lctx.

Inductive has_type_ln: ictx -> lctx -> term_ln -> term_ln -> Prop :=

(* ========================= *)
(* Variables                 *)
(* ========================= *)
  (* variable *)
| ty_var : forall Γ Δ x T,
    lookup_ln Γ x = Some T ->
    has_type_ln Γ Δ (t_fvar x) T

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

(* application rule: argument must be pure; open the function's captured Δ with the arg *)
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

(*       sub_lctx Δz Δ -> *)

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
      
      has_type_ln Γ Δ z (t_App P t_Zero) ->

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

| ty_End :
    forall Γ,
      has_type_ln Γ empty_lctx t_End (t_Type 0)

| ty_SendTy :
    forall Γ r A S i,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      has_type_ln Γ empty_lctx S (t_Type 0) ->
      has_type_ln Γ empty_lctx
        (t_SendTy r A S)
        (t_Type 0)

| ty_RecvTy :
    forall Γ r A S i L,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln ((x,A)::Γ) empty_lctx
           (open_ln S (t_fvar x))
           (t_Type 0)) ->
      has_type_ln Γ empty_lctx
        (t_RecvTy r A S)
        (t_Type 0)

(* typing for select/branch session *types* (they inhabit t_Session) *)

| ty_SelectTy :
    forall Γ r branches,
      local_session_wf (t_SelectTy r branches) ->
      (forall lbl Se,
         In (lbl, Se) branches ->
         has_type_ln Γ empty_lctx Se (t_Type 0)) ->
      has_type_ln Γ empty_lctx
        (t_SelectTy r branches)
        (t_Type 0)

| ty_BranchTy :
    forall Γ r branches,
      local_session_wf (t_BranchTy r branches) ->
      (forall lbl Se,
         In (lbl, Se) branches ->
         has_type_ln Γ empty_lctx Se (t_Type 0)) ->
      has_type_ln Γ empty_lctx
        (t_BranchTy r branches)
        (t_Type 0)

(* ========================= *)
(* Session Terms             *)
(* ========================= *)

| ty_SendV : forall Γ Δ s p q A S v P T, 
    LM.find (s,p) Δ = Some T ->
    (* check the *stored* channel type T is a send-type *)
    convertible_n_par_ln T (t_SendTy q A S) ->
    has_type_ln Γ empty_lctx v A ->
    (* continuation type depends on v: instantiate S with v *)
    has_type_ln Γ (LM.add (s,p) (open_ln S v) Δ) P t_End ->
    has_type_ln Γ Δ (t_SendV q (t_chan (s,p)) v P) t_End

| ty_Recv : forall Γ Δ s p q A S body T L,
    LM.find (s,p) Δ = Some T ->
    convertible_n_par_ln T (t_RecvTy q A S) ->
    (forall x, ~ In x L -> ~ In x (map fst Γ) ->
       has_type_ln ((x,A)::Γ) (LM.add (s,p) (open_ln S (t_fvar x)) Δ)
                   (open_ln body (t_fvar x)) t_End) ->
    has_type_ln Γ Δ (t_Recv q (t_chan (s,p)) body) t_End

| ty_Select :
    forall Γ Δ s p q T branches l S local_cont,

      LM.find (s,p) Δ = Some T ->

      convertible_n_par_ln
        T
        (t_SelectTy q branches) ->

      In (l, S) branches ->

      has_type_ln Γ
        (LM.add (s,p) S (LM.remove (s,p) Δ))
        local_cont
        t_End ->

      has_type_ln Γ Δ
        (t_Select q l (t_chan (s,p)) local_cont)
        t_End


| ty_Branch :
    forall Γ Δ s p q T branches local_branches,

      LM.find (s,q) Δ = Some T ->

      convertible_n_par_ln
        T
        (t_BranchTy p branches) ->

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
    forall Γ Δ s r T,

      LM.find (s,r) Δ = Some T ->

      convertible_n_par_ln T t_End ->

      has_type_ln Γ
        Δ
        (t_Close (t_chan (s,r)))
        t_End

| ty_Par :
    forall Γ Δ1 Δ2 P Q,
      disjoint Δ1 Δ2 ->
      has_type_ln Γ Δ1 P t_End ->
      has_type_ln Γ Δ2 Q t_End ->
      has_type_ln Γ (merge Δ1 Δ2)
        (t_Par P Q)
        t_End

| ty_SBind :
    forall Γ A S i L,
      has_type_ln Γ empty_lctx A (t_Type i) ->
      (forall x,
         ~ In x L ->
         ~ In x (map fst Γ) ->
         has_type_ln ((x,A)::Γ) empty_lctx
           (open_ln S (t_fvar x))
           (t_Type 0)) ->
      has_type_ln Γ empty_lctx
        (t_SBind A S)
        (t_Type 0)

| ty_conv :
    forall Γ Δ t A B,
      has_type_ln Γ Δ t A ->
      convertible_n_par_ln A B ->
      has_type_ln Γ Δ t B.

(* ====== Configuration semantics (no step_natrec) ====== *)

(* configuration: linear context Δ and process P *)
Inductive config : Type := 
  | cfg : lctx -> term_ln -> config.

(* open_local_proj: when we are instantiating a projected local session
   type with a concrete value v, this function traverses the local type
   and replaces occurrences of the special binder node t_SBind by open_ln *)
Fixpoint open_local_proj (S v : term_ln) : term_ln :=
  match S with

  (* -------- session-type constructors: recurse into the continuation ----- *)
  | t_SendTy r A Se =>
      t_SendTy r (open_local_proj A v) (open_local_proj Se v)

  | t_RecvTy r A Se =>
      t_RecvTy r (open_local_proj A v) (open_local_proj Se v)

  (* t_SBind: this is the binder node that we SHOULD instantiate now.
     We apply open_ln once to substitute v for the binder.  We do NOT
     recursively call open_local_proj on the result to avoid double-opening
     the same binder. If that result still contains other (different)
     SBind nodes, they correspond to other bindings and should remain. *)
  | t_SBind A Se =>
      open_ln Se v

  (* branches: map over second component (the continuation) recursively *)
  | t_SelectTy r branches =>
      t_SelectTy r (map (fun '(lbl, Se) => (lbl, open_local_proj Se v)) branches)

  | t_BranchTy r branches =>
      t_BranchTy r (map (fun '(lbl, Se) => (lbl, open_local_proj Se v)) branches)

  (* -------- type-level structure: recurse into subterms -------------- *)
  | t_Pi A B =>
      t_Pi (open_local_proj A v) (open_local_proj B v)

  | t_Lam A b =>
      t_Lam (open_local_proj A v) (open_local_proj b v)

  | t_App f a =>
      t_App (open_local_proj f v) (open_local_proj a v)

  | t_NatRec_ln P z s n =>
      t_NatRec_ln (open_local_proj P v)
                  (open_local_proj z v)
                  (open_local_proj s v)
                  (open_local_proj n v)

  | t_Succ n =>
      t_Succ (open_local_proj n v)

  (* -------- base / atomic constructors: leave as-is --------------- *)
  | t_Type i => t_Type i
  | t_Nat => t_Nat
  | t_Zero => t_Zero
  | t_bvar n => t_bvar n
  | t_fvar x => t_fvar x
  | t_chan c => t_chan c
  | t_End => t_End

  (* -------- process-level terms (we conservatively recurse) ------- *)
  (* If you prefer to *not* touch process-level terms here, you may
     change these cases to return the original term unchanged. *)
  | t_SendV r c val P =>
      t_SendV r (open_local_proj c v) (open_local_proj val v) (open_local_proj P v)

  | t_Recv r c body =>
      t_Recv r (open_local_proj c v) (open_local_proj body v)

  | t_Close c =>
      t_Close (open_local_proj c v)

  | t_Wait c =>
      t_Wait (open_local_proj c v)

  | t_Fork p =>
      t_Fork (open_local_proj p v)

  | t_Par p q =>
      t_Par (open_local_proj p v) (open_local_proj q v)

  | t_Select r l c P =>
      t_Select r l (open_local_proj c v) (open_local_proj P v)

  | t_Branch r c bs =>
      t_Branch r (open_local_proj c v)
                (map (fun '(lbl, body) => (lbl, open_local_proj body v)) bs)

  end.

Definition advance_session
  (s r1 r2 : string)
  (v : term_ln)
  (S1 S2 : term_ln)
  (Δ : lctx)
  : lctx :=
  LM.mapi
    (fun (e : endpoint) T =>
       match e with
       | (s', r) =>
           if String.eqb s s' then
             if String.eqb r r1 then open_ln S1 v
             else if String.eqb r r2 then open_ln S2 v
             else open_local_proj T v
           else T
       end)
    Δ.

(* New: step_cfg_on indexed by session name s *)
Inductive step_cfg_on (s : string) : config -> config -> Prop :=

(* ================================================= *)
(* Message Communication (session s)                 *)
(* ================================================= *)

| step_comm_on :
    forall Δ r1 r2
           T1 T2
           A S1 S2
           v P body
           Δ',

      LM.find (s, r1) Δ = Some T1 ->
      LM.find (s, r2) Δ = Some T2 ->

      convertible_n_par_ln
        T1 (t_SendTy r2 A S1) ->

      convertible_n_par_ln
        T2 (t_RecvTy r1 A S2) ->

      value_ln v ->

      Δ' =
        advance_session s r1 r2 v S1 S2 Δ ->
(*       Δ' =
        LM.add (s, r1) (open_ln S1 v)
        (LM.add (s, r2) (open_ln S2 v)
          (LM.remove (s, r1)
            (LM.remove (s, r2) Δ))) -> *)

      step_cfg_on s
        (cfg Δ
           (t_Par
              (t_SendV r2 (t_chan (s, r1)) v P)
              (t_Recv  r1 (t_chan (s, r2)) body)))
        (cfg Δ'
           (t_Par
              P
              (open_ln body v)))

(* ================================================= *)
(* Labelled Choice Communication (session s)         *)
(* ================================================= *)

| step_choice_on :
    forall Δ p q
           T1 T2
           branches
           l S
           P local_branches body_l
           Δ',

      LM.find (s, p) Δ = Some T1 ->
      LM.find (s, q) Δ = Some T2 ->

      convertible_n_par_ln
        T1 (t_SelectTy q branches) ->

      convertible_n_par_ln
        T2 (t_BranchTy p branches) ->

      lookup_branch l branches = Some S ->
      lookup_branch l local_branches = Some body_l ->

      Δ' =
        LM.add (s, p) S
        (LM.add (s, q) S
          (LM.remove (s, p)
            (LM.remove (s, q) Δ))) ->

      step_cfg_on s
        (cfg Δ
           (t_Par
              (t_Select q l (t_chan (s, p)) P)
              (t_Branch p (t_chan (s, q)) local_branches)))
        (cfg Δ'
           (t_Par
              P
              body_l)).

(* well-typed configuration: P has type t_End under Δ *)
Definition has_type_cfg (Γ : ictx) (c : config) : Prop :=
  match c with
  | cfg Δ P => has_type_ln Γ Δ P t_End
  end.

Definition step (s : string) (G : gtype)
  (acc : lctx) (r : string) : lctx :=
  match project r G with
  | Some ST => LM.add (s,r) ST acc
  | None => acc
  end.

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

Definition init_session
  (s : string)
  (G : gtype)
  : lctx :=
  fold_left (step s G) (roles G) empty_lctx.


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

(* Definition init_session
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
 *)

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

(* Definition coherent_session (s : string) (Δ : lctx) : Prop :=
  exists G,
    gtype_wf G /\
    forall r S,
      LM.find (s,r) Δ = Some S ->
      project r G = Some S. *)

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

(*   Hypothesis P_Session : P t_Session. *)
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

  Hypothesis P_SBind :
    forall A b,
      P A ->
      P b ->
      P (t_SBind A b).

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

(*   - apply P_Session. *)
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
  - apply P_SBind; apply term_ln_ind_strong.
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
            apply IHt2 with (k := S k). lia. easy.
          }
       4: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       7: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       3: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            split. apply IHt2 with (k := k). lia. easy.
            apply IHt3 with (k := k). lia. easy.
          }
       2: { simpl in H0. simpl.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := S k). lia. easy.
          }
       7: { simpl. simpl in H0.
            split. apply IHt1 with (k := k). lia. easy.
            apply IHt2 with (k := k). lia. easy.
          }
       3: { simpl. simpl in H0.
            apply IHt with (k := k). lia. easy.
          }
       2: { simpl in H0. simpl.
            apply IHt with (k := k). lia. easy.
          }
       1: { simpl in H0. simpl. easy. }
(*        1: { simpl. easy. } *)
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
       1: { simpl. simpl in H0.
            split.
            apply IHt1 with (k := k); easy.
            apply IHt2 with (k := S k). lia. easy.
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
       split. apply IHt2 with (k := S k). lia. easy.
       apply cl_larger with (k := k); easy.
       }
       2:{
       simpl in H0. simpl.
       split.
       apply cl_larger with (k := k); easy.
       apply IHt with (k := S k); try lia. easy.
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

Fixpoint depth_of_projection
  (G : gtype)
  (r : string)
  (k : nat) : nat :=
  match G with
  | g_end => k

  | g_bvar _ => k

  | g_msg p q A G' =>
      if String.eqb r p then k
      else if String.eqb r q then k
      else depth_of_projection G' r (S k)

  | g_natrec _ z _ _ =>
      k

  | g_choice _ _ _ =>
      k
  end.

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
           split. easy. 
           apply IHG2 with (r := r); try easy.
          (*  apply gl_larger with (k := S k). lia.  *) easy. 
           (* easy. *)
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
           apply IHG with (r := r).
           apply gl_larger with (k := S k). lia. easy. 
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
              apply gl_larger with (k := S k). lia. easy. 
              easy.
            ++ rewrite H3 in H0. easy.
         + rewrite H2 in H0.
           unfold option_map in H0.
           case_eq(project r G); intros.
           rewrite H3 in H0. inversion H0.
           simpl. split. easy.
           apply IHG with (r := r); try easy.
           rewrite H3 in H0.
           easy.
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


(*   (* t_Session *)
  - reflexivity. *)

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
  - rewrite IHt1, IHt2. easy.
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
      ++ unfold option_map.
         unfold projection_total in *.
         specialize(IHHwf r).
         destruct IHHwf. rewrite H2.
         exists (t_SBind A x). easy.
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
    exists (t_NatRec_ln P S1 (t_Lam t_Nat S2) n).
    easy.
Qed.

Fixpoint lookup_gbranch
  (l : string)
  (bs : list (string * gtype))
  : option gtype :=
  match bs with
  | [] => None
  | (l0, G) :: bs' =>
      if String.eqb l l0
      then Some G
      else lookup_gbranch l bs'
  end.

(* Inductive step_gtype : gtype -> gtype -> Prop :=

| g_step_msg :
    forall p q A G',
      step_gtype (g_msg p q A G') G'

| g_step_choice :
    forall p q branches l G',
      lookup_gbranch l branches = Some G' ->
      step_gtype (g_choice p q branches) G'. *)

(* Definition coherent_session (s : string) (Δ : lctx) : Prop :=
  exists G,
    gtype_wf G /\
    forall r T,
      LM.find (s,r) Δ = Some T ->
      exists S,
        project r G = Some S /\
        convertible_n_par_ln T S. *)



Require Import Coq.FSets.FMapFacts.
Module LMFacts := FMapFacts.Facts(LM).

Lemma fold_preserves_other_key :
  forall rs G s r  acc,
    ~ In r rs ->
    LM.find (s,r)
      (fold_left (step s G) rs acc)
    =
    LM.find (s,r) acc.
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn.
         simpl in H. unfold not in H.
          (* First extract the two useful facts from H *)
          assert (Hneq : r <> a).
          {
            intro Heq.
            apply H.
            left.
            symmetry.
            exact Heq.
          }

          assert (Hnotin : ~ In r l).
          {
            intro Hin.
            apply H.
            right.
            exact Hin.
          }

          (* Now apply the IH to the fold over l *)
          rewrite IHl.
          + (* Now goal reduces to showing step does not affect (s,r) *)
            unfold step.
            destruct (project a G) eqn:Hproj.

            * (* project a G = Some ST *)
              apply LMFacts.add_neq_o.
              intros Heq.
              inversion Heq.
              subst. simpl in H1. subst.
              contradiction.

            * (* project a G = None *)
              reflexivity.

          + (* discharge IH premise *)
            exact Hnotin.
Qed.

Lemma existsb_eqb_false_notin :
  forall xs x,
    existsb (String.eqb x) xs = false ->
    ~ In x xs.
Proof. intro l.
       induction l; intros.
       - easy.
       - simpl. simpl in IHl. simpl in H.
         apply orb_false_iff in H.
         destruct H as (Ha, Hb).
         unfold not. intros.
         destruct H.
         + subst. rewrite String.eqb_refl in Ha. easy.
         + apply IHl in Hb. easy. 
Qed.

Lemma not_in_propa: forall l a, ~ In a l -> ~ In a (remove_dups l).
Proof. intro l.
       induction l; intros.
       - simpl. easy.
       - simpl. simpl in H.
         unfold not. intros.
         case_eq(existsb (String.eqb a) l); intros.
         + unfold not in H.
           assert(a = a0 -> False).
           { intros. apply H. left. easy. }
           assert( In a0 l -> False).
           { intros. apply H. right. easy. }
           apply IHl in H3.
           apply H3. rewrite H1 in H0. easy.
         + rewrite H1 in H0.
           apply existsb_eqb_false_notin in H1.
           simpl in H0.
           assert( In a0 l -> False).
           { intros. apply H. right. easy. }
           apply IHl in H2.
           destruct H0.
           apply H. subst. left. easy.
           easy.
Qed.

Lemma nd_rd: forall l, NoDup (remove_dups l).
Proof. induction l; intros.
       - simpl. constructor.
       - simpl.
         case_eq(existsb (String.eqb a) l); intros.
         + apply existsb_exists in H.
           destruct H as (x,(Ha,Hb)).
           easy.
         + constructor; try easy.
           apply existsb_eqb_false_notin in H.
           apply not_in_propa. easy.
Qed.

Lemma roles_NoDup :
  forall G, NoDup (roles G).
Proof.
  intros G.
  apply nd_rd.
Qed.

Lemma fold_left_preserves_find :
  forall rs G s r acc1 acc2,
    LM.find (s,r) acc1 = LM.find (s,r) acc2 ->
    LM.find (s,r)
      (fold_left (step s G) rs acc1)
    =
    LM.find (s,r)
      (fold_left (step s G) rs acc2).
Proof. intro l.
       induction l; intros.
       - cbn. easy.
       - cbn. 
        unfold step at 2.
        unfold step at 3.
        destruct (project a G) eqn:Hproj.

        + (* project a G = Some ST *)

          simpl.

          destruct (String.eqb r a) eqn:Heq.

          * (* r = a *)
            apply String.eqb_eq in Heq.
            subst.
            rewrite IHl with (acc2 := (LM.add (s, a) t acc2)). easy.
            
            (* both sides become Some ST *)
            rewrite LMFacts.add_eq_o.
            rewrite LMFacts.add_eq_o.
            easy. easy. easy.
          * (* r <> a *)
            apply String.eqb_neq in Heq.
            rewrite IHl with (acc2 := (LM.add (s, a) t acc2)). easy.
            rewrite LMFacts.add_neq_o.
            rewrite LMFacts.add_neq_o.
            easy.
            unfold not. intros.
            destruct H0. simpl in H1. subst. easy.
            unfold not. intros.
            destruct H0. simpl in H1. subst. easy.
        + rewrite IHl with (acc2 := acc2); easy.
Qed.

Lemma fold_init_session_find :
  forall rs G s r S,
    In r rs ->
    NoDup rs ->
    project r G = Some S ->
    LM.find (s,r)
      (fold_left (step s G) rs empty_lctx)
    = Some S.
Proof. intro l.
       induction l; intros.
       - simpl in H. easy.
       - simpl. simpl in H.
         destruct H.
         + subst.
           unfold step at 2. rewrite H1.
           inversion H0. subst.
           rewrite fold_preserves_other_key; try easy.
           rewrite LMFacts.add_eq_o. easy. easy.
         + inversion H0. subst.
           specialize(IHl G s r S H H5 H1).
           rewrite <- IHl.
           apply fold_left_preserves_find.
           unfold step.
           assert (Hneq : r <> a).
           {
             intro Heq.
             subst.
             apply H4.
             exact H.
           }
           destruct (project a G).
           ++ apply LMFacts.add_neq_o.
              unfold not. intros. 
              destruct H2. simpl in H3. subst. easy.
           ++ cbn. easy.
Qed.

Lemma init_session_find :
  forall G s r S,
    In r (roles G) ->
    project r G = Some S ->
    LM.find (s,r) (init_session s G) = Some S.
Proof.
  intros G s r S Ha Hb.
  unfold init_session.
(*   unfold step. *)

  remember (roles G) as rs.
  revert r S Ha Hb. revert G Heqrs s.
  induction rs as [| r0 rs IH]; intros.
  - (* roles G = [] *)
    simpl. inversion Ha.
  - simpl in Ha.
    destruct Ha as [Ha | Ha].
    + subst.
      cbn.
      rewrite fold_preserves_other_key.
      unfold step. rewrite Hb.
      rewrite LMFacts.add_eq_o. easy.
      easy.
      unfold not. intros.
      specialize(roles_NoDup G); intro HH.
      rewrite <- Heqrs in HH.
      inversion HH. subst. easy.
    + cbn.
      assert(r <> r0).
      { unfold not. intros. subst.
        specialize(roles_NoDup G); intro HH.
        rewrite <- Heqrs in HH.
        inversion HH. subst. easy.
      }
      (*       rewrite fold_preserves_other_key. *)
      assert (Hstep :
        LM.find (s,r) (step s G empty_lctx r0)
        =
        LM.find (s,r) empty_lctx).
      {
        unfold step.
        destruct (project r0 G).
        - apply LMFacts.add_neq_o.
          intros Heq.
          inversion Heq. simpl in H1.
          subst.
          contradiction.
        - reflexivity.
      }
      apply fold_left_preserves_find with (rs := rs) (G := G) in Hstep.
      rewrite Hstep.
      apply fold_init_session_find; try easy.
      specialize(roles_NoDup G); intro HH.
      rewrite <- Heqrs in HH.
      inversion HH. subst. easy.
Qed.

Lemma init_session_find_inv :
  forall G s r T,
    LM.find (s,r) (init_session s G) = Some T ->
    In r (roles G).
Proof.
  intros G s r T.
  unfold init_session.
  remember (roles G) as rs eqn:Heqrs.
  clear Heqrs.
  revert G (* Heqrs *) r T.
  
  induction rs as [|r0 rs IH]; intros G (* Heqrs *) r T Hfind.
  - (* rs = [] *)
    simpl in Hfind.
    discriminate.
  - simpl in Hfind.
    unfold step in Hfind at 2.
    destruct (project r0 G) eqn:Hproj.
    + simpl in Hfind.
      destruct (EndpointOT.eq_dec (s,r) (s,r0)) as [Heq | Hneq].
      * (* (s,r) = (s,r0) *)
        inversion Heq; subst. simpl in H0.
        simpl. left; easy.
      * assert (Hstep :
        LM.find (s,r)
          (fold_left (step s G) rs empty_lctx)
        = Some T).
        {
          (* strip the initial add *)
          assert (Hbase :
            LM.find (s,r)
              (LM.add (s,r0) t empty_lctx)
            =
            LM.find (s,r) empty_lctx).
          {
            apply LMFacts.add_neq_o.
            intro Heq.
            apply Hneq.
            simpl. unfold EndpointOT.eq. split; easy.
          }

          (* lift through fold *)
          erewrite fold_left_preserves_find with (acc2 := empty_lctx) in Hfind.
          - easy.
          - apply LMFacts.add_neq_o.
            intro Heq.
            apply Hneq.
            simpl. unfold EndpointOT.eq. split; easy.
        }
        simpl. right.
        eapply IH; eauto.
        +
        simpl. right.
        eapply IH; eauto.
      Qed.

Inductive nat_canonical : term_ln -> Prop :=
| nc_zero :
    nat_canonical t_Zero
| nc_succ :
    forall n,
      nat_canonical n ->
      nat_canonical (t_Succ n).

Inductive branches_canonical : list (string * gtype) -> Prop :=
| bc_nil :
    branches_canonical []
| bc_cons :
    forall l G bs,
      gtype_indices_canonical G ->
      branches_canonical bs ->
      branches_canonical ((l, G) :: bs)
with gtype_indices_canonical : gtype -> Prop :=
| gc_end :
    gtype_indices_canonical g_end
| gc_bvar :
    forall n,
      gtype_indices_canonical (g_bvar n)
| gc_msg :
    forall p q A G,
      gtype_indices_canonical G ->
      gtype_indices_canonical (g_msg p q A G)
| gc_choice :
    forall p q branches,
      branches_canonical branches ->
      gtype_indices_canonical (g_choice p q branches)
| gc_natrec :
    forall P z s n,
      nat_canonical n ->
      gtype_indices_canonical z ->
      gtype_indices_canonical s ->
      gtype_indices_canonical (g_natrec P z s n).

Definition coherent_session
  (s : string)
  (Δ : lctx)
  (G : gtype) : Prop :=
  gtype_wf G /\
  gtype_indices_canonical G /\
  forall r T,
    LM.find (s,r) Δ = Some T ->
    exists S,
      project r G = Some S /\
      convertible_n_par_ln T S.

Lemma init_session_coherent :
  forall G s,
    gtype_wf G ->
    gtype_indices_canonical G ->
    coherent_session s (init_session s G) G.
Proof.
  intros G s Hwf.
  unfold coherent_session.
  split.
  - exact Hwf.
  - split. exact H. clear H.
    intros r T Hfind.

    (* Show r must be in roles G *)
    assert (Hin : In r (roles G)).
    {
      (* If LM.find (s,r) returns Some T in init_session,
         then r must have been inserted,
         so r ∈ roles G *)
      unfold init_session in Hfind.
      eapply init_session_find_inv; eauto.
    }

    (* Now use init_session_find to identify the inserted type *)
    unfold init_session in Hfind.

    (* From init_session_find *)
    assert (Hexact :
      exists S0,
        project r G = Some S0 /\
        LM.find (s,r) (init_session s G) = Some S0).
    {
      (* projection_total gives existence *)
      destruct (projection_total_wf G Hwf r) as [S0 Hproj].
      exists S0.
      split.
      - exact Hproj.
      - apply init_session_find; auto.
    }

    destruct Hexact as [S0 [Hproj Hfind0]].
    unfold init_session in Hfind0.
    rewrite Hfind in Hfind0.
    inversion Hfind0.
    subst T.

    exists S0.
    split.
    + exact Hproj.
    + (* stored type equals projection exactly *)
      apply rst_refl.
Qed.

Lemma project_msg_inv :
  forall p q (A : term_ln) (G' : gtype) (r : string) (S : term_ln),
    project r (g_msg p q A G') = Some S ->
    (r = p /\
       exists Sp, S = t_SendTy q A Sp /\ project p G' = Some Sp)
    \/
    (r = q /\
       exists Sp, S = t_RecvTy p A Sp /\ project q G' = Some Sp)
    \/
    (r <> p /\ r <> q /\ exists Sp, S = t_SBind A Sp /\ project r G' = Some Sp).
Proof.
  intros p q A G' r S Hproj.
  simpl in Hproj.
  (* decide whether r = p or r = q or neither *)
  destruct (String.eqb r p) eqn:Heq_p.
  - (* r = p case *)
    apply String.eqb_eq in Heq_p; subst r.
    (* project p (g_msg p q A G') = option_map ... (project p G') *)
    simpl in Hproj.
    destruct (project p G') eqn:HpG.
    + simpl in Hproj. inversion Hproj; subst.
      left. split; [reflexivity|].
      exists t. split; easy.
    + (* option_map None = None, contradiction with Some S *)
      simpl in Hproj. discriminate.
  - (* r <> p *)
    destruct (String.eqb r q) eqn:Heq_q.
    + (* r = q case *)
      apply String.eqb_eq in Heq_q; subst r.
      simpl in Hproj.
      destruct (project q G') eqn:HqG.
      * simpl in Hproj. inversion Hproj; subst.
        right. left. split; [reflexivity|].
        exists t. split; easy.
      * simpl in Hproj. discriminate.
    + (* r <> p and r <> q: projection stays as project r G' *)
      simpl in Hproj.
      (* in this branch project r (g_msg ...) = project r G' *)
      right. right.
      rewrite String.eqb_neq in Heq_p, Heq_q.
      unfold option_map in Hproj.
      destruct (project r G'). inversion Hproj. subst.
      split. easy. split. 
      easy. exists t. easy.
      easy.
Qed.

Fixpoint update_branch
  (l : string)
  (G' : gtype)
  (bs : list (string * gtype))
  : list (string * gtype) :=
  match bs with
  | [] => []
  | (l0,G0)::bs' =>
      if String.eqb l l0
      then (l0,G')::bs'
      else (l0,G0)::update_branch l G' bs'
  end.

Inductive gaction :=
| act_msg : string -> string -> term_ln -> gaction
| act_sel : string -> string -> string -> gaction.

Definition disjoint_roles (p q r1 r2 : string) : Prop :=
  r1 <> p /\ r1 <> q /\ r2 <> p /\ r2 <> q.

Inductive step_gtype :
  gtype -> gaction -> gtype -> Prop :=

| g_step_msg :
    forall p q A G v,
      value_ln v ->
      step_gtype
        (g_msg p q A G)
        (act_msg p q v)
        (open_gtype v G)

| g_step_choice :
    forall p q branches l G',
      gtype_wf (g_choice p q branches) ->
      lookup_gbranch l branches = Some G' ->
      step_gtype
        (g_choice p q branches)
        (act_sel p q l)
        G'

| g_step_msg_ctx :
    forall p q A G r1 r2 v G',
      disjoint_roles p q r1 r2 ->
      step_gtype G (act_msg r1 r2 v) G' ->
      step_gtype
        (g_msg p q A G)
        (act_msg r1 r2 v)
        (g_msg p q A G')

| g_step_choice_ctx :
    forall p q branches branches' r1 r2 v,
      gtype_wf (g_choice p q branches) ->
      disjoint_roles p q r1 r2 ->
      step_branches (act_msg r1 r2 v) branches branches' ->
      step_gtype
        (g_choice p q branches)
        (act_msg r1 r2 v)
        (g_choice p q branches')

| g_unfold_natrec_zero :
    forall P z s n act_tau,
      convertible_n_par_ln n t_Zero ->
      step_gtype (g_natrec P z s n) act_tau z

| g_unfold_natrec_succ :
    forall P z s n n' act_tau,
      convertible_n_par_ln n (t_Succ n') ->
      step_gtype (g_natrec P z s n) act_tau s

| g_step_choice_ctx_sel :
    forall p q branches branches' r1 r2 l,
      gtype_wf (g_choice p q branches) ->
      disjoint_roles p q r1 r2 ->
      step_branches (act_sel r1 r2 l) branches branches' ->
      step_gtype
        (g_choice p q branches)
        (act_sel r1 r2 l)
        (g_choice p q branches')

with step_branches :
  gaction ->
  list (string * gtype) ->
  list (string * gtype) ->
  Prop :=

| step_branches_nil :
    forall act,
      step_branches act [] []

| step_branches_cons :
    forall act l G G' bs bs',
      step_gtype G act G' ->
      step_branches act bs bs' ->
      step_branches act ((l,G)::bs)
                        ((l,G')::bs').

Scheme step_gtype_ind'
  := Induction for step_gtype Sort Prop
with step_branches_ind'
  := Induction for step_branches Sort Prop.

Combined Scheme step_mutind
  from step_gtype_ind', step_branches_ind'.


Lemma go_unfold_eq :
  forall r bs,
    (fix go (bs : list (string * gtype)) : option (list (string * term_ln)) :=
       match bs with
       | [] => Some []
       | (l, G') :: bs' =>
           match project r G' with
           | Some Se =>
               match go bs' with
               | Some Ss => Some ((l, Se) :: Ss)
               | None => None
               end
           | None => None
           end
       end) bs
    =
    project_choice_go r bs.
Proof.
  intros r bs.
  induction bs as [| [l G] bs IH]; simpl; auto.
  rewrite IH.
  reflexivity.
Qed.


Lemma Forall2_proj_In :
  forall r1 (l : list (string * gtype))
         (Ss : list (string * term_ln))
         (lbl : string) (G : gtype),
    Forall2
      (fun '(lbl0,G0) '(lbl1,Se) =>
         lbl0 = lbl1 /\ project r1 G0 = Some Se)
      l Ss ->
    In (lbl,G) l ->
    exists Se,
      In (lbl,Se) Ss /\
      project r1 G = Some Se.
Proof.
  intros r1 l Ss lbl G HForall.
  induction HForall; intros Hin.
  - inversion Hin.  
  - simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      destruct y as [lbly Sey].
      simpl in *.
      destruct H as [Heq Hproj].
      subst.
      exists Sey.
      split; [left; reflexivity | exact Hproj].
    + specialize (IHHForall Hin).
      destruct IHHForall as [Se [HinS Hproj]].
      exists Se.
      split; [right; exact HinS | exact Hproj].
Qed.

Lemma project_choice_go_all_some :
  forall r branches S,
    (forall lbl G,
        In (lbl,G) branches ->
        project r G = Some S) ->
    exists Ss,
      project_choice_go r branches = Some Ss.
Proof.
  intros r branches.
  induction branches as [| [lbl G] bs IH]; intros S Hall.

  (* -------------------- *)
  (* Base case            *)
  (* -------------------- *)
  - simpl.
    exists [].
    reflexivity.

  (* -------------------- *)
  (* Inductive case       *)
  (* -------------------- *)
  - simpl in *.

    (* From Hall we know head projection succeeds *)
    assert (Hhead :
      project r G = Some S).
    {
      apply Hall with (lbl := lbl).
      left; reflexivity.
    }

    (* From Hall we know tail projections succeed *)
    assert (Htail :
      forall lbl0 G0,
        In (lbl0,G0) bs ->
        project r G0 = Some S).
    {
      intros lbl0 G0 Hin.
      apply Hall with (lbl := lbl0).
      right; exact Hin.
    }

    (* Apply IH to tail *)
    destruct (IH S Htail) as [Ss IHs].

    rewrite Hhead.
    rewrite IHs.

    exists ((lbl, S) :: Ss).
    reflexivity.
Qed.

Lemma Forall2_uniform_projection :
  forall (l  : list (string * gtype))
         (Ss : list (string * term_ln))
         r S,
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project r G = Some Se)
      l Ss ->
    (forall lbl G,
        In (lbl,G) l ->
        project r G = Some S) ->
    forall lbl Se,
      In (lbl,Se) Ss ->
      Se = S.
Proof. intros.
       revert S H0 H1. revert lbl Se.
       induction H; intros.
       - inversion H1.
       - simpl in H2.
         destruct H2 as [H2 | H2].
         + subst. destruct x.
           destruct H as (Ha, Hb).
           subst.
           specialize(H1 lbl g).
           assert(In (lbl, g) ((lbl, g) :: l)).
           left. easy.
           apply H1 in H. rewrite Hb in H. inversion H. easy.
         + apply IHForall2 with (lbl := lbl); try easy.
           intros.
           apply H1 with (lbl := lbl0). simpl. right. easy.
Qed.

Lemma term_eqb_eq :
  forall t1 t2,
    term_eqb t1 t2 = true ->
    t1 = t2.
Proof.
  induction t1 using term_ln_ind_strong; intros t2 Heq;
  destruct t2; simpl in Heq; try discriminate; try easy; try (destruct e; easy).

  (* t_bvar *)
  - apply Nat.eqb_eq in Heq.
    subst; reflexivity.

  (* t_fvar *)
  - apply String.eqb_eq in Heq.
    subst; reflexivity.

  (* t_Type *)
  - apply Nat.eqb_eq in Heq.
    subst; reflexivity.

  (* t_Pi *)
  - apply andb_true_iff in Heq as [H1 H2].
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst; reflexivity.

  (* t_Lam *)
  - apply andb_true_iff in Heq as [H1 H2].
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst; reflexivity.

  (* t_App *)
  - apply andb_true_iff in Heq as [H1 H2].
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst; reflexivity.

  (* t_Succ *)
  - apply IHt1 in Heq.
    subst; reflexivity.

  (* t_NatRec_ln *)
  - repeat (apply andb_true_iff in Heq; destruct Heq as [Heq Hrest]).
    apply andb_true_iff in Heq; destruct Heq as [Heq1 Hrest2].
    apply andb_true_iff in Heq1; destruct Heq1 as [Heq1 Hrest3].
    apply IHt1_1 in Heq1.
    apply IHt1_2 in Hrest3.
    apply IHt1_3 in Hrest2.
    apply IHt1_4 in Hrest.
    subst; reflexivity.

  - destruct e, e0.
    apply andb_true_iff in Heq; destruct Heq as [Heq1 Hrest2].
    rewrite String.eqb_eq in Heq1, Hrest2.
    subst. easy.

  (* t_SendTy *)
  - apply andb_true_iff in Heq as [Hr Hrest].
    apply andb_true_iff in Hr as [HA HS].
    apply String.eqb_eq in HA; subst.
    apply IHt1_1 in HS.
    apply IHt1_2 in Hrest.
    subst; reflexivity.

  (* t_RecvTy *)
  - apply andb_true_iff in Heq as [Hr Hrest].
    apply andb_true_iff in Hr as [HA HS].
    apply String.eqb_eq in HA; subst.
    apply IHt1_1 in HS.
    apply IHt1_2 in Hrest.
    subst; reflexivity.

  (* t_SendV *)
  - repeat (apply andb_true_iff in Heq; destruct Heq as [Heq Hrest]).
    apply andb_true_iff in Heq; destruct Heq as [Heq1 Hrest2].
    apply andb_true_iff in Heq1; destruct Heq1 as [Heq1 Hrest3].
    apply String.eqb_eq in Heq1.
    apply IHt1_1 in Hrest3.
    apply IHt1_2 in Hrest2.
    apply IHt1_3 in Hrest.
    subst; reflexivity.

  (* t_Recv *)
  - repeat (apply andb_true_iff in Heq; destruct Heq as [Heq Hrest]).
    apply andb_true_iff in Heq; destruct Heq as [Heq1 Hrest2].
    apply String.eqb_eq in Heq1.
    apply IHt1_1 in Hrest2.
    apply IHt1_2 in Hrest.
    subst; reflexivity.

  (* t_Close *)
  - apply IHt1 in Heq.
    subst; reflexivity.

  (* t_Wait *)
  - apply IHt1 in Heq.
    subst; reflexivity.

  (* t_Fork *)
  - apply IHt1 in Heq.
    subst; reflexivity.

  (* t_Par *)
  - apply andb_true_iff in Heq as [H1 H2].
    apply IHt1_1 in H1.
    apply IHt1_2 in H2.
    subst; reflexivity.
  
  - apply andb_true_iff in Heq.
    destruct Heq as [Hr Hbr].
    apply String.eqb_eq in Hr.
    subst s.
    revert l Hbr.
    induction branches as [| [lbl b] bs IH]; intros l Hbr.
    + destruct l; easy.
    + inversion H. subst.
      destruct l as [| [lbl2 b2] bs2]; simpl in Hbr; try discriminate.
      repeat (apply andb_true_iff in Hbr; destruct Hbr as [Hbr Hrest]).
      apply andb_true_iff in Hbr. destruct Hbr as [Hbr Hrest2].
      apply H2 in Hrest2. subst.
      rewrite String.eqb_eq in Hbr. subst.
      apply IH with (l := bs2) in H3.
      inversion H3. easy.
      easy.

  - apply andb_true_iff in Heq.
    destruct Heq as [Hr Hbr].
    apply String.eqb_eq in Hr.
    subst s.
    revert l Hbr.
    induction branches as [| [lbl b] bs IH]; intros l Hbr.
    + destruct l; easy.
    + inversion H. subst.
      destruct l as [| [lbl2 b2] bs2]; simpl in Hbr; try discriminate.
      repeat (apply andb_true_iff in Hbr; destruct Hbr as [Hbr Hrest]).
      apply andb_true_iff in Hbr. destruct Hbr as [Hbr Hrest2].
      apply H2 in Hrest2. subst.
      rewrite String.eqb_eq in Hbr. subst.
      apply IH with (l := bs2) in H3.
      inversion H3. easy.
      easy.

  - apply andb_true_iff in Heq.
    destruct Heq as [Hr Hbr].
    apply andb_true_iff in Hr.
    destruct Hr as [Hr Hbr2].
    apply andb_true_iff in Hr.
    destruct Hr as [Hr Hbr3].
    apply IHt1_1 in Hbr2.
    apply IHt1_2 in Hbr.
    subst.
    rewrite String.eqb_eq in Hr, Hbr3.
    subst. easy.

  - apply andb_true_iff in Heq.
    destruct Heq as [Hr Hbr].
    apply andb_true_iff in Hr.
    destruct Hr as [Hr Hbr2].
    apply IHt1 in Hbr2. subst.
    rewrite String.eqb_eq in Hr. subst.
    clear IHt1.
    revert l Hbr.
    induction branches as [| [lbl b] bs IH]; intros l Hbr.
    + destruct l; easy.
    + inversion H. subst.
      destruct l as [| [lbl2 b2] bs2]; simpl in Hbr; try discriminate.
      repeat (apply andb_true_iff in Hbr; destruct Hbr as [Hbr Hrest]).
      apply andb_true_iff in Hbr. destruct Hbr as [Hbr Hrest2].
      apply H2 in Hrest2. subst.
      rewrite String.eqb_eq in Hbr. subst.
      apply IH with (l := bs2) in H3.
      inversion H3. easy.
      easy.
  - apply andb_true_iff in Heq.
    destruct Heq as [Hr Hbr].
    erewrite IHt1_1. erewrite IHt1_2; eauto.
    easy.
Qed.

Lemma term_br_eqb_eq: forall l1 l2,
  (fix branches_eqb (bs1' bs2' : list (string * term_ln)) {struct bs1'} : bool :=
     match bs1' with
     | [] => match bs2' with
             | [] => true
             | _ :: _ => false
             end
     | (l1, b1) :: bs1'' =>
         match bs2' with
         | [] => false
         | (l2, b2) :: bs2'' => (l1 =? l2)%string && term_eqb b1 b2 && branches_eqb bs1'' bs2''
         end
     end)
    l1 l2 =
  true -> l1 = l2.
Proof. intro l1.
       induction l1; intros.
       - destruct l2; try easy.
       - destruct a.
         destruct l2; try easy.
         destruct p.
         apply andb_true_iff in H.
         destruct H as (Ha,Hb).
         apply andb_true_iff in Ha.
         destruct Ha as (Ha,Hc).
         apply term_eqb_eq in Hc.
         rewrite String.eqb_eq in Ha. subst.
         f_equal. apply IHl1; easy.
Qed.

Lemma project_open_commute :
  forall G r v,
    project r (open_gtype v G)
    =
    option_map (fun S => open_ln S v)
               (project r G).
Admitted.

Lemma Forall2_In_right :
  forall A B (R : A -> B -> Prop) l l' y,
    Forall2 R l l' ->
    In y l' ->
    exists x,
      In x l /\
      R x y.
Proof. intros.
       revert H0.
       induction H; intros.
       - inversion H0.
       - simpl in H1.
         destruct H1. subst.
         exists x. split. left. easy. easy.
         apply IHForall2 in H1.
         destruct H1 as (x1,(H1a,H1b)).
         exists x1. split. simpl. right. easy.
         easy. 
Qed.

Lemma project_choice_go_advance :
  forall l0 l' l'0 p r1 r2 v S1 S2,
    p <> r1 ->
    p <> r2 ->
    (* l'0 contains old projections of p *)
    Forall2
      (fun '(lbl, G) '(lbl', Se) =>
         lbl = lbl' /\ project p G = Some Se)
      l0 l'0 ->
    (* l' contains advanced branches *)
    Forall2
      (fun '(lbl, G) '(lbl', G') =>
         lbl = lbl' /\
         project r1 G' = Some (open_ln S1 v) /\
         project r2 G' = Some (open_ln S2 v) /\
         (forall r S_old,
            r <> r1 -> r <> r2 ->
            project r G = Some S_old ->
            project r G' = Some (open_local_proj S_old v)))
      l0 l' ->
    project_choice_go p l'
    =
    Some (map (fun '(lbl, Se) => (lbl, open_local_proj Se v)) l'0).
Proof. intro l0.
       induction l0; intros.
       - inversion H1. subst.
         inversion H2. subst. simpl. easy.
       - inversion H1. subst.
         destruct a, y.
         destruct H5. subst.
         inversion H2. subst.
         destruct y. 
         destruct H6. subst.
         eapply IHl0 in H9; eauto.
         simpl.
         destruct H5 as (H5a,(H5b,H5)).
         specialize(H5 p t H H0 H4).
         rewrite H5.
         rewrite H9. easy.
Qed.

Lemma forallb_map_preserves :
  forall (Ss : list (string * term_ln)) Se v,
    forallb (fun '(_, S') => term_eqb Se S') Ss = true ->
    forallb
      (fun '(_, S') => term_eqb (open_local_proj Se v) S')
      (map (fun '(lbl, Se0) => (lbl, open_local_proj Se0 v)) Ss)
    = true.
Proof. intro Ss.
       induction Ss; intros.
       - simpl. easy.
       - simpl in H.
         destruct a.
         apply andb_true_iff in H. destruct H as (Ha,Hb).
         apply IHSs with (v := v) in Hb.
         simpl.
         rewrite Hb.
         apply term_eqb_eq in Ha. subst.
         rewrite term_eqb_refl. easy.
Qed.

Definition P_g :=
  fun (G : gtype) (act : gaction) (G' : gtype) =>
    forall r1 r2 v A S1 S2,
      act = act_msg r1 r2 v ->
      project r1 G = Some (t_SendTy r2 A S1) ->
      project r2 G = Some (t_RecvTy r1 A S2) ->
      (* main participants *)
      project r1 G' = Some (open_ln S1 v) /\
      project r2 G' = Some (open_ln S2 v) /\
      (* every other role gets its projection opened appropriately *)
      (forall r S_old,
         r <> r1 ->
         r <> r2 ->
         project r G = Some S_old ->
         project r G' = Some (open_local_proj S_old v)).

Definition P_b :=
  fun (act : gaction)
      (bs  : list (string * gtype))
      (bs' : list (string * gtype)) =>
    forall r1 r2 v A S1 S2,
      act = act_msg r1 r2 v ->
      (* assumption: every original branch has the same r1/r2 projections *)
      (forall lbl G,
         In (lbl, G) bs ->
         project r1 G = Some (t_SendTy r2 A S1) /\
         project r2 G = Some (t_RecvTy r1 A S2) (* /\ *)
         (* for any third party role, the original branch exposes some S_old *)
      ) ->
      (* conclusion: branches are pairwise preserved (same labels) and each advanced *)
      Forall2
        (fun '(lbl, G) '(lbl', G') =>
           lbl = lbl' /\
           project r1 G' = Some (open_ln S1 v) /\
           project r2 G' = Some (open_ln S2 v) /\
           (forall r S_old, r <> r1 -> r <> r2 -> 
              project r G = Some S_old ->
              project r G' = Some (open_local_proj S_old v))
        )
        bs bs'.

Lemma step_preserves_project_mutual :
  (forall G act G', step_gtype G act G' -> P_g G act G')
  /\
  (forall act bs bs', step_branches act bs bs' -> P_b act bs bs').
Proof.  apply step_mutind; intros.
        9:{ unfold P_g, P_b in *.
            cbn in *. intros.
            subst.
            constructor.
            split. easy.
            specialize(H2 l G).
            assert((l, G) = (l, G) \/ In (l, G) bs).
            left. easy.
            apply H2 in H1.
            destruct H1 as (H1a,H1b).
            subst.
            specialize(H r1 r2 v A S1 S2 eq_refl H1a H1b).
            split. easy. split. easy.
            intros.
            apply H; try easy.
            
            apply H0 with (A := A); try easy.
            intros.
            specialize(H2 lbl G0).
            assert((l, G) = (lbl, G0) \/ In (lbl, G0) bs ).
            right. easy.
            apply H2 in H3. easy.
          }
        8:{ unfold P_b. intros.
            constructor.
          }
        4:{ unfold P_g, P_b in *.
            intros.
            symmetry in H0.
            inversion H0. subst.
            simpl in H1.
            split. 
            - simpl.
              unfold disjoint_roles in d.
              assert((r1 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r1 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              rewrite H3, H4.
              rewrite H3, H4 in H1.
              assert((r2 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r2 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              simpl in H2.
              rewrite H5, H6 in H2.
              rewrite go_unfold_eq.
              rewrite go_unfold_eq in H1, H2.
              destruct (project_choice_go r2 branches) as [l |] eqn:Hgo.
              2: discriminate H2.
              destruct l as [| [lbl0 Se] Ss].
              1: discriminate H2.
              apply project_choice_go_some in Hgo.
              destruct (project_choice_go r1 branches) as [l |] eqn:Hgo1.
              2: discriminate H1.
              destruct l as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              inversion Hgo. subst.
              destruct x.
              inversion Hgo1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
              rewrite H7 in H1. inversion H1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se S') Ss); intros.
              rewrite H8 in H2.
              inversion H2. subst.
              destruct H10 as (Ha,Hb).
              destruct H12 as (Hc,Hd).
              subst.

              specialize (H r1 r2 v A S1 S2 eq_refl).
              assert(
                (forall (lbl : string) (G : gtype),
                   In (lbl, G) ((lbl1, g0) :: l) ->
                   project r1 G = Some (t_SendTy r2 A S1) /\
                   project r2 G = Some (t_RecvTy r1 A S2))).
              { intros. simpl in H9. destruct H9.
                inversion H9. subst. split. easy. easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H11.
                destruct H11 as (Se,(H1a,H1b)).
                rewrite forallb_forall in H7, H8.
                specialize(H8 (lbl, Se) H1a).
                cbn in H8.
                destruct Se; try easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H14.
                destruct H14 as (Se,(H2a,H2b)).
                specialize(H7 (lbl, Se) H2a).
                cbn in H7.
                destruct Se; try easy.
                apply andb_true_iff in H7.
                destruct H7 as (H7,H7a).
                apply andb_true_iff in H7.
                destruct H7 as (H7,H7b).
                apply andb_true_iff in H8.
                destruct H8 as (H8,H8a).
                apply andb_true_iff in H8.
                destruct H8 as (H8,H8b).
                rewrite String.eqb_eq in H7, H8. subst.
                apply term_eqb_eq in H7a, H7b, H8a, H8b.
                subst. easy.
                easy. easy.
              }
              pose proof (H H9) as Hall_full.
              assert (Hall_r1 :
                forall lbl G',
                  In (lbl,G') branches' ->
                  project r1 G' = Some (open_ln S1 v)).
              {
                intros lbl G' Hin.
                inversion Hall_full. subst.
                destruct y.
                simpl in Hin.
                destruct H13. subst.
                destruct Hin. inversion H10. rewrite <- H17. easy.
                specialize(Forall2_proj_In); intros.
                pose proof (Forall2_In_right _ _ _ _ _ _ H16 H10)
                as [x [Hx_in Hrel]].
                destruct x. easy.
              }

              destruct (project_choice_go r1 branches') as [l' |] eqn:Hgo'.
              destruct l' as [| [lbl0 Se0] Ss0].
              apply project_choice_go_some in Hgo'.
              inversion Hgo'. subst.
              inversion s.
              apply project_choice_go_some in Hgo'.
              inversion Hgo'. subst.
              destruct x.
              assert (project r1 g1 = Some (open_ln S1 v)).
              {
                apply Hall_r1 with (lbl := s0).
                left; reflexivity.
              }
              destruct H15 as (Ha,Hc).
              subst.
              rewrite Hc in H10.
              inversion H10. subst.
              assert (Hall_tail :
                forall lbl G',
                  In (lbl,G') l0 ->
                  project r1 G' = Some (open_ln S1 v)).
              {
                intros lbl G' Hin.
                apply Hall_r1 with (lbl := lbl).
                right; exact Hin.
              }
              destruct l0. inversion H16.
              cbn. easy.
              destruct p0.
              assert (Hunif :
                forall lbl Se,
                  In (lbl,Se) Ss0 ->
                  Se = (open_ln S1 v)).
              {
                apply (Forall2_uniform_projection
                         ((s0,g2)::l0)
                         Ss0
                         r1
                         (open_ln S1 v)).
                - exact H16.
                - exact Hall_tail.
              }
              assert(forallb (fun '(_, S') => term_eqb (open_ln S1 v) S') Ss0 = true).
              { rewrite forallb_forall.
                intros. destruct x.
                specialize(Hunif s1 t H12).
                subst.
                apply term_eqb_refl.
              }
              rewrite H12. easy.
              apply project_choice_go_all_some in Hall_r1.
              destruct Hall_r1. rewrite H10 in Hgo'. easy.
              rewrite H8 in H2. easy.
              rewrite H7 in H1. easy.
            -  split.
            + unfold disjoint_roles in d.
              assert((r1 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r1 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              simpl in H2.
              rewrite H3, H4 in H1.
              assert((r2 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r2 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              rewrite H5, H6 in H2.
              simpl.
              rewrite H5, H6.
              rewrite go_unfold_eq.
              rewrite go_unfold_eq in H1, H2.
              destruct (project_choice_go r2 branches) as [l |] eqn:Hgo.
              2: discriminate H2.
              destruct l as [| [lbl0 Se] Ss].
              1: discriminate H2.
              apply project_choice_go_some in Hgo.
              destruct (project_choice_go r1 branches) as [l |] eqn:Hgo1.
              2: discriminate H1.
              destruct l as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              inversion Hgo. subst.
              destruct x.
              inversion Hgo1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
              rewrite H7 in H1. inversion H1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se S') Ss); intros.
              rewrite H8 in H2.
              inversion H2. subst.
              destruct H10 as (Ha,Hb).
              destruct H12 as (Hc,Hd).
              subst.
              specialize (H r1 r2 v A S1 S2 eq_refl).
              assert(
              (forall (lbl : string) (G : gtype),
                 In (lbl, G) ((lbl1, g0) :: l) -> project r1 G = Some (t_SendTy r2 A S1) /\ project r2 G = Some (t_RecvTy r1 A S2))).
              { intros. simpl in H9. destruct H9.
                inversion H9. subst. easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H11.
                destruct H11 as (Se,(H1a,H1b)).
                rewrite forallb_forall in H7, H8.
                specialize(H8 (lbl, Se) H1a).
                cbn in H8.
                destruct Se; try easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H14.
                destruct H14 as (Se,(H2a,H2b)).
                specialize(H7 (lbl, Se) H2a).
                cbn in H7.
                destruct Se; try easy.
                apply andb_true_iff in H7.
                destruct H7 as (H7,H7a).
                apply andb_true_iff in H7.
                destruct H7 as (H7,H7b).
                apply andb_true_iff in H8.
                destruct H8 as (H8,H8a).
                apply andb_true_iff in H8.
                destruct H8 as (H8,H8b).
                rewrite String.eqb_eq in H7, H8. subst.
                apply term_eqb_eq in H7a, H7b, H8a, H8b.
                subst. easy.
                easy. easy.
              }
              pose proof (H H9) as Hall_full.
              assert (Hall_r2 :
                forall lbl G',
                  In (lbl,G') branches' ->
                  project r2 G' = Some (open_ln S2 v)).
              {
                intros lbl G' Hin.
                inversion Hall_full. subst.
                destruct y.
                simpl in Hin.
                destruct H13. subst.
                destruct Hin. inversion H10. rewrite <- H17. easy.
                specialize(Forall2_proj_In); intros.
                pose proof (Forall2_In_right _ _ _ _ _ _ H16 H10)
                as [x [Hx_in Hrel]].
                destruct x. easy.
              }
              destruct (project_choice_go r2 branches') as [l' |] eqn:Hgo'.
              destruct l' as [| [lbl0 Se0] Ss0].
              apply project_choice_go_some in Hgo'.
              inversion Hgo'. subst.
              inversion s.
              apply project_choice_go_some in Hgo'.
              inversion Hgo'. subst.
              destruct x.
              assert (project r2 g1 = Some (open_ln S2 v)).
              {
                apply Hall_r2 with (lbl := s0).
                left; reflexivity.
              }
              destruct H15 as (Ha,Hc).
              subst.
              rewrite Hc in H10.
              inversion H10. subst.
              assert (Hall_tail :
                forall lbl G',
                  In (lbl,G') l0 ->
                  project r2 G' = Some (open_ln S2 v)).
              {
                intros lbl G' Hin.
                apply Hall_r2 with (lbl := lbl).
                right; exact Hin.
              }
              destruct l0. inversion H16.
              cbn. easy.
              destruct p0.
              assert (Hunif :
                forall lbl Se,
                  In (lbl,Se) Ss0 ->
                  Se = (open_ln S2 v)).
              {
                apply (Forall2_uniform_projection
                         ((s0,g2)::l0)
                         Ss0
                         r2
                         (open_ln S2 v)).
                - exact H16.
                - exact Hall_tail.
              }
              assert(forallb (fun '(_, S') => term_eqb (open_ln S2 v) S') Ss0 = true).
              { rewrite forallb_forall.
                intros. destruct x.
                specialize(Hunif s1 t H12).
                subst.
                apply term_eqb_refl.
              }
              rewrite H12. easy.
              apply project_choice_go_all_some in Hall_r2.
              destruct Hall_r2. rewrite H10 in Hgo'. easy.
              rewrite H8 in H2. easy.
              rewrite H7 in H1. easy.
            + unfold disjoint_roles in d.
              assert((r1 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r1 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              simpl in H2.
              rewrite H3, H4 in H1.
              assert((r2 =? p)%string = false).
              { apply String.eqb_neq. easy. }
              assert((r2 =? q)%string = false).
              { apply String.eqb_neq. easy. }
              rewrite H5, H6 in H2.
              simpl.
              intros.
              case_eq((r =? p)%string); intros.
              rewrite String.eqb_eq in H10. subst.
              rewrite String.eqb_refl in H9.
              rewrite go_unfold_eq.
              rewrite go_unfold_eq in H1, H2, H9.
              unfold option_map in H9.
              destruct (project_choice_go p branches) as [l |] eqn:Hgo.
              2: discriminate H9. inversion H9. subst.
              destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
              destruct l1 as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
              destruct l2 as [| [lbl2 Se2] Ss2].
              1: discriminate H2.
              apply project_choice_go_some in Hgo2.
              inversion Hgo1. subst.
              inversion Hgo2. subst.
              destruct x.
              destruct H13. subst.
              destruct H15. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
              rewrite H10 in H1. inversion H1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
              rewrite H13 in H2. inversion H2. subst.
              specialize(H r1 r2 v A S1 S2 eq_refl).
              assert(
              (forall (lbl : string) (G : gtype),
                 In (lbl, G) ((lbl2, g0) :: l0) -> project r1 G = Some (t_SendTy r2 A S1) /\ project r2 G = Some (t_RecvTy r1 A S2))
              ).
              { intros. simpl in H15.
                destruct H15. inversion H15. subst.
                easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H14; try easy.
                destruct H14 as (Se,(H14a,H14b)).
                rewrite forallb_forall in H10.
                specialize(H10 (lbl,Se) H14a).
                simpl in H10.
                destruct Se; try easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H17; try easy.
                destruct H17 as (See,(H17a,H17b)).
                rewrite forallb_forall in H13.
                specialize(H13 (lbl,See) H17a).
                simpl in H13.
                destruct See; try easy.
                apply andb_true_iff in H10, H13.
                destruct H10 as (Hf1,Hf2).
                destruct H13 as (Hf3,Hf4).
                apply term_eqb_eq in Hf2, Hf4. subst.
                apply andb_true_iff in Hf1, Hf3.
                destruct Hf1 as (Hf1,Hf5).
                destruct Hf3 as (Hf3,Hf6).
                apply term_eqb_eq in Hf5, Hf6. subst.
                rewrite String.eqb_eq in Hf1, Hf3. subst.
                easy.
              }
              specialize(H H15).
              cbn.
              unfold option_map.
              inversion H.
              subst. simpl.
              destruct y.
              cbn.
              destruct H19 as (Hu,(Hv1,(Hv2,Hv3))).
              subst.
              apply project_choice_go_some in Hgo.
              simpl.
              inversion Hgo.
              subst.
              destruct y. destruct H19. subst.
              apply Hv3 in H18; try easy.
              rewrite H18.
              cbn.
              specialize (project_choice_go_advance l0 l' l'0 p r1 r2 v S1 S2 H7 H8 H22 H21); intro HH.
              rewrite HH. easy.
              rewrite H13 in H2. easy.
              rewrite H10 in H1. easy.
              easy. easy.
              
              case_eq((r =? q)%string); intros.
              rewrite H11 in H9.
              rewrite H10 in H9.
              rewrite String.eqb_eq in H11. subst.

             rewrite go_unfold_eq.
              rewrite go_unfold_eq in H1, H2, H9.
              unfold option_map in H9.
              destruct (project_choice_go q branches) as [l |] eqn:Hgo.
              2: discriminate H9. inversion H9. subst.
              destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
              destruct l1 as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
              destruct l2 as [| [lbl2 Se2] Ss2].
              1: discriminate H2.
              apply project_choice_go_some in Hgo2.
              inversion Hgo1. subst.
              inversion Hgo2. subst.
              destruct x.
              destruct H14. subst.
              destruct H16. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
              rewrite H11 in H1. inversion H1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
              rewrite H14 in H2. inversion H2. subst.
              specialize(H r1 r2 v A S1 S2 eq_refl).
              assert(
              (forall (lbl : string) (G : gtype),
                  In (lbl, G) ((lbl2, g0) :: l0) -> project r1 G = Some (t_SendTy r2 A S1) /\ project r2 G = Some (t_RecvTy r1 A S2))
              ).
              { intros. simpl in H16.
                destruct H16. inversion H16. subst.
                easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H15; try easy.
                destruct H15 as (Se,(H15a,H15b)).
                rewrite forallb_forall in H11.
                specialize(H11 (lbl,Se) H15a).
                simpl in H10.
                destruct Se; try easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H18; try easy.
                destruct H18 as (See,(H18a,H18b)).
                rewrite forallb_forall in H14.
                specialize(H14 (lbl,See) H18a).
                simpl in H14.
                destruct See; try easy.
                apply term_eqb_eq in H11. inversion H11. subst.
                apply andb_true_iff in H14.
                destruct H14 as (Hf1,Hf2).
                apply andb_true_iff in Hf1.
                destruct Hf1 as (Hf1,Hf3).
                rewrite String.eqb_eq in Hf1.
                apply term_eqb_eq in Hf2, Hf3.
                subst. easy.
              }
              specialize(H H16).
              cbn.
              unfold option_map.
              inversion H.
              subst. simpl.
              destruct y.
              cbn.
              destruct H20 as (Hu,(Hv1,(Hv2,Hv3))).
              subst.
              apply project_choice_go_some in Hgo.
              simpl.

              inversion Hgo.
              subst.
              destruct y. destruct H20. subst.
              apply Hv3 in H19; try easy.
              rewrite H19.
              cbn.
              specialize (project_choice_go_advance l0 l' l'0 q r1 r2 v S1 S2 H7 H8 H23 H22); intro HH.
              rewrite HH. easy.
              rewrite H14 in H2. easy.
              rewrite H11 in H1. easy.
              easy. easy.
              
              rewrite H10, H11 in H9.
              rewrite go_unfold_eq.
              rewrite go_unfold_eq in H1, H2, H9.
              destruct (project_choice_go r branches) as [l |] eqn:Hgo.
              destruct l as [| [lbl Se] Ss].
              1: discriminate H9.
              apply project_choice_go_some in Hgo.
              simpl.
              destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
              destruct l1 as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
              destruct l2 as [| [lbl2 Se2] Ss2].
              1: discriminate H2.
              apply project_choice_go_some in Hgo2.
              inversion Hgo1. subst.
              inversion Hgo2. subst.
              destruct x.
              destruct H15. subst.
              destruct H17. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
              rewrite H12 in H1. inversion H1. subst.
              case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
              rewrite H15 in H2. inversion H2. subst.
              specialize(H r1 r2 v A S1 S2 eq_refl).
              assert(
                 (forall (lbl : string) (G : gtype),
                   In (lbl, G) ((lbl2, g0) :: l) -> project r1 G = Some (t_SendTy r2 A S1) /\ project r2 G = Some (t_RecvTy r1 A S2))
              ).
              { intros. simpl in H17.
                destruct H17. inversion H17. subst.
                easy.
                apply Forall2_proj_In with (lbl := lbl0) (G := G) in H16; try easy.
                destruct H16 as (Sea,(H16a,H16b)).
                rewrite forallb_forall in H12.
                specialize(H12 (lbl0,Sea) H16a).
                simpl in H11.
                destruct Sea; try easy.
                apply Forall2_proj_In with (lbl := lbl0) (G := G) in H19; try easy.
                destruct H19 as (See,(H19a,H19b)).
                rewrite forallb_forall in H15.
                specialize(H15 (lbl0,See) H19a).
                simpl in H15.
                destruct See; try easy.
                apply term_eqb_eq in H12. inversion H12. subst.
                apply andb_true_iff in H15.
                destruct H15 as (Hf1,Hf2).
                apply andb_true_iff in Hf1.
                destruct Hf1 as (Hf1,Hf3).
                rewrite String.eqb_eq in Hf1.
                apply term_eqb_eq in Hf2, Hf3.
                subst. easy.
              }
              specialize(H H17).

              cbn.
              unfold option_map.
              inversion H.
              subst. simpl.
              destruct y.
              cbn.
              destruct H21 as (Hu,(Hv1,(Hv2,Hv3))).
              subst.
              simpl.

              inversion Hgo.
              subst. destruct H22. subst.
              apply Hv3 in H20; try easy.
              rewrite H20.
              cbn.
              specialize (project_choice_go_advance l l' Ss r r1 r2 v S1 S2 H7 H8 H25 H23); intro HH.
              rewrite HH.
              case_eq(forallb (fun '(_, S') => term_eqb Se S') Ss); intros.
              rewrite H18 in H9. inversion H9. subst.
              specialize (forallb_map_preserves Ss S_old v H18); intro HHH.
              rewrite HHH. easy.
              rewrite H18 in H9. easy.
              rewrite H15 in H2. easy.
              rewrite H12 in H1. easy. easy. easy. easy.
         }
       4:{
       unfold P_g. intros.
       simpl in H0, H1.
       case_eq(project r1 z); intros.
       rewrite H2 in H0.
       case_eq(project r1 s); intros.
       rewrite H3 in H0.
       inversion H0.
       rewrite H3 in H0. easy.
       rewrite H2 in H0. easy.
       }
     4:{
       unfold P_g. intros.
       simpl in H0, H1.
       case_eq(project r1 z); intros.
       rewrite H2 in H0.
       case_eq(project r1 s); intros.
       rewrite H3 in H0.
       inversion H0.
       rewrite H3 in H0. easy.
       rewrite H2 in H0. easy.
       }
     2:{
       unfold P_g. intros.
       simpl in H0, H1.
       inversion H.
       }
     2:{
       unfold P_g in *. intros.
       simpl in H0, H1, H2.
       symmetry in H0.
       inversion H0. subst.
       unfold disjoint_roles in d.
       assert((r1 =? p)%string = false).
       { apply String.eqb_neq. easy. }
       assert((r1 =? q)%string = false).
       { apply String.eqb_neq. easy. }
       simpl in H2.
       rewrite H3, H4 in H1.
       assert((r2 =? p)%string = false).
       { apply String.eqb_neq. easy. }
       assert((r2 =? q)%string = false).
       { apply String.eqb_neq. easy. }
       rewrite H5, H6 in H2.
       unfold option_map in H1, H2.
       case_eq(project r1 G); intros.
       rewrite H7 in H1. easy.
       rewrite H7 in H1. easy.
       }
     1:{ unfold P_g in *. intros.
         inversion H. subst.
         simpl in H0, H1.
         case_eq((r2 =? r1)%string); intros.
         rewrite H2 in H1. 
         unfold option_map in H1.
         destruct(project r2 G); easy.
         rewrite H2 in H1.
         rewrite String.eqb_refl in H0, H1.
         unfold option_map in H0, H1.
         case_eq(project r1 G); intros.
         rewrite H3 in H0.
         inversion H0. subst.
         case_eq(project r2 G); intros.
         rewrite H4 in H1.
         inversion H1. subst.
         specialize(project_open_commute G r1 v1); intros.
         unfold option_map in H5.
         rewrite H3 in H5.
         specialize(project_open_commute G r2 v1); intros.
         unfold option_map in H6.
         rewrite H4 in H6.
         split. easy. split. easy.
         intros.
         simpl in H9.
         apply String.eqb_neq in H7, H8.
         rewrite H7, H8 in H9.
         unfold option_map in H9.
         case_eq(project r G ); intros.
         rewrite H10 in H9. inversion H9. subst.
         simpl.
         specialize(project_open_commute); intros.
         rewrite H11.
         unfold option_map. rewrite H10.
         easy.
         rewrite H10 in H9. easy.
         rewrite H4 in H1. easy.
         rewrite H3 in H0. easy.
       }
     1:{ unfold P_g, P_b in *. intros.
         inversion H0.
       }
Qed.

Lemma step_gtype_preserves_project :
  forall G act G',
    step_gtype G act G' ->
    forall r1 r2 v A S1 S2,
      act = act_msg r1 r2 v ->
      project r1 G = Some (t_SendTy r2 A S1) ->
      project r2 G = Some (t_RecvTy r1 A S2) ->
      project r1 G' = Some (open_ln S1 v) /\
      project r2 G' = Some (open_ln S2 v) /\
      (forall r S_old,
         r <> r1 ->
         r <> r2 ->
         project r G = Some S_old ->
         project r G' = Some (open_local_proj S_old v)).
Proof.
  intros G act G' Hstep.
  destruct step_preserves_project_mutual as [H _].
  unfold P_g in H.
  eapply H; eauto.
Qed.

Lemma step_branches_preserves_project :
  forall act bs bs',
    step_branches act bs bs' ->
    forall r1 r2 v A S1 S2,
      act = act_msg r1 r2 v ->
      (forall lbl G,
         In (lbl, G) bs ->
         project r1 G = Some (t_SendTy r2 A S1) /\
         project r2 G = Some (t_RecvTy r1 A S2)) ->
      Forall2
        (fun '(lbl, G) '(lbl', G') =>
           lbl = lbl' /\
           project r1 G' = Some (open_ln S1 v) /\
           project r2 G' = Some (open_ln S2 v) /\
           (forall r S_old,
              r <> r1 -> r <> r2 ->
              project r G = Some S_old ->
              project r G' = Some (open_local_proj S_old v)))
        bs bs'.
Proof.
  intros act bs bs' Hstep.
  destruct step_preserves_project_mutual as [_ H].
  unfold P_b in H.
  eapply H; eauto.
Qed.

Lemma step_branches_preserves_labels :
  forall act bs bs',
    step_branches act bs bs' ->
    map fst bs' = map fst bs.
Proof.
  induction 1.
  - reflexivity.
  - simpl.
    rewrite IHstep_branches.
    reflexivity.
Qed.

Lemma Forall2_map_fst_In :
  forall (A B : Type)
         (l1 : list (string * A))
         (l2 : list (string * B))
         (R : (string * A) -> (string * B) -> Prop)
         s,
    Forall2
      (fun '(lbl1,a) '(lbl2,b) =>
         lbl1 = lbl2 /\ R (lbl1,a) (lbl2,b))
      l1 l2 ->
    In s (map fst l2) ->
    In s (map fst l1).
Proof.
  intros A B l1 l2 R s HForall.
  induction HForall; intros Hin.
  - (* nil *)
    simpl in Hin. contradiction.

  - (* cons *)
    simpl in *.
    destruct x as [lbl1 a].
    destruct y as [lbl2 b].
    destruct H as [Heq _].
    subst lbl2.

    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + (* head *)
      subst.
      left.
      reflexivity.
    + (* tail *)
      right.
      apply IHHForall.
      exact Hin.
Qed.

Lemma Forall2_preserves_NoDup_labels :
  forall (A B : Type)
         (l1 : list (string * A))
         (l2 : list (string * B))
         (R : (string * A) -> (string * B) -> Prop),
    Forall2
      (fun '(lbl1,a) '(lbl2,b) =>
         lbl1 = lbl2 /\ R (lbl1,a) (lbl2,b))
      l1 l2 ->
    NoDup (map fst l1) ->
    NoDup (map fst l2).
Proof. intros A B l.
       induction l; intros.
       - inversion H. easy.
       - simpl in H0.
         inversion H.
         subst. simpl.
         destruct a, y.
         destruct H3. subst.
         apply NoDup_cons_iff.
         apply NoDup_cons_iff in H0. split.
         unfold not. intros.
         destruct H0.
         apply H0. simpl. simpl in H1.
         apply Forall2_map_fst_In with (s := s0) in H5; easy.
         apply IHl with (R := R); try easy.
Qed.

Lemma notin_map_fst_implies_neq :
  forall (A : Type) (l : list (string * A)) s lbl y,
    ~ In s (map fst l) ->
    NoDup (map fst l) ->
    In (lbl, y) l ->
    lbl <> s.
Proof.
  intros A l.
  induction l as [| [lbl0 a0] l IH]; intros s lbl y Hnotin Hndup Hin.

  - (* l = [] *)
    inversion Hin.

  - simpl in *.
    inversion Hndup as [| x xs Hnotin_tail Hndup_tail]; subst.
    simpl in Hnotin.

    destruct Hin as [Hin | Hin].

    + (* head case *)
      inversion Hin; subst.
      simpl in Hnotin.
      intro Heq.
      subst.
      apply Hnotin.
      left; reflexivity.

    + (* tail case *)
      apply IH with (y := y).
      * (* ~ In s (map fst l) *)
        intro Hin_map.
        apply Hnotin.
        right; exact Hin_map.
      * (* NoDup (map fst l) *)
        exact Hndup_tail.
      * (* In (lbl, y) l *)
        exact Hin.
Qed.

Lemma Forall2_map_fst_In_project :
  forall (branches : list (string * gtype))
         (Ss : list (string * term_ln))
         r1 s,
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project r1 G = Some Se)
      branches Ss ->
    In s (map fst Ss) ->
    In s (map fst branches).
Proof.
  intros l.
  induction l; intros.
  - inversion H. subst. easy.
  - simpl in *.
    inversion H. subst.
    simpl in H0.
    destruct a, y.
    destruct H0.
    + simpl in H0. subst.
      destruct H3. subst. simpl. left. easy.
    + destruct H3. subst.
      apply IHl with (s := s) in H5.
      right. easy.
      easy.
Qed.

Lemma Forall2_preserves_NoDup_labels_project :
  forall (branches : list (string * gtype))
         (Ss : list (string * term_ln))
         r1,
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project r1 G = Some Se)
      branches Ss ->
    NoDup (map fst branches) ->
    NoDup (map fst Ss).
Proof.
  intros l.
  induction l; intros.
  - simpl. inversion H. easy.
  - destruct a. simpl in H0.
    apply NoDup_cons_iff in H0.
    inversion H. subst.
    simpl.
    apply NoDup_cons_iff. 
    destruct H0.
    split. unfold not. intros.
    apply H0. destruct y. destruct H3. subst.
    simpl in H2.
    eapply Forall2_map_fst_In_project with (s := s0) in H5; try easy.
    apply IHl with (r1 := r1); easy.
Qed.

Lemma lookup_branch_same:
  forall l lbl x y,
  NoDup (map fst l) ->
  lookup_branch lbl l = Some x ->
  In (lbl, y) l ->
  x = y.
Proof. intro l.
       induction l; intros.
       - inversion H1. 
       - simpl in H,H0,H1.
         destruct H1.
         + destruct a. inversion H1. subst.
           simpl in H.
           rewrite String.eqb_refl in H0.
           inversion H0. easy.
         + simpl in H,H0. destruct a.
           apply NoDup_cons_iff in H.
           destruct H.
           simpl in H.
           apply notin_map_fst_implies_neq with (lbl := lbl) (y := y) in H; try easy.
           apply String.eqb_neq in H.
           rewrite H in H0.
           apply IHl with (lbl := lbl); easy.
Qed.

Lemma lookup_gbranch_in :
  forall bs lbl G,
    NoDup (map fst bs) -> 
    In (lbl,G) bs ->
    lookup_gbranch lbl bs = Some G.
Proof.
  intro bs.
  induction bs as [| [l0 G0] bs IH]; intros lbl G Hndup Hin.
  - inversion Hin.
  - simpl in *.
    inversion Hndup as [| ? ? Hnotin Hndup']; subst.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      simpl.
      rewrite String.eqb_refl.
      reflexivity.
    + simpl.
      assert((lbl =? l0)%string = false).
      { apply notin_map_fst_implies_neq with (lbl := lbl) (y := G) in Hnotin; try easy.
        apply String.eqb_neq. easy.
      }
      rewrite H.
      apply IH; easy.
Qed.

Lemma lookup_gbranch_In :
  forall l bs G,
    lookup_gbranch l bs = Some G ->
    In (l, G) bs.
Proof.
  intros l bs.
  induction bs as [| [lbl G0] bs IH]; intros G H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (String.eqb l lbl) eqn:E.
    + apply String.eqb_eq in E.
      inversion H; subst.
      left; subst; reflexivity.
    + right.
      apply IH.
      exact H.
Qed.

Lemma project_choice_go_from_Forall2 :
  forall p l1 l',
    Forall2
      (fun '(lbl, G) '(lbl', Se) =>
         lbl = lbl' /\ project p G = Some Se)
      l1 l' ->
    project_choice_go p l1 = Some l'.
Proof.
  intros p l1 l' H.
  induction H.
  - (* nil *)
    simpl.
    reflexivity.

  - (* cons *)
    simpl.
    destruct x as [lbl G].
    destruct y as [lbl' Se].
    destruct H as [Heq Hproj].
    subst.
    rewrite Hproj.
    rewrite IHForall2.
    reflexivity.
Qed.

Lemma project_choice_go_context_preserved :
  forall p r1 r2 l1 l' l'0 Se,
    p <> r1 ->
    p <> r2 ->
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project p G = Some Se)
      l1 l' ->
    Forall2
      (fun '(lbl,G) '(lbl',G') =>
         lbl = lbl' /\
         project r1 G' = Some Se /\
         project r2 G' = Some Se /\
         (forall r S_old,
            r <> r1 ->
            r <> r2 ->
            project r G = Some S_old ->
            project r G' = Some S_old))
      l1 l'0 ->
    project_choice_go p l'0 = Some l'.
Proof.
  intros p r1 r2 l1 l' l'0 Se Hp1 Hp2 Hproj Hstep.
  revert r1 r2 Hp1 Hp2 Hstep. revert l'0.
  induction Hproj; intros.
  - (* nil *)
    inversion Hstep; simpl; reflexivity.

  - (* cons *)
    inversion Hstep; subst.
    simpl.
    destruct x as [lbl G].
    destruct y as [lbl' Se1].
    destruct y0 as [lbl'' G'].
    simpl in *.
    destruct H2. subst.
    apply IHHproj in H4; try easy.
    rewrite H4.
    destruct H. subst.
    apply H1 in H0; try easy.
    rewrite H0.
    easy.
Qed.

Lemma project_choice_go_context_preserved_c :
  forall p r1 r2 l1 l' l'0 Se1 Se2,
    p <> r1 ->
    p <> r2 ->
    Forall2
      (fun '(lbl,G) '(lbl',Se) =>
         lbl = lbl' /\ project p G = Some Se)
      l1 l' ->
    Forall2
      (fun '(lbl,G) '(lbl',G') =>
         lbl = lbl' /\
         project r1 G' = Some Se1 /\
         project r2 G' = Some Se2 /\
(*          convertible_n_par_ln Se1 Se2 /\ *)
         (forall r S_old,
            r <> r1 ->
            r <> r2 ->
            project r G = Some S_old ->
            project r G' = Some S_old))
      l1 l'0 ->
    project_choice_go p l'0 = Some l'.
Proof.
  intros p r1 r2 l1 l' l'0 Se1 Se2 Hp1 Hp2 Hproj Hstep.
  revert r1 r2 Hp1 Hp2 Hstep. revert Se1 Se2. revert l'0.
  induction Hproj; intros.
  - (* nil *)
    inversion Hstep; simpl; reflexivity.

  - (* cons *)
    inversion Hstep; subst.
    simpl.
    destruct x as [lbl G].
    destruct y as [lbl' Se1a].
    destruct y0 as [lbl'' G'].
    simpl in *.
    destruct H2. subst.
    apply IHHproj in H4; try easy.
    rewrite H4.
    destruct H. subst.
    apply H1 in H0; try easy.
    rewrite H0.
    easy.
Qed.

Lemma step_branches_preserves_nodup :
  forall act bs bs',
    step_branches act bs bs' ->
    NoDup (map fst bs) ->
    NoDup (map fst bs').
Proof. intros.
       apply step_branches_preserves_labels in H.
       rewrite H. easy.
Qed.

Definition P_g_sel (G : gtype) (act : gaction) (G' : gtype) :=
  forall p q l Ss Bs Se1a Se2a,
    act = act_sel p q l ->
    project p G = Some (t_SelectTy q Ss) ->
    project q G = Some (t_BranchTy p Bs) ->
    lookup_branch l Ss = Some Se1a ->
    lookup_branch l Bs = Some Se2a ->
    project p G' = Some Se1a /\
    project q G' = Some Se2a /\
    (forall r S_old,
       r <> p ->
       r <> q ->
       project r G = Some S_old ->
       project r G' = Some S_old).

Definition P_b_sel
  (act : gaction)
  (bs bs' : list (string * gtype)) :=
  forall r1 r2 l Ss Bs Se1a Se2a,
    act = act_sel r1 r2 l ->
    (forall lbl G,
        In (lbl, G) bs ->
        project r1 G = Some (t_SelectTy r2 Ss) /\
        project r2 G = Some (t_BranchTy r1 Bs)) ->
    lookup_branch l Ss = Some Se1a ->
    lookup_branch l Bs = Some Se2a ->
    Forall2
      (fun '(lbl, G) '(lbl', G') =>
         lbl = lbl' /\
         project r1 G' = Some Se1a /\
         project r2 G' = Some Se2a /\
         (forall r S_old,
            r <> r1 ->
            r <> r2 ->
            project r G = Some S_old ->
            project r G' = Some S_old))
      bs bs'.

Lemma step_preserves_project_sel_mutual :
  (forall G act G', step_gtype G act G' -> P_g_sel G act G') /\
  (forall act bs bs', step_branches act bs bs' -> P_b_sel act bs bs').
Proof.  apply step_mutind.
        7:{
        unfold P_g_sel, P_b_sel in *.
        intros. 
        inversion H0. subst.
        rename p0 into r1.
        rename q0 into r2.

        simpl in H1, H2.
        unfold disjoint_roles in d.
        assert((r1 =? p)%string = false).
        { apply String.eqb_neq. easy. }
        assert((r1 =? q)%string = false).
        { apply String.eqb_neq. easy. }
        assert((r2 =? p)%string = false).
        { apply String.eqb_neq. easy. }
        assert((r2 =? q)%string = false).
        { apply String.eqb_neq. easy. }
        rewrite H5, H6 in H1.
        rewrite H7, H8 in H2.
        simpl.
        rewrite H5, H6, H7, H8.
        split.
        - rewrite go_unfold_eq in H1, H2.
          rewrite go_unfold_eq.
          destruct (project_choice_go r1 branches) as [l |] eqn:Hgo.
          2: discriminate H1.
          destruct l as [| [lbl0 Se0] Ss0].
          1: discriminate H1.
          apply project_choice_go_some in Hgo.
          destruct (project_choice_go r2 branches) as [l |] eqn:Hgo1.
          2: discriminate H2.
          destruct l as [| [lbl1 Se1] Ss1].
          1: discriminate H2.
          apply project_choice_go_some in Hgo1.
          case_eq(forallb (fun '(_, S') => term_eqb Se0 S') Ss0); intros.
          rewrite H9 in H1.
          inversion H1. subst.
          case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
          rewrite H10 in H2.
          inversion H2. subst.
          inversion Hgo. subst.
          inversion Hgo1. subst.
          destruct x.
          destruct H14 as (H14,Ha).
          destruct H16 as (H16,Hb).
          subst.
          inversion g. subst.
          clear H14 H16 H19 H20.
          rename H17 into Hndup.
          simpl in Hndup.
          specialize(H r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
          assert(
           (forall (lbl : string) (G : gtype),
             In (lbl, G) ((lbl1, g0) :: l) -> project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
          ).
          {
            intros.
            simpl in H11.
            destruct H11. inversion H11. subst. easy.
            apply Forall2_proj_In with (lbl := lbl) (G := G) in H15.
            destruct H15 as (Se1,(Ha1,Hb1)).
            apply Forall2_proj_In with (lbl := lbl) (G := G) in H18.
            destruct H18 as (Se2,(Ha2,Hb2)).
            rewrite forallb_forall in H9,H10.
            specialize(H9 (lbl,Se1) Ha1).
            cbn in H9.
            destruct Se1; try easy.
            specialize(H10 (lbl,Se2) Ha2).
            cbn in H10.
            destruct Se2; try easy.
            apply andb_true_iff in H9, H10.
            destruct H9 as (H9a,H9b).
            destruct H10 as (H10a,H10b).
            apply term_br_eqb_eq in H9b, H10b. subst.
            apply String.eqb_eq in H9a,H10a. subst.
            easy.
            easy.
            easy.
         }
          specialize(H H11).
          destruct (project_choice_go r1 branches') as [l1 |] eqn:Hgo2.
          destruct l1. 
          apply project_choice_go_some in Hgo2.
          inversion Hgo2. subst. inversion s.
          destruct p0.
          apply project_choice_go_some in Hgo2.
          inversion Hgo2. subst.
          destruct x.
          destruct H16 as (H16,Hc).
          subst. 
          assert (t = Se1a).
          {
            specialize (H H3 H4).
            inversion H.
            subst.
            destruct H16. subst.
            destruct H13. rewrite Hc in H12.
            inversion H12. easy.
          }
          subst Se1a.
          specialize(H H3 H4).
          assert (Hunif :
            forall lbl G,
              In (lbl,G) ((s0,g1)::l2) ->
              project r1 G = Some t).
          {   intros lbl G HinG.
              simpl in HinG.
              destruct HinG as [HinG | HinG].
              + inversion HinG. subst.
                inversion H. subst. easy.
              + inversion H. subst.
                destruct H16. subst.
                apply Forall2_In_right with (y := (lbl, G)) in H20.
                destruct H20 as [x [Hin_left HR]].
                destruct x.
                easy.
                easy.
          }
          assert (Hunif2 :
            forall lbl Se,
              In (lbl,Se) ((s0, t) :: l1) ->
              Se = t).
          {
            eapply Forall2_uniform_projection.
            - exact Hgo2.
            - exact Hunif.
          }
          assert (Hforall :
            forallb (fun '(_, S') => term_eqb t S') l1 = true).
          {
            rewrite forallb_forall.
            intros [lbl Se] Hin.
            specialize (Hunif2 lbl Se).
            assert (In (lbl,Se) ((s0,t)::l1)).
            {
              right. exact Hin.
            }
            specialize (Hunif2 H12).
            subst.
            apply term_eqb_refl.
          } 
          rewrite Hforall. easy.

           assert (Hall :
            forall lbl G',
              In (lbl,G') branches' ->
              project r1 G' = Some Se1a).
          {
            intros lbl G' Hin.

            assert (Hlookup :
              lookup_gbranch lbl branches' = Some G').
            {
              apply lookup_gbranch_in; auto.
              inversion s. subst.
              simpl.
              inversion Hndup.
              subst.
              constructor.
              specialize(step_branches_preserves_labels _ _ _ H20); intros HH.
              rewrite HH.
              easy.
              eapply step_branches_preserves_nodup; eauto.
            }
            specialize (H H3 H4).
            inversion H. subst. destruct y.
            simpl in Hin.
            destruct Hin. inversion H12. subst. easy.
            apply Forall2_In_right with (y := (lbl, G')) in H17.
            destruct H17. destruct x.
            easy. easy.
          }

          destruct (project_choice_go_all_some r1 branches' Se1a Hall)
            as [Ssu Hsome].

          rewrite Hgo2 in Hsome.
          discriminate.

          rewrite H10 in H2. easy.
          rewrite H9 in H1. easy.
        - split.
          + rewrite go_unfold_eq in H1, H2.
            rewrite go_unfold_eq.
            destruct (project_choice_go r1 branches) as [l |] eqn:Hgo.
            2: discriminate H1.
            destruct l as [| [lbl0 Se0] Ss0].
            1: discriminate H1.
            apply project_choice_go_some in Hgo.
            destruct (project_choice_go r2 branches) as [l |] eqn:Hgo1.
            2: discriminate H2.
            destruct l as [| [lbl1 Se1] Ss1].
            1: discriminate H2.
            apply project_choice_go_some in Hgo1.
            case_eq(forallb (fun '(_, S') => term_eqb Se0 S') Ss0); intros.
            rewrite H9 in H1.
            inversion H1. subst.
            case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
            rewrite H10 in H2.
            inversion H2. subst.
            inversion Hgo. subst.
            inversion Hgo1. subst.
            destruct x.
            destruct H14 as (H14,Ha).
            destruct H16 as (H16,Hb).
            subst.
            inversion g. subst.
            clear H14 H16 H19 H20.
            rename H17 into Hndup.
            simpl in Hndup.
            specialize(H r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
            assert(
             (forall (lbl : string) (G : gtype),
               In (lbl, G) ((lbl1, g0) :: l) -> project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
            ).
            {
              intros.
              simpl in H11.
              destruct H11. inversion H11. subst. easy.
              apply Forall2_proj_In with (lbl := lbl) (G := G) in H15.
              destruct H15 as (Se1,(Ha1,Hb1)).
              apply Forall2_proj_In with (lbl := lbl) (G := G) in H18.
              destruct H18 as (Se2,(Ha2,Hb2)).
              rewrite forallb_forall in H9,H10.
              specialize(H9 (lbl,Se1) Ha1).
              cbn in H9.
              destruct Se1; try easy.
              specialize(H10 (lbl,Se2) Ha2).
              cbn in H10.
              destruct Se2; try easy.
              apply andb_true_iff in H9, H10.
              destruct H9 as (H9a,H9b).
              destruct H10 as (H10a,H10b).
              apply term_br_eqb_eq in H9b, H10b. subst.
              apply String.eqb_eq in H9a,H10a. subst.
              easy.
              easy.
              easy.
           }
            specialize(H H11).
            destruct (project_choice_go r2 branches') as [l1 |] eqn:Hgo2.
            destruct l1. 
            apply project_choice_go_some in Hgo2.
            inversion Hgo2. subst. inversion s.
            destruct p0.
            apply project_choice_go_some in Hgo2.
            inversion Hgo2. subst.
            destruct x.
            destruct H16 as (H16,Hc).
            subst. 
            assert (t = Se2a).
            {
              specialize (H H3 H4).
              inversion H.
              subst.
              destruct H16. subst.
              destruct H13. destruct H13. rewrite Hc in H13.
              inversion H13. easy.
            }
            subst Se2a.
            specialize(H H3 H4).
            assert (Hunif :
              forall lbl G,
                In (lbl,G) ((s0,g1)::l2) ->
                project r2 G = Some t).
            {   intros lbl G HinG.
                simpl in HinG.
                destruct HinG as [HinG | HinG].
                + inversion HinG. subst.
                  inversion H. subst. easy.
                + inversion H. subst.
                  destruct H16. subst.
                  apply Forall2_In_right with (y := (lbl, G)) in H20.
                  destruct H20 as [x [Hin_left HR]].
                  destruct x.
                  easy.
                  easy.
            }
            assert (Hunif2 :
              forall lbl Se,
                In (lbl,Se) ((s0, t) :: l1) ->
                Se = t).
            {
              eapply Forall2_uniform_projection.
              - exact Hgo2.
              - exact Hunif.
            }
            assert (Hforall :
              forallb (fun '(_, S') => term_eqb t S') l1 = true).
            {
              rewrite forallb_forall.
              intros [lbl Se] Hin.
              specialize (Hunif2 lbl Se).
              assert (In (lbl,Se) ((s0,t)::l1)).
              {
                right. exact Hin.
              }
              specialize (Hunif2 H12).
              subst.
              apply term_eqb_refl.
            } 
            rewrite Hforall. easy.

             assert (Hall :
              forall lbl G',
                In (lbl,G') branches' ->
                project r2 G' = Some Se2a).
            {
              intros lbl G' Hin.

              assert (Hlookup :
                lookup_gbranch lbl branches' = Some G').
              {
                apply lookup_gbranch_in; auto.
                inversion s. subst.
                simpl.
                inversion Hndup.
                subst.
                constructor.
                specialize(step_branches_preserves_labels _ _ _ H20); intros HH.
                rewrite HH.
                easy.
                eapply step_branches_preserves_nodup; eauto.
              }
              specialize (H H3 H4).
              inversion H. subst. destruct y.
              simpl in Hin.
              destruct Hin. inversion H12. subst. easy.
              apply Forall2_In_right with (y := (lbl, G')) in H17.
              destruct H17. destruct x.
              easy. easy.
            }

            destruct (project_choice_go_all_some r2 branches' Se2a Hall)
              as [Ssu Hsome].

            rewrite Hgo2 in Hsome.
            discriminate.
            
            rewrite H10 in H2. easy.
            rewrite H9 in H1. easy.
          + intros.
            case_eq((r =? p)%string); intros.
            rewrite H12 in H11.
            apply String.eqb_eq in H12. subst.
            rewrite go_unfold_eq in H1, H2, H11.
            rewrite go_unfold_eq.
            unfold option_map.
            unfold option_map in H11.
              destruct (project_choice_go p branches) as [l |] eqn:Hgo.
              inversion H11. subst.
              apply project_choice_go_some in Hgo.
              simpl.
              destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
              destruct l1 as [| [lbl1 Se1] Ss1].
              1: discriminate H1.
              apply project_choice_go_some in Hgo1.
              destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
              destruct l2 as [| [lbl2 Se2] Ss2].
              1: discriminate H2.
              apply project_choice_go_some in Hgo2.
              inversion Hgo1. subst.
              inversion Hgo2. subst.
              destruct x.
              destruct H15. subst.
              destruct H17. subst.
              specialize(H r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
              assert(
              (forall (lbl : string) (G : gtype),
   In (lbl, G) ((lbl2, g0) :: l1) -> project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
              ).
              { intros. simpl in H12.
                case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
                rewrite H15 in H1.
                inversion H1. subst.
                case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
                rewrite H17 in H2.
                inversion H2. subst.
                destruct H12. inversion H12. subst.
                easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H16; try easy.
                destruct H16 as (Sea,(H16a,H16b)).
                rewrite forallb_forall in H15.
                specialize(H15 (lbl,Sea) H16a). cbn in H15.
                destruct Sea; try easy.
                apply Forall2_proj_In with (lbl := lbl) (G := G) in H19; try easy.
                destruct H19 as (Sea,(H19a,H19b)).
                rewrite forallb_forall in H17.
                specialize(H17 (lbl,Sea) H19a). cbn in H17.
                destruct Sea; try easy.
                apply andb_true_iff in H15, H17.
                destruct H15 as (H15a,H15b).
                destruct H17 as (H17a,H17b).
                apply String.eqb_eq in H15a,H17a.
                apply term_br_eqb_eq in H15b,H17b.
                subst. easy.
                rewrite H17 in H2. easy.
                rewrite H15 in H1. easy.
              }
              specialize(H H12).
              inversion Hgo. subst.
              destruct y. destruct H18. subst.
              specialize(H H3 H4).
              inversion H. subst.
              cbn.
              destruct y. 
              destruct H20 as (Ha,(Hb,(Hc,Hd))). subst.
              apply Hd in H17; try easy.
              rewrite H17.
              specialize(project_choice_go_context_preserved_c p r1 r2 l1 l' l'0 Se1a Se2a H9 H10 H21); intro HH.
              rewrite HH. easy.
              easy.
              easy.
              easy. easy.
              
              rewrite H12 in H11.
              case_eq((r =? q)%string); intros.
              rewrite H13 in H11.
              rewrite String.eqb_eq in H13. subst.
              rewrite go_unfold_eq in H1, H2, H11.
              rewrite go_unfold_eq.
              unfold option_map.
              unfold option_map in H11.
                  destruct (project_choice_go q branches) as [l |] eqn:Hgo.
                  inversion H11. subst.
                  apply project_choice_go_some in Hgo.
                  simpl.
                  destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
                  destruct l1 as [| [lbl1 Se1] Ss1].
                  1: discriminate H1.
                  apply project_choice_go_some in Hgo1.
                  destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
                  destruct l2 as [| [lbl2 Se2] Ss2].
                  1: discriminate H2.
                  apply project_choice_go_some in Hgo2.
                  inversion Hgo1. subst.
                  inversion Hgo2. subst.
                  destruct x.
                  destruct H16. subst.
                  destruct H18. subst.
                  specialize(H r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
                  assert(
                  (forall (lbl : string) (G : gtype),
       In (lbl, G) ((lbl2, g0) :: l1) -> project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
                  ).
                  { intros. simpl in H12.
                    case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
                    rewrite H16 in H1.
                    inversion H1. subst.
                    case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
                    rewrite H18 in H2.
                    inversion H2. subst.
                    destruct H13. inversion H13. subst.
                    easy.
                    apply Forall2_proj_In with (lbl := lbl) (G := G) in H17; try easy.
                    destruct H17 as (Sea,(H17a,H17b)).
                    rewrite forallb_forall in H16.
                    specialize(H16 (lbl,Sea) H17a). cbn in H16.
                    destruct Sea; try easy.
                    apply Forall2_proj_In with (lbl := lbl) (G := G) in H20; try easy.
                    destruct H20 as (Sea,(H20a,H20b)).
                    rewrite forallb_forall in H18.
                    specialize(H18 (lbl,Sea) H20a). cbn in H18.
                    destruct Sea; try easy.
                    apply andb_true_iff in H16, H18.
                    destruct H16 as (H16a,H16b).
                    destruct H18 as (H18a,H18b).
                    apply String.eqb_eq in H16a,H18a.
                    apply term_br_eqb_eq in H16b,H18b.
                    subst. easy.
                    rewrite H18 in H2. easy.
                    rewrite H16 in H1. easy.
                  }
                  specialize(H H13).
                  inversion Hgo. subst.
                  destruct y. destruct H19. subst.
                  specialize(H H3 H4).
                  inversion H. subst.
                  cbn.
                  destruct y. 
                  destruct H21 as (Ha,(Hb,(Hc,Hd))). subst.
                  apply Hd in H18; try easy.
                  rewrite H18.
                  specialize(project_choice_go_context_preserved_c q r1 r2 l1 l' l'0 Se1a Se2a H9 H10 H22 H24); intro HH.
                  rewrite HH. easy.
                  easy.
                  easy.
                  easy.
                  
                  rewrite H13 in H11.
                  rewrite go_unfold_eq in H1, H2, H11.
                  rewrite go_unfold_eq.
                  unfold option_map.
                  unfold option_map in H11.
                      destruct (project_choice_go r branches) as [l |] eqn:Hgo.
                      destruct l as [| [lbl0 Se0] Ss0].
                      1: discriminate H11.
                      case_eq(forallb (fun '(_, S') => term_eqb Se0 S') Ss0); intros.
                      rewrite H14 in H11.
                      inversion H11. subst.
                      apply project_choice_go_some in Hgo.
                      simpl.
                      destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
                      destruct l1 as [| [lbl1 Se1] Ss1].
                      1: discriminate H1.
                      apply project_choice_go_some in Hgo1.
                      destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
                      destruct l2 as [| [lbl2 Se2] Ss2].
                      1: discriminate H2.
                      apply project_choice_go_some in Hgo2.
                      inversion Hgo1. subst.
                      inversion Hgo2. subst.
                      destruct x.
                      destruct H18. subst.
                      destruct H20. subst.
                      specialize(H r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
                      assert(
                        (forall (lbl : string) (G : gtype),
                           In (lbl, G) ((lbl2, g0) :: l) ->
                           project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
                      ).
                      { intros. simpl in H15.
                        case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
                        rewrite H18 in H2. inversion H2. subst.
                        case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
                        rewrite H20 in H1. inversion H1. subst.
                        
                        destruct H15 as [H15 | H15].
                        inversion H15. subst.
                        inversion Hgo. subst.
                        destruct H25. subst. easy.
                        
                        apply Forall2_proj_In with (lbl := lbl) (G := G) in H22.
                        destruct H22 as (Sea,(H22a,H22b)).
                        rewrite forallb_forall in H18.
                        specialize(H18 (lbl,Sea) H22a).
                        cbn in H18.
                        destruct Sea; try easy.
                        apply Forall2_proj_In with (lbl := lbl) (G := G) in H19.
                        destruct H19 as (Sea,(H19a,H19b)).
                        rewrite forallb_forall in H20.
                        specialize(H20 (lbl,Sea) H19a).
                        cbn in H20.
                        destruct Sea; try easy.
                        apply andb_true_iff in H18, H20.
                        destruct H18 as (H18a,H18b).
                        destruct H20 as (H20a,H20b).
                        apply String.eqb_eq in H18a,H20a.
                        apply term_br_eqb_eq in H18b,H20b.
                        subst. easy.
                        easy. easy.
                        rewrite H20 in H1. easy.
                        rewrite H18 in H2. easy.
                      }
                      specialize(H H15).
                      inversion Hgo. subst.
                      destruct H23. subst.
                      specialize(H H3 H4).
                      inversion H. subst.
                      cbn.
                      destruct y. 
                      destruct H23 as (Ha,(Hb,(Hc,Hd))). subst.
                      apply Hd in H20; try easy.
                      rewrite H20.
                      specialize(project_choice_go_context_preserved_c r r1 r2 l Ss0 l' Se1a Se2a H9 H10 H25 H26); intro HH.
                      rewrite HH, H14. easy.
                      easy. easy.
                      rewrite H14 in H11. easy.
                      easy.
     }
   6:{ unfold P_g_sel. intros.
       subst.
       simpl in H0, H1.
       destruct(project p z).
       destruct(project p s). easy.
       easy.
       easy.
     }
   5:{ unfold P_g_sel. intros.
       subst.
       simpl in H0, H1.
       destruct(project p z).
       destruct(project p s). easy.
       easy.
       easy.
     }
   4:{ unfold P_b_sel, P_g_sel.
       intros.
       inversion H0.
     }
   3:{ unfold P_b_sel, P_g_sel.
       intros.
       inversion H0.
     }
   2:{ unfold P_b_sel, P_g_sel.
       intros.
       inversion H.
       subst.
       inversion g. subst.
       rename p0 into r1.
       rename q0 into r2.
       apply String.eqb_neq in H7.
       simpl in H0, H1.
       assert((r2 =? r1)%string = false).
       { apply String.eqb_neq.
         apply String.eqb_neq in H7.
         easy.
       }
       rewrite String.eqb_refl in H0, H1.
       rewrite H4 in H1.
       rewrite go_unfold_eq in H0, H1.
       unfold option_map in H0, H1.
       case_eq(project_choice_go r1 branches); intros.
       rewrite H5 in H0. inversion H0. subst.
       case_eq(project_choice_go r2 branches); intros.
       rewrite H6 in H1.
       inversion H1. subst.
       apply project_choice_go_some in H5, H6.
       pose proof H5 as H5Back.
       apply Forall2_proj_In with (lbl := l0) (G := G') in H5.
       destruct H5 as (s1,(H5a,H5b)).
       apply Forall2_preserves_NoDup_labels_project in H5Back.
       assert(s1 = Se1a).
       { specialize (lookup_branch_same Ss l0 Se1a s1 H5Back H2 H5a); intros.
         easy.
       }
       subst.
       pose proof H6 as H6Back.
       apply Forall2_proj_In with (lbl := l0) (G := G') in H6.
       destruct H6 as (s2,(H6a,H6b)).
       apply Forall2_preserves_NoDup_labels_project in H6Back.
       assert(s2 = Se2a).
       { specialize (lookup_branch_same Bs l0 Se2a s2 H6Back H3 H6a); intros.
         easy.
       }
       subst.
       split. easy. split. easy.
       intros.
       simpl in H12.
       apply String.eqb_neq in H5, H6.
       rewrite H5, H6 in H12.
       rewrite go_unfold_eq in H12.
       case_eq(project_choice_go r branches); intros.
       rewrite H13 in H12.
       destruct l. easy.
       destruct p.
       case_eq(forallb (fun '(_, S') => term_eqb t S') l); intros.
       rewrite H14 in H12. inversion H12. subst.
       apply project_choice_go_some in H13.
       inversion H13. subst.
       destruct x. destruct H18. subst.

        assert (Hunif :
          forall lbl G,
            In (lbl,G) l1 ->
            project r G = Some S_old).
        {
          intros lbl G Hin.

          (* Find matching element in l *)
          apply Forall2_proj_In with (lbl := lbl) (G := G) in H19; try easy.

          destruct H19 as [y [Hin_l HR]].
          rewrite forallb_forall in H14.
          specialize(H14 (lbl,y) Hin_l).
          cbn in H14.
          apply term_eqb_eq in H14. subst.
          easy.
        }
        destruct (String.eqb l0 s) eqn:Heq.
        ++ apply String.eqb_eq in Heq.
           subst.
           simpl in e.
           rewrite String.eqb_refl in e.
           inversion e; subst.
           exact H16.
        ++ simpl in e.
           rewrite Heq in e.
           assert (Hin : In (l0, G') l1).
           { apply lookup_gbranch_In. easy. }
           eapply Hunif; eauto.
        ++ rewrite H14 in H12. easy.
        ++ rewrite H13 in H12. easy.
        ++ easy.
        ++ apply lookup_gbranch_In. easy.
        ++ easy.
        ++ apply lookup_gbranch_In. easy.
        ++ rewrite H6 in H1. easy.
        ++ rewrite H5 in H0. easy.
    }
  1:{ unfold P_b_sel, P_g_sel.
      intros.
      inversion H.
    }
   1:{ unfold P_b_sel, P_g_sel.
       intros. subst.
       constructor.
     }
  1:{ unfold P_b_sel, P_g_sel.
      intros. subst.
      constructor.
      - split. easy.
        apply H with (l := l0) (Ss := Ss) (Bs:= Bs); try easy.
        specialize (H0 r1 r2 l0 Ss Bs Se1a Se2a eq_refl).
        assert (Hin : In (l, G) ((l, G) :: bs)).
        { left; reflexivity. }

        specialize (H2 l G Hin).
        easy.
        assert (Hin : In (l, G) ((l, G) :: bs)).
        { left; reflexivity. }

        specialize (H2 l G Hin).
        easy.
      - assert(
        (forall (lbl : string) (G : gtype),
   In (lbl, G) bs -> project r1 G = Some (t_SelectTy r2 Ss) /\ project r2 G = Some (t_BranchTy r1 Bs)) 
        ).
        intros.
        apply H2 with (lbl := lbl).
        simpl. right. easy.
        specialize(H0 r1 r2 l0 Ss Bs Se1a Se2a eq_refl H1 H3 H4).
        apply H0.
     }
Qed.

Lemma step_gtype_preserves_project_sel :
  forall G act G',
    step_gtype G act G' ->
    forall p q l Ss Bs Se1a Se2a,
      act = act_sel p q l ->
      project p G = Some (t_SelectTy q Ss) ->
      project q G = Some (t_BranchTy p Bs) ->
      lookup_branch l Ss = Some Se1a ->
      lookup_branch l Bs = Some Se2a ->
      project p G' = Some Se1a /\
      project q G' = Some Se2a /\
      (forall r S_old,
         r <> p ->
         r <> q ->
         project r G = Some S_old ->
         project r G' = Some S_old).
Proof.
  intros G act G' Hstep.
  destruct step_preserves_project_sel_mutual as [H _].
  unfold P_g_sel in H.
  eapply H; eauto.
Qed.

Lemma step_branches_preserves_project_sel :
  forall act bs bs',
    step_branches act bs bs' ->
    forall r1 r2 l Ss Bs Se1a Se2a,
      act = act_sel r1 r2 l ->
      (forall lbl G,
          In (lbl, G) bs ->
          project r1 G = Some (t_SelectTy r2 Ss) /\
          project r2 G = Some (t_BranchTy r1 Bs)) ->
      lookup_branch l Ss = Some Se1a ->
      lookup_branch l Bs = Some Se2a ->
      Forall2
        (fun '(lbl, G) '(lbl', G') =>
           lbl = lbl' /\
           project r1 G' = Some Se1a /\
           project r2 G' = Some Se2a /\
           (forall r S_old,
              r <> r1 ->
              r <> r2 ->
              project r G = Some S_old ->
              project r G' = Some S_old))
        bs bs'.
Proof.
  intros act bs bs' Hstep.
  destruct step_preserves_project_sel_mutual as [_ H].
  unfold P_b_sel in H.
  eapply H; eauto.
Qed.

Lemma convertible_SendTy_inv :
  forall T r A S,
    convertible_n_par_ln T (t_SendTy r A S) ->
    exists A' S',
      T = t_SendTy r A' S' /\
      convertible_n_par_ln A' A /\
      convertible_n_par_ln S' S.
Admitted.

Lemma convertible_RecvTy_inv :
  forall T r A S,
    convertible_n_par_ln T (t_RecvTy r A S) ->
    exists A' S',
      T = t_RecvTy r A' S' /\
      convertible_n_par_ln A' A /\
      convertible_n_par_ln S' S.
Admitted.

Lemma convertible_SelectTy_inv_strong :
  forall T r bs,
    convertible_n_par_ln T (t_SelectTy r bs) ->
    exists bs',
      T = t_SelectTy r bs' /\
      Forall2
        (fun '(l1,S1) '(l2,S2) =>
           l1 = l2 /\ convertible_n_par_ln S1 S2)
        bs' bs.
Admitted.

Lemma convertible_BranchTy_inv_strong :
  forall T r bs,
    convertible_n_par_ln T (t_BranchTy r bs) ->
    exists bs',
      T = t_BranchTy r bs' /\
      Forall2
        (fun '(l1,S1) '(l2,S2) =>
           l1 = l2 /\ convertible_n_par_ln S1 S2)
        bs' bs.
Admitted.


Lemma project_msg_heads_agree :
  forall G r1 r2 A1 A2 S1 S2,
    gtype_wf G ->
    project r1 G = Some (t_SendTy r2 A1 S1) ->
    project r2 G = Some (t_RecvTy r1 A2 S2) ->
    A1 = A2.
Admitted.

Lemma project_SendTy_inv :
  forall G r1 r2 A S,
    project r1 G = Some (t_SendTy r2 A S) ->
    (exists G',
        G = g_msg r1 r2 A G')
    \/
    (exists p q branches lbl G0,
        G = g_choice p q branches /\
        r1 <> p /\
        r1 <> q /\
        In (lbl, G0) branches /\
        project r1 G0 = Some (t_SendTy r2 A S)).
Proof. intro G.
       induction G using gtype_ind_strong; intros.
       3:{
       simpl in H0.
       case_eq((r1 =? p)%string); intros.
       rewrite H1 in H0.
       rewrite String.eqb_eq in H1. subst.
       rewrite go_unfold_eq in H0.
       unfold option_map in H0.
       destruct(project_choice_go p branches); easy.
       rewrite H1 in H0.
       case_eq((r1 =? q)%string); intros.
       rewrite H2 in H0.
       rewrite String.eqb_eq in H2. subst.
       rewrite go_unfold_eq in H0.
       unfold option_map in H0.
       destruct(project_choice_go q branches); easy.
       rewrite H2 in H0.
       rewrite go_unfold_eq in H0.
       destruct (project_choice_go r1 branches) as [l |] eqn:Hgo.
       destruct l as [| [lbl Se] Ss].
       1: discriminate H0.
       case_eq(forallb (fun '(_, S') => term_eqb Se S') Ss); intros.
       rewrite H3 in H0. inversion H0.
       subst.
       apply project_choice_go_some in Hgo.
       inversion Hgo. subst.
       destruct x. destruct H7. subst.
       inversion H. subst.
       right.
       exists p, q, ((lbl, g) :: l), lbl, g.
       apply String.eqb_neq in H1, H2.
       split. easy. split. easy. split. easy.
       split. left. easy. easy.
       rewrite H3 in H0. easy.
       easy.
       }
       2:{
       simpl in H.
       case_eq((r1 =? p)%string); intros.
       rewrite H0 in H.
       rewrite String.eqb_eq in H0. subst.
       unfold option_map in H.
       case_eq(project p G); intros.
       rewrite H0 in H. inversion H. subst.
       left. exists G. easy.
       rewrite H0 in H. easy.
       rewrite H0 in H.
       case_eq((r1 =? q)%string); intros.
       rewrite H1 in H.
       rewrite String.eqb_eq in H1. subst.
       unfold option_map in H.
       case_eq(project q G); intros.
       rewrite H1 in H. inversion H.
       rewrite H1 in H. easy.
       rewrite H1 in H.
       unfold option_map in H.
       case_eq(project r1 G); intros.
       rewrite H2 in H. inversion H.
       rewrite H2 in H. easy.
       }
       2:{
       inversion H.
       destruct(project r1 G1); destruct(project r1 G2); easy.
       }
       1:{
       simpl in H. easy.
       }
       1:{
       simpl in H. easy.
       }
Qed.

Lemma project_RecvTy_inv :
  forall G r1 r2 A S,
    project r1 G = Some (t_RecvTy r2 A S) ->
    (exists G',
        G = g_msg r2 r1 A G')
    \/
    (exists p q branches lbl G0,
        G = g_choice p q branches /\
        r1 <> p /\
        r1 <> q /\
        In (lbl, G0) branches /\
        project r1 G0 = Some (t_RecvTy r2 A S)).
Proof. intro G.
       induction G using gtype_ind_strong; intros.
       3:{
       simpl in H0.
       case_eq((r1 =? p)%string); intros.
       rewrite H1 in H0.
       rewrite String.eqb_eq in H1. subst.
       rewrite go_unfold_eq in H0.
       unfold option_map in H0.
       destruct(project_choice_go p branches); easy.
       rewrite H1 in H0.
       case_eq((r1 =? q)%string); intros.
       rewrite H2 in H0.
       rewrite String.eqb_eq in H2. subst.
       rewrite go_unfold_eq in H0.
       unfold option_map in H0.
       destruct(project_choice_go q branches); easy.
       rewrite H2 in H0.
       rewrite go_unfold_eq in H0.
       destruct (project_choice_go r1 branches) as [l |] eqn:Hgo.
       destruct l as [| [lbl Se] Ss].
       1: discriminate H0.
       case_eq(forallb (fun '(_, S') => term_eqb Se S') Ss); intros.
       rewrite H3 in H0. inversion H0.
       subst.
       apply project_choice_go_some in Hgo.
       inversion Hgo. subst.
       destruct x. destruct H7. subst.
       inversion H. subst.
       right.
       exists p, q, ((lbl, g) :: l), lbl, g.
       apply String.eqb_neq in H1, H2.
       split. easy. split. easy. split. easy.
       split. left. easy. easy.
       rewrite H3 in H0. easy.
       easy.
       }
       2:{
       simpl in H.
       case_eq((r1 =? p)%string); intros.
       rewrite H0 in H.
       rewrite String.eqb_eq in H0. subst.
       unfold option_map in H.
       case_eq(project p G); intros.
       rewrite H0 in H. inversion H.
       rewrite H0 in H. easy.
       rewrite H0 in H.
       case_eq((r1 =? q)%string); intros.
       rewrite H1 in H.
       rewrite String.eqb_eq in H1. subst.
       unfold option_map in H.
       case_eq(project q G); intros.
       rewrite H1 in H. inversion H.
       subst.
       left. exists G. easy.
       rewrite H1 in H. easy.
       rewrite H1 in H.
       unfold option_map in H.
       case_eq(project r1 G); intros.
       rewrite H2 in H. inversion H.
       rewrite H2 in H. easy.
       }
       2:{
       inversion H.
       destruct(project r1 G1); destruct(project r1 G2); easy.
       }
       1:{
       simpl in H. easy.
       }
       1:{
       simpl in H. easy.
       }
Qed.

Lemma branch_projection_uniform :
  forall p q branches r lbl1 lbl2 G1 G2 S,
    gtype_wf (g_choice p q branches) ->
    r <> p ->
    r <> q ->
    In (lbl1, G1) branches ->
    In (lbl2, G2) branches ->
    project r G1 = Some S ->
    project r G2 = Some S.
Proof. intros.
       inversion H. subst.
       unfold third_party_consistent in H12.
       specialize(H12 r H0 H1).
       unfold branches_agree_for in *.
       destruct branches. easy.
       destruct p0.
       case_eq(project r g); intros.
       rewrite H5 in H12.
       simpl in H2.
       destruct H2. inversion H2. subst.
       rewrite H5 in H4. inversion H4. subst.
       simpl in H3. destruct H3. inversion H3. subst. easy.
       apply H12 with (lbl := lbl2); easy.
       apply H12 in H2. rewrite H2 in H4. inversion H4. subst.
       simpl in H3. destruct H3. inversion H3. subst. easy.
       apply H12 with (lbl := lbl2); easy.
       rewrite H5 in H12.
       easy.
Qed.

Lemma project_msg_implies_global_step :
  (forall G r1 r2 v A S1 S2,
     gtype_wf G ->
     value_ln v ->
     project r1 G = Some (t_SendTy r2 A S1) ->
     project r2 G = Some (t_RecvTy r1 A S2) ->
     exists G',
       step_gtype G (act_msg r1 r2 v) G').
Proof. intro G.
       induction G using gtype_ind_strong; intros.
       3:{
       simpl in H2, H3.
       case_eq((r1 =? p)%string); intros.
       rewrite H4 in H2.
       rewrite String.eqb_eq in H4. subst.
       case_eq((r2 =? p)%string); intros.
       rewrite H4 in H3.
       rewrite String.eqb_eq in H4. subst.
       rewrite go_unfold_eq in H2,H3.
       unfold option_map in H2,H3.
       destruct(project_choice_go p branches); easy.
       rewrite H4 in H3.
       case_eq((r2 =? q)%string); intros.
       rewrite H5 in H3.
       rewrite String.eqb_eq in H5. subst.
       unfold option_map in H2,H3.
       rewrite go_unfold_eq in H2,H3.
       destruct(project_choice_go p branches); easy.
       rewrite H5 in H3.
       rewrite go_unfold_eq in H2,H3.
       unfold option_map in H2,H3.
       destruct(project_choice_go p branches); easy.
       rewrite H4 in H2.
       case_eq((r1 =? q)%string); intros.
       rewrite H5 in H2.
       rewrite String.eqb_eq in H5. subst.
       case_eq((r2 =? p)%string); intros.
       rewrite H5 in H3.
       rewrite String.eqb_eq in H5. subst.
       unfold option_map in H2,H3.
       rewrite go_unfold_eq in H2,H3.
       destruct(project_choice_go p branches); easy.
       rewrite H5 in H3.
       case_eq((r2 =? q)%string); intros.
       rewrite H6 in H3.
       rewrite String.eqb_eq in H6. subst.
       unfold option_map in H2,H3.
       rewrite go_unfold_eq in H2,H3.
       destruct(project_choice_go q branches); easy.
       rewrite H6 in H3.
       rewrite go_unfold_eq in H2,H3.
       unfold option_map in H2,H3.
       destruct(project_choice_go q branches); easy.
       rewrite H5 in H2.
       case_eq((r2 =? p)%string); intros.
       rewrite H6 in H3.
       rewrite String.eqb_eq in H6. subst.
       unfold option_map in H2,H3.
       rewrite go_unfold_eq in H2,H3.
       destruct(project_choice_go p branches); easy.
       rewrite H6 in H3.
       case_eq((r2 =? q)%string); intros.
       rewrite H7 in H3.
       rewrite String.eqb_eq in H7. subst.
       unfold option_map in H2,H3.
       rewrite go_unfold_eq in H2,H3.
       destruct(project_choice_go q branches); easy.
       rewrite H7 in H3.
       rewrite go_unfold_eq in H2,H3.
       destruct (project_choice_go r1 branches) as [l1 |] eqn:Hgo1.
       destruct l1 as [| [lbl1 Se1] Ss1].
       1: discriminate H2.
       destruct (project_choice_go r2 branches) as [l2 |] eqn:Hgo2.
       destruct l2 as [| [lbl2 Se2] Ss2].
       1: discriminate H3.
       apply project_choice_go_some in Hgo1, Hgo2.
       inversion Hgo1. subst. 
       inversion Hgo2. subst.
       destruct x.
       destruct H11. subst.
       destruct H13. subst.
       inversion H. subst.
       case_eq(forallb (fun '(_, S') => term_eqb Se1 S') Ss1); intros.
       rewrite H8 in H2. inversion H2. subst.
       case_eq(forallb (fun '(_, S') => term_eqb Se2 S') Ss2); intros.
       rewrite H11 in H3. inversion H3. subst.
       inversion H0. subst.
       assert(In (lbl2, g) ((lbl2, g) :: l)).
       { left. easy. }
       specialize(H22 lbl2 g H16).
       specialize(H13 r1 r2 v A S1 S2 H22 H1 H9 H10).
       destruct H13 as [g' Hstep_head].
       assert (
          forall lbl G0,
            In (lbl,G0) l ->
            project r1 G0 = Some (t_SendTy r2 A S1)
            /\ project r2 G0 = Some (t_RecvTy r1 A S2)
        ).
       {
         intros.
         rewrite forallb_forall in H8, H11.
         apply Forall2_proj_In with (lbl := lbl) (G := G0) in H12.
         destruct H12 as (See,(H12a,H12b)).
         specialize(H8 (lbl, See) H12a).
         cbn in H8.
         destruct See; try easy.
         apply Forall2_proj_In with (lbl := lbl) (G := G0) in H15.
         destruct H15 as (See,(H15a,H15b)).
         specialize(H11 (lbl, See) H15a).
         cbn in H11.
         destruct See; try easy.
         apply andb_true_iff in H8, H11.
         destruct H8 as (H8a,H8b).
         destruct H11 as (H11a,H11b).
         apply andb_true_iff in H8a, H11a.
         destruct H8a as (H8a,H8c).
         destruct H11a as (H11a,H11c).
         apply term_eqb_eq in H8b, H8c, H11b, H11c.
         apply String.eqb_eq in H8a, H11a.
         subst. easy.
         easy. easy.
       }
       assert (exists l',
       step_branches (act_msg r1 r2 v) l l').
       {
        rename H21 into Hndup.
        clear (* H23 *) H16 (* H12 H15 *) H22 H20 Hgo1 Hgo2.
        revert H14 Ss1 Ss2 H12 H15 H8 H11.
        induction l as [| [lbl G] l IH]; intros.
        - exists [].
          constructor.
        - inversion H14. subst.
          inversion H12. subst.
          destruct y. destruct H21. subst.
          inversion H15. subst.
          destruct y. destruct H22. subst.
          apply IH with (Ss1 := l') (Ss2 := l'0)in H20; try easy.
          inversion H0. subst.
          assert(In (s0, G) ((s0, G) :: l) ). left. easy.
          specialize(H13 s0 G H16).
          destruct H13 as (H13a,H13b).
          assert(gtype_wf G).
          { inversion H0. subst.
            assert(In (s0, G) ((lbl2, g) :: (s0, G) :: l)).
            right. left. easy.
            specialize(H35 s0 G H13).
            apply H30 in H13. easy.
          }
          specialize(H18 r1 r2 v A S1 S2 H13 H1 H13a H13b).
          destruct H18 as (G',H18).
          destruct H20 as (l'',H20).
          exists(((s0, G') :: l'')).
          constructor; easy.
          inversion H.
          constructor. subst.
          easy.
          subst. inversion H27. easy.
          constructor; try easy.
          inversion Hndup as [| xa xsa Hnotin Hnodup_tail]; subst.
          simpl.
          constructor. unfold not.
          intros. apply Hnotin. 
          right. easy.
          inversion Hnodup_tail. easy.
          intros.
          inversion H0. subst.
          assert( In (lbl, G0) ((lbl2, g) :: (s0, G) :: l)).
          { simpl in H16. destruct H16.
            inversion H16. subst.
            left. easy.
            right. right. easy.
          }
          apply H31 in H22. easy.
          unfold third_party_consistent in *.
          intros.
          specialize(H23 r H16 H22).
          cbn. cbn in H23.
          destruct(project r g).
          intros.
          apply H23 with (lbl := lbl). right. easy.
          easy.
          inversion Hndup.
          subst.
          simpl. constructor.
          unfold not. intros.
          apply H25. right. easy.
          inversion H27. easy.
          inversion H0.
          subst.
          unfold third_party_consistent in *.
          intros.
          specialize(H23 r H16 H22).
          cbn. cbn in H23.
          destruct(project r g).
          intros.
          apply H23 with (lbl := lbl). right. easy.
          easy.
          intros.
          apply H13 with (lbl := lbl). right. easy.
          rewrite forallb_forall in H8.
          apply forallb_forall.
          intros.
          destruct x.
          specialize(H8 (s, t1)).
          apply H8. right. easy.
          rewrite forallb_forall in H11.
          apply forallb_forall.
          intros.
          destruct x.
          specialize(H11 (s, t1)).
          apply H11. right. easy.
          }
         destruct H17 as (l',H17).
         exists ( (g_choice p q ((lbl2, g') :: l'))).
         constructor. easy.
         unfold disjoint_roles.
         split.
         apply String.eqb_neq. easy.
         split.
         apply String.eqb_neq. easy.
         split.
         apply String.eqb_neq. easy.
         apply String.eqb_neq. easy.
         constructor. easy. easy.
         rewrite H11 in H3. easy.
         rewrite H8 in H2. easy.
         easy. easy.
       }
       2:{
       simpl in H1, H2.
       case_eq((r1 =? p)%string); intros.
       rewrite H3 in H1.
       rewrite String.eqb_eq in H3. subst.
       case_eq((r2 =? p)%string); intros.
       rewrite H3 in H2.
       unfold option_map in *.
       destruct(project r2 G); easy.
       rewrite H3 in H2.
       case_eq((r2 =? q)%string); intros.
       rewrite H4 in H2.
       rewrite String.eqb_eq in H4. subst.
       unfold option_map in *.
       case_eq(project q G); intros.
       rewrite H4 in H2. inversion H2. subst.
       case_eq( project p G); intros.
       rewrite H5 in H1.
       inversion H1. subst.
       exists (open_gtype v G). constructor.
       easy.
       rewrite H5 in H1. easy.
       rewrite H4 in H2. easy.
       rewrite H4 in H2.
       unfold option_map in *.
       destruct(project r2 G); easy.
       rewrite H3 in H1.
       case_eq((r1 =? q)%string); intros.
       rewrite H4 in H1.
       unfold option_map in *.
       destruct(project r1 G); easy.
       rewrite H4 in H1.
       unfold option_map in *.
       destruct(project r1 G); easy.
       }
       1:{
       inversion H1.
       }
       1:{
       simpl in H1, H2.
       destruct(project r1 G1); destruct(project r1 G2); easy.
       }
       1:{
       simpl in H1. easy.
       }
Qed.

Lemma open_local_proj_par_conv :
  forall t S v,
    par_conv_n_ln t S ->
    par_conv_n_ln (open_local_proj t v)
                  (open_local_proj S v).
Admitted.

Lemma open_local_proj_preserves_conv :
  forall t S v,
  convertible_n_par_ln t S ->
  convertible_n_par_ln (open_local_proj t v)
                       (open_local_proj S v).
Admitted.

Lemma project_select_implies_global_step :
  forall G p q l bs1 bs2 S,
    gtype_wf G ->
    project p G = Some (t_SelectTy q bs1) ->
    project q G = Some (t_BranchTy p bs2) ->
    lookup_branch l bs1 = Some S ->
    exists G',
      step_gtype G (act_sel p q l) G'.
Admitted.

Lemma lookup_branch_transport :
  forall bs branches l S,
    Forall2
      (fun '(l1,S1) '(l2,S2) =>
         l1 = l2 /\ convertible_n_par_ln S1 S2)
      bs branches ->
    lookup_branch l branches = Some S ->
    exists S',
      lookup_branch l bs = Some S' /\
      convertible_n_par_ln S' S.
Proof. intro l.
       induction l; intros.
       - inversion H. subst.
         simpl in H0. easy.
       - inversion H.
         subst.
         destruct a, y.
         destruct H3. subst.
         simpl in H0.
         case_eq((l0 =? s0)%string ); intros.
         rewrite H1 in H0.
         inversion H0. subst.
         rewrite String.eqb_eq in H1. subst.
         exists t. simpl.
         rewrite String.eqb_refl. split. easy. easy.
         rewrite H1 in H0.
         eapply IHl with (l := l0) (S := S) in H5.
         destruct H5 as (S',(H5a,H5b)).
         exists S'. split. simpl. rewrite H1. easy. easy.
         easy.
Qed.

Lemma local_global_simulation :
  forall s Δ Δ' P P' G,
    coherent_session s Δ G ->
    step_cfg_on s (cfg Δ P) (cfg Δ' P') ->
    exists act G',
      step_gtype G act G' /\
      coherent_session s Δ' G'.
Proof.  intros.
        remember (cfg Δ P) as c1.
        remember (cfg Δ' P') as c2.
        revert G Δ Δ' H Heqc1 Heqc2. revert P P'.
        rename H0 into H.
        induction H; intros.
        - subst. inversion Heqc2.
          subst. inversion Heqc1. subst.
          clear Heqc1 Heqc2.
          rename Δ0 into Δ.
          unfold coherent_session in *.
          destruct H5 as (Hb,(Hcan,Ha)).
          apply Ha in H, H0.
          destruct H as (st1,(Ha1,Hb1)).
          destruct H0 as (st2,(Ha2,Hb2)).
          assert(convertible_n_par_ln st1 (t_SendTy r2 A S1)).
          { apply rst_sym in Hb1. apply rst_trans with (y := T1); easy. }
          assert(convertible_n_par_ln st2 (t_RecvTy r1 A S2)).
          { apply rst_sym in Hb2. apply rst_trans with (y := T2); easy. }
          
          apply convertible_SendTy_inv in H.
          apply convertible_RecvTy_inv in H0.
          destruct H as (A1,(Sc1,(H1a,(H1b,H1c)))).
          destruct H0 as (A2,(Sc2,(H2a,(H2b,H2c)))).
          subst.
          specialize(project_msg_heads_agree G r1 r2 A1 A2 Sc1 Sc2 Hb Ha1 Ha2); intro HH.
          subst.
          
          specialize(project_msg_implies_global_step G r1 r2 v A2 Sc1 Sc2 Hb H3 Ha1 Ha2); intro HH.
          destruct HH as (G',HH).
          exists (act_msg r1 r2 v), G'.
          split. easy. 
          split.
          admit.
          split.
          admit.
          intros.
          specialize(step_gtype_preserves_project G (act_msg r1 r2 v) G' HH r1 r2 v A2 Sc1 Sc2 eq_refl Ha1 Ha2); intro HHH.
          unfold advance_session in *.
          case_eq(String.eqb r r1); intros.
          + rewrite String.eqb_eq in H0.
            unfold advance_session in H.
            rewrite LMFacts.mapi_o in H.
            unfold option_map in H.
            subst.
            rewrite String.eqb_refl in H.
            rewrite String.eqb_refl in H.
            case_eq(LM.find (elt:=term_ln) (s, r1) Δ); intros.
            rewrite H0 in H.
            inversion H. subst.
            exists (open_ln Sc1 v). split. easy.
            admit.
            rewrite H0 in H. easy.
            intros.
            destruct x, y. simpl in H4.
            destruct H4.
            subst. easy.
          + case_eq(String.eqb r r2); intros.
            ++ rewrite String.eqb_eq in H4.
               unfold advance_session in H.
               rewrite LMFacts.mapi_o in H.
               unfold option_map in H.
               subst.
               rewrite String.eqb_refl in H.
               rewrite String.eqb_refl in H.
               case_eq(LM.find (elt:=term_ln) (s, r2) Δ); intros.
               rewrite H0,H4 in H.
               inversion H. subst.
               exists (open_ln Sc2 v). split. easy.
               admit.
               rewrite H0,H4 in H. easy.
               intros.
               destruct x, y. simpl in H5.
               destruct H5.
               subst. easy.
            ++ unfold advance_session in H.
               rewrite LMFacts.mapi_o in H.
               rewrite String.eqb_refl in H.
               rewrite H0, H4 in H.
               unfold option_map in H.
               case_eq(LM.find (elt:=term_ln) (s, r) Δ); intros.
               rewrite H5 in H.
               inversion H. 
               apply Ha in H5.
               destruct H5 as (S,(H5a,H5b)).
               apply HHH in H5a; try easy.
               subst.
               exists (open_local_proj S v).
               split. easy.
               apply open_local_proj_preserves_conv. easy.
               apply String.eqb_neq. easy.
               apply String.eqb_neq. easy.
               rewrite H5 in H. easy.
               intros.
               destruct x, y. simpl in H5.
               destruct H5.
               subst. easy.
        - inversion Heqc2. subst.
          inversion Heqc1. subst.
          clear Heqc1 Heqc2.
          rename Δ0 into Δ.
          unfold coherent_session in *.
          destruct H6 as (Hb,(Hcan,Ha)).
          apply Ha in H, H0.
          destruct H as (st1,(Ha1,Hb1)).
          destruct H0 as (st2,(Ha2,Hb2)).
          assert(convertible_n_par_ln st1 (t_SelectTy q branches)).
          { apply rst_sym in Hb1. apply rst_trans with (y := T1); easy. }
          assert(convertible_n_par_ln st2 (t_BranchTy p branches)).
          { apply rst_sym in Hb2. apply rst_trans with (y := T2); easy. }

          apply convertible_SelectTy_inv_strong in H.
          apply convertible_BranchTy_inv_strong in H0.
          destruct H as (bs1,(Hc,Hd)).
          destruct H0 as (bs2,(He,Hf)).
          subst.

          apply lookup_branch_transport with (l := l) (S := S) in Hd.
          destruct Hd as (S1,(Hd1,Hd2)).
          apply lookup_branch_transport with (l := l) (S := S) in Hf.
          destruct Hf as (S2,(Hf1,Hf2)).
          specialize(project_select_implies_global_step G p q l bs1 bs2 S1 Hb Ha1 Ha2 Hd1); intro HH.
          destruct HH as (G',HH).
          exists (act_sel p q l) , G'.
          split. easy. 
          split.
          admit.
          split.
          admit.
          intros.
          
          specialize(step_gtype_preserves_project_sel G (act_sel p q l) G' HH p q l bs1 bs2 S1 S2 eq_refl Ha1 Ha2 Hd1 Hf1); intro HHH.
          case_eq(String.eqb r p); intros.
          rewrite String.eqb_eq in H0. subst.
          rewrite LMFacts.add_eq_o in H.
          inversion H. subst.
          exists S1. split. easy. apply rst_sym. easy.
          simpl. easy.
          case_eq(String.eqb r q); intros.
          rewrite String.eqb_eq in H5. subst.
          rewrite LMFacts.add_neq_o in H.
          rewrite LMFacts.add_eq_o in H.
          inversion H. subst.
          exists S2. split. easy. apply rst_sym. easy.
          simpl. easy. simpl.
          unfold not. intros. destruct H5. subst.
          rewrite String.eqb_refl in H0. easy.
          destruct HHH as (Hu,(Hv,Hy)).
          rewrite LMFacts.add_neq_o in H.
          rewrite LMFacts.add_neq_o in H.
          rewrite LMFacts.remove_neq_o in H.
          rewrite LMFacts.remove_neq_o in H.
          apply Ha in H.
          destruct H as (Snew,(Hn,Hm)).
          apply Hy in Hn.
          exists Snew. split. easy. easy.
          apply String.eqb_neq. easy.
          apply String.eqb_neq. easy.
          simpl. unfold not. intros. destruct H6. subst. 
          rewrite String.eqb_refl in H5. easy.
          simpl. unfold not. intros. destruct H6. subst. 
          rewrite String.eqb_refl in H0. easy.
          simpl. unfold not. intros. destruct H6. subst. 
          rewrite String.eqb_refl in H5. easy.
          simpl. unfold not. intros. destruct H6. subst. 
          rewrite String.eqb_refl in H0. easy.
          easy. easy.
Admitted.

