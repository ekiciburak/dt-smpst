Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.

(* De Bruijn representation - recommended for dependently typed calculi *)
Inductive term : Type :=
  | Star : term
  | Nat : term
  | Pi : term -> term -> term
  | Sigma : term -> term -> term
  | Zero : term
  | Succ : term -> term
  | Pair : term -> term -> term -> term -> term
  | Fst : term -> term
  | Snd : term -> term
  | Var : nat -> term
  | Lam : term -> term -> term
  | App : term -> term -> term
  | NatRec : term -> term -> term -> term -> term.
