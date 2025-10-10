Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term.

Definition env := list whnf.
(* --------------------------------------------- *)
(* Capture-avoiding shift on TERMS (de Bruijn)   *)
(* shift_term d c t  : add d to any Var x with x >= c *)
(* --------------------------------------------- *)
Fixpoint shift_term (d c : nat) (t : term) : term :=
  match t with
  | Star        => Star
  | Nat         => Nat
  | Var x       => if Nat.leb c x then Var (x + d) else Var x

  | Pi A B      => Pi (shift_term d c A) (shift_term d (S c) B)
  | Sigma A B   => Sigma (shift_term d c A) (shift_term d (S c) B)

  | Lam A b     => Lam (shift_term d c A) (shift_term d (S c) b)
  | App t u     => App (shift_term d c t) (shift_term d c u)

  | Pair A B a b =>
      Pair (shift_term d c A) (shift_term d (S c) B) (shift_term d c a) (shift_term d c b)

  | TFst p      => TFst (shift_term d c p)
  | TSnd p      => TSnd (shift_term d c p)

  | Zero        => Zero
  | Succ n      => Succ (shift_term d c n)

  | NatRec P z s n =>
      NatRec (shift_term d c P) (shift_term d c z) (shift_term d c s) (shift_term d c n)

  | Vec n A     => Vec (shift_term d c n) (shift_term d c A)
  | VNil A      => VNil (shift_term d c A)
  | VCons A n x xs =>
      VCons (shift_term d c A) (shift_term d c n) (shift_term d c x) (shift_term d c xs)

  | VecRec A P z s n xs =>
      VecRec (shift_term d c A) (shift_term d c P) (shift_term d c z) (shift_term d c s)
             (shift_term d c n) (shift_term d c xs)
  end.

(* --------------------------------------------------------- *)
(* Single-hole substitution on TERMS at index c:             *)
(*   subst c u t    replaces Var c in t with u, adjusting    *)
(*   for binders via shift_term.                                 *)
(* Patterns:                                                 *)
(*  - x < c   : unchanged                                    *)
(*  - x = c   : replace by (shift_term c 0 u)                    *)
(*  - x > c   : decrement index (Var (x-1))                  *)
(* --------------------------------------------------------- *)
Fixpoint subst_term (c : nat) (u : term) (t : term) : term :=
  match t with
  | Star        => Star
  | Nat         => Nat
  | Var x       =>
      if Nat.ltb x c then Var x
      else if Nat.eqb x c then shift_term c 0 u
           else Var (x - 1)

  | Pi A B      => Pi (subst_term c u A) (subst_term (S c) u B)
  | Sigma A B   => Sigma (subst_term c u A) (subst_term (S c) u B)

  | Lam A b     => Lam (subst_term c u A) (subst_term (S c) u b)
  | App t1 t2   => App (subst_term c u t1) (subst_term c u t2)

  | Pair A B a b =>
      Pair (subst_term c u A) (subst_term (S c) u B) (subst_term c u a) (subst_term c u b)

  | TFst p      => TFst (subst_term c u p)
  | TSnd p      => TSnd (subst_term c u p)

  | Zero        => Zero
  | Succ n      => Succ (subst_term c u n)

  | NatRec P z s n =>
      NatRec (subst_term c u P) (subst_term c u z) (subst_term c u s) (subst_term c u n)

  | Vec n A     => Vec (subst_term c u n) (subst_term c u A)
  | VNil A      => VNil (subst_term c u A)
  | VCons A n x xs =>
      VCons (subst_term c u A) (subst_term c u n) (subst_term c u x) (subst_term c u xs)

  | VecRec A P z s n xs =>
      VecRec (subst_term c u A) (subst_term c u P) (subst_term c u z) (subst_term c u s)
             (subst_term c u n) (subst_term c u xs)
  end.
  

