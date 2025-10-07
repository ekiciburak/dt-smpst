Require Import Coq.Lists.List Coq.Init.Nat Lia.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

Inductive term : Type :=
  | Star : term
  | Nat : term
  | Pi : term -> term -> term
  | Sigma : term -> term -> term
  | Zero : term
  | Succ : term -> term
  | Pair : term -> term -> term -> term -> term
  | TFst : term -> term
  | TSnd : term -> term
  | Var : nat -> term
  | Lam : term -> term -> term
  | App : term -> term -> term
  | NatRec : term -> term -> term -> term -> term
  | Vec : term -> term -> term (* Vec n A *)
  | VNil   : term -> term 
  | VCons  : term -> term -> term -> term -> term   
  | VecRec : term -> term -> term -> term -> term -> term -> term.
  (* VecRec A P z s n xs
     Think of a dependent motive P over (n : Nat) and (xs : Vec n A).
     z is the base case (for empty), s is the step case. *)

(* ---------- Semantic domain: weak-head normal forms ---------- *)

Inductive whnf : Type :=
| VStar    : whnf
| VNat     : whnf
| VPi      : whnf -> closure -> whnf
| VSigma   : whnf -> closure -> whnf
| VLam     : closure -> whnf
| VPair    : whnf -> whnf -> whnf -> whnf -> whnf
| VZero    : whnf
| VSucc    : whnf -> whnf
| VNeutral : neutral -> whnf
| VVec    : whnf -> whnf -> whnf                 (* the family at (n, A) *)
| VNilV   : whnf -> whnf                         (* empty vector at A *)
| VConsV  : whnf -> whnf -> whnf -> whnf -> whnf (* cons A n x xs *)

with neutral : Type :=
| NVar     : nat -> neutral
| NApp     : neutral -> whnf -> neutral
| NFst     : neutral -> neutral
| NSnd     : neutral -> neutral
| NNatRec  : whnf -> whnf -> whnf -> neutral -> neutral
| NVecRec : whnf (*A*) -> whnf (*P*) -> whnf (*z*) -> whnf (*s*) -> whnf (*n*) -> neutral (*xs*) -> neutral

with closure : Type :=
| Cl : list whnf -> term -> closure.

Coercion VNeutral : neutral >-> whnf.


  
  