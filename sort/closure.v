Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval.

(* ---------------------------------------------------------------- *)
(* 1) Closure application (relational wrapper around eval').         *)
(* ---------------------------------------------------------------- *)

(* A single fresh neutral you can reuse under binders *)
Definition fresh : whnf := VNeutral (NVar 0).

Definition cl_env  (c : closure) : list whnf :=
  match c with Cl ρ _ => ρ end.

Definition cl_body (c : closure) : term :=
  match c with Cl _ b => b end.

(* Closure application wrapper already defined earlier: *)

Definition clos_eval' (cl : closure) (v v' : whnf) : Prop :=
  match cl with
    | Cl ρ body => eval' (env_cons v ρ) body v' 
  end. 

(* You already had this combined scheme for eval/vapp/natrec *)
(* Scheme eval'_rect ... with vapp_rect ... with eval_natrec_rect ...
   Combined Scheme evalsys_rect from eval'_rect, vapp_rect, eval_natrec_rect. *)

Scheme whnf_recta := Induction for whnf Sort Prop.

(* ---------------------------------------------------------------- *)
(* 3) Bidirectional typing over a *semantic* context of WHNF types.  *)
(*    Γ : list whnf  (rightmost is Var 0).                           *)
(*    We use eval' with the identity env [id_env (length Γ)].        *)
(* ---------------------------------------------------------------- *)

(* -- algorithmic convertibility on WHNFs (non-mutual) ------------------- *)

Definition clos_eval_fuel (fuel : nat) (cl : closure) (v : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match cl with
    | Cl ρ t => evalk fuel' (env_cons v ρ) t
    end
  end.
  
Inductive conv_clo : closure -> closure -> Prop :=
| ConvClo : forall B B' v v',
    clos_eval' B  fresh v ->
    clos_eval' B' fresh v' ->
    conv v v' ->
    conv_clo B B'

with conv : whnf -> whnf -> Prop :=
| CoV_Star  : conv VStar VStar
| CoV_Nat   : conv VNat  VNat

| CoV_Pi : forall A A' B B',
    conv A A' ->
    conv_clo B B' ->
    conv (VPi A B) (VPi A' B')

| CoV_Sigma : forall A A' B B',
    conv A A' ->
    conv_clo B B' ->
    conv (VSigma A B) (VSigma A' B')

| CoV_Lam : forall cl1 cl2,
    conv_clo cl1 cl2 ->
    conv (VLam cl1) (VLam cl2)

| CoV_Pair : forall A B a b A' B' a' b',
    conv A A' -> conv B B' -> conv a a' -> conv b b' ->
    conv (VPair A B a b) (VPair A' B' a' b')

| CoV_Zero : conv VZero VZero
| CoV_Succ : forall n n', conv n n' -> conv (VSucc n) (VSucc n')

(* Neutral congruence, folded into conv *)
| CoV_NVar    : forall i,
    conv (VNeutral (NVar i)) (VNeutral (NVar i))
| CoV_NApp    : forall n n' v v',
    conv (VNeutral n) (VNeutral n') -> conv v v' ->
    conv (VNeutral (NApp n v)) (VNeutral (NApp n' v'))
| CoV_NFst    : forall n n',
    conv (VNeutral n) (VNeutral n') ->
    conv (VNeutral (NFst n)) (VNeutral (NFst n'))
| CoV_NSnd    : forall n n',
    conv (VNeutral n) (VNeutral n') ->
    conv (VNeutral (NSnd n)) (VNeutral (NSnd n'))
| CoV_NNatRec : forall P P' z z' s s' n n',
    conv P P' -> conv z z' -> conv s s' ->
    conv (VNeutral n) (VNeutral n') ->
    conv (VNeutral (NNatRec P z s n)) (VNeutral (NNatRec P' z' s' n'))

| CoV_Vec : forall n n' A A',
    conv n n' -> conv A A' ->
    conv (VVec n A) (VVec n' A')

| CoV_VNil : forall A A',
    conv A A' ->
    conv (VNilV A) (VNilV A')

| CoV_VCons : forall A A' n n' x x' xs xs',
    conv A A' -> conv n n' -> conv x x' -> conv xs xs' ->
    conv (VConsV A n x xs) (VConsV A' n' x' xs')

(* Neutral congruence for VecRec *)
| CoV_NVecRec : forall A A' P P' z z' s s' n n' nx nx',
    conv A A' -> conv P P' -> conv z z' -> conv s s' -> conv n n' ->
    conv (VNeutral nx) (VNeutral nx') ->
    conv (VNeutral (NVecRec A P z s n nx))
         (VNeutral (NVecRec A' P' z' s' n' nx')).


Scheme conv_ind'      := Induction for conv      Sort Prop
with conv_clo_ind'  := Induction for conv_clo  Sort Prop.
Combined Scheme conv_mutind from conv_ind', conv_clo_ind'.


Fixpoint conv_fuel (fuel:nat) (v w:whnf) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match v, w with
    | VStar, VStar => true
    | VNat,  VNat  => true
    | VPi A B, VPi A' B' =>
        if conv_fuel fuel' A A' then
          match clos_eval_fuel fuel' B fresh,
                clos_eval_fuel fuel' B' fresh with
          | Some vB, Some vB' => conv_fuel fuel' vB vB'
          | _, _ => false
          end
        else false
    | VSigma A B, VSigma A' B' =>
        if conv_fuel fuel' A A' then
          match clos_eval_fuel fuel' B fresh,
                clos_eval_fuel fuel' B' fresh with
          | Some vB, Some vB' => conv_fuel fuel' vB vB'
          | _, _ => false
          end
        else false
    | VLam cl1, VLam cl2 =>
        match clos_eval_fuel fuel' cl1 fresh,
              clos_eval_fuel fuel' cl2 fresh with
        | Some v1, Some v2 => conv_fuel fuel' v1 v2
        | _, _ => false
        end
    | VPair A B a b, VPair A' B' a' b' =>
        andb (conv_fuel fuel' A A')
             (andb (conv_fuel fuel' B B')
                   (andb (conv_fuel fuel' a a') (conv_fuel fuel' b b')))
    | VZero, VZero => true
    | VSucc n, VSucc n' => conv_fuel fuel' n n'
    | VNeutral n, VNeutral n' => conv_neutral_fuel fuel' n n'
    | VVec n A, VVec n' A' => andb (conv_fuel fuel' n n') (conv_fuel fuel' A A')

    | VNilV A, VNilV A' =>
        conv_fuel fuel' A A'

    | VConsV A n x xs, VConsV A' n' x' xs' =>
        andb (conv_fuel fuel' A A')
             (andb (conv_fuel fuel' n n')
                   (andb (conv_fuel fuel' x x')
                         (conv_fuel fuel' xs xs')))
    | _, _ => false
    end
  end
with conv_neutral_fuel (fuel : nat) (n n' : neutral) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match n, n' with
    | NVar i, NVar j => Nat.eqb i j

    | NApp n v, NApp n' v' =>
        andb (conv_neutral_fuel fuel' n n') (conv_fuel fuel' v v')

    | NFst n, NFst n' =>
        conv_neutral_fuel fuel' n n'

    | NSnd n, NSnd n' =>
        conv_neutral_fuel fuel' n n'

    | NNatRec P z s n, NNatRec P' z' s' n' =>
        andb (conv_fuel          fuel' P P')
         (andb (conv_fuel        fuel' z z')
          (andb (conv_fuel       fuel' s s')
                (conv_neutral_fuel fuel' n n')))

    (* NEW: VecRec neutral congruence *)
    | NVecRec A P z s n nx, NVecRec A' P' z' s' n' nx' =>
        andb (conv_fuel          fuel' A A')
         (andb (conv_fuel        fuel' P P')
          (andb (conv_fuel       fuel' z z')
           (andb (conv_fuel      fuel' s s')
            (andb (conv_fuel     fuel' n n')
                  (conv_neutral_fuel fuel' nx nx')))))

    | _, _ => false
    end
  end.

Scheme eval'_recta      := Induction for eval'       Sort Prop
with   vapp_recta        := Induction for vapp        Sort Prop
with   eval_natrec_recta := Induction for eval_natrec Sort Prop.
Combined Scheme evalsys_rect from eval'_rect, vapp_rect, eval_natrec_rect.

Definition clos_evalk (k:nat) (cl:closure) : option whnf :=
  match cl with Cl ρ body => evalk k (env_cons fresh ρ) body end.
  
  
