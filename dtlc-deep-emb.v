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

(* Section ManualMutualInduction_Prop.

Variable Pw : whnf -> Prop.
Variable Pn : neutral -> Prop.
Variable Pc : closure -> Prop.

(* Hypotheses for each constructor — exactly the premises you’d expect *)
Hypotheses
 (H_VStar   : Pw VStar)
 (H_VNat    : Pw VNat)
 (H_VPi     : forall A B, Pw A -> Pc B -> Pw (VPi A B))
 (H_VSigma  : forall A B, Pw A -> Pc B -> Pw (VSigma A B))
 (H_VLam    : forall cl, Pc cl -> Pw (VLam cl))
 (H_VPair   : forall A B a b, Pw A -> Pw B -> Pw a -> Pw b -> Pw (VPair A B a b))
 (H_VZero   : Pw VZero)
 (H_VSucc   : forall n, Pw n -> Pw (VSucc n))
 (H_VNeutral: forall n, Pn n -> Pw (VNeutral n))

 (H_NVar    : forall i, Pn (NVar i))
 (H_NApp    : forall n v, Pn n -> Pw v -> Pn (NApp n v))
 (H_NFst    : forall n, Pn n -> Pn (NFst n))
 (H_NSnd    : forall n, Pn n -> Pn (NSnd n))
 (H_NNatRec : forall P z s n, Pw P -> Pw z -> Pw s -> Pn n -> Pn (NNatRec P z s n))

 (* closure needs the semantic env list handled: we require [Forall Pw ρ] *)
 (H_Cl      : forall ρ t, Forall Pw ρ -> Pc (Cl ρ t)).

(* Helper to produce [Forall Pw ρ] by recursion over the list *)

(* Mutually recursive proofs for whnf / neutral / closure *)
Fixpoint whnf_proof (v : whnf) {struct v} : Pw v :=
  match v with
  | VStar            => H_VStar
  | VNat             => H_VNat
  | VPi A B          => H_VPi A B (whnf_proof A) (closure_proof B)
  | VSigma A B       => H_VSigma A B (whnf_proof A) (closure_proof B)
  | VLam cl          => H_VLam cl (closure_proof cl)
  | VPair A B a b    => H_VPair A B a b
                              (whnf_proof A) (whnf_proof B)
                              (whnf_proof a) (whnf_proof b)
  | VZero            => H_VZero
  | VSucc n          => H_VSucc n (whnf_proof n)
  | VNeutral n       => H_VNeutral n (neutral_proof n)
  end

with neutral_proof (n : neutral) {struct n} : Pn n :=
  match n with
  | NVar i           => H_NVar i
  | NApp n v         => H_NApp n v (neutral_proof n) (whnf_proof v)
  | NFst n           => H_NFst n (neutral_proof n)
  | NSnd n           => H_NSnd n (neutral_proof n)
  | NNatRec P z s n' => H_NNatRec P z s n'
                          (whnf_proof P) (whnf_proof z) (whnf_proof s)
                          (neutral_proof n')
  end

with closure_proof (c : closure) {struct c} : Pc c :=
  match c with
  | Cl ρ t =>
      (* Local list recursion to build [Forall Pw ρ] without adding
         a new mutually-recursive definition. *)
      let fix build (ρ0 : list whnf) : Forall Pw ρ0 :=
          match ρ0 with
          | []     => Forall_nil _
          | v :: r => Forall_cons _ (whnf_proof v) (build r)
          end
      in H_Cl ρ t (build ρ)
  end.

Theorem whnf_mutind :
  (forall v, Pw v) /\ (forall n, Pn n) /\ (forall c, Pc c).
Proof.
  split; [exact whnf_proof | split; [exact neutral_proof | exact closure_proof]].
Qed.

End ManualMutualInduction_Prop. *)

(* ---------------------------------------------------------------- *)
(* 0) Shifting for semantic neutrals/values, to maintain de Bruijn   *)
(*    discipline when we extend environments.                        *)
(* ---------------------------------------------------------------- *)

Fixpoint shift_neutral (d c : nat) (n : neutral) : neutral :=
  match n with
  | NVar k               => NVar (if Nat.leb c k then k + d else k)
  | NApp n v             => NApp (shift_neutral d c n) (shift_whnf d c v)
  | NFst n               => NFst (shift_neutral d c n)
  | NSnd n               => NSnd (shift_neutral d c n)
  | NNatRec P z s n0     => NNatRec (shift_whnf d c P) (shift_whnf d c z) (shift_whnf d c s) (shift_neutral d c n0)
  | NVecRec A P z s n xs => NVecRec (shift_whnf d c A) (shift_whnf d c P) (shift_whnf d c z) (shift_whnf d c s) (shift_whnf d c n) (shift_neutral d c xs)
  end
with shift_whnf (d c : nat) (v : whnf) : whnf :=
  match v with
  | VStar           => VStar
  | VNat            => VNat
  | VPi A B         => VPi (shift_whnf d c A)
                           (match B with Cl ρ b => Cl (map (shift_whnf d c) ρ) b end)
  | VSigma A B      => VSigma (shift_whnf d c A)
                              (match B with Cl ρ b => Cl (map (shift_whnf d c) ρ) b end)
  | VLam (Cl ρ b)   => VLam (Cl (map (shift_whnf d c) ρ) b)
  | VPair A B a b   => VPair (shift_whnf d c A) (shift_whnf d c B)
                             (shift_whnf d c a) (shift_whnf d c b)
  | VZero           => VZero
  | VSucc v1        => VSucc (shift_whnf d c v1)
  | VNeutral n      => VNeutral (shift_neutral d c n)
  | VVec n A        => VVec (shift_whnf d c n) (shift_whnf d c A)  (* <— here *)
  | VNilV A         => VNilV (shift_whnf d c A)
  | VConsV A n x xs => VConsV (shift_whnf d c A) (shift_whnf d c n) (shift_whnf d c x) (shift_whnf d c xs)
  end.

Coercion VNeutral : neutral >-> whnf.

Definition env := list whnf.

(* Push a new head value; shift older entries so de Bruijn indices line up. *)
Definition env_cons (v : whnf) (ρ : env) : env :=
  v :: map (shift_whnf 1 0) ρ.

(* Identity environment of length n (Var i ↦ Neutral (NVar i)). *)
Fixpoint id_env (n : nat) : env :=
  match n with
  | 0 => []
  | S k => VNeutral (NVar 0) :: map (shift_whnf 1 0) (id_env k)
  end.


(* ---------- Big-step evaluation (tidy, mutual) ---------- *)

(**
  eval' ρ t v      : under environment ρ, term t evaluates to value v (WHNF)
  vapp  v1 v2 v3   : semantic application (v1 v2) evaluates to v3 (β or neutral)
  eval_natrec vP vz vs vn v :
       semantic natrec with motive vP, base vz, step vs, on argument vn yields v
*)

(* ================================================================= *)
(* Mutual relational semantics, now including vapps and eval_vecrec. *)
(* ================================================================= *)

Inductive eval' : env -> term -> whnf -> Prop :=
| E'_Star  : forall ρ,
    eval' ρ Star VStar
| E'_Nat   : forall ρ,
    eval' ρ Nat VNat
| E'_Var_Some : forall ρ x v,
    nth_error ρ x = Some v ->
    eval' ρ (Var x) v
| E'_Var_None : forall ρ x,
    nth_error ρ x = None ->
    eval' ρ (Var x) (VNeutral (NVar x))
| E'_Pi : forall ρ A B vA,
    eval' ρ A vA ->
    eval' ρ (Pi A B) (VPi vA (Cl ρ B))
| E'_Sigma : forall ρ A B vA,
    eval' ρ A vA ->
    eval' ρ (Sigma A B) (VSigma vA (Cl ρ B))
| E'_Lam : forall ρ A b,
    eval' ρ (Lam A b) (VLam (Cl ρ b))
| E'_App : forall ρ t u vt vu v,
    eval' ρ t vt ->
    eval' ρ u vu ->
    vapp vt vu v ->
    eval' ρ (App t u) v
| E'_Pair : forall ρ A B a b vA vB va vb,
    eval' ρ A vA -> eval' ρ B vB ->
    eval' ρ a va -> eval' ρ b vb ->
    eval' ρ (Pair A B a b) (VPair vA vB va vb)
| E'_TFst_Pair : forall ρ p A B va vb,
    eval' ρ p (VPair A B va vb) ->
    eval' ρ (TFst p) va
| E'_TFst_Neut : forall ρ p n,
    eval' ρ p (VNeutral n) ->
    eval' ρ (TFst p) (VNeutral (NFst n))
| E'_TFst_Other : forall ρ p vp,
    eval' ρ p vp ->
    (forall A B va vb, vp <> VPair A B va vb) ->
    (forall n, vp <> VNeutral n) ->
    eval' ρ (TFst p) vp
| E'_TSnd_Pair : forall ρ p A B va vb,
    eval' ρ p (VPair A B va vb) ->
    eval' ρ (TSnd p) vb
| E'_TSnd_Neut : forall ρ p n,
    eval' ρ p (VNeutral n) ->
    eval' ρ (TSnd p) (VNeutral (NSnd n))
| E'_TSnd_Other : forall ρ p vp,
    eval' ρ p vp ->
    (forall A B va vb, vp <> VPair A B va vb) ->
    (forall n, vp <> VNeutral n) ->
    eval' ρ (TSnd p) vp
| E'_Zero : forall ρ,
    eval' ρ Zero VZero
| E'_Succ : forall ρ n vn,
    eval' ρ n vn ->
    eval' ρ (Succ n) (VSucc vn)
| E'_NatRec : forall ρ P z s n vP vz vs vn v,
    eval' ρ P vP ->
    eval' ρ z vz ->
    eval' ρ s vs ->
    eval' ρ n vn ->
    eval_natrec vP vz vs vn v ->
    eval' ρ (NatRec P z s n) v
| E'_Vec : forall ρ n A vn vA,
    eval' ρ n vn ->
    eval' ρ A vA ->
    eval' ρ (Vec n A) (VVec vn vA)
| E'_VNil : forall ρ A vA,
    eval' ρ A vA ->
    eval' ρ (VNil A) (VNilV vA)
| E'_VCons : forall ρ A n x xs vA vn vx vxs,
    eval' ρ A vA ->
    eval' ρ n vn ->
    eval' ρ x vx ->
    eval' ρ xs vxs ->
    eval' ρ (VCons A n x xs) (VConsV vA vn vx vxs)
| E'_VecRec : forall ρ A P z s n xs
                      vA vP vz vs vn vxs v,
    eval' ρ A vA ->
    eval' ρ P vP ->
    eval' ρ z vz ->
    eval' ρ s vs ->
    eval' ρ n vn ->
    eval' ρ xs vxs ->
    eval_vecrec vA vP vz vs vn vxs v ->
    eval' ρ (VecRec A P z s n xs) v

(* semantic application: either β-step for lambdas, or extend neutral spine *)
with vapp : whnf -> whnf -> whnf -> Prop :=
| VApp_Lam : forall ρ' b v v',
    eval' (env_cons v ρ') b v' ->
    vapp (VLam (Cl ρ' b)) v v'
| VApp_Neut : forall n v,
    vapp (VNeutral n) v (VNeutral (NApp n v))
| VApp_Other : forall w v,
    (forall ρ' b, w <> VLam (Cl ρ' b)) ->
    (forall n,   w <> VNeutral n) ->
    vapp w v w

(* semantic Nat recursion on an already evaluated argument *)
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

(* multi-argument semantic application (for specs of vappsk) *)
with vapps : whnf -> list whnf -> whnf -> Prop :=
| vapps_nil  : forall f, vapps f [] f
| vapps_cons : forall f a r rest res,
    vapp f a r ->
    vapps r rest res ->
    vapps f (a :: rest) res

(* semantic Vec recursion on already-evaluated scrutinee *)
with eval_vecrec : whnf -> whnf -> whnf -> whnf -> whnf -> whnf -> whnf -> Prop :=
| EVR_Nil :
    forall vA vP vz vs vn vw,
      eval_vecrec vA vP vz vs vn (VNilV vw) vz
| EVR_Cons :
    forall vA vP vz vs vn vn' va vxs vrec v vw,
      eval_vecrec vA vP vz vs vn' vxs vrec ->
      vapps vs [vn'; va; vxs; vrec] v ->     (* <— use vapps *)
      eval_vecrec vA vP vz vs vn (VConsV vw vn' va vxs) v
| EVR_Neut :
    forall vA vP vz vs vn nx,
      eval_vecrec vA vP vz vs vn (VNeutral nx)
                  (VNeutral (NVecRec vA vP vz vs vn nx)).


(* We assume [term], [whnf], [neutral], [closure] from before. *)


Fixpoint evalk (fuel : nat) (ρ : env) (t : term) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match t with
    | Star => Some VStar
    | Nat  => Some VNat

    | Var x =>
        match nth_error ρ x with
        | Some v => Some v
        | None   => Some (VNeutral (NVar x))
        end

    | Pi A B =>
        match evalk fuel' ρ A with
        | Some vA => Some (VPi vA (Cl ρ B))
        | None    => None
        end

    | Sigma A B =>
        match evalk fuel' ρ A with
        | Some vA => Some (VSigma vA (Cl ρ B))
        | None    => None
        end

    | Lam A b =>
        Some (VLam (Cl ρ b))

    | App t u =>
        match evalk fuel' ρ t with
        | Some vt =>
          match evalk fuel' ρ u with
          | Some vu => vappk fuel' vt vu
          | None    => None
          end
        | None => None
        end

    | Pair A B a b =>
        match evalk fuel' ρ A with
        | Some vA =>
          match evalk fuel' ρ B with
          | Some vB =>
            match evalk fuel' ρ a with
            | Some va =>
              match evalk fuel' ρ b with
              | Some vb => Some (VPair vA vB va vb)
              | None    => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end

    | TFst p =>
        match evalk fuel' ρ p with
        | Some (VPair _ _ va _) => Some va
        | Some (VNeutral np)    => Some (VNeutral (NFst np))
        | Some vp               => Some vp  (* ill-typed/stuck head *)
        | None                  => None
        end

    | TSnd p =>
        match evalk fuel' ρ p with
        | Some (VPair _ _ _ vb) => Some vb
        | Some (VNeutral np)    => Some (VNeutral (NSnd np))
        | Some vp               => Some vp
        | None                  => None
        end

    | Zero     => Some VZero
    | Succ n   =>
        match evalk fuel' ρ n with
        | Some vn => Some (VSucc vn)
        | None    => None
        end

    | NatRec P z s n =>
        match evalk fuel' ρ P with
        | Some vP =>
          match evalk fuel' ρ z with
          | Some vz =>
            match evalk fuel' ρ s with
            | Some vs =>
              match evalk fuel' ρ n with
              | Some vn => vnatreck fuel' vP vz vs vn
              | None    => None
              end
            | None => None
            end
          | None => None
          end
        | None => None
        end
    | Vec n A =>
        match evalk fuel' ρ n, evalk fuel' ρ A with
        | Some vn, Some vA => Some (VVec vn vA)
        | _, _ => None
        end

    | VNil A =>
        match evalk fuel' ρ A with
        | Some vA => Some (VNilV vA)
        | _ => None
        end

    | VCons A n x xs =>
        match evalk fuel' ρ A,
              evalk fuel' ρ n,
              evalk fuel' ρ x,
              evalk fuel' ρ xs with
        | Some vA, Some vn, Some vx, Some vxs =>
            Some (VConsV vA vn vx vxs)
        | _,_,_,_ => None
        end
    | VecRec A P z s n xs =>
        match evalk fuel' ρ A,
              evalk fuel' ρ P,
              evalk fuel' ρ z,
              evalk fuel' ρ s,
              evalk fuel' ρ n,
              evalk fuel' ρ xs with
        | Some vA, Some vP, Some vz, Some vs, Some vn, Some vxs =>
            vvecreck fuel' vA vP vz vs vn vxs
        | _,_,_,_,_,_ => None
        end
    end
  end

with vappk (fuel : nat) (vf vu : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vf with
    | VLam (Cl ρ' body) => evalk fuel' (env_cons vu ρ') body
    | VNeutral nf       => Some (VNeutral (NApp nf vu))
    | _                 => Some vf                  (* IMPORTANT: not [Some vf] *)
    end
  end

with vnatreck (fuel : nat) (vP vz vs vn : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vn with
    | VZero      => Some vz
    | VSucc vn'  =>
        (* rec on predecessor *)
        match vnatreck fuel' vP vz vs vn' with
        | Some vrec =>
          (* compute s n *)
          match vappk fuel' vs vn' with
          | Some v1 =>
            (* (s n) vrec *)
            vappk fuel' v1 vrec
          | None => None
          end
        | None => None
        end
    | VNeutral nn => Some (VNeutral (NNatRec vP vz vs nn))
    | _           => Some vz  (* unreachable in well-typed terms *)
    end
  end

with vappsk (fuel : nat) (f : whnf) (args : list whnf) {struct fuel} : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match args with
    | []        => Some f
    | a :: rest =>
        match vappk fuel' f a with
        | Some r => vappsk fuel' r rest
        | None   => None
        end
    end
  end

with vvecreck
  (fuel : nat) (vA vP vz vs vn : whnf) (vxs : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vxs with
    | VNilV _ =>
        (* [] ++ ys  ==>  z (we pass ys as vz at the term level) *)
        Some vz

    | VConsV _ vn' va vxs' =>
        (* recurse on tail, then apply step to [vn'; va; vxs'; vrec] *)
        match vvecreck fuel' vA vP vz vs vn' vxs' with
        | Some vrec => vappsk fuel' vs [vn'; va; vxs'; vrec]
        | None => None
        end

    | VNeutral nx =>
        (* stuck on a neutral scrutinee *)
        Some (VNeutral (NVecRec vA vP vz vs vn nx))

    | _ =>
        (* ill-typed shape shouldn't happen at runtime *)
        None
    end
  end.

(* Convenience wrapper with a big default fuel. *)
Definition eval (ρ : env) (t : term) : option whnf :=
  evalk 500 ρ t.

(* Constant motive Nat : Nat -> Star  given as a term returning Nat *)
Definition PconstNat : term := Lam Nat Nat.

(* add : Nat -> Nat -> Nat *)
Definition add : term :=
  Lam Nat (                             (* m *)
    Lam Nat (                           (* n *)
      NatRec
        PconstNat                       (* P : Nat -> Star, constant Nat *)
        (Var 0)                         (* base: n *)
        (Lam Nat                        (* step: λ k:Nat. λ acc:Nat. Succ acc *)
          (Lam (App PconstNat (Var 0))
               (Succ (Var 0))))
        (Var 1)                         (* recurse on m *)
  )).

(* mult : Nat -> Nat -> Nat *)
Definition mult : term :=
  Lam Nat (                             (* m *)
    Lam Nat (                           (* n *)
      NatRec
        PconstNat                       (* motive: Nat *)
        Zero                            (* base: 0 *)
        (Lam Nat
          (Lam (App PconstNat (Var 0))  (* acc : Nat *)
               (App (App add (Var 2))   (* add n acc ; n is Var 2 here *)
                    (Var 0))))
        (Var 1)                         (* recurse on m *)
  )).

Eval compute in eval [] (App (App add (Succ (Succ (Succ Zero)))) (Succ Zero)).

(* numerals *)
Definition one  : term := Succ Zero.
Definition two  : term := Succ one.
Definition three: term := Succ two.
Definition four : term := Succ three.
Definition five  : term := Succ four.
Definition six   : term := Succ five.
Definition seven  : term := Succ six.
Definition eighth : term := Succ seven.

(* Examples *)
Eval compute in evalk 200 [] (App (App add two) one).
(* Expected:   Some (VSucc (VSucc (VSucc VZero)))    i.e. 3 *)

Eval compute in eval [] (App (App mult one) four).
(* Expected:   Some (VSucc (VSucc (VSucc (VSucc VZero))))  i.e. 4 *)

(* Pair motive: P n = Σ (_:Nat). Nat  (i.e., Nat × Nat) *)
Definition PpairNat : term :=
  Lam Nat (Sigma Nat (Lam Nat Nat)).

(* Base: <0,1> *)
Definition fib_base : term :=
  Pair Nat (Lam Nat Nat) Zero (Succ Zero).

(* Step: λ k:Nat. λ acc:P k. <snd acc, add (fst acc) (snd acc)> *)
Definition fib_step : term :=
  Lam Nat
    (Lam (App PpairNat (Var 0))
         (Pair Nat (Lam Nat Nat)
           (TSnd (Var 0))
           (App (App add (TFst (Var 0))) (TSnd (Var 0)))
         )).

(* fib : Nat -> Nat  =  fst (NatRec P base step n) *)
Definition fib : term :=
  Lam Nat
    (TFst (NatRec PpairNat fib_base fib_step (Var 0))).

(* Examples (works with your fuelled evaluator wrapper `eval`) *)
Eval compute in eval [] (App fib Zero).    (* = Some VZero *)
Eval compute in eval [] (App fib one).     (* = Some (VSucc VZero)             = 1 *)
Eval compute in eval [] (App fib two).     (* = Some (VSucc VZero)             = 1 *)
Eval compute in eval [] (App fib three).   (* = Some (VSucc (VSucc VZero))     = 2 *)
Eval compute in eval [] (App fib four).    (* = Some (VSucc (VSucc (VSucc VZero))) = 3 *)
Eval compute in eval [] (App fib five).    (* = 5 *)
Eval compute in eval [] (App fib six).     (* = 8 *)
Eval compute in eval [] (App fib seven).   (* = 13 *)
Eval compute in eval [] (App fib eighth).   (* = 13 *)


(* plus k m := m + k, via add *)
Definition tm_plus (k m : term) : term := App (App add m) k.

(* step function for VecRec:
   λ k:Nat. λ a:A. λ xs:Vec k A. λ ih:Vec (plus k m) A.
      VCons A (plus k m) a ih
*)
Definition tm_s_cons (A m : term) : term :=
  Lam Nat
    (Lam A
      (Lam (Vec (Var 1) A)
        (Lam (Vec (tm_plus (Var 2) m) A)
             (VCons A (tm_plus (Var 3) m) (Var 2) (Var 0))))).
(* de Bruijn indices inside the body:
   Var 3 = k,  Var 2 = a,  Var 1 = xs,  Var 0 = ih *)

(* Motive just to satisfy typing; runtime eval doesn't depend on it *)
Definition tm_vec_motive (A : term) : term :=
  Lam Nat (Pi (Vec (Var 0) A) Star).

(* append A n xs m ys := VecRec A (tm_vec_motive A) ys (tm_s_cons A m) n xs *)
Definition tm_append (A n xs m ys : term) : term :=
  VecRec A (tm_vec_motive A) ys (tm_s_cons A m) n xs.

(* numerals in the object language *)
Definition tm_num (k:nat) : term :=
  Nat.iter k Succ Zero.

(* [1]  and  [1;2]  as terms *)
Definition tm_vnil_nat : term := VNil Nat.
Definition tm_v1 : term :=
  VCons Nat Zero (Succ Zero) tm_vnil_nat.                 (* [1] *)

Definition tm_v12 : term :=
  VCons Nat (Succ Zero) (Succ Zero)                       (* head 1 *)
        (VCons Nat Zero (Succ (Succ Zero)) tm_vnil_nat).  (* tail [2] *)

(* [3] *)
Definition tm_v3 : term :=
  VCons Nat Zero (Succ (Succ (Succ Zero))) tm_vnil_nat.

(* apply append to Nat, lengths, and the two vectors *)
Definition tm_append_v12_v3 : term :=
  tm_append Nat (Succ (Succ Zero)) tm_v12 (Succ Zero) tm_v3.

Definition bigfuel := 500%nat.

Definition sem_env_of_ctx (Γ : list whnf) : env := id_env (length Γ).

(* Expect: VConsV VNat (Succ (Succ Zero)) 1 (VConsV VNat (Succ Zero) 2 (VConsV VNat Zero 3 [])) *)
Compute evalk bigfuel [] tm_append_v12_v3.


Scheme eval'_rect      := Induction for eval'        Sort Prop
with vapp_rect         := Induction for vapp         Sort Prop
with eval_natrec_rect  := Induction for eval_natrec  Sort Prop
with vapps_rect        := Induction for vapps        Sort Prop
with eval_vectrec_rect := Induction for eval_vecrec  Sort Prop.

Combined Scheme evalsys_mutind from eval'_rect, vapp_rect, eval_natrec_rect, vapps_rect, eval_vectrec_rect.

 (* mutual induction on the first derivation *)
Lemma det_quintet :
  (forall ρ t v1, eval' ρ t v1 -> forall v2, eval' ρ t v2 -> v1 = v2) /\
  (forall f a r1, vapp f a r1 -> forall r2, vapp f a r2 -> r1 = r2) /\
  (forall vP vz vs vn r1, eval_natrec vP vz vs vn r1 -> forall r2, eval_natrec vP vz vs vn r2 -> r1 = r2) /\
  (forall f as_ r1, vapps f as_ r1 -> forall r2, vapps f as_ r2 -> r1 = r2) /\
  (forall vA vP vz vs vn vxs r1, eval_vecrec vA vP vz vs vn vxs r1 -> forall r2, eval_vecrec vA vP vz vs vn vxs r2 -> r1 = r2).
Proof.
  apply evalsys_mutind; intros.
- inversion H. easy.
- inversion H. easy.
- inversion H. subst. rewrite H2 in e. inversion e. easy.
  subst. rewrite H2 in e. easy.
- inversion H. subst. rewrite H2 in e. easy.
  subst. easy.
- inversion H0. subst.
  f_equal. apply H. easy.
- inversion H0. subst.
  f_equal. apply H. easy.
- inversion H. easy.
- inversion H2. subst.
  apply H in H5. subst.
  apply H0 in H7. subst.
  apply H1. easy.
- inversion H3. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in H12. subst.
  apply H2 in H13. subst. easy.
- inversion H0. subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H3 A B va vb). reflexivity.
- inversion H0. subst.
  apply H in H3. easy.
  subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H5 n). reflexivity.
- inversion H0. subst.
  apply H in H3. subst.
  exfalso. apply (n A B v2 vb). reflexivity.
  subst. apply H in H3. subst.
  exfalso. apply (n0 n1). reflexivity.
  subst. apply H. easy.
- inversion H0. subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H3 A B va vb). reflexivity.
- inversion H0. subst.
  apply H in H3. easy.
  subst.
  apply H in H3. inversion H3. easy.
  subst. apply H in H2.
  subst. exfalso. apply (H5 n). reflexivity.
- inversion H0. subst.
  apply H in H3. subst.
  exfalso. apply (n A B va v2). reflexivity.
  subst. apply H in H3. subst.
  exfalso. apply (n0 n1). reflexivity.
  subst. apply H. easy.
- inversion H. easy.
- inversion H0. subst.
  apply H in H3. subst. easy.
- inversion H4. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in H13. subst.
  apply H2 in H14. subst.
  apply H3 in H15. subst. easy.
- inversion H1. subst.
  apply H in H5.
  apply H0 in H7. subst.
  easy.
- inversion H0; subst.
  apply H in H3. subst. easy.
- inversion H3. subst.
  apply H in H9. subst.
  apply H0 in H11. subst.
  apply H1 in e1. subst.
  apply H2 in e2. subst.
  apply H2 in H13. subst.
  apply H1 in H12. subst. easy.
- inversion H6. subst.
  apply H5.
  apply H in H13. subst.
  apply H0 in H15. subst.
  apply H1 in H17. subst.
  apply H2 in H18. subst.
  apply H3 in H19. subst.
  apply H4 in H20. subst.
  apply H5 in H21. subst. easy.
- inversion H0; subst.
 + (* VApp_Lam *) eapply H; eauto.
 + exfalso. apply (H1 ρ' b). reflexivity.
- inversion H. easy.
  exfalso. apply (H1 n). reflexivity.
- inversion H.
  + subst. exfalso. apply (n ρ' b). reflexivity.
  + subst. exfalso. apply (n0 n1). reflexivity.
  + subst. easy.
- inversion H. easy.
  easy.
- inversion H2. subst.
  apply H in H4. subst.
  apply H0 in H5. subst.
  apply H1 in H9. easy.
  subst. exfalso. apply (H3 vn). easy.
- inversion H. subst.
  easy.
  subst. exfalso. apply (H2 nn). easy.
- inversion H. subst.
  easy. 
  subst. exfalso. apply (n vn0). easy.
  subst. exfalso. apply (n1 nn). easy.
  easy.
- inversion H.
  easy.
- inversion H1. subst. apply H0. apply H in H5. subst. easy.
- inversion H. easy.
- inversion H1. subst.
  apply H0.
  apply H in H12. subst. easy.
(* - inversion H4. subst.
  apply H0 in H9. subst.
  apply H1 in H15. subst.
  apply H2 in H17. subst.
  apply H in H8. subst.
  apply H3. easy. *)
- inversion H.
  subst. easy.
Qed.

(* Determinism corollaries for the three relations *)
Theorem eval'_det :
  forall ρ t v1 v2, eval' ρ t v1 -> eval' ρ t v2 -> v1 = v2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Ha with (ρ := ρ) (t := t); easy.
Qed.

Theorem vapp_det :
  forall f a r1 r2, vapp f a r1 -> vapp f a r2 -> r1 = r2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Hb with (f := f) (a := a); easy.
Qed.

Theorem eval_natrec_det :
  forall vP vz vs vn r1 r2,
    eval_natrec vP vz vs vn r1 -> eval_natrec vP vz vs vn r2 -> r1 = r2.
Proof. intros. 
       specialize det_quintet; intros (Ha,(Hb,Hc)).
       apply Hc with (vP := vP) (vz := vz) (vs := vs) (vn := vn); easy.
Qed.

Lemma eval'_Lam_inv ρ A b v: eval' ρ (Lam A b) v -> v = VLam (Cl ρ b).
Proof. intros H. inversion H; subst; reflexivity. Qed.

Lemma eval'_Pi_inv ρ A B v: eval' ρ (Pi A B) v -> exists vA, v = VPi vA (Cl ρ B) /\ eval' ρ A vA.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma eval'_Sigma_inv ρ A B v: eval' ρ (Sigma A B) v -> exists vA, v = VSigma vA (Cl ρ B) /\ eval' ρ A vA.
Proof. intros H; inversion H; subst; eauto. Qed.

Lemma evalk_monotone: forall k k' ρ t v,
  k' >= k ->
  evalk k ρ t = Some v ->
  evalk k' ρ t = Some v
with vappk_step_mono: forall k k' vf vu r,
  k' >= k ->
  vappk k vf vu = Some r ->
  vappk k' vf vu = Some r
with vnatreck_step_mono: forall k k' vP vz vs vn r,
  k' >= k ->
  vnatreck k vP vz vs vn = Some r ->
  vnatreck k' vP vz vs vn = Some r
with vappsk_step_mono: forall k k' vf vu r,
  k' >= k ->
  vappsk k vf vu = Some r ->
  vappsk k' vf vu = Some r
with vvecreck_monotone: forall k k' vA vP vz vs vn vxs r,
  k' >= k ->
  vvecreck k vA vP vz vs vn vxs = Some r ->
  vvecreck k' vA vP vz vs vn vxs = Some r.
Proof. intro k.
       induction k; intros.
       - simpl in *. easy.
       - simpl in H0.
         case_eq t; intros.
         + subst. inversion H0.
           destruct k'. easy.
           simpl. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl. easy.
         + subst. simpl in *.
           destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy. simpl. easy.
         + subst. destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. apply IHk with (k' := k') in H1. simpl. rewrite H1. easy. lia.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. 
             apply IHk with (k' := k') in H1; try lia.
             rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0. 
             apply IHk with (k' := k') in H1; try lia.
             rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *. destruct k'. easy.
           simpl. easy.
         + subst. destruct k'. easy. simpl. easy.
         + subst. 
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                apply IHk with (k' := k') in H1; try lia.
                apply IHk with (k' := k') in H2; try lia.
                simpl. rewrite H1, H2. 
                apply vappk_step_mono with (k' := k') in H0; try lia. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4.
                         apply vnatreck_step_mono with (k' := k') in H0; try lia. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                apply IHk with (k' := k') in H1; try lia.
                apply IHk with (k' := k') in H2; try lia.
                simpl. rewrite H1, H2. 
                easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             apply IHk with (k' := k') in H1; try lia.
             simpl. rewrite H1. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0. simpl.
                         apply IHk with (k' := k') in H1; try lia.
                         apply IHk with (k' := k') in H2; try lia.
                         apply IHk with (k' := k') in H3; try lia.
                         apply IHk with (k' := k') in H4; try lia.
                         rewrite H1, H2, H3, H4.
                         easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
         + subst. simpl in *.
           destruct k'. easy.
           case_eq(evalk k ρ t0); intros.
           * rewrite H1 in H0.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H2 in H0.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H3 in H0.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H4 in H0.
                         case_eq(evalk k ρ t4); intros.
                         ***** rewrite H5 in H0.
                               case_eq(evalk k ρ t5); intros.
                               ****** rewrite H6 in H0.
                                      apply IHk with (k' := k') in H1; try lia.
                                      apply IHk with (k' := k') in H2; try lia.
                                      apply IHk with (k' := k') in H3; try lia.
                                      apply IHk with (k' := k') in H4; try lia.
                                      apply IHk with (k' := k') in H5; try lia.
                                      apply IHk with (k' := k') in H6; try lia.
                                      simpl.
                                      rewrite H1, H2, H3, H4, H5, H6.
                                      apply vvecreck_monotone with (k' := k') in H0; try lia. easy.
                               ****** rewrite H6 in H0. easy.
                         ***** rewrite H5 in H0. easy.
                    **** rewrite H4 in H0. easy.
                *** rewrite H3 in H0. easy.
             ** rewrite H2 in H0. easy.
           * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H. easy.
       + destruct k'. easy.
         simpl in *.
         case_eq vf; intros; subst; try easy.
         destruct c.  
         apply evalk_monotone with (k' := k') in H0; try lia. easy.
     - intro k.
       induction k; intros.
       + simpl in H0. easy.
       + destruct k'. easy.
         simpl in H0. simpl.
         case_eq vn; intros; subst; try easy.
         case_eq(vnatreck k vP vz vs w ); intros.
         * rewrite H1 in H0.
           case_eq(vappk k vs w); intros.
           ** rewrite H2 in H0.
              apply IHk with (k' := k') in H1; try lia.
              rewrite H1.
              apply vappk_step_mono with (k' := k') in H2; try lia. 
              rewrite H2. 
              apply vappk_step_mono with (k' := k') in H0; try lia. 
              easy.
           ** rewrite H2 in H0. easy.
        * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H. easy.
       + destruct k'. easy.
         simpl in *.
         case_eq vu; intros; subst; try easy.
         case_eq(vappk k vf w); intros.
         * rewrite H1 in H0. 
           apply vappk_step_mono with (k' := k') in H1; try lia.
           rewrite H1.
           apply IHk; try lia. easy.
         * rewrite H1 in H0. easy.
     - intro k.
       induction k; intros.
       + simpl in H0. easy.
       + destruct k'. easy.
         simpl in H0. simpl.
         case_eq vxs; intros; subst; try easy.
         case_eq(vvecreck k vA vP vz vs w0 w2 ); intros.
         * rewrite H1 in H0.
           apply IHk with (k' := k') in H1; try lia.
           rewrite H1.
           apply vappsk_step_mono with (k := k); try lia.
           easy.
         * rewrite H1 in H0. easy.
Qed.

Lemma evalk_TFst_general :
  forall k ρ t v,
    evalk k ρ t = Some v ->
    evalk (S k) ρ (TFst t) =
      match v with
      | VPair _ _ va _ => Some va
      | VNeutral np    => Some (VNeutral (NFst np))
      | _              => Some v
      end.
Proof.
  intros k ρ t v H.
  destruct k as [|k]; simpl in *.
  - discriminate H.
  - (* S k *)
    rewrite H. destruct v; reflexivity.
Qed.

Corollary evalk_TFst_VStar :
  forall k ρ t,
    evalk k ρ t = Some VStar ->
    evalk (S k) ρ (TFst t) = Some VStar.
Proof.
  intros k ρ t H. now rewrite (evalk_TFst_general _ _ _ _ H).
Qed.

(* And with your monotonicity, any k' >= k+1 also works. *)
Corollary evalk_TFst_VStar_ge :
  forall k k' ρ t,
    k' >= S k ->
    evalk k ρ t = Some VStar ->
    evalk k' ρ (TFst t) = Some VStar.
Proof.
  intros k k' ρ t Hge Hev.
  specialize (evalk_TFst_general k ρ t VStar Hev); intros .
  eapply evalk_monotone; eauto.
Qed.

Theorem evalk_sound: forall k ρ t v,
  evalk k ρ t = Some v ->
  eval' ρ t v
with vappk_sound: forall k vf vu r,
  vappk k vf vu = Some r ->
  vapp vf vu r
with vnatreck_sound: forall k vP vz vs vn r,
  vnatreck k vP vz vs vn = Some r ->
  eval_natrec vP vz vs vn r
with vappsk_sound: forall k f args r,
  vappsk k f args = Some r ->
  vapps f args r
with vvecreck_sound: forall k vA vP vz vs vn vxs v,
  vvecreck k vA vP vz vs vn vxs = Some v ->
  eval_vecrec vA vP vz vs vn vxs v.
Proof. intro k.
       induction k; intros.
       - simpl in H. easy.
       - simpl in H. 
         case_eq t; intros.
         + subst. inversion H. constructor.
         + subst. inversion H. constructor.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst. inversion H. constructor.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0.
             inversion H. constructor. easy.
           * rewrite H0 in H. easy.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         inversion H. constructor; easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst.
           destruct (evalk k ρ t0) eqn:Ep; try discriminate.
           case_eq w; intros.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TFst_Other. easy.
             easy.
             easy.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TFst_Other. easy.
             easy.
             easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. subst.
             apply IHk in Ep. 
             apply E'_TFst_Pair with (A := w0) (B := w1) (vb:= w3). easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
         + subst.
           destruct (evalk k ρ t0) eqn:Ep; try discriminate.
           case_eq w; intros.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TSnd_Other. easy.
             easy.
             easy.
           * subst. inversion H. 
             apply IHk in Ep.
             apply E'_TSnd_Other. easy.
             easy.
             easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. subst.
             apply IHk in Ep. 
             apply E'_TSnd_Pair with (A := w0) (B := w1) (va:= w2). easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H.
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
           * subst. inversion H. 
             apply IHk in Ep. constructor; easy.
         + subst.
           case_eq(nth_error ρ n); intros.
           * rewrite H0 in H. inversion H. subst.
             constructor. easy.
           * rewrite H0 in H.
             inversion H. subst.
             apply E'_Var_None. easy.
         + subst. inversion H. constructor.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H. 
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                apply IHk in H0, H1.
                apply vappk_sound in H.
                apply E'_App with (vt := w) (vu := w0); easy.
              ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst. 
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         apply vnatreck_sound in H.
                         apply E'_NatRec with (vP := w) (vz := w0) (vs := w1) (vn := w2); easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
            * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H. 
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                apply IHk in H0, H1. inversion H. subst.
                apply E'_Vec; easy.
              ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             apply IHk in H0; try lia.
             inversion H. subst.
             constructor. easy.
           * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H. simpl.
                         apply IHk in H0; try lia.
                         apply IHk in H1; try lia.
                         apply IHk in H2; try lia.
                         apply IHk in H3; try lia.
                         inversion H. subst.
                         constructor; easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
            * rewrite H0 in H. easy.
         + subst.
           case_eq(evalk k ρ t0); intros.
           * rewrite H0 in H.
             case_eq(evalk k ρ t1); intros.
             ** rewrite H1 in H.
                case_eq(evalk k ρ t2); intros.
                *** rewrite H2 in H.
                    case_eq(evalk k ρ t3); intros.
                    **** rewrite H3 in H.
                         case_eq(evalk k ρ t4); intros.
                         ***** rewrite H4 in H.
                               case_eq(evalk k ρ t5); intros.
                               ****** rewrite H5 in H.
                                      apply IHk in H0; try lia.
                                      apply IHk in H1; try lia.
                                      apply IHk in H2; try lia.
                                      apply IHk in H3; try lia.
                                      apply IHk in H4; try lia.
                                      apply IHk in H5; try lia.
                                      apply vvecreck_sound in H.
                                      econstructor; eauto.
                               ****** rewrite H5 in H. easy.
                         ***** rewrite H4 in H. easy.
                    **** rewrite H3 in H. easy.
                *** rewrite H2 in H. easy.
             ** rewrite H1 in H. easy.
           * rewrite H0 in H. easy.
       - intro k. 
         induction k; intros. 
         + simpl in H. easy.
         + simpl in H.
           destruct vf.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. destruct c. apply evalk_sound in H.
             constructor. easy.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
       - intro k.
         induction k; intros.
         + simpl in H. easy.
         + simpl in H.
           case_eq vn; intros; subst.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H. subst.
             constructor.
           * case_eq(vnatreck k vP vz vs w); intros.
             ** rewrite H0 in H.
                apply IHk in H0.
                case_eq(vappk k vs w); intros.
                *** rewrite H1 in H.
                    apply vappk_sound in H, H1.
                    apply ENR_Succ with (vrec := w0) (v1 := w1); easy.
                *** rewrite H1 in H. easy.
             ** rewrite H0 in H. easy.
           * inversion H. subst.
             constructor.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
       - intro k.
         induction k; intros.
         + simpl in H. easy.
         + simpl in H.
           case_eq args; intros; subst.
           * inversion H. subst.
             constructor.
           * case_eq(vappk k f w); intros.
             ** rewrite H0 in H.
                apply IHk in H.
                apply vapps_cons with (r := w0).
                apply vappk_sound with (k := k). easy. easy.
             ** rewrite H0 in H. easy.
       - intro k. 
         induction k; intros. 
         + simpl in H. easy.
         + simpl in H.
           case_eq vxs; intros; subst; try easy.
           * inversion H. subst.
             constructor.
           * inversion H. subst. constructor.
           * case_eq(vvecreck k vA vP vz vs w0 w2); intros.
             ** rewrite H0 in H.
                simpl.
                apply IHk in H0.
                apply EVR_Cons with (vrec := w3).
                easy. apply vappsk_sound in H. easy.
             ** rewrite H0 in H. easy.
Qed.

(* ---------- Completeness: relational ⇒ some fuel computes the same ---------- *)

Lemma evalk_complete:
  (* eval' *)
  (forall ρ t v, eval' ρ t v -> exists k, evalk k ρ t = Some v) /\
  (* vapp *)
  (forall f a r, vapp f a r -> exists k, vappk k f a = Some r) /\
  (* natrec *)
  (forall vP vz vs vn r, eval_natrec vP vz vs vn r -> exists k, vnatreck k vP vz vs vn = Some r) /\
  (* vapps completeness *)
  (forall f as_ r, vapps f as_ r -> exists k, vappsk k f as_ = Some r)
  /\
  (* vec recursor completeness *)
  (forall vA vP vz vs vn vxs v, eval_vecrec vA vP vz vs vn vxs v -> exists k, vvecreck k vA vP vz vs vn vxs = Some v).
Proof.
  eapply (evalsys_mutind
    (* motives *)
    (fun ρ t v           _ => exists k, evalk   k ρ t = Some v)            (* eval' *)
    (fun f a r           _ => exists k, vappk   k f a = Some r)            (* vapp *)
    (fun vP vz vs vn r   _ => exists k, vnatreck k vP vz vs vn = Some r)   (* eval_natrec *)
    (fun f as_ r         _ => exists k, vappsk  k f as_ = Some r)          (* vapps *)
    (fun vA vP vz vs vn vxs v _ => exists k, vvecreck k vA vP vz vs vn vxs = Some v)  (* eval_vecrec *)
  ); intros.
  (* ===== evalk_complete ===== *)
    + exists 1. simpl. easy.
    + exists 1. simpl. easy.

    + exists 1. simpl. rewrite e. easy.
    + exists 1. simpl. rewrite e. easy.


    + (* Pi *)
      destruct H as [kA HA].
      exists (S kA). simpl. now rewrite HA.

    + (* Sigma *)
      destruct H as [kA HA].
      exists (S kA). simpl. now rewrite HA.
      
    + exists 1. simpl. easy.

    + (* App *)
      destruct H as [kt Ht].
      destruct H0 as [ku Hu].
      destruct H1 as [ka Ha].
      set (K := S (Nat.max kt (Nat.max ku ka))).
      exists K. simpl.
      assert (K >= kt) by (unfold K; lia).
      assert (K >= ku) by (unfold K; lia).
      assert (K >= ka) by (unfold K; lia).
      
      rewrite evalk_monotone with (k := kt) (v := vt); try lia.
      rewrite evalk_monotone with (k := ku) (v := vu); try lia.
      rewrite vappk_step_mono with (k := ka) (r := v); try lia.
      easy. easy. easy. easy.

    + (* Pair *)
      destruct H as [kA HA].
      destruct H0 as [kB HB].
      destruct H1 as [ka Ha].
      destruct H2 as [kb Hb].
      set (K := S (Nat.max kA (Nat.max kB (Nat.max ka kb)))).
      exists K. simpl.
      assert (K >= kA) by (unfold K; lia).
      assert (K >= kB) by (unfold K; lia).
      assert (K >= ka) by (unfold K; lia).
      assert (K >= kb) by (unfold K; lia).

      rewrite evalk_monotone with (k := kA) (v := vA); try lia.
      rewrite evalk_monotone with (k := kB) (v := vB); try lia.
      rewrite evalk_monotone with (k := ka) (v := va); try lia.
      rewrite evalk_monotone with (k := kb) (v := vb); try lia.
      easy. easy. easy. easy. easy.

    + (* TFst Pair *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TFst Neut *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TFst Other/stuck *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp.
      (* side-conditions guarantee scrutinee isn’t Pair/Neutral, so the [match] picks [Some vp] *)
      destruct vp; try reflexivity; try (exfalso; eapply H1; reflexivity); try (exfalso; eapply H2; reflexivity).
      exfalso.
      apply(n vp1 vp2 vp3 vp4). easy.
      exfalso.
      apply(n0 n1). easy.

    + (* TSnd Pair *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TSnd Neut *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + (* TSnd Other/stuck *)
      destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp.
      (* side-conditions guarantee scrutinee isn’t Pair/Neutral, so the [match] picks [Some vp] *)
      destruct vp; try reflexivity; try (exfalso; eapply H1; reflexivity); try (exfalso; eapply H2; reflexivity).
      exfalso.
      apply(n vp1 vp2 vp3 vp4). easy.
      exfalso.
      apply(n0 n1). easy.

    + exists 1. simpl. easy.
    
    + (* Succ *)
      destruct H as [kn Hn].
      exists (S kn). simpl in Hn. simpl. rewrite Hn. easy.

    + (* NatRec *)
      destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      destruct H3 as [kr Hr].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks (Nat.max kn kr))))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).
      assert (K >= kr) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vP); try lia.
      rewrite evalk_monotone with (k := kz) (v := vz); try lia.
      rewrite evalk_monotone with (k := ks) (v := vs); try lia.
      rewrite evalk_monotone with (k := kn) (v := vn); try lia.
      rewrite vnatreck_step_mono with (k := kr) (r := v); try lia.
      easy. easy. easy. easy. easy. easy.

    + destruct H as [k He].
      destruct H0 as [kz Hz].
      set (K := S (Nat.max k kz)).
      exists K. simpl.
      rewrite evalk_monotone with (k := k) (v := vn); try lia.
      rewrite evalk_monotone with (k := kz) (v := vA); try lia.
      easy. easy. easy.

    + destruct H as [kp Hp].
      exists (S kp). simpl. rewrite Hp. reflexivity.

    + destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks kn)))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vA); try lia.
      rewrite evalk_monotone with (k := kz) (v := vn); try lia.
      rewrite evalk_monotone with (k := ks) (v := vx); try lia.
      rewrite evalk_monotone with (k := kn) (v := vxs); try lia.
      easy. easy. easy. easy. easy.
    
    + destruct H as [kP HP].
      destruct H0 as [kz Hz].
      destruct H1 as [ks Hs].
      destruct H2 as [kn Hn].
      destruct H3 as [kr Hr].
      destruct H4 as [kv Hv].
      destruct H5 as [ku Hu].
      set (K := S (Nat.max kP (Nat.max kz (Nat.max ks (Nat.max kn (Nat.max kr (Nat.max kv ku))))))).
      exists K. simpl.
      assert (K >= kP) by (unfold K; lia).
      assert (K >= kz) by (unfold K; lia).
      assert (K >= ks) by (unfold K; lia).
      assert (K >= kn) by (unfold K; lia).
      assert (K >= kr) by (unfold K; lia).
      assert (K >= kv) by (unfold K; lia).
      assert (K >= ku) by (unfold K; lia).

      rewrite evalk_monotone with (k := kP) (v := vA); try lia.
      rewrite evalk_monotone with (k := kz) (v := vP); try lia.
      rewrite evalk_monotone with (k := ks) (v := vz); try lia.
      rewrite evalk_monotone with (k := kn) (v := vs); try lia.
      rewrite evalk_monotone with (k := kr) (v := vn); try lia.
      rewrite evalk_monotone with (k := kv) (v := vxs); try lia.
      rewrite vvecreck_monotone with (k := ku) (r := v); try lia.
      easy. easy. easy. easy. easy. easy. easy. easy.
      
    + (* Lam: β-step *)
      destruct H as [k He].
      exists (S k). simpl. now rewrite He.
    + (* Neutral: extend spine *)
      exists 1%nat. reflexivity.
    
    
    + (* Other: fallback *)
      exists 1%nat. simpl.
      destruct w; try easy.
      destruct c. exfalso. apply (n l t). easy.
      exfalso. apply (n0 n1). easy.

    + (* Zero *)
      exists 1%nat. reflexivity.
    + (* Succ *)
      destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      destruct H1 as [k3 Hr3].
      set (K := S (Nat.max k1 (Nat.max k2 k3))).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      assert (K >= k3) by (unfold K; lia).
      Check vnatreck_step_mono.
      rewrite vnatreck_step_mono with (k := k1) (r := vrec); try lia.
      rewrite vappk_step_mono with (k := k2) (r := v1); try lia.
      rewrite vappk_step_mono with (k := k3) (r := v); try lia.
      easy. easy. easy. easy.
    + (* Neutral *)
      exists 1%nat. reflexivity.
    + (* Other/stuck *)
      exists 1%nat. simpl.
      destruct vn; try easy. 
      exfalso. apply (n vn). easy.
      exfalso. apply (n1 n2). easy.
    + exists 1%nat. reflexivity.
    + destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      set (K := S (Nat.max k1 k2)).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      rewrite vappk_step_mono with (k := k1) (r := r); try lia.
      rewrite vappsk_step_mono with (k := k2) (r := res); try lia.
      easy. easy. easy.
    + exists 1%nat. reflexivity.
    + destruct H as [k1 Hr1].
      destruct H0 as [k2 Hr2].
      set (K := S (Nat.max k1 k2)).
      exists K. simpl.
      assert (K >= k1) by (unfold K; lia).
      assert (K >= k2) by (unfold K; lia).
      rewrite vvecreck_monotone with (k := k1) (r := vrec); try lia.
      rewrite vappsk_step_mono with (k := k2) (r := v); try lia.
      easy. easy. easy.
    + exists 1%nat. simpl. reflexivity.
Qed.

Corollary vappk_complete: forall f a r, 
  vapp f a r -> exists k, vappk k f a = Some r.
Proof. intros. 
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Hb. easy. 
Qed.

Corollary vnatreck_complete: forall vP vz vs vn r, 
  eval_natrec vP vz vs vn r -> exists k, vnatreck k vP vz vs vn = Some r.
Proof. intros. 
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Hc. easy. 
Qed.

Corollary evalk_complete_: forall ρ t v, 
  eval' ρ t v -> exists k, evalk k ρ t = Some v.
Proof. intros.
       specialize(evalk_complete); intros (Ha, (Hb, Hc)).
       apply Ha. easy. 
Qed.

(* A convenient equivalence to use in tests and proofs *)
Corollary evalk_eval'_iff :
  forall ρ t v, (exists k, evalk k ρ t = Some v) <-> eval' ρ t v.
Proof.
  split; [intros [k Hk]; eapply evalk_sound; eauto|].
  intros He. 
  specialize(evalk_complete); intros (Ha, (Hb, Hc)).
  apply Ha. easy.
Qed.


(* Bidirectional Typing *)

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

(* Definition clos_eval' (cl : closure) (v v' : whnf) : Prop :=
  eval' (env_cons v (cl_env cl)) (cl_body cl) v'. *)

Lemma clos_eval'_det (c:closure) (v x y:whnf) :
  clos_eval' c v x -> 
  clos_eval' c v y -> 
  x = y.
Proof.
  destruct c as [ρ body]; simpl; eauto using eval'_det.
Qed.

(* Algorithmic convertibility on WHNFs and neutrals *)
(* Inductive convV : whnf -> whnf -> Prop :=
| CV_Star  : convV VStar VStar
| CV_Nat   : convV VNat  VNat

| CV_Pi : forall A A' B B',
    convV A A' ->
    (forall vB vB',        (* compare codomains under a fresh neutral *)
        clos_eval' B  fresh vB  ->
        clos_eval' B' fresh vB' ->
        convV vB vB') ->
    convV (VPi A B) (VPi A' B')

| CV_Sigma : forall A A' B B',
    convV A A' ->
    (forall vB vB',
        clos_eval' B  fresh vB  ->
        clos_eval' B' fresh vB' ->
        convV vB vB') ->
    convV (VSigma A B) (VSigma A' B')

(* You can drop CV_Lam if you don't want η/extensionality for functions *)
| CV_Lam : forall cl1 cl2,
    (forall v1 v2,
        clos_eval' cl1 fresh v1 ->
        clos_eval' cl2 fresh v2 ->
        convV v1 v2) ->
    convV (VLam cl1) (VLam cl2)

| CV_Pair : forall A B a b A' B' a' b',
    convV A A' -> 
    convV B B' -> 
    convV a a' -> 
    convV b b' ->
    convV (VPair A B a b) (VPair A' B' a' b')

| CV_Zero : convV VZero VZero
| CV_Succ : forall n n', convV n n' -> convV (VSucc n) (VSucc n')

| CV_Neutral : forall n n',
    convN n n' ->
    convV (VNeutral n) (VNeutral n')

with convN : neutral -> neutral -> Prop :=
| CN_Var  : forall i, convN (NVar i) (NVar i)
| CN_App  : forall n n' v v',
    convN n n' -> 
    convV v v' ->
    convN (NApp n v) (NApp n' v')
| CN_Fst  : forall n n', 
    convN n n' -> 
    convN (NFst n) (NFst n')
| CN_Snd  : forall n n',
   convN n n' ->
   convN (NSnd n) (NSnd n')
| CN_NatRec : forall P P' z z' s s' n n',
    convV P P' -> 
    convV z z' -> 
    convV s s' -> 
    convN n n' ->
    convN (NNatRec P z s n) (NNatRec P' z' s' n').

Scheme convV_rect := Induction for convV Sort Prop
with convN_rect := Induction for convN Sort Prop.
Combined Scheme conv_rect from convV_rect, convN_rect.
 *)
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

Inductive conv : whnf -> whnf -> Prop :=
| CoV_Star  : conv VStar VStar
| CoV_Nat   : conv VNat  VNat

| CoV_Pi : forall A A' B B',
    conv A A' ->
    (forall vB vB',
        clos_eval' B  fresh vB  ->
        clos_eval' B' fresh vB' ->
        conv vB vB') ->
    conv (VPi A B) (VPi A' B')

| CoV_Sigma : forall A A' B B',
    conv A A' ->
    (forall vB vB',
        clos_eval' B  fresh vB  ->
        clos_eval' B' fresh vB' ->
        conv vB vB') ->
    conv (VSigma A B) (VSigma A' B')

(* Optional η; drop if you don't want extensionality for functions *)
| CoV_Lam : forall cl1 cl2,
    (forall v1 v2,
        clos_eval' cl1 fresh v1 ->
        clos_eval' cl2 fresh v2 ->
        conv v1 v2) ->
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

Definition clos_eval_fuel (fuel : nat) (cl : closure) (v : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match cl with
    | Cl ρ t =>
        (* extend the environment ρ with v and evaluate the body t *)
        evalk fuel' (env_cons v ρ) t
    end
  end.

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

    | _, _ => false
    end
  end.

Lemma clos_eval_fuel_sound :
  forall k B x v,
    clos_eval_fuel k B x = Some v ->
    clos_eval' B x v.
Proof.
  intros k B x v H.
  destruct k as [|k']; [inversion H|].
  simpl in H.
  unfold clos_eval'.
  destruct B as [ρ t]; simpl in H.
  (* now H : evalk k' (x :: ρ) t = Some v *)
  apply evalk_sound in H.
  apply H.
Qed.

Lemma clos_eval_fuel_complete :
  forall B x v,
    clos_eval' B x v ->
    exists K, forall k, k >= K -> clos_eval_fuel k B x = Some v.
Proof.
  intros [ρ t] x v H; cbn in *.
  destruct evalk_complete as (Ha,(Hb,Hc)).
  destruct (Ha (env_cons x ρ) t v H) as [K HK].
  exists (S K). intros.
  unfold clos_eval_fuel.
  destruct k. 
  inversion H0. subst. simpl in HK.
  apply evalk_monotone with (k := K); try lia.
  easy.
Qed.

Lemma clos_eval_fuel_monotone :
  forall k k' B x v,
    k' >= k ->
    clos_eval_fuel k B x = Some v ->
    clos_eval_fuel k' B x = Some v.
Proof.
   intros.
   unfold clos_eval_fuel in *. destruct k. easy.
   destruct k'. easy.
   destruct B. 
   apply evalk_monotone with (k := k); try lia.
   easy.
Qed.

Lemma conv_fuel_sound :
  forall k v w,
    conv_fuel k v w = true ->
    conv v w
with conv_neutral_fuel_sound :
  forall k n n',
    conv_neutral_fuel k n n' = true ->
    conv (VNeutral n) (VNeutral n').
Proof.
  (* === conv_fuel_sound === *)
  intros k; induction k as [|k IH] using nat_ind; intros; simpl in H; try discriminate.
  - (* k = S k, main cases on v,w *)

    destruct v; destruct w; simpl in H; try discriminate.

    + (* VStar, VStar *)
      now constructor.

    + (* VNat, VNat *)
      now constructor.

    + (* VPi ... *)
      cbn in H.
      destruct (conv_fuel k v w) eqn:HA; try discriminate.
      apply IH in HA as HAA.
      destruct (clos_eval_fuel k c fresh) eqn:HB; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
      apply clos_eval_fuel_sound in HB.
      apply clos_eval_fuel_sound in HB'.
      apply IH in H as HBB.
      eapply CoV_Pi; [exact HAA|].
      intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy.
    + (* VSigma ... *)
      cbn in H.
      destruct (conv_fuel k v w) eqn:HA; try discriminate.
      apply IH in HA as HAA.
      destruct (clos_eval_fuel k c fresh) eqn:HB; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
      apply clos_eval_fuel_sound in HB.
      apply clos_eval_fuel_sound in HB'.
      apply IH in H as HBB.
      eapply CoV_Sigma; [exact HAA|].
      intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy.

    + (* VLam cl1, VLam cl2 *)
      cbn in H.
      destruct (clos_eval_fuel k c fresh) eqn:HC; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HC'; try discriminate.
      apply clos_eval_fuel_sound in HC.
      apply clos_eval_fuel_sound in HC'.
      apply IH in H.
      constructor. 
      intros.
      destruct c, c0. simpl in *.
      specialize (eval'_det _ _ _ _ H0 HC); intros. subst.
      specialize (eval'_det _ _ _ _ H1 HC'); intros. subst.
      easy.

    + (* VPair ... *)
      apply Bool.andb_true_iff in H as [H12 H34].
      apply Bool.andb_true_iff in H34 as [H1 H2].
      apply Bool.andb_true_iff in H2 as [H3 H4].
      apply IH in H12.
      apply IH in H1.
      apply IH in H3.
      apply IH in H4.
      constructor; easy.

    + (* VZero, VZero *)
      now constructor.

    + (* VSucc n, VSucc n' *)
      now constructor; apply IH.

    + (* VNeutral n, VNeutral n' *)
      now apply conv_neutral_fuel_sound with (k := k).
    + apply Bool.andb_true_iff in H as [H1 H2].
      apply IH in H2.
      apply IH in H1.
     constructor; easy.
    
    + constructor. apply IH. easy.
    + apply Bool.andb_true_iff in H as [H1 H2].
      apply Bool.andb_true_iff in H2 as [H2 H3].
      apply Bool.andb_true_iff in H3 as [H3 H4].
      constructor. apply IH. easy.
      apply IH. easy.
      apply IH. easy.
      apply IH. easy.

  (* === conv_neutral_fuel_sound === *)
  - (* start neutral branch *)
    intros k; induction k as [|k IH] using nat_ind; intros; simpl in H; try discriminate.
    destruct n; destruct n'; simpl in H; try discriminate.

    + (* NVar *)
      apply Nat.eqb_eq in H. subst.
      constructor.

    + (* NApp *)
      apply Bool.andb_true_iff in H as [Hh Ha].
      specialize (IH _ _ Hh).
      apply conv_fuel_sound in Ha.
      econstructor; eauto.

    + (* NFst *)
      now constructor; eauto using IH.

    + (* NSnd *)
      now constructor; eauto using IH.

    + (* NNatRec *)
     apply Bool.andb_true_iff in H as [H Htail].
     apply Bool.andb_true_iff in Htail as [Hs Htail].
     apply Bool.andb_true_iff in Htail as [Hn Htail].
      apply conv_fuel_sound in H.
      apply conv_fuel_sound in Hs.
      apply conv_fuel_sound in Hn.
      (* Order was P, z, s, then n; adjust if your andb nesting differs *)
      econstructor; eauto.
Qed.

(* B(n) := Vec (S n) Nat  where n is Var 0 *)
Definition ClVecSuccNat : closure :=
  Cl [] (Vec (Succ (Var 0)) Nat).

(* Π(n:Nat). Vec (S n) Nat  as a semantic WHNF *)
Definition VPi_Nat_VecSuccNat : whnf :=
  VPi VNat ClVecSuccNat.

Compute (clos_eval_fuel 20 ClVecSuccNat fresh).
(* Expected:  Some (VVec (VSucc fresh) VNat) *)

Definition v5 : whnf :=
  VSucc (VSucc (VSucc (VSucc (VSucc VZero)))).

Compute (clos_eval_fuel 20 ClVecSuccNat v5).
(* Expected:  Some (VVec (VSucc v5) VNat)    i.e., Vec (S 5) Nat *)


Scheme eval'_recta      := Induction for eval'       Sort Prop
with   vapp_recta        := Induction for vapp        Sort Prop
with   eval_natrec_recta := Induction for eval_natrec Sort Prop.
Combined Scheme evalsys_rect from eval'_rect, vapp_rect, eval_natrec_rect.

(* --- Backward compatibility alias so old code using [convV] still compiles --- *)
(* Notation convV := conv. *)

Inductive infer : list whnf -> term -> whnf -> Prop :=
| I_Var : forall Γ x A,
    nth_error Γ x = Some A ->
    infer Γ (Var x) A

| I_Star : forall Γ, infer Γ Star VStar
| I_Nat  : forall Γ, infer Γ Nat  VStar

| I_Pi : forall Γ A B vA,
    (* A : Star *)
    infer Γ A VStar ->
    (* evaluate A to extend context semantically *)
    eval' (sem_env_of_ctx Γ) A vA ->
    (* B : Star under x:A *)
    infer (vA :: Γ) B VStar ->
    infer Γ (Pi A B) VStar

| I_Sigma : forall Γ A B vA,
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->
    infer (vA :: Γ) B VStar ->
    infer Γ (Sigma A B) VStar

| I_App : forall Γ t u A B vu vB,
    (* t : Π (x:A). B *)
    infer Γ t (VPi A B) ->
    (* u ⇐ A *)
    check Γ u A ->
    (* evaluate u to a semantic value (under Γ’s identity env) *)
    eval' (sem_env_of_ctx Γ) u vu ->
    (* result type is B·vu *)
    clos_eval' B vu vB ->
    infer Γ (App t u) vB

(* Lambda *synthesizes* a Pi when you also provide a codomain closure B
   such that the body checks against B·fresh under Γ extended by vA. *)
| I_Lam : forall Γ A b vA B vBodyTy,
    (* domain is a type *)
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->
    (* instantiate codomain at a fresh neutral; this *defines* what the body’s type is *)
    clos_eval' B fresh vBodyTy ->
    (* body checks against that instantiated codomain *)
    check (vA :: Γ) b vBodyTy ->
    (* result: the lambda synthesizes Π vA. B *)
    infer Γ (Lam A b) (VPi vA B)

| I_Fst : forall Γ p A B,
    infer Γ p (VSigma A B) ->
    infer Γ (TFst p) A

| I_Snd : forall Γ p A B vfst vB,
    (* p : Σ (x:A). B *)
    infer Γ p (VSigma A B) ->
    (* type of second projection is B · (fst p) *)
    (* We push a neutral for (fst p): that’s exactly the neutral head we get
       when p is neutral; when p is a pair, inference of p already gave us A,B. *)
    (* To stay simple, just state the resulting type via closure application
       to the WHNF of (TFst p). *)
    eval' (sem_env_of_ctx Γ) (TFst p) vfst ->
    clos_eval' B vfst vB ->
    infer Γ (TSnd p) vB

| I_Zero : forall Γ, infer Γ Zero VNat
| I_Succ : forall Γ n,
    check Γ n VNat ->
    infer Γ (Succ n) VNat

| I_NatRec : forall Γ P z s n vP vs vn v,
    (* P : Π Nat . Star *)
    infer Γ P (VPi VNat (Cl (sem_env_of_ctx Γ) Star)) ->
    (* z : P 0 *)
    (* infer/check P 0: use application rule in the semantic world *)
    eval' (sem_env_of_ctx Γ) P vP ->
    clos_eval' (match vP with VPi _ c => c | _ => Cl [] Star end) VZero v ->
    check Γ z v ->
    (* s : Π n:Nat. Π _:P n. P (S n) *)
    (* For brevity, assume s is annotated and typechecks appropriately *)
    eval' (sem_env_of_ctx Γ) s vs ->
    (* n : Nat *)
    check Γ n VNat ->
    eval' (sem_env_of_ctx Γ) n vn ->
    (* result type is P n *)
    clos_eval' (match vP with VPi _ c => c | _ => Cl [] Star end) vn v ->
    infer Γ (NatRec P z s n) v

(* infer Γ (Vec n A) ⋆  when  n : Nat  and  A : ⋆ *)
| I_Vec : forall Γ n A,
    infer Γ n VNat ->
    infer Γ A VStar ->
    infer Γ (Vec n A) VStar

(* -------------------- Vec introductions -------------------- *)

| I_VNil : forall Γ A vA,
    (* A : ⋆ *)
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->
    (* [] has type Vec 0 A *)
    infer Γ (VNil A) (VVec VZero vA)

| I_VCons : forall Γ A n x xs vA vn,
    (* A : ⋆ and n : Nat *)
    infer Γ A VStar ->
    check Γ n VNat ->
    (* evaluate the bits we’ll reuse semantically *)
    eval' (sem_env_of_ctx Γ) A vA ->
    eval' (sem_env_of_ctx Γ) n vn ->
    (* x : A  and  xs : Vec n A *)
    check Γ x vA ->
    check Γ xs (VVec vn vA) ->
    (* cons has type Vec (S n) A *)
    infer Γ (VCons A n x xs) (VVec (VSucc vn) vA)

(* -------------------- Vec eliminator -------------------- *)

| I_VecRec : forall Γ A P z s n xs
                    vA vP vs vn vxs
                    vPn vTy_res,
    (* A : ⋆ and compute its WHNF *)
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->

    (* Motive: P : Π n:Nat. Π _:Vec n A. ⋆ *)
    infer Γ P (VPi VNat (Cl (sem_env_of_ctx Γ)
                            (Pi (Vec (Var 0) A) Star))) ->
    eval' (sem_env_of_ctx Γ) P vP ->

    (* Step is assumed annotated and well-typed (as in your NatRec rule) *)
    eval' (sem_env_of_ctx Γ) s vs ->

    (* Scrutinee indices and value: n : Nat, xs : Vec n A *)
    check Γ n VNat ->
    eval' (sem_env_of_ctx Γ) n vn ->
    check Γ xs (VVec vn vA) ->
    eval' (sem_env_of_ctx Γ) xs vxs ->

    (* Result type is (P n) xs:
       1) instantiate P at n to get a Pi (over vectors) value vPn,
       2) extract its codomain closure and instantiate at xs. *)
    clos_eval'
      (match vP with VPi _ c => c | _ => Cl [] Star end)
      vn vPn ->
    clos_eval'
      (match vPn with VPi _ c => c | _ => Cl [] Star end)
      vxs vTy_res ->

    infer Γ (VecRec A P z s n xs) vTy_res

(* Introductions synthesize only when canonical: pair/lambda won’t synthesize without a target. *)
with check : list whnf -> term -> whnf -> Prop :=
| C_Sub : forall Γ t A A',
    infer Γ t A' ->
    conv A' A ->
    check Γ t A

| C_Lam : forall Γ A b vA vA' B,
    (* decodes the intended rule properly *)
    eval' (sem_env_of_ctx Γ) A vA ->
    (* expected type provides domain vA' and codomain closure B *)
    conv vA vA' ->
    (* body checks against B applied to a fresh neutral Var 0
       (implemented by just extending the context with vA' and checking b
        against the *semantic* result of applying B to that variable)
    *)
    (* Build the semantic type of the body *)
    (* Use a fresh neutral as the bound variable: *)
    let x := VNeutral (NVar 0) in
    forall vBodyTy,
      clos_eval' B x vBodyTy ->
      (* Check the body under Γ extended by vA' *)
      check (vA' :: Γ) b vBodyTy ->
      check Γ (Lam A b) (VPi vA' B)

| C_Pair : forall Γ A Btm a b vA va vBsnd Bcl,
    (* We are checking [Pair A Btm a b] against the expected Sigma type [VSigma vA Bcl] *)
    (* 1) A : Star and evaluate it to vA (domain of the Sigma) *)
    check Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->

    (* 2) a : vA and evaluate it to va (to instantiate the codomain) *)
    check Γ a vA ->
    eval' (sem_env_of_ctx Γ) a va ->

    (* 3) the type of b is Bcl · va *)
    clos_eval' Bcl va vBsnd ->
    check Γ b vBsnd ->

    (* Conclusion: the pair checks against the expected Sigma *)
    check Γ (Pair A Btm a b) (VSigma vA Bcl)

| C_AnnoNat : forall Γ n,
    infer Γ n VNat -> check Γ n VNat

(* Fallback: anything that synthesizes A' and is convertible to A checks. *)
| C_FromInfer : forall Γ t A A',
    infer Γ t A' ->
    conv A' A ->
    check Γ t A.

Scheme infer_rect := Induction for infer Sort Prop
with check_rect := Induction for check Sort Prop.
Combined Scheme typing_rect from infer_rect, check_rect.

Lemma clos_eval'_det_eq B vu v1 v2 :
  clos_eval' B vu v1 -> 
  clos_eval' B vu v2 -> 
  v1 = v2.
Proof. 
  destruct B; unfold clos_eval'; eauto using eval'_det. 
Qed.

Lemma clos_eval'_fresh_id_env n b v :
  clos_eval' (Cl (id_env n) b) (VNeutral (NVar 0)) v <-> 
  eval' (id_env (S n)) b v.
Proof. reflexivity. Qed.

Lemma check_of_infer :
  forall Γ t A, infer Γ t A -> check Γ t A.
Proof.
  intros Γ t A Hin.
  apply C_Sub with (A' := A).
  easy.
  admit.
Admitted.

Lemma app_checks_sem_subst :
  forall Γ t u vA B vu vB,
    infer Γ t (VPi vA B) ->
    check Γ u vA ->
    eval' (sem_env_of_ctx Γ) u vu ->
    clos_eval' B vu vB ->
    check Γ (App t u) vB.
Proof.
  intros. eapply C_FromInfer.
  - eapply I_App; eauto.
  - admit.
Admitted.

Lemma infer_beta_subst :
  forall Γ A b B vA vBodyTy u vu vB,
    (* synthesize Π from the lambda *)
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->
    clos_eval' B fresh vBodyTy ->
    check (vA :: Γ) b vBodyTy ->
    (* argument *)
    check Γ u vA ->
    eval' (sem_env_of_ctx Γ) u vu ->
    (* instantiate result type at the argument value *)
    clos_eval' B vu vB ->
    (* conclusion *)
    infer Γ (App (Lam A b) u) vB.
Proof.
  intros. eapply I_App.
  - eapply I_Lam; eauto.
  - exact H3.
  - exact H4.
  - exact H5.
Qed.

(* Example: From synthesis to checking (if you don’t have a C_Sub rule) *)
Lemma check_of_infer_mutual :
  (forall Γ t A, infer Γ t A -> check Γ t A) /\
  (forall Γ t A, check Γ t A -> True).
Proof.
  eapply (typing_rect
    (fun Γ t A _ => check Γ t A)   (* motive for infer *)
    (fun Γ t A _ => True)); intros.
  - apply C_Sub with (A' := A).
    constructor. easy.
    admit.
  - 
  
          (* motive for check *)
  all:intros; try exact I.

  (* For each infer-constructor, replay the corresponding check rule.
     In App, use the IHs you get for the function and argument premises. *)
Admitted.







