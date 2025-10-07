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

Definition env := list whnf.

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

(* Push a new head value; shift older entries so de Bruijn indices line up. *)
Definition env_cons (v : whnf) (ρ : env) : env :=
  v :: map (shift_whnf 1 0) ρ.

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
                  (VNeutral (NVecRec vA vP vz vs vn nx))
(* Add this to eval_vecrec to make it total on arbitrary vxs *)
| EVR_Other :
    forall vA vP vz vs vn vxs,
      (forall vw, vxs <> VNilV vw) ->
      (forall vw vn' va xs, vxs <> VConsV vw vn' va xs) ->
      (forall nx, vxs <> VNeutral nx) ->
      eval_vecrec vA vP vz vs vn vxs vz.

Scheme eval'_rect      := Induction for eval'        Sort Prop
with vapp_rect         := Induction for vapp         Sort Prop
with eval_natrec_rect  := Induction for eval_natrec  Sort Prop
with vapps_rect        := Induction for vapps        Sort Prop
with eval_vectrec_rect := Induction for eval_vecrec  Sort Prop.

Combined Scheme evalsys_mutind from eval'_rect, vapp_rect, eval_natrec_rect, vapps_rect, eval_vectrec_rect.

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
         Some vz  
    end
  end.

(* Convenience wrapper with a big default fuel. *)
Definition eval (ρ : env) (t : term) : option whnf :=
  evalk 500 ρ t.

(* Constant motive Nat : Nat -> Star  given as a term returning Nat *)
Definition PconstNat : term := Lam Nat Nat.

(* add : Nat -> Nat -> Nat *)
(* Definition add : term :=
  Lam Nat (                             (* m *)
    Lam Nat (                           (* n *)
      NatRec
        PconstNat                       (* P : Nat -> Star, constant Nat *)
        (Var 0)                         (* base: n *)
        (Lam Nat                        (* step: λ k:Nat. λ acc:Nat. Succ acc *)
          (Lam (App PconstNat (Var 0))
               (Succ (Var 0))))
        (Var 1)                         (* recurse on m *)
  )). *)

(* Correct: recurse on the SECOND argument (n),
   base = first argument (m) *)
Definition add : term :=
  Lam Nat (                             (* m : Nat *)
    Lam Nat (                           (* n : Nat *)
      NatRec
        PconstNat                       (* P : Nat -> Star, here constant Nat *)
        (Var 1)                         (* base: m *)
        (Lam Nat                        (* step: λ k:Nat. λ acc:Nat. Succ acc *)
          (Lam (App PconstNat (Var 0))
               (Succ (Var 0))))
        (Var 0)                         (* recurse on n *)
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
Definition nine : term := Succ eighth.

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
Eval compute in eval [] (App fib eighth).   (* = 21 *)
Eval compute in eval [] (App fib nine).   (* = 34 *)

(* plus k m := m + k, via add *)
Definition tm_plus (k m : term) : term := App (App add k) m.

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
Definition tm_vec_motive (A m : term) : term :=
  Lam Nat (Lam (Vec (Var 0) A) (Vec (tm_plus (Var 1) m) A)).

(* append A n xs m ys := VecRec A (tm_vec_motive A m) ys (tm_s_cons A m) n xs *)
Definition tm_append (A n xs m ys : term) : term :=
  VecRec A (tm_vec_motive A m) ys (tm_s_cons A m) n xs.

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

(* Expect: VConsV VNat (Succ (Succ Zero)) 1 (VConsV VNat (Succ Zero) 2 (VConsV VNat Zero 3 [])) *)
Compute evalk bigfuel [] tm_append_v12_v3.


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
- inversion H. easy. easy.
- inversion H1. subst.
  apply H0.
  apply H in H12. subst. easy.
  subst.
  exfalso. apply (H3 vw vn' va vxs). easy.
 - inversion H. subst.
   easy.
   subst. exfalso.
   apply (H2 nx). easy.
- inversion H.
  subst. easy. subst.
  exfalso. apply (n0 vw vn' va vxs0). easy.
  subst.
  exfalso.
  apply (n1 nx). easy.
  easy.
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
             constructor. easy. easy. easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * inversion H. subst. constructor; easy.
           * case_eq(vvecreck k vA vP vz vs w0 w2); intros.
             ** rewrite H0 in H.
                simpl.
                apply IHk in H0.
                apply EVR_Cons with (vrec := w3).
                easy. apply vappsk_sound in H. easy.
             ** rewrite H0 in H. easy.
Qed.

(* ---------- Completeness: relational ⇒ some fuel computes the same ---------- *)

Lemma vvecreck_other_complete :
  forall vA vP vz vs vn vxs,
    (forall vw,               vxs <> VNilV vw) ->
    (forall vw vn' va xs,     vxs <> VConsV vw vn' va xs) ->
    (forall nx : neutral,     vxs <> VNeutral nx) ->
    exists k, vvecreck k vA vP vz vs vn vxs = Some vz.
Proof.
  intros vA vP vz vs vn vxs Hnil Hcons Hneu.
  exists 1%nat. cbn.               (* unfold one fuel *)
  destruct vxs; try reflexivity.
  - (* VNilV _ *)    exfalso. eapply Hneu; reflexivity.
  - (* VConsV _ _ _ _ *) exfalso. eapply Hcons; reflexivity.
Qed.


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
    + apply vvecreck_other_complete; easy.
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

Lemma conv_fuel_monotone :
  forall k k' v w,
    k' >= k ->
    conv_fuel k v w = true ->
    conv_fuel k' v w = true
with conv_neutral_fuel_monotone :
  forall k k' n n',
    k' >= k ->
    conv_neutral_fuel k n n' = true ->
    conv_neutral_fuel k' n n' = true.
Proof. intro k.
       induction k; intros.
       + easy.
       + (* k = S k *)
        destruct k' as [|k'']; [lia|].
        rename H0 into Ht.
        simpl in Ht |- *.
        destruct v; destruct w; try discriminate; cbn in *.

        * (* VStar, VStar *) exact Ht.
        * (* VNat, VNat   *) exact Ht.

        * (* VPi A B, VPi A' B' *)
          destruct (conv_fuel k v w)   eqn:HA; try discriminate.
          destruct (clos_eval_fuel k c  fresh) eqn:HB; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
          (* from Ht we know conv_fuel k v0 v1 = true *)
          apply IHk with (k' := k'') in HA; try lia.
          rewrite HA.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w1); try lia.
          apply IHk; try lia. easy. easy. easy.

        * (* VPi A B, VPi A' B' *)
          destruct (conv_fuel k v w)   eqn:HA; try discriminate.
          destruct (clos_eval_fuel k c  fresh) eqn:HB; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HB'; try discriminate.
          (* from Ht we know conv_fuel k v0 v1 = true *)
          apply IHk with (k' := k'') in HA; try lia.
          rewrite HA.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w1); try lia.
          apply IHk; try lia. easy. easy. easy.
        * (* VLam cl1, VLam cl2 *)
          destruct (clos_eval_fuel k c  fresh) eqn:HC; try discriminate.
          destruct (clos_eval_fuel k c0 fresh) eqn:HC'; try discriminate.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w); try lia.
          rewrite clos_eval_fuel_monotone with (k := k) (v := w0); try lia.
          apply IHk; try lia. easy. easy. easy.

        * (* VPair A B a b, VPair A' B' a' b' *)
          apply Bool.andb_true_iff in Ht as [HAB Hab].
          apply Bool.andb_true_iff in Hab as [Ha Hb].
          apply Bool.andb_true_iff in Hb  as [Ha' Hb'].
          apply IHk with (k' := k'') in HAB; try lia.
          apply IHk with (k' := k'') in Ha; try lia.
          apply IHk with (k' := k'') in Ha'; try lia.
          apply IHk with (k' := k'') in Hb'; try lia.
          rewrite HAB, Ha, Ha', Hb'. easy.
        * easy.

        * apply IHk; try lia. (* VZero, VZero *) exact Ht.

        * (* VNeutral n, VNeutral n' *)
          apply conv_neutral_fuel_monotone with (k := k); try lia. exact Ht.

        * (* VVec n A, VVec n' A' *)
          apply Bool.andb_true_iff in Ht as [Hn HA].
          apply IHk with (k' := k'') in Hn; try lia.
          apply IHk with (k' := k'') in HA; try lia.
          rewrite Hn, HA. easy.

        * (* VNilV A, VNilV A' *)
          eapply (IHk k''); [lia| exact Ht].

        * (* VConsV A n x xs, VConsV A' n' x' xs' *)
          apply Bool.andb_true_iff in Ht as [HA Hrest].
          apply Bool.andb_true_iff in Hrest as [Hn Htail].
          apply Bool.andb_true_iff in Htail as [Hx Hxs].
          apply IHk with (k' := k'') in HA; try lia.
          apply IHk with (k' := k'') in Hn; try lia.
          apply IHk with (k' := k'') in Hx; try lia.
          apply IHk with (k' := k'') in Hxs; try lia.
          rewrite HA, Hn, Hx, Hxs. easy.

    (* ===== neutral lemma ===== *)
    + intros k; induction k as [|k IH] using nat_ind; intros k' n n' Hge Ht.
      ++ simpl in Ht; discriminate.
      ++ destruct k' as [|k'']; [lia|].
        simpl in Ht |- *.
        destruct n; destruct n'; try discriminate; cbn in *.

        * (* NVar *) (* Nat.eqb i j = true remains true at higher fuel trivially *)
          exact Ht.

        * (* NApp *)
          apply Bool.andb_true_iff in Ht as [Hh Ha].
          apply IH with (k' := k'') in Hh; try lia.
          apply conv_fuel_monotone with (k' := k'') in Ha; try lia.
          rewrite Hh, Ha. easy.
          
        * (* NFst *)
          eapply IH; [lia| exact Ht].

        * (* NSnd *)
          eapply IH; [lia| exact Ht].

        * (* NNatRec *)
          apply Bool.andb_true_iff in Ht as [HP Htail].
          apply Bool.andb_true_iff in Htail as [Hz Htail'].
          apply Bool.andb_true_iff in Htail' as [Hs Hn].
          apply conv_fuel_monotone with (k' := k'') in HP; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hz; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hs; try lia.
          apply IH with (k' := k'') in Hn; try lia.
          rewrite HP, Hz, Hs, Hn. reflexivity.

        * (* VVecRec *)
          apply Bool.andb_true_iff in Ht as [HP Htail].
          apply Bool.andb_true_iff in Htail as [Hz Htail'].
          apply Bool.andb_true_iff in Htail' as [Hs Hn].
          apply Bool.andb_true_iff in Hn as [Hu Hn].
          apply Bool.andb_true_iff in Hn as [Hv Hn].
          apply conv_fuel_monotone with (k' := k'') in HP; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hz; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hs; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hu; try lia.
          apply conv_fuel_monotone with (k' := k'') in Hv; try lia.
          apply IH with (k' := k'') in Hn; try lia.
          rewrite HP, Hz, Hs, Hn, Hv, Hu. reflexivity.
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
      apply ConvClo with (v := w0) (v' := w1).
      easy. easy. easy.
      
      
(*       intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy. *)
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
      apply ConvClo with (v := w0) (v' := w1).
      easy. easy. easy.
(*       intros vB vB'.
      intros HvB HvB'.
      unfold clos_eval' in *.
      destruct c, c0.
      specialize (eval'_det _ _ _ _ HvB HB); intros. subst.
      specialize (eval'_det _ _ _ _ HvB' HB'); intros. subst.
      easy. *)

    + (* VLam cl1, VLam cl2 *)
      cbn in H.
      destruct (clos_eval_fuel k c fresh) eqn:HC; try discriminate.
      destruct (clos_eval_fuel k c0 fresh) eqn:HC'; try discriminate.
      apply clos_eval_fuel_sound in HC.
      apply clos_eval_fuel_sound in HC'.
      apply IH in H.
      constructor.
      apply ConvClo with (v := w) (v' := w0).
      easy. easy. easy.
(*       intros.
      destruct c, c0. simpl in *.
      specialize (eval'_det _ _ _ _ H0 HC); intros. subst.
      specialize (eval'_det _ _ _ _ H1 HC'); intros. subst.
      easy. *)

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
    +  apply Bool.andb_true_iff in H as [H Htail].
     apply Bool.andb_true_iff in Htail as [Hs Htail].
     apply Bool.andb_true_iff in Htail as [Hn Htail].
     apply Bool.andb_true_iff in Htail as [Hu Htail].
     apply Bool.andb_true_iff in Htail as [Hv Htail].
      apply conv_fuel_sound in H.
      apply conv_fuel_sound in Hs.
      apply conv_fuel_sound in Hn.
      apply conv_fuel_sound in Hu.
      apply conv_fuel_sound in Hv. 
      (* Order was P, z, s, then n; adjust if your andb nesting differs *)
      econstructor; eauto.
Qed.

(* If not already present: fuelled closure-eval and its facts *)
Definition clos_evalk (k:nat) (cl:closure) : option whnf :=
  match cl with Cl ρ body => evalk k (env_cons fresh ρ) body end.

Lemma clos_evalk_complete :
  forall cl v, clos_eval' cl fresh v -> exists k, clos_evalk k cl = Some v.
Proof.
  intros [ρ body] v H; simpl in *.
  now eapply evalk_complete in H.
Qed.

Lemma clos_evalk_monotone :
  forall k k' cl v,
    k' >= k ->
    clos_evalk k cl = Some v ->
    clos_evalk k' cl = Some v.
Proof.
  intros k k' [ρ body] v Hge H; simpl in *.
  eauto using evalk_monotone.
Qed.

Lemma lift_conv_fuel :
  forall v w K k, k >= K ->
  conv_fuel K v w = true -> conv_fuel k v w = true.
Proof. intros; eapply conv_fuel_monotone; eauto. Qed.

Lemma lift_clos_eval :
  forall B v K k,
  k >= K -> clos_eval_fuel K B fresh = Some v ->
  clos_eval_fuel k  B fresh = Some v.
Proof. intros; eapply clos_eval_fuel_monotone; eauto. Qed.

Lemma conv_complete :
  (forall v w, conv v w -> exists k, conv_fuel k v w = true) /\
  (forall B B', conv_clo B B' -> exists k v v', clos_eval_fuel k B  fresh = Some v /\ clos_eval_fuel k B' fresh = Some v' /\ conv_fuel k v v' = true).
Proof.
  apply (conv_mutind
    (* P: depends on the derivation (3rd arg). *)
    (fun v w _ =>
       exists k, conv_fuel k v w = true)
    (* Q: ***also*** depends on the derivation h *)
    (fun B B' h =>
       exists k, exists v v',
         clos_eval_fuel k B  fresh = Some v /\
         clos_eval_fuel k B' fresh = Some v' /\
         conv_fuel k v v' = true)); intros.
   10:{
     destruct H as (kA, HA).
     destruct H0 as (kB, HB).
     exists (S (S (Nat.max kA kB))).
     simpl.
     destruct kA. easy.
     rewrite conv_neutral_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. simpl in HA. easy.
     }
     9:{ exists 2. simpl. apply Nat.eqb_refl. }
     9:{ destruct H as (k, H).
         destruct k. easy.
         exists (S (S k)). simpl.
         simpl in H. easy.
     }
     15:{ intros.
          destruct H as (k3, H).

          destruct (clos_eval_fuel_complete B  fresh v  c) as [k1 HK1].
          destruct (clos_eval_fuel_complete B' fresh v' c0) as [k2 HK2].

          (* pick a large enough fuel *)
          set (K := Nat.max k3 (Nat.max k1 k2)).
          exists K, v, v'. repeat split.

          rewrite clos_eval_fuel_monotone with (k := k1) (v := v); try lia.
          easy. apply HK1. lia. apply HK2. lia.
          rewrite conv_fuel_monotone with (k := k3); try lia. easy.
     }
   - exists 1. easy.
   - exists 1. easy.
   - destruct H as (kA, HA).
     destruct H0 as (kB, (v1, (v2, (Hb1, (Hb2, Hc))))).
     exists (S (Nat.max kA kB)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v1); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v2); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, HA).
     destruct H0 as (kB, (v1, (v2, (Hb1, (Hb2, Hc))))).
     exists (S (Nat.max kA kB)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v1); try lia.
     rewrite clos_eval_fuel_monotone with (k := kB) (v := v2); try lia.
     rewrite conv_fuel_monotone with (k := kB); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, (v1, (v2, (Ha1, (Ha2,Ha3))))).
     exists (S kA). simpl.
     rewrite Ha1, Ha2. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     exists (S (Nat.max kA (Nat.max ka (Nat.max kb kc)))).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     rewrite conv_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - exists 1. easy.
   - destruct H as (k, H).
     exists (S k). simpl. easy.
   - destruct H as (k, H).
     destruct k. easy.
     exists (S (S k)). simpl. simpl in H. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     destruct kc. easy.
     exists (S (S (Nat.max kA (Nat.max ka (Nat.max kb kc))))). simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     simpl. simpl in Hc.
     rewrite conv_neutral_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     exists (S (Nat.max kA ka)).
     simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     easy. easy.
   - destruct H as (k, H).
     exists (S k). simpl. easy.
   - destruct H as (kA, HA).
     destruct H0 as (ka, Ha). 
     destruct H1 as (kb, Hb).
     destruct H2 as (kc, Hc).
     exists (S ((Nat.max kA (Nat.max ka (Nat.max kb kc))))). simpl.
     rewrite conv_fuel_monotone with (k := kA); try lia.
     rewrite conv_fuel_monotone with (k := ka); try lia.
     rewrite conv_fuel_monotone with (k := kb); try lia.
     rewrite conv_fuel_monotone with (k := kc); try lia.
     easy. easy. easy. easy.
   - destruct H as (k1, HA).
     destruct H0 as (k2, HP).
     destruct H1 as (k3, Hz).
     destruct H2 as (k4, Hs).
     destruct H3 as (k5, Hn).
     destruct H4 as (k6, Hnx).
    
     destruct k6. easy.
     exists (S (S (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 k6))))))). simpl.
     rewrite conv_fuel_monotone with (k := k1); try lia.
     rewrite conv_fuel_monotone with (k := k2); try lia.
     rewrite conv_fuel_monotone with (k := k3); try lia.
     rewrite conv_fuel_monotone with (k := k4); try lia.
     rewrite conv_fuel_monotone with (k := k5); try lia.
     rewrite conv_neutral_fuel_monotone with (k := k6); try lia.
     simpl in Hnx. easy. easy. easy. easy. easy. easy.
Qed.

Corollary conv_complete_conv: forall v w, conv v w -> exists k, conv_fuel k v w = true.
Proof. destruct conv_complete as [H _]. exact H. Qed.

Corollary conv_complete_clo :
  forall B B',
    conv_clo B B' ->
    exists k v v',
      clos_eval_fuel k B  fresh = Some v /\
      clos_eval_fuel k B' fresh = Some v' /\
      conv_fuel k v v' = true.
Proof. destruct conv_complete as [_ H]. exact H. Qed.

(* ∀-style closure predicate *)
Inductive conv_clo_forall: closure -> closure -> Prop :=
| ConvClo_forall: forall B B',
  (forall v v',
    clos_eval' B  fresh v ->
    clos_eval' B' fresh v' ->
    conv_forall v v') -> conv_clo_forall B B'
   
with conv_forall : whnf -> whnf -> Prop :=
| CoF_Star  : conv_forall VStar VStar
| CoF_Nat   : conv_forall VNat  VNat

| CoF_Pi : forall A A' B B',
    conv_forall A A' ->
    conv_clo_forall B B' ->
    conv_forall (VPi A B) (VPi A' B')

| CoF_Sigma : forall A A' B B',
    conv_forall A A' ->
    conv_clo_forall B B' ->
    conv_forall (VSigma A B) (VSigma A' B')

| CoF_Lam : forall cl1 cl2,
    conv_clo_forall cl1 cl2 ->
    conv_forall (VLam cl1) (VLam cl2)

| CoF_Pair : forall A B a b A' B' a' b',
    conv_forall A A' -> conv_forall B B' ->
    conv_forall a a' -> conv_forall b b' ->
    conv_forall (VPair A B a b) (VPair A' B' a' b')

| CoF_Zero : conv_forall VZero VZero
| CoF_Succ : forall n n', conv_forall n n' -> conv_forall (VSucc n) (VSucc n')

(* Neutral congruence *)
| CoF_NVar    : forall i,
    conv_forall (VNeutral (NVar i)) (VNeutral (NVar i))
| CoF_NApp    : forall n n' v v',
    conv_forall (VNeutral n) (VNeutral n') -> conv_forall v v' ->
    conv_forall (VNeutral (NApp n v)) (VNeutral (NApp n' v'))
| CoF_NFst    : forall n n',
    conv_forall (VNeutral n) (VNeutral n') ->
    conv_forall (VNeutral (NFst n)) (VNeutral (NFst n'))
| CoF_NSnd    : forall n n',
    conv_forall (VNeutral n) (VNeutral n') ->
    conv_forall (VNeutral (NSnd n)) (VNeutral (NSnd n'))
| CoF_NNatRec : forall P P' z z' s s' n n',
    conv_forall P P' -> conv_forall z z' -> conv_forall s s' ->
    conv_forall (VNeutral n) (VNeutral n') ->
    conv_forall (VNeutral (NNatRec P z s n)) (VNeutral (NNatRec P' z' s' n'))

| CoF_Vec : forall n n' A A',
    conv_forall n n' -> conv_forall A A' ->
    conv_forall (VVec n A) (VVec n' A')

| CoF_VNil : forall A A',
    conv_forall A A' ->
    conv_forall (VNilV A) (VNilV A')

| CoF_VCons : forall A A' n n' x x' xs xs',
    conv_forall A A' -> conv_forall n n' ->
    conv_forall x x' -> conv_forall xs xs' ->
    conv_forall (VConsV A n x xs) (VConsV A' n' x' xs')

| CoF_NVecRec : forall A A' P P' z z' s s' n n' nx nx',
    conv_forall A A' -> conv_forall P P' -> conv_forall z z' ->
    conv_forall s s' -> conv_forall n n' ->
    conv_forall (VNeutral nx) (VNeutral nx') ->
    conv_forall (VNeutral (NVecRec A P z s n nx))
                (VNeutral (NVecRec A' P' z' s' n' nx')).

Scheme conv_forall_rect      := Induction for conv_forall      Sort Prop
with   conv_clo_forall_rect := Induction for conv_clo_forall Sort Prop.
Combined Scheme conv_forall_mutind from conv_forall_rect, conv_clo_forall_rect.

Inductive conv_clo_exists_forall : closure -> closure -> Prop :=
| ConvCloE : forall B B' v v',
    clos_eval' B  fresh v ->
    clos_eval' B' fresh v' ->
    conv_forall v v' ->
    conv_clo_exists_forall B B'.

Lemma conv_clo_forall_to_conv_clo_exists_forall :
  forall B B',
    conv_clo_forall B B' ->
    (exists v,  clos_eval' B  fresh v) ->
    (exists v', clos_eval' B' fresh v') ->
    conv_clo_exists_forall B B'.
Proof.
  intros B B' H [v Hv] [v' Hv'].
  inversion H as [B1 B1' Hf]; subst.
  eapply ConvCloE; eauto using Hf.
Qed.

Lemma eval'_TFst_Var_exists :
  forall ρ x v, eval' (env_cons fresh ρ) (Var x) v ->
    exists r, eval' (env_cons fresh ρ) (TFst (Var x)) r.
Proof.
  intros ρ x v Hv; destruct v;
    eauto using E'_TFst_Pair, E'_TFst_Neut
         (* and the fallback: *) .
  - eexists; eapply E'_TFst_Other; eauto;
      [ intros A B va vb H; discriminate H
      | intros n H; discriminate H ].
  - exists VNat. constructor; easy.
  - exists (VPi v c). constructor; easy.
  - exists (VSigma v c). constructor; easy.
  - exists (VLam c). constructor; easy.
  - exists (VZero). constructor; easy.
  - exists (VSucc v). constructor; easy.
  - exists (VVec v1 v2). constructor; easy.
  - exists (VNilV v). constructor; easy.
  - exists (VConsV v1 v2 v3 v4). constructor; easy.
Qed.

Lemma eval'_TFst_App_exists :
  forall ρ t u v1 vt vu, 
    eval' (env_cons fresh ρ) (App t u) v1 ->
    eval' (env_cons fresh ρ) t vt ->
    eval' (env_cons fresh ρ) u vu ->
    vapp vt vu v1 ->
    exists r, eval' (env_cons fresh ρ) (TFst (App t u)) r.
Proof.
  intros ρ t u v1 vt vu HeApp _ _ _.
  (* split on the shape of the WHNF of (App t u) *)
  destruct v1 eqn:Ev; 
    try ( (* “other” shapes: Star/Nat/Pi/Sigma/Lam/Zero/Succ *)
         eexists; 
         (* rewrite the scrutinee to the chosen shape in the hypothesis *)
         rewrite Ev in HeApp; 
         (* use the 'other/stuck' TFst rule; discharge side-conditions by discriminate *)
         eapply E'_TFstOther; [exact HeApp
                              | intros A B a b H; discriminate H
                              | intros n H; discriminate H ]);
    eauto.
  - exists VStar. constructor; easy.
  - exists VNat. constructor; easy.
  - exists (VPi w c). constructor; easy.
  - exists (VSigma w c). constructor; easy.
  - exists (VLam c). constructor; easy.
  - eauto using E'_TFst_Pair, E'_TFst_Neut.
  - exists (VZero). constructor; easy.
  - exists (VSucc w). constructor; easy.
  - eauto using E'_TFst_Pair, E'_TFst_Neut.
  - subst. exists (VVec w1 w2). constructor; easy.
  - exists (VNilV w). constructor; easy.
  - exists (VConsV w1 w2 w3 w4). constructor; easy.
Qed.

Lemma eval'_TFst_Fst_exists :
  forall ρ p v1 A B vb, 
    eval' (env_cons fresh ρ) (TFst p) v1 ->
    eval' (env_cons fresh ρ) p (VPair A B v1 vb) ->
    exists r, eval' (env_cons fresh ρ) (TFst (TFst p)) r.
Proof.
  intros ρ p v1 A B vb Hfst _HpPair.
  (* Split on the shape of the value of (TFst p) *)
  destruct v1.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - (* VPi   *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSigma *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPair A1 B1 a b : first projection on a pair *)
    eexists. eapply E'_TFst_Pair. exact Hfst.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - (* VNeutral neu : becomes neutral NFst *)
    eexists. eapply E'_TFst_Neut. exact Hfst.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - eexists. eapply E'_TFst_Other; eauto; easy.
  - eexists. eapply E'_TFst_Other; eauto; easy.
Qed.

Lemma eval'_TFst_Snd_exists :
  forall ρ p va v1 A B, 
    eval' (env_cons fresh ρ) (TSnd p) v1 ->
    eval' (env_cons fresh ρ) p (VPair A B va v1) ->
    exists r, eval' (env_cons fresh ρ) (TFst (TSnd p)) r.
Proof.
  intros ρ p va v1 A B Hsnd _HpPair.
  (* case on the WHNF of (TSnd p) *)
  destruct v1.
  - (* VStar *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNat  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPi   *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSigma*) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VLam  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPair A1 B1 a b : fst returns a *)
    eexists. eapply E'_TFst_Pair. exact Hsnd.
  - (* VZero *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNeutral neu : becomes neutral NFst *)
    eexists. eapply E'_TFst_Neut. exact Hsnd.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
Qed.

Lemma eval'_TFst_TSnd_exists :
  forall ρ p n,
    eval' (env_cons fresh ρ) (TSnd p) (NSnd n) ->
    exists r, eval' (env_cons fresh ρ) (TFst (TSnd p)) r.
Proof.
  intros ρ p n Hsnd.
  eexists. eapply E'_TFst_Neut. exact Hsnd.
Qed.

Lemma eval'_TFst_NatRec_exists :
  forall ρ P z s n v1 vP vz vs vn,
    eval' (env_cons fresh ρ) (NatRec P z s n) v1 ->
    eval' (env_cons fresh ρ) P vP ->
    eval' (env_cons fresh ρ) z vz ->
    eval' (env_cons fresh ρ) s vs ->
    eval' (env_cons fresh ρ) n vn ->
    eval_natrec vP vz vs vn v1 ->
    exists v, eval' (env_cons fresh ρ) (TFst (NatRec P z s n)) v.
Proof.
  intros ρ P z s n v1 vP vz vs vn Hnr _ _ _ _ _.
  (* split on the shape of the WHNF of NatRec P z s n *)
  destruct v1 eqn:Ev;
    try ( (* “other” shapes: Star/Nat/Pi/Sigma/Lam/Zero/Succ *)
         eexists;
         rewrite Ev in Hnr;
         eapply E'_TFstOther; [exact Hnr
                              | intros A B a b H; discriminate H
                              | intros n' H; discriminate H ]);
    eauto.
  - (* VStar *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNat  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPi   *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSigma*) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VLam  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPair A1 B1 a b : fst returns a *)
    eexists. eapply E'_TFst_Pair. exact Hnr.
  - (* VZero *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNeutral neu : becomes neutral NFst *)
    eexists. eapply E'_TFst_Neut. exact Hnr.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
Qed.

Lemma eval'_TFst_VecRec_exists :
  forall ρ A P z s n xs v1 vA vP vz vs vn vxs,
    eval' (env_cons fresh ρ) (VecRec A P z s n xs) v1 ->
    eval' (env_cons fresh ρ) A vA  ->
    eval' (env_cons fresh ρ) P vP  ->
    eval' (env_cons fresh ρ) z vz  ->
    eval' (env_cons fresh ρ) s vs  ->
    eval' (env_cons fresh ρ) n vn  ->
    eval' (env_cons fresh ρ) xs vxs ->
    eval_vecrec vA vP vz vs vn vxs v1 ->
    exists v, eval' (env_cons fresh ρ) (TFst (VecRec A P z s n xs)) v.
Proof.
  intros ρ A P z s n xs v1 vA vP vz vs vn vxs Hrec _ _ _ _ _ _ _.
  (* Case on the WHNF result of the VecRec *)
  destruct v1 eqn:Ev;
    try ( (* “other” shapes: Star/Nat/Pi/Sigma/Lam/Zero/Succ *)
         eexists;
         rewrite Ev in Hrec;
         eapply E'_TFstOther; [ exact Hrec
                              | intros A' B' a' b' H; discriminate H
                              | intros n' H; discriminate H ]).
  - (* VStar *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNat  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPi   *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSigma*) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VLam  *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VPair A1 B1 a b : fst returns a *)
    eexists. eapply E'_TFst_Pair. exact Hrec.
  - (* VZero *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VNeutral neu : becomes neutral NFst *)
    eexists. eapply E'_TFst_Neut. exact Hrec.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
  - (* VSucc n *) eexists. eapply E'_TFst_Other; eauto.
    + intros A' B' a' b' H; discriminate H.
    + intros n' H; discriminate H.
Qed.

Lemma eval'_Var_exists :
  forall ρ n, exists v, eval' (env_cons fresh ρ) (Var n) v.
Proof.
  intros ρ n.
  destruct (nth_error (env_cons fresh ρ) n) as [v|] eqn:Hlk.
  - (* hit in the env: return that value *)
    eexists. constructor. exact Hlk.
    (* i.e. your Var-Some constructor: E'_VarSome Hlk *)
  - (* miss in the env: return neutral variable *)
    eexists. now constructor.
    (* i.e. your Var-None constructor: E'_VarNone Hlk *)
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

(* Identity environment of length n (Var i ↦ Neutral (NVar i)). *)
Fixpoint id_env (n : nat) : env :=
  match n with
  | 0 => []
  | S k => VNeutral (NVar 0) :: map (shift_whnf 1 0) (id_env k)
  end.

Definition sem_env_of_ctx (Γ : list whnf) : env := id_env (length Γ).

(* accept both syntactic lambda and Pi-value as “function closures” *)
Definition fn_closure_of (v : whnf) : option closure :=
  match v with
  | VLam cl   => Some cl
  | VPi _ c   => Some c
  | _         => None
  end.
  
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

(* (* Lambda *synthesizes* a Pi when you also provide a codomain closure B
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
 *)
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

| I_NatRec : forall Γ P z s n vP cP vn vTy vP0,
    (* P : Π Nat . Star *)
    check Γ P (VPi VNat (Cl (sem_env_of_ctx Γ) Star)) ->
    eval' (sem_env_of_ctx Γ) P vP ->
    fn_closure_of vP = Some cP ->          (* or: exists cP, ... *)
    (* z : P 0 *)
    clos_eval' cP VZero vP0 ->
    check Γ z vP0 ->
    (* s well-typed: you can keep it as a separate premise or as you had it *)
    (* n : Nat *)
    check Γ n VNat ->
    eval' (sem_env_of_ctx Γ) n vn ->
    (* result type is (P n) i.e. cP·vn *)
    clos_eval' cP vn vTy ->
    infer Γ (NatRec P z s n) vTy


(* infer Γ (Vec n A) ⋆  when  n : Nat  and  A : ⋆ *)
| I_Vec : forall Γ n A,
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
                    vA vP vn vxs
                    cP vPn c2 vTy_res,
    infer Γ A VStar ->
    eval' (sem_env_of_ctx Γ) A vA ->

    (* P checks against the expected Π Nat. Π (Vec …). ★ *)
    check Γ P (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) A) Star))) ->
    eval' (sem_env_of_ctx Γ) P vP ->

    check Γ n VNat -> eval' (sem_env_of_ctx Γ) n vn ->
    check Γ xs (VVec vn vA) -> eval' (sem_env_of_ctx Γ) xs vxs ->

    (* instantiate the *value* of P twice via its closure *)
    fn_closure_of vP = Some cP ->
    clos_eval' cP vn vPn ->
    fn_closure_of vPn = Some c2 ->
    clos_eval' c2 vxs vTy_res ->

    infer Γ (VecRec A P z s n xs) vTy_res

(* Introductions synthesize only when canonical: pair/lambda won’t synthesize without a target. *)
with check : list whnf -> term -> whnf -> Prop :=

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

(* expected type is VSigma Aexp Bcl; we allow the syntactic Aty
   to evaluate to some vA_eval merely convertible to Aexp *)
| C_Pair : forall Γ Aty Btm a b Aexp Bcl vA_eval va vBsnd,
    (* 1) Aty : ⋆ and evaluate it *)
    check Γ Aty VStar ->
    eval' (sem_env_of_ctx Γ) Aty vA_eval ->

    (* 2) the first component a : vA_eval and evaluate it *)
    check Γ a vA_eval ->
    eval' (sem_env_of_ctx Γ) a va ->

    (* 3) instantiate codomain with that evaluated first component *)
    clos_eval' Bcl va vBsnd ->
    check Γ b vBsnd ->

    (* 4) crucial alignment: the domain we computed is convertible to the expected domain *)
    conv vA_eval Aexp ->

    check Γ (Pair Aty Btm a b) (VSigma Aexp Bcl)


(* | C_Pair : forall Γ A Btm a b vA va vBsnd Bcl,
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
 *)
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

(* helper to peel a codomain closure out of a vPi value;
   fall back to a dummy closure if needed (shouldn't happen on well-typed inputs). *)
Definition codclo_of (v : whnf) (Γ : list whnf) : closure :=
  match v with
  | VPi _ c => c
  | _       => Cl (sem_env_of_ctx Γ) Star
  end.

Fixpoint infer_fuel (k:nat) (Γ:list whnf) (t:term) : option whnf :=
  match k with
  | 0 => None
  | S k' =>
    match t with
    | Var x => nth_error Γ x
    | Star  => Some VStar
    | Nat   => Some VStar

    | Pi A B =>
        match infer_fuel k' Γ A with
        | Some VStar =>
            match evalk k' (sem_env_of_ctx Γ) A with
            | Some vA =>
                match infer_fuel k' (vA :: Γ) B with
                | Some VStar => Some VStar
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end

    | Sigma A B =>
        match infer_fuel k' Γ A with
        | Some VStar =>
            match evalk k' (sem_env_of_ctx Γ) A with
            | Some vA =>
                match infer_fuel k' (vA :: Γ) B with
                | Some VStar => Some VStar
                | _ => None
                end
            | _ => None
            end
        | _ => None
        end

    | App t u =>
        match infer_fuel k' Γ t with
        | Some (VPi A B) =>
            match check_fuel k' Γ u A with
            | true =>
                match evalk k' (sem_env_of_ctx Γ) u with
                | Some vu =>
                    match clos_eval_fuel k' B vu with
                    | Some vB => Some vB
                    | None => None
                    end
                | None => None
                end
            | false => None
            end
        | _ => None
        end
        
    | Lam  _ _ | Pair _ _ _ _ =>
        (* Pairs don’t synthesize; they only check against an expected Sigma *)
        None
    | TFst p =>
        match infer_fuel k' Γ p with
        | Some (VSigma A _B) => Some A
        | _ => None
        end

    | TSnd p =>
        match infer_fuel k' Γ p with
        | Some (VSigma _A B) =>
            match evalk k' (sem_env_of_ctx Γ) (TFst p) with
            | Some vfst =>
                match clos_eval_fuel k' B vfst with
                | Some vB => Some vB
                | None => None
                end
            | None => None
            end
        | _ => None
        end

    | Zero   => Some VNat
    | Succ n => if check_fuel k' Γ n VNat then Some VNat else None

| NatRec P z s n =>
    (* Expect P : Π Nat . ★  (checked, not inferred) *)
    let expP := VPi VNat (Cl (sem_env_of_ctx Γ) Star) in
    if check_fuel k' Γ P expP then
      match evalk k' (sem_env_of_ctx Γ) P with
      | Some vP =>
          match fn_closure_of vP with
          | Some cP =>
              (* evaluate the index *)
              match evalk k' (sem_env_of_ctx Γ) n with
              | Some vn =>
                  (* result type is (cP · vn) *)
                  match clos_eval_fuel k' cP vn with
                  | Some vTy =>
                      (* base has type (cP · 0), and n : Nat *)
                      match clos_eval_fuel k' cP VZero with
                      | Some vP0 =>
                          if andb (check_fuel k' Γ z vP0)
                                  (check_fuel k' Γ n VNat)
                          then Some vTy
                          else None
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
    else None


| Vec n A =>
    match infer_fuel k' Γ A with
    | Some VStar => Some VStar
    | _ => None
    end


    | VNil A =>
        match infer_fuel k' Γ A with
        | Some VStar =>
            match evalk k' (sem_env_of_ctx Γ) A with
            | Some vA => Some (VVec VZero vA)
            | None => None
            end
        | _ => None
        end

    | VCons A n x xs =>
        match infer_fuel k' Γ A with
        | Some VStar =>
            match check_fuel k' Γ n VNat with
            | true =>
                match evalk k' (sem_env_of_ctx Γ) A,
                      evalk k' (sem_env_of_ctx Γ) n with
                | Some vA, Some vn =>
                    if andb (check_fuel k' Γ x vA)
                            (check_fuel k' Γ xs (VVec vn vA))
                    then Some (VVec (VSucc vn) vA)
                    else None
                | _, _ => None
                end
            | false => None
            end
        | _ => None
        end

    | VecRec A P z s n xs =>
        match infer_fuel k' Γ A with
        | Some VStar =>
          match evalk k' (sem_env_of_ctx Γ) A with
          | Some vA =>
            (* Expected type of P: Π n:Nat. Π xs:Vec n A. ★ *)
            let expP := VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) A) Star)) in
            if check_fuel k' Γ P expP then
              match evalk k' (sem_env_of_ctx Γ) P,
                    evalk k' (sem_env_of_ctx Γ) n,
                    evalk k' (sem_env_of_ctx Γ) xs with
              | Some vP, Some vn, Some vxs =>
                if andb (check_fuel k' Γ n VNat)
                        (check_fuel k' Γ xs (VVec vn vA))
                then
                  (* instantiate motive as a value, allowing VLam or VPi at each step *)
                  let app1 :=
                    match vP with
                    | VLam cl => clos_eval_fuel k' cl vn
                    | VPi  _ c => clos_eval_fuel k' c  vn
                    | _ => None
                    end in
                  match app1 with
                  | Some (VLam cl2) => clos_eval_fuel k' cl2 vxs
                  | Some (VPi  _ c2) => clos_eval_fuel k' c2  vxs
                  | _ => None
                  end
                else None
              | _, _, _ => None
              end
            else None
          | None => None
          end
        | _ => None
        end


    end
  end

with check_fuel (k:nat) (Γ:list whnf) (t:term) (Aexp:whnf) : bool :=
  match k with
  | 0 => false
  | S k' =>
    match t with
    | Lam Aann b =>
        match evalk k' (sem_env_of_ctx Γ) Aann with
        | Some vA =>
          match Aexp with                         (* ← use Aexp *)
          | VPi vA' B =>
              if conv_fuel k' vA vA'
              then
                match clos_eval_fuel k' B fresh with
                | Some vBodyTy =>
                    check_fuel k' (vA' :: Γ) b vBodyTy
                | None => false
                end
              else false
          | _ => false
          end
        | None => false
        end

| Pair Aty Btm a b =>
    match Aexp with
    | VSigma vA_exp Bcl =>
        if check_fuel k' Γ Aty VStar then
          match evalk k' (sem_env_of_ctx Γ) Aty with
          | Some vA_eval =>
              if conv_fuel k' vA_eval vA_exp then
                if check_fuel k' Γ a vA_eval then
                  match evalk k' (sem_env_of_ctx Γ) a with
                  | Some va =>
                      match clos_eval_fuel k' Bcl va with
                      | Some vBsnd => check_fuel k' Γ b vBsnd
                      | None => false
                      end
                  | None => false
                  end
                else false
              else false
          | None => false
          end
        else false
    | _ => false
    end

    | _ =>
        match infer_fuel k' Γ t with
        | Some A' => conv_fuel k' A' Aexp        (* ← use Aexp *)
        | None => false
        end
    end
  end.


Compute infer_fuel 1000 [] add.

Compute check_fuel 100 [] add (VPi VNat (Cl [] (Pi Nat Nat))).
Compute check_fuel 8 [] mult (VPi VNat (Cl [] (Pi Nat Nat))).

Definition xs1 := VCons Nat Zero (Succ Zero) (VNil Nat).  (* [1] *)
Definition ys1' := VCons Nat Zero Zero (VNil Nat).        (* [0] *)

Compute check_fuel 1000 []
  (tm_vec_motive Nat (Succ Zero))
  (VPi VNat (Cl [] (Pi (Vec (Var 0) Nat) Star))).

Compute infer_fuel 100 [] ys1'.
Compute infer_fuel 100 [] tm_append_v12_v3.

Compute check_fuel 1000 []
  (tm_append_v12_v3)
  (VVec (VSucc (VSucc (VSucc VZero))) VNat).


Lemma fn_closure_of_sound_app :
  forall k vP vn vPn c,
    (match vP with
     | VPi _ c' => clos_eval_fuel k c' vn
     | VLam cl  => clos_eval_fuel k cl  vn
     | _ => None
     end) = Some (VPi vPn c) ->
  exists cP, fn_closure_of vP = Some cP /\ clos_eval' cP vn (VPi vPn c).
Proof.
  intros k vP vn vPn c H; destruct vP; simpl in H; try discriminate.
  all: inversion H; subst; eexists; split; [reflexivity| eapply clos_eval_fuel_sound].
  exact H. exact H.
Qed.


Theorem infer_fuel_sound :
  forall k Γ t A, infer_fuel k Γ t = Some A -> infer Γ t A
with check_fuel_sound :
  forall k Γ t A, check_fuel k Γ t A = true -> check Γ t A.
Proof. intro k.
       induction k; intros.
       - easy.
       - simpl in H.
         case_eq t; intros; subst.
         + inversion H. subst. constructor.
         + inversion H. subst. constructor.
         + (* Pi A B *)
           destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
           destruct (infer_fuel k (w :: Γ) t1) eqn:HB; try discriminate.
           destruct w0; try discriminate.
           inversion H; subst.
           apply I_Pi with (vA := w).
           * eapply IHk; eauto.
           * apply evalk_sound with (k := k). easy.
           * eapply IHk; eauto.
         + (* Sigma A B *)
           destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
           destruct (infer_fuel k (w :: Γ) t1) eqn:HB; try discriminate.
           destruct w0; try discriminate.
           inversion H; subst.
           apply I_Sigma with (vA := w).
           * eapply IHk; eauto.
           * apply evalk_sound with (k := k). easy.
           * eapply IHk; eauto.
         + inversion H. subst. constructor.
         + case_eq(check_fuel k Γ t0 VNat); intros.
           * rewrite H0 in H. inversion H. constructor.
             apply check_fuel_sound with (k := k). easy.
           * rewrite H0 in H. easy.
         + (* Pair does not synthesize *)
           discriminate.
         + destruct (infer_fuel k Γ t0) eqn:Hp; try discriminate.
           destruct w; try discriminate.
           inversion H; subst.
           eapply I_Fst.
           eapply IHk; eauto.
         + (* TSnd p *)
           destruct (infer_fuel k Γ t0) eqn:Hp; try discriminate.
           destruct w; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) (TFst t0)) eqn:Ef; try discriminate.
           destruct (clos_eval_fuel k c w0) eqn:EB; try discriminate.
           inversion H; subst.
           apply I_Snd with (A:=w) (B:=c) (vfst:=w0) (vB:=A).
           * eapply IHk; eauto.
           * eapply evalk_sound; eauto.
           * eapply clos_eval_fuel_sound; eauto.
         + constructor. easy.
         + discriminate. 
                           
         + (* App t u *)
           destruct (infer_fuel k Γ t0) eqn:Ht; try discriminate.
           destruct w; try discriminate.
           destruct (check_fuel k Γ t1 w) eqn:Hu; try discriminate.
           destruct (evalk k (sem_env_of_ctx Γ) t1) eqn:Eu; try discriminate.
           destruct (clos_eval_fuel k c w0) eqn:EB; try discriminate.
           inversion H; subst.
(*            eapply I_App. *)
           apply I_App with (A:=w) (B:=c) (vu:=w0) (vB:=A).
           * eapply IHk; eauto.
           * eapply check_fuel_sound; eauto.
           * eapply evalk_sound; eauto.
           * eapply clos_eval_fuel_sound; eauto.
         + (* t = NatRec t0 t1 t2 t3, and H is the big match you showed *)
            simpl in H.
            destruct (check_fuel k Γ t0 (VPi VNat (Cl (sem_env_of_ctx Γ) Star))) eqn:HCp; try discriminate H.
            destruct (evalk k (sem_env_of_ctx Γ) t0) as [vP|] eqn:HP; try discriminate H.
            destruct (fn_closure_of vP) as [cP|] eqn:HcP; try discriminate H.
            destruct (evalk k (sem_env_of_ctx Γ) t3) as [vn|] eqn:Hn; try discriminate H.
            destruct (clos_eval_fuel k cP vn) as [vTy|] eqn:HTy; try discriminate H.
            destruct (clos_eval_fuel k cP VZero) as [vP0|] eqn:HP0; try discriminate H.
            (* split the final andb *)
            case_eq((check_fuel k Γ t1 vP0 && check_fuel k Γ t3 VNat)%bool); intros.
            rewrite H0 in H.
            apply Bool.andb_true_iff in H0.
            destruct H0 as [Hz HnNat]. inversion H. subst. clear H.
            (* the branch returns Some vTy, so A = vTy *)
(*             assert (A = vTy) by reflexivity. subst A. *)

            (* Now discharge premises of I_NatRec *)
            eapply I_NatRec.
            * (* check Γ P expP *)
              eapply check_fuel_sound; eauto.
            * (* eval' P vP *)
              eapply evalk_sound; eauto.
            * (* fn_closure_of vP = Some cP *)
              exact HcP.
            * (* clos_eval' cP VZero vP0 *)
              eapply clos_eval_fuel_sound; eauto.
            * (* check Γ z vP0 *)
              eapply check_fuel_sound; eauto.
            * (* check Γ n Nat *)
              eapply check_fuel_sound; eauto.
            * (* eval' n vn *)
              eapply evalk_sound; eauto.
            * (* clos_eval' cP vn vTy *)
              eapply clos_eval_fuel_sound; eauto.
            * rewrite H0 in H. easy.
        + (* Vec n A : ★ (relaxed) *)
          destruct (infer_fuel k Γ t1) eqn:HA; try discriminate.
          destruct w; try discriminate.
          inversion H; subst. constructor. eapply IHk; eauto.

        + (* VNil A *)
          destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
          destruct w; try discriminate.
          destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
          inversion H; subst.
          eapply I_VNil; eauto.
          * eapply evalk_sound; eauto.
    + (* VCons A n x xs *)
      destruct (infer_fuel k Γ t0) eqn:HA; try discriminate.
      destruct w; try discriminate.
      destruct (check_fuel k Γ t1 VNat) eqn:Hn; try discriminate.
      destruct (evalk k (sem_env_of_ctx Γ) t0) eqn:EA; try discriminate.
      destruct (evalk k (sem_env_of_ctx Γ) t1) eqn:EN; try discriminate.
      destruct (check_fuel k Γ t2 w) eqn:Hx; try discriminate.
      destruct (check_fuel k Γ t3 (VVec w0 w)) eqn:Hxs; try discriminate.
      simpl in H.
      inversion H; subst.
      eapply I_VCons with (vA:=w) (vn:=w0); eauto.
      * eapply evalk_sound; eauto.          (* vA *)
      * eapply evalk_sound; eauto.          (* vn *)
    +


      revert H.
      simpl.  (* unfold the VecRec branch of infer_fuel *)

      (* 1) A : ⋆, and its WHNF *)
      destruct (infer_fuel k Γ t0) as [ATy|] eqn:HA0; [| now discriminate].
      destruct ATy; try now discriminate.
      pose proof (IHk Γ t0 VStar HA0) as I_A.  (* infer Γ t0 ⋆ *)

      destruct (evalk k (sem_env_of_ctx Γ) t0) as [vA|] eqn:EA; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ EA) as EvA.

      (* 2) Motive P has the expected type (checked, not inferred) *)
      destruct (check_fuel k Γ t1
                 (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) t0) Star))))
               eqn:HP; [| now discriminate].
      pose proof (check_fuel_sound _ _ _ _ HP) as C_P.

      (* 3) Evaluate P, n, xs *)
      destruct (evalk k (sem_env_of_ctx Γ) t1) as [vP|] eqn:EP ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ EP) as EvP.

      destruct (evalk k (sem_env_of_ctx Γ) t4) as [vn|] eqn:En ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ En) as Evn.

      destruct (evalk k (sem_env_of_ctx Γ) t5) as [vxs|] eqn:Exs ; [| now discriminate].
      pose proof (evalk_sound _ _ _ _ Exs) as Evxs.


      (* name the two boolean checks *)
      remember (check_fuel k Γ t4 VNat)                 as bn  eqn:Hbn.
      remember (check_fuel k Γ t5 (VVec vn vA))         as bxs eqn:Hbxs.

      intros H.
      (* split the two boolean checks; kill the false branches using [H] *)
      destruct bn  eqn:Ebn  ; [| now discriminate H].
      destruct bxs eqn:Ebxs ; [| now discriminate H].
      simpl in H.

      (* from the booleans = true we get declarative checks *)
      assert (C_t4 : check Γ t4 VNat).
      { subst bn. apply check_fuel_sound with (k := k). easy. }
      assert (C_t5 : check Γ t5 (VVec vn vA)).
      { subst bxs. apply check_fuel_sound with (k := k). easy. }

      (* first semantic application of the motive: P n *)
      set (app1 :=
             match vP with
             | VPi _ c  => clos_eval_fuel k c  vn
             | VLam cl  => clos_eval_fuel k cl vn
             | _        => None
             end) in *.
      destruct app1 as [vPn|] eqn:Happ1 ; [| now discriminate H].


      (* only function shapes can yield a final [Some A] *)
      destruct vPn as
             [ | | dom c1 | dom c1 | cl1
               | | | | | | | ] ; try (simpl in H; now discriminate H).
      * (* vPn = VPi dom c1 *)
        destruct (clos_eval_fuel k c1 vxs) as [vTy|] eqn:Happ2 ; [| now discriminate H].
        inversion H; subst A; clear H.
          (* figure out which closure was used in the first app, and convert to [clos_eval'] *)
        destruct vP as
               [ | | A0 c0 | A0 c0 | cl0
                 | | | | | | |  ] ; try (simpl in Happ1; discriminate Happ1).
       
         ** (* vP = VPi A0 c0, so app1 = clos_eval_fuel k c0 vn *)
          simpl in Happ1.
          (* clos_eval' (first step) *)
          assert (CE1 : clos_eval' c0 vn (VPi dom c1)).
          { destruct (clos_eval_fuel k c0 vn) eqn:HP1 ;
              inversion Happ1; subst; eauto using clos_eval_fuel_sound. }
          (* clos_eval' (second step) *)
          assert (CE2 : clos_eval' c1 vxs vTy)
            by (eapply clos_eval_fuel_sound; exact Happ2).

          (* build the intended typing derivation *)
          eapply I_VecRec
            with (vA:=vA) (vP:=VPi A0 c0) (vn:=vn) (vxs:=vxs)
                 (vPn:=VPi dom c1) (vTy_res:=vTy); eauto.
            simpl. easy. simpl. easy.
        ** eapply I_VecRec
            with (vA:=vA) (vP:=(VLam cl0)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VPi dom c1) (vTy_res:=vTy) (cP := cl0) (c2 := c1); eauto.
            unfold app1 in *.
            apply clos_eval_fuel_sound with (k := k). easy.
            simpl.
            apply clos_eval_fuel_sound with (k := k). easy.
            
      * destruct cl1 as [ρ b].
        destruct (clos_eval_fuel k (Cl ρ b) vxs) as [vTy|] eqn:Happ2 ; [| now discriminate H].
        inversion H; subst A; clear H.

        (* again, find which closure produced [app1] and convert it to [clos_eval'] *)
        destruct vP as
               [ | | | | cl0
                 | | | | | | | ] ; try (simpl in Happ1; discriminate Happ1).
         ** (* vP = VLam cl0, so app1 = clos_eval_fuel k cl0 vn *)
          simpl in Happ1.
          unfold app1 in *.
          assert (CE1 : clos_eval' c vn (VLam (Cl ρ b))).
          { destruct (clos_eval_fuel k c vn) eqn:HP1 ;
              inversion Happ1; subst; eauto using clos_eval_fuel_sound. }
          assert (CE2 : clos_eval' (Cl ρ b) vxs vTy)
            by (eapply clos_eval_fuel_sound; exact Happ2).

          eapply I_VecRec
            with (vA:=vA) (vP:=(VPi vP c)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VLam (Cl ρ b)) (vTy_res:=vTy); eauto.
           simpl. easy. simpl. easy.
        ** eapply I_VecRec
            with (vA:=vA) (vP:=(VLam cl0)) (vn:=vn) (vxs:=vxs)
                 (vPn:=VLam (Cl ρ b)) (vTy_res:=vTy) (cP := cl0); eauto.
           unfold app1 in *.
           apply clos_eval_fuel_sound with (k := k). easy.
           simpl. easy.
           apply clos_eval_fuel_sound with (k := k). easy.
           
      - intro k.
        induction k; intros.
        + easy.
        + simpl in H.
          case_eq t; intros; subst.
          17:{ 
          case_eq(infer_fuel k Γ (VecRec t0 t1 t2 t3 t4 t5)); intros.
          rewrite H0 in H.
      eapply C_FromInfer.
      - (* from the synthesis boolean to declarative inference *)
        eapply infer_fuel_sound; eauto.      (* uses H0 : infer_fuel k Γ (VecRec …) = Some w *)
      - (* from the conversion boolean to declarative convertibility *)
        eapply conv_fuel_sound; eauto.
      - rewrite H0 in H. easy.
      }
        12:{
        case_eq(infer_fuel k Γ (App t0 t1)); intros.
        rewrite H0 in H.
        apply C_FromInfer with (A := A) (A' := w).
        apply infer_fuel_sound with (k := k). easy.
        apply conv_fuel_sound with (k := k). easy.
        rewrite H0 in H. easy.
      }

      11:{ 
      case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
      rewrite H0 in H.
      destruct A; try easy.
      case_eq( conv_fuel k w A); intros.
      rewrite H1 in H.
      case_eq(clos_eval_fuel k c fresh); intros.
      rewrite H2 in H.
      apply C_Lam with (vA := w) (vBodyTy := w0).
      apply evalk_sound with (k := k). easy.
      apply conv_fuel_sound with (k := k). easy.
      apply clos_eval_fuel_sound with (k := k). simpl.
      unfold fresh in *. easy.
      apply IHk. easy.
      rewrite H2 in H. easy.
      rewrite H1 in H. easy.
      rewrite H0 in H. easy.
      }

      7:{
          destruct A; try easy.
          case_eq(check_fuel k Γ t0 VStar); intros.
          rewrite H0 in H.
          case_eq(evalk k (sem_env_of_ctx Γ) t0); intros.
          rewrite H1 in H.
          case_eq(conv_fuel k w A); intros.
          rewrite H2 in H.
          case_eq(check_fuel k Γ t2 w); intros.
          rewrite H3 in H.
          case_eq(evalk k (sem_env_of_ctx Γ) t2 ); intros.
          rewrite H4 in H.
          case_eq(clos_eval_fuel k c w0); intros.
          rewrite H5 in H.
      eapply C_Pair with (va:=w0) (vBsnd:=w1) (Bcl:=c) (vA_eval := w).
      apply IHk. easy.
      apply evalk_sound with (k := k). easy.
      apply IHk. easy.
      apply evalk_sound with (k := k). easy.
      apply clos_eval_fuel_sound with (k := k). easy.
      apply IHk. easy.
      apply conv_fuel_sound with (k := k). easy.
      rewrite H5 in H. easy.
      rewrite H4 in H. easy.
      rewrite H3 in H. easy.
      rewrite H2 in H. easy.
      rewrite H1 in H. easy.
      rewrite H0 in H. easy.
      }

      9:{ case_eq( infer_fuel k Γ (Var n) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
          apply infer_fuel_sound with (k := k). easy.
          apply conv_fuel_sound with (k := k). easy.
          rewrite H0 in H. easy.
        }

      3:{ case_eq(infer_fuel k Γ (Pi t0 t1)); intros.
          + rewrite H0 in H.
            apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
       }
       
          

      2:{ destruct (infer_fuel k Γ Nat) eqn:Hinfer
        ; try (rewrite Hinfer in H; discriminate).

      eapply C_FromInfer.
      - eapply infer_fuel_sound; eauto.            (* infer Γ Nat w          *)
      - eapply conv_fuel_sound;  eauto.
      - easy.            (* conv  w       A        *)
          }

      2:{ case_eq(infer_fuel k Γ (Sigma t0 t1)); intros.
          + rewrite H0 in H.
            apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
       }

      5:{ case_eq(infer_fuel k Γ (TSnd t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      4:{ case_eq(infer_fuel k Γ (TFst t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (Vec t0 t1)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (VNil t0) ); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      5:{ case_eq(infer_fuel k Γ (VCons t0 t1 t2 t3)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      4:{ case_eq(infer_fuel k Γ (NatRec t0 t1 t2 t3)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      3:{ case_eq(infer_fuel k Γ (Succ t0)); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      2:{ case_eq(infer_fuel k Γ Zero); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
          + rewrite H0 in H. easy.
        }

      case_eq(infer_fuel k Γ Star); intros.
          rewrite H0 in H.
          apply C_FromInfer with (A' := w).
            apply infer_fuel_sound with (k := k). easy.
            apply conv_fuel_sound with (k := k). easy.
            rewrite H0 in H. easy.
Qed.

Theorem infer_check_fuel_monotone:
  (forall Γ t A k k', 
     k' >= k ->
     infer_fuel k Γ t = Some A -> 
     infer_fuel k' Γ t = Some A) /\
  (forall Γ t A k k', 
     k' >= k ->
     check_fuel k Γ t A = true -> 
     check_fuel k' Γ t A = true ).
Proof. eapply typing_rect; intros.
Admitted.



Theorem infer_fuel_monotone:
  (forall Γ t A k k', 
     k' >= k ->
     infer_fuel k Γ t = Some A -> 
     infer_fuel k' Γ t = Some A).
Proof. intros.
       eapply infer_check_fuel_monotone with (k' := k') (k := k); try lia.
       easy.
Qed.

Theorem check_fuel_monotone:
  (forall Γ t A k k', 
     k' >= k ->
     check_fuel k Γ t A = true -> 
     check_fuel k' Γ t A = true ).
Proof. intros.
       eapply infer_check_fuel_monotone with (k' := k') (k := k); try lia.
       easy.
Qed.


Lemma max_ge_s_k5 :
  forall k k0 k1 k2 k3 k4 k5,
    Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2
      (match Nat.max k4 (S k5) with
       | 0 => S k3
       | S m' => S (Nat.max k3 m')
       end)))) >= S k5.
Proof.
  intros k k0 k1 k2 k3 k4 k5.
  set (n := Nat.max k4 (S k5)).
  assert (Hn : n >= S k5) by (unfold n; apply Nat.le_max_r).
  destruct n as [|m'] eqn:En.
  - (* impossible: n = 0 but n >= S k5 *)
    simpl in Hn; lia.
  - (* n = S m' *)
    simpl.
    lia.
Qed.

Lemma max_ge_k4 :
  forall k k0 k1 k2 k3 k4 k5,
    Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2
      (match Nat.max k4 (S k5) with
       | 0 => S k3
       | S m' => S (Nat.max k3 m')
       end)))) >= k4.
Proof.
  intros k k0 k1 k2 k3 k4 k5.
  set (n := Nat.max k4 (S k5)).
  assert (Hn : n >= k4) by (unfold n; apply Nat.le_max_l).

  destruct n as [|m'] eqn:En.
  - (* n = 0 *)
    simpl.                        (* match yields S k3 *)
    repeat (apply Nat.le_trans with (m := Nat.max _ _); try apply Nat.le_max_l).
    apply Nat.le_trans with (m := S k3).
    + lia.
    + (* S k3 >= k4 (but here n = 0 so k4 = 0) *)
      simpl in Hn; lia.
  - (* n = S m' *)
    simpl. lia.
Qed.

Lemma max_ge_s_k2 :
  forall k k1 k2 k3,
    Nat.max k (Nat.max k1
      (match k3 with
       | 0 => S k2
       | S m' => S (Nat.max k2 m')
       end)) >= S k2.
Proof.
  intros k k1 k2 k3.
  destruct k3 as [| m']; simpl.
  - lia.
  - lia.
Qed.

Lemma max_ge_k3 :
  forall k k1 k2 k3,
    Nat.max k (Nat.max k1
      (match k3 with
       | 0 => S k2
       | S m' => S (Nat.max k2 m')
       end)) >= k3.
Proof.
  intros k k1 k2 k3.
  destruct k3 as [| m']; simpl.
  - lia.
  - lia.
Qed.

Theorem infer_fuel_complete :
  (forall Γ t A, infer Γ t A -> exists k, infer_fuel k Γ t = Some A) /\
  (forall Γ t A, check Γ t A -> exists k, check_fuel k Γ t A = true).
Proof.
  eapply typing_rect; intros.
  - exists 1. simpl. easy.
  - exists 1. simpl. easy.
  - exists 1. simpl. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    exists (S (Nat.max k (Nat.max k0 k1))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite infer_fuel_monotone with (k := k0) (A := VStar); try lia.
    easy.
    easy. easy. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    exists (S (Nat.max k (Nat.max k0 k1))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite infer_fuel_monotone with (k := k0) (A := VStar); try lia.
    easy.
    easy. easy. easy.
  - destruct H0 as (k0, H0).
    destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e1).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c0.
    destruct c0 as (k2, c0).

    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (S k2))))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vu); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := (VPi A (Cl l t0))); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := A); try lia.
    simpl.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vB); try lia.
    easy. unfold clos_eval_fuel. easy.
    easy. easy. easy.
  - destruct H as (k, H).
    exists (S k). simpl.
    rewrite H. easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c.
    destruct c as (k2, c).
    exists (S (Nat.max k (Nat.max k1 (S k2)))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := (VSigma A (Cl l t))); try lia.
    rewrite evalk_monotone with (k := k1) (v := vfst); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vB); try lia.
    easy. easy. easy. easy.
  - exists 1. easy.
  - destruct H as (k, H).
    exists (S k). simpl. rewrite H. easy.
  - destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H as (k, H).
    unfold clos_eval' in *.
    destruct cP.
    apply evalk_complete in e.
    destruct e as (k2, e).
    apply evalk_complete in c0.
    destruct c0 as (k3, c0).
    apply evalk_complete in e1.
    destruct e1 as (k4, e1).
    apply evalk_complete in c3.
    destruct c3 as (k5, c3).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max (S k3) (Nat.max k4 (S k5)))))))). simpl.
    rewrite check_fuel_monotone with (k := k) (A := (VPi VNat (Cl (sem_env_of_ctx Γ) Star))); try lia.
    rewrite evalk_monotone with (k := k2) (v := vP); try lia.
    rewrite e0.
    rewrite evalk_monotone with (k := k4) (v := vn); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k5) (v := vTy); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k3) (v := vP0); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := vP0); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := VNat); try lia.
    simpl. easy. easy. easy.
    destruct (Nat.max k4 (S k5)); lia. simpl. easy.
    apply max_ge_s_k5. simpl. easy.
    apply max_ge_k4. easy. easy. easy.
  - destruct H as (k, H).
    exists (S k). simpl. rewrite H.
    easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    exists (S (Nat.max k k1)). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    easy. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H2 as (k2, H2).
    apply evalk_complete in e, e0.
    destruct e as (k3, e).
    destruct e0 as (k4, e0).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 k4)))))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := VNat); try lia.
    rewrite evalk_monotone with (k := k3) (v := vA); try lia.
    rewrite evalk_monotone with (k := k4) (v := vn); try lia.
    rewrite check_fuel_monotone with (k := k2) (A := (VVec vn vA)); try lia.
    rewrite check_fuel_monotone with (k := k1) (A :=vA); try lia. 
    simpl. easy. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    destruct H2 as (k2, H2).
    apply evalk_complete in e, e0, e1, e2.
    destruct e as (k3, e).
    destruct e0 as (k4, e0).
    destruct e1 as (k5, e1).
    destruct e2 as (k6, e2).
    unfold clos_eval' in *.
    destruct cP, c2.
    apply evalk_complete in c3, c4.
    destruct c3 as (k7, c3).
    destruct c4 as (k8, c4).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 (Nat.max k6 (Nat.max (S k7) (S k8))))))))))). simpl.
    rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite evalk_monotone with (k := k3) (v := vA); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := (VPi VNat (Cl (sem_env_of_ctx Γ) (Pi (Vec (Var 0) A) Star)))); try lia.
    rewrite evalk_monotone with (k := k4) (v := vP); try lia.
    rewrite evalk_monotone with (k := k5) (v := vn); try lia.
    rewrite evalk_monotone with (k := k6) (v := vxs); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := VNat); try lia.
    rewrite check_fuel_monotone with (k := k2) (A := (VVec vn vA)); try lia.
    simpl.
    destruct vP; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k7) (v := vPn); try lia. 
    destruct vPn; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. 
    simpl in e4. inversion e4. easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. simpl in e4. inversion e4. easy.
    simpl. simpl in e3. inversion e3. easy.
    rewrite clos_eval_fuel_monotone with (k := S k7) (v := vPn); try lia. 
    destruct vPn; try easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. 
    simpl in e4. inversion e4. easy.
    rewrite clos_eval_fuel_monotone with (k := S k8) (v := vTy_res); try lia.
    easy. simpl. simpl in e4. inversion e4. easy.
    simpl. simpl in e3. inversion e3. easy.
    easy. easy. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    apply evalk_complete in e.
    destruct e as (k1, e).
    unfold clos_eval' in *.
    destruct B.
    apply evalk_complete in c0.
    destruct c0 as (k2, c0).
    apply conv_complete_conv in c.
    destruct c as (k3, c).
    exists (S (Nat.max k (Nat.max k1 (Nat.max (S k2) k3)))). simpl.
    rewrite evalk_monotone with (k := k1) (v := vA); try lia.
    rewrite conv_fuel_monotone with (k := k3); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k2) (v := vBodyTy); try lia.
    rewrite check_fuel_monotone with (k := k) (A := vBodyTy); try lia.
    easy.
    apply max_ge_s_k2. simpl. easy.
    apply max_ge_k3. easy. easy.
  - destruct H as (k, H).
    destruct H0 as (k0, H0).
    destruct H1 as (k1, H1).
    apply evalk_complete in e, e0.
    destruct e as (k2, e).
    destruct e0 as (k3, e0).
    apply conv_complete_conv in c3.
    destruct c3 as (k4, c3).
    unfold clos_eval' in *.
    destruct Bcl.
    apply evalk_complete in c1.
    destruct c1 as (k5, c1).
    exists (S (Nat.max k (Nat.max k0 (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (S k5)))))))).
    simpl.
    rewrite check_fuel_monotone with (k := k) (A := VStar); try lia.
    rewrite evalk_monotone with (k := k2) (v := vA_eval); try lia.
    rewrite conv_fuel_monotone with (k := k4); try lia.
    rewrite check_fuel_monotone with (k := k0) (A := vA_eval); try lia.
    rewrite evalk_monotone with (k := k3) (v := va); try lia.
    rewrite clos_eval_fuel_monotone with (k := S k5) (v := vBsnd); try lia.
    rewrite check_fuel_monotone with (k := k1) (A := vBsnd); try lia.
    easy. simpl. easy. easy. easy. easy. easy. easy.
  - destruct H as (k, H).
    inversion i.
    + subst. exists 2. simpl. rewrite H0. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
    + subst. destruct k. easy. exists (S (S k)). simpl in *. rewrite H. easy.
  - destruct H as (k, H).
    inversion i.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H2.
      destruct H2 as (k1, H2).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      unfold clos_eval' in *.
      destruct B. 
      apply evalk_complete in H3.
      destruct H3 as (k3, H3).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (S k3))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      unfold clos_eval' in *.
      destruct B. 
      apply evalk_complete in H2.
      destruct H2 as (k3, H2).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (S k3))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst. 
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VNat); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VNat); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1, H6.
      destruct H1 as (k1, H1).
      destruct H6 as (k2, H6).
      apply conv_complete_conv in c.
      destruct c as (k3, c).
      unfold clos_eval' in *.
      destruct cP.
      apply evalk_complete in H3, H7.
      destruct H3 as (k4, H3).
      destruct H7 as (k5, H7).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max (S k4) (S k5))))))). simpl in *.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k3); try lia. easy. easy.
    + subst.
      apply conv_complete_conv in c.
      destruct c as (k1, c).
      exists (S (Nat.max k k1)). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := VStar); try lia.
      rewrite conv_fuel_monotone with (k := k1); try lia. easy. easy.
    + subst. 
      apply evalk_complete in H1.
      destruct H1 as (k1, H1).
      apply conv_complete_conv in c.
      destruct c as (k2, c).
      exists (S (Nat.max k (Nat.max k1 k2))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := (VVec VZero vA)); try lia.
      rewrite conv_fuel_monotone with (k := k2); try lia. easy. easy.
    + subst.
      apply evalk_complete in H2, H3.
      destruct H2 as (k1, H2).
      destruct H3 as (k2, H3).
      apply conv_complete_conv in c.
      destruct c as (k3, c).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 k3)))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := (VVec (VSucc vn) vA)); try lia.
      rewrite conv_fuel_monotone with (k := k3); try lia. easy. easy.
    + subst.
      apply evalk_complete in H1, H3, H5, H7.
      destruct H1 as (k1, H1).
      destruct H3 as (k2, H3).
      destruct H5 as (k3, H5).
      destruct H7 as (k4, H7).
      apply conv_complete_conv in c.
      destruct c as (k5, c).
      unfold clos_eval' in *.
      destruct cP, c2.
      apply evalk_complete in H9, H11.
      destruct H9 as (k6, H9).
      destruct H11 as (k7, H11).
      exists (S (Nat.max k (Nat.max k1 (Nat.max k2 (Nat.max k3 (Nat.max k4 (Nat.max k5 (Nat.max (S k6) (S k7))))))))). simpl.
      rewrite infer_fuel_monotone with (k := k) (A := A'); try lia.
      rewrite conv_fuel_monotone with (k := k5); try lia. easy. easy.
Qed.


(** Preservation for synthesis *)
Theorem preservation_infer_bigstep :
  forall Γ t A v,
    infer Γ t A ->
    eval' (sem_env_of_ctx Γ) t v ->
    exists A0, (* a type value for the result *)
      (* either as an algorithmic type or via a value-typing judgement, see §2 *)
      conv A0 A.
Admitted.

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
  apply C_FromInfer with (A' := A).
  easy.
  apply conv_fuel_sound with (k := 1).
  simpl.
  destruct A; try easy.
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







