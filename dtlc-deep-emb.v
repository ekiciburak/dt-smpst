Require Import Coq.Lists.List Coq.Init.Nat Lia.
Import ListNotations.

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
  | NatRec : term -> term -> term -> term -> term.

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

with neutral : Type :=
| NVar     : nat -> neutral
| NApp     : neutral -> whnf -> neutral
| NFst     : neutral -> neutral
| NSnd     : neutral -> neutral
| NNatRec  : whnf -> whnf -> whnf -> neutral -> neutral

with closure : Type :=
| Cl : list whnf -> term -> closure.

Coercion VNeutral : neutral >-> whnf.

Definition env := list whnf.

(* ---------- Big-step evaluation (tidy, mutual) ---------- *)

(**
  eval' ρ t v      : under environment ρ, term t evaluates to value v (WHNF)
  vapp  v1 v2 v3   : semantic application (v1 v2) evaluates to v3 (β or neutral)
  eval_natrec vP vz vs vn v :
       semantic natrec with motive vP, base vz, step vs, on argument vn yields v
*)

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
    (* annotation A is ignored at WHNF *)
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

(* semantic application: either β-step for lambdas, or extend neutral spine *)
with vapp : whnf -> whnf -> whnf -> Prop :=

| VApp_Lam : forall ρ' b v v',
    eval' (v :: ρ') b v' ->
    vapp (VLam (Cl ρ' b)) v v'

| VApp_Neut : forall n v,
    vapp (VNeutral n) v (VNeutral (NApp n v))

(* ill-typed heads are left unchanged; this case is never used in well-typed runs,
   but keeps the relation total over arbitrary inputs. *)
(* | VApp_Other : forall w v,
    (forall ρ' b, w <> VLam (Cl ρ' b)) ->
    (forall n,   w <> VNeutral n) ->             (* NEW: exclude neutral *)
    (forall A B, w <> VPi A B) ->
    (forall A B, w <> VSigma A B) ->
    w <> VStar -> w <> VNat ->
    vapp w v w *)

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
    vapp vs vn v1 ->          (* s n *)
    vapp v1 vrec v ->         (* (s n) (rec n) *)
    eval_natrec vP vz vs (VSucc vn) v

| ENR_Neut : forall vP vz vs nn,
    eval_natrec vP vz vs (VNeutral nn) (VNeutral (NNatRec vP vz vs nn))

| ENR_Other : forall vP vz vs vn,
    (forall w, vn <> VSucc w) ->
    vn <> VZero ->
    (forall n, vn <> VNeutral n) ->
    eval_natrec vP vz vs vn vz.

(* ---------------------------------------------------------------- *)
(* 0) Shifting for semantic neutrals/values, to maintain de Bruijn   *)
(*    discipline when we extend environments.                        *)
(* ---------------------------------------------------------------- *)

Fixpoint shift_neutral (d c : nat) (n : neutral) : neutral :=
  match n with
  | NVar k        => NVar (if Nat.leb c k then k + d else k)
  | NApp n v      => NApp (shift_neutral d c n) (shift_whnf d c v)
  | NFst n        => NFst (shift_neutral d c n)
  | NSnd n        => NSnd (shift_neutral d c n)
  | NNatRec P z s n0 =>
      NNatRec (shift_whnf d c P)
              (shift_whnf d c z)
              (shift_whnf d c s)
              (shift_neutral d c n0)
  end

with shift_whnf (d c : nat) (v : whnf) : whnf :=
  match v with
  | VStar          => VStar
  | VNat           => VNat
  | VPi A B        => VPi (shift_whnf d c A)
                          (match B with Cl ρ b => Cl (map (shift_whnf d c) ρ) b end)
  | VSigma A B     => VSigma (shift_whnf d c A)
                             (match B with Cl ρ b => Cl (map (shift_whnf d c) ρ) b end)
  | VLam (Cl ρ b)  => VLam (Cl (map (shift_whnf d c) ρ) b)
  | VPair A B a b  => VPair (shift_whnf d c A) (shift_whnf d c B)
                            (shift_whnf d c a) (shift_whnf d c b)
  | VZero          => VZero
  | VSucc v1       => VSucc (shift_whnf d c v1)
  | VNeutral n     => VNeutral (shift_neutral d c n)
  end.


(* Push a new head value; shift older entries so de Bruijn indices line up. *)
Definition env_cons (v : whnf) (ρ : env) : env :=
  v :: map (shift_whnf 1 0) ρ.

(* Identity environment of length n (Var i ↦ Neutral (NVar i)). *)
Fixpoint id_env (n : nat) : env :=
  match n with
  | 0 => []
  | S k => VNeutral (NVar 0) :: map (shift_whnf 1 0) (id_env k)
  end.

(* ---------------------------------------------------------------- *)
(* 1) Closure application (relational wrapper around eval').         *)
(* ---------------------------------------------------------------- *)

(* A single fresh neutral you can reuse under binders *)
Definition fresh : whnf := VNeutral (NVar 0).

(* Closure application wrapper already defined earlier: *)
Definition clos_eval' (cl : closure) (v v' : whnf) : Prop :=
  match cl with
    | Cl ρ body => eval' (env_cons v ρ) body v' 
  end.

(* Algorithmic convertibility on WHNFs and neutrals *)
Inductive convV : whnf -> whnf -> Prop :=
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
    convV A A' -> convV B B' -> convV a a' -> convV b b' ->
    convV (VPair A B a b) (VPair A' B' a' b')

| CV_Zero : convV VZero VZero
| CV_Succ : forall n n', convV n n' -> convV (VSucc n) (VSucc n')

| CV_Neutral : forall n n',
    convN n n' ->
    convV (VNeutral n) (VNeutral n')

with convN : neutral -> neutral -> Prop :=
| CN_Var  : forall i, convN (NVar i) (NVar i)
| CN_App  : forall n n' v v',
    convN n n' -> convV v v' ->
    convN (NApp n v) (NApp n' v')
| CN_Fst  : forall n n', convN n n' -> convN (NFst n) (NFst n')
| CN_Snd  : forall n n', convN n n' -> convN (NSnd n) (NSnd n')
| CN_NatRec : forall P P' z z' s s' n n',
    convV P P' -> convV z z' -> convV s s' -> convN n n' ->
    convN (NNatRec P z s n) (NNatRec P' z' s' n').


(* ---------------------------------------------------------------- *)
(* 3) Bidirectional typing over a *semantic* context of WHNF types.  *)
(*    Γ : list whnf  (rightmost is Var 0).                           *)
(*    We use eval' with the identity env [id_env (length Γ)].        *)
(* ---------------------------------------------------------------- *)

Definition sem_env_of_ctx (Γ : list whnf) : env := id_env (length Γ).

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

(* Introductions synthesize only when canonical: pair/lambda won’t synthesize without a target. *)
with check : list whnf -> term -> whnf -> Prop :=
| C_Sub : forall Γ t A A',
    infer Γ t A' ->
    convV A' A ->
    check Γ t A

| C_Lam : forall Γ A b vA vA' B,
    (* decodes the intended rule properly *)
    eval' (sem_env_of_ctx Γ) A vA ->
    (* expected type provides domain vA' and codomain closure B *)
    convV vA vA' ->
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
    convV A' A ->
    check Γ t A.

Require Import Coq.Lists.List Coq.Init.Nat.
Import ListNotations.

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
    end
  end

with vappk (fuel : nat) (vf vu : whnf) : option whnf :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match vf with
    | VLam (Cl ρ' body) => evalk fuel' (vu :: ρ') body
    | VNeutral nf       => Some (VNeutral (NApp nf vu))
    | _                 => Some vf  (* ill-typed: leave head unchanged *)
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

(* Examples *)
Eval compute in evalk 200 [] (App (App add two) one).
(* Expected:   Some (VSucc (VSucc (VSucc VZero)))    i.e. 3 *)

Eval compute in eval [] (App (App mult one) four).
(* Expected:   Some (VSucc (VSucc (VSucc (VSucc VZero))))  i.e. 4 *)

Scheme eval'_rect      := Induction for eval'        Sort Prop
with vapp_rect         := Induction for vapp         Sort Prop
with eval_natrec_rect  := Induction for eval_natrec  Sort Prop.

Combined Scheme evalsys_mutind from eval'_rect, vapp_rect, eval_natrec_rect.

 (* mutual induction on the first derivation *)
Lemma det_trio :
  (forall ρ t v1, eval' ρ t v1 -> forall v2, eval' ρ t v2 -> v1 = v2) /\
  (forall f a r1, vapp f a r1 -> forall r2, vapp f a r2 -> r1 = r2) /\
  (forall vP vz vs vn r1, eval_natrec vP vz vs vn r1 -> forall r2, eval_natrec vP vz vs vn r2 -> r1 = r2).
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
Qed.

(* Determinism corollaries for the three relations *)
Theorem eval'_det :
  forall ρ t v1 v2, eval' ρ t v1 -> eval' ρ t v2 -> v1 = v2.
Proof. intros. 
       specialize det_trio; intros (Ha,(Hb,Hc)).
       apply Ha with (ρ := ρ) (t := t); easy.
Qed.

Theorem vapp_det :
  forall f a r1 r2, vapp f a r1 -> vapp f a r2 -> r1 = r2.
Proof. intros. 
       specialize det_trio; intros (Ha,(Hb,Hc)).
       apply Hb with (f := f) (a := a); easy.
Qed.

Theorem eval_natrec_det :
  forall vP vz vs vn r1 r2,
    eval_natrec vP vz vs vn r1 -> eval_natrec vP vz vs vn r2 -> r1 = r2.
Proof. intros. 
       specialize det_trio; intros (Ha,(Hb,Hc)).
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
  vnatreck k' vP vz vs vn = Some r.
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
  eval_natrec vP vz vs vn r.
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
       - intro k. 
         induction k; intros. 
         + simpl in H. easy.
         + simpl in H.
           destruct vf.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * destruct c. apply evalk_sound in H.
             constructor. easy.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
           * inversion H; subst. constructor; intros; try discriminate; try congruence.
       - intro k.
         induction k; intros.
         + simpl in H. easy.
         + simpl in H.
           case_eq vn; intros; subst.
           * inversion H. apply ENR_Other; easy.
           * inversion H. apply ENR_Other; easy.
           * inversion H. apply ENR_Other; easy.
           * inversion H. apply ENR_Other; easy.
           * inversion H. apply ENR_Other; easy.
           * inversion H. apply ENR_Other; easy.
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
Qed.

Require Import Coq.Arith.PeanoNat Lia.

(* ---------- Completeness: relational ⇒ some fuel computes the same ---------- *)

Lemma evalk_complete:
  (* eval' *)
  (forall ρ t v, eval' ρ t v -> exists k, evalk k ρ t = Some v) /\
  (* vapp *)
  (forall f a r, vapp f a r -> exists k, vappk k f a = Some r) /\
  (* natrec *)
  (forall vP vz vs vn r, eval_natrec vP vz vs vn r -> exists k, vnatreck k vP vz vs vn = Some r).
Proof.
  eapply (evalsys_mutind
    (* motives: say what we prove for each relation *)
    (fun ρ t v  _ => exists k, evalk k ρ t = Some v)             (* for eval' *)
    (fun f a r  _ => exists k, vappk k f a = Some r)             (* for vapp *)
    (fun vP vz vs vn r _ => exists k, vnatreck k vP vz vs vn = Some r)); intros.  (* natrec *)
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




