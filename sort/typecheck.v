Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst sort.eval sort.closure.

(* Bidirectional Typing *)
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

