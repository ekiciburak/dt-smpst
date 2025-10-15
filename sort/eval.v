Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.term sort.subst.

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
        | None   => None (* Some (VNeutral (NVar x)) *)
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
        | _                     => None
        end

    | TSnd p =>
        match evalk fuel' ρ p with
        | Some (VPair _ _ _ vb) => Some vb
        | _                     => None
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
    | _                 => None 
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
    | _           => None 
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


    | _ => None
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


