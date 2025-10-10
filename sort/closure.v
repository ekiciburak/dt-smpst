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
| ConvClo : forall B B',
    (forall w v v', clos_eval' B w v -> clos_eval' B' w v' -> conv v v') ->
(*     clos_eval' B  fresh v ->
    clos_eval' B' fresh v' ->
    conv v v' -> *)
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

(* ------------------------------------------------------------------ *)
(*  Constructive enumerator + extensional conv_clo_fuel (Option A)     *)
(* ------------------------------------------------------------------ *)

(* --- small utilities on whnfs --- *)

(* Structural boolean equality on neutral *)
Fixpoint neutral_eqb (n1 n2 : neutral) : bool :=
  match n1, n2 with
  | NVar i, NVar j => Nat.eqb i j
  | NApp n1' v1, NApp n2' v2 =>
      andb (neutral_eqb n1' n2') (whnf_eqb v1 v2) (* forward ref to whnf_eqb; use Fixpoint mutual below *)
  | NFst n1', NFst n2' => neutral_eqb n1' n2'
  | NSnd n1', NSnd n2' => neutral_eqb n1' n2'
  | NNatRec P z s n1', NNatRec P' z' s' n2' =>
      andb (andb (whnf_eqb P P') (whnf_eqb z z'))
           (andb (whnf_eqb s s') (neutral_eqb n1' n2'))
  | NVecRec A P z s n1' nx, NVecRec A' P' z' s' n2' nx' =>
      andb (andb (whnf_eqb A A') (whnf_eqb P P'))
           (andb (andb (whnf_eqb z z') (whnf_eqb s s'))
                 (andb (whnf_eqb n1' n2') (neutral_eqb nx nx')))
  | _, _ => false
  end

(* Main whnf_eqb: closes over neutral_eqb via mutual recursion *)
with whnf_eqb (x y : whnf) : bool :=
  match x, y with
  | VStar, VStar => true
  | VNat, VNat => true
  | VPi A B, VPi A' B' =>
      andb (whnf_eqb A A')
           (* closures carry closure, which we conservatively treat as unequal to avoid
              needing decidable equality on closures/terms. *)
           false
  | VSigma A B, VSigma A' B' =>
      andb (whnf_eqb A A') false
  | VLam _, VLam _ => false
  | VPair A B a b, VPair A' B' a' b' =>
      andb (whnf_eqb A A')
           (andb (whnf_eqb B B') (andb (whnf_eqb a a') (whnf_eqb b b')))
  | VZero, VZero => true
  | VSucc n, VSucc n' => whnf_eqb n n'
  | VNeutral n, VNeutral n' => neutral_eqb n n'
  | VVec n A, VVec n' A' => andb (whnf_eqb n n') (whnf_eqb A A')
  | VNilV A, VNilV A' => whnf_eqb A A'
  | VConsV A n x xs, VConsV A' n' x' xs' =>
      andb (whnf_eqb A A') (andb (whnf_eqb n n') (andb (whnf_eqb x x') (whnf_eqb xs xs')))
  | _, _ => false
  end.


(* remove duplicates conservatively using whnf_eqb *)
Fixpoint nodups_whnfs (l:list whnf) : list whnf :=
  match l with
  | [] => []
  | x::xs =>
      if existsb (fun y => whnf_eqb x y) xs then nodups_whnfs xs else x :: nodups_whnfs xs
  end.

(* iterate a constructor n times: helper for small_nats *)
Fixpoint iter_succ (n : nat) (x : whnf) : whnf :=
  match n with
  | 0 => x
  | S n' => VSucc (iter_succ n' x)
  end.

Fixpoint small_nats (d : nat) : list whnf :=
  match d with
  | 0 => []
  | S d' => small_nats d' ++ [iter_succ d' VZero]
  end.

Fixpoint small_neutrals (n : nat) : list whnf :=
  match n with
  | 0 => []
  | S n' => VNeutral (NVar n') :: small_neutrals n'
  end.

(* environment values: in your setup env is list whnf already *)
Definition env_values (fuel : nat) (cl : closure) : list whnf :=
  cl_env cl.

(* small vectors built from a list of element-types As *)
Definition make_small_vectors (fuel : nat) (As : list whnf) : list whnf :=
  (* conservative: just VNil for each A, plus maybe one representative cons if possible *)
  flat_map (fun A => [VNilV A]) As.

(* candidate set for a closure at fuel *)
Definition candidate_args_of (fuel : nat) (cl : closure) : list whnf :=
  nodups_whnfs (
    fresh ::
    (env_values fuel cl) ++
    (small_neutrals fuel) ++
    (small_nats fuel) ++
    (make_small_vectors fuel (env_values fuel cl ++ [VNat; VStar]))
  ).

(* check_on_candidates: evaluate cl/cl' at each candidate and run conv_fuel on results *)
Definition check_on_candidates (fuel : nat) (cl cl' : closure) : bool :=
  let cands := candidate_args_of fuel cl ++ candidate_args_of fuel cl' in
  forallb (fun w =>
    match clos_eval_fuel fuel cl w, clos_eval_fuel fuel cl' w with
    | Some v, Some v' => conv_fuel fuel v v'
    | _, _ => false
    end) cands.

Definition conv_clo_fuel_new (fuel : nat) (cl cl' : closure) : bool :=
  match clos_eval_fuel fuel cl fresh, clos_eval_fuel fuel cl' fresh with
  | Some vf, Some vf' =>
      if conv_fuel fuel vf vf'
      then check_on_candidates fuel cl cl'
      else false
  | _, _ => false
  end.

(* ------------------------------------------------------------------ *)
(*  Make conv_clo extensional (relational)                            *)
(* ------------------------------------------------------------------ *)

(* Inductive conv_clo : closure -> closure -> Prop :=
| ConvClo_ext : forall B B',
    (forall (w:whnf) (v v':whnf),
       clos_eval' B w v ->
       clos_eval' B' w v' ->
       conv v v') ->
    conv_clo B B'.
 *)
(* conv remains as before (unchanged) *)
(* (Assume you keep the conv inductive from your file, unchanged) *)

(* ------------------------------------------------------------------ *)
(*  Replace uses: you will update conv_fuel to call conv_clo_fuel     *)
(*  (but here I leave conv_fuel unchanged structurewise and show how  *)
(*   to use conv_clo_fuel in Pi/Sigma/Lam cases below)                *)
(* ------------------------------------------------------------------ *)

(* If you want to mutate the earlier conv_fuel, replace the closure-checking branches:
   - in VPi and VSigma, replace clos_eval_fuel ... fresh matches by conv_clo_fuel
   - in VLam case replace clos_eval_fuel ... fresh by conv_clo_fuel
   Below I give a patched snippet for those cases. *)

(* ------------------------------------------------------------------ *)
(*  Extensional variant: conv_fuel_patch / conv_neutral_fuel_patch    *)
(* ------------------------------------------------------------------ *)

(* extensional variant: conv_fuel_patch / conv_neutral_fuel_patch *)


(* ---------- helper: list ops ---------- *)
Fixpoint list_union {A} (eqb : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x::xs => if existsb (fun y => eqb x y) l2 then list_union eqb xs l2 else x :: list_union eqb xs l2
  end.

(* ---------- seeds ---------- *)
Definition seed_values (fuel : nat) (cl : closure) : list whnf :=
  (* conservative seeds: env values, fresh, small neutrals, small nats *)
  let env_vs := cl_env cl in
  let neut := small_neutrals fuel in
  let nats := small_nats fuel in
  nodups_whnfs (fresh :: env_vs ++ neut ++ nats).

(* ---------- one step of exploration: apply closure to all seeds and collect results ---------- *)
Definition closure_step (fuel : nat) (cl : closure) (xs : list whnf) : list whnf :=
  fold_right (fun w acc =>
    match clos_eval_fuel fuel cl w with
    | Some v => if existsb (fun y => whnf_eqb v y) acc then acc else v :: acc
    | None => acc
    end) xs xs.
(* Note: we fold starting with xs so we keep seeds and add new results. *)

(* ---------- full enumeration: iterate closure_step up to `fuel` times ---------- *)
Fixpoint enumerate_values_of_closure_aux (fuel : nat) (cl : closure) (n : nat) (acc : list whnf) : list whnf :=
  match n with
  | 0 => acc
  | S n' =>
      let acc' := closure_step fuel cl acc in
      (* if acc' = acc, early stop; but we keep bounded loops for simplicity *)
      enumerate_values_of_closure_aux fuel cl n' (list_union whnf_eqb acc' acc)
  end.

Definition enumerate_values_of_closure (fuel : nat) (cl : closure) : list whnf :=
  let seeds := seed_values fuel cl in
  enumerate_values_of_closure_aux fuel cl fuel seeds.

(* ---------- new extensional conv_clo_fuel using enumeration ---------- *)

Definition conv_clo_fuel_enum (fuel : nat) (cl cl' : closure) : bool :=
  let s1 := enumerate_values_of_closure fuel cl in
  let s2 := enumerate_values_of_closure fuel cl' in
  let cands := nodups_whnfs (s1 ++ s2) in
  forallb (fun w =>
    match clos_eval_fuel fuel cl w, clos_eval_fuel fuel cl' w with
    | Some v, Some v' => conv_fuel fuel v v'
    | _, _ => false
    end) cands.

(* Keep fresh-based quick path only as an optimization, but do not rely on it for soundness. *)
Definition conv_clo_fuel (fuel : nat) (cl cl' : closure) : bool :=
  (* Optional optimization: quick check at fresh *)
  match clos_eval_fuel fuel cl fresh, clos_eval_fuel fuel cl' fresh with
  | Some vf, Some vf' =>
      if negb (conv_fuel fuel vf vf') then false
      else conv_clo_fuel_enum fuel cl cl'
  | _, _ => conv_clo_fuel_enum fuel cl cl'
  end.

(* ------------------------------------------------------------------ *)
(*  Extensional patched mutual conv functions using enumeration       *)
(*  Names: conv_fuel_patch / conv_neutral_fuel_patch                  *)
(*  They use conv_clo_fuel_enum : nat -> closure -> closure -> bool   *)
(*  (the enumerating, fuel-bounded extensional closure checker).      *)
(* ------------------------------------------------------------------ *)

Fixpoint conv_fuel_patch (fuel:nat) (v w:whnf) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match v, w with
    | VStar, VStar => true
    | VNat,  VNat  => true

    | VPi A B, VPi A' B' =>
        if conv_fuel_patch fuel' A A' then
          (* extensional equality on closures (bodies) using enumerator *)
          if conv_clo_fuel_enum fuel' B B' then
            match clos_eval_fuel fuel' B fresh,
                  clos_eval_fuel fuel' B' fresh with
            | Some vB, Some vB' => conv_fuel_patch fuel' vB vB'
            | _, _ => false
            end
          else false
        else false

    | VSigma A B, VSigma A' B' =>
        if conv_fuel_patch fuel' A A' then
          if conv_clo_fuel_enum fuel' B B' then
            match clos_eval_fuel fuel' B fresh,
                  clos_eval_fuel fuel' B' fresh with
            | Some vB, Some vB' => conv_fuel_patch fuel' vB vB'
            | _, _ => false
            end
          else false
        else false

    | VLam cl1, VLam cl2 =>
        (* for lambdas, accept when their closures are extensional-equal *)
        if conv_clo_fuel_enum fuel' cl1 cl2 then true else false

    | VPair A B a b, VPair A' B' a' b' =>
        andb (conv_fuel_patch fuel' A A')
             (andb (conv_fuel_patch fuel' B B')
                   (andb (conv_fuel_patch fuel' a a')
                         (conv_fuel_patch fuel' b b')))

    | VZero, VZero => true
    | VSucc n, VSucc n' => conv_fuel_patch fuel' n n'
    | VNeutral n, VNeutral n' => conv_neutral_fuel_patch fuel' n n'
    | VVec n A, VVec n' A' =>
        andb (conv_fuel_patch fuel' n n') (conv_fuel_patch fuel' A A')
    | VNilV A, VNilV A' => conv_fuel_patch fuel' A A'
    | VConsV A n x xs, VConsV A' n' x' xs' =>
        andb (conv_fuel_patch fuel' A A')
             (andb (conv_fuel_patch fuel' n n')
                   (andb (conv_fuel_patch fuel' x x')
                         (conv_fuel_patch fuel' xs xs')))
    | _, _ => false
    end
  end

with conv_neutral_fuel_patch (fuel : nat) (n n' : neutral) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    match n, n' with
    | NVar i, NVar j => Nat.eqb i j

    | NApp n0 v, NApp n1 v' =>
        andb (conv_neutral_fuel_patch fuel' n0 n1)
             (conv_fuel_patch fuel' v v')

    | NFst n0, NFst n1 =>
        conv_neutral_fuel_patch fuel' n0 n1

    | NSnd n0, NSnd n1 =>
        conv_neutral_fuel_patch fuel' n0 n1

    | NNatRec P z s n0, NNatRec P' z' s' n1 =>
        andb (conv_fuel_patch fuel' P P')
             (andb (conv_fuel_patch fuel' z z')
                   (andb (conv_fuel_patch fuel' s s')
                         (conv_neutral_fuel_patch fuel' n0 n1)))

    | NVecRec A P z s n0 nx, NVecRec A' P' z' s' n1 nx' =>
        andb (conv_fuel_patch fuel' A A')
             (andb (conv_fuel_patch fuel' P P')
                   (andb (conv_fuel_patch fuel' z z')
                         (andb (conv_fuel_patch fuel' s s')
                               (andb (conv_fuel_patch fuel' n0 n1)
                                     (conv_neutral_fuel_patch fuel' nx nx')))))

    | _, _ => false
    end
  end.



  
  
