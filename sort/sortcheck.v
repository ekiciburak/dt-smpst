Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Require Import String.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.sort sort.subst sort.eval.

Definition context := list term.

(* Type checking result monad *)
Inductive result (A : Type) : Type :=
| Ok : A -> result A
| Err : string -> result A.

Arguments Ok {A} _.
Arguments Err {A} _.

Definition bind {A B} (r : result A) (f : A -> result B) : result B :=
  match r with
  | Ok x => f x
  | Err msg => Err msg
  end.

Notation "'do' x <- e1 ; e2" := (bind e1 (fun x => e2))
  (at level 200, x ident, e1 at level 100, e2 at level 200).

Definition ret {A} (x : A) : result A := Ok x.

(* Helper function for equality check *)
Fixpoint eqb (t1 t2 : term) : bool :=
  match t1, t2 with
  | Star, Star => true
  | Nat, Nat => true
  | Zero, Zero => true
  | Succ n1, Succ n2 => eqb n1 n2
  | Pi A1 B1, Pi A2 B2 => eqb A1 A2 && eqb B1 B2
  | Sigma A1 B1, Sigma A2 B2 => eqb A1 A2 && eqb B1 B2
  | Var n1, Var n2 => Nat.eqb n1 n2
  | Lam A1 b1, Lam A2 b2 => eqb A1 A2 && eqb b1 b2
  | App f1 a1, App f2 a2 => eqb f1 f2 && eqb a1 a2
  | NatRec P1 z1 s1 n1, NatRec P2 z2 s2 n2 => 
      eqb P1 P2 && eqb z1 z2 && eqb s1 s2 && eqb n1 n2
  | _, _ => false
  end.

(* weak-head normalization with fuel (well-formed recursive definition) -- allows for App under binder *)
Fixpoint whnf (fuel : nat) (t : term) : term :=
  match fuel with
  | 0 => t
  | S fuel' =>
      match t with
      | App f a =>
          (* first reduce the head to WHNF *)
          let f' := whnf fuel' f in
          match f' with
          | Lam _ b =>
              (* perform one β-step and continue normalizing the result *)
              whnf fuel' (subst 0 a b)
          | _ =>
              (* cannot β-reduce; return application with reduced head *)
              App f' a
          end
      | _ => t
      end
  end.

Definition simplify_default (t : term) : term := whnf 100 t.

Fixpoint type_check (Γ : context) (t : term) : result term :=
  match t with
  | Star => ret Star
  
  | Nat => ret Star
  
  | Zero => ret Nat
  
  | Succ n =>
      do n_ty <- type_check Γ n;
      if eqb n_ty Nat then ret Nat
      else Err "Succ expects Nat argument"

| Pi A B =>
    do tyA <- type_check Γ A;
    if eqb tyA Star then
      do tyB <- type_check (A :: Γ) B;
      (* Allow both Star and Pi types as valid codomains *)
      match tyB with
      | Star => ret Star
      | Pi dom cod => 
          if eqb cod Star then ret Star
          else Err "Pi codomain must be a type"
      | _ => Err "Pi codomain must be a type"
      end
    else Err "Pi domain must be a type"
  
| Sigma A B =>
    do tyA <- type_check Γ A;
    if eqb tyA Star then
      do tyB <- type_check (A :: Γ) B;
      (* Ensure that B evaluates to a type *)
      let whnf_B := eval 100 tyB in
      match whnf_B with
      | Some Star => ret Star
      | Some (Pi dom cod) => 
          if eqb cod Star then ret Star
          else Err "Sigma codomain must be a type"
      | _ => Err "Sigma codomain must be a type"
      end
    else Err "Sigma domain must be a type"

  | Pair A B a b =>
    do tyA <- type_check Γ A;
    if negb (eqb tyA Star) then Err "First type argument must be a type" else
    do tyB <- type_check (A :: Γ) B;
    
    (* Ensure B is a valid type family *)
    let whnf_tyB := simplify_default tyB in
    match whnf_tyB with
    | Star => 
        (* Non-dependent pair *)
        do tya <- type_check Γ a;
        if eqb tya A then
          do tyb <- type_check Γ b;
          if eqb tyb B then ret (Sigma A B)
          else Err "Second component has wrong type"
        else Err "First component has wrong type"
    | Pi dom cod =>
        if eqb dom A && eqb cod Star then
          (* Dependent pair *)
          do tya <- type_check Γ a;
          if eqb tya A then
            do tyb <- type_check Γ b;
            let expected_type := simplify_default (App B a) in
            if eqb tyb expected_type then 
              (* Return the normalized type *)
              ret (Sigma A whnf_tyB)  (* Use the normalized type *)
            else Err "Second component has wrong type"
          else Err "First component has wrong type"
        else Err "Second type argument must be A -> Type"
    | _ => Err "Second type argument must be a type"
    end

  | TFst p =>
      do tyP <- type_check Γ p;
      match tyP with
      | Sigma A B => ret A
      | _ => Err "Fst expects Sigma type"
      end
  
  | TSnd p =>
    do tyP <- type_check Γ p;
    match tyP with
    | Sigma A B =>
        let fst_val := TFst p in
        let result_type := subst 0 fst_val B in
        ret (simplify_default result_type)
    | _ => Err "Snd expects Sigma type"
    end
  
  | Var x =>
      match nth_error Γ x with
      | Some ty => ret ty
      | None => Err "Variable not found in context"
      end
  
  | Lam A b =>
      do tyA <- type_check Γ A;
      if eqb tyA Star then
        do tyB <- type_check (A :: Γ) b;
        ret (Pi A tyB)
      else Err "Lambda domain must be a type"
  
  | App f a =>
    do tyF <- type_check Γ f;
    match tyF with
    | Pi A B =>
        do tyA <- type_check Γ a;
        if eqb tyA A then 
          let result_type := subst 0 a B in
          ret (simplify_default result_type)
        else Err "Argument type mismatch in application"
    | _ => Err "Application expects function type"
    end

  | NatRec P z s n =>
    do tyN <- type_check Γ n;
    if negb (eqb tyN Nat) then Err "NatRec expects Nat argument" else
    do tyP <- type_check (Nat :: Γ) P;
    
    (* Check that z and s are well-formed terms *)
    match type_check Γ z, type_check Γ s with
    | Ok tyZ, Ok tyS =>
        match tyP with
        | Pi dom cod =>
            if eqb dom Nat then
              let result_type := App P n in
              ret (simplify_default result_type)  (* Use the fuel-based simplifier *)
            else
              ret Nat  (* Fallback: assume Nat *)
        | _ =>
            ret Nat  (* Fallback: assume Nat *)
        end
    | Err msg, _ => Err msg
    | _, Err msg => Err msg
    end

(* (* Alternative simpler approach for NatRec *)
  | NatRec P z s n =>
      do tyN <- type_check Γ n;
      if negb (eqb tyN Nat) then Err "NatRec expects Nat argument" else
      do tyP <- type_check (Nat :: Γ) P;
      (* For now, just assume P returns Nat and skip complex checks *)
      do tyZ <- type_check Γ z;
      do tyS <- type_check Γ s;
      ret Nat  (* Assume result is always Nat for simplicity *) *)
  end.


(* Type checking with error messages *)
Definition type_of (t : term) : result term :=
  type_check [] t.

(* === Test cases === *)

(* Simple types *)
Example type_nat : type_of Nat = Ok Star. reflexivity. Qed.
Example type_zero : type_of Zero = Ok Nat. reflexivity. Qed.

(* Function types *)
Example type_identity_fn : 
  type_of (Lam Nat (Var 0)) = Ok (Pi Nat Nat).
reflexivity. Qed.

Example type_dep_pair_with_type :
  type_of (Pair Nat (Lam Nat Nat) two (Succ two)) = 
  Ok (Sigma Nat (Pi Nat Star)).
Proof. reflexivity. Qed.

(* Correct version for Sigma Nat (Pi Nat Nat) *)
Definition correct_dep_pair :=
  Pair Nat (Lam Nat (Var 0))  (* Identity function type *) 
        two                   (* First component *)
        (Lam Nat (Var 0)).    (* Identity function *)

(* Example type_correct_dep_pair :
  type_of correct_dep_pair = Ok (Sigma Nat (Pi Nat Nat)).
Proof. unfold type_of, correct_dep_pair. simpl. reflexivity. Qed. *)


Example type_app : 
  type_of (App (Lam Nat (Var 0)) two) = Ok Nat.
reflexivity. Qed.


(* NatRec example - addition *)
Example type_add : 
  type_of add = Ok (Pi Nat (Pi Nat Nat)).
  unfold type_of.
  unfold add.
  simpl.
  unfold simplify_default. simpl.
reflexivity. Qed.

(* Test well-typed terms *)
Example test_add_2_1 : 
  type_of (App (App add two) one) = Ok Nat.
reflexivity. Qed.

Example test_add_2_11 : 
  type_of mult = Ok (Pi Nat (Pi Nat Nat)).
reflexivity. Qed.

Example test_mult_2_3 : 
  type_of (App (App mult two) three) = Ok Nat.
reflexivity. Qed.

(* Error cases *)
Example error_app_non_function : 
  type_of (App two one) = Err "Application expects function type".
reflexivity. Qed.

Example error_fst_non_pair : 
  type_of (TFst two) = Err "Fst expects Sigma type".
reflexivity. Qed.



Definition ctx := list term.

Fixpoint lookup (Γ : ctx) (x : nat) : option term :=
  match Γ, x with
  | nil, _ => None
  | A :: Γ, 0 => Some A
  | A :: Γ, S n => lookup Γ n
  end.

Definition conv := multi step.

Inductive infer_type : ctx -> term -> term -> Prop :=
  | Inf_Var : forall Γ x A,
      lookup Γ x = Some A ->
      infer_type Γ (Var x) A

  | Inf_App : forall Γ t u A B,
      infer_type Γ t (Pi A B) ->
      check_type Γ u A ->
      infer_type Γ (App t u) (subst 0 u B)

  | Inf_Star : forall Γ,
      infer_type Γ Star Star

  | Inf_Nat : forall Γ,
      infer_type Γ Nat Star

  | Inf_Pi : forall Γ A B,
      check_type Γ A Star ->
      check_type (A :: Γ) B Star ->
      infer_type Γ (Pi A B) Star

  | Inf_Sigma : forall Γ A B,
      check_type Γ A Star ->
      check_type (A :: Γ) B Star ->
      infer_type Γ (Sigma A B) Star

  | Inf_Zero : forall Γ,
      infer_type Γ Zero Nat

  | Inf_Succ : forall Γ n,
      infer_type Γ n Nat ->
      infer_type Γ (Succ n) Nat

  | Inf_Pair : forall Γ A B a b,
      check_type Γ A Star ->
      check_type (A :: Γ) B Star ->
      check_type Γ a A ->
      check_type Γ b (subst 0 a B) ->
      infer_type Γ (Pair A B a b) (Sigma A B)

  | Inf_Fst : forall Γ A B p,
      infer_type Γ p (Sigma A B) ->
      infer_type Γ (TFst p) A

  | Inf_Snd : forall Γ A B p,
      infer_type Γ p (Sigma A B) ->
      infer_type Γ (TSnd p) (subst 0 (TFst p) B)

  | Inf_NatRec : forall Γ P z s n,
      infer_type Γ P (Pi Nat Star) ->                    (* P : Nat → Type *)
      check_type Γ z (App P Zero) ->                     (* z : P Zero *)
      check_type Γ s (Pi Nat (Pi (App P (Var 0))         (* s : Π(n:Nat), P n → P (Succ n) *)
                                (App P (Succ (Var 0))))) ->
      infer_type Γ n Nat ->
      infer_type Γ (NatRec P z s n) (App P n)

  | Inf_Conv : forall Γ t A B,  (* Conversion for inference *)
      infer_type Γ t A ->
      check_type Γ B Star ->     (* B must be a valid type *)
      conv A B ->                (* A and B are convertible *)
      infer_type Γ t B

with check_type : ctx -> term -> term -> Prop :=
  | Check_Lam : forall Γ A b B,
      check_type Γ A Star ->
      check_type (A :: Γ) b B ->
      check_type Γ (Lam A b) (Pi A B)

  | Check_Zero : forall Γ,
      check_type Γ Zero Nat

  | Check_Succ : forall Γ n,
      check_type Γ n Nat ->
      check_type Γ (Succ n) Nat

  | Check_Pair : forall Γ A B a b,
      check_type Γ A Star ->
      check_type (A :: Γ) B Star ->
      check_type Γ a A ->
      check_type Γ b (subst 0 a B) ->
      check_type Γ (Pair A B a b) (Sigma A B)

  | Check_NatRec : forall Γ P z s n T,
      check_type Γ P (Pi Nat Star) ->
      check_type Γ z (App P Zero) ->
      check_type Γ s (Pi Nat (Pi (App P (Var 0)) 
                                (App P (Succ (Var 0))))) ->
      check_type Γ n Nat ->
      check_type Γ T Star ->
      conv (App P n) T ->
      check_type Γ (NatRec P z s n) T

  | Check_Infer : forall Γ t T,
      infer_type Γ t T ->
      check_type Γ t T.

Scheme infer_type_mut := Induction for infer_type Sort Prop
with check_type_mut := Induction for check_type Sort Prop.

Inductive wf_ctx : ctx -> Prop :=
  | Wf_Empty : wf_ctx nil
  | Wf_Extend : forall Γ A,
      wf_ctx Γ ->
      check_type Γ A Star ->
      wf_ctx (A :: Γ).

Fixpoint closed (t : term) (k : nat) : Prop :=
  match t with
  | Var n    => n < k
  | Lam A b  => closed A k /\ closed b (S k)
  | Pi A B   => closed A k /\ closed B (S k)
  | Sigma A B => closed A k /\ closed B (S k)
  | Succ n  => closed n k
  | Pair A B a b => closed A k /\ closed B k /\ closed a k /\ closed b k
  | TFst p | TSnd p => closed p k
  | App f a => closed f k /\ closed a k
  | NatRec P z s n => closed P k /\ closed z k /\ closed s k /\ closed n k
  | Star | Nat | Zero => True
  end.

(* canonical atomic types *)
Inductive atomic_type : term -> Prop :=
  | at_star : atomic_type Star
  | at_nat : atomic_type Nat.

(* well-founded types *)
Inductive wf_type : term -> Prop :=
  | wf_atomic : forall t,
      atomic_type t ->
      wf_type t
  | wf_pi : forall A B,
      wf_type A ->                (* domain *)
      wf_type B ->                (* codomain *)
      wf_type (Pi A B)
  | wf_sigma : forall A B,
      wf_type A ->                (* first component *)
      wf_type B ->                (* second component *)
      wf_type (Sigma A B).

Fixpoint is_term (t : term) : bool :=
  match t with
  | Var n => true
  | Zero => true
  | Succ n => is_term n
  | Pair A B a b => is_term a && is_term b
  | Lam A b => is_term b
  | _ => false
  end.

(* Non-bidirectional typing without conversion *)
Inductive has_type2 : ctx -> term -> term -> Prop :=
  | T_Var : forall Γ x A,
(*       wf_type A -> *)
      lookup Γ x = Some A ->
      has_type2 Γ (Var x) A

  | T_Star : forall Γ,
      has_type2 Γ Star Star

  | T_Nat : forall Γ,
      has_type2 Γ Nat Star

  | T_Pi : forall Γ A B,
      wf_type A ->
(*       closed A 0 -> *)
      has_type2 (A :: Γ) B Star ->
      has_type2 Γ (Pi A B) Star

  | T_Sigma : forall Γ A B,
      wf_type A ->
      has_type2 (A :: Γ) B Star ->
      has_type2 Γ (Sigma A B) Star

  | T_Lam : forall Γ A b B,
      closed A 0 ->
      has_type2 (A :: Γ) b B ->
      has_type2 Γ (Lam A b) (Pi A B)

  | T_App : forall Γ t u A B,
      wf_type A ->
      is_term u = true ->
      closed u 0 ->
      has_type2 Γ t (Pi A B) ->
      has_type2 Γ u A ->
      has_type2 Γ (App t u) (subst 0 u B)

  | T_Zero : forall Γ,
      has_type2 Γ Zero Nat

  | T_Succ : forall Γ n,
      has_type2 Γ n Nat ->
      has_type2 Γ (Succ n) Nat

  | T_Pair : forall Γ A B a b,
      is_term a = true ->
      closed a 0 ->
      has_type2 Γ a A ->
      has_type2 Γ b (subst 0 a B) ->
      has_type2 Γ (Pair A B a b) (Sigma A B)

  | T_Fst : forall Γ A B p,
      wf_type B ->
      has_type2 Γ p (Sigma A B) ->
      has_type2 Γ (TFst p) A

  | T_Snd : forall Γ A B p,
      wf_type A ->
      is_term (TFst p) = true ->
      closed p 0 ->
      has_type2 Γ p (Sigma A B) ->
      has_type2 Γ (TSnd p) (subst 0 (TFst p) B)

  | T_NatRec : forall Γ P z s n,
      has_type2 Γ P (Pi Nat Star) ->
      has_type2 Γ z (App P Zero) ->
      has_type2 Γ s (Pi Nat (Pi (App P (Var 0)) (App P (Succ (Var 0))))) ->
      has_type2 Γ n Nat ->
      has_type2 Γ (NatRec P z s n) (App P n).

Fixpoint zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | x::xs, y::ys => (x, y) :: zip xs ys
  | _, _ => []
  end.

Definition foreach2_ty A B (xs : list A) (ys : list B ) (P : A -> B -> Type) :=
  fold_right
    (fun x y => x*y)%type
    unit%type
    (map (fun pr:A*B => let (x, y) := pr in P x y) (zip xs ys)).

(** [env_typing] relates a value environment to its typing. It asserts
    the types (in a [nil] environment) of each of a series of values. *)
Definition env_typing Vs Ts :=
  ((List.length Vs = List.length Ts) *
  foreach2_ty _ _ Vs Ts (fun x y => (has_type2 nil x y (* /\ is_term x = true *) /\ wf_type y)))%type.

(** [env_typing_env] also relates a value environment to its typing. It asserts
    the types (in a given environment) of each of a series of values. *)
Definition env_typing_env env Vs Ts :=
  ((List.length Vs = List.length Ts) *
  foreach2_ty _ _ Vs Ts (fun x y => (has_type2 env x y (* /\ is_term x = true *) /\ wf_type y)))%type.

Hint Unfold env_typing.

(** [env_typing_env] environments can be extended, one term-type pair at a time. *)
Lemma env_typing_intro:
  forall env V Vs T Ts,
    wf_type T ->
    has_type2 env V T ->
    env_typing_env env (Vs) (Ts) ->
    env_typing_env env (V::Vs) (T::Ts).
Proof.
 intros.
 unfold env_typing_env in *.
 unfold foreach2_ty in *.
 simpl in *.
 intuition.
 
Qed.

Require Import Coq.Arith.Peano_dec.

Require Import Coq.Arith.PeanoNat.

Fixpoint subst_env (k : nat) (vs : list term) (t : term) {struct t} : term :=
  match t with
  | Var x =>
      if Nat.leb k x then
        match nth_error vs (x - k) with
        | Some v => lift 0 k v
        | None => Var x
        end
      else Var x
  | Star => Star
  | Nat => Nat
  | Pi A B =>
      Pi (subst_env k vs A)
         (subst_env (S k) (map (lift 0 1) vs) B)
  | Sigma A B =>
      Sigma (subst_env k vs A)
            (subst_env (S k) (map (lift 0 1) vs) B)
  | Lam A b =>
      Lam (subst_env k vs A)
          (subst_env (S k) (map (lift 0 1) vs) b)
  | App t1 t2 =>
      App (subst_env k vs t1) (subst_env k vs t2)
  | Zero => Zero
  | Succ n => Succ (subst_env k vs n)
  | Pair A B a b =>
      Pair (subst_env k vs A) (subst_env k vs B)
           (subst_env k vs a) (subst_env k vs b)
  | TFst p => TFst (subst_env k vs p)
  | TSnd p => TSnd (subst_env k vs p)
  | NatRec P z s n =>
      NatRec (subst_env k vs P)
             (subst_env k vs z)
             (subst_env k vs s)
             (subst_env k vs n)
  end.

Require Import List.

Lemma wftS: forall T c,
  wf_type T -> has_type2 c T Star.
Proof. intro T.
       induction T; intros.
       3:{ inversion H.
           - subst.
             inversion H0.
           - subst. 
             constructor. easy. simpl.
             apply IHT2. easy.
         }
       11:{ inversion H.
            subst.
            inversion H0.
          }
       9:{ inversion H.
           subst.
           inversion H0.
         }
       9:{ inversion H. subst. inversion H0. }
       6:{ inversion H. subst.
           inversion H0.
         }
       - constructor.
       - constructor.
       - constructor.
         inversion H. subst. inversion H0.
         subst. easy.
         apply IHT2. 
         inversion H. subst. inversion H0.
         subst. easy.
       - inversion H.
         subst. easy.
       - inversion H.
         subst. easy.
       - inversion H.
         subst. easy.
       - inversion H.
         subst. easy.
       - inversion H.
         subst. easy.
Qed.

Lemma liftterm: forall A n k, is_term A = true -> is_term (lift n k A) = true.
Proof. intro A.
       induction A; intros.
       3:{ simpl in H. easy. }
       10:{ simpl. inversion H. rewrite IHA2. easy. easy. }
       9:{ simpl. destruct (n <? k); easy. }
       6:{ simpl. inversion H.
           rewrite IHA3, IHA4. easy.
           apply Bool.andb_true_iff in H1. easy.
           apply Bool.andb_true_iff in H1. easy.
          }
       8:{ simpl in H. easy. }
       - simpl in H. easy.
       - easy.
       - easy.
       - easy.
       - simpl in H. simpl.
         apply IHA. easy.
       - easy.
       - easy.
       - easy.
Qed.

Lemma wfsubstR: forall B A n, is_term A = true -> wf_type B -> wf_type (subst n A B).
Proof. intro B.
       induction B; intros.
       3:{ simpl in H.
           inversion H0.
           subst. inversion H1.
           subst.
           simpl.
           apply wf_pi. 
           apply IHB1. easy. easy.
           apply IHB2. apply liftterm. easy. easy.
         }
       10:{ simpl in H.
           inversion H0.
           subst. inversion H1.
          }
       10:{ simpl in H.
            inversion H0.
             subst. inversion H1.
          }
        9:{ simpl in H0.
            inversion H0. inversion H1.
          }
        6:{ inversion H0. subst.
            inversion H1.
          }
        - simpl. easy.
        - simpl. easy.
        - simpl. inversion H0.
          subst. easy.
          subst. simpl.
          apply wf_sigma.
          apply IHB1; easy.
          apply IHB2. apply liftterm. easy. easy.
        - easy.
        - simpl. inversion H0.
          subst. easy.
        - simpl. inversion H0.
          subst. easy.
        - simpl. inversion H0.
          subst. easy.
        - simpl. inversion H0.
          subst. easy.
Qed.

Lemma wfsubstL: forall B A n, is_term A = true -> wf_type (subst n A B) -> wf_type B.
Proof. intro B.
       induction B; intros.
       3:{ simpl in H.
           inversion H0.
           subst. inversion H1.
           subst.
           apply wf_pi. apply IHB1 with (n:= n) (A := A). easy. easy. 
           apply IHB2 with (A := (lift 1 0 A)) (n := S n). 
           apply liftterm. easy. easy.
         }
       10:{ simpl in H.
           inversion H0.
           subst. inversion H1.
          }
       10:{ simpl in H.
            inversion H0.
             subst. inversion H1.
          }
        9:{ simpl in H0.
            case_eq(n ?= n0); intros. rewrite H1 in H0. rewrite lift_0 in H0.
            - inversion H0. subst.
              inversion H2.
              subst. easy.
              subst. easy.
              subst. easy.
              subst. easy.
            - rewrite H1 in H0.
              easy.
            - rewrite H1 in H0.
              inversion H0. subst. easy.
          }
          6:{ inversion H0. subst.
              inversion H1.
            }
          - easy.
          - easy.
          - simpl in H0.
            inversion H0.
            subst. easy.
            subst.
            apply wf_sigma.
            apply IHB1 with (A := A) (n := n); easy.
            apply IHB2 with (A := (lift 1 0 A)) (n := S n).
            apply liftterm. easy. easy.
          - easy.
          - simpl in H0. inversion H0. subst. easy.
          - simpl in H0. inversion H0. subst. easy.
          - simpl in H0. inversion H0. subst. easy.
          - simpl in H0. inversion H0. subst. easy.
Qed.

Require Import List.

Lemma shift_nonfree_noop :
  forall M n k env T,
    wf_type T ->
    length env <= k ->
    has_type2 env M T -> lift n k M = M.
Proof.
 intro M.
 induction M; simpl; intros.
 3:{ simpl.
     inversion H1. subst.
     rewrite IHM1 with (env := env) (T := Star).
     rewrite IHM2 with (env := (M1 :: env)) (T := Star). easy.
     simpl. constructor. constructor.
     simpl. lia.
     easy. easy. easy.
     apply wftS with (c := env) in H5. easy.
    }
  9: { inversion H1. subst.
      case_eq(n <? k); intros.
      + easy.
      + admit.
    }
  10:{ simpl.
       inversion H1. subst.
       rewrite IHM1 with (env := env) (T := (Pi A B)).
       rewrite IHM2 with (env := env) (T := A).
       easy. easy. easy. easy.
       apply wf_pi. easy. apply wfsubstL in H. easy.
       easy.
       easy. easy.
    }
  6:{ simpl. inversion H1. subst.
      inversion H. subst. easy.
      subst.
      rewrite IHM1 with (env := env) (T := Star).
      rewrite IHM2 with (env := env) (T := Star).
      rewrite IHM3 with (env := env) (T := M1).
      rewrite IHM4 with (env := env) (T := (subst 0 M3 M2)).
      easy.
      apply wfsubstR. easy. easy.
      easy. easy.
      easy.
      easy.
      easy. constructor. constructor.
      easy.
      apply wftS. easy. constructor. constructor.
      easy.
      apply wftS. easy.
     }
  - easy.
  - easy.
  - simpl. 
    inversion H1. subst.
    rewrite IHM1 with (env := env) (T := Star).
    rewrite IHM2 with (env := (M1 :: env)) (T := Star).
    easy. easy. simpl. lia. easy. easy. easy.
    apply wftS with (c := env) in H5. easy.
  - easy.
  - simpl. inversion H1. subst.
    rewrite IHM with (env := env) (T := Nat).
    easy. easy. easy. easy.
  - simpl. inversion H1. subst.
    rewrite IHM with (env := env) (T := (Sigma T B)).
    easy.
    apply wf_sigma. easy. easy.
    easy. easy.
  - simpl. inversion H1. subst.
    rewrite IHM with (env := env) (T := (Sigma A B)).
    easy.
    apply wf_sigma. easy. easy.
    easy. easy.
  - simpl. 
    inversion H1. subst.
    rewrite IHM1 with (env := env) (T := Star).
    rewrite IHM2 with (env := (M1 :: env)) (T := B).
    easy. inversion H. subst. easy. subst. easy. simpl. lia.
    easy. constructor. constructor. easy.
    inversion H. easy.
    apply wftS with (c := env) in H4. easy.
  - simpl.
    inversion H1. subst.
    inversion H. subst. easy.
Admitted.


Lemma env_typing_shift_noop :
  forall Vs env,
    env_typing Vs env ->
    forall n k, map (lift n k) Vs = Vs.
Proof.
 intro Vs.
 induction Vs; simpl; intros env H; auto.
 intros n k.
 inversion H as [len tps].
 case_eq env; intros.
 + subst. easy.
 + subst.
 unfold foreach2_ty in tps.
 simpl in tps.
 f_equal.
  inversion tps.
  eapply shift_nonfree_noop with (T := t) (env := nil); eauto. easy. simpl.
  
  simpl; lia. easy.
 rewrite IHVs with (env := l); auto.
 unfold env_typing.
 split. inversion len. easy.
 unfold foreach2_ty.
 destruct tps.
 easy.
Qed.

Lemma shift_preserves_typing:
  forall M k n env1 env2 env env' T,
    wf_type T ->
    env1 ++ env2 = env ->
    k = length env1 ->
    n = length env' ->
    has_type2 env M T -> 
    has_type2 (env1++env'++env2) (lift n k M) T.
Proof. intro M.
       induction M; intros.
       11: { simpl.
             inversion H3. subst. simpl in *.
             rewrite shift_nonfree_noop with (env := env1) (T := Star).
             apply T_Lam. easy.
             specialize (IHM2  (S (Datatypes.length env1)) (Datatypes.length env')
              (M1 :: env1) env2 ((M1 :: env1) ++ env2) env' B).
             simpl in IHM2. apply IHM2. inversion H. subst. easy. subst. easy.
             easy.
             easy.
             easy. easy. constructor. constructor. easy.
             inversion H. subst. easy. subst.
             apply wftS with (c := env1) in H2. easy.
          }
        10: { inversion H3. subst.
              inversion H.
              - subst. inversion H0. 
                + subst.
                  simpl.
                  case_eq( n <? Datatypes.length env1); intros.
                  ++ apply T_Var. admit.
                  ++ apply T_Var. admit.
                + subst. simpl.
                  case_eq( n <? Datatypes.length env1); intros.
                  ++ apply T_Var. admit.
                  ++ apply T_Var. admit.
              - subst. simpl.
                case_eq( n <? Datatypes.length env1); intros.
                + constructor. admit.
                + constructor. admit.
              - subst. simpl.
                case_eq( n <? Datatypes.length env1); intros.
                + apply T_Var. admit.
                + apply T_Var. admit.
             }
        3: { simpl.
             inversion H3. subst.
             rewrite shift_nonfree_noop with (env := env1) (T := Star).
             constructor.
             easy.
            specialize (IHM2  (S (Datatypes.length env1)) (Datatypes.length env')
              (M1 :: env1) env2 ((M1 :: env1) ++ env2) env' Star).
            simpl in IHM2. apply IHM2. easy. easy. easy. easy. easy. easy. easy.
            apply wftS with (c := env1) in H7. easy.
          }
        9: { inversion H3. subst. simpl in *.
             assert((lift (Datatypes.length env') (Datatypes.length env1) M2) = M2) by admit.
             rewrite H0.
             apply T_App with (A := A) (B := B). easy. easy. easy.
             apply IHM1 with (env := env1 ++ env2 ).
             apply wf_pi. easy.
             apply wfsubstL with (A := M2) (n := 0). easy. easy.
             easy.
             easy. easy. easy.
             rewrite <- H0.
             apply IHM2 with (env := env1 ++ env2 ). easy. easy. easy.
             easy. easy.
           }
        - simpl.
          inversion H3. constructor.
        - simpl. inversion H3. constructor.
        - simpl. inversion H3. subst.
          rewrite shift_nonfree_noop with (env := env1) (T := Star).
          apply T_Sigma. easy.
          specialize (IHM2  (S (Datatypes.length env1)) (Datatypes.length env')
           (M1 :: env1) env2 ((M1 :: env1) ++ env2) env' Star).
          simpl in IHM2. apply IHM2. inversion H. subst. easy. easy.
          easy.
          easy.
          easy. easy. easy.
          apply wftS with (c := env1) in H7. easy.
        - inversion H3. subst. simpl.
          constructor.
        - inversion H3. subst. simpl.
          constructor.
          apply IHM with (env := (env1 ++ env2)).
          easy. easy. easy. easy. easy.
        - inversion H3. subst. simpl.
          setoid_rewrite shift_nonfree_noop with (env := env1) (T := Star) at 2.
          setoid_rewrite shift_nonfree_noop with (env := env1) (T := Star) at 1.
          apply T_Pair.
          admit.
          admit.
          apply IHM3 with (env := (env1 ++ env2)).
          inversion H. easy. easy. easy. easy. easy.
          easy.
          simpl.
          apply IHM4 with (env := (env1 ++ env2) ).
          admit.
          easy.
          easy. easy. 
          admit. 
          constructor. constructor. easy.
          admit.
          constructor. constructor. easy.
          admit.
        - inversion H3. subst.
          simpl.
          apply T_Fst with (B := B). easy.
          apply IHM with (env := (env1 ++ env2)).
          apply wf_sigma. easy. easy.
          easy. easy. easy. easy.
        - inversion H3. subst.
          simpl.
          assert((lift (Datatypes.length env') (Datatypes.length env1) M) = M) by admit.
          rewrite H0.
          apply T_Snd with (A := A). easy. easy. easy.
          rewrite <- H0.
          apply IHM with (env := (env1 ++ env2)).
          apply wf_sigma. easy. easy.
          easy. easy. easy. easy.
        - subst.
          inversion H3. subst. simpl.
          inversion H. subst. easy.
Admitted.

Lemma substitution :
  forall M N A B Γ1 Γ2,
    wf_type B ->
    has_type2 (Γ1 ++ A :: Γ2) M B ->
    has_type2 Γ2 N A ->
    has_type2 (Γ1 ++ Γ2) (subst (length Γ2) N M) B.
Admitted.

(* (* Inductive *)

From MMaps Require Import MMaps.

Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.


Module M := MMaps.RBT.Make(Nat).
Module MF := MMaps.Facts.Properties Nat M.

Definition ctx: Type := M.t term.

(* Typing relation *)
Inductive has_type : ctx -> term -> term -> Prop :=
  | T_Star : forall Γ,
      has_type Γ Star Star
  | T_Nat : forall Γ,
      has_type Γ Nat Star
  | T_Var : forall Γ x T,
      M.find x Γ = Some T ->
      has_type Γ (Var x) T
  | T_Pi : forall Γ G A B k,
      has_type Γ A Star ->
      G = (M.add k A Γ) ->
      has_type G B Star ->
      has_type Γ (Pi A B) Star
  | T_Lam : forall Γ G A b B k,
      G = (M.add k A Γ) ->
      has_type G B Star ->
      has_type Γ (Lam A b) (Pi A B)
  | T_App : forall Γ f a A B,
      has_type Γ f (Pi A B) ->
      has_type Γ a A ->
      has_type Γ (App f a) B
  | T_Sigma : forall Γ G A B k,
      has_type Γ A Star ->
      G = (M.add k A Γ) ->
      has_type G B Star ->
      has_type Γ (Sigma A B) Star
  | T_Pair : forall Γ A B a b,
      has_type Γ a A ->
      has_type Γ b B ->
      has_type Γ (Pair A B a b) (Sigma A B)
  | T_Fst : forall Γ p A B,
      has_type Γ p (Sigma A B) ->
      has_type Γ (TFst p) A
  | T_Snd : forall Γ p A B,
      has_type Γ p (Sigma A B) ->
      has_type Γ (TSnd p) B
  | T_Zero : forall Γ,
      has_type Γ Zero Nat
  | T_Succ : forall Γ n,
      has_type Γ n Nat ->
      has_type Γ (Succ n) Nat
  | T_NatRec : forall Γ P z s n k,
      has_type Γ n Nat ->
      has_type Γ z Nat ->
      has_type (M.add k Nat Γ) s (Pi Nat (Pi Nat Nat)) ->
      has_type Γ (NatRec P z s n) Nat.

Definition lift_ctx (d k: nat) (Γ : ctx) : ctx :=
  M.map (fun T => lift d k T) Γ.

Lemma lift_preserves_typing_map :
  forall Γ t T d k,
    has_type Γ t T ->
    has_type (lift_ctx d k Γ) (lift d k t) (lift d k T).
Proof.
  intros Γ t T d k Hty.
  revert d k.
  induction Hty; intros.
  4:{ simpl.
      apply T_Pi with (G := M.add k (lift d k0 A) (lift_ctx d k0 Γ)) (k := k). simpl in *. easy.
      easy.
      simpl in *.
      simpl in *.
      
   constructor. 


Example type_addI : has_type (M.empty) add (Pi Nat (Pi Nat Nat)).
Proof.
  unfold add.
  apply T_Lam with (k := 0).                    (* λ m *)
  apply T_Lam with (k := 1).                    (* λ n *)
  apply T_NatRec with (k := 2).
  - apply T_Var. simpl. reflexivity.  (* Var 1 : Nat *)
  - apply T_Var. simpl. reflexivity.  (* Var 0 : Nat *)
  - apply T_Lam with (k := 3).                    (* λ m *)
    apply T_Lam with (k := 4).          (* step function s *)
    apply T_Succ. apply T_Var. simpl; reflexivity.
Qed.

Example type_add2 : has_type (extend (extend (extend (extend (extend (M.empty) 0 Nat) 1 Nat) 2 Nat) 3 Nat) 4 Nat) add
  (Pi Nat (Pi Nat Nat)).
Proof.
  unfold add.
  apply T_Lam with (k := 0).                    (* λ m *)
  apply T_Lam with (k := 1).                    (* λ n *)
  apply T_NatRec with (k := 2).
  - apply T_Var. simpl. reflexivity.  (* Var 1 : Nat *)
  - apply T_Var. simpl. reflexivity.  (* Var 0 : Nat *)
  - apply T_Lam with (k := 3).                    (* λ m *)
    apply T_Lam with (k := 4).          (* step function s *)
    apply T_Succ. apply T_Var. simpl; reflexivity.
Qed.


Example type_mult : has_type (M.empty) mult (Pi Nat (Pi Nat Nat)).
Proof.
  unfold mult.
  (* mult = Lam Nat (Lam Nat (NatRec ...)) *)
  (* Step 1: type the outer Lam *)
  apply T_Lam with (k := 0). 
  (* Context now: [Nat] *)
  (* Step 2: type the inner Lam *)
  apply T_Lam with (k := 1).
  (* Context now: [Nat; Nat] *)
  (* Step 3: type NatRec *)
  apply T_NatRec with (k := 2).
  - (* n : Var 1, which is the first argument in context, type Nat *)
    apply T_Var. simpl. reflexivity.
  - (* base case z = Zero : Nat *)
    apply T_Zero.
  - (* step function s = Lam Nat (Lam Nat (App (App add (Var 0)) (Var 2))) *)
    apply T_Lam with (k := 3).
    (* Context now: [Nat; Nat; Nat] *)
    apply T_Lam with (k := 4).
    (* Context now: [Nat; Nat; Nat; Nat] *)
    (* Body: App (App add (Var 0)) (Var 2) *)
    apply T_App with (A := Nat).
    + apply T_App with (A := Nat).
      apply type_add2.
      apply T_Var. simpl. reflexivity.
    + (* argument Var 2 : Nat *)
      apply T_Var. simpl. reflexivity.
Qed.

 *)
(* (* List-based context *)
Definition ctx := list term.

(* Lookup a variable by de Bruijn index *)
Definition lookup (Γ : ctx) (n : nat) : option term :=
  nth_error Γ n.

(* Extend context under a binder *)
Definition extend (Γ : ctx) (T : term) : ctx := T :: Γ. *)

(* Inductive has_type : ctx -> term -> term -> Prop :=
  | T_Star : forall Γ, has_type Γ Star Star
  | T_Nat : forall Γ, has_type Γ Nat Star
  | T_Var : forall Γ x T, lookup Γ x = Some T -> has_type Γ (Var x) T
  | T_Pi : forall Γ A B, has_type Γ A Star -> has_type (A :: Γ) B Star -> has_type Γ (Pi A B) Star
  | T_Lam : forall Γ A b B, has_type (A :: Γ) b B -> has_type Γ (Lam A b) (Pi A B)
  | T_App : forall Γ f a A B, has_type Γ f (Pi A B) -> has_type Γ a A -> has_type Γ (App f a) B
  | T_Sigma : forall Γ A B, has_type Γ A Star -> has_type (A :: Γ) B Star -> has_type Γ (Sigma A B) Star
  | T_Pair : forall Γ A B a b, has_type Γ a A -> has_type Γ b B -> has_type Γ (Pair A B a b) (Sigma A B)
  | T_Fst : forall Γ p A B, has_type Γ p (Sigma A B) -> has_type Γ (TFst p) A
  | T_Snd : forall Γ p A B, has_type Γ p (Sigma A B) -> has_type Γ (TSnd p) B
  | T_Zero : forall Γ, has_type Γ Zero Nat
  | T_Succ : forall Γ n, has_type Γ n Nat -> has_type Γ (Succ n) Nat
  | T_NatRec : forall Γ P z s n, has_type Γ n Nat -> has_type Γ z Nat -> has_type (Nat :: Γ) s (Pi Nat (Pi Nat Nat)) -> has_type Γ (NatRec P z s n) Nat.

Lemma lift_id_below_all :
  forall t d k,
    (forall n, occurs_inb n t = true -> n < k) ->
    lift d k t = t.
Proof. intro t.
       induction t; intros.
        10:{
        simpl in *.
        specialize(H n).
        assert((n =? n) = true).
        { rewrite Nat.eqb_refl. easy. }
        apply H in H0.
        apply Nat.ltb_lt in H0. rewrite H0. easy.
        }
       - easy.
       - easy.
       - simpl.
         rewrite IHt1, IHt2. easy.
         intros. simpl in H.
         specialize(H n).
         assert(occurs_inb n t1 || occurs_inb n t2 = true).
         { rewrite H0. lia. }
         apply H in H1. lia.
         intros. simpl in H.
         specialize(H n).
         assert(occurs_inb n t1 || occurs_inb n t2 = true).
         { rewrite H0. lia. }
         apply H in H1. lia.
Admitted.

Lemma lift_under_extend_correct :
  forall t d k,
    (forall n, occurs_inb n t = true -> n < k) ->
    lift d (k+1) t = lift d k (lift 1 k t).
Admitted.

Lemma lookup_extend_eq :
  forall Γ T n,
    lookup (T :: Γ) (S n) = lookup Γ n.
Proof.
  intros Γ T n.
  simpl.
  (* nth_error (T :: Γ) n = nth_error Γ (n - 1) if n > 0 *)
  destruct n.
  - easy.
  - easy.
Qed.

Lemma ctx_eqe: forall x Γ Δ A T,
  (forall (x : nat) (T' : term), lookup Γ x = Some T' -> lookup Δ x = Some T') ->
  lookup (A :: Γ) x = Some T ->
  lookup (A :: Δ) x = Some T.
Proof. intro x.
       induction x; intros.
       - simpl in *. easy.
       - simpl in *. apply H. easy.
Qed.

Lemma weakening : forall Γ Δ t T,
  has_type Γ t T ->
  (forall x T', lookup Γ x = Some T' -> lookup Δ x = Some T') ->
  has_type Δ t T.
Proof.
  intros Γ Δ t T Htyp Hlook.
  revert Δ Hlook.
  induction Htyp; intros.
  4:{
  constructor. 
  apply IHHtyp1. easy.
  apply IHHtyp2. intros.
  apply ctx_eqe with ( Γ :=  Γ). easy.
  easy.
  }
  3:{ 
  constructor.
  apply Hlook. easy.

  }
  
  constructor.
  constructor.

  constructor. 
  apply IHHtyp.
  intros.
  apply ctx_eqe with ( Γ :=  Γ). easy.
  easy.
  
  apply T_App with (A := A).
  apply IHHtyp1. easy.
  apply IHHtyp2. easy.

  constructor. 
  apply IHHtyp1. easy.
  apply IHHtyp2. intros.
  apply ctx_eqe with ( Γ :=  Γ). easy.
  easy.

  constructor.
  apply IHHtyp1. easy.
  apply IHHtyp2. intros.
  apply Hlook. easy.

  apply T_Fst with (B:=B).
  apply IHHtyp.
  intros. apply Hlook. easy.

  apply T_Snd with (A:=A).
  apply IHHtyp.
  intros. apply Hlook. easy.
  
  constructor.
  constructor.
  apply IHHtyp. easy.
  
  constructor.
  apply IHHtyp1. easy.
  apply IHHtyp2. easy.
  apply IHHtyp3. intros.

  
  apply ctx_eqe with ( Γ :=  Γ). easy.
  easy.
Qed. *)

Lemma lift_closed_gen :
  forall t k d,
    closed t k ->   (* t has no free variables after depth k *)
    lift d k t = t.
Proof.
  intros t.
  induction t; intros.
  10:{ simpl. inversion H. 
       simpl in H. subst.
       assert(n <? S n = true).
       { apply Nat.ltb_lt. lia. }
       rewrite H0.
       easy.
       subst. simpl in H. 
       assert(n <? S m = true).
       { apply Nat.ltb_lt. lia. }
       rewrite H1.
       easy.
  }
  admit.
  admit.
  - (* Pi A B *)
    destruct H as [HA HB].
    simpl. rewrite IHt2.
    rewrite IHt1. easy. easy. easy.
Admitted.

Lemma lift_closed_id :
  forall t d,
    closed t 0 ->   (* t has no free variables after depth k *)
    lift d 0 t = t.
Proof. intros. rewrite lift_closed_gen.
       easy. easy.
Qed.

Lemma closed_weaken : forall t k k',
  k <= k' ->
  closed t k ->
  closed t k'.
Proof. intro t.
       induction t; intros.
       3:{ simpl in *.
           split. apply IHt1 with (k := k). easy. easy.
           apply IHt2 with (k := S k). lia. easy.
         }
       9:{ simpl in *. lia. }
Admitted.

Lemma closed_lift : forall t k d,
  closed t k ->
  closed (lift d k t) (k + d).
Proof. intro t.
       induction t; intros.
       3:{ simpl.
           split. apply IHt1. simpl in H. easy.
           apply IHt2. simpl in H. easy.
         }
       9:{ simpl.
           simpl in H.
           apply Nat.ltb_lt in H. rewrite H.
           simpl.
           apply Nat.ltb_lt in H. lia.
         }
Admitted.

Lemma lift_closed_general :
  forall t d k k',
    closed t k -> k <= k' -> closed (lift d k t) (k' + d).
Proof. intros.
       apply closed_lift with (d := d) in H.
       apply closed_weaken with (k := k + d). lia.
       easy.
Qed.

(* Lemma subst_closed_shift :
  forall t s j d,
    closed t (S j + d) ->
    closed s 0 ->
    closed (subst (j + d) (lift d 0 s) t) (j + d).
Proof. intro t.
       induction t; intros.
       3:{ simpl. split.
           apply IHt1.
(*            apply closed_weaken with (k := j); try lia. *)
           simpl in H. easy.
           easy.
           simpl.
           rewrite lift_lift.
           specialize(IHt2 s j (S d)).
           simpl in IHt2. 
           assert((j + S d) = S (j + d)) by lia.
           rewrite H1 in IHt2.
           assert(1 + d = S d) by lia.
           rewrite H2.
           apply IHt2. simpl in H. easy. easy.
         }
        9:{ simpl.
            destruct (n ?= j + d) eqn:E.
            simpl. rewrite lift_0. simpl.
            apply lift_closed_general. easy.
            lia. inversion H. subst.
            admit.
            subst.
            inversion H. subst. admit.
            subst.
            apply closed_weaken with (k := S (j + d)).
            + simpl.
              
              rewrite E.
              simpl in *.
               (* variable does not match: stays Var n *)
              apply Nat.eqb_neq in E.
              lia.
           }
Admitted. *)



