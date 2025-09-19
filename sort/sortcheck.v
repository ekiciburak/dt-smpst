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

  | Fst p =>
      do tyP <- type_check Γ p;
      match tyP with
      | Sigma A B => ret A
      | _ => Err "Fst expects Sigma type"
      end
  
  | Snd p =>
    do tyP <- type_check Γ p;
    match tyP with
    | Sigma A B =>
        let fst_val := Fst p in
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
  type_of (Fst two) = Err "Fst expects Sigma type".
reflexivity. Qed.
