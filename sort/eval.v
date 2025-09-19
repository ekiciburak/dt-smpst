Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.sort sort.subst.

Fixpoint is_value (t : term) : bool :=
  match t with
  | Star | Nat | Zero => true
  | Succ n => is_value n
  | Pi A B => is_value A && is_value B
  | Sigma A B => is_value A && is_value B
  | Pair A B a b => is_value A && is_value B && is_value a && is_value b
  | Lam _ _ => true
  | _ => false
  end.


(* Better evaluator with small-step reduction *)
Inductive step : term -> term -> Prop :=
  | ST_AppLam : forall A b v,
      is_value v = true ->
      step (App (Lam A b) v) (subst 0 v b)
  | ST_Succ : forall n n',
      step n n' ->
      step (Succ n) (Succ n')
  | ST_App1 : forall t1 t1' t2,
      step t1 t1' ->
      step (App t1 t2) (App t1' t2)
  | ST_App2 : forall v1 t2 t2',
      is_value v1 = true ->
      step t2 t2' ->
      step (App v1 t2) (App v1 t2')
  | ST_FstPair : forall A B a b,
      is_value a = true -> is_value b = true ->
      step (Fst (Pair A B a b)) a
  | ST_SndPair : forall A B a b,
      is_value a = true -> is_value b = true ->
      step (Snd (Pair A B a b)) b
  | ST_NatRecZero : forall P z s,
      step (NatRec P z s Zero) z
  | ST_NatRecSucc : forall P z s n,
      is_value n = true ->
      step (NatRec P z s (Succ n)) (App (App s n) (NatRec P z s n))
  | ST_NatRec : forall P z s n n',
      step n n' ->
      step (NatRec P z s n) (NatRec P z s n').

Fixpoint eval (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      (* Values don't reduce further *)
      | t' => if is_value t' then Some t' else
          match t with

      | App t1 t2 =>
          match eval fuel' t1 with
          | Some (Lam _ b) =>
              (* evaluate argument fully before substituting *)
              match eval fuel' t2 with
              | Some v2 => eval fuel' (subst 0 v2 b)
              | None => None
              end
          | Some t1' =>
              match eval fuel' t2 with
              | Some t2' => Some (App t1' t2')
              | None => None
              end
          | None => None
          end
          | Fst (Pair A B a b) =>
              if is_value a && is_value b then eval fuel' a
              else None
          
          | Snd (Pair A B a b) =>
              if is_value a && is_value b then eval fuel' b
              else None
          
      | NatRec P z s Zero =>
          eval fuel' z
      | NatRec P z s (Succ n) =>
          (* recursively evaluate n first *)
          match eval fuel' n with
          | Some n' =>
              let rec_call := NatRec P z s n' in
              eval fuel' (App (App s n') rec_call)
          | None => None
          end


          
          | Succ n =>
              match eval fuel' n with
              | Some n' => eval fuel' (Succ n')
              | None => None
              end
          
          | _ => None  (* No reduction possible *)
          end
      end
  end.

(* === Numbers === *)
Definition zero := Zero.
Definition one := Succ Zero.
Definition two := Succ (Succ Zero).
Definition three := Succ (Succ (Succ Zero)).
Definition four := Succ (Succ (Succ (Succ Zero))).
Definition five := Succ (Succ (Succ (Succ (Succ Zero)))).

(* === Addition === *)
(* add m n *)
Definition add :=
  Lam Nat (Lam Nat
    (NatRec
      (Lam Nat Nat)             (* P: Nat -> Type *)
      (Var 0)                    (* z --> return n  *)
      (Lam Nat (Lam Nat (Succ (Var 0))))  (* s --> λk rec, rec [where rec = Succ k] *)
      (Var 1)                    (* induction over m *)
    )
  ).

(* === Multiplication === *)
(* mult m n *)
Definition mult :=
  Lam Nat (Lam Nat
    (NatRec
      (Lam Nat Nat)       (* P: Nat -> Type *)
      Zero                 (* z --> return Zero  *)
      (Lam Nat (Lam Nat (App (App add (Var 0)) (Var 2)))) (* s --> λk rec, n + rec [where rec = mult k n]  *)
      (Var 1)              (* induction over m *)
    )
  ).

(* === Examples === *)
Definition add_2_1 := App (App add three) one.
Definition mult_2_3 := App (App mult two) three.
Definition mult_3_3 := App (App mult three) three.
Definition mult_4_5 := App (App mult four) five.
Definition mult_5_4 := App (App mult five) four.
Definition mult_5_5 := App (App mult five) five.
Definition mult_5_5_5 := App (App mult (App (App mult five) five)) five.

Fixpoint term2nat (t: term):=
  match t with
    | Zero   => Some O
    | Succ k =>
      match (term2nat k) with
        | Some u => Some (S u)
        | _      => None 
      end
    | _      => None
  end.

Eval compute in eval 50 add_2_1.    (* Some (Succ (Succ (Succ Zero))) *)
Eval compute in eval 100 mult_2_3.  (* Some (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))) *)
Eval compute in eval 150 mult_3_3.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in eval 150 mult_4_5.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in eval 150 mult_5_4.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in match (eval 500 mult_4_5) with
                  | Some k => term2nat k
                  | _      => None
                end.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in match (eval 500 mult_5_5_5) with
                  | Some k => term2nat k
                  | _      => None
                end.  (* Some (Succ ... 9 times ... Zero) *)

Definition dep_pair_example :=
  Pair Nat
       (Lam Nat Nat)        (* B = λ x : Nat. Nat, type of second component depends on first *)
       two
       (Succ (Succ two)).          (* second component = 2+1 = 3 *)

Definition fst_dep := Fst dep_pair_example.
Definition snd_dep := Snd dep_pair_example.

Eval compute in eval 10 fst_dep.  (* Should be Some two *)
Eval compute in eval 10 snd_dep.
  (* Should be Some (Succ two) *)
