Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Bool.Bool Lia.
From DTSMPST Require Import sort.sort sort.subst.


Fixpoint is_value (t : term) : bool :=
  match t with
  | Star | Nat | Zero => true
  | Succ n => is_value n
(*   | Pi A B => is_value A && is_value B
  | Sigma A B => is_value A && is_value B *)
  | Pair A B a b => is_value A && is_value B && is_value a && is_value b
  | Lam _ _ => true
  | _ => false
  end.

(* (* Better evaluator with small-step reduction *)
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
 *)

Fixpoint eval2 (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      (* Values don't reduce further *)
      | t' => if is_value t' then Some t' else
          match t with

      | App t1 t2 =>
          match eval2 fuel' t1 with
          | Some (Lam _ b) =>
              (* evaluate argument fully before substituting *)
              match eval2 fuel' t2 with
                | Some v2 => eval2 fuel' (subst2 0 v2 b)
                | None => None
              end
          | Some t1' =>
              match eval2 fuel' t2 with
                | Some t2' => Some (App t1' t2')
                | None => None
              end
          | None => None
          end
      | TFst p =>
          match eval2 fuel' p with
          | Some (Pair _ _ a b) => eval2 fuel' a
          | Some p' => Some (TFst p')
          | None => None
          end
      | TSnd p =>
          match eval2 fuel' p with
          | Some (Pair _ _ a b) => eval2 fuel' b
          | Some p' => Some (TSnd p')
          | None => None
          end


      | NatRec P z s Zero =>
          eval2 fuel' z
      | NatRec P z s (Succ n) =>
          (* recursively evaluate n first *)
          match eval2 fuel' n with
            | Some n' =>
                let rec_call := NatRec P z s n' in
                eval2 fuel' (App (App s n') rec_call)
            | None => None
          end

      | Succ n =>
          match eval2 fuel' n with
          | Some n' => eval2 fuel' (Succ n')
          | None => None
          end

     | Lam A b =>
         match eval2 fuel' A, eval2 fuel' b with
         | Some A', Some b' => Some (Lam A' b')
         | _, _ => None
         end
     | Pi A B =>
         match eval2 fuel' A, eval2 fuel' B with
         | Some A', Some B' => Some (Pi A' B')
         | _, _ => None
         end
     | Sigma A B =>
         match eval2 fuel' A, eval2 fuel' B with
         | Some A', Some B' => Some (Sigma A' B')
         | _, _ => None
         end
     | Pair A B a b =>
         match eval2 fuel' A, eval2 fuel' B, eval2 fuel' a, eval2 fuel' b with
         | Some A', Some B', Some a', Some b' =>
             Some (Pair A' B' a' b')
         | _, _, _, _ => None
         end


      | _ => None  (* No reduction possible *)
          end
      end
  end.


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
      | TFst p =>
          match eval fuel' p with
          | Some (Pair _ _ a b) => eval fuel' a
          | Some p' => Some (TFst p')
          | None => None
          end
      | TSnd p =>
          match eval fuel' p with
          | Some (Pair _ _ a b) => eval fuel' b
          | Some p' => Some (TSnd p')
          | None => None
          end


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

     | Lam A b =>
         match eval fuel' A, eval fuel' b with
         | Some A', Some b' => Some (Lam A' b')
         | _, _ => None
         end
     | Pi A B =>
         match eval fuel' A, eval fuel' B with
         | Some A', Some B' => Some (Pi A' B')
         | _, _ => None
         end
     | Sigma A B =>
         match eval fuel' A, eval fuel' B with
         | Some A', Some B' => Some (Sigma A' B')
         | _, _ => None
         end
     | Pair A B a b =>
         match eval fuel' A, eval fuel' B, eval fuel' a, eval fuel' b with
         | Some A', Some B', Some a', Some b' =>
             Some (Pair A' B' a' b')
         | _, _, _, _ => None
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
Definition six :=  Succ (Succ (Succ (Succ (Succ (Succ Zero))))).
Definition seven := Succ(Succ (Succ (Succ (Succ (Succ (Succ Zero)))))).

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
      Zero                (* z: return Zero *)
      (Lam Nat (Lam Nat (App (App add (Var 0)) (Var 2)))) (* s: λk rec, n + rec *)
      (Var 1)             (* induction over m *)
    )
  ).

(* Definition fact_body : term :=
  Lam Nat (Lam Nat (  (* takes self and n *)
    NatRec Nat
      (Succ Zero)                     (* base = 1 *)
      (Lam Nat (Lam Nat (App (App mult (Succ (Var 1))) (Var 0))))  (* step *)
      (Var 0)
  )).

Definition Fix (A : term) (f : term) : term :=
  Lam A (  (* takes a dummy arg to simulate unfolding *)
    NatRec A
      (App f (Var 0))                          (* base: f applied to dummy *)
      (Lam A (Lam (Var 1) (App f (Var 0))))    (* step: f applied to recursive call *)
      (Var 0)                                  (* argument to NatRec *)
  ).

Definition fact : term :=
  App (Fix (Pi Nat Nat) fact_body) (Lam Nat (Var 0)). *)


Definition fact : term :=
  Lam Nat (
    NatRec Nat
      (Succ Zero)   (* base: 1 *)
      (Lam Nat (Lam Nat (
         App (App mult (Succ (Var 1))) (Var 0)
      )))
      (Var 0)
  ).

(* fib : Nat -> Nat *)
(* fib : Nat -> Nat, implemented by iterating pairs (fib n, fib (n+1)) *)
Definition fib : term :=
  Lam Nat
    (TFst
      (NatRec
         (Lam Nat (Sigma Nat Nat))                 (* P : Nat -> Sigma Nat Nat *)
         (Pair Nat Nat (Succ Zero) (Succ Zero))           (* z : (0,1) *)
         (Lam Nat (Lam (Sigma Nat Nat)             (* s : \m rec. ... *)
            (Pair Nat Nat
               (TSnd (Var 0))                       (* new first = old second *)
               (App (App add (TFst (Var 0)))        (* new second = fst(rec) + snd(rec) *)
                    (TSnd (Var 0))
               )
            )
         ))
         (Var 0)                                   (* recurse on the argument n (Var 0) *)
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
Definition fact2 : term := App fact seven.
Definition fib3 : term := App fib six.

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

Eval compute in eval2 50 add_2_1.    (* Some (Succ (Succ (Succ Zero))) *)
Eval compute in eval2 100 mult_2_3.  (* Some (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))) *)
Eval compute in eval2 150 mult_3_3.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in eval2 150 mult_4_5.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in eval2 150 mult_5_4.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in match (eval2 500 mult_4_5) with
                  | Some k => term2nat k
                  | _      => None
                end.  (* Some (Succ ... 9 times ... Zero) *)
Eval compute in match (eval2 500 mult_5_5_5) with
                  | Some k => term2nat k
                  | _      => None
                end. 
(* Eval compute in match (eval2 10000 fact2) with
                  | Some k => term2nat k
                  | _      => None
                end.  *)
Eval compute in match (eval2 500 fib3) with
                  | Some k => term2nat k
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
                end. 
(* Eval compute in match (eval 10000 fact2) with
                  | Some k => term2nat k
                  | _      => None
                end.  *)
Eval compute in match (eval 500 fib3) with
                  | Some k => term2nat k
                  | _      => None
                end. 

Definition dep_pair_example :=
  Pair Nat
       (Lam Nat Nat)        (* B = λ x : Nat. Nat, type of second component depends on first *)
       three
       (Succ (Succ three)).          (* second component = 2+1 = 3 *)

Definition fst_dep := TFst dep_pair_example.
Definition snd_dep := TSnd dep_pair_example.

Eval compute in eval 10 fst_dep.  (* Should be Some two *)
Eval compute in eval 10 snd_dep.
  (* Should be Some (Succ two) *)




(*Inductively*)

Inductive step : term -> term -> Prop :=
  (* β-reduction *)
  | Step_Beta : forall A b v,
      is_value v = true ->
      step (App (Lam A b) v) (subst 0 v b)
  | Step_Pi : forall A B v,
      is_value v = true ->
      step (App (Pi A B) v) (subst 0 v B)

  (* Application congruence *)
  | Step_App1 : forall t1 t1' t2,
      step t1 t1' ->
      step (App t1 t2) (App t1' t2)
  | Step_App2 : forall v1 t2 t2',
      is_value v1 = true ->
      step t2 t2' ->
      step (App v1 t2) (App v1 t2')

  (* Lambda congruence *)
  | Step_Lam : forall A t t',
      step t t' ->
      step (Lam A t) (Lam A t')

  (* Pi congruence *)
  | Step_Pi1 : forall A B B',
      step B B' ->
      step (Pi A B) (Lam A B')
  | Step_Pi2 : forall A A' B,
      step A A' ->
      step (Pi A B) (Lam A' B)

  (* Pairs *)
  | Step_FstPair : forall A B v1 v2,
      is_value v1 = true -> is_value v2 = true ->
      step (TFst (Pair A B v1 v2)) v1
  | Step_Fst : forall t t',
      step t t' -> step (TFst t) (TFst t')

  | Step_SndPair : forall A B v1 v2,
      is_value v1 = true -> is_value v2 = true ->
      step (TSnd (Pair A B v1 v2)) v2
  | Step_Snd : forall t t',
      step t t' -> step (TSnd t) (TSnd t')

  (* Natural numbers *)
  | Step_Succ : forall n n',
      step n n' -> step (Succ n) (Succ n')

  | Step_NatRecZero : forall P z s,
      step (NatRec P z s Zero) z
  | Step_NatRecSucc : forall P z s n,
      step (NatRec P z s (Succ n))
           (App (App s n) (NatRec P z s n))

  | Step_NatRec : forall P z s n n',
      step n n' ->
      step (NatRec P z s n) (NatRec P z s n').

Inductive multi {X:Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall x, multi R x x
  | multi_step : forall x y z,
      R x y -> multi R y z -> multi R x z.

Notation "t1 '-->*' t2" := (multi step t1 t2) (at level 40).



Example mult_2_3_eval : multi step mult_2_3 six.
Proof.
  unfold mult_2_3, mult, two, three, six, add, zero, one.

  (* Step 1: reduce the left side of the outer App *)
  eapply multi_step.
  { 
    apply Step_App1.
    (* reduce App (Lam …) (Succ 2) → Step_Beta *)
    apply Step_Beta.
    simpl; reflexivity.
  }

  (* Step 2: now outer App has Lam … applied to 3 → Step_Beta *)
  eapply multi_step.
  { 
    apply Step_Beta.
    simpl; reflexivity.
  }

  (* Step 3: NatRec over two (Succ one) *)
  eapply multi_step.
  { 
    apply Step_NatRecSucc.
  }

  (* Step 4: Reduce App (App s n) (NatRec ...) *)
  eapply multi_step.
  {
    apply Step_App1.
    apply Step_Beta.
    simpl; reflexivity.
  }

  (* Step 5: inner NatRec for n=Zero *)
  eapply multi_step.
  { 
    (* Step outer App to reach NatRec *)
    apply Step_App2.
    - simpl; reflexivity.  (* function is value *)
    - simpl. apply Step_NatRecSucc. (* now NatRec Zero is at top *)
  }

  (* Step 6: reduce App (App s n) for inner NatRec *)
  eapply multi_step.
  { 
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_App1.
    apply Step_Beta.
    simpl; reflexivity.
  }

  (* Step 7: base case NatRec for Zero *)
  eapply multi_step.
  { 
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_App2.
    simpl; easy.
    apply Step_NatRecZero.
  }

  (* Step 8: compute addition using add function *)
  eapply multi_step.
  { 
    apply Step_App2.
    simpl; easy.
    apply Step_Beta.
    simpl; reflexivity.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    simpl; reflexivity.
    apply Step_App1.
    apply Step_Beta.
    easy.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    apply Step_Beta.
    simpl; reflexivity.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_NatRecZero.
  }

  (* Step 9: final Succ applications for add result *)
  eapply multi_step.
  { 
    apply Step_Beta.
    easy.
  }

  eapply multi_step.
  { 
    simpl.
    apply Step_App1.
    apply Step_Beta.
    easy.
  }

  eapply multi_step.
  { 
    simpl.
    apply Step_Beta.
    easy.
  }

  simpl.
  eapply multi_step.
  { 
    apply Step_NatRecSucc.
  }

  eapply multi_step.
  { 
    apply Step_App1.
    apply Step_Beta.
    easy.
  }

  simpl.
  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    apply Step_NatRecSucc.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    apply Step_App1.
    apply Step_Beta.
    easy.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_NatRecSucc.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_App1.
    apply Step_Beta.
    simpl; easy.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_App2.
    easy.
    apply Step_NatRecZero. 
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_App2.
    simpl; easy.
    apply Step_Beta.
    easy.
  }

  eapply multi_step.
  { 
    apply Step_App2.
    easy.
    simpl.
    apply Step_Beta.
    simpl; easy.
  }

  eapply multi_step.
  { 
    simpl.
    apply Step_Beta.
    easy.
  }

  simpl.

  (* Step 10: we reach six *)
  eapply multi_refl.
Qed.




