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

Section ManualMutualInduction_ListIH.

  Variable Pw : whnf -> Prop.
  Variable Pn : neutral -> Prop.
  Variable Pc : closure -> Prop.
  (* New: predicate on the inner list ρ *)
  Variable Pr : list whnf -> Prop.

  (* Hypotheses for each constructor *)
  Hypotheses
    (H_VStar    : Pw VStar)
    (H_VNat     : Pw VNat)
    (H_VPi      : forall A B, Pw A -> Pc B -> Pw (VPi A B))
    (H_VSigma   : forall A B, Pw A -> Pc B -> Pw (VSigma A B))
    (H_VLam     : forall cl, Pc cl -> Pw (VLam cl))
    (H_VPair    : forall A B a b, Pw A -> Pw B -> Pw a -> Pw b -> Pw (VPair A B a b))
    (H_VZero    : Pw VZero)
    (H_VSucc    : forall n, Pw n -> Pw (VSucc n))
    (H_VNeutral : forall n, Pn n -> Pw (VNeutral n))
    (H_VVec     : forall n A, Pw n -> Pw A -> Pw (VVec n A))
    (H_VNilV    : forall A, Pw A -> Pw (VNilV A))
    (H_VConsV   : forall A n x xs, Pw A -> Pw n -> Pw x -> Pw xs -> Pw (VConsV A n x xs))

    (H_NVar    : forall i, Pn (NVar i))
    (H_NApp    : forall n v, Pn n -> Pw v -> Pn (NApp n v))
    (H_NFst    : forall n, Pn n -> Pn (NFst n))
    (H_NSnd    : forall n, Pn n -> Pn (NSnd n))
    (H_NNatRec : forall P z s n, Pw P -> Pw z -> Pw s -> Pn n -> Pn (NNatRec P z s n))
    (H_NVecRec : forall A P z s n xs, Pw A -> Pw P -> Pw z -> Pw s -> Pw n -> Pn xs -> Pn (NVecRec A P z s n xs))

    (* New: list induction principles for Pr *)
    (H_Pr_nil  : Pr [])
    (H_Pr_cons : forall (v : whnf) (ρ : list whnf), Pw v -> Pr ρ -> Pr (v :: ρ))

    (* Cl now expects Pr ρ rather than Forall Pw ρ *)
    (H_Cl      : forall ρ t, Pr ρ -> Pc (Cl ρ t)).

  (* Mutual recursive proofs: whnf_proof, neutral_proof, closure_proof.
     closure_proof builds Pr ρ by iterating over the list, using whnf_proof
     for each head and recursion for the tail. *)
  Fixpoint whnf_proof (v : whnf) {struct v} : Pw v :=
    match v with
    | VStar            => H_VStar
    | VNat             => H_VNat
    | VPi A B          => H_VPi A B (whnf_proof A) (closure_proof B)
    | VSigma A B       => H_VSigma A B (whnf_proof A) (closure_proof B)
    | VLam cl          => H_VLam cl (closure_proof cl)
    | VPair A B a b    => H_VPair A B a b (whnf_proof A) (whnf_proof B) (whnf_proof a) (whnf_proof b)
    | VZero            => H_VZero
    | VSucc n          => H_VSucc n (whnf_proof n)
    | VNeutral n       => H_VNeutral n (neutral_proof n)
    | VVec n A         => H_VVec n A (whnf_proof n) (whnf_proof A)
    | VNilV A          => H_VNilV A (whnf_proof A)
    | VConsV A n x xs  => H_VConsV A n x xs (whnf_proof A) (whnf_proof n) (whnf_proof x) (whnf_proof xs)
    end

  with neutral_proof (n : neutral) {struct n} : Pn n :=
    match n with
    | NVar i           => H_NVar i
    | NApp n' v        => H_NApp n' v (neutral_proof n') (whnf_proof v)
    | NFst n'          => H_NFst n' (neutral_proof n')
    | NSnd n'          => H_NSnd n' (neutral_proof n')
    | NNatRec P z s n' => H_NNatRec P z s n' (whnf_proof P) (whnf_proof z) (whnf_proof s) (neutral_proof n')
    | NVecRec A P z s n' xs =>
        H_NVecRec A P z s n' xs
          (whnf_proof A) (whnf_proof P) (whnf_proof z) (whnf_proof s)
          (whnf_proof n') (neutral_proof xs)
    end

  with closure_proof (c : closure) {struct c} : Pc c :=
    match c with
    | Cl ρ t =>
        (* build the Pr ρ instance by recursion over ρ, calling whnf_proof for heads *)
        let fix build (ρ0 : list whnf) : Pr ρ0 :=
            match ρ0 with
            | []     => H_Pr_nil
            | v::r   => H_Pr_cons v r (whnf_proof v) (build r)
            end
        in H_Cl ρ t (build ρ)
    end.

  Theorem whnf_mutind_listIH :
    (forall v, Pw v) /\ (forall n, Pn n) /\ (forall c, Pc c).
  Proof.
    split.
    - intro v; exact (whnf_proof v).
    - split.
      + intro n; exact (neutral_proof n).
      + intro c; exact (closure_proof c).
  Qed.

End ManualMutualInduction_ListIH.

(* Section ManualMutualInduction_Prop.

  Variable Pw : whnf -> Prop.
  Variable Pn : neutral -> Prop.
  Variable Pc : closure -> Prop.

  (* Hypotheses for each constructor (one hypothesis per constructor) *)
  Hypotheses
    (H_VStar    : Pw VStar)
    (H_VNat     : Pw VNat)
    (H_VPi      : forall A B, Pw A -> Pc B -> Pw (VPi A B))
    (H_VSigma   : forall A B, Pw A -> Pc B -> Pw (VSigma A B))
    (H_VLam     : forall cl, Pc cl -> Pw (VLam cl))
    (H_VPair    : forall A B a b, Pw A -> Pw B -> Pw a -> Pw b -> Pw (VPair A B a b))
    (H_VZero    : Pw VZero)
    (H_VSucc    : forall n, Pw n -> Pw (VSucc n))
    (H_VNeutral : forall n, Pn n -> Pw (VNeutral n))
    (H_VVec     : forall n A, Pw n -> Pw A -> Pw (VVec n A))
    (H_VNilV    : forall A, Pw A -> Pw (VNilV A))
    (H_VConsV   : forall A n x xs, Pw A -> Pw n -> Pw x -> Pw xs -> Pw (VConsV A n x xs))

    (H_NVar    : forall i, Pn (NVar i))
    (H_NApp    : forall n v, Pn n -> Pw v -> Pn (NApp n v))
    (H_NFst    : forall n, Pn n -> Pn (NFst n))
    (H_NSnd    : forall n, Pn n -> Pn (NSnd n))
    (H_NNatRec : forall P z s n, Pw P -> Pw z -> Pw s -> Pn n -> Pn (NNatRec P z s n))
    (H_NVecRec : forall A P z s n xs, Pw A -> Pw P -> Pw z -> Pw s -> Pw n -> Pn xs -> Pn (NVecRec A P z s n xs))

    (H_Cl     : forall ρ t, Forall Pw ρ -> Pc (Cl ρ t)).

  (* Helper: build a Forall Pw ρ by structural recursion over the list ρ,
     using the mutual whnf_proof function for elements. *)

(* ---- mutual Fixpoint: whnf_proof, neutral_proof, closure_proof ---- *)
  Fixpoint whnf_proof (v : whnf) {struct v} : Pw v :=
    match v with
    | VStar            => H_VStar
    | VNat             => H_VNat
    | VPi A B          => H_VPi A B (whnf_proof A) (closure_proof B)
    | VSigma A B       => H_VSigma A B (whnf_proof A) (closure_proof B)
    | VLam cl          => H_VLam cl (closure_proof cl)
    | VPair A B a b    => H_VPair A B a b (whnf_proof A) (whnf_proof B) (whnf_proof a) (whnf_proof b)
    | VZero            => H_VZero
    | VSucc n          => H_VSucc n (whnf_proof n)
    | VNeutral n       => H_VNeutral n (neutral_proof n)
    | VVec n A         => H_VVec n A (whnf_proof n) (whnf_proof A)
    | VNilV A          => H_VNilV A (whnf_proof A)
    | VConsV A n x xs  => H_VConsV A n x xs (whnf_proof A) (whnf_proof n) (whnf_proof x) (whnf_proof xs)
    end

  with neutral_proof (n : neutral) {struct n} : Pn n :=
    match n with
    | NVar i           => H_NVar i
    | NApp n' v        => H_NApp n' v (neutral_proof n') (whnf_proof v)
    | NFst n'          => H_NFst n' (neutral_proof n')
    | NSnd n'          => H_NSnd n' (neutral_proof n')
    | NNatRec P z s n' => H_NNatRec P z s n' (whnf_proof P) (whnf_proof z) (whnf_proof s) (neutral_proof n')
    | NVecRec A P z s n' xs => H_NVecRec A P z s n' xs
                                    (whnf_proof A) (whnf_proof P) (whnf_proof z) (whnf_proof s)
                                    (whnf_proof n') (neutral_proof xs)
    end

  with closure_proof (c : closure) {struct c} : Pc c :=
    match c with
    | Cl ρ t =>
        (* local structural recursion over ρ that may call whnf_proof for each head *)
        let fix build (ρ0 : list whnf) : Forall Pw ρ0 :=
            match ρ0 with
            | []     => @Forall_nil whnf Pw
            | v :: r => @Forall_cons whnf Pw v r (whnf_proof v) (build r)
            end
        in H_Cl ρ t (build ρ)
    end.

  Theorem whnf_mutind :
    (forall v, Pw v) /\ (forall n, Pn n) /\ (forall c, Pc c).
  Proof.
    split.
    - intro v; exact (whnf_proof v).
    - split.
      + intro n; exact (neutral_proof n).
      + intro c; exact (closure_proof c).
  Qed.

End ManualMutualInduction_Prop.
 *)

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

  | VPi A B         =>
      VPi (shift_whnf d c A)
          (match B with Cl ρ b => Cl (map (shift_whnf d (S c)) ρ) b end)
  | VSigma A B      =>
      VSigma (shift_whnf d c A)
             (match B with Cl ρ b => Cl (map (shift_whnf d (S c)) ρ) b end)

  | VLam (Cl ρ b)   => VLam (Cl (map (shift_whnf d (S c)) ρ) b)

  | VPair A B a b   => VPair (shift_whnf d c A) (shift_whnf d c B)
                             (shift_whnf d c a) (shift_whnf d c b)
  | VZero           => VZero
  | VSucc v1        => VSucc (shift_whnf d c v1)
  | VNeutral n      => VNeutral (shift_neutral d c n)
  | VVec n A        => VVec (shift_whnf d c n) (shift_whnf d c A)
  | VNilV A         => VNilV (shift_whnf d c A)
  | VConsV A n x xs => VConsV (shift_whnf d c A) (shift_whnf d c n) (shift_whnf d c x) (shift_whnf d c xs)
  end.

Lemma shift_compose_mut :
    (forall v,  forall d1 d2 c, shift_whnf d1 c (shift_whnf d2 c v) = shift_whnf (d1 + d2) c v) /\
    (forall n,  forall d1 d2 c, shift_neutral d1 c (shift_neutral d2 c n) = shift_neutral (d1 + d2) c n) /\
    (forall cl, forall d1 d2 c,
                match cl with
                  | Cl ρ t => map (shift_whnf d1 c) (map (shift_whnf d2 c) ρ) = map (shift_whnf (d1 + d2) c) ρ
                end).
Proof.
  apply (whnf_mutind_listIH
           (fun v  => forall d1 d2 c, shift_whnf d1 c (shift_whnf d2 c v) = shift_whnf (d1 + d2) c v)
           (fun n  => forall d1 d2 c, shift_neutral d1 c (shift_neutral d2 c n) = shift_neutral (d1 + d2) c n)
           (fun cl => forall d1 d2 c, 
                      match cl with
                        | Cl ρ _ => map (shift_whnf d1 c) (map (shift_whnf d2 c) ρ) = map (shift_whnf (d1 + d2) c) ρ
                      end)
          (fun ρ => forall d1 d2 c0, map (shift_whnf d1 c0) (map (shift_whnf d2 c0) ρ) = map (shift_whnf (d1 + d2) c0) ρ)
        ); intros.
  - simpl. easy.
  - simpl. easy.
  - simpl. destruct B.
    rewrite H. simpl. rewrite H0. easy.
  - simpl. destruct B.
    rewrite H, H0. easy.
  - simpl. destruct cl. rewrite <- H.
    simpl. easy.
  - simpl. rewrite H, H0, H1, H2. easy.
  - simpl. easy.
  - simpl. rewrite H. easy.
  - simpl. rewrite H. easy.
  - simpl. rewrite H, H0. easy.
  - simpl. rewrite H. easy.
  - simpl. rewrite H, H0, H1, H2. easy.
  - simpl.
    case_eq( c <=? i); intros.
    assert(c <= i + d2).
    { apply Nat.leb_le in H. lia. }
    apply Nat.leb_le in H0. rewrite H0.
    assert((i + d2 + d1) = (i + (d1 + d2))).
    { lia. } 
    rewrite H1. easy.
    rewrite H. easy.
  - simpl. rewrite H, H0. easy.
  - simpl. rewrite H. easy.
  - simpl. rewrite H. easy.
  - simpl. rewrite H, H0, H1, H2. easy.
  - simpl. rewrite H, H0, H1, H2, H3, H4. easy.
  - simpl. easy.
  - simpl. rewrite H0, H. easy.
  - simpl. rewrite H. easy.
(*     induction H; intros.
    + simpl. easy.
    + simpl. rewrite H, IHForall. easy. *)
Qed.
  