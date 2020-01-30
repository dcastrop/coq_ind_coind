From mathcomp.ssreflect Require Import all_ssreflect.

Require Import Eqdep_dec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.

  Definition Occ (P : Type -> Type) := forall (X : Type), X -> P X -> Prop.

  CoInductive GFix T (P : Type -> Type) (R : Occ P) : Type :=
  | GFix_in (p : P T) : (forall (t : T), R T t p -> GFix T R) -> GFix T R.
  Arguments GFix_in [T] [P] [R] p f.

  Definition monotone P (R : Occ P)
    := forall (X Y : Type) p, (forall x, R X x p -> Y) -> P Y.

  Definition fmap P R (rmap : monotone R) (X Y : Type)
    : (X -> Y) -> P X -> P Y
    := fun f x => rmap _ _ x (fun x _ => f x).

  Definition gFix_out S P (R : Occ P) (map : monotone R)
    : GFix S R -> P (GFix S R) :=
    fun x => match x with
             | GFix_in p f => map _ _ p f
             end.

  Definition ana A P (R : Occ P)
    : (A -> P A) -> A -> GFix A R
    := fun h => cofix f x := GFix_in (h x) (fun x _ => f x).

  Definition gfix_unfold A P (R : Occ P) (x : GFix A R) : GFix A R :=
    match x with
    | GFix_in p f => GFix_in p f
    end.

  Lemma gfix_unfold_id A P (R : Occ P) (x : GFix A R) : x = gfix_unfold x.
  Proof. by case: x. Qed.

  (* An alternative is having a single constructor [LFix_in S : P S -> (S ->
     LFix P) -> LFix P], but this requires the use of axioms, or restricting [S]
     to have decidable equality *)
  (* Inductive LFix S (P : Type -> Type) : Type := *)
  (* | LFix_in1 : P False -> LFix S P *)
  (* | LFix_in2 : P S -> (S -> LFix S P) -> LFix S P. *)

  Inductive LFix T (P : Type -> Type) (R : Occ P) : Type :=
  | LFix_in (p : P T) : (forall (t : T), R T t p -> LFix T R) -> LFix T R.
  Arguments LFix_in [T] [P] [R] p f.

  Definition lFix_out S P (R : Occ P) (map : monotone R)
    : LFix S R -> P (LFix S R) :=
    fun x => match x with
             | LFix_in p f => map _ _ p f
             end.

  Definition cata A B P (R : Occ P) (map : monotone R)
    : (P B -> B) -> LFix A R -> B
    := fun g => fix f x :=
         match x with
         | LFix_in p k => g (map _ _ p (fun n e => f (k n e)))
         end.

  Inductive Finite S P (R : Occ P) : GFix S R -> Prop :=
  | Fin_fold (p : P S) (f : forall (t : S), R S t p -> GFix S R) :
      (forall s (occ : R S s p), Finite (f s occ)) ->
      Finite (GFix_in p f).

  Definition dec_eq (S : Type) P := forall (x y : P S), decidable (x = y).

  Lemma Finite_inv1 S P (R : Occ P) (p0 : GFix S R) (dec : dec_eq S P)
        (p : P S) (f : forall (t : S), R S t p -> GFix S R) :
    Finite p0 ->
    p0 = GFix_in p f ->
    forall s (occ : R S s p), Finite (f s occ).
  Proof.
    case=> p1 f0 H [E]; move: E f0 H=>->f0 H {p1}.
    set F := fun p1 : P S => _.
    by move => /(inj_pair2_eq_dec (P S) dec F p f0 f)<-.
  Defined.

  Lemma Finite_inv2 S P (R : Occ P) (dec : dec_eq S P)
        (g : S -> P S) (x : S) (p : P S) :
    Finite (ana R g x) ->
    forall s (occ : R S s (g x)), Finite (ana R g s).
  Proof.
    move=> F s r; move: F.
    do 2 rewrite (gfix_unfold_id (ana _ _ _)) /=.
    move=> E; move: (Finite_inv1 dec E erefl) => /(_ s r)-H.
    move: H.
    by rewrite (gfix_unfold_id ((cofix f x0 := GFix_in _ _) s)) /=.
  Defined.

  Fixpoint fromGFix S P (R : Occ P) (eq : dec_eq S P)
           (p : GFix S R) (F : Finite p) {struct F} : LFix S R
    := match p as p0 return p = p0 -> LFix S R with
       | GFix_in p f =>
         fun PF => LFix_in p (fun n a => fromGFix eq (Finite_inv1 eq F PF a))
       end erefl.

  Fixpoint fcata A B P (R : Occ P) (eq : dec_eq A P) (map : monotone R)
           (f : P B -> B) (p : GFix A R) (F : Finite p) {struct F} : B
    := match p as p0 return p = p0 -> B with
       | GFix_in p k =>
         fun PF =>
           f (map _ _ p
                  (fun n a => fcata eq map f (Finite_inv1 eq F PF a)))
       end erefl.

  Definition fhylo A B P (R : Occ P) (eq : dec_eq A P) (map : monotone R)
           (g : P B -> B) (h : A -> P A)
    : forall (x : A) (F : Finite (ana R h x)), B
    := fix f (x : A) (F : Finite (ana R h x)) {struct F} :=
         g (map _ _ (h x) (fun n Occ => f n (Finite_inv2 eq (h x) F Occ))).
End FixGen.

Section ExampleInfTree.
  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Inductive treeOcc A : forall (X : Type), X -> treeP A X -> Prop :=
  | Occ_in a X (x : X) (l : list X) : List.In x l -> treeOcc x (C a l).

  Definition citree A S := GFix S (@treeOcc A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat :=
    ana (@treeOcc nat) (fun n => (C n (downfrom n))) n.
End ExampleInfTree.

Section QSort.
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  Lemma deq : dec_eq (seq nat) (P nat).
    move=> x y.
    rewrite /decidable.
    case: x; case: y=>//; try (by right); try (by left).
    move=> PIVOT LEFT RIGHT PIVOT0 LEFT0 RIGHT0.
    case: (PIVOT0 =P PIVOT)=>[->|F]; last by right => [[/F]].
    case: (LEFT0 =P LEFT)=>[->|F]; last by right => [[/F]].
    case: (RIGHT0 =P RIGHT)=>[->|F]; last by right => [[/F]].
    by left.
  Defined.

  Definition P_occ A X : X -> P A X -> Prop :=
    fun x p => match p with
               | Empty => False
               | Div _ l r => x = l \/ x = r
               end.

  Definition pmap A : monotone (@P_occ A) :=
    fun X Y (x : P A X) f =>
      match x as x0 return x = x0 -> P A Y with
      | Empty => fun _ => Empty _ _
      | Div h l r =>
        fun PF =>
          match PF in _ = x return P_occ l x -> P_occ r x -> P A Y with
          | erefl => fun pl pr => Div h (f l pl) (f r pr)
          end (or_introl erefl) (or_intror erefl)
      end erefl.

  Definition p_split (l : seq nat) : P nat (seq nat) :=
    match l with
    | [::] => Empty _ _
    | h :: t => Div h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.

  Definition p_merge (t : P nat (seq nat)) : seq nat :=
    match t with
    | Empty => [::]
    | Div h l r => l ++ h :: r
    end.

  Lemma p_split_terminates (l : seq nat) : Finite (ana (@P_occ nat) p_split l).
  Proof.
    move: {-1} (size l) (leqnn (size l)) => n LE.
    elim: n=>[|n Ih] in l LE *; case: l LE=>[|h t]//= LE;
      rewrite (gfix_unfold_id (ana _ _ _))//; constructor => s []->; apply/Ih.
    + by rewrite size_filter; move: (leq_ltn_trans (count_size (leq^~ h) t) LE).
    + by rewrite size_filter; move: (leq_ltn_trans (count_size [eta leq h.+1] t) LE).
  Qed.

  Definition msort (x : seq nat) : seq nat
    := fhylo deq (@pmap nat) p_merge (p_split_terminates x).
End QSort.
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlIntConv ExtrOcamlNatInt.
Extraction Inline pmap.
Extraction Inline fhylo.
Extraction Inline p_merge.
Extraction Inline p_split.
Set Extraction Optimize.
Recursive Extraction msort pmap.
