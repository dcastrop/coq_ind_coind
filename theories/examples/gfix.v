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
  Proof with eauto.
    destruct x...
  Qed.

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

  Definition p_dec_eq (S : Type) P := forall (x y : P S), {x = y} + {x <> y}.

  Lemma Finite_inv1 S P (R : Occ P) (p0 : GFix S R) (dec : p_dec_eq S P)
        (p : P S) (f : forall (t : S), R S t p -> GFix S R) :
    Finite p0 ->
    p0 = GFix_in p f ->
    forall s (occ : R S s p), Finite (f s occ).
  Proof with eauto. intros [p1 f0 H] E; inversion E... Defined.

  Fixpoint fromGFix S P (R : Occ P) (eq : p_dec_eq S P)
           (p : GFix S R) (F : Finite p) {struct F} : LFix S R
    := match p as p0 return p = p0 -> LFix S R with
       | GFix_in p f =>
         fun PF => LFix_in p (fun n a => fromGFix eq (Finite_inv1 eq F PF a))
       end eq_refl.

  Fixpoint fcata A B P (R : Occ P) (eq : p_dec_eq A P) (map : monotone R)
           (f : P B -> B) (p : GFix A R) (F : Finite p) {struct F} : B
    := match p as p0 return p = p0 -> B with
       | GFix_in p k =>
         fun PF =>
           f (map _ _ p
                  (fun n a => fcata eq map f (Finite_inv1 eq F PF a)))
       end eq_refl.

  Lemma Finite_inv2 S P (R : Occ P) (dec : p_dec_eq S P)
        (g : S -> P S) (x : S) (p : P S) :
    Finite (ana R g x) ->
    forall s (occ : R S s (g x)), Finite (ana R g s).
  Proof.
    intros F s r.
    rewrite gfix_unfold_id in F; simpl in F.
    generalize (Finite_inv1 dec F eq_refl).
    clear F; intros F; specialize (F s r).
    rewrite gfix_unfold_id in F; simpl in F.
    rewrite gfix_unfold_id; simpl.
    trivial.
  Defined.

  Definition fana A P (R : Occ P) (eq : p_dec_eq A P)
    : forall (f : A -> P A) (x : A), Finite (ana R f x) -> LFix A R
    := fun h => fix f x F {struct F} :=
         LFix_in (h x) (fun x Occ => f x (Finite_inv2 eq (h x) F Occ)).

  Definition fhylo A B P (R : Occ P) (eq : p_dec_eq A P) (map : monotone R)
           (g : P B -> B) (h : A -> P A)
    : forall (x : A) (F : Finite (ana R h x)), B
    := fix f (x : A) (F : Finite (ana R h x)) {struct F} :=
         g (map _ _ (h x) (fun n Occ => f n (Finite_inv2 eq (h x) F Occ))).
End FixGen.

Require Import List.
Import ListNotations.

Section ExampleInfTree.
  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Inductive treeOcc A : forall (X : Type), X -> treeP A X -> Prop :=
  | Occ_in a X (x : X) (l : list X) : In x l -> treeOcc x (C a l).

  Definition citree A S := GFix S (@treeOcc A).

  Fixpoint downfrom n :=
    match n with
    | 0 => []
    | S m => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat :=
    ana (@treeOcc nat) (fun n => (C n (downfrom n))) n.
End ExampleInfTree.

Section QSort.
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  Lemma deq : p_dec_eq (list nat) (P nat).
    intros [] []; try (right; intro F; discriminate F); try (left; reflexivity).
    case (PeanoNat.Nat.eq_dec PIVOT0 PIVOT)=>[->|F];
        try (right; intros H; inversion H; subst; apply (F eq_refl)).
    case (List.list_eq_dec PeanoNat.Nat.eq_dec LEFT0 LEFT)=>[->|F];
        try (right; intros H; inversion H; subst; apply (F eq_refl)).
    case (List.list_eq_dec PeanoNat.Nat.eq_dec RIGHT0 RIGHT)=>[->|F];
        try (right; intros H; inversion H; subst; apply (F eq_refl)).
    left; trivial.
  Defined.

  Definition P_occ A X : X -> P A X -> Prop :=
    fun x p => match p with
               | Empty _ _ => False
               | Div _ l r => x = l \/ x = r
               end.

  Definition pmap A X Y (p : P A X) (f : forall x, P_occ x p -> Y) : P A Y :=
    match p as p0 return p = p0 -> P A Y with
    | Empty _ _ => fun _ => Empty _ _
    | Div h l r =>
      fun PF =>
        match PF in _ = x return P_occ l x -> P_occ r x -> P A Y with
        | eq_refl => fun pl pr => Div h (f l pl) (f r pr)
        end (or_introl eq_refl) (or_intror eq_refl)
    end eq_refl.

  Definition p_split (l : list nat) : P nat (list nat) :=
    match l with
    | [] => Empty _ _
    | h :: t =>
      Div h
          (filter (fun x => Nat.leb x h) t)
          (filter (fun x => negb (Nat.leb x h)) t)
    end.

  Definition p_merge (t : P nat (list nat)) : list nat :=
    match t with
    | Empty _ _  => []
    | Div h l r => l ++ h :: r
    end.

  Lemma p_split_terminates (l : list nat) : Finite (ana (@P_occ nat) p_split l).
  Proof.
    generalize (PeanoNat.Nat.leb_refl (length l)).
    generalize (length l) at -1.
    intros n LE; revert l LE.
    induction n; intros []; simpl; intro EQ; try (discriminate EQ); eauto;
      rewrite (gfix_unfold_id (ana _ _ _)); constructor; intros s F; destruct F.
    - subst; apply IHn; clear IHn.
      apply PeanoNat.Nat.leb_le in EQ.
      apply PeanoNat.Nat.leb_le.
      generalize (fun (x : nat) => Nat.leb x n0); intros P; clear n0.
      revert n EQ; induction l; auto; simpl; elim (P a); simpl; intros n LE.
      + destruct n; try (apply Le.le_n_0_eq in LE; discriminate LE).
        apply Le.le_n_S; apply Le.le_S_n in LE; auto.
      + apply Le.le_Sn_le in LE; apply IHl; auto.
    - subst; apply IHn; clear IHn.
      apply PeanoNat.Nat.leb_le in EQ.
      apply PeanoNat.Nat.leb_le.
      generalize (fun (x : nat) => negb (Nat.leb x n0)); intros P; clear n0.
      revert n EQ; induction l; auto; simpl; elim (P a); simpl; intros n LE.
      + destruct n; try (apply Le.le_n_0_eq in LE; discriminate LE).
        apply Le.le_n_S; apply Le.le_S_n in LE; auto.
      + apply Le.le_Sn_le in LE; apply IHl; auto.
  Qed.

  Definition spl (x : list nat) := fana deq (p_split_terminates x).

  Definition msort (x : list nat) : list nat
    := fhylo deq (@pmap nat) p_merge (p_split_terminates x).
End QSort.
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlIntConv ExtrOcamlNatInt.
Extraction Inline pmap.
Extraction Inline ana.
Extraction Inline fana.
Extraction Inline fcata.
Extraction Inline fhylo.
Extraction Inline p_merge.
Extraction Inline p_split.
Set Extraction Optimize.
Recursive Extraction msort.
