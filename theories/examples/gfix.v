Require Import Eqdep_dec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.
  Definition dec X := forall (x y : X), {x = y} + {x <> y}.

  Context
    (F : Type -> Type)
    (OCC : forall (X : Type), X -> F X -> Prop)
    (fmap : forall (X Y : Type) p, (forall (x : X), OCC X x p -> Y) -> F Y)
    (* (f_dec_eq : forall S, dec S -> dec (F S)) *)
  .
  Arguments OCC [X] x f_x.
  Arguments fmap [X Y] [p] f.

  CoInductive GFix T : Type :=
  | GFix_in (p : F T) : (forall (t : T), OCC t p -> GFix T) -> GFix T.
  Notation "[ 'G_IN' f | x ]"
    := (GFix_in (fun y (_ : OCC y x) => f y)) (at level 0).

  Definition gFix_out T (x : GFix T) : F (GFix T) :=
    match x with
    | GFix_in f => fmap f
    end.

  Definition ana A (h : A -> F A) : A -> GFix A
    := cofix f x := [G_IN f | h x].

  Definition gfix_unfold A (x : GFix A) : GFix A :=
    match x with
    | GFix_in f => GFix_in f
    end.

  Lemma gfix_unfold_id A (x : GFix A) : x = gfix_unfold x.
  Proof with eauto. destruct x... Qed.

  (* An alternative is having a single constructor [LFix_in S : P S -> (S ->
     LFix P) -> LFix P], but this requires the use of axioms, or restricting [S]
     to have decidable equality *)
  (* Inductive LFix S (P : Type -> Type) : Type := *)
  (* | LFix_in1 : P False -> LFix S P *)
  (* | LFix_in2 : P S -> (S -> LFix S P) -> LFix S P. *)

  Inductive LFix T : Type :=
  | LFix_in (p : F T) : (forall (t : T), OCC t p -> LFix T) -> LFix T.
  Notation "[ 'L_FMAP' f | x ]"
    := (match x with
        | LFix_in k => fmap (fun n e => f (k n e))
        end) (at level 0).

  Definition lFix_out S (x : LFix S) : F (LFix S) :=
    match x with
    | LFix_in f => fmap f
    end.

  Definition cata A B (h : F B -> B) : LFix A -> B
    := fix f x :=
         match x with
         | LFix_in k => h (fmap (fun n e => f (k n e)))
         end.

  Inductive Finite S : GFix S -> Prop :=
  | Fin_fold (p : F S) (f : forall t, OCC t p -> GFix S) :
      (forall s (occ : OCC s p), Finite (f s occ)) -> Finite (GFix_in f).

  Lemma Fin_inv1 S (p0 : GFix S) (p : F S) (f : forall t, OCC t p -> GFix S) :
    Finite p0 -> p0 = GFix_in f -> forall s (occ : OCC s p), Finite (f s occ).
  Proof with eauto. intros [p1 f0 H] E; inversion E... Defined.

  Fixpoint fromGFix S (p : GFix S) (F : Finite p) {struct F} : LFix S
    := match p as p0 return p = p0 -> LFix S with
       | GFix_in f =>
         fun PF => LFix_in (fun n a => fromGFix (Fin_inv1 F PF a))
       end eq_refl.

  Definition fcata A B (g : F B -> B) : forall (p : GFix A), Finite p -> B
    := fix f p FIN {struct FIN} :=
         g (match p as p0 return p = p0 -> F B with
           | GFix_in k =>
             fun PF =>
               fmap (fun n a => f (k n a) (Fin_inv1 FIN PF a))
           end eq_refl).

  Lemma Fin_inv2 S (g : S -> F S) (x : S) (p : F S) :
    Finite (ana g x) -> forall s (occ : OCC s (g x)), Finite (ana g s).
  Proof.
    intros FIN s r.
    rewrite gfix_unfold_id in FIN; simpl in FIN.
    generalize (Fin_inv1 FIN eq_refl).
    clear FIN; intros FIN; specialize (FIN s r).
    rewrite gfix_unfold_id in FIN; simpl in FIN.
    rewrite gfix_unfold_id; simpl.
    trivial.
  Defined.

  Definition fana A (h : A -> F A) : forall (x : A), Finite (ana h x) -> LFix A
    := fix f x F := LFix_in (fun x occ => f x (Fin_inv2 (h x) F occ)).

  Definition thylo A B (g : F B -> B) (h : A -> F A)
    : forall (x : A) (F : Finite (ana h x)), B
    := fix f x F := g (fmap (fun n occ => f n (Fin_inv2 (h x) F occ))).

  Definition fhylo A B
             (g : F B -> B)
             (h : A -> F A)
             (FIN : forall x, Finite (ana h x))
    : A -> B := fun x => thylo g (FIN x).

  (* Goal forall A B P (R : Occ P) (eq : p_dec_eq A P) (map : monotone R) *)
  (*             (g : P B -> B) (h : A -> P A) (x : A) (F : Finite (ana R h x)), *)
  (*     fhylo eq map g F = cata map g (fana eq F). *)

End FixGen.

Require Import List.
Import ListNotations.

Section ExampleInfTree.
  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Definition treeOcc A X (x : X) (t : treeP A X) : Prop :=
    match t with
    | C _ l => In x l
    end.

  Definition citree A S := GFix (@treeOcc A) S.

  Fixpoint downfrom n :=
    match n with
    | 0 => []
    | S m => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat :=
    ana (@treeOcc nat) (fun n => (C n (downfrom n))) n.
End ExampleInfTree.

Section QSort.
  (* Functor *)
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  (* 'Position' but in Prop rather than Set or Type *)
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

  Lemma list_filter_length A (pred : A -> bool) (l : list A) :
    length (filter pred l) <= length l.
  Proof with eauto.
    induction l...
    simpl; case (pred a); simpl.
    - apply le_n_S...
    - apply le_S in IHl...
  Qed.
  Hint Resolve list_filter_length.

  Import PeanoNat.Nat.
  Lemma p_split_terminates (l : list nat) : Finite (ana (@P_occ nat) p_split l).
  Proof.
    generalize (leb_refl (length l)); generalize (length l) at -1.
    intros n LE; revert l LE.
    induction n; intros []; simpl; intro EQ; try (discriminate EQ); eauto;
      rewrite (gfix_unfold_id (ana _ _ _)); constructor; intros s F; destruct F.
    - subst; apply IHn; clear IHn.
      apply leb_le in EQ; apply leb_le, (le_trans _ (length l) n); eauto.
    - subst; apply IHn; clear IHn.
      apply leb_le in EQ; apply leb_le, (le_trans _ (length l) n); eauto.
  Qed.

  Definition app A : LFix _ A -> list nat := cata (@pmap nat) p_merge.
  Definition spl1 (x : list nat) := fana (p_split_terminates x).
  Definition spl2 := ana (@P_occ nat) p_split.

  Definition msort : list nat -> list nat
    := fhylo (@pmap nat) p_merge p_split_terminates.
End QSort.

(* From Coq Require Extraction ExtrHaskellBasic ExtrHaskellNatInteger. *)
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Inline pmap.
Extraction Inline ana.
Extraction Inline fana.
Extraction Inline cata.
Extraction Inline fcata.
Extraction Inline fhylo.
Extraction Inline thylo.
Extraction Inline p_merge.
Extraction Inline p_split.
Print Extraction Inline.
Extraction "msort" msort spl1 spl2 app.
