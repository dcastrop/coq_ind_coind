From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
(* Import Prenex Implicits. *)

Section FixGen.
  Context
    (L : Type)
    (F : Type -> Type)
    (OCC : forall (X : Type), X -> F X -> Prop)
    (fmap : forall (X Y : Type) p, (forall (x : X), OCC X x p -> Y) -> F Y)
  .
  Arguments OCC [X] x f_x.
  Arguments fmap [X Y] [p] f.

  Definition unlabel A (x : {p : F L & forall t (o : OCC t p), A}) : F A :=
    fmap (projT2 x).

  CoInductive GFix : Type :=
  | GFix_in (p : F L) : (forall (t : L), OCC t p -> GFix) -> GFix.
  Notation "[ 'G_IN' f | x ]"
    := (GFix_in (fun y (_ : OCC y x) => f y)) (at level 0).

  Definition gfix_unfold (x : GFix) : GFix :=
    match x with
    | GFix_in f => GFix_in f
    end.

  Lemma gfix_unfold_id (x : GFix) : x = gfix_unfold x.
  Proof with eauto. destruct x... Qed.

  (* Could generalize to [GFix T -> GFix T' -> Prop], but would require an
   * extra relation to "zip" elements of [F]
   *)
  Definition GFix_EQ_ (r : GFix -> GFix -> Prop) (g1 g2 : GFix) : Prop :=
    match g1, g2 with
    | @GFix_in p1 f1, @GFix_in p2 f2
      => p1 = p2 /\ (forall t o1 o2, r (f1 t o1) (f2 t o2))
    end.
  Lemma GFix_EQ_mon : monotone2 GFix_EQ_.
  Proof. intros [p1 f1] [p2 f2] r r' [E1 H1] F1; simpl; eauto. Qed.
  Hint Resolve GFix_EQ_mon.
  Definition G_EQ l r := paco2 GFix_EQ_ bot2 l r.

  Definition gFix_out (x : GFix) : F GFix :=
    match x with
    | GFix_in f => fmap f
    end.

  Definition ana (h : L -> F L) : L -> GFix
    := cofix f x := [G_IN f | h x].

  Lemma ana_unfold (h : L -> F L) :
    forall x, ana h x = [G_IN ana h | h x].
  Proof. intros x; rewrite (gfix_unfold_id (ana h x)); eauto. Qed.


  Inductive LFix : Type :=
  | LFix_in (p : F L) : (forall (t : L), OCC t p -> LFix) -> LFix.
  Notation "[ 'L_FMAP' f | x ]"
    := (match x with
        | LFix_in k => fmap (fun n e => f (k n e))
        end) (at level 0).

  Fixpoint LFix_EQ (p1 p2: LFix) : Prop :=
    match p1, p2 with
    | @LFix_in p1 f1, @LFix_in p2 f2 =>
      p1 = p2 /\ (forall t o1 o2, LFix_EQ (f1 t o1) (f2 t o2))
    end.

  Definition lFix_out (x : LFix) : F LFix :=
    match x with
    | LFix_in f => fmap f
    end.

  Definition cata A (h : F A -> A) : LFix -> A
    := fix f x :=
         match x with
         | LFix_in k => h (fmap (fun n e => f (k n e)))
         end.

  Inductive Finite : GFix -> Prop :=
  | Fin_fold (p : F L) (f : forall t, OCC t p -> GFix) :
      (forall s (occ : OCC s p), Finite (f s occ)) -> Finite (GFix_in f).

  Lemma Fin_inv1 p0 p (f : forall t, OCC t p -> GFix) :
    Finite p0 -> p0 = GFix_in f -> forall s (occ : OCC s p), Finite (f s occ).
  Proof with eauto. intros [p1 f0 H] E; inversion E... Defined.

  Fixpoint fromGFix (p : GFix) (F : Finite p) {struct F} : LFix
    := match p as p0 return p = p0 -> LFix with
       | GFix_in f =>
         fun PF => LFix_in (fun n a => fromGFix (Fin_inv1 F PF a))
       end eq_refl.

  Definition fcata A (g : F A -> A) : forall (p : GFix), Finite p -> A
    := fix f p FIN {struct FIN} :=
         g (match p as p0 return p = p0 -> F A with
           | GFix_in k =>
             fun PF =>
               fmap (fun n a => f (k n a) (Fin_inv1 FIN PF a))
           end eq_refl).

  Lemma Fin_inv2 (g : L -> F L) (x : L) (p : F L) :
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
  Arguments Fin_inv2 [g] [x] p F0 [s] occ.

  Definition fana (h : L -> F L) : forall x, Finite (ana h x) -> LFix
    := fix f x F := LFix_in (fun x occ => f x (Fin_inv2 (h x) F occ)).

  Definition thylo B (g : F B -> B) (h : L -> F L)
    : forall (x : L) (F : Finite (ana h x)), B
    := fix f x F := g (fmap (fun n occ => f n (Fin_inv2 (h x) F occ))).

  Definition fhylo B
             (g : F B -> B)
             (h : L -> F L)
             (FIN : forall x, Finite (ana h x))
    : L -> B := fun x => thylo g (FIN x).

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

  Definition citree S A := GFix S (@treeOcc A).

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

  Definition app A : LFix A _ -> list nat := cata (@pmap nat) p_merge.
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
