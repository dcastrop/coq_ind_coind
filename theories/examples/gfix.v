From mathcomp.ssreflect Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.
  CoInductive GFix T (P : Type -> Type) : Type :=
  | GFix_in : P T -> (T -> GFix T P) -> GFix T P.

  Definition monotone P := forall X Y, (X -> Y) -> P X -> P Y.

  Definition enumerable P Y := forall X, P X -> P Y * seq (Y * X).

  Definition gFix_out S P (map : monotone P) (x : GFix S P) : P (GFix S P) :=
    match x with
    | GFix_in p f => map _ _ f p
    end.

  CoFixpoint ana A (P : Type -> Type) (f : A -> P A) (x : A) : GFix A P :=
    GFix_in (f x) (ana f).

  Definition gfix_unfold A P (x : GFix A P) : GFix A P :=
    match x with
    | GFix_in p f => GFix_in p f
    end.

  Lemma gfix_unfold_id A P (x : GFix A P) : x = gfix_unfold x.
  Proof. by case: x. Qed.

  Inductive LFix S (P : Type -> Type) : Type :=
  | LFix_in : P S -> (S -> LFix S P) -> LFix S P.

  Definition lFix_out S P (map : monotone P) (x : LFix S P) : P (LFix S P) :=
    match x with
    | LFix_in p f => map _ _ f p
    end.

  Fixpoint cata A B P (map : monotone P) (f : P B -> B) (x : LFix A P) : B :=
    match x with
    | LFix_in p k => f (map _ _ (fun n => cata map f (k n)) p)
    end.

  (* I need to state "if p contains s, then ..." *)
  Inductive Finite S P : GFix S P -> Prop :=
  | Fin_fold (p : P S) (f : S -> GFix S P) :
      (forall (s : S), Finite (f s)) -> Finite (GFix_in p f).

  Lemma Finite_inv1 S P (p0 : GFix S P) (p : P S) (f : S -> GFix S P) :
    Finite p0 -> p0 = GFix_in p f -> forall s, Finite (f s).
  Proof. by case=> p1 f1 H1 [_ <-]. Defined.

  Lemma Finite_inv2 S P (f : S -> P S) (x : S) :
    Finite (ana f x) -> forall s, Finite (ana f s).
  Proof.
    rewrite (gfix_unfold_id (ana f x)) /= -/ana.
    set p0 := GFix_in (f x) (ana f).
    have EQ: p0 = GFix_in (f x) (ana f) by [].
    by move=> Fin; move: Fin EQ; apply/Finite_inv1.
  Defined.

  Fixpoint fromGFix S P (p : GFix S P) (F : Finite p) {struct F} : LFix S P
    := match p as p0 return p = p0 -> LFix S P with
       | GFix_in p f =>
         fun Pf => LFix_in p (fun n => fromGFix (Finite_inv1 F Pf n))
       end erefl.

  Fixpoint fcata A B P (map : monotone P) (f : P B -> B)
           (x : GFix A P) (pf : Finite x) {struct pf} : B :=
    match x as x0 return x = x0 -> B with
    | GFix_in p k =>
      fun eq =>
        f (map _ _ (fun n => fcata map f (Finite_inv1 pf eq n)) p)
    end erefl.

  Definition fhylo A B P (map : monotone P) (g : P B -> B) (h : A -> P A)
    : forall (x : A), Finite (ana h x) -> B :=
    fix f (x : A) (pf : Finite (ana h x)) {struct pf} :=
      g (map _ _ (fun s => f s (Finite_inv2 pf s)) (h x)).

  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Definition citree S A := GFix S (treeP A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat := ana (fun n => C n (downfrom n)) n.
End FixGen.

Section QSort.
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  Definition p_split (l : seq nat) : P nat (seq nat) :=
    match l with
    | [::] => Empty _ _
    | h :: t => Div h (filter (fun x => x <= h) t) (filter (fun x => x > h) t)
    end.

  Definition p_merge (t : P nat (seq nat)) : seq nat :=
    match t with
    | Empty => [::]
    | Div h l r => l ++ h :: r
    end.

  Lemma p_split_terminates : forall l, Finite (ana p_split l).
  Proof.
    move=>l; move: {-1} (size l) (leqnn (size l)) => n LE.
    rewrite (gfix_unfold_id (ana p_split l)).
    elim: n=>[|n Ih] in l LE *; case: l LE=>[|h t]//=; rewrite -/ana.
End MSort.
