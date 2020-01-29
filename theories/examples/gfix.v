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
    GFix_in (f x) (fun y => ana f y).

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

  Inductive Finite S P : GFix S P -> Prop :=
  | Fin_fold (p : P S) (f : S -> GFix S P) :
      (forall (s : S), Finite (f s)) -> Finite (GFix_in p f).

  Lemma Finite_inv S P (p0 : GFix S P) (p : P S) (f : S -> GFix S P) :
    Finite p0 -> p0 = GFix_in p f -> forall s, Finite (f s).
  Proof. by case=> p1 f1 H1 [_ <-]. Defined.

  Fixpoint fromGFix S P (p : GFix S P) (F : Finite p) {struct F} : LFix S P
    := match p as p0 return p = p0 -> LFix S P with
       | GFix_in p f =>
         fun Pf => LFix_in p (fun n => fromGFix (Finite_inv F Pf n))
       end erefl.

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
