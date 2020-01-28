From mathcomp.ssreflect Require Import ssreflect ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.

  CoInductive PCFix (S : Type) (P : Type -> Type) : Type :=
  | GFix_fold (S' : Type) : P S' -> (S' -> S + PCFix S P) -> PCFix S P.

  Definition monotone P := forall {x y : Type}, (x -> y) -> P x -> P y.

  Definition GFix := PCFix False.

  Definition unF A B (f : A -> False + B) (x : A) : B :=
    match f x with
    | inl f => False_rect B f
    | inr x => x
    end.

  Definition genF A B (f : A -> B) (x : A) : False + B := inr (f x).

  Definition gfix_unfold P (map : monotone P) (x : GFix P)
    : P (GFix P)%type :=
    match x with
    | GFix_fold _ p f => map _ (GFix P)%type (unF f) p
    end.

  Inductive treeP (A : Type) (t : Type) : Type :=
  | CS : A -> list t -> treeP A t.

  Definition citree A := GFix (treeP A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  CoFixpoint exn (n : nat) : citree nat :=
    GFix_fold (CS n (downfrom n)) (genF (fun m => exn m)).

End FixGen.
