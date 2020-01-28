From mathcomp.ssreflect Require Import ssreflect ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.
  CoInductive GFix (S : Set) (P : Set -> Set) : Set :=
  | GFix_fold : P S -> (S -> GFix S P) -> GFix S P.

  Definition Gunfold
             (S : Set)
             (P : Set -> Set)
             (map : forall (x : Set) (y : Set), (x -> y) -> P x -> P y)
             (x : GFix S P) : P (GFix S P) :=
    match x with
    | GFix_fold p f => map _ (GFix S P) f p
    end.

  Inductive treeP (A : Set) (t : Set) : Set :=
  | CS : A -> list t -> treeP A t.

  Definition citree A := GFix nat (treeP A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  CoFixpoint exn (n : nat) : citree nat :=
    GFix_fold (CS n (downfrom n)) (fun m => exn m).
End FixGen.
