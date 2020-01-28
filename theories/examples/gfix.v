From mathcomp.ssreflect Require Import ssreflect ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.

  CoInductive PCFix (S : Type) (P : Type -> Type) : Type :=
  | GFix_fold (S' : Type) : P S' -> (S' -> S + PCFix S P) -> PCFix S P.
  Definition GFix := PCFix False.

  Inductive GFin S P : S + PCFix S P -> Prop :=
  | Fin_fold (S' : Type) (p : P S') (f : S' -> S + PCFix S P) :
      (forall (s : S'), GFin (f s)) ->
      GFin (inr (GFix_fold p f)).
  Definition Fin P : GFix P -> Prop := fun x => GFin (inr x).

  Inductive PIFix (S : Type) (P : Type -> Type) : Type :=
  | LFix_fold (S' : Type) : P S' -> (S' -> S + PIFix S P) -> PIFix S P.
  Definition LFix := PCFix False.

  (* Fixpoint fromGFix S P (p : PCFix S P) (pf : GFin (inr p)) {struct pf} : PIFix S P *)
  (*   := match p as p0 return p = p0 -> PIFix S P with *)
  (*      | GFix_fold _ p f => _ *)
  (*      end eq_refl. *)

  Definition genF A B (f : A -> B) (x : A) : False + B := inr (f x).

  Definition unF A B (f : A -> False + B) (x : A) : B :=
    match f x with
    | inl f => False_rect B f
    | inr x => x
    end.

  Definition monotone P := forall {x y : Type}, (x -> y) -> P x -> P y.

  Definition gfix_unfold P (map : monotone P) (x : GFix P)
    : P (GFix P)%type :=
    match x with
    | GFix_fold _ p f => map _ (GFix P)%type (unF f) p
    end.

  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Definition citree A := GFix (treeP A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  CoFixpoint ana A (P : Type -> Type) (f : A -> P A) (x : A) : GFix P :=
    GFix_fold (f x) (genF (fun y => ana f y)).

  Definition exn (n : nat) : citree nat := ana (fun n => C n (downfrom n))n.
End FixGen.
