From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import fcoind.cseq.

Section Nested.
  CoInductive itree A := C : A -> fseq (itree A) -> itree A.

  Definition build (f : nat -> itree nat) : forall m, vseq (itree nat) m :=
    cofix bb m := if m is t.+1 then Cns (f m) (bb t) else Nil _.

  CoFixpoint example (n : nat) : itree nat :=
    C n (eS (build example n)).
End Nested.
