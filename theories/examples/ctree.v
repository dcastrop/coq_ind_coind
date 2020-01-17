From mathcomp.ssreflect Require Import ssreflect ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import fcoind.ctree.

Section ExampleTree.

  CoInductive ttree := TC : nat -> ftree ttree -> ttree.

  Fixpoint nshape (n : nat) : shape :=
    match n with
    | 0 => SL
    | n.+1 => SN (nshape n) (nshape n)
    end.

  Definition tbuild (f : nat -> ttree) : forall m, vtree ttree (nshape m) :=
    cofix bb m :=
      match m with
      | 0 => CL _
      | t.+1 =>
        match maxnn t with
        | erefl => CN (f m) (bb t) (bb t)
        end
      end.

  CoFixpoint texample (n : nat) : ttree :=
    TC n (eS (tbuild texample n)).
End ExampleTree.
