# Nested Induction/Coinduction in Coq

This repository contains a way to trick Coq into having some kind of nested induction/coinduction, by nesting "finite coinductive types" that are isomorphic to an inductive type.

## The problem

We cannot build this in Coq:

```coq
Module Problem.
  CoInductive itree A := C : A -> seq (itree A) -> itree A.

  Fail CoFixpoint example (n : nat) : itree nat :=
    C n ((fix build_branches m : seq (itree nat) :=
            match m with
            | 0 => [::]
            | t.+1 => example t :: build_branches t
            end) n).
End Problem.
```

The nested recursive call is not in guarded form:
```coq
The command has indeed failed with message:
Recursive definition of example is ill-formed.
In environment
example : nat -> itree nat
n : nat
Sub-expression "(fix build_branches (m : nat) : seq (itree nat) :=
                   match m with
                   | 0 => [::]
                   | t.+1 => example t :: build_branches t
                   end) n" not in guarded form (should be a constructor, an abstraction, a match, a cofix or a recursive
call).
Recursive definition is:
"fun n : nat =>
 C n
   ((fix build_branches (m : nat) : seq (itree nat) := match m with
                                                       | 0 => [::]
                                                       | t.+1 => example t :: build_branches t
                                                       end) n)".
```

## A Solution

Possible solutions include using a non-inductive type instead of `seq`. This trick uses "finite coinductive types":

```coq
  CoInductive vseq : nat -> Type :=
  | Nil   : vseq 0
  | Cns n : A -> vseq n -> vseq n.+1.
  
  CoInductive itree A := C n : A -> vseq (itree A) n -> itree A.

  CoFixpoint example (n : nat) : itree nat :=
    C n ((cofix build_branches m : vseq (itree nat) m :=
            match m with
            | 0 => Nil _
            | t.+1 => Cns (example t) (build_branches t)
            end) n).
```

I think that `cofix build_branches ...` must terminate: every corecursive call must be guarded. But by the type index, this means that it must be on a smaller natural number. There is a proof that `x : seq A` and `vseq A` are isomorphic:

```coq
  Lemma iso1 l : vseq_to_seq (seq_to_vseq l) = l.

  Lemma iso2 n (v : vseq n) (p : size (vseq_to_seq v) = n) :
    cast_vseq p (seq_to_vseq (vseq_to_seq v)) = v.
```
