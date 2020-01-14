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
            | t.+1 => example m :: build_branches t
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
                   | t.+1 => example m :: build_branches t
                   end) n" not in guarded form (should be a constructor, an abstraction, a match, a cofix or a recursive
call).
Recursive definition is:
"fun n : nat =>
 C n
   ((fix build_branches (m : nat) : seq (itree nat) := match m with
                                                       | 0 => [::]
                                                       | t.+1 => example m :: build_branches t
                                                       end) n)".
```

## A Solution

Possible solutions include using a non-inductive type instead of `seq`. This trick uses "finite coinductive types":

```coq
  CoInductive vseq : nat -> Type :=
  | Nil   : vseq 0
  | Cns n : A -> vseq n -> vseq n.+1.
  
  Definition fseq := {n & vseq n}.
  
  CoInductive itree A := C : A -> fseq (itree A) -> itree A.
  
  CoFixpoint example (n : nat) : itree nat :=
    C n (existT _ _ ((cofix build_branches m : vseq (itree nat) m :=
                        match m with
                        | 0 => Nil _
                        | t.+1 => Cns (example m) (build_branches t)
                        end) n)).
```

Note that `cofix build_branches ...` must terminate: every corecursive call must be guarded. But by the type index, this means that `m` must be on a smaller natural number. IWould it be interesting to prove that any correcursive function producing `vseq A m` must terminate? There is already a proof that `seq A` and `fseq A` are isomorphic:

```coq
  Definition seq_to_fseq (l : seq) : fseq := ...
  Definition fseq_to_seq (l : fseq) : seq := ...
  
  Lemma f_iso1 l : fseq_to_seq (seq_to_fseq l) = l.
  Lemma f_iso2 l : seq_to_fseq (fseq_to_seq l) = l.
```
