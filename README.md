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

This trick uses "finite coinductive types", instead of nesting an inductive type. These "finite coinductive types" should be isomorphic to an inductive type.

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

### `fseq` is isomorphic to a list

There is a proof that `seq A` and `fseq A` are isomorphic:

```coq
  Definition seq_to_fseq (l : seq) : fseq := ...
  Definition fseq_to_seq (l : fseq) : seq := ...
  
  Lemma f_iso1 l : fseq_to_seq (seq_to_fseq l) = l.
  Lemma f_iso2 l : seq_to_fseq (fseq_to_seq l) = l.
```

**Constructors**: 
```coq
  Definition f_nil : fseq := existT _ _ Nil.
  Definition f_cons h t := existT _ _ (Cns h (projT2 t)).
```
**Induction principle**:
```coq
fseq_ind : forall (A : Type) (P : fseq A -> Type),
    P (f_nil A) ->
    (forall (h : A) (t : fseq A), P t -> P (f_cons h t)) ->
    forall l : fseq A, P l
```


### Is any correcursive function producing `vseq A m` terminating?

Informally, any CoFixpoint producing `vseq A m` must terminate after exactly `m` steps because every corecursive call must be guarded. Since the type index gets smaller after every correcursive call, the only constructor that we could produce after `m` steps is `Nil`. 
