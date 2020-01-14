From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section CSeq.
  Context (A : Type).

  CoInductive vseq : nat -> Type :=
  | Nil   : vseq 0
  | Cns n : A -> vseq n -> vseq n.+1.

  Definition cast_vseq n m (p : n = m) : vseq n -> vseq m :=
    match p in _ = m return vseq n -> vseq m with
    | erefl => id
    end.

  Lemma succ_inj n m : n.+1 = m.+1 -> n = m.
  Proof. by move=>[]. Defined.

  Fixpoint vseq_to_seq n (x : vseq n) {struct n} : seq A :=
    match x in vseq m return m = n -> seq A with
    | Nil =>
      fun _ => [::]
    | Cns m h t =>
      match n return m.+1 = n -> seq A with
      | 0 =>
        fun pf =>
          match pf with end
      | n.+1 =>
        fun pf =>
          h :: vseq_to_seq (cast_vseq (succ_inj pf) t)
      end
    end erefl.

  Fixpoint seq_to_vseq (l : seq A) : vseq (size l) :=
    match l with
    | [::] => Nil
    | h :: t => Cns h (seq_to_vseq t)
    end.

  Definition aseq_to_vseq n (l : seq A) (p : size l = n) : vseq n :=
    match p with
    | erefl => seq_to_vseq l
    end.

  Lemma cast_nil n (p : n = n) (v : vseq n) : cast_vseq p v = v.
  Proof.
    move: (@nat_irrelevance n n p erefl) => irr.
    by rewrite /cast_vseq irr.
  Qed.

  Lemma iso1 l : vseq_to_seq (seq_to_vseq l) = l.
  Proof. by elim: l=>[|a l /=->]. Qed.

  Lemma vseq_size n (v : vseq n) : size (vseq_to_seq v) = n.
  Proof.
    elim: n v =>[|n Ih] v.
    - by case Eq: _ / v.
    - by case Eq: _ / v =>[//|m h t]; move: Eq t=>[<-]t {m}; rewrite /=Ih.
  Defined.

  Lemma cast_cons n m h (t : vseq n) (p : n.+1 = m.+1)
    : cast_vseq p (Cns h t) = Cns h (cast_vseq (succ_inj p) t).
  Proof.
    move: (succ_inj p) (succ_inj p) => p0 p1; move: p0 p1 p t=>-> p1 p t.
    by rewrite (nat_irrelevance p erefl) (nat_irrelevance p1 erefl)/=.
  Qed.

  Lemma iso2 n (v : vseq n) :
    cast_vseq (vseq_size v) (seq_to_vseq (vseq_to_seq v)) = v.
  Proof.
    elim: n v =>[|n Ih] v.
    - by case Eq: _ / v=>//= p; rewrite (nat_irrelevance p erefl).
    - case Eq: _ / v =>[//|m h t]; move: Eq t=>[<-]t {m} /=.
      by rewrite cast_cons (nat_irrelevance (succ_inj _) (vseq_size t)) Ih.
  Qed.
End CSeq.

Module Problem.
  CoInductive itree A := C : A -> seq (itree A) -> itree A.

  Fail CoFixpoint example (n : nat) : itree nat :=
    C n ((fix build_branches m : seq (itree nat) :=
            match m with
            | 0 => [::]
            | t.+1 => example m :: build_branches t
            end) n).
End Problem.

Section Nested.
  CoInductive itree A := C n : A -> vseq (itree A) n -> itree A.

  CoFixpoint example (n : nat) : itree nat :=
    C n ((cofix build_branches m : vseq (itree nat) m :=
            match m with
            | 0 => Nil _
            | t.+1 => Cns (example m) (build_branches t)
            end) n).
End Nested.
