From mathcomp.ssreflect Require Import all_ssreflect seq.
From mathcomp Require Import finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Problem.
  CoInductive itree A := C : A -> seq (itree A) -> itree A.

  Fail CoFixpoint example (n : nat) : itree nat :=
    C n ((fix build_branches m : seq (itree nat) :=
            match m with
            | 0 => [::]
            | t.+1 => example m :: build_branches t
            end) n).
End Problem.

(**
 Finite Coinductive Sequences
*)
Section CSeq.
  Context (A : Type).

  CoInductive vseq : nat -> Type :=
  | Nil   : vseq 0
  | Cns n : A -> vseq n -> vseq n.+1.

  Fixpoint vseq_to_seq n (x : vseq n) {struct n} : seq A :=
    match x
          in vseq m
          return m = n -> seq A
    with
    | Nil =>
      fun _ =>
        [::]
    | Cns m h t =>
      match n
            return m.+1 = n -> seq A
      with
      | 0 =>
        fun pf =>
          match pf with end
      | n.+1 =>
        fun pf =>
          match esym (succn_inj pf)
                in _ = n
                return vseq n -> seq A
          with
          | erefl =>
            fun t =>
              h :: vseq_to_seq t
          end t
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

  (*
  Lemma cast_nil n (p : n = n) (v : vseq n) : cast_vseq p v = v.
  Proof.
    move: (@nat_irrelevance n n p erefl) => irr.
    by rewrite /cast_vseq irr.
  Qed.

  Lemma viso1 l : vseq_to_seq (seq_to_vseq l) = l.
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

  Lemma viso2 n (v : vseq n) :
    cast_vseq (vseq_size v) (seq_to_vseq (vseq_to_seq v)) = v.
  Proof.
    elim: n v =>[|n Ih] v.
    - by case Eq: _ / v=>//= p; rewrite (nat_irrelevance p erefl).
    - case Eq: _ / v =>[//|m h t]; move: Eq t=>[<-]t {m} /=.
      by rewrite cast_cons (nat_irrelevance (succ_inj _) (vseq_size t)) Ih.
  Qed.
  *)

  Definition fseq := {n & vseq n}.
  Definition f_nil : fseq := existT _ _ Nil.
  Definition f_cons h t := existT _ _ (Cns h (projT2 t)).
  Notation "[::]" := f_nil.
  Notation "h :: t" := (f_cons h t).

  Lemma fseq_ind (P : fseq -> Type) :
    P [::] ->
    (forall h t, P t -> P (h :: t)) ->
    forall l, P l.
  Proof.
    move=>P_nil P_cons [n v].
    elim: n => [|n Ih] in v *; first by case E: _/v.
    case E:_ /v=>[//|m h t]; move: E Ih =>[->] Ih {n}.
    rewrite -/(h :: existT _ _ _).
    by apply: P_cons; apply: Ih.
  Qed.

  Definition fseq_to_seq v := vseq_to_seq (projT2 v).
  Definition seq_to_fseq v := existT _ _ (seq_to_vseq v).

  Lemma f_iso1 l : fseq_to_seq (seq_to_fseq l) = l.
  Proof. by rewrite /fseq_to_seq/seq_to_fseq viso1. Qed.

  Lemma roll_cons n h t :
    existT vseq n.+1 (Cns h t) = h :: (existT vseq n t).
  Proof. by []. Qed.

  Lemma f_iso2 l : seq_to_fseq (fseq_to_seq l) = l.
  Proof.
    elim/fseq_ind: l=>//= h t Ih.
    rewrite /seq_to_fseq/fseq_to_seq/=.
    by rewrite roll_cons -/(fseq_to_seq _) -/(seq_to_fseq _) Ih.
  Qed.

End CSeq.

Notation "'fseqB' v" := (existT _ _ v) (at level 0).

Section Nested.

  CoInductive itree A := C : A -> fseq (itree A) -> itree A.

  CoFixpoint example (n : nat) : itree nat :=
    C n (fseqB ((cofix build_branches m : vseq (itree nat) m :=
                   match m with
                   | 0 => Nil _
                   | t.+1 => Cns (example m) (build_branches t)
                   end) n)).
End Nested.
