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

(* exists size *)
Notation "'eS'" := (existT _ _).
(**
 Finite Coinductive Sequences
*)
Section CSeq.
  Context (A : Type).

  CoInductive vseq : nat -> Type :=
  | Nil   : vseq 0
  | Cns n : A -> vseq n -> vseq n.+1.

  Fixpoint vseq_to_seq n (x : vseq n) {struct n} : seq A :=
    match x in vseq m return m = n -> seq A with
    | Nil => fun _ => [::]
    | Cns m h t =>
      match n return m.+1 = n -> seq A with
      | 0 => fun pf => match pf with end
      | n.+1 =>
        fun pf =>
          match esym (succn_inj pf) with
          | erefl => fun t => h :: vseq_to_seq t
          end t
      end
    end erefl.

  Fixpoint seq_to_vseq (l : seq A) : vseq (size l) :=
    match l with
    | [::] => Nil
    | h :: t => Cns h (seq_to_vseq t)
    end.

  Definition fseq := {n & vseq n}.
  Definition f_nil : fseq := eS Nil.
  Definition f_cons h t := eS (Cns h (projT2 t)).
  Notation "[::]" := f_nil.
  Notation "h :: t" := (f_cons h t).

  Definition f_head (t : fseq) :=
    match t with
    | existT _ v =>
      match v with
      | Nil => None
      | Cns _ h _ => Some h
      end
    end.

  Definition f_tail (t : fseq) :=
    match t with
    | existT _ v =>
      match v with
      | Nil => None
      | Cns _ _ t => Some (existT _ _ t)
      end
    end.

  Definition f_size (t : fseq) := projT1 t.

  Lemma fseq_ind (P : fseq -> Type) :
    P [::] ->
    (forall h t, P t -> P (h :: t)) ->
    forall l, P l.
  Proof.
    move=>P_nil P_cons [n v].
    elim: n => [|n Ih] in v *; first by case E: _/v.
    case E:_ /v=>[//|m h t]; move: E t =>[<-] t {m}.
    rewrite -/(h :: existT _ _ _).
    by apply: P_cons; apply: Ih.
  Qed.

  Definition fseq_to_seq v := vseq_to_seq (projT2 v).
  Definition seq_to_fseq v := existT _ _ (seq_to_vseq v).

  Lemma fseq_iso1 l : fseq_to_seq (seq_to_fseq l) = l.
  Proof.
    rewrite /fseq_to_seq/seq_to_fseq/=.
    elim: l=>//= h t Ih.
    by rewrite (nat_irrelevance (esym _) erefl) Ih.
  Qed.

  Lemma fseq_iso2 l : seq_to_fseq (fseq_to_seq l) = l.
  Proof.
    elim/fseq_ind: l=>//= h t Ih.
    rewrite /seq_to_fseq/fseq_to_seq/= (nat_irrelevance (esym _) erefl)/=.
    rewrite  -[existT _ _ _]/(h :: existT _ _ _).
    by rewrite -/(fseq_to_seq _) -/(seq_to_fseq _) Ih.
  Qed.
End CSeq.

Section Nested.
  CoInductive itree A := C : A -> fseq (itree A) -> itree A.

  Definition build (f : nat -> itree nat) : forall m, vseq (itree nat) m :=
    cofix bb m :=
      match m with
      | 0 => Nil _
      | t.+1 => Cns (f m) (bb t)
      end.

  CoFixpoint example (n : nat) : itree nat :=
    C n (eS (build example n)).

End Nested.


(**
 Finite Coinductive Trees
*)
Section CTree.
  Context (A : Type).

  CoInductive vtree : nat -> Type :=
  | CL : vtree 0
  | CN l r : A -> vtree l -> vtree r -> vtree (maxn l r).+1.

  Inductive tree : Type :=
  | L : tree
  | N : A -> tree -> tree -> tree.

  Fixpoint depth (t : tree) :=
    match t with
    | L => 0
    | N _ l r => (maxn (depth l) (depth r)).+1
    end.

  Lemma maxn_left l r n : maxn l r <= n -> l <= n.
  Proof. by rewrite geq_max=>/andP-[]. Qed.

  Lemma maxn_right l r n : maxn l r <= n -> r <= n.
  Proof. by rewrite geq_max=>/andP-[]. Qed.

  Lemma z_ge_succn B n (p : 0 >= n.+1) : B.
  Proof. by []. Qed.

  Fixpoint vtree_to_dtree n m (x : vtree n) {struct m} : n <= m -> tree :=
    match x in vtree n return n <= m -> tree with
    | CL => fun _ => L
    | CN dl dr v l r =>
      match m with
      | 0 => fun pf => z_ge_succn _ pf
      | m.+1 =>
        fun pf =>
          N v
            (vtree_to_dtree l (maxn_left pf))
            (vtree_to_dtree r (maxn_right pf))
      end
    end.

  Definition vtree_to_tree n (x : vtree n) : tree := vtree_to_dtree x (leqnn n).

  Fixpoint tree_to_vtree (t : tree) : vtree (depth t) :=
    match t return vtree (depth t) with
    | L => CL
    | N h l r => CN h (tree_to_vtree l) (tree_to_vtree r)
    end.

  Definition ftree := {n & vtree n}.
  Definition f_leaf : ftree := existT _ _ CL.
  Definition f_node h l r := existT _ _ (CN h (projT2 l) (projT2 r)).

  Lemma ftree_ind (P : ftree -> Type) :
    P f_leaf ->
    (forall h l r, P l -> P r -> P (f_node h l r)) ->
    forall t, P t.
  Proof.
    move=>P_leaf P_node [n v]; move: {-2}n (leqnn n) v => m.
    elim: n => [|n Ih] in m *; first by case: m=>// _; case E:_/.
    move=> m_le_Sn v; case:_/v m_le_Sn =>[|dl dr h l r]// m_le_Sn{m}.
    move: (Ih _ (maxn_left m_le_Sn) l) (Ih _ (maxn_right m_le_Sn) r).
    by apply: P_node.
  Qed.

  Definition ftree_to_tree v := vtree_to_tree (projT2 v).
  Definition tree_to_ftree v := existT _ _ (tree_to_vtree v).

  Lemma vtree_gt n (t : vtree n) l m :
    (forall m (p : n <= m), vtree_to_dtree t p = l) ->
    (forall (p : n <= m), vtree_to_dtree t p = l).
  Proof. by []. Qed.

  Lemma ftree_iso1 l : ftree_to_tree (tree_to_ftree l) = l.
  Proof.
    rewrite /ftree_to_tree/tree_to_ftree/vtree_to_tree/=.
    move: (leqnn (depth l)); apply: vtree_gt.
    elim: l; first by case.
    by move=>h l Ihl r Ihr/=; case=>//=m p; rewrite Ihl Ihr.
  Qed.

  Lemma fold_dtree n (l : vtree n) m1 (p : n <= m1) m2 (q : n <= m2) :
    vtree_to_dtree l p = vtree_to_dtree l q.
  Proof.
    elim: m1 n l p m2 q =>[|n Ih].
    - by move=> n; case E:_/ =>// p [].
    - move=> n'; case:_/ =>[|dl dr h l r]; first by move=> _ []/=.
      move=> p [//|m q]/=.
      by rewrite (Ih _ l (maxn_left p) _ (maxn_left q))
                 (Ih _ r (maxn_right p) _ (maxn_right q)).
  Qed.

  Lemma ftree_iso2 l : tree_to_ftree (ftree_to_tree l) = l.
  Proof.
    elim/ftree_ind: l=>//= h l r Ihl Ihr.
    rewrite /ftree_to_tree/tree_to_ftree/=.
    rewrite -[existT _ _ _]/(f_node h (existT _ _ _) (existT _ _ _)).
    rewrite (fold_dtree _ (maxn_left _) (leqnn _)).
    rewrite (fold_dtree _ (maxn_right _) (leqnn _)).
    rewrite -!/(tree_to_ftree _) -!/(vtree_to_tree _) -!/(ftree_to_tree _).
    by rewrite Ihl Ihr.
  Qed.
End CTree.

Section ExampleTree.
  CoInductive ttree := TC : nat -> ftree ttree -> ttree.

  Definition tbuild (f : nat -> ttree) : forall m, vtree ttree m :=
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
