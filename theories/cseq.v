From mathcomp.ssreflect Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import fcoind.pfin.
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

  Fixpoint vseq_to_seq' n (x : vseq n) (p : Fin n) {struct p} : seq A :=
    match x in (vseq m) return (n = m -> seq A) with
    | Nil => fun _ => [::]
    | Cns m h t => fun pf => h :: vseq_to_seq' t (inv_succ p pf)
    end erefl.

  Definition vseq_to_seq n (x : vseq n) : seq A := vseq_to_seq' x (all_fin n).

  Fixpoint seq_to_vseq (l : seq A) : vseq (size l) :=
    match l with
    | [::] => Nil
    | h :: t => Cns h (seq_to_vseq t)
    end.

  Definition fseq := {n & vseq n}.
  Definition f_nil : fseq := eS Nil.
  Definition f_cons h t := eS (Cns h (projT2 t)).

  Definition f_head (t : fseq) :=
    match t with
    | existT _ v =>
      match v with
      | Nil => None
      | Cns _ h _ => Some h
      end
    end.

  Lemma prednSm n m : n = S m -> predn n = m.
  Proof. by case: n=>// n ->. Qed.

  Definition f_tail (t : fseq) :=
    match t with
    | existT n v =>
      match v in vseq m return n = m -> option fseq with
      | Nil => fun _ => None
      | Cns _ _ t =>
        fun pf =>
          match prednSm pf in _ = n return vseq n -> option fseq with
          | erefl => fun t => Some (existT _ (predn n) t)
          end t
      end erefl
    end.

  Definition f_size (t : fseq) := projT1 t.


  Definition v_foldl' B (z : B) (f : B -> A -> B)
    : forall n (x :vseq n), Fin n -> B :=
    (fix h (z : B) (n : nat) (t : vseq n) (p : Fin n) {struct p} :=
       match t in vseq m return n = m -> B with
       | Nil => fun _ => z
       | Cns m x l => fun pf => h (f z x) _ l (inv_succ p pf)
       end erefl) z.

  Definition v_foldl B (z : B) (f : B -> A -> B) n (x : vseq n) : B :=
    v_foldl' z f x (all_fin n).

  Definition t_foldl B (z : B) (f : B -> A -> B) (x : fseq) : B :=
    v_foldl z f (projT2 x).

  Definition t_reverse : fseq -> fseq :=
    t_foldl f_nil (fun x y => f_cons y x).

  Definition t_filter (p : A -> bool)  : fseq -> fseq :=
    fun t =>
      t_reverse (t_foldl f_nil (fun y x => if p x then f_cons x y else y) t).

  Lemma fseq_ind (P : fseq -> Prop) :
    P f_nil ->
    (forall h t, P t -> P (f_cons h t)) ->
    forall l, P l.
  Proof.
    move=>P_nil P_cons [n v].
    elim: n => [|n Ih] in v *; first by case E: _/v.
    case E:_ /v=>[//|m h t]; move: E t =>[<-] t {m}.
    rewrite -/(f_cons h (existT _ _ _)).
      by apply: P_cons; apply: Ih.
  Qed.

  Definition fseq_to_seq v := vseq_to_seq (projT2 v).
  Definition seq_to_fseq v := existT _ _ (seq_to_vseq v).

  Lemma fseq_iso1 l : fseq_to_seq (seq_to_fseq l) = l.
  Proof.
    rewrite /fseq_to_seq/seq_to_fseq/vseq_to_seq.
    rewrite /projT2/projT1; move: (all_fin (size l)) =>p.
    by elim: l=>[|h t Ih]/= in p *; case: p=>//= p; rewrite Ih.
  Qed.

  Lemma acc_irrelevant n (v : vseq n) p q : vseq_to_seq' v p = vseq_to_seq' v q.
  Proof.
    elim: n v p q =>[|n Ih].
    - by case E:_ / =>//; move=>[Hp] [Hq].
    - case E: _/ => [|m h t]//; move: E t=>[<-] {m} t [Hp] [Hq]/=.
      move: (inv_succ _ _) (inv_succ _ _) => p q.
      by rewrite (Ih _ p q).
  Qed.

  Lemma fold_vseq_to_seq' n (v : vseq n) p : vseq_to_seq' v p = vseq_to_seq v.
  Proof. by rewrite /vseq_to_seq; apply/acc_irrelevant. Qed.

  Lemma unroll_fseq h t : fseq_to_seq (f_cons h t) = h :: fseq_to_seq t.
  Proof.
    case: t => x v; rewrite /f_cons/projT2/fseq_to_seq/vseq_to_seq.
    case: (all_fin _) => Hp; rewrite /projT2/projT1.
    by rewrite [in LHS]/= (acc_irrelevant _ (inv_succ _ _) (all_fin x)).
  Qed.

  Lemma fseq_iso2 : forall l, seq_to_fseq (fseq_to_seq l) = l.
  Proof.
    elim/fseq_ind=>//= h t Ih; rewrite unroll_fseq /seq_to_fseq/=.
    rewrite -![existT _ _ _]/(f_cons h (existT _ _ _)).
    by rewrite -/(seq_to_fseq _) Ih.
  Qed.
End CSeq.
