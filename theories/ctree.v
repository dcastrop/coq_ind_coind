From mathcomp.ssreflect Require Import ssreflect ssrfun ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import fcoind.pfin.

(* exists size *)
Notation "'eS'" := (existT _ _).

(**
 Finite Coinductive Trees (indexed by shape)
*)
Section CTree.
  Context (A : Type).

  CoInductive vtree : nat -> Type :=
  | CL : vtree 0
  | CN l r : A -> vtree l -> vtree r -> vtree (maxn l r).+1.

  Inductive tree : Type :=
  | L : tree
  | N : A -> tree -> tree -> tree.

  Fixpoint vtree_to_tree' n (x : vtree n) (d : Fin n) {struct d} : tree :=
    match x in vtree m return n = m -> tree with
    | CL => fun _ => L
    | CN dl dr v l r =>
      fun pf =>
        N v (vtree_to_tree' l (inv_maxl d pf))
            (vtree_to_tree' r (inv_maxr d pf))
    end erefl.

  Definition vtree_to_tree n (x : vtree n) : tree :=
    vtree_to_tree' x (all_fin n).

  Fixpoint depth (t : tree) : nat :=
    match t with
    | L => 0
    | N _ l r => (maxn (depth l) (depth r)).+1
    end.

  Fixpoint tree_to_vtree (t : tree) : vtree (depth t) :=
    match t return vtree (depth t) with
    | L => CL
    | N h l r => CN h (tree_to_vtree l) (tree_to_vtree r)
    end.

  Definition ftree := {n & vtree n}.
  Definition f_leaf : ftree := existT _ _ CL.
  Definition f_node h l r := existT _ _ (CN h (projT2 l) (projT2 r)).

  Lemma ftree_ind (P : ftree -> Prop) :
    P f_leaf ->
    (forall h l r, P l -> P r -> P (f_node h l r)) ->
    forall t, P t.
  Proof.
    move=>P_leaf P_node [n v]; move: {-2}n (leqnn n) v => m H v.
    elim: n=>[|n Ih]// in m H v *; first by case: m H v =>// _; case E:_ /.
    case: m H v =>//; first by move=> _; case E: _ /.
    move=> m H; case E: _/ =>[|sl sr h l r]//; move: E H=>[->]{m} H.
    rewrite -/(f_node _ (existT _ _ _) (existT _ _ _)); apply: P_node.
    - by apply: Ih; apply: (leq_trans (leq_maxl sl sr)).
    - by apply: Ih; apply: (leq_trans (leq_maxr sl sr)).
  Qed.

  Definition ftree_to_tree v := vtree_to_tree (projT2 v).
  Definition tree_to_ftree v := existT _ _ (tree_to_vtree v).

  Lemma ftree_iso1 l : ftree_to_tree (tree_to_ftree l) = l.
  Proof.
    rewrite /tree_to_ftree/ftree_to_tree/vtree_to_tree/projT1/projT2.
    move: (all_fin (depth l)); elim: l=>//; first by case=>H//=.
    by move=> h l Ihl r Ihr []/= H; rewrite Ihl Ihr.
  Qed.

  Lemma totree_acc_irr n (t : vtree n) p q :
    vtree_to_tree' t p = vtree_to_tree' t q.
  Proof.
    rewrite /Fin in p q *; elim: n {-2} n (leqnn n) t p q =>[|n Ih].
    - by case=>// _; case E:_ / =>//; move=> [Hp] [Hq].
    - case=>[|m]; first by move=> _; case E:_ / =>//; move=>[Hp] [Hq].
      move=> m_le_n; case E:_ / => [|dl dr h l r]//; move=>[Hp] [Hq]/=.
      move: E m_le_n =>[->] m_le_n.
      move: (leq_trans (leq_maxl _ _) m_le_n) => l_n.
      move: (leq_trans (leq_maxr _ _) m_le_n) => r_n.
      by do ! rewrite (Ih _ _ _ _ (all_fin _)) //.
  Qed.

  Lemma step_vtotree dl dr h (l : vtree dl) (r : vtree dr) :
    vtree_to_tree (CN h l r) = N h (vtree_to_tree l) (vtree_to_tree r).
  Proof.
    rewrite /vtree_to_tree; case: all_fin=>H.
    by rewrite [in LHS]/= !(totree_acc_irr _ _ (all_fin _)).
  Qed.

  Lemma step_ftotree h (l : ftree) (r : ftree) :
    ftree_to_tree (f_node h l r) = N h (ftree_to_tree l) (ftree_to_tree r).
  Proof. by rewrite /ftree_to_tree step_vtotree. Qed.

  Lemma ftree_iso2 l : tree_to_ftree (ftree_to_tree l) = l.
  Proof.
    elim/ftree_ind: l=>[//|h l r Ih1 Ih2].
    rewrite step_ftotree/tree_to_ftree/= -/(f_node h (eS _) (eS _)).
    by rewrite -!/(tree_to_ftree _) Ih1 Ih2.
  Qed.
End CTree.
