From mathcomp.ssreflect Require Import ssreflect ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* exists size *)
Notation "'eS'" := (existT _ _).

(**
 Finite Coinductive Trees (indexed by shape)
*)
Section CTree.
  Context (A : Type).

  Inductive shape : Type :=
  | SL : shape
  | SN : shape -> shape -> shape.

  Inductive tree : Type :=
  | L : tree
  | N : A -> tree -> tree -> tree.

  CoInductive vtree : shape -> Type :=
  | CL : vtree SL
  | CN l r : A -> vtree l -> vtree r -> vtree (SN l r).

  Inductive Fin : shape -> Prop :=
  | FL : Fin SL
  | FN l r : Fin l -> Fin r -> Fin (SN l r).

  Lemma all_fin : forall t, Fin t.
  Proof. by elim=>[|x l r]; constructor. Defined.

  Lemma inv_fin1 : forall n l r, Fin n -> n = SN l r -> Fin l.
  Proof. by move=> n l r; case=>// l' r' H0 H1 [<-]. Defined.

  Lemma inv_fin2 : forall n l r, Fin n -> n = SN l r -> Fin r.
  Proof. by move=> n l r; case=>// l' r' H0 H1 [_ <-]. Defined.

  Fixpoint vtree_to_tree' n (x : vtree n) (d : Fin n) {struct d} : tree :=
    match x in vtree m return n = m -> tree with
    | CL => fun _ => L
    | CN dl dr v l r =>
      fun pf =>
        N v (vtree_to_tree' l (inv_fin1 d pf))
            (vtree_to_tree' r (inv_fin2 d pf))
    end erefl.

  Definition vtree_to_tree n (x : vtree n) : tree :=
    vtree_to_tree' x (all_fin n).

  Fixpoint tshape (t : tree) : shape :=
    match t with
    | L => SL
    | N _ l r => SN (tshape l) (tshape r)
    end.

  Fixpoint tree_to_vtree (t : tree) : vtree (tshape t) :=
    match t return vtree (tshape t) with
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
    move=>P_leaf P_node [n v].
    elim: n v=>//; first by case E:_ / =>//.
    move=> l Ihl r Ihr; case E:_ / =>[| l' r' x' cl cr]//.
    move: E cl Ihl cr Ihr =>[<-<-] cl /(_ cl)-Pcl cr /(_ cr)-Pcr.
    rewrite -/(f_node _ (existT _ _ _) (existT _ _ _)).
    by apply: P_node.
  Qed.

  Definition ftree_to_tree v := vtree_to_tree (projT2 v).
  Definition tree_to_ftree v := existT _ _ (tree_to_vtree v).

  Lemma ftree_iso1 l : ftree_to_tree (tree_to_ftree l) = l.
  Proof.
    rewrite /ftree_to_tree/tree_to_ftree/vtree_to_tree/=.
    by elim: l=>//= x l -> r ->.
  Qed.

  Lemma ftree_iso2 l : tree_to_ftree (ftree_to_tree l) = l.
  Proof.
    elim/ftree_ind: l=>//= h l r.
    rewrite /ftree_to_tree/tree_to_ftree/= => IHl IHr.
    rewrite -/(f_node h (existT _ _ _) (existT _ _ _)).
    by rewrite -!/(vtree_to_tree _) IHl IHr.
  Qed.
End CTree.
