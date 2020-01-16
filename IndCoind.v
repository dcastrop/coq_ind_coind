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

Module PFin.
  Inductive Fin : nat -> Prop :=
  | FZ : Fin 0
  | FS n : Fin n -> Fin n.+1.

  Lemma all_fin : forall n, Fin n.
  Proof. by elim=>[|n]; constructor. Defined.

  Lemma inv_vec : forall n m, Fin n -> n = m.+1 -> Fin m.
  Proof. by move=> n m; case=>// n' H [<-].
  Defined.
End PFin.

(**
 Finite Coinductive Sequences
*)
Module CSeq.
  Import PFin.
  Section CSeq.
    Context (A : Type).

    CoInductive vseq : nat -> Type :=
    | Nil   : vseq 0
    | Cns n : A -> vseq n -> vseq n.+1.

    Fixpoint vseq_to_seq' n (x : vseq n) (p : Fin n) {struct p} : seq A :=
      match x in (vseq m) return (n = m -> seq A) with
      | Nil => fun _ => [::]
      | Cns m h t => fun pf => h :: vseq_to_seq' t (inv_vec p pf)
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
         | Cns m x l => fun pf => h (f z x) _ l (inv_vec p pf)
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
      rewrite /fseq_to_seq/seq_to_fseq/vseq_to_seq/=.
      by elim: l=>//= h t ->.
    Qed.

    Lemma fseq_iso2 l : seq_to_fseq (fseq_to_seq l) = l.
    Proof.
      elim/fseq_ind: l=>//= h t Ih.
      rewrite /seq_to_fseq/fseq_to_seq/=.
      rewrite  -[existT _ _ _]/(f_cons h (existT _ _ _)).
      by rewrite -/(fseq_to_seq _) -/(seq_to_fseq _) Ih.
    Qed.
  End CSeq.
End CSeq.

Section Nested.
  Import CSeq.
  CoInductive itree A := C : A -> fseq (itree A) -> itree A.

  Definition build (f : nat -> itree nat) : forall m, vseq (itree nat) m :=
    cofix bb m := if m is t.+1 then Cns (f m) (bb t) else Nil _.

  CoFixpoint example (n : nat) : itree nat :=
    C n (eS (build example n)).
End Nested.

(**
 Finite Coinductive Trees (indexed by shape)
*)
Module CTree.
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

    (* Lemma vtree_gt n (t : vtree n) l m : *)
    (*   (forall m (p : n <= m), vtree_to_dtree t p = l) -> *)
    (*   (forall (p : n <= m), vtree_to_dtree t p = l). *)
    (* Proof. by []. Qed. *)

    Lemma ftree_iso1 l : ftree_to_tree (tree_to_ftree l) = l.
    Proof.
      rewrite /ftree_to_tree/tree_to_ftree/vtree_to_tree/=.
      by elim: l=>//= x l -> r ->.
    Qed.

    (* Lemma fold_dtree n (l : vtree n) m1 (p : n <= m1) m2 (q : n <= m2) : *)
    (*   vtree_to_dtree l p = vtree_to_dtree l q. *)
    (* Proof. *)
    (*   elim: m1 n l p m2 q =>[|n Ih]. *)
    (*   - by move=> n; case E:_/ =>// p []. *)
    (*   - move=> n'; case:_/ =>[|dl dr h l r]; first by move=> _ []/=. *)
    (*     move=> p [//|m q]/=. *)
    (*     by rewrite (Ih _ l (maxn_left p) _ (maxn_left q)) *)
    (*                (Ih _ r (maxn_right p) _ (maxn_right q)). *)
    (* Qed. *)

    Lemma ftree_iso2 l : tree_to_ftree (ftree_to_tree l) = l.
    Proof.
      elim/ftree_ind: l=>//= h l r.
      rewrite /ftree_to_tree/tree_to_ftree/= => IHl IHr.
      rewrite -[existT _ _ _]/(f_node h (existT _ _ _) (existT _ _ _)).
      by rewrite -!/(vtree_to_tree _) IHl IHr.
    Qed.
  End CTree.
End CTree.

Section ExampleTree.
  Import CTree.

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

Require Import Extraction.

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive seq => list [ "[]" "( :: )" ].

Extract Inductive sigT => "( * )" [ "(, )" ].
Extraction Inline projT1.
Extraction Inline projT2.

Set Extraction Flag 2047.
(** Extract CSeq
 *)

Extraction Implicit CSeq.Cns [ n ].
Extraction Implicit CSeq.vseq_to_seq' [ n ].
Extraction Implicit CSeq.vseq_to_seq [ n ].
Extraction Implicit CSeq.v_foldl' [ n ].
Extraction Implicit CSeq.v_foldl [ n ].

Extraction Inline CSeq.vseq_to_seq'.
Extraction Inline CSeq.v_foldl'.
Extraction Inline CSeq.v_foldl.
Extraction Inline CSeq.t_foldl.
Extraction Inline predn.

(* Unset Extraction SafeImplicits. *)
Extraction CSeq.

(** Extract Tree
 *)

Extraction Implicit CTree.CN [ l r ].
Extraction Implicit CTree.vtree_to_tree' [ n ].
Extraction Implicit CTree.vtree_to_tree  [ n ].

Extraction Inline CTree.vtree_to_tree'.

Extraction CTree.
