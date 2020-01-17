From mathcomp.ssreflect Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Coq Require Extraction.

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant predn => "(fun n -> n-1) ".
Extract Constant leq => "( <= )".
Extract Constant maxn => "max".
Extraction Inline leq.
Extraction Inline predn.
Extraction Inline maxn.

Extract Inductive bool => bool [ "true" "false" ].
Extract Inductive seq => list [ "[]" "( :: )" ].
Extract Inductive option => option [ "Some" "None" ].

Extract Inductive sigT => "( * )" [ "(, )" ].
Extract Constant projT1 => "fst".
Extract Constant projT2 => "snd".
Extraction Inline projT1.
Extraction Inline projT2.

Extract Inductive reflect => bool [ "true" "false" ].
Extraction Inline pred.
Extraction Inline rel.
Extraction Inline Equality.axiom.

Set Extraction Flag 2047.

(** Extract CSeq
 *)
Require fcoind.cseq.

Extraction Implicit cseq.Cns [ n ].
Extraction Implicit cseq.vseq_to_seq' [ n ].
Extraction Implicit cseq.vseq_to_seq [ n ].
Extraction Implicit cseq.v_foldl' [ n ].
Extraction Implicit cseq.v_foldl [ n ].

Extraction Inline cseq.vseq_to_seq'.
Extraction Inline cseq.v_foldl'.
Extraction Inline cseq.v_foldl.
Extraction Inline cseq.t_foldl.

(* Unset Extraction SafeImplicits. *)
Extraction "../extraction/cseq"
           cseq.vseq_to_seq
           cseq.fseq_to_seq
           cseq.seq_to_vseq
           cseq.seq_to_fseq
           cseq.f_nil
           cseq.f_cons
           cseq.f_head
           cseq.f_tail
           cseq.t_foldl
           cseq.t_reverse
           cseq.t_filter.

(** Extract Tree *)
(*  *)

Require fcoind.stree.
Extraction Implicit stree.CN [ l r ].
Extraction Implicit stree.vtree_to_tree' [ n ].
Extraction Implicit stree.vtree_to_tree  [ n ].

Extraction Inline stree.vtree_to_tree'.

Extraction "../extraction/stree"
           fcoind.stree.shape
           fcoind.stree.tree
           fcoind.stree.vtree
           fcoind.stree.vtree_to_tree
           fcoind.stree.tshape
           fcoind.stree.tree_to_vtree
           fcoind.stree.ftree
           fcoind.stree.f_leaf
           fcoind.stree.f_node
           fcoind.stree.ftree_to_tree
           fcoind.stree.tree_to_ftree.

(** Extract Tree *)
(*  *)

Require fcoind.ctree.
Extraction Implicit ctree.CN [ l r ].
Extraction Implicit ctree.vtree_to_tree' [ n ].
Extraction Implicit ctree.vtree_to_tree  [ n ].

Extraction Inline ctree.vtree_to_tree'.

Extraction "../extraction/ctree"
           fcoind.ctree.tree
           fcoind.ctree.vtree
           fcoind.ctree.vtree_to_tree
           fcoind.ctree.tree_to_vtree
           fcoind.ctree.ftree
           fcoind.ctree.f_leaf
           fcoind.ctree.f_node
           fcoind.ctree.ftree_to_tree
           fcoind.ctree.tree_to_ftree.
