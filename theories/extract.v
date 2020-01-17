From mathcomp.ssreflect Require Import all_ssreflect seq.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Coq Require Extraction.

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Inductive bool => bool [ "true" "false" ].
Extract Inductive seq => list [ "[]" "( :: )" ].
Extract Inductive option => option [ "Some" "None" ].

Extract Inductive sigT => "( * )" [ "(, )" ].
Extract Constant projT1 => "fst".
Extract Constant projT2 => "snd".
Extraction Inline projT1.
Extraction Inline projT2.

Extraction Inline predn.

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
Extraction "extraction/cseq"
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

Require fcoind.ctree.
Extraction Implicit ctree.CN [ l r ].
Extraction Implicit ctree.vtree_to_tree' [ n ].
Extraction Implicit ctree.vtree_to_tree  [ n ].

Extraction Inline ctree.vtree_to_tree'.

Extraction "extraction/ctree"
           fcoind.ctree.shape
           fcoind.ctree.tree
           fcoind.ctree.vtree
           fcoind.ctree.vtree_to_tree
           fcoind.ctree.tshape
           fcoind.ctree.tree_to_vtree
           fcoind.ctree.ftree
           fcoind.ctree.f_leaf
           fcoind.ctree.f_node
           fcoind.ctree.ftree_to_tree
           fcoind.ctree.tree_to_ftree.
