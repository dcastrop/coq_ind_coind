From mathcomp.ssreflect Require Import ssreflect ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Import Coq.Init.Wf.

Definition Fin (n : nat) := Acc lt n.

Definition all_fin : forall n, Fin n := Wf_nat.lt_wf.

Lemma inv_succ : forall n m, Fin n -> n = m.+1 -> Fin m.
Proof. by move=> n m H E; move: E H=>-> H; apply/(Acc_inv H). Defined.
