From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Type FUNCTOR.
  Parameter (L : Type).
  Parameter (F : Type -> Type).
  Parameter (OCC : forall (X : Type), X -> F X -> Prop).
  Axiom (omap : forall (X Y : Type) p, (forall (x : X), OCC x p -> Y) -> F Y).
End FUNCTOR.

Module Type SPF (M:FUNCTOR).
  Inductive App (X : Type) : Type
    := App_C { shape : M.F M.L; get : forall x : M.L, M.OCC x shape -> X }.
  Reserved Notation "x '\pos'  F"
           (at level 70, no associativity,
            format "'[hv' x '/ '  '\pos'  F ']'").
  Notation "x \pos F" := (M.OCC x (shape F)).
  Definition App_R X Y (r : X -> Y -> Prop) (f : App X) (g : App Y) :=
    shape f = shape g /\
    forall x (o1 : x \pos f) (o2 : x \pos g), r (get o1) (get o2).
  Axiom App_R_mon :
    forall X Y (x : App X) (y : App Y) (r r' : X -> Y -> Prop),
      App_R r x y -> (forall ex ey, r ex ey -> r' ex ey) -> App_R r' x y.
  Definition fmap_dom X Y (x : App X) (f : forall p, p \pos x -> Y) : App Y
    := App_C (fun y (o : y \pos x) => f y o).
  Definition fmap X Y (f : X -> Y) (x : App X) : App Y
    := App_C (fun y (o : y \pos x) => f (get o)).
  Parameter fmap_id
    : forall X : Type, fmap id =1 id :> (App X -> App X).
  Parameter fmap_comp
    : forall (X Y Z : Type) (f : X -> Y) (g : Y -> Z),
      fmap g \o fmap f =1 fmap (g \o f).
End SPF.

Module SPFunctor (M : FUNCTOR) : SPF(M).
  Import M.

  Create HintDb gfix.
  #[universes(template)] Inductive App X
    := App_C {
           shape : F L;
           get : forall x, OCC x shape -> X
         }.
  Hint Constructors App : gfix.

  Reserved Notation "x '\pos'  F"
           (at level 70, no associativity,
            format "'[hv' x '/ '  '\pos'  F ']'").
  Notation "x \pos F" := (OCC x (shape F)).

  Definition App_R X Y (r : X -> Y -> Prop) (f : App X) (g : App Y) :=
    shape f = shape g /\
    forall x (o1 : x \pos f) (o2 : x \pos g), r (get o1) (get o2).
  Hint Unfold App_R : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context[App_R] ] => rewrite /App_R/=
  end : gfix.

  Lemma App_R_mon X Y (x : App X) (y : App Y) (r r' : X -> Y -> Prop) :
    App_R r x y -> (forall ex ey, r ex ey -> r' ex ey) -> App_R r' x y.
  Proof. case: x; case: y=>/= sx fx sy fy []; eauto with gfix. Qed.
  Hint Resolve App_R_mon : gfix.

  Definition fmap_dom X Y (x : App X) (f : forall p, p \pos x -> Y) : App Y
    := App_C (fun y (o : y \pos x) => f y o).

  Definition fmap X Y (f : X -> Y) (x : App X) : App Y
    := App_C (fun y (o : y \pos x) => f (get o)).

  Lemma fmap_id X : fmap id =1 id :> (App X -> App X).
  Proof. case; by eauto. Qed.

  Lemma fmap_comp X Y Z (f : X -> Y) (g : Y -> Z)
    : fmap g \o fmap f =1 fmap (g \o f).
  Proof. by move=>[p k]. Qed.
End SPFunctor.

Module GFix(M : FUNCTOR) (F : SPF(M)).
  (* Import M SPM. *)
  Hint Resolve F.App_R_mon : gfix.

  CoInductive GFix : Type := G_in { g_out : F.App GFix }.
  Hint Constructors GFix : gfix.

  Notation "'g_in'" := G_in (at level 0).

  Lemma g_in_out : id =1 g_in \o g_out.
  Proof. by case. Qed.

  Lemma g_out_in : id =1 g_out \o g_in.
  Proof. by []. Qed.

  (* Could generalize to [GFix T -> GFix T' -> Prop], but would require an
   * extra relation to "zip" elements of [F]
   *)
  Definition GFix_EQ_ (r : GFix -> GFix -> Prop) (gl gr : GFix) : Prop :=
    F.App_R r (g_out gl) (g_out gr).
  Hint Unfold GFix_EQ_ : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context [GFix_EQ_ _ _ _]] => rewrite /GFix_EQ_/=
  end : gfix.

  Reserved Notation "x =g y" (at level 70, no associativity).
  Notation "x =g y" := (paco2 GFix_EQ_ bot2 x y) : type_scope.

  Lemma GFix_EQ_mon : monotone2 GFix_EQ_.
  Proof. eauto with gfix. Qed.
  Hint Resolve GFix_EQ_mon : gfix.

  Definition ana A (h : A -> F.App A) : A -> GFix
    := cofix f := g_in \o (F.fmap f) \o h.

  Lemma ana_eq A (h : A -> F.App A) :
    g_out \o ana h =1 F.fmap (ana h) \o h.
  Proof. by []. Qed.

  Corollary ana_unroll A (h : A -> F.App A) :
    ana h =1 g_in \o F.fmap (ana h) \o h.
  Proof. move=>x; by rewrite (g_in_out (ana h x)). Qed.
End GFix.

Module LFix(M : FUNCTOR) (F : SPF(M)).
  Inductive LFix : Type := L_in { l_out : F.App LFix }.
  Hint Constructors LFix : gfix.

  Notation "'l_in'" := L_in (at level 0).

  Lemma l_in_out : id =1 l_in \o l_out.
  Proof. by case. Qed.

  Lemma l_out_in : id =1 l_out \o l_in.
  Proof. by []. Qed.

  Fixpoint LFix_EQ (l r : LFix) : Prop := F.App_R LFix_EQ (l_out l) (l_out r).

  Reserved Notation "x =l y" (at level 70, no associativity).
  Notation "x =l y" := (LFix_EQ x y) : type_scope.

  Definition cata A (h : F.App A -> A) : LFix -> A
    := fix f x := (h \o (F.fmap f) \o l_out) x.

  Lemma cata_eq A (h : F.App A -> A) :
    cata h \o l_in =1 h \o F.fmap (cata h).
  Proof. by []. Qed.

  Corollary cata_unroll A (h : F.App A -> A) :
    cata h =1 h \o F.fmap (cata h) \o l_out.
  Proof. move=>x; by rewrite (l_in_out x). Qed.
End LFix.

Module FinGFix (M : FUNCTOR) (F : SPF(M)).
  Module G := GFix(M)(F).
  Module L := LFix(M)(F).
  Import F.
  Import G.
  Import L.

  Inductive Finite : GFix -> Prop :=
  | Fin_fold (x : F.App GFix) :
      (forall y (o : y \pos x), Finite (F.get o)) -> Finite (g_in x).

  Lemma Fin_inv1 (p : GFix) :
    Finite p -> forall s (o : s \pos g_out p), Finite (F.get o).
  Proof. by move=>[]. Defined.

  Definition LGFix := { p : GFix | Finite p }.

  Definition lg_forget (x : F.App LGFix) : F.App GFix :=
    F.fmap (@sval GFix Finite) x.

  Definition lg_fin (x : F.App LGFix) y (o : y \pos x)
    : Finite (sval (F.get o)) := @proj2_sig GFix Finite (F.get o).

  Definition lg_in (x : F.App LGFix) : LGFix :=
    exist _ _ (Fin_fold (fun n (o : n \pos (lg_forget x)) => lg_fin o)).

  Definition lg_out (x : LGFix) : F.App LGFix :=
    F.fmap_dom (fun n (o : n \pos g_out (proj1_sig x)) =>
                  exist _ _ (Fin_inv1 (proj2_sig x) o)).

  Definition cata_ A (g : F.App A -> A) : forall p, Finite p -> A
    := fix f p FIN {struct FIN} :=
         g (F.fmap_dom (fun n a => f (get a) (Fin_inv1 FIN a))).

  Definition cata A (g : F.App A -> A) : LGFix -> A :=
    fun x => cata_ g (proj2_sig x).

  Definition gfix_to_lfix : LGFix -> LFix := cata l_in.
  Definition lfix_to_gfix : LFix -> LGFix := L.cata lg_in.

  Lemma Fin_inv2 A (g : A -> F.App A) (a : A) :
    Finite (ana g a) -> forall s (o : s \pos (g a)), Finite (ana g (get o)).
  Proof. rewrite ana_unroll; apply/Fin_inv1. Defined.

  Definition fana_ A (h : A -> F.App A) : forall x, Finite (ana h x) -> LFix
    := fix f x F := l_in (F.fmap_dom (fun y o => f (get o) (Fin_inv2 F o))).

  (* Terminating functions *)
  Reserved Notation "x ->> y"
           (at level 90, no associativity, y at level 200).
  Notation "A ->> B" := {h : A -> B | forall x, Finite (ana h x)}.

  Definition fin_ana A (h : A ->> F.App A) : A -> LFix :=
    fun x => fana_ (proj2_sig h x).

  Definition fin_hylo A B (g : F.App B -> B) (h : A -> F.App A)
    : forall (x : A) (F : Finite (ana h x)), B
    := fix f x F := g (F.fmap_dom (fun y o => f (get o) (Fin_inv2 F o))).

  Definition fhylo A B (g : F.App B -> B) (h : A ->> F.App A)
    : A -> B := fun x => fin_hylo g (proj2_sig h x).
End FinGFix.

Module TreeF : FUNCTOR.
  Definition L := nat.
  Inductive F (t : Type) : Type :=
  | C : nat -> seq t -> F t.

  Definition OCC X (x : X) (t : F X) : Prop :=
    match t with
    | C _ l => List.In x l
    end.

  Definition lmap X Y (l : seq X) (f : forall (x : X))

  Definition omap X Y (p : F X) (f : forall (x : X), OCC x p -> Y) : F Y
    := match p with
       | C h l => C h (map (fun x => f x _) l)(* ((fix lmap l := *)
         (* match l return List.In x l -> seq Y with *)
         (* | [::] => fun _ => [::] *)
         (* | h :: t => fun pf => _ *)
         (* end) l) *)
       end.

  Definition omap

End TreeF.

  Definition citree S A := GFix S (@treeOcc A).

  Fixpoint downfrom n :=
    match n with
    | 0 => []
    | S m => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat :=
    ana (@treeOcc nat) (fun n => (C n (downfrom n))) n.
End ExampleInfTree.

Section QSort.
  (* Functor *)
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  (* 'Position' but in Prop rather than Set or Type *)
  Definition P_occ A X : X -> P A X -> Prop :=
    fun x p => match p with
               | Empty _ _ => False
               | Div _ l r => x = l \/ x = r
               end.

  Definition pmap A X Y (p : P A X) (f : forall x, P_occ x p -> Y) : P A Y :=
    match p as p0 return p = p0 -> P A Y with
    | Empty _ _ => fun _ => Empty _ _
    | Div h l r =>
      fun PF =>
        match PF in _ = x return P_occ l x -> P_occ r x -> P A Y with
        | eq_refl => fun pl pr => Div h (f l pl) (f r pr)
        end (or_introl eq_refl) (or_intror eq_refl)
    end eq_refl.

  Definition p_split (l : list nat) : P nat (list nat) :=
    match l with
    | [] => Empty _ _
    | h :: t =>
      Div h
          (filter (fun x => Nat.leb x h) t)
          (filter (fun x => negb (Nat.leb x h)) t)
    end.

  Definition p_merge (t : P nat (list nat)) : list nat :=
    match t with
    | Empty _ _  => []
    | Div h l r => l ++ h :: r
    end.

  Lemma list_filter_length A (pred : A -> bool) (l : list A) :
    length (filter pred l) <= length l.
  Proof with eauto.
    induction l...
    simpl; case (pred a); simpl.
    - apply le_n_S...
    - apply le_S in IHl...
  Qed.
  Hint Resolve list_filter_length.

  Import PeanoNat.Nat.
  Lemma p_split_terminates (l : list nat) : Finite (ana (@P_occ nat) p_split l).
  Proof.
    generalize (leb_refl (length l)); generalize (length l) at -1.
    intros n LE; revert l LE.
    induction n; intros []; simpl; intro EQ; try (discriminate EQ); eauto;
      rewrite (gfix_unfold_id (ana _ _ _)); constructor; intros s F; destruct F.
    - subst; apply IHn; clear IHn.
      apply leb_le in EQ; apply leb_le, (le_trans _ (length l) n); eauto.
    - subst; apply IHn; clear IHn.
      apply leb_le in EQ; apply leb_le, (le_trans _ (length l) n); eauto.
  Qed.

  Definition app A : LFix A _ -> list nat := cata (@pmap nat) p_merge.
  Definition spl1 (x : list nat) := fana (p_split_terminates x).
  Definition spl2 := ana (@P_occ nat) p_split.

  Definition msort : list nat -> list nat
    := fhylo (@pmap nat) p_merge p_split_terminates.
End QSort.

(* From Coq Require Extraction ExtrHaskellBasic ExtrHaskellNatInteger. *)
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Inline pmap.
Extraction Inline ana.
Extraction Inline fana.
Extraction Inline cata.
Extraction Inline fcata.
Extraction Inline fhylo.
Extraction Inline thylo.
Extraction Inline p_merge.
Extraction Inline p_split.
Print Extraction Inline.
Extraction "msort" msort spl1 spl2 app.
