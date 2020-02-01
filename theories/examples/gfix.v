From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x '\pos' F"
         (at level 70, no associativity,
          format "'[hv' x '/ '  '\pos'  F ']'").
Reserved Notation "x =l y" (at level 70, no associativity).
Reserved Notation "x =g y" (at level 70, no associativity).
Reserved Notation "x '=1[sval]' y" (at level 70, no associativity).
Reserved Notation "x +> y"
         (at level 90, no associativity).


Section Definitions.
  Context (L : Type).
  Context (F : forall (t : Type),  Type).
  Context (OCC : forall (X : Type), X -> F X -> Prop).
  Context (omap : forall (X Y : Type) p, (forall (x : X), OCC x p -> Y) -> F Y).

  Definition DOM X (y : F X) := {x : X | OCC x y}.

  Create HintDb gfix.
  #[universes(template)] Inductive App X
    := App_C {
           shape :> F L;
           get : DOM shape -> X
         }.
  Hint Constructors App : gfix.

  Definition mk_app (f : F L) : App L :=
    {| shape := f; get := fun y => proj1_sig y |}.

  Definition App_R X Y (r : X -> Y -> Prop) (f : App X) (g : App Y) :=
    shape f = shape g /\
    forall (o1 : DOM f) (o2 : DOM g), sval o1 = sval o2 -> r (get o1) (get o2).
  Hint Unfold App_R : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context[App_R] ] => rewrite /App_R/=
  end : gfix.

  Lemma App_R_mon X Y (x : App X) (y : App Y) (r r' : X -> Y -> Prop) :
    App_R r x y -> (forall ex ey, r ex ey -> r' ex ey) -> App_R r' x y.
  Proof. case: x; case: y=>/= sx fx sy fy []; eauto with gfix. Qed.
  Hint Resolve App_R_mon : gfix.

  Definition fmap_dom X Y (x : App X) (f : DOM x -> Y) : App Y := App_C f.

  Definition fmap X Y (f : X -> Y) (x : App X) : App Y
    := App_C (f \o get (a:=x)).

  Lemma fmap_id X : fmap id =1 id :> (App X -> App X).
  Proof. case; by eauto. Qed.

  Lemma fmap_comp X Y Z (f : X -> Y) (g : Y -> Z)
    : fmap g \o fmap f =1 fmap (g \o f).
  Proof. by move=>[p k]. Qed.

  CoInductive GFix : Type := G_in { g_out : App GFix }.
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
    App_R r (g_out gl) (g_out gr).
  Definition GFix_EQ x y := paco2 GFix_EQ_ bot2 x y.
  Hint Unfold GFix_EQ : gfix.
  Hint Unfold GFix_EQ_ : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context [GFix_EQ _ _]] => rewrite /GFix_EQ/GFix_EQ_/=
  end : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context [GFix_EQ_ _ _ _]] => rewrite /GFix_EQ_/=
  end : gfix.

  Notation "x =g y" := (GFix_EQ x y) : type_scope.

  Lemma GFix_EQ_mon : monotone2 GFix_EQ_.
  Proof. eauto with gfix. Qed.
  Hint Resolve GFix_EQ_mon : gfix.

  Definition ana A (h : A -> App A) : A -> GFix
    := cofix f := g_in \o fmap f \o h.

  Lemma ana_eq A (h : A -> App A) :
    g_out \o ana h =1 fmap (ana h) \o h.
  Proof. by []. Qed.

  Corollary ana_unroll A (h : A -> App A) :
    ana h =1 g_in \o fmap (ana h) \o h.
  Proof. move=>x; by rewrite (g_in_out (ana h x)). Qed.

  Inductive LFix : Type := L_in { l_out : App LFix }.
  Hint Constructors LFix : gfix.

  Notation "'l_in'" := L_in (at level 0).

  Lemma l_in_out : id =1 l_in \o l_out.
  Proof. by case. Qed.

  Lemma l_out_in : id =1 l_out \o l_in.
  Proof. by []. Qed.

  Fixpoint LFix_EQ (l r : LFix) : Prop := App_R LFix_EQ (l_out l) (l_out r).

  Notation "x =l y" := (LFix_EQ x y) : type_scope.

  Definition cata A (h : App A -> A) : LFix -> A
    := fix f x := (h \o (fmap f) \o l_out) x.

  Lemma cata_eq A (h : App A -> A) :
    cata h \o l_in =1 h \o fmap (cata h).
  Proof. by []. Qed.

  Corollary cata_unroll A (h : App A -> A) :
    cata h =1 h \o fmap (cata h) \o l_out.
  Proof. move=>x; by rewrite (l_in_out x). Qed.

  Inductive Finite : GFix -> Prop :=
  | Fin_fold (x : App GFix) :
      (forall (y : DOM x), Finite (get y)) -> Finite (g_in x).

  Lemma Fin_inv1 (p : GFix) :
    Finite p -> forall (x : DOM (g_out p)), Finite (get x).
  Proof. by move=>[]. Defined.

  Definition LGFix := { p : GFix | Finite p }.

  Definition E_LGFix (s1 s2 : LGFix) := sval s1 =g sval s2.

  Definition lg_forget : App LGFix -> App GFix := fmap (@sval GFix Finite).

  Definition lg_fin (x : App LGFix) (y : DOM x)
    : Finite (sval (get y)) := @proj2_sig GFix Finite (get y).

  Definition lg_in (x : App LGFix) : LGFix :=
    exist _ _ (@Fin_fold (fmap sval x) (lg_fin (x:=x))).

  Definition lg_out_ (x : LGFix) (n : DOM (g_out (sval x))) :=
    exist [eta Finite] (get n) (Fin_inv1 (proj2_sig x) n).

  (* Try remove fun here? *)
  Definition lg_out (x : LGFix) : App LGFix := fmap_dom (lg_out_ (x:=x)).

  Notation "f =1[sval] g" := (forall x, sval (f x) = sval (g x)).

  Lemma lg_in_out : lg_in \o lg_out =1[sval] id.
  Proof. by case; case; case. Qed.

  Lemma lg_out_in : lg_out \o lg_in =1 id.
  Proof.
    move=> x; rewrite /lg_in/lg_out/comp/fmap_dom/lg_fin/lg_out_//=.
    (* Here I do need extensional equality, unfortunately *)
  Abort.

  Definition cata_ A (g : App A -> A) : forall p, Finite p -> A
    := fix f p FIN {struct FIN} :=
         g (fmap_dom (fun n => f (get n) (Fin_inv1 FIN n))).

  Definition tcata A (g : App A -> A) : LGFix -> A :=
    fun x => cata_ g (proj2_sig x).

  Definition gfix_to_lfix : LGFix -> LFix := tcata l_in.
  Definition lfix_to_gfix : LFix -> LGFix := cata lg_in.

  Lemma Fin_inv2 A (g : A -> App A) (a : A) :
    Finite (ana g a) -> forall (o : DOM (g a)), Finite (ana g (get o)).
  Proof. rewrite ana_unroll; apply/Fin_inv1. Defined.

  Definition fana_ A (h : A -> App A) : forall x, Finite (ana h x) -> LFix
    := fix f x F := l_in (fmap_dom (fun y => f (get y) (Fin_inv2 F y))).

  (* Terminating functions *)
  Notation "A +> B" := {h : A -> B | forall x, Finite (ana h x)}.

  Definition fin_ana A (h : A +> App A) : A -> LFix :=
    fun x => fana_ (proj2_sig h x).

  Definition t_ana A (h : A +> App A) : A -> LGFix :=
    fun x => exist _ _ (proj2_sig h x).

  Definition fin_hylo A B (g : App B -> B) (h : A -> App A)
    : forall (x : A) (F : Finite (ana h x)), B
    := fix f x F := g (fmap_dom (fun y => f (get y) (Fin_inv2 F y))).

  Definition fhylo A B (g : App B -> B) (h : A +> App A)
    : A -> B := fun x => fin_hylo g (proj2_sig h x).
End Definitions.

Notation "A +> B" := {h : A -> B | forall x, Finite (ana h x)}.
Notation "x =l y" := (LFix_EQ x y) : type_scope.
Notation "'l_in'" := L_in (at level 0).
Notation "x =g y" := (GFix_EQ x y) : type_scope.
Notation "'g_in'" := G_in (at level 0).

Module ExInfTree.

  (* Functor & "strict positivisation" *)
  Inductive T A (t : Type) : Type :=
  | C : A -> seq t -> T A t.

  Definition T_OCC (A X : Type) (x : X) (t : T A X) : Prop :=
    match t with
    | C _ l => List.In x l
    end.

  Fixpoint lmap X Y (l : seq X) {struct l}
    : (forall (x : X), List.In x l -> Y) -> seq Y
    := match l return (forall (x : X), List.In x l -> Y) -> seq Y with
       | [::] =>
         fun _ =>
           [::]
       | h :: t =>
         fun fn =>
           fn h (or_introl (erefl h)) :: lmap (fun x p => fn x (or_intror p))
       end.

  Definition t_omap (A X Y : Type) (p : T A X)
    : (forall (x : X), T_OCC x p -> Y) -> T A Y
    := match p return (forall (x : X), T_OCC x p -> Y) -> T A Y with
       | C h l => fun f => C h (lmap f)
       end.

  Definition t_app := fun X Y (x : T X Y) => mk_app (@T_OCC X) x.
  Coercion t_app : T >-> App.

  (* The example *)
  Definition ctree (X : Type) := GFix nat (@T_OCC X).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | S m => n :: downfrom m
    end.

  Definition exn : nat -> ctree nat :=
    ana (fun n => C n (downfrom n)).
End ExInfTree.

Module QSort.
  (* Functor definitions *)
  Inductive F A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  Definition F_OCC A X : X -> F A X -> Prop :=
    fun x p =>
      match p with
      | Empty => False
      | Div _ l r => x = l \/ x = r
      end.

  Definition F_DOM A := DOM (@F_OCC A).

  Definition p_omap A X Y (p : F A X) (f : F_DOM p -> Y) : F A Y :=
    match p as p0 return p = p0 -> F A Y with
    | Empty => fun _ => Empty _ _
    | Div h l r =>
      fun PF =>
        match PF in _ = x return F_DOM x -> F_DOM x -> F A Y with
        | erefl => fun pl pr => Div h (f pl) (f pr)
        end (exist _ _ (or_introl erefl)) (exist _ _ (or_intror erefl))
    end erefl.

  Definition f_app := fun X Y (x : F X Y) => mk_app (@F_OCC X) x.
  Definition f_fun := fun L X Y (x : App L (@F_OCC X) Y) =>
                        p_omap (get (a:=x)).
  Coercion f_app : F >-> App.

  (* The qsort *)
  Definition p_split_ (l : list nat) : F nat (list nat) :=
    match l with
    | [::] => Empty _ _
    | h :: t =>
      Div h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.

  Definition p_merge_ (t : F nat (list nat)) : list nat :=
    match t with
    | Empty => [::]
    | Div h l r => l ++ h :: r
    end.
  Definition p_merge A := p_merge_ \o @f_fun A nat (seq nat).

  Lemma p_split_terminates (l : list nat) : Finite (ana p_split_ l).
  Proof.
    move: {-1}(size l) (leqnn (size l)) => n LE; move: l LE.
    elim: n=>[|n Ih];case=>[|h t]/= LE; rewrite ana_unroll//; constructor=>/=.
    (* by move=> y []->; apply/Ih; rewrite size_filter; apply/(leq_trans (count_size _ _)). *)
  (* Qed. *)
  Admitted.

  Definition p_split : seq nat +> App (seq nat) (@F_OCC nat) (seq nat) :=
    exist _ _ p_split_terminates.

  Definition spl1 (x : list nat) := fana_ (p_split_terminates x).
  Definition spl2 := ana p_split_.
  Definition app A : LFix A _ -> list nat := cata (@p_merge A).

  Definition qsort : list nat -> list nat
    := fhylo (@p_merge (list nat)) p_split.
End QSort.

(* From Coq Require Extraction ExtrHaskellBasic ExtrHaskellNatInteger. *)
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Inline mk_app.
Extraction Inline pmap.
Extraction Inline shape.
Extraction Inline get.
Extraction Inline fmap_dom.
Extraction Inline comp.
Extraction Inline ana.
Extraction Inline fana_.
Extraction Inline cata.
Extraction Inline tcata.
Extraction Inline fhylo.
Extraction Inline fin_hylo.
Extraction Inline QSort.p_merge.
Extraction Inline QSort.p_merge_.
Extraction Inline QSort.p_split.
Extraction Inline QSort.p_split_.
Extraction Inline QSort.p_omap.
Extraction Inline QSort.f_app.
Extraction Inline QSort.f_fun.
Recursive Extraction QSort.
