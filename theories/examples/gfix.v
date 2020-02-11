From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.

Require Import Eqdep_dec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Reserved Notation "x '\pos' F" *)
(*          (at level 70, no associativity, *)
(*           format "'[hv' x '/ '  '\pos'  F ']'"). *)
Reserved Notation "x =l y" (at level 70, no associativity).
Reserved Notation "x =g y" (at level 70, no associativity).
Reserved Notation "x =a/g y" (at level 70, no associativity).
Reserved Notation "x '=1/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/a/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/sval' y" (at level 70, no associativity).
(* Reserved Notation "x +> y" *)
(*          (at level 90, no associativity). *)

CoInductive vec (X : Type) : nat -> Type :=
| vnil : vec X 0
| vcons : X -> forall n, vec X n -> vec X n.+1.

Lemma vcons_inj A (h1 h2 : A) n (t1 t2 : vec A n) :
  vcons h1 t1 = vcons h2 t2 -> h1 = h2 /\ t1 = t2.
Proof. move=>[]; eauto with *. Qed.

Check list_ind.

Lemma vec_ind (A : Type) (P : forall n, vec A n -> Prop)
      (P_nil : P 0 (vnil A))
      (P_cons : forall a n v, P n v -> P n.+1 (vcons a v))
  : forall n v, P n v.
Proof.
  elim=>[|n Ih]; case E: _ / => [|h m t]//.
  move: E t => [<- {m}] t.
  by apply/P_cons/Ih.
Qed.

Lemma uvec X n (v : vec X n) : v = match v with
                                   | vnil => vnil X
                                   | vcons h _ t => vcons h t
                                   end.
Proof. by case: v. Qed.

Definition vmap A B (f : A -> B) : forall n, vec A n -> vec B n :=
  cofix vmap _ x :=
    match x with
    | vnil => vnil B
    | vcons h _ t => vcons (f h) (vmap _ t)
    end.

Definition vmap_fold A (B : nat -> Type)
           (g : A -> forall n, B n -> B n.+1) (z : B 0)
  : forall n, vec A n -> B n
  := fix f n v {struct n} :=
       match v in vec _ n0 return n = n0 -> B n0 with
       | vnil => fun=>z
       | vcons h m t =>
         match n return n = m.+1 -> B m.+1 with
         | 0 => fun pf=>match pf with end
         | n.+1 => fun pf=>match pf with | erefl => fun t=> g h _ (f _ t) end t
         end
       end erefl.

Definition cvec_to_ivec A : forall n, vec A n -> Vector.t A n
  := vmap_fold (Vector.cons A) (Vector.nil A).
Fixpoint ivec_to_cvec A n (v : Vector.t A n)
  := match v with
     | Vector.nil => vnil A
     | Vector.cons h n t => vcons h (ivec_to_cvec t)
     end.

Create HintDb gfix.

Lemma vmap_nil A B (f : A -> B) : vmap f (vnil A) = vnil B.
Proof. by rewrite (uvec (vmap _ _)). Qed.
Hint Resolve vmap_nil : gfix.
Hint Extern 1 =>
match goal with
| [ |- context[vmap _ (vnil _)] ] => rewrite vmap_nil
end : gfix.

Lemma vmap_cons A B (f : A -> B) (h : A) n (t : vec A n) :
  vmap f (vcons h t) = vcons (f h) (vmap f t).
Proof. by rewrite (uvec (vmap _ _)). Qed.
Hint Resolve vmap_cons : gfix.
Hint Extern 1 =>
match goal with
| [ |- context[vmap _ (vcons _ _)] ] => rewrite vmap_cons
end : gfix.

Lemma iso_ci_vec_l A n (v : Vector.t A n) : cvec_to_ivec (ivec_to_cvec v) = v.
Proof. elim: v=>[|h m t Ih]/=; [|rewrite Ih]; by eauto with gfix. Qed.

Lemma iso_ci_vec_r A n (v : vec A n) : ivec_to_cvec (cvec_to_ivec v) = v.
Proof. elim: v=>[|h m t Ih]/=; [|rewrite Ih]; by eauto with gfix. Qed.

Lemma vmap_imap A B (f : A -> B) n (v : Vector.t A n)
  : vmap f (ivec_to_cvec v) = ivec_to_cvec (Vector.map f v).
Proof. elim: v=>[|m h t Ih]/=; [|rewrite vmap_cons Ih]; by eauto with gfix. Qed.

Lemma imap_vmap A B (f : A -> B) n (v : vec A n)
  : Vector.map f (cvec_to_ivec v) = cvec_to_ivec (vmap f v).
Proof. elim: v=>[|m h t Ih]/=; [|rewrite Ih]; by eauto with gfix. Qed.

Lemma rw_comp A B C (f : A -> B) (g : B -> C) (h : A -> C) :
  g \o f =1 h -> forall x, g (f x) = h x.
Proof. by move=>H x; move: (H x)=>/=->. Qed.

Section Definitions.
  (****************************************************************************)
  (** Assumptions and Strict positivisation of functors, using vectors as    **)
  (** "functions with finite support"                                        **)
  (****************************************************************************)
  Parameter F : forall (t : Type),  Type.
  Parameter occ : forall (X : Type), F X -> nat.
  Definition OCC (V : Type -> nat -> Type) Y X (x : F Y) := V X (occ x).
  Definition CApp X := {sh : F unit & OCC vec X sh}.
  Coercion c_shape X (a : CApp X) : F unit := projT1 (P:=OCC vec X) a.
  Coercion c_cont X  (a : CApp X) : OCC vec X (c_shape a)
    := projT2 (P:=OCC vec X) a.

  Definition IApp X := {sh : F unit & OCC Vector.t X sh}.
  Coercion i_shape X (a : IApp X) : F unit := projT1 (P:=OCC Vector.t X) a.
  Coercion i_cont X (a : IApp X) : OCC Vector.t X (i_shape a)
    := projT2 (P:=OCC Vector.t X) a.

  Definition to_capp A (v : IApp A) : CApp A :=
    existT _ (i_shape v) (ivec_to_cvec (i_cont v)).
  Definition to_iapp A (v : CApp A) : IApp A :=
    existT _ (c_shape v) (cvec_to_ivec (c_cont v)).

  Lemma to_capp_iapp A : to_capp (A:= A) \o to_iapp (A := A) =1 id.
  Proof. by case=>sh cn; rewrite /to_capp/to_iapp/= iso_ci_vec_r. Qed.

  Lemma to_iapp_capp A : to_iapp (A:= A) \o to_capp (A := A) =1 id.
  Proof. by case=>sh cn; rewrite /to_capp/to_iapp/= iso_ci_vec_l. Qed.

  Parameter strict : forall X, F X -> IApp X.
  Arguments strict [X] f_x.

  Parameter un_strict : forall X, IApp X -> F X.
  Arguments un_strict [X] a_x.

  Axiom un_strict_strict : forall X, un_strict (X:=X) \o strict (X:=X) =1 id.
  Axiom strict_un_strict : forall X, strict (X:=X) \o un_strict (X:=X) =1 id.

  Inductive CVec_All (A : Type) (P : A -> Prop)
    : forall n, vec A n -> Prop :=
  | vnil_a :
      CVec_All P (vnil A)
  | vcons_a n h t :
      P h ->
      CVec_All P t ->
      CVec_All P (@vcons A h n t)
  .
  Hint Constructors CVec_All : gfix.

  Lemma vec_0_is_nil_ T n (v : vec T n)
    : match n return vec T n -> Prop with
      | O => fun v => v = vnil T
      | _ => fun _ => True
      end v.
  Proof. by case: v. Qed.

  Lemma vec_0_nil T (v : vec T 0) : v = vnil T.
  Proof. by apply/(vec_0_is_nil_ v). Qed.

  Derive Dependent Inversion cvec_all_inv
    with (forall A (P : A -> Prop) n (v : vec A n), CVec_All P v) Sort Prop.

  (* Definition vec_all_cons (A : Type) (P : A -> Prop) h n (v : vec A n) *)
  (*       (x : CVec_All P (vcons h v)) : P h /\ CVec_All P v := *)

  Inductive CVec_R (A B : Type) (P : A -> B -> Prop)
    : forall n m, vec A n -> vec B m -> Prop :=
  | vnil_r :
      CVec_R P (vnil A) (vnil B)
  | vcons_r n m h1 h2 t1 t2 :
      P h1 h2 ->
      CVec_R P t1 t2 ->
      CVec_R P (@vcons A h1 n t1) (@vcons B h2 m t2)
  .
  Hint Constructors CVec_R : gfix.

  Derive Dependent Inversion cvec_r_inv
    with (forall (A B : Type) (P : A -> B -> Prop)
                 n m (v1 : vec A n) (v2 : vec B m), CVec_R P v1 v2)
         Sort Prop.

  Lemma cvec_r_refl (A : Type) n (v : vec A n) : CVec_R eq v v.
  Proof. by elim: v =>[|h m t IH]; eauto with gfix. Qed.

  Lemma vec_nil_cons A B (P : A -> B -> Prop) n (v : vec A n) h
    : ~ CVec_R P (vcons h v) (vnil B).
  Proof. by elim/cvec_r_inv. Qed.

  Definition IVec_R (A B : Type) (P : A -> B -> Prop)
    : forall n m (v1 : Vector.t A n) (v2 : Vector.t B m), Prop
    :=  fix f n m v1 v2 {struct v1}
          := match v1, v2 with
             | Vector.nil, Vector.nil => True
             | Vector.cons h1 n1 t1, Vector.cons h2 n2 t2
               => P h1 h2 /\ f _ _ t1 t2
             | _, _ => False
             end.
  (* Hint Constructors IVec_R : gfix. *)

  Definition IApp_R X Y (r : X -> Y -> Prop) (f : IApp X) (g : IApp Y) :=
    i_shape f = i_shape g /\ IVec_R r (i_cont f) (i_cont g).
  Hint Unfold IApp_R : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context[IApp_R] ] => rewrite /IApp_R/=
  end : gfix.

  Definition CApp_R X Y (r : X -> Y -> Prop) (f : CApp X) (g : CApp Y) :=
    c_shape f = c_shape g /\ CVec_R r (c_cont f) (c_cont g).
  Hint Unfold CApp_R : gfix.
  Hint Extern 1 =>
  match goal with
  | [ |- context[CApp_R] ] => rewrite /CApp_R/=
  end : gfix.

  Lemma IApp_R_mon X Y (x : IApp X) (y : IApp Y) (r r' : X -> Y -> Prop) :
    IApp_R r x y -> (forall ex ey, r ex ey -> r' ex ey) -> IApp_R r' x y.
  Proof.
    rewrite /IApp_R/i_cont/shape/==>[[E_sh E_cn] H]; split=>//.
    move: (projT2 x) (projT2 y) E_cn; rewrite /OCC.
    move: (occ _) (occ _)=> n2 n1 v1 v2.
    by elim: v1 n2 v2=>[|h1 m1 t1 Ih] n2; case=>[|h2 m2 t2]/= []; eauto with gfix.
  Qed.
  Hint Resolve IApp_R_mon : gfix.

  Lemma CApp_R_mon X Y (x : CApp X) (y : CApp Y) (r r' : X -> Y -> Prop) :
    CApp_R r x y -> (forall ex ey, r ex ey -> r' ex ey) -> CApp_R r' x y.
  Proof.
    rewrite /CApp_R/c_cont/shape/==>[[E_sh E_cn] H]; split=>//.
    move: (projT2 x) (projT2 y) E_cn; rewrite /OCC.
    move: (occ _) (occ _)=> n2 n1 v1 v2.
    by elim; eauto with gfix.
  Qed.
  Hint Resolve CApp_R_mon : gfix.

  Definition i_fmap X Y (f : X -> Y) (x : IApp X) : IApp Y
    := existT _ _ (Vector.map f (i_cont x)).
  Hint Unfold i_fmap : gfix.

  Definition c_fmap X Y (f : X -> Y) (x : CApp X) : CApp Y
    := existT _ _ (vmap f (c_cont x)).
  Hint Unfold c_fmap : gfix.

  Lemma fmapI X n : vmap (A:=X) (n:=n) id =1 id.
  Proof. by elim=>[|h t v Ih]; eauto with gfix; rewrite vmap_cons Ih. Qed.

  Lemma fmap_comp X Y Z (f : X -> Y) (g : Y -> Z) n
    : Vector.map (n:=n) g \o Vector.map (n:=n) f =1 Vector.map (n:=n) (g \o f).
  Proof. by elim=>[|h t v Ih]//=; rewrite -Ih. Qed.

  (****************************************************************************)
  (** Greatest fixpoints                                                     **)
  (****************************************************************************)

  CoInductive GFix : Type := G_in {g_out : CApp GFix}.
  Hint Constructors GFix : gfix.

  Notation "'g_in'" := (G_in).

  Lemma g_in_out : g_in \o g_out =1 id.
  Proof. by case. Qed.

  Lemma g_out_in : g_out \o g_in =1 id.
  Proof. by []. Qed.

  Definition GFix_EQ_ (r : GFix -> GFix -> Prop) (gl gr : GFix) : Prop :=
    CApp_R r (g_out gl) (g_out gr).
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

  Lemma GFix_EQ_mon : monotone2 GFix_EQ_.
  Proof. eauto with gfix. Qed.
  Hint Resolve GFix_EQ_mon : gfix.

  Notation "x =g y" := (GFix_EQ x y) : type_scope.
  Notation "x =a/g y" := (CApp_R GFix_EQ x y) : type_scope.

  Lemma gfix_refl r x : paco2 GFix_EQ_ r x x.
  Proof.
    move: x {-1 3}x (erefl x); apply/paco2_acc=> r0 _ CIH.
    move=> x0 x -> {x0}; move: CIH=>/(_ _ _ erefl)-CIH.
    apply/paco2_fold; case: x => a_x; constructor=>//=.
    move: (c_cont a_x); rewrite /OCC; move: (occ a_x)=>n.
    by elim=>[|h m t Ih]; eauto with gfix.
  Qed.

  Lemma gfix_sym r x y : paco2 GFix_EQ_ r x y -> paco2 GFix_EQ_ r y x.
  Admitted.

  Lemma gfix_trans r x y z :
    paco2 GFix_EQ_ r x y ->
    paco2 GFix_EQ_ r y z ->
    paco2 GFix_EQ_ r x z.
  Admitted.

  Notation "f =1/g g" := (forall x, f x =g g x) : type_scope.
  Notation "f =1/a/g g" := (forall x, f x =a/g g x) : type_scope.

  Lemma eq_g_in A (f g : A -> CApp GFix)
    : f =1/a/g g -> g_in \o f =1/g g_in \o g.
  Proof.
    move=> H x/=.
    apply/paco2_fold; rewrite /GFix_EQ_/=.
    apply/(CApp_R_mon (r:=GFix_EQ)); first by apply/H.
    by move=> ex ey E; left.
  Qed.

  Lemma eq_g_out A (f g : A -> GFix)
    : f =1/g g -> g_out \o f =1/a/g g_out \o g.
  Proof.
    move=> H x/=; move: (f x) (g x) (H x) => {H x f g}.
    case=>af; case=>ag/= /(paco2_unfold GFix_EQ_mon)-[/= H0 H1].
    constructor=>//; move: H1; elim; eauto with gfix.
    by move=> n m h1 h2 t1 t2 [E1 _ E2|//]; constructor.
  Qed.

  Lemma eq_gfix A (f g : A -> GFix) : f =1 g -> f =1/g g.
  Proof. by move=> H x; rewrite H; apply/gfix_refl. Qed.

  Definition ana A (h : A -> CApp A) : A -> GFix
    := cofix f := g_in \o c_fmap f \o h.

  Lemma ana_eq A (h : A -> CApp A) :
    g_out \o ana h =1 c_fmap (ana h) \o h.
  Proof. by []. Qed.

  Corollary ana_unroll A (h : A -> CApp A) :
    ana h =1 g_in \o c_fmap (ana h) \o h.
  Proof. by move=>x; rewrite /= (rw_comp (g_in_out) (ana _ _)). Qed.

  Lemma ana_univ_r A (h : A -> CApp A) (f : A -> GFix)
    : g_out \o f =1/a/g c_fmap f \o h -> f =1/g ana h.
  Proof.
    move=> H x.
    move: {-2}(f x) (erefl (f x)) {-2}(ana h x) (erefl (ana h x))=> fx Ef ax Ea.
    set P_CIH := fun x => fx = f x /\ ax = ana h x.
    move: (ex_intro P_CIH x (conj Ef Ea)) => {x Ef Ea}.
    rewrite /P_CIH {P_CIH}; move: fx ax; apply/paco2_acc=>r _ CIH.
    move=> x0 x1 [x] [->->] {x0 x1}.
    move: CIH=> /(_ _ _ (ex_intro _ _ (conj _ _))).
    move=>/(_ _ _ _ erefl erefl)-CIH.

    have {H}H: f =1/g g_in \o c_fmap f \o h
      by move: H=>/eq_g_in-H y; move: (H y)=>/=; rewrite (rw_comp g_in_out).

    move:(paco2_mon r (H x))=>/(_ (fun x y z => False_rect _ z))-H'.
    apply/(gfix_trans H'); rewrite ana_unroll /GFix_EQ_/==>{H' H}.
    apply/paco2_fold; constructor=>//=.
    move: (h x) => [shape]; rewrite /OCC/=; move: (occ shape)=>n {shape x}.
    elim=>[|x m xs Ih]; rewrite ?vmap_nil ?vmap_cons; constructor=>//; right.
    by apply: CIH.
  Qed.

  Lemma ana_univ_l A (h : A -> CApp A) (f : A -> GFix)
    : f =1/g ana h -> g_out \o f =1/a/g c_fmap f \o h.
  Proof.
  Admitted.

  Lemma ana_univ A (h : A -> CApp A) (f : A -> GFix)
    : f =1/g ana h <-> g_out \o f =1/a/g c_fmap f \o h.
  Proof. by split; [apply/ana_univ_l|apply/ana_univ_r]. Qed.

  (****************************************************************************)
  (** Least fixpoints                                                        **)
  (****************************************************************************)

  Inductive LFix : Type := L_in {l_out : IApp LFix}.
  Hint Constructors LFix : gfix.

  Notation "'l_in'" := (L_in).

  Lemma l_in_out : l_in \o l_out =1 id.
  Proof. by case. Qed.

  Lemma l_out_in : l_out \o l_in =1 id.
  Proof. by []. Qed.

  Fixpoint LFix_EQ (gl gr : LFix) {struct gl} : Prop :=
    IApp_R LFix_EQ (l_out gl) (l_out gr).

  Notation "x =l y" := (LFix_EQ x y) : type_scope.

  Definition cata A (g : IApp A -> A) : LFix -> A
    := fix f x := (g \o i_fmap f \o l_out) x.

  Lemma cata_eq A (g : IApp A -> A) :
    cata g \o l_in =1 g \o i_fmap (cata g).
  Proof. by []. Qed.

  Corollary cata_unroll A (g : IApp A -> A) :
    cata g =1 g \o i_fmap (cata g) \o l_out.
  Proof. by move=>x; rewrite -(rw_comp (l_in_out) x)/=. Qed.

  Lemma cata_univ A (g : IApp A -> A) :
    forall (f : LFix -> A), cata g =1 f <-> f \o l_in =1 g \o i_fmap f.
  Admitted.

  (****************************************************************************)
  (** "Finite greatest fixpoints"                                            **)
  (****************************************************************************)

  Lemma nat_dec : forall x y : nat, {x = y} + {x <> y}.
  Proof. by decide equality. Defined.

  Definition Member A (x : A) : forall n : nat, vec A n -> Prop
    := vmap_fold (B:=fun=>Prop) (fun h _ p => x = h \/ p) False.

  Lemma member_vmap A B (y : A) (f : A -> B) n (v : vec A n)
    : Member y v -> Member (f y) (vmap f v).
  Proof. elim: v=>[|h m t Ih]//= [->|/Ih-H]; first (by left); by right. Qed.

  Definition vec_le A n m (v : vec A n) (v' : vec A m)
    := forall (y : A), Member y v -> Member y v'.

  Lemma member_refl A n (v : vec A n) : vec_le v v.
  Proof. by []. Qed.
  Arguments member_refl [A n] v.

  Definition VAll A P n (v : vec A n) := forall y, Member y v -> P y.

  Lemma vec_le_hd A n (v : vec A n) (h : A) m (t : vec A m) :
    vec_le (vcons h t) v -> Member h v.
  Proof. by move=>/(_ h (or_introl erefl)). Qed.

  Lemma vec_le_tl A n (v : vec A n) (h : A) m (t : vec A m) :
    vec_le (vcons h t) v -> vec_le t v.
  Proof. by move=>H x M; apply/H/or_intror/M. Qed.

  Lemma vall_tl A (P : A -> Prop) n (v : vec A n) (h : A) m (t : vec A m) :
    VAll P v -> vec_le (vcons h t) v -> VAll P t.
  Proof. by move=> H1 H2 y M; apply/H1/H2; right. Defined.

  Lemma vall_hd A (P : A -> Prop) n (v : vec A n) (h : A) m (t : vec A m) :
    VAll P v -> vec_le (vcons h t) v -> P h.
  Proof. by move=> H1 H2; apply/H1/H2; left. Defined.

  Inductive Fin : GFix -> Prop :=
  | Fin_fold x : VAll Fin (c_cont x) -> Fin (g_in x).

  Lemma Fin_inv1 p : Fin p -> VAll Fin (c_cont (g_out p)).
  Proof. rewrite /VAll; by case. Defined.

  Definition App A (P : A -> Prop)
    := {x : CApp A | forall y, Member y (c_cont x) -> P y}.

  Definition vecP A (P : A -> Prop) n
    := {x : vec A n | forall y, Member y x -> P y}.

  Definition fmap_ A B (P : A -> Prop)
             (f : forall x, P x -> B) n (v : vec A n) (H : VAll P v) : vec B n
    := (cofix m n (v' : vec A n) (M : vec_le v' v) :=
            match v' in vec _ m return vec_le v' v -> vec B m with
            | vnil => fun=> vnil B
            | vcons h _ t =>
              fun M => vcons (f h (H _ (vec_le_hd M))) (m _ t (vec_le_tl M))
            end M) n v (member_refl v).

  Definition fmap_A A B (P : A -> Prop) (f : forall x, P x -> B) (x : App P)
    : CApp B := existT _ (c_shape (sval x)) (fmap_ f (proj2_sig x)).

  Definition f_out (x : sig Fin) : App Fin :=
    exist _ (g_out (sval x)) (Fin_inv1 (proj2_sig x)).

  Definition f_cata A (g : CApp A -> A) (x : sig Fin) : A
    := (fix f p (FIN : Fin p) {struct FIN} : A
        := (g \o fmap_A f \o f_out) (exist _ _ FIN)) _ (proj2_sig x).

  Definition Terminating A (h : A -> IApp A)
    := { x : A | Fin (ana (to_capp (A:=A) \o h) x) }.

  Definition vmap_P A B (P : A -> Prop)
             (f : forall x, P x -> B) n (v : Vector.t A n) (H : VAll P v) : vec B n
    := (cofix m n (v' : vec A n) (M : vec_le v' v) :=
            match v' in vec _ m return vec_le v' v -> vec B m with
            | vnil => fun=> vnil B
            | vcons h _ t =>
              fun M => vcons (f h (H _ (vec_le_hd M))) (m _ t (vec_le_tl M))
            end M) n v (member_refl v).

  Definition f_ana_ A (h : A -> IApp A) (x : Terminating h) : LFix
    := (fix f x (H : Fin (ana (to_capp (A:=A) \o h) x)) {struct H} :=
          l_in \o i_fmap
       )

    (* move: H. *)
    (* rewrite ana_unroll/==>/Fin_inv1/=. *)
    (* move: (h x)=> [sh]; rewrite /OCC/==>v H. *)
    (* apply: l_in. *)
    (* apply/(existT _ sh). *)
    (* rewrite /OCC. *)
    (* have: *)
    (*   (forall y, Member y (ivec_to_cvec v) -> Member y (ivec_to_cvec v)) *)
    (*   by []. *)
    (* move: {-2} v. *)
    (* move: {-4 5}(occ sh) => m. *)
    (* elim=>/=. *)
    (* move=> _. *)
    (* apply: Vector.nil. *)
    (* move=> h0 n t Ih H'. *)
    (* apply: Vector.cons. *)
    (* apply: f_ana_. *)
    (* apply: H=>/={Ih}. *)
    (* apply/member_vmap/H'; left; reflexivity. *)
    (* by apply/Ih=>y M; apply/H'; right. *)
  Defined.
    :=
    := cofix f := g_in \o f_map_ f \o g.

  Inductive Fin_ana A (P : A -> Prop) (g : sig P -> App P) : sig P -> Prop :=
  | Ana_fold x : VAll (Fin_ana g) (proj2_sig (g x)) -> Fin_ana g x
  .

  Lemma Ana_inv1 A (P : A -> Prop) (g : sig P -> App P) (x : sig P)
    : Fin_ana g x -> VAllP (Fin_ana g) (proj2_sig (g x)).
  Proof. by case. Defined.

  Derive Dependent Inversion VAllP_inv
    with (forall A (P : A -> Prop) (Q : sig P -> Prop)
                 (g : sig P -> App P) n (v : vec A n) (H : VAll P v),
             VAllP Q H)
         Sort Prop.

  (* Finiteness: *)
  Definition f_ana A (P : A -> Prop) (g : sig P -> App P)
             (H : forall (x : sig P), Fin (f_ana_ g x))
             (x : sig P) : Fix := exist _ _ (H x).

  Fixpoint Member A x n (v : vec A n) {struct n} :=
    match v in vec _ m return Prop with
    | vnil => False
    | vcons h r t =>
      match n with
      |
      x = h \/ Member x t
    end.

  Definition VAll A (P : A -> Prop) n (v : vec A n) :=



  Definition Fix := sig Fin.
  (* Definition App A (P : A -> Prop) := {x : CApp A | VAll P (c_cont x) }. *)

  Definition f_in (x : CApp Fix) : Fix :=
    let gf := existT _ (c_shape x) (sval (p_unzip (c_cont x)))
    in exist _ _ (Fin_fold (x:=gf) (proj2_sig (p_unzip (c_cont x)))).
  Definition f_out (x : Fix) : CApp Fix :=
    existT _ (c_shape (g_out (sval x))) (p_zip (Fin_inv1 (proj2_sig x))).

  Definition fmap A B (P : A -> Prop) (Q : B -> Prop)
             (f : forall x, P x -> sig Q)
    : forall n (x : vec A n), VAll P x -> { v : vec B n | VAll Q v }
    := fix m n (v : vec A n) (H : VAll P v) {struct H} :=
         match v as v0 in vec _ m
               return existT _  _ v = existT _ _ v0 ->
                      { v : vec B m | VAll Q v }
         with
         | vnil => fun => exist _ _ (P_nil Q)
         | vcons h r t =>
           fun E =>
             exist _ _ (P_cons (proj2_sig (f h (VAll_inv1 H E)))
                               (proj2_sig (m r t (VAll_inv2 H E))))
         end erefl.


  Definition f_cata A (P : A -> Prop) (g : CApp (sig P) -> sig P) (x : Fix) : sig P
    := (fix f p (FIN : Fin p) {struct FIN} : sig P
         := (g \o fmap f \o f_out) (exist Fin p FIN)) _ (proj2_sig x).

  Definition fmap_ A B (P : A -> Prop)
             (f : sig P -> B)
    : forall n (x : vec A n), VAll P x -> vec B n
    := cofix m n (v : vec A n) (H : VAll P v)  :=
         match v as v0 in vec _ m
               return existT _  _ v = existT _ _ v0 -> vec B m
         with
         | vnil => fun => vnil B
         | vcons h r t =>
           fun E => vcons (f (exist _ _ (VAll_inv1 H E))) (m r t (VAll_inv2 H E))
         end erefl.

  Definition f_map_ A B (P : A -> Prop)
             (f : sig P -> B) (x : App P) : CApp B
    := existT _ (c_shape (sval x)) (fmap_ f (proj2_sig x)).

  Definition f_map A B (P : A -> Prop) (Q : B -> Prop)
             (f : forall x, P x -> sig Q) (x : App P) : App Q
    := exist _ (existT _ (c_shape (sval x)) _) (projT2 (fmap f (proj2_sig x))).

  Definition f_cata A (P : A -> Prop) (g : App P -> sig P) (x : Fix) : sig P
    := (fix f p (FIN : Fin p) {struct FIN} : sig P
         := (g \o f_map f \o f_out) (exist Fin p FIN)) _ (proj2_sig x).

  (* Potentially infinite *)
  Definition f_ana_ A (P : A -> Prop) (g : sig P -> App P) : sig P -> GFix
    := cofix f := g_in \o f_map_ f \o g.

  Inductive Fin_ana A (P : A -> Prop) (g : sig P -> App P) : sig P -> Prop :=
  | Ana_fold x : VAll (Fin_ana g) (proj2_sig (g x)) -> Fin_ana g x
  .

  Lemma Ana_inv1 A (P : A -> Prop) (g : sig P -> App P) (x : sig P)
    : Fin_ana g x -> VAllP (Fin_ana g) (proj2_sig (g x)).
  Proof. by case. Defined.

  Derive Dependent Inversion VAllP_inv
    with (forall A (P : A -> Prop) (Q : sig P -> Prop)
                 (g : sig P -> App P) n (v : vec A n) (H : VAll P v),
             VAllP Q H)
         Sort Prop.

  (* Finiteness: *)
  Definition f_ana A (P : A -> Prop) (g : sig P -> App P)
             (H : forall (x : sig P), Fin (f_ana_ g x))
             (x : sig P) : Fix := exist _ _ (H x).

  Definition f_hylo_comp B A (P : B -> Prop) (Q : A -> Prop)
             (g : App P -> sig P) (h : sig Q -> App Q)
             (H : forall (x : sig Q), Fin (f_ana_ h x)) : sig Q -> sig P
    := f_cata g \o f_ana H.

  Definition FIN_ANA A (P : A -> Prop) (h : sig P -> App P)
    := (fun (x : A) => sig (fun (H : P x) => Fin (f_ana_ h (exist _ _ H)))).

  Definition forget_fin A (P : A -> Prop) (h : sig P -> App P)
             (x : sig (FIN_ANA h)) : sig P
    := exist _ (sval x) (sval (proj2_sig x)).

  Definition f_ana_unroll_ A (P : A -> Prop) (h : sig P -> App P) :
    f_ana_ h =1 g_in \o f_map_ (f_ana_ h) \o h.
  Proof. by move=>x/=; rewrite (rw_comp (g_in_out) (f_ana_ _ _)). Defined.

  Definition wrap_fin A (Q : A -> Prop) (h : sig Q -> App Q)
             (x : sig (FIN_ANA h)) : App (FIN_ANA h).
    Print FIN_ANA.
    move: x=> [x [Q_x]].
    rewrite f_ana_unroll_/=. =>/Fin_inv1.
    rewrite (rw_comp g_out_in).
    (* exist (fun x => VAll (FIN_ANA h) (c_cont x)) (sval (h (forget_fin x))) (Fin_inv1 (proj2_sig (proj2_sig x))). *)

  Definition f_hylo B A (P : B -> Prop) (Q : A -> Prop)
             (g : App P -> sig P) (h : sig Q -> App Q)
             (x : sig Q) (H : Fin (f_ana_ h x)) : sig P
    := (fix f (x : sig Q) (FIN : Fin (f_ana_ h x)) {struct FIN} : sig P
         := (g \o f_map f \o h) (exist Fin x FIN)) _ H.

  Definition f_hylo B A (P : B -> Prop) (Q : A -> Prop)
             (g : App P -> sig P) (h : sig Q -> App Q)
             (x : sig Q) (H : forall (x : sig Q), Fin (f_ana_ h x)) : sig P
    := (fix f x (FIN : Fin (f_ana_ h x)) {struct FIN} : sig P
         := (g \o f_map f \o h)) x H.


  (* Redo with "finite anamorphisms", and without the properties *)

  Definition f_cata A (P : A -> Prop) (g : App P -> sig P) (x : Fix) : sig P
    := (fix f p (FIN : Fin p) {struct FIN} : sig P
         := (g \o f_map f \o f_out) (exist Fin p FIN)) _ (proj2_sig x).

  Notation "f =1/sval g" := (forall x, sval (f x) = sval (g x)).

  Lemma f_in_out : f_in \o f_out =1/sval id.
  Proof. by case; case. Qed.

  Lemma f_out_in : f_out \o f_in =1/sval id.
  Proof. by []. Qed.

  (* TODO *)
  (* Definition gfix_to_lfix : Fix -> LFix := f_cata l_in. *)
  (* Definition lfix_to_gfix : LFix -> Fix := cata lg_in. *)

  Definition fin_ana A (h : A +> App A) : A -> LFix :=
    fun x => fana_ (proj2_sig h x).

  Definition t_ana A (h : A +> App A) : A -> Fix :=
    fun x => exist _ _ (proj2_sig h x).

  Definition fin_hylo_ A B (g : App B -> B) (h : A -> App A)
    : forall (x : A) (F : Fin (ana h x)), B
    := fix f x F := g (fmap_dom (fun y => f (get y) (Fin_inv2 F y))).

  Definition fin_hylo A B (g : App B -> B) (h : A -> App A)
    : forall (x : A) (F : Fin (ana h x)), B
    := fix f x F := g (fmap_dom (fun y => f (get y) (Fin_inv2 F y))).

  Goal forall A B (g : App B -> B) (h : A -> App A) (x : A) (FIN : Fin (ana h x)),
      fin_hylo g FIN = g (fmap_dom (fun y => fin_hylo g (Fin_inv2 FIN y))).
    move=> A B g h x.
    move=> A B g h x.
    move: (ana h x)

  Definition fhylo A B (g : App B -> B) (h : A +> App A)
    : A -> B := fun x => fin_hylo g (proj2_sig h x).

  Goal forall A B (g : App B -> B) (h : A +> App A),
      fhylo g h =1 g \o fmap (fhylo g h) \o sval h.
  Proof.
    move=>A B g [h FIN]/=; rewrite /fhylo/==>x/=.
    case: (FIN x).
End Definitions.

Notation "A +> B" := {h : A -> B | forall x, Fin (ana h x)}.
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

  Lemma p_split_terminates (l : list nat) : Fin (ana p_split_ l).
  Proof.
    move: {-1}(size l) (leqnn (size l)) => n LE; move: l LE.
    elim: n=>[|n Ih];case=>[|h t]/= LE; rewrite ana_unroll//; constructor=>[[//=]].
    by move=> y []->; apply/Ih; rewrite size_filter; apply/(leq_trans (count_size _ _)).
  Qed.

  Definition p_split : seq nat +> App (seq nat) (@F_OCC nat) (seq nat) :=
    exist _ _ p_split_terminates.

  Definition spl1 (x : list nat) := fana_ (p_split_terminates x).
  Definition spl2 := ana p_split_.
  Definition app A : LFix A _ -> list nat := cata (@p_merge A).

  Definition qsort : list nat -> list nat
    := fun x => fhylo (@p_merge (list nat)) p_split x.
End QSort.

(* From Coq Require Extraction ExtrHaskellBasic ExtrHaskellNatInteger. *)
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction Inline mk_app.
Extraction Inline pmap.
Extraction Inline shape.
Extraction Inline get.
Extraction Inline fmap_dom.
Extraction Inline fmap.
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
Print QSort.
Recursive Extraction QSort.
