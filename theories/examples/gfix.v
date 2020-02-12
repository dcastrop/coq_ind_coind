From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.

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

Definition VAll A P n := fun (v : vec A n) => forall y, Member y v -> P y.

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

Definition fmap_ A B (P : A -> Prop)
           (f : forall x, P x -> B) n (v : vec A n) (H : VAll P v) : vec B n
  := (cofix m n (v' : vec A n) (M : vec_le v' v) :=
          match v' in vec _ m return vec_le v' v -> vec B m with
          | vnil => fun=> vnil B
          | vcons h _ t =>
            fun M => vcons (f _ (H _ (vec_le_hd M)))
                           (m _ t (vec_le_tl M))
          end M) n v (member_refl v).

Section Definitions.
  (****************************************************************************)
  (** Assumptions and Strict positivisation of functors, using vectors as    **)
  (** "functions with finite support"                                        **)
  (****************************************************************************)
  Context (F : Type). (* Shape *)
  Context (occ : F -> nat). (* Number of positions *)
  Definition OCC (V : Type -> nat -> Type) X (x : F) := V X (occ x).
  Definition CApp X := {sh : F & OCC vec X sh}.
  Coercion c_shape X (a : CApp X) : F := projT1 (P:=OCC vec X) a.
  Coercion c_cont X  (a : CApp X) : OCC vec X (c_shape a)
    := projT2 (P:=OCC vec X) a.

  Definition IApp X := {sh : F & OCC Vector.t X sh}.
  Coercion i_shape X (a : IApp X) : F := projT1 (P:=OCC Vector.t X) a.
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

  (* Parameter strict : forall X, F X -> IApp X. *)
  (* Arguments strict [X] f_x. *)

  (* Parameter un_strict : forall X, IApp X -> F X. *)
  (* Arguments un_strict [X] a_x. *)

  (* Axiom un_strict_strict : forall X, un_strict (X:=X) \o strict (X:=X) =1 id. *)
  (* Axiom strict_un_strict : forall X, strict (X:=X) \o un_strict (X:=X) =1 id. *)

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

  CoInductive GFix : Type
    := G_fold (sh : F) (rec : vec GFix (occ sh)).
  Hint Constructors GFix : gfix.
  Definition g_shape x := match x with | G_fold f _ => f end.
  Definition g_cont x : vec GFix (occ (g_shape x)) :=
    match x with | G_fold _ f => f end.

  Definition g_in  x := G_fold (c_cont x).
  Definition g_out x : CApp GFix := existT _ _ (g_cont x).

  Lemma g_in_out : g_in \o g_out =1 id.
  Proof. by case. Defined.

  Lemma g_out_in : g_out \o g_in =1 id.
  Proof. by case. Qed.

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
    apply/paco2_fold; case: x => a_x v; constructor=>//=.
    move: (occ a_x) v=>n.
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
    case=>sh_f c_f; case=>sh_g c_g/= /(paco2_unfold GFix_EQ_mon)-[/= E H1].
    constructor=>//=; elim: H1; eauto with gfix.
    by move=> n m h1 h2 t1 t2 [E1 _ E2|//]; constructor.
  Qed.

  Lemma eq_gfix A (f g : A -> GFix) : f =1 g -> f =1/g g.
  Proof. by move=> H x; rewrite H; apply/gfix_refl. Qed.

  Definition ana A (h : A -> CApp A) : A -> GFix
    := cofix f x :=
         match h x with
         | existT sh_x c_x => @G_fold sh_x (vmap f c_x)
         end.

  Lemma ana_eq A (h : A -> CApp A) :
    g_out \o ana h =1 c_fmap (ana h) \o h.
  Proof. move=>x; rewrite /g_out/=; by case: (h x)=>/=. Qed.

  Corollary ana_unroll A (h : A -> CApp A) :
    ana h =1 g_in \o c_fmap (ana h) \o h.
  Proof.
    move=>x; rewrite -(rw_comp g_in_out (ana _ _))/=.
    by rewrite (rw_comp (ana_eq _) _).
  Qed.

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

  Inductive LFix : Type
    := L_fold (sh : F) (c : Vector.t LFix (occ sh)).
  Hint Constructors LFix : gfix.
  Definition l_shape x := match x with | L_fold x _ => x end.
  Definition l_cont x : Vector.t LFix (occ (l_shape x))
    := match x with | L_fold _ x => x end.

  Definition l_in (x : IApp LFix) : LFix :=
    match x with | existT _ c => L_fold c end.

  Definition l_out (x : LFix) : IApp LFix :=
    match x with | L_fold _ c => existT _ _ c end.

  Lemma l_in_out : l_in \o l_out =1 id.
  Proof. by case. Qed.

  Lemma l_out_in : l_out \o l_in =1 id.
  Proof. by case. Qed.

  Fixpoint LFix_EQ (f g : LFix) {struct f} : Prop :=
    l_shape f = l_shape g /\ IVec_R LFix_EQ (l_cont f) (l_cont g).

  Notation "x =l y" := (LFix_EQ x y) : type_scope.

  Definition cata A (g : IApp A -> A) : LFix -> A
    := fix f x :=
         match x with
         | L_fold sh_x c_x => g (existT _ sh_x (Vector.map f c_x))
         end.

  Lemma cata_eq A (g : IApp A -> A) :
    cata g \o l_in =1 g \o i_fmap (cata g).
  Proof. by move=>[sh_x c_x]/=; rewrite /i_fmap/=. Qed.

  Corollary cata_unroll A (g : IApp A -> A) :
    cata g =1 g \o i_fmap (cata g) \o l_out.
  Proof.
    move=> x; rewrite -[in LHS](rw_comp l_in_out x).
    by rewrite -[cata g _]/((cata g \o l_in) (l_out x)) cata_eq.
  Qed.

  Lemma cata_univ A (g : IApp A -> A) :
    forall (f : LFix -> A), cata g =1 f <-> f \o l_in =1 g \o i_fmap f.
  Admitted.

  (****************************************************************************)
  (** "Terminating anamorphisms"                                             **)
  (****************************************************************************)

  Inductive Fin : GFix -> Prop :=
  | Fin_fold x : VAll Fin (c_cont x) -> Fin (g_in x).

  Lemma Fin_inv1 p : Fin p -> VAll Fin (c_cont (g_out p)).
  Proof. rewrite /VAll; by case. Defined.

  Definition App A (P : A -> Prop)
    := {x : CApp A | forall y, Member y (c_cont x) -> P y}.

  Definition vecP A (P : A -> Prop) n
    := {x : vec A n | forall y, Member y x -> P y}.

  (* Terminating anamorphisms *)
  Definition Term A (h : A -> IApp A) : A -> Prop
    := fun x => Fin (ana (to_capp (A:=A) \o h) x).

  Definition IAll A (P : A -> Prop) :=
    fun n (x : Vector.t A n) => forall e, Member e (ivec_to_cvec x) -> P e.

  Inductive FinF A (h : A -> IApp A) : A -> Prop :=
  | FinF_fold x : IAll (FinF h) (i_cont (h x)) -> FinF h x.

  Lemma FinF_inv A (h : A -> IApp A) x : FinF h x -> IAll (FinF h) (i_cont (h x)).
  Proof. by case. Defined.

  Definition wrap A (h : A -> IApp A)
    : sig (FinF h) -> {x : IApp A | IAll (FinF h) (i_cont x)}
    := fun x =>
         exist (fun x => IAll (FinF h) (i_cont x)) (h (sval x))
               (FinF_inv (proj2_sig x)).
  Arguments wrap [A] h.

  Definition ivec_le A m n (v' : Vector.t A m) (v : Vector.t A n) :=
    vec_le (ivec_to_cvec v') (ivec_to_cvec v).

  Definition i_fmap' A B (P : A -> Prop) (f : forall p : A, P p -> B)
             m (v : Vector.t A m) (H : IAll P v) :
    forall n (v' : Vector.t A n), ivec_le v' v -> Vector.t B n
    := fix m n (v' : Vector.t A n) :=
         match v' in Vector.t _ m
               return ivec_le v' v -> Vector.t B m with
         | Vector.nil => fun=> Vector.nil _
         | Vector.cons h _ t =>
           fun M => Vector.cons _ (f _ (H _ (vec_le_hd M)))
                                _ (m _ t (vec_le_tl M))
         end.

  Definition i_fmap_ A B (P : A -> Prop) (f : forall p : A, P p -> B)
             n (v : Vector.t A n) (H : IAll P v) : Vector.t B n
    := i_fmap' f H (member_refl (ivec_to_cvec v)).

  Definition fmap_I A B (P : A -> Prop) (f : forall p, P p -> B)
             (x : sig (fun x => IAll P (i_cont x))) : IApp B
    := existT _ _ (i_fmap_ f (proj2_sig x)).

  Definition f_ana_ A (h : A -> IApp A) : forall (x : A), FinF h x -> LFix
    := fix f x H := (l_in \o fmap_I f \o wrap h) (exist _ _ H).
  Arguments f_ana_ [A] h [x].

  Lemma f_ana_irr A (h : A -> IApp A) (x : A) (F1 F2 : FinF h x) :
      f_ana_ h F1 = f_ana_ h F2.
  Proof.
    move: x F1 F2; fix Ih 2; move=> x [{}x H1] F2; move:F2 H1=>[{}x H2] H1/=.
    congr L_fold; rewrite /i_fmap_/=.
    move: {1 4 6}(i_cont (h x)) (member_refl _).
    rewrite /OCC; move: {-3 5 7 9} (occ (h x)) => n.
    elim=>[|hv mv tv IhL]//= M.
    by rewrite (Ih _ (H1 _ _) (H2 _ (vec_le_hd M))) IhL.
  Qed.

  Definition f_ana A (h : A -> IApp A) (T : forall x, FinF h x) x : LFix
    := f_ana_ h (T x).

  Lemma f_ana_unr A (h : A -> IApp A) (T : forall x, FinF h x) :
      f_ana T =1 l_in \o i_fmap (f_ana T) \o h.
  Proof.
    rewrite /f_ana/wrap/==>x.
    move: (T x)=> [{}x ALL]/=; congr L_fold.
    rewrite /fmap_I/i_fmap/i_fmap_/=.
    move: {-2 3}(i_cont (h x)) (member_refl _).
    rewrite /OCC/=; move: {-3 5 7}(occ (h x))=>n.
    by elim=>[|hv mv tv Ih]//= H; rewrite Ih f_ana_irr.
  Qed.

  Lemma FinF_inv1 A (h : A -> IApp A) (sh : F) (c : OCC Vector.t A sh) (x : A)
        : FinF h x -> existT _ sh c = h x -> IAll (FinF h) c.
  Proof.
    case=> {}x H E e M; apply/H.
    by move: E M=><-/=.
  Defined.

  Definition f_hylo_ A B (g : IApp B -> B) (h : A -> IApp A)
    : forall x, FinF h x -> B
    := fix f x H :=
         match h x as h0 return h0 = h x -> B with
         | existT sh_x c_x => fun E => g (existT _ sh_x (i_fmap_ f (FinF_inv1 H E)))
         end erefl.
  Arguments f_hylo_ [A B] g h [x] F.

  Lemma f_hylo_irr A B (g : IApp B -> B) (h : A -> IApp A)
    : forall x (F1 F2 : FinF h x), f_hylo_ g h F1 = f_hylo_ g h F2.
  Proof.
  Admitted.
  (*   fix Ih 2; move=> x. *)
  (*   case=>[{}x H1] F2; case: F2 H1=>[{}x H2] H1/=; congr g. *)
  (*   rewrite /fmap_I/wrap/=; congr existT; rewrite /i_fmap_. *)
  (*   move: {1 4 6}(i_cont (h x)) (member_refl _). *)
  (*   rewrite /OCC; move: {-3 5 7 9} (occ (h x)) => n. *)
  (*   elim=>[|hv mv tv IhL]//= M. *)
  (*   by rewrite IhL (Ih _ (H1 _ (vec_le_hd M)) (H2 _ (vec_le_hd M))). *)
  (* Qed. *)

  Definition f_hylo A B (g : IApp B -> B) (h : A -> IApp A)
             (T : forall x, FinF h x)
    : A -> B := fun x => f_hylo_ g h (T x).
  Arguments f_hylo [A B] g h T.

  Lemma f_hylo_unr A B (g : IApp B -> B) (h : A -> IApp A)
        (T : forall x, FinF h x)
    : f_hylo g h T =1 g \o i_fmap (f_hylo g h T) \o h.
  Proof.
  Admitted.
  (*   rewrite /f_hylo/wrap/==>x. *)
  (*   move: (T x)=> [{}x ALL]/=; congr g. *)
  (*   rewrite /fmap_I/i_fmap/i_fmap_/=; congr existT. *)
  (*   move: {-2 3}(i_cont (h x)) (member_refl _). *)
  (*   rewrite /OCC/=; move: {-3 5 7}(occ (h x))=>n. *)
  (*   by elim=>[|hv mv tv Ih]//= H; rewrite Ih f_hylo_irr. *)
  (* Qed. *)

  (****************************************************************************)
  (** "Finite Greatest Fixpoints"                                            **)
  (****************************************************************************)

  Definition fmap A B (P : A -> Prop) (f : sig P -> B) (x : App P)
    : CApp B
    := existT _ _ (fmap_ (fun p F => f (exist _ p F)) (proj2_sig x)).

  Definition fmap_A A B (P : A -> Prop) (f : forall p, P p -> B) (x : App P)
    : CApp B := existT _ _ (fmap_ f (proj2_sig x)).

  Lemma fmap_P A B (P : A -> Prop) (Q : B -> Prop) (f : forall p, P p -> B)
        (H : forall p (H : P p), Q (f p H)) (x : App P)
    : VAll Q (c_cont (fmap_A f x)).
  Proof.
    rewrite /VAll; case: x=>[[]]; rewrite /OCC/=/fmap_=> shape cont P_cont y.
    set map := cofix m n v' M : vec B n := _.
    move: {-3}(occ shape) {1 3}(cont) (member_refl cont) => n.
    by elim=>//= h m t Ih M [->|/Ih]//.
  Defined.
  Arguments fmap_P [A B P Q f] H x.

  Definition f_out (x : sig Fin) : App Fin :=
    exist _ (g_out (sval x)) (Fin_inv1 (proj2_sig x)).

  Definition f_cata A (g : CApp A -> A) : {x : GFix | Fin x} -> A
    := fun x =>
         (fix f p (FIN : Fin p) {struct FIN} : A
          := (g \o fmap_A f \o f_out) (exist _ _ FIN)
         ) _ (proj2_sig x).

  Lemma f_cata_unr A (g : CApp A -> A)
    : f_cata g =1 g \o fmap (f_cata g) \o f_out.
  Proof. by move=>[x] []. Qed.

  Lemma p_cata A (P : A -> Prop) (g : CApp A -> A)
        (H : forall p, VAll P (c_cont p) -> P (g p))
    : forall (x : GFix) (FIN : Fin x), P (f_cata g (exist _ _ FIN)).
  Proof.
    fix IH 2; move=>x FIN.
    rewrite f_cata_unr; apply/H; apply: fmap_P; apply: IH.
  Qed.

End Definitions.

Notation "x =l y" := (LFix_EQ x y) : type_scope.
Notation "x =g y" := (GFix_EQ x y) : type_scope.
(* Notation "'g_in'" := G_in (at level 0). *)

Module ExInfTree.

  (* Functor shape *)
  Inductive t A : Type :=
  | C (x : A) (n : nat) : t A.

  Fixpoint t_occ A (t : t A) :=
    match t with
    | C _ l => l
    end.
  Arguments t_occ A t : clear implicits.

  (* The example *)
  Definition ctree (X : Type) := GFix (t_occ X).

  Fixpoint downfrom (n : nat) : vec nat n :=
    match n with
    | 0 => vnil _
    | S m => vcons n (downfrom m)
    end.

  Definition tree_gen (n : nat) : CApp (t_occ nat) nat :=
    existT _ (C (2 *n) _) (downfrom n).

  Definition exn : nat -> ctree nat :=
    ana tree_gen.
End ExInfTree.

From Coq Require Extraction.
(* Unset Extraction SafeImplicits. *)
Extract Inductive sigT => "(*)"  [ "(,)" ].
Extraction Implicit vcons [n].
Extraction Implicit vmap [n].
(* Extraction Inline projT1. *)
(* Extraction Inline projT2. *)
Extraction Inline ana.
Extraction Inline comp.
Extraction Inline c_shape.
Extraction Inline c_cont.
Extraction Inline c_fmap.
Extraction Inline ExInfTree.t_occ.
Extraction Inline ExInfTree.tree_gen.
Extraction ExInfTree.

Module QSort.
  (* Functor definitions *)
  Inductive tree' A := Empty | Div (PIVOT : A).

  Definition tree_occ A (x : tree' A) : nat :=
    match x with
    | Empty => 0
    | Div _ => 2
    end.
  Arguments tree_occ A x : clear implicits.

  Definition empty A : IApp (tree_occ nat) A
    := existT _ (Empty _) (Vector.nil _).
  Definition node X n (l r : X) : IApp (tree_occ nat) X
    := existT _ (Div n) (Vector.cons _ l _ (Vector.cons _ r _ (Vector.nil _))).

  Definition getl (A X : Type) (h : A) (l : Vector.t X (tree_occ _ (Div h)))
    : X := match l in Vector.t _ n return n = 2 -> X with
           | Vector.nil => fun E => match E with end
           | Vector.cons h _ _ => fun=>h
           end erefl.

  Definition getr (A X : Type) (h : A) (l : Vector.t X (tree_occ _ (Div h)))
    : X := match l in Vector.t _ n return n = 2 -> X with
           | Vector.nil => fun E => match E with end
           | Vector.cons _ m v =>
             match v in Vector.t _ m return m.+1 = 2 -> X with
             | Vector.nil => fun E => match E with end
             | Vector.cons h _ _ => fun => h
             end
           end erefl.

  (* The qsort *)
  Definition p_split (l : list nat) : IApp (tree_occ nat) (seq nat) :=
    match l with
    | [::] => empty _
    | h :: t =>
      node h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.

  Print Vector.

  Definition p_merge (t : IApp (tree_occ nat) (seq nat)) : seq nat
    := let: existT sh_t c_t := t in
       match sh_t return Vector.t (seq nat) (tree_occ _ sh_t) -> seq nat with
       | Empty => fun=>[::]
       | Div h => fun c=> getl c ++ h :: getr c
       end c_t.

  Lemma p_split_terminates (l : list nat) : FinF p_split l.
  Proof.
    move: {-1}(size l) (leqnn (size l)) => n; move: l.
    elim: n=>[|n Ih] [|h t]/= LE; eauto with gfix; constructor=>/=.
    - by move=> x [].
    - by rewrite ltn0 in LE.
    - move=> e/= [->|[->|//]]; apply/Ih.
      + rewrite size_filter.
        by apply: (leq_ltn_trans (count_size _ t) LE).
      + rewrite size_filter.
        by apply: (leq_ltn_trans (count_size _ t) LE).
  Qed.

  Definition spl1 := f_ana p_split_terminates.
  (* Definition spl2 := ana p_split_. *)
  Definition app : LFix (tree_occ nat) -> seq nat := cata p_merge.

  Definition qsort : list nat -> list nat := f_hylo p_merge p_split_terminates.
End QSort.

(* From Coq Require Extraction ExtrHaskellBasic ExtrHaskellNatInteger. *)
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Set Extraction TypeExpand.
Set Extraction Flag 2047.
Extraction Implicit Vector.cons [n].
Extraction Implicit Vector.map [n].
Extraction Implicit i_fmap' [m n].
Extraction Implicit i_fmap_ [n].
Extract Inductive Vector.t => "list" [ "[]" "(::)" ].
Extraction Inline projT1.
Extraction Inline projT2.
Extraction Inline pmap.
Extraction Inline shape.
Extraction Inline fmap.
Extraction Inline comp.
Extraction Inline ana.
Extraction Inline f_ana.
Extraction Inline cata.
Extraction Inline f_cata.
Extraction Inline f_hylo.
Extraction Inline f_hylo_.
Extraction Inline fmap_I.
Extraction Inline wrap.
Extraction Inline i_cont.
Extraction Inline i_shape.
Extraction Inline i_fmap_.
Extraction Inline i_fmap'.
Extraction Inline Vector.hd.
Extraction Inline Vector.tl.
Extraction Inline Vector.caseS.
Extraction Inline QSort.tree_occ.
Extraction Inline QSort.empty.
Extraction Inline QSort.node.
Extraction Inline QSort.p_merge.
Extraction Inline QSort.p_split.
Extraction Implicit QSort.getl [h].
Extraction Implicit QSort.getr [h].
(* Unset Extraction SafeImplicits. *)
Recursive Extraction QSort.
