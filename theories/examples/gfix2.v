From mathcomp Require Import all_ssreflect.
From Paco Require Import paco paco2.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "x =l y" (at level 70, no associativity).
Reserved Notation "x =g y" (at level 70, no associativity).
Reserved Notation "x =a/g y" (at level 70, no associativity).
Reserved Notation "x '=1/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/a' y" (at level 70, no associativity).
Reserved Notation "x '=1/a/g' y" (at level 70, no associativity).
Reserved Notation "x '=1/sval' y" (at level 70, no associativity).

Section Definitions.
  (****************************************************************************)
  (** Assumptions and Strict positivisation of functors                      **)
  (****************************************************************************)

  Structure equivalence A :=
    mkEquiv { eqRel : A -> A -> Prop;
              e_refl : forall x, eqRel x x;
              e_sym : forall x y, eqRel x y -> eqRel y x;
              e_trans : forall x y z, eqRel x y -> eqRel y z -> eqRel x z;
            }.

  Structure TyEq :=
    { Ty : Type;
      Eq : equivalence Ty
    }.
  Coercion getTy (T : TyEq) := Ty T.

  Add Parametric Relation (A: TyEq) : A (eqRel (Eq A))
      reflexivity proved by (@e_refl A (Eq A))
      symmetry proved by (@e_sym A (Eq A))
      transitivity proved by (@e_trans A (Eq A))
        as ExtEq.

  Reserved Notation "f =e g" (at level 70, no associativity).
  Reserved Notation "f =1e g" (at level 70, no associativity).
  Notation "f =e g" := (eqRel (Eq _) f g).
  Notation "f =1e g" := (forall x, eqRel (Eq _) (f x) (g x)).

  Definition extEq (A : TyEq) (B : Type) : equivalence (B -> A).
  Proof.
    apply: (@mkEquiv _ (fun f g =>forall x, eqRel (Eq A) (f x) (g x))).
    - by move=>f x; apply: e_refl.
    - by move=>f g H x; apply: e_sym.
    - by move=>f g h Hf Hg x; apply: e_trans.
  Defined.

  Structure Functor :=
    { Shape : Type;
      Position : Type;
      (** Is position valid in shape? *)
      dom : Shape -> Position -> bool;
    }.

  Definition Cont F (sh : Shape F) (X : TyEq)
    := {| Ty := sig (dom sh) -> X; Eq := extEq X _ |}.

  Definition AppT F (X : Type) := {sh : Shape F & sig (dom sh) -> X}.

  Lemma cont_irr F X (sh : Shape F) (f : sig (dom sh) -> X)
    : forall x p1 p2, f (exist _ x p1) = f (exist _ x p2).
  Proof. move=> x/= p1 p2; by rewrite (bool_irrelevance p1 p2). Qed.

  Definition AppR F (X : TyEq) (x y : AppT F X) : Prop
    := projT1 x = projT1 y /\
       (forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2)).

  Lemma AppR_inv_sh F X x y :
    @AppR F X x y -> projT1 x = projT1 y.
  Proof. by case. Qed.

  Lemma AppR_inv_k F X x y :
    @AppR F X x y ->
    forall e d1 d2, projT2 x (exist _ e d1) =e projT2 y (exist _ e d2).
  Proof. by case. Qed.

  Definition equivApp F (X : TyEq) : equivalence (AppT F X).
  Proof.
    apply: (@mkEquiv _ (@AppR F X)).
    - move=> [shx kx]; constructor=>//=x d1 d2.
      rewrite (bool_irrelevance d1 d2); by apply: e_refl.
    - move=> x y [Sxy Exy]; split; first by apply/esym.
      by move=> e d1 d2; symmetry.
    - move=> x y z [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
      move=>e d1 d2; have d3: dom (projT1 y) e by move: d1; rewrite Sxy.
      rewrite (Exy e d1 d3) (Eyz e d3 d2); by reflexivity.
  Defined.

  Definition App F (X : TyEq)
    := {| Ty := AppT F X; Eq := equivApp F X |}.

  Structure arr (A B : TyEq) :=
    { func :> Ty A -> Ty B;
      f_eq : forall x y, x =e y -> func x =e func y
    }.

  Definition arrE (A B : TyEq) : equivalence (arr A B).
  Proof.
    apply: (@mkEquiv _ (fun (f g : arr A B) => f =1e g)).
    - move=>x/=; by reflexivity.
    - move=>x y/= H e; rewrite H; by reflexivity.
    - move=>x y z/= H1 H2 e; by rewrite H1.
  Defined.

  Definition arrow A B : TyEq :=
    {| Ty := arr A B;
       Eq := arrE A B;
    |}.

  Definition fmapA_f F A B (f : arrow A B) (x : Ty (App F A)) : Ty (App F B)
    := existT _ (projT1 x) (f \o projT2 x).

  Lemma fmapA_eqF F A B (f : arrow A B)
    : forall x y, x =e y -> fmapA_f (F:=F) f x =e fmapA_f f y.
  Proof.
    move=> [sx kx] [sy ky] [/=Es Ek]; split=>//= e d1 d2.
    by apply/f_eq/Ek.
  Qed.

  Definition fmapA F A B (f : arrow A B) : arrow (App F A) (App F B)
    := {| func := _ ; f_eq := fmapA_eqF f |}.

  Definition Alg F A := arrow (App F A) A.
  Definition CoAlg F A := arrow A (App F A).

  Inductive LFixT F : Type :=
  | LFix_in (sh : Shape F): (sig (dom sh) -> LFixT F) -> LFixT F.

  Definition l_shape F (x : LFixT F) :=
    match x with
    | LFix_in sh _ => sh
    end.
  Definition l_cont F (x : LFixT F) :=
    match x return sig (dom (l_shape x)) -> LFixT F with
    | LFix_in _ k => k
    end.

  Fixpoint LFixR F (x y : LFixT F) : Prop :=
    l_shape x = l_shape y /\
    forall e d1 d2,
        LFixR (@l_cont F x (exist _ e d1)) (@l_cont F y (exist _ e d2)).

  Lemma LFixR_inv_sh F (x y : LFixT F) : LFixR x y -> l_shape x = l_shape y.
  Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

  Lemma LFixR_inv_k F (x y : LFixT F)
    : LFixR x y ->
      forall e d1 d2,
        LFixR (@l_cont F x (exist _ e d1)) (@l_cont F y (exist _ e d2)).
  Proof. by case: x=>[sx kx]; case: y=>[sy ky] []. Qed.

  Lemma LFixR_refl F x : @LFixR F x x.
  Proof.
    elim: x=>// shx k Ih; constructor=>//=x p1 p2.
    by rewrite (bool_irrelevance p1 p2); apply: Ih.
  Qed.

  Lemma LFixR_sym F x y : @LFixR F x y -> @LFixR F y x.
  Proof.
    elim: x => sx kx Ih in y *; case: y => sy ky /=[/esym-Sxy E].
    split=>// e d1 d2; by apply/Ih/E.
  Qed.

  Lemma LFixR_trans F x y z : @LFixR F x y -> @LFixR F y z -> @LFixR F x z.
  Proof.
    elim: x=> sx kx Ih in y z *; case: y=> sy ky/=; case: z=> sz kz/=.
    move=> [Sxy Exy] [Syz Eyz]; split; first by rewrite Sxy.
    move=> e d1 d2; apply: Ih; first by apply: Exy; rewrite Syz.
    by apply/Eyz.
  Qed.

  Definition LFix_Eq F :=
    {| eqRel := @LFixR F;
       e_refl := @LFixR_refl F;
       e_sym := @LFixR_sym F;
       e_trans := @LFixR_trans F;
    |}.

  Definition LFix F :=
    {| Ty := LFixT F; Eq := @LFix_Eq F; |}.

  Definition l_in_f F (x : App F (LFix F)) : LFix F :=
    LFix_in (projT2 x).

  Lemma l_in_eq F x y : x =e y -> @l_in_f F x =e @l_in_f F y.
  Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

  Definition l_out_f F (x : LFix F) : App F (LFix F) :=
    match x with
    | LFix_in sh k => existT _ sh k
    end.

  Lemma l_out_eq F x y : x =e y -> @l_out_f F x  =e @l_out_f F y.
  Proof. by case: x=> sx kx; case: y=> sy ky/= [/=Es Ek]; split. Qed.

  Definition l_in F : Alg F (LFix F) :=
    {| func := _; f_eq := @l_in_eq F |}.
  Definition l_out F : CoAlg F (LFix F) :=
    {| func := _; f_eq := @l_out_eq F |}.

  Definition cata_f F A (g : Alg F A) : Ty (LFix F) -> Ty A
    := fix f x :=
         match x with
         | LFix_in s k => g (existT _ s (f \o k))
         end.

  Lemma cata_arr F A (g : Alg F A) :
    forall x y, x =e y -> cata_f g x =e cata_f g y.
  Proof.
    move=> x y /=; elim: x => sx kx Ih/= in y *; case: y=> sy ky/= [Es Ek].
    apply/(f_eq g); split=>//= e d1 d2; by apply/Ih.
  Qed.

  Definition cata F A (g : Alg F A) : arrow (LFix F) A
    := {| func := _; f_eq := cata_arr g |}.

  Lemma cata_univ_r F A (g : Alg F A) (f : arrow (LFix F) A)
    : f =1e g \o fmapA F f \o @l_out F -> f =1e cata g.
  Proof.
    move=> H; elim=> sx kx /= Ih.
    rewrite H/=; apply/f_eq; rewrite /fmapA_f/=.
    split=>//= e d1 d2; rewrite Ih (cont_irr (X:=LFix F) kx).
    by reflexivity.
  Qed.

  Lemma cata_univ_l F A (g : Alg F A) (f : arrow (LFix F) A)
    : f =1e cata g -> f =1e g \o fmapA F f \o @l_out F.
  Proof.
    move=> H; elim=> sx kx /= Ih.
    rewrite H/=; apply/(f_eq g); rewrite /fmapA_f/=.
    split=>//= e d1 d2; rewrite Ih (cont_irr (X:=LFix F) kx).
    rewrite -[cata_f g _]/(cata g _) -H Ih.
    by reflexivity.
  Qed.

  Lemma cata_univ F A (g : Alg F A) (f : arr (LFix F) A)
    : f =1e cata g <-> f =1e g \o fmapA F f \o @l_out F.
  Proof. by split;[apply/cata_univ_l|apply/cata_univ_r]. Qed.

  Inductive FinF F A (h : CoAlg F A) : A -> Prop :=
  | FinF_fold x : (forall e, FinF h (projT2 (h x) e)) -> FinF h x.

  Lemma FinF_inv F A (h : CoAlg F A) x
    : FinF h x -> forall e, FinF h (projT2 (h x) e).
  Proof. by case. Defined.

  Definition ana_f_ F A (h : CoAlg F A) : forall (x : A), FinF h x -> LFix F
    := fix f x H :=
         let hx := h x in
         LFix_in (fun e => f (projT2 hx e) (FinF_inv H e)).

         (* match h x return FinF h x-> LFix F with *)
         (* | existT s k => fun H' => LFix_in (fun e => f (k e) (FinF_inv1 H p e)) *)
         (* end H. *)

  (* Finite coalgebras *)
  Structure FCoAlg F A :=
    { coalg :> CoAlg F A;
      finite : forall x, FinF coalg x
    }.

  Definition ana_f F A (h : FCoAlg F A) : A -> LFix F
    := fun x => ana_f_ (finite h x).

  Lemma ana_arr F A (h : FCoAlg F A) :
    forall x y, x =e y -> ana_f h x =e ana_f h y.
  Proof.
    rewrite /ana_f; move=> x y; move: x y (finite h x) (finite h y).
    fix Ih 3; move=> x y [x' Fx] [y' Fy]/=; split.
    - by case: (f_eq (coalg h) H).
    - move=> e d1 d2 /=; apply: Ih.
      by move: (f_eq (coalg h) H)=> [E1 /(_ e d1 d2)].
  Qed.

  Definition ana F A (h : FCoAlg F A) : arrow A (LFix F)
    := {| func := ana_f h; f_eq := ana_arr h |}.

End Definitions.
