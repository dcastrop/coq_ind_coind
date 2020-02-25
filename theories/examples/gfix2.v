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

  Reserved Notation "f =e g" (at level 70, no associativity).
  Reserved Notation "f =1e g" (at level 70, no associativity).
  Notation "f =e g" := (eqRel (Eq _) f g).
  Notation "f =1e g" := (forall x, eqRel (Eq _) (f x) (g x)).

  Lemma extEq A B (E : equivalence A) : equivalence (B -> A).
  Proof.
    apply: (@mkEquiv _ (fun f g =>forall x, eqRel E (f x) (g x))).
    - by move=>f x; apply: e_refl.
    - by move=>f g H x; apply: e_sym.
    - by move=>f g h Hf Hg x; apply: e_trans.
  Defined.

  Definition IRR A (P : A -> Prop) B (f : {x | P x} -> B)
    := forall x p1 p2, f (exist _ x p1) = f (exist _ x p2).

  Definition iarr A (P : A -> Prop) B :=
    (* {f : *) {x | P x} -> B (* | IRR f} *).


  Lemma extEqP A (P : A -> Prop) B (E : equivalence B) : equivalence (iarr P B).
  Proof.
    by apply/extEq.
    (* apply: *)
    (*   (@mkEquiv _ *)
    (*             (fun f g=> *)
    (*                forall x p1 p2, *)
    (*                  eqRel E (sval f (exist _ x p1)) (sval g (exist _ x p2)))). *)
    (* - move=>f x p1 p2; by rewrite (proj2_sig f); apply: e_refl. *)
    (* - move=> f g H x p1 p2; apply: e_sym. *)
    (*   by rewrite (proj2_sig f x p2 p1) (proj2_sig g x p1 p2). *)
    (* - move=> f g h H1 H2 x p1 p2; apply: e_trans; first by apply: H1. *)
    (*   by rewrite (proj2_sig g x p2 p1). *)
  Defined.

  Structure Functor :=
    { Shape : Type;
      Position : Shape -> Type;
      (* (** Is position valid in shape? *) *)
      (* Dom : Shape -> Position -> Prop; *)
    }.

  Definition Cont F (sh : Shape F) (X : TyEq)
    := {| Ty := iarr (Dom sh) (Ty X); Eq := extEqP _ (Eq X) |}.

  Definition AppT F X := {sh : Shape F & iarr (Dom sh) (Ty X)}.

  Inductive AppR F X : AppT F X -> AppT F X -> Prop :=
  | AppR_mk sh (k1 : iarr (Dom sh) (Ty X)) (k2 : iarr (Dom sh) (Ty X)):
      k1 =1e k2 ->
      (* (forall x d1 d2, (* sval *) k1 (exist _ x d1) =e (* sval *) k2 (exist _ x d2)) -> *)
      AppR (existT _ sh k1) (existT _ sh k2).

  Lemma AppR_inv_sh F X (x y : AppT F X) : AppR x y -> projT1 x = projT1 y.
  Proof. by case. Defined.

  Lemma AppR_inv_kl F X (x y : AppT F X)
    : forall a : AppR x y,
      eq_rect _ _ (projT2 x) _ (AppR_inv_sh a) =1e projT2 y.
  Proof. by case. Defined.

  Lemma AppR_inv_kr F X (x y : AppT F X)
    : forall a : AppR x y,
      projT2 x =1e eq_rect _ _ (projT2 y) _ (esym (AppR_inv_sh a)).
  Proof. by case. Defined.

  Lemma equivApp F X : equivalence (Ty X) -> equivalence (AppT F X).
  Proof.
    move=> H; apply: (@mkEquiv _ (@AppR F X)).
    - move=> [shx kx]; constructor=>//=x.
      by apply: e_refl.
      (* rewrite (proj2_sig kx); by apply: e_refl. *)
    - move=> [shx kx] [shy ky] [sh k k' E]; constructor=>//=x.
      by apply: e_sym.
      (* move: E1 k' d1 E2=><- k' d1 E2; apply: e_sym. *)
      (* by rewrite (proj2_sig k x d2 d1) (proj2_sig k' x d1 d2). *)
    - move=>x y z. case=>/= sh k1 k2 Exy.
      case: z=>[shz kz] Eyz.
      move: (AppR_inv_sh Eyz) => /= Syz; rewrite -Syz in kz Eyz *.
      constructor=>e; apply: (e_trans (Exy e)).
      move: (AppR_inv_kl Eyz)=>/(_ e)/=.
      move=> [shx kx] [shy ky] [shz kz] E1 E2.
      move: (AppR_inv_sh E1) => /= Sxy.
      move: Sxy ky E1 E2=><- ky E1 E2.
      move: (AppR_inv_kr E1)  => /= Exy.
      move: (AppR_inv_sh E2) => /= Syz.
      move: Syz kz E2=><- ky E2.
      move: (AppR_inv_sh E2) (AppR_inv_kl E2) => /= Syz Eyz {E2}.
      SearchAbout eq_rect.
      Print Assumptions Eqdep.Eq_rect_eq.eq_rect_eq
      move: Sxy Syz ky kz E.
      move: (AppR_inv_sh E) (AppR_inv_k E) => Sxy Exy {E} E.
      move: (AppR_inv_sh E) (AppR_inv_k E) => Syz Eyz {E}.
      case: x Sxy Exy => shx kx/= Sxy Exy.
      case: z Syz Eyz => shz kz/= Syz Eyz.
      case: y Sxy Syz Exy Eyz => shy ky/= Sxy Syz Exy Eyz.
      move: Sxy Syz kx ky kz Exy Eyz=><-<- kx ky kz Exy Eyz.
      constructor=>//= x d1 d2; apply: e_trans; first by apply: Exy.
      by rewrite (proj2_sig ky x d2 d1).
  Defined.

  Definition App F (X : TyEq)
    := {| Ty := AppT F X; Eq := equivApp F (Eq X) |}.

  Definition arr (A B : TyEq) :=
    { f : Ty A -> Ty B | forall x y, x =e y -> f x =e f y }.

  Definition Alg F A := arr (App F A) A.
  Definition CoAlg F A := arr A (App F A).

  Unset Elimination Schemes.
  Inductive LFixT F : Type :=
  | LFix_in (sh : Shape F): iarr (Dom sh) (LFixT F) -> LFixT F.
  Set Elimination Schemes.

  Definition l_shape F (x : LFixT F) :=
    match x with
    | LFix_in sh _ => sh
    end.
  Definition l_cont F (x : LFixT F) :=
    match x return iarr (Dom (l_shape x)) (LFixT F) with
    | LFix_in _ k => k
    end.

  Lemma LFixT_ind :
    forall (F : Functor) (P : LFixT F -> Prop),
      (forall sh (l : iarr (Dom sh) (LFixT F)),
          (forall x, P (sval l x)) -> P (LFix_in l)) ->
      forall l : LFixT F, P l.
  Proof.
    move=> F P P_next; fix IH 1.
    case=>[shx k]; apply: P_next => x.
    by apply: IH.
  Qed.

  Inductive LFixR F : LFixT F -> LFixT F -> Prop :=
  | LFix_R sh1 sh2
           (k1 : iarr (Dom sh1) (LFixT F))
           (k2 : iarr (Dom sh2) (LFixT F))
    : sh1 = sh2 ->
      (forall x p1 p2,
          LFixR (sval k1 (exist _ x p1)) (sval k2 (exist _ x p2))) ->
      LFixR (LFix_in k1) (LFix_in k2).

  Lemma LFixR_inv_sh F (x y : LFixT F) : LFixR x y -> l_shape x = l_shape y.
  Proof. by case. Qed.

  Lemma LFixR_inv_k F (x y : LFixT F)
    : LFixR x y ->
      (forall e d1 d2,
          LFixR (sval (l_cont x) (exist _ e d1))
                (sval (l_cont y) (exist _ e d2))).
  Proof. by case. Qed.

  Lemma LFixR_refl F x : @LFixR F x x.
  Proof.
    elim: x=>// shx k Ih; constructor=>//=x p1 p2.
    by rewrite (proj2_sig k); apply: Ih.
  Qed.

  Lemma LFixR_sym F x y : @LFixR F x y -> @LFixR F y x.
  Proof.
    elim => shx shy kx ky Sxy Exy Ih.
    constructor; first by apply/esym.
    by move=> px d1 d2; apply: Ih.
  Qed.

  Lemma LFixR_trans F x y z : @LFixR F x y -> @LFixR F y z -> @LFixR F x z.
  Proof.
    move=> E; move: E z.
    elim => shx shy kx ky Sxy Exy Ih z E.
    move: (LFixR_inv_sh E) (LFixR_inv_k E) => /= {E}.
    case: z=>/= shz kz Syz Eyz.
    move: Sxy Syz kx ky kz Exy Eyz Ih=><-<- kx ky kz Exy Eyz Ih.
    constructor=>//=p d1 d2; apply: Ih.
    by rewrite (proj2_sig ky p d2 d1).
  Qed.

  Definition LFix_Eq F :=
    {| eqRel := @LFixR F;
       e_refl := @LFixR_refl F;
       e_sym := @LFixR_sym F;
       e_trans := @LFixR_trans F;
    |}.

  Definition LFix F :=
    {| Ty := LFixT F; Eq := @LFix_Eq F; |}.

  Definition l_in_f F (x : Ty (App F (LFix F))) : Ty (LFix F) :=
    LFix_in (projT2 x).

  Lemma l_in_eq F x y : x =e y -> @l_in_f F x =e @l_in_f F y.
  Proof. by move=>/=[sh1 sh2 k1 k2 S12 E12]; constructor. Qed.

  Definition l_out_f F (x : Ty (LFix F)) : Ty (App F (LFix F)) :=
    match x with
    | LFix_in sh k => existT _ sh k
    end.

  Lemma l_out_eq F x y : x =e y -> @l_out_f F x  =e @l_out_f F y.
  Proof. by move=>/=[sh1 sh2 k1 k2 S12 E12]; constructor. Qed.

  Definition l_in F : Alg F (LFix F) := exist _ (@l_in_f F) (@l_in_eq F).
  Definition l_out F : CoAlg F (LFix F) := exist _ (@l_out_f F) (@l_out_eq F).

  Lemma comp_eq A B C (f : arr B C) (g : arr A B) :
    forall x y, x =e y -> ((sval f \o sval g) x) =e ((sval f \o sval g) y).
  Proof. move=> x y E /=; by apply/(proj2_sig f)/(proj2_sig g). Qed.

  Definition comp A B C (f : arr B C) (g : arr A B) : arr A C
    := exist _ (sval f \o sval g) (@comp_eq A B C f g).

  Lemma id_eq A : forall (x y : Ty A), x =e y -> id x =e id y.
  Proof. by []. Qed.

  Definition id A : arr A A := exist _ (fun x => x) (@id_eq A).

  (* Notation "g >>> f" := (comp f g). *)
  (* Notation "x = y" := (Eq x y). *)
  (* Notation "f =1 g" := (forall x, Eq (sval f x) (sval g x)). *)

  (* Goal forall F, @l_in F \o @l_out F =1 id (LFix F). *)
  (* Proof. *)
  (*   move=> F; elim=>sh k; rewrite /=/l_in_f/l_out_f/==>Ih. constructor=> x. *)
  (*   by move: Ih=> /(_ x); case: (k x)=>//=. *)
  (* Qed. *)

  (* Lemma l_in_out *)

  Definition IRR_comp A (P : A -> Prop) B C
             (f : B -> C) (g : sig P -> B) (H : IRR g) : IRR (f \o g).
  Proof.
    move=>x p1 p2 /=.
    by rewrite H.
  Defined.

  Definition icomp A (P : A -> Prop) B C
             (f : B -> C) (g : iarr P B) : iarr P C
    := match g with
       | exist rr H => exist _ (f \o rr) (@IRR_comp A P B C f rr H)
       end.

  Definition cata_f F A (g : Alg F A) : Ty (LFix F) -> Ty A
    := fix f x :=
         let gg := sval g in
         match x with
         | LFix_in sh k =>
           match k with
           | exist rr H => gg (existT (fun x=>_) sh (exist _ (f \o rr) (IRR_comp f H)))
           end
         end.

  Lemma cata_arr F A (g : Alg F A) :
    forall x y, Eq x y -> Eq (cata_f g x) (cata_f g y).
  Proof.
    move=> x y; elim=> sh k1 k2 _ Ih /=.
    apply: (proj2_sig g); constructor=> {}x/=; by apply: Ih.
  Qed.

  Definition cata F A (g : Alg F A) : arr (LFix F) A
    := exist _ (cata_f g) (cata_arr g).

End Definitions.
