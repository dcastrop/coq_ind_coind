From mathcomp.ssreflect Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section FixGen.
  CoInductive GFix T (P : Type -> Type) : Type :=
  | GFix_in : P T -> (T -> GFix T P) -> GFix T P.

  Definition monotone P := forall X Y, (X -> Y) -> P X -> P Y.

  Definition enumerable P Y := forall X, P X -> P Y * seq (Y * X).

  Definition gFix_out S P (map : monotone P) (x : GFix S P) : P (GFix S P) :=
    match x with
    | GFix_in p f => map _ _ f p
    end.

  CoFixpoint ana A (P : Type -> Type) (f : A -> P A) (x : A) : GFix A P :=
    GFix_in (f x) (ana f).

  Definition gfix_unfold A P (x : GFix A P) : GFix A P :=
    match x with
    | GFix_in p f => GFix_in p f
    end.

  Lemma gfix_unfold_id A P (x : GFix A P) : x = gfix_unfold x.
  Proof. by case: x. Qed.

  (* An alternative is having a single constructor [LFix_in S : P S -> (S ->
     LFix P) -> LFix P], but this requires the use of axioms, or restricting [S]
     to have decidable equality *)
  (* Inductive LFix S (P : Type -> Type) : Type := *)
  (* | LFix_in1 : P False -> LFix S P *)
  (* | LFix_in2 : P S -> (S -> LFix S P) -> LFix S P. *)

  Inductive LFix (P : Type -> Type) : Type :=
  (* | LFix_in1 : P False -> LFix S P *)
  | LFix_in (S : Type) : P S -> (S -> LFix P) -> LFix P.

  Definition lFix_out (P : Type -> Type) (map : monotone P) (x : LFix P) : P (LFix P) :=
    match x with
    | LFix_in _ p f => map _ _ f p
    end.

  Fixpoint cata B P (map : monotone P) (f : P B -> B) (x : LFix P) : B :=
    match x with
    | LFix_in _ p k => f (map _ _ (fun n => cata map f (k n)) p)
    end.

  Definition P_Finite (P : Type -> Type) := forall S, P S -> option (P False).

  (* I need to state "if p contains s, then ..." *)
  Inductive Finite S P (T : P_Finite P) (occ : P S -> seq S)
            : GFix S P -> Prop :=
  | Fin_fold1 (x : P S) (p : P False) f :
      T _ x = Some p ->
      Finite T occ (GFix_in x f)
  | Fin_fold2 (p : P S) (f : S -> GFix S P) :
      T _ p = None ->
      (forall s, List.In s (occ p) -> Finite T occ (f s)) ->
      (* I need to add something here, or change P_Finite in some way *)
      Finite T occ (GFix_in p f).

  Lemma Finite_inv1 S P (T : P_Finite P) (occ : P S -> seq S)
        (p0 : GFix S P) (p : P S) (f : S -> GFix S P) :
    Finite T occ p0 ->
    p0 = GFix_in p f ->
    T _ p = None ->
    forall s, List.In s (occ p) -> Finite T occ (f s).
  Proof. by case=>[x p1 f0 E [<-_]|p1 f1 _ H1 [<-<-]//]; move: E=>->. Defined.

  Lemma Finite_inv2 S (P : Type -> Type)
        (T : P_Finite P)
        (occ : P S -> seq S)
        (f : S -> P S) (x : S) (y : P S) :
    Finite T occ (ana f x) ->
    T _ (f x) = None ->
    forall s, List.In s (occ (f x)) -> Finite T occ (ana f s).
  Proof.
    rewrite (gfix_unfold_id (ana f x)) /= -/ana.
    by case E: _ / =>[z pF f' T_z|z f' T_z]; move: E T_z=>[-> ->]->//.
  Defined.

  Fixpoint fromGFix S P (is_empty : P_Finite P) (occ : P S -> seq S) (p : GFix S P)
           (F : Finite is_empty occ p) {struct F} : LFix P
    := match p as p0 return p = p0 -> LFix P with
       | GFix_in p f =>
         fun PF =>
           match is_empty _ p as p0 return is_empty _ p = p0 -> LFix P with
           | Some p' =>
             fun _ =>
               LFix_in p' (False_rect _)
           | None =>
             fun EQ =>
               LFix_in p (fun n => fromGFix (Finite_inv1 F PF EQ n))
           end erefl
       end erefl.

  Fixpoint fcata A B P (is_empty : P_Finite P) (map : monotone P) (f : P B -> B)
           (x : GFix A P) (F : Finite is_empty x) {struct F} : B :=
    match x as x0 return x = x0 -> B with
    | GFix_in p k =>
      fun PF =>
        match is_empty _ p as p0 return is_empty _ p = p0 -> B with
        | Some p' =>
          fun _ =>
            f (map _ _ (False_rect _) p')
        | None =>
          fun EQ =>
            f (map _ _ (fun n => fcata map f (Finite_inv1 F PF EQ n)) p)
        end erefl
    end erefl.

  Definition fhylo A B P (is_empty : P_Finite P) (map : monotone P)
             (g : P B -> B) (h : A -> P A)
    : forall (x : A), Finite is_empty (ana h x) -> B :=
    fix f (x : A) (F : Finite is_empty (ana h x)) {struct F} :=
      let h_x := h x in
      match is_empty _ h_x as y return is_empty _ h_x = y -> B with
      | Some p => fun EQ => g (map _ _ (False_rect _) p)
      | None => fun EQ => g (map _ _ (fun s => f s (Finite_inv2 h_x F EQ s)) h_x)
      end erefl.
End FixGen.

Section ExampleInfTree.
  Inductive treeP (A : Type) (t : Type) : Type :=
  | C : A -> list t -> treeP A t.

  Definition citree S A := GFix S (treeP A).

  Fixpoint downfrom n :=
    match n with
    | 0 => [::]
    | m.+1 => n :: downfrom m
    end.

  Definition exn (n : nat) : citree nat nat :=
    ana (fun n => (C n (downfrom n))) n.
End ExampleInfTree.

Section QSort.
  Inductive P A T := Empty | Div (PIVOT : A) (LEFT : T) (RIGHT : T).

  Definition test A B (x : P A B) : option (P A False) :=
    match x with
    | Empty => Some (Empty _ _)
    | _ => None
    end.

  Definition p_split (l : seq nat) : P nat (seq nat) :=
    match l with
    | [::] => Empty _ _
    | h :: t => Div h [seq x <- t | x <= h] [seq x <- t | x > h]
    end.

  Definition p_merge (t : P nat (seq nat)) : seq nat :=
    match t with
    | Empty => [::]
    | Div h l r => l ++ h :: r
    end.

  Lemma p_split_terminates : forall l, Finite (@test nat) (ana p_split l).
  Proof.
    move=>l; move: {-1} (size l) (leqnn (size l)) => n LE.
    elim: n=>[|n Ih] in l LE *; case: l LE=>[|h t]//=.
    - by rewrite (gfix_unfold_id (ana _ _))/= -/ana=> _; apply/Fin_fold1.
    - by rewrite (gfix_unfold_id (ana _ _))/= -/ana=> _; apply/Fin_fold1.
    - rewrite (gfix_unfold_id (ana _ _))/= -/ana.
      move=> LE; apply/Fin_fold2=>// s.
End MSort.
