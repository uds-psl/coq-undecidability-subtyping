(** * Reduction from Flattened System Fsub to Deterministic System Fsub *)
(* begin details : Imports *)
Require Import Vector Arith Lia Relations Logic.Eqdep.
From Equations Require Import Equations.
Require Import Utils.Various_utils.
Require Import FsubD FsubF.
(* end details *)

(** ** Reduction *)

(** The translation is essentially the identity however the proof relies on _eager substitution_,
  the following construction defines, for a non-empty context, a smaller context in which the first bounds are substituted, the substitution in question, and a couple of facts that characterize them. *)

Section argument.
Context {w : nat}.
Definition nonVar {m} (s : @ntype w m) := {f & {f0 & var_ntype f f0 = s}}->False.

Fixpoint mkEager {m} (Γ : @ctx w (S m)) : { Γ' : @ctx w m & { σ : fin w -> fin (S m) -> @ntype w m &
   (forall i j f f0, var_ntype i j = σ f f0 -> ctx_at Γ' i j = subst_ntype σ (ctx_at Γ f f0))
/\ (forall i j, nonVar (σ i j) -> subst_ntype σ (ctx_at Γ i j) = σ i j)  }}.
Proof with eauto. destruct m.
  -exists empty. apply (nonEmptyCtx Γ (fun _ => _)). intros v t. exists (fun i => nth' v i .; var_ntype i).
   split.  contradiction. intros i [j|]. contradiction. simpl. intro. asimpl. now apply idSubst_ntype.
  -apply (nonEmptyCtx Γ (fun _ => _)). intros h Γt. destruct (mkEager _ Γt) as [Γs [σ [Hv  Hnv]]].
   exists (add (Vector.map (subst_ntype σ) h) Γs). exists (up_ntype_ntype σ). split.
   +intros i [j | ] k [l | ]; asimpl; simpl; intro.
     ++assert (var_ntype i j = σ k l). { asimpl in H. destruct (σ k l); asimpl in H. now inversion H. discriminate. }
      rewrite (Hv _ _ _ _ H0). asimpl. apply (ext_ntype); auto.
     ++inversion H.
     ++asimpl in H. destruct (σ k l); asimpl in H; inversion H.
     ++inversion H. rewrite nth'_map. asimpl. apply ext_ntype; auto.
  +intros i [j|]. asimpl. unfold funcomp. simpl. asimpl. 2: {intro. exfalso. apply H. now exists i, var_zero. }
   destruct (σ i j) eqn:sH. asimpl. intro. exfalso. apply H. now exists f, (↑f0). intro.
   assert (nv : nonVar (σ i j)). { intros [f [f0 vH]]. rewrite sH in vH. discriminate. }
   rewrite <- sH. rewrite <- (Hnv _ _ nv). asimpl. apply ext_ntype. intros i' j'. asimpl. now simpl.
Defined.

Definition eagerCtx {m} (Γ : @ctx w (S m)) := projT1 (mkEager Γ).
Definition eagerSubst {m} (Γ : @ctx w (S m)) := projT1 (projT2 (mkEager Γ)).

(* begin details: Facts about the construction *)
Fact helperU {m s0 p} {σ : fin w -> fin (S m) -> ntype m} : uAllN s0 = subst_ntype σ (uAllN p) ->
  subst_ptype (up_ntype_ntype σ) p = s0.
Proof. asimpl. now inversion 1. Qed.

Fact helperB {m n0 t0 t1 t2} {σ : fin w -> fin (S m) -> ntype m} : bAllN t1 t2 = subst_ptype σ (bAllN t0 n0) ->
  Vector.map (subst_ntype σ) t0 = t1.
Proof. asimpl. now inversion 1. Qed.

Fact helperBb {m n0 t0 t1 t2} {σ : fin w -> fin (S m) -> ntype m} : bAllN t1 t2 = subst_ptype σ (bAllN t0 n0) ->
  subst_ntype (up_ntype_ntype σ) n0 = t2.
Proof. asimpl. now inversion 1. Qed.

Fact helperACtx {m} (Γ : @ctx w (S m)) v : eagerCtx (add v Γ) = add (Vector.map (subst_ntype (eagerSubst Γ)) v) (eagerCtx Γ).
Proof. unfold eagerCtx. unfold eagerSubst. simpl. now destruct (mkEager Γ) as [Γ' [σ H]]. Qed.

Fact helperASubst {m} (Γ : @ctx w (S m)) v : eagerSubst (add v Γ) = up_ntype_ntype (eagerSubst Γ).
Proof. unfold eagerSubst. simpl. now destruct (mkEager Γ) as [Γ' [σ H]]. Qed.

Fact congr_pair {X Y} (a b : X) (c d : Y) : a = b -> c = d -> (a, c) = (b, d).
Proof. congruence. Qed.

Definition ctx0 (Γ : @ctx w 0) : Γ = empty := match Γ with empty => eq_refl end.

Fixpoint helper {m} {Γ : @ctx w (S m)} {i j s0} : uAllN s0 = (eagerSubst Γ) i j -> ctx_at Γ i j = ren_ntype ↑ (uAllN s0).
Proof. apply (nonEmptyCtx Γ). intros h t. destruct m.
  -rewrite (ctx0 t). unfold eagerSubst. simpl. destruct j; cbn. discriminate. intros <-. now asimpl.
  -rewrite helperASubst. destruct j; simpl. 2: discriminate. unfold funcomp. destruct (eagerSubst t i f) eqn:gsH.
    discriminate. intro. symmetry in gsH. rewrite (helper _ _ _ _ _ gsH). now rewrite H.
Qed.

Fixpoint iterFnShift {m} (n :  nat) : fin m -> fin (n+m).
Proof. destruct n. exact id. intros i. apply ↑,(iterFnShift _ _ i).
Defined.
Fact iterFnShiftR {m} (n :  nat) (t : @ntype w m) : ren_ntype (iterFnShift (S n)) t = ren_ntype ↑ (ren_ntype (iterFnShift n) t).
Proof. simpl. asimpl. now apply extRen_ntype.
Qed.
Fact iterFnShiftL {m n t} (Heq : S n+m=n+S m) : ren_ntype (iterFnShift n) (ren_ntype ↑ t) = match Heq in (_ = n0) return @ntype w n0 with
  | eq_refl => ren_ntype (iterFnShift (S n)) t
  end.
Proof with eauto. induction n.
  -simpl in *. rewrite (UIP_refl _ _ Heq). erewrite compRenRen_ntype. now unfold funcomp. now asimpl.
  -rewrite iterFnShiftR. assert (S n + m = n + S m). auto. rewrite (IHn H). repeat rewrite iterFnShiftR.
   generalize (@ren_ntype w (n + m) (S (n + m)) ↑ (@ren_ntype w m (n + m) (@iterFnShift m n) t)) H Heq.
   simpl. rewrite Nat.add_succ_r. intros. rewrite (UIP_refl _ _ H0). now rewrite (UIP_refl _ _ Heq0).
Qed.
Fixpoint helperSubst {m} {Γ : @ctx w (S m)} {f f0} n n' (s : fin w -> fin m -> ntype n') (Heq: n+m=n') {struct m} : nonVar (eagerSubst Γ f f0) ->
   subst_ntype s (eagerSubst Γ f f0) = match Heq in (_ = n0 ) return @ntype w n0 with
   | eq_refl => ren_ntype (iterFnShift n) (eagerSubst Γ f f0)
   end.
Proof with eauto. apply (nonEmptyCtx Γ). intros h Γ'. unfold eagerSubst. destruct m; simpl.
  -destruct f0. contradiction. simpl. intro. generalize s Heq. rewrite <- Heq.
   intros. rewrite (UIP_refl _ _ Heq0). rewrite rinstInst_ntype. now apply ext_ntype.
  -destruct (mkEager Γ') as [Γ0 [σ [H1 H2]]] eqn:HΓ. simpl. destruct f0; simpl. 2: {intros Hnv. exfalso. apply Hnv. eauto. }
   unfold funcomp. intro. assert (σ f f0 = eagerSubst Γ' f f0). { unfold eagerSubst. now rewrite HΓ. }
   rewrite H0. assert (nonVar (eagerSubst Γ' f f0)).
   { unfold nonVar. destruct (eagerSubst Γ' f f0). intro. apply H. asimpl. rewrite H0. asimpl. eauto. intros [f1 [f2 Hv]]. discriminate. }
   erewrite compRenSubst_ntype. 2: now unfold funcomp. assert (S n + m = n'). lia. rewrite (helperSubst _ _ _ _ (S n) _ _ H4); auto.
   assert (S n+m=n+S m). lia. rewrite (iterFnShiftL H5). generalize (ren_ntype (iterFnShift (S n)) (eagerSubst Γ' f f0)) Heq H4 H5.
   rewrite <-  Heq. rewrite Nat.add_succ_r. simpl. intros.
   rewrite (UIP_refl _ _ Heq0). rewrite (UIP_refl _ _ H6). now rewrite (UIP_refl _ _ H7).
Qed.
Fact helperRen' {m} {Γ : @ctx w (S m)} {f f0} : nonVar (eagerSubst Γ f f0) ->
  subst_ntype (eagerSubst Γ) (ren_ntype ↑ (eagerSubst Γ f f0)) = (eagerSubst Γ f f0).
Proof. intro. rewrite (compRenSubst_ntype  _ _ (fun i : fin w => (↑ >> eagerSubst Γ i))). 2: now asimpl.
  assert (0+m=m). auto. rewrite (helperSubst 0 m _ H0 H). generalize H0. simpl. intro. rewrite (UIP_refl _ _ H1).
  now asimpl.
Qed.
Fact helperRen {m} {Γ : @ctx w (S m)} {f f0 s0} : uAllN s0 = eagerSubst Γ f f0 ->
  subst_ptype (up_ntype_ntype (eagerSubst Γ)) (ren_ptype (upRen_ntype_ntype ↑) s0) = s0.
Proof. intro. assert (nonVar (eagerSubst Γ f f0)).
  { unfold nonVar. destruct (eagerSubst Γ f f0). discriminate. intros [f1 [f2 Hf]]. discriminate. }
  pose (helperRen' H0). rewrite <- H in e. unfold ren_ntype in e. unfold subst_ntype in e.
  inversion e. now rewrite H2 at 1.
Qed.
(* end details *)

Derive Signature for subD.
Lemma fromEager {m} (Γ : ctx (S m)) {s t} :
  (exists h, eagerCtx Γ |-D h; subst_ntype (eagerSubst Γ) t <: subst_ptype (eagerSubst Γ) s) ->
  exists h, Γ |-D h; t <: s.
Proof. intros [h H]. remember (eagerCtx Γ) as Γ'. remember (subst_ntype (eagerSubst Γ) t) as t'.
  remember (subst_ptype (eagerSubst Γ) s) as s'. induction H.
  -eexists. destruct s. apply DTop. discriminate.
  -destruct t; asimpl in Heqt'. 2: discriminate.  edestruct IHsubD; try eassumption.
   rewrite HeqΓ'. unfold eagerCtx. unfold eagerSubst in *.
   destruct (mkEager Γ) as [Γ' [σ [He He']]] eqn:HΓ. simpl in *. apply (He _ _ _ _ Heqt').
   exists (S x). now apply DVar.
  -destruct s. eexists. apply DTop. destruct t.
    +asimpl in Heqt'. edestruct IHsubD.
     4: { eexists. apply DVar. rewrite (helper Heqt'). apply DAllNeg. exact H0. }
     rewrite helperACtx. rewrite (helperB Heqs'). now rewrite HeqΓ'.
     rewrite helperASubst. now rewrite (helperBb Heqs').
     rewrite helperASubst. now rewrite <- (helperRen Heqt') at 1.
    +edestruct IHsubD. 4: { eexists. apply DAllNeg. exact H0. }
     rewrite helperACtx. rewrite (helperB Heqs'). now rewrite HeqΓ'.
     rewrite helperASubst. now rewrite (helperBb Heqs').
     rewrite helperASubst. now rewrite (helperU Heqt').
Qed.

Lemma flat_det (s : @ntype w 0) t : (exists h,|-F h; s <: t) -> (exists h, empty |-D h; s <: t).
Proof. intros [h H]. depind H.
  -eexists. constructor.
  -unfold ninst in H. unfold pinst in H. edestruct (fromEager (add _ empty) IHsubF).
   exists (S x). now apply DAllNeg.
Qed.

Fixpoint toEager {m} {Γ : @ctx w (S m)} {s t h} (H : Γ |-D h; s <: t) :
 exists i, eagerCtx Γ |-D i; subst_ntype (eagerSubst Γ) s <: subst_ptype (eagerSubst Γ) t /\ i <= h.
Proof. destruct H.
  -exists 0. split; auto; asimpl. apply DTop.
  -destruct (toEager _ _ _ _ _ H) as [i' [Hi Hk]].
   asimpl in *. unfold eagerSubst in *. unfold eagerCtx in *.
   destruct (mkEager Γ) as [Γ' [σ [Hv Hnv]]]. simpl in *. destruct (σ i j) eqn:sH.
    +exists (S i'). split. 2: lia. apply DVar. symmetry in sH. now rewrite (Hv _ _ _ _ sH).
    +exists i'. split. 2: lia. assert (nv : nonVar (σ i j)).
     { intros [f [f0 vH]]. rewrite sH in vH. discriminate. }  rewrite <- sH. now rewrite <- (Hnv _ _ nv).
  -destruct (toEager _ _ _ _ _ H) as [i' [Hi Hk]]. exists (S i'). split. 2: lia.
   apply DAllNeg. rewrite <- helperACtx. rewrite <- (helperASubst _ t1). exact Hi.
Qed.

Lemma det_flat (s : @ntype w 0) t : (exists h, empty |-D h; s <: t) -> (exists h,|-F h; s <: t).
Proof. intros [h H]. revert H. revert s t. induction h using Wf_nat.lt_wf_ind.
  intros. depind H0.
  - eexists. constructor.
  - contradiction.
  - destruct (toEager H0) as [k [Hi Hk]]. edestruct (H k). lia.
    exact Hi. exists (S x). apply FAllNeg. exact H1.
Qed.

End argument.


(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : FsubF_SUBTYPE ⪯  FsubD_SUBTYPE.
Proof.
  exists (fun ntt => existT _ (projT1 ntt) (existT _ 0 (empty, (fst (projT2 ntt), snd (projT2 ntt)) ))).
  intros [n [s t]]. cbn. split. now apply flat_det. now apply det_flat.
Qed.
