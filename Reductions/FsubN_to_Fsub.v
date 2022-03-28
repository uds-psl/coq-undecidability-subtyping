(** * Reduction from the Normal System Fsub to the full System Fsub *)
(* begin details : Imports *)
Require Import Fsub_na Fsub FsubN.
Require Import Utils.syntax Utils.Various_utils Logic.Eqdep.
From Equations Require Import Equations.
(* end details *)

(** ** Reduction 
The translation is the identity and the reduction follows from transitivity.
*)
Section argument.

Lemma reflexivity `{arrow_flag} Γ s : Γ |-N s <: s.
Proof. revert Γ. induction s; try constructor; eauto. Qed.


Fact reordering `{arrow_flag} {Γ Δ s t s' t'} r : Γ |-N s <: t -> 
  (forall x, (nth_default (var_type x) Γ x)⟨r⟩ = nth_default (var_type (r x)) Δ (r x)) -> s' = s⟨r⟩ -> t'=t⟨r⟩ ->
  Δ |-N s' <: t'.
Proof. intros Hn. revert Δ r s' t'. induction Hn; intros; subst; asimpl; econstructor; eauto.
  eapply IHHn2; try reflexivity. auto_case. now asimpl.
  repeat rewrite nthd_cons. change (var_type (S n)) with (ren_type ↑ (var_type n)).
  change (var_type (S (r n))) with (ren_type ↑ (var_type (r n))).
  repeat rewrite map_nthd. asimpl. erewrite <- compRenRen_type. 2:eauto. now rewrite H.
Qed.

Fact weakening' `{arrow_flag} {Γ s t s' t' u} : Γ |-N s <: t -> s' = s⟨↑⟩ -> t'=t⟨↑⟩ ->
  (u⟨↑⟩ :: map (ren_type ↑) Γ) |-N s' <: t'.
Proof. intros. eapply reordering; eauto. intro. rewrite nthd_cons.
  change (var_type (↑ x)) with (ren_type ↑ (var_type x)). now rewrite map_nthd.
Qed.

Fact weakening `{arrow_flag} {Γ s t u} : Γ |-N s <: t -> (u⟨↑⟩ :: map (ren_type ↑) Γ) |-N s⟨↑⟩ <: t⟨↑⟩.
Proof. intros. eapply weakening'; eauto. Qed.

Definition transitivity_at `{arrow_flag} t := forall Γ s u r, Γ |-N s <: t⟨r⟩ -> Γ |-N t⟨r⟩ <: u -> Γ |-N s <: u.

Fact transitivity_proj `{arrow_flag} Γ s t u : transitivity_at t ->
  Γ |-N s <: t -> Γ |-N t <: u -> Γ |-N s <: u.
Proof. intros Ht. specialize (Ht Γ s u id). now asimpl in Ht. Qed.
Hint Resolve transitivity_proj : core.
Hint Constructors subN : core.

Fact transitivity_ren `{arrow_flag} t r : transitivity_at t -> transitivity_at t⟨r⟩.
Proof. unfold transitivity_at. intros. eapply H0; asimpl in H0; asimpl in H1; eauto.
  now rewrite renRen_type in H2.
Qed.

Lemma narrow `{arrow_flag} {Γ Δ s t}:
  (forall x, Δ |-N nth_default (var_type x) Δ x <: nth_default (var_type x) Γ x) ->
  (forall x, nth_default (var_type x) Γ x = nth_default (var_type x) Δ x
    \/ transitivity_at (nth_default (var_type x) Γ x)) ->
  Γ |-N s <: t -> Δ |-N s <: t.
Proof with asimpl;eauto. intros Hsub Hchar Hn. revert Δ Hsub Hchar.
  induction Hn; intros; try constructor; eauto.
  -destruct (Hchar n); eauto. rewrite H in *. eauto.
  -eapply IHHn2.
    +auto_case; try apply reflexivity. repeat rewrite nthd_cons.
     change (var_type (S n)) with (ren_type ↑ (var_type n)). repeat rewrite map_nthd.
     eapply weakening. eapply Hsub.
    +auto_case. repeat rewrite nthd_cons.
     change (var_type (S n)) with (ren_type ↑ (var_type n)). repeat rewrite map_nthd.
     destruct (Hchar n); eauto using transitivity_ren. rewrite H. now left.
Qed.

Fact congr_NORM `{arrow_flag} {Δ Γ s t} : Γ=Δ -> Γ |-N s <: t -> Δ |-N s <: t.
Proof. congruence. Qed.

Derive Signature for subN.
Fact trans_at `{arrow_flag} t : transitivity_at t.
Proof with asimpl;eauto. unfold transitivity_at. induction t; intros.
  - depind H; try discriminate. inversion H. exact H0. apply NVar,IHsubN,H0.
  - depind H; try discriminate. apply NVar,IHsubN,H0. depind H0; try discriminate. auto.
  - depind H; try discriminate. apply NVar,IHsubN; assumption.
    depind H2; try discriminate. auto. asimpl in *. inversion H1. inversion H2.
    rewrite (DPI H5). rewrite (DPI H11). rewrite (DPI H4). apply NArr.
    eapply IHt1. erewrite H9. rewrite <- (DPI H4). now rewrite (DPI H8). now erewrite H6.
    eapply IHt2. now erewrite H7. erewrite H10. rewrite <- (DPI H4). now rewrite (DPI H8).
  - depind H; try discriminate. apply NVar,IHsubN; assumption. depind H2; try discriminate. auto.
    asimpl in *. inversion H1. inversion H2. clear IHsubN0 IHsubN1 IHsubN2 IHsubN3.
    apply NAll. eapply IHt1. now rewrite (DPI H6). now rewrite (DPI H4). eapply IHt2.
      + rewrite (DPI H5). eapply narrow; try apply H0.
        *intros [|x]. asimpl. eapply weakening. rewrite <- (DPI H4). now rewrite (DPI H6).
         asimpl. apply reflexivity.
        *intros [|x]; try cbn; eauto. right. apply transitivity_ren. rewrite <- (DPI H4).
         apply transitivity_ren. unfold transitivity_at. intros. eapply IHt1; eauto.
       + now rewrite (DPI H7).
Qed.

Fact transitivity  `{arrow_flag}{Γ s t u} : Γ |-N s <: t -> Γ |-N t <: u -> Γ |-N s <: u.
Proof. eauto using trans_at. Qed.

Fixpoint encode_off (t:@type' arrow_off) : Fsub_na.type.
Proof. inversion t.
  -exact (Fsub_na.var_type H).
  -exact (Fsub_na.top).
  -apply (Fsub_na.all); apply encode_off. exact H. exact H0.
Defined.

Fixpoint encode_on (t:@type' arrow_on) : Fsub.type.
Proof. inversion t.
  -exact (Fsub.var_type H).
  -exact (Fsub.top).
  -apply Fsub.arr; apply encode_on. exact H. exact H0.
  -apply Fsub.all; apply encode_on. exact H. exact H0.
Defined.

Derive Signature for type'.
Derive Signature for Fsub.sub.
Derive Signature for Fsub_na.sub'.

Fact encode_off_inj {σ τ} : encode_off σ = encode_off τ -> σ = τ.
Proof. depind σ; depind τ; cbn; try discriminate; try congruence.
  intro. inversion H. apply congr_all. now apply IHσ1. now apply IHσ2.
Qed.
Fact encode_off_inv τ : {t & encode_off t = τ}.
Proof. induction τ.
  -now exists (var_type n).
  -now exists top.
  -destruct IHτ1 as [σ1 H1]. destruct IHτ2 as [σ2 H2]. exists (all σ1 σ2). cbn.
   now rewrite H1,H2.
Qed.
Fact encode_off_ren t ξ : encode_off (ren_type ξ t) = Fsub_na.ren_type ξ (encode_off t).
Proof. depind t; cbn; auto. discriminate. now rewrite IHt1,IHt2.
Qed.
Fact encode_on_inj {σ τ} : encode_on σ = encode_on τ -> σ = τ.
Proof. depind σ; depind τ; cbn; try discriminate; try congruence;
  try inversion H; try now rewrite (DPI H1). inversion H0. rewrite (DPI H2),(DPI H3).
  cbn. intro. inversion H1. now rewrite (IHσ1 _ H5),(IHσ2 _ H6).
  intro. inversion H. now rewrite (IHσ1 _ H1),(IHσ2 _ H2).
Qed.
Fact encode_on_inv τ : {t & encode_on t = τ}.
Proof. induction τ.
  -now exists (var_type n).
  -now exists top.
  -destruct IHτ1 as [σ1 H1]. destruct IHτ2 as [σ2 H2]. exists (arr σ1 σ2). cbn.
   now rewrite H1,H2.
  -destruct IHτ1 as [σ1 H1]. destruct IHτ2 as [σ2 H2]. exists (all σ1 σ2). cbn.
   now rewrite H1,H2.
Qed.
Fact encode_on_ren t ξ : encode_on (ren_type ξ t) = Fsub.ren_type ξ (encode_on t).
Proof. depind t; cbn; auto.
  *inversion H. rewrite (DPI H1). cbn. now rewrite IHt1,IHt2.
  *now rewrite IHt1,IHt2.
Qed.
Fact sub'_ctx_congr {Γ Γ' σ τ} : Γ=Γ' -> Γ |-' σ <: τ -> Γ' |-' σ <: τ.
Proof. congruence. Qed.
Fact sub_ctx_congr {Γ Γ' σ τ} : Γ=Γ' -> Γ |- σ <: τ -> Γ' |- σ <: τ.
Proof. congruence. Qed.

Lemma subN_iff_sub_off {Γ σ τ} : Γ |-N' σ <: τ <-> map encode_off Γ |-' encode_off σ <: encode_off τ.
Proof. split.
  -intro Hn. depind Hn; cbn.
    *now apply Fsub_na.Refl.
    *eapply (Fsub_na.Trans _ _ (nth_default (Fsub_na.var_type n) (map encode_off Γ) n )); auto.
     now apply Fsub_na.Var. change (Fsub_na.var_type n) with (encode_off (var_type n)).
     now rewrite nth_default_eq,map_nth,<- nth_default_eq.
    *now apply Fsub_na.Top.
    *discriminate.
    *apply Fsub_na.All. assumption. revert IHHn2. apply sub'_ctx_congr. rewrite <- map_cons.
     repeat rewrite map_map. apply map_ext. intro. apply encode_off_ren.
  -intro H. depind H; cbn.
    *rewrite (encode_off_inj H). apply reflexivity.
    *destruct (encode_off_inv τ) as [t Ht]. apply (@transitivity _ _ _ t).
     apply IHsub'1. now rewrite Ht.
     apply IHsub'2. now rewrite Ht.
    *depind τ0; try discriminate. apply NTop.
    *depind σ; try discriminate. rewrite <- H in H0. inversion H. rewrite <- H2 in *.
     rewrite nth_default_eq,map_nth in H0.
     rewrite (encode_off_inj H0). rewrite <- nth_default_eq. apply NVar,reflexivity.
    *depind σ; try discriminate. depind τ; try discriminate. inversion H1. inversion H2.
     apply NAll. apply IHsub'1. now rewrite H6,H4. apply IHsub'2.
     rewrite H5,H7,<- H6,<- map_cons. repeat rewrite map_map.
     enough ((fun x : type' => encode_off (ren_type ↑ x))=(fun x : type' => Fsub_na.ren_type ↑ (encode_off x))) as ->.
     reflexivity. fext. intro. apply encode_off_ren.
Qed.

Lemma subN_iff_sub_on {Γ σ τ} : Γ |-N+ σ <: τ <-> map encode_on Γ |- encode_on σ <: encode_on τ.
Proof. split.
  -intro Hn. depind Hn.
    *now apply Refl.
    *eapply Trans; eauto. rewrite nth_default_eq,<- map_nth,<-nth_default_eq. cbn. now apply Fsub.Var.
    *now apply Top.
    *inversion H. rewrite (DPI H1). rewrite (DPI H2). rewrite (DPI H3). now apply Arr.
    *cbn. apply All. auto. revert IHHn2. apply sub_ctx_congr. rewrite <- map_cons.
     repeat rewrite map_map. apply map_ext. intro. apply encode_on_ren.
  -intro H. depind H; cbn.
    *rewrite (encode_on_inj H). apply reflexivity.
    *destruct (encode_on_inv τ) as [t Ht]. apply (@transitivity _ _ _ t).
     apply IHsub1. now rewrite Ht.
     apply IHsub2. now rewrite Ht.
    *depind τ0; try discriminate. apply NTop. inversion H. rewrite (DPI H2) in H0. discriminate.
    *depind σ; try discriminate. rewrite <- H in H0. inversion H. rewrite <- H2 in *.
     rewrite nth_default_eq,map_nth in H0.
     rewrite (encode_on_inj H0). rewrite <- nth_default_eq. apply NVar,reflexivity.
     inversion H. rewrite (DPI H3) in H0. discriminate.
    *depind σ; try discriminate. depind τ; try discriminate. inversion H1. inversion H2.
     rewrite (DPI H6),(DPI H7) in *. inversion H3. inversion H4. apply NArr.
     apply IHsub1. now rewrite H8,H10. apply IHsub2. now rewrite H9,H11.
    *depind σ; try discriminate; inversion H1; depind τ; try discriminate; inversion H2.
     rewrite (DPI H5) in H3. discriminate. rewrite (DPI H5) in H2. discriminate.
     inversion H1. rewrite (DPI H9) in H3. discriminate.
     apply NAll. apply IHsub1. now rewrite H6,H4. apply IHsub2.
     rewrite H5,H7,<- H6,<- map_cons. repeat rewrite map_map.
     enough ((fun x : type' => encode_on (ren_type ↑ x))=(fun x : type' => Fsub.ren_type ↑ (encode_on x))) as ->.
     reflexivity. fext. intro. apply encode_on_ren.
Qed.

Definition encoding_off : @ctx arrow_off * (@type' arrow_off * @type' arrow_off)
  -> list Fsub_na.type * (Fsub_na.type * Fsub_na.type)
:= fun H : ctx * (type' * type') => let (Γ, p) := H in let (σ, τ) := p
  in pair (list_map encode_off Γ) (pair (encode_off σ) (encode_off τ)).


Definition encoding_on : @ctx arrow_on * (@type' arrow_on * @type' arrow_on)
  -> list Fsub.type * (Fsub.type * Fsub.type)
:= fun H : ctx * (type' * type') => let (Γ, p) := H in let (σ, τ) := p
  in pair (list_map encode_on Γ) (pair (encode_on σ) (encode_on τ)).

End argument.


(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.


Theorem reduction_off : FsubN_off_SUBTYPE ⪯ Fsub'_SUBTYPE.
Proof. exists encoding_off. intros [Γ [s t]]. cbn. eapply subN_iff_sub_off.
Qed.


Theorem reduction_on : FsubN_on_SUBTYPE ⪯ Fsub_SUBTYPE.
Proof. exists encoding_on. intros [Γ [s t]]. cbn. apply subN_iff_sub_on.
Qed.