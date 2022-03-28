Require Import FsubN FsubN_to_Fsub Utils.Various_utils.
From Equations Require Import Equations.

Section argument.

Definition types2termtype : @ctx arrow_on * (type * type) ->
      @ctx arrow_on * @ctx arrow_on * (term * type).
Proof. intros [Γ [σ τ]]. split. split. exact nil. exact Γ. split.
  -exact (tapp (tlam τ (lam (var_type 0) (var_term 0))) σ).
  -exact (arr σ σ).
Defined.

Definition add_arrow `{arrow_flag} (t: type') : type.
Proof. induction t.
  -apply var_type,n.
  -apply top.
  -apply arr. exact IHt1. exact IHt2.
  -apply all. exact IHt1. exact IHt2.
Defined.

Definition add_arrows : {b : arrow_flag & (@FsubN.ctx b * (@type' b * @type' b))%type} ->
      @FsubN.ctx arrow_on * (type * type).
Proof. intros [b [Γ [s t]]]. split. exact (map add_arrow Γ). split. exact (add_arrow s). exact (add_arrow t).
Defined.

Fact add_arrow_ren `{arrow_flag} t r : add_arrow (ren_type r t) = ren_type r (add_arrow t).
Proof. revert r. induction t; intros; asimpl; simpl; auto.
  +apply congr_arr; auto.
  +apply congr_all; auto.
Qed.

Fixpoint add_arrow_on (t : type) : add_arrow t = t.
Proof. refine (match t with var_type n => _ | top => _ | arr t1 t2 => _ | all t1 t2 => _ end).
  -destruct a. intro. auto. now simpl.
  -destruct a. intro. auto. now simpl.
  -simpl. apply congr_arr; apply add_arrow_on.
  -destruct a. intro. auto. simpl. apply congr_all; apply add_arrow_on.
Qed.

Definition generalzation : @ctx arrow_off * (@type' arrow_off * @type' arrow_off) ->
      {b : arrow_flag & (@ctx b * (@type' b * @type' b))%type}.
Proof. intros [Γ [s t]]. exists arrow_off. split. exact Γ. split. exact s. exact t.
Defined.

End argument.

(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Derive Signature for chkN.

Theorem reduction_off2gen : FsubN_off_SUBTYPE ⪯ FsubN_SUBTYPE.
Proof. exists generalzation. intros [Γ [s t]]. tauto.
Qed.

Theorem reduction_gen2on : FsubN_SUBTYPE ⪯ FsubN_on_SUBTYPE.
Proof. exists add_arrows. intros [b [Γ [s t]]]. cbn. split; intro.
  -induction H; simpl.
    +apply NRefl.
    +apply NVar. revert IHsubN. change (@var_type arrow_on n) with (@add_arrow b (var_type n)).
     rewrite map_nthd. apply congr_NORM; auto.
    +apply NTop.
    +apply NArr; assumption.
    +apply NAll. assumption. revert IHsubN2. apply congr_NORM; auto.
     rewrite <- map_cons. repeat rewrite map_map. apply map_ext. intro. apply add_arrow_ren.
  -depind H.
    +destruct s; try discriminate. destruct t; try discriminate. simpl in *. inversion H. inversion H0. apply NRefl.
    +destruct s0; try discriminate. simpl in *. inversion H0. apply NVar. apply IHsubN.
     change (@var_type arrow_on n) with (@add_arrow b (var_type n)). now rewrite map_nthd.
    +destruct t; try discriminate. apply NTop.
    +destruct s; try discriminate. inversion H1. pose (Ht := DPI H6). rewrite add_arrow_on in Ht. rewrite Ht.
     apply NArr. apply IHsubN1. rewrite (DPI H3). rewrite (add_arrow_on t1). now rewrite H4.
     apply IHsubN2. rewrite (DPI H3). rewrite H5. now rewrite add_arrow_on.
    +destruct s; try discriminate. destruct t; try discriminate. simpl in *. apply NAll.
      *apply IHsubN1. inversion H1. rewrite (DPI H4). inversion H2. now rewrite (DPI H6).
      *apply IHsubN2. inversion H1. rewrite (DPI H5). inversion H2. rewrite (DPI H7).
       enough (list_map add_arrow (list_map (ren_type ↑) (t3 :: Γ0)) =
             ren_type ↑ t1 :: list_map (ren_type ↑) (list_map add_arrow Γ0) ) by now rewrite H3.
       rewrite <- (DPI H6). repeat rewrite <- map_cons. repeat rewrite map_map. apply map_ext.
       intro. apply add_arrow_ren.
Qed.

Theorem reduction : FsubN_on_SUBTYPE ⪯ FsubN_TYPECHK.
Proof.
 exists types2termtype. intros [Γ [σ τ]]. cbn. split.
  -intros. eexists. eapply NTInst. eapply NTAbst. eapply NAbst. eapply NTVar.
   eassumption. now simpl.
  -intros [i H]. depind H; try discriminate; try clear IHchkN.
    (* Subsumption (Λ τ (λ 0 0)) σ : t  and  t <: σ->σ *)
    +revert σ0 H H0. induction i using Wf_nat.lt_wf_ind. intros.
     depind H0; try discriminate; try clear IHchkN.
      *clear H1. revert σ H H0. induction i using Wf_nat.lt_wf_ind. intros.
       depind H1; try discriminate; try clear IHchkN. eapply (H0 _ _ _ (transitivity H H3) H1).
       inversion H5. rewrite <- H7 in *. rewrite <- H8 in *. clear H3 H5 H7 H8.
       depind H1; try discriminate; try clear IHchkN.
       { revert σ H H1. induction i using Wf_nat.lt_wf_ind. intros.
         depind H5; try discriminate; try clear IHchkN. eapply (H1 _ _ _ (transitivity H H2) H5).
         inversion H1. inversion H2. eapply (transitivity H0).
         rewrite <- (DPI H10). rewrite <- (DPI H7). now rewrite <- (DPI H6). }
       inversion H0. inversion H. now rewrite <- (DPI H7).
      *depind H0; try discriminate; try clear IHchkN; inversion H4; clear H4.
        2: { inversion H. rewrite <- (DPI H6). exact H1. }
        rewrite H2 in *. rewrite <- H7 in *. rewrite <- H8 in *. clear H2 H3 H5 H7 H8.
        eapply (@transitivity _ _ _ σ0). exact H1. clear H1. cbn.
        (* Subsumption Λ τ (λ 0 0) : t  and  t <: ∀ σ0 τ0 *) 
        revert σ H0 H. induction i using Wf_nat.lt_wf_ind. intros.
        depind H0; try discriminate; try clear IHchkN.
        { eapply (H1 i _ _ H0). exact (transitivity H H2). }
        inversion H1. clear H1. rewrite <- H5 in *. rewrite <- H4 in *. clear H H4 H5.
        inversion H2. rewrite <- (DPI H). rewrite <- (DPI H5). now rewrite <- (DPI H1).
    +inversion H2. rewrite <- H4 in *. rewrite <- H5 in *. clear H2 H4 H5. 
     depind H; try discriminate; try clear IHchkN.
     2: { inversion H0. rewrite <- H5. inversion H1. rewrite H5. rewrite <- (DPI H7).  assumption. }
     (* Subsumption Λ τ (λ 0 0) : t  and  t <: ∀ σ0 τ0*)
     revert σ H0 H. induction i using Wf_nat.lt_wf_ind. intros.
     depind H3; try discriminate; try clear IHchkN. eapply (H0 _ _ _ (transitivity H H4) H3).
     inversion H4. rewrite <- H6 in *. rewrite <- H7 in *. clear H4 H6 H7.
     clear H. depind H3; try discriminate; try clear IHchkN.
     (* Subsumption λ 0 0 : t  and  t <: σ->σ *)
     { revert σ H H3. induction i using Wf_nat.lt_wf_ind. intros.
       depind H4; try discriminate; try clear IHchkN; inversion H0; eapply (transitivity H1);
       rewrite <- (DPI H6); rewrite <- (DPI H10); now rewrite <- (DPI H7). } 
     inversion H0. apply (transitivity H1). rewrite <- (DPI H4). rewrite <- (DPI H8). now rewrite <- (DPI H5).
 Unshelve. all: auto.
Qed.