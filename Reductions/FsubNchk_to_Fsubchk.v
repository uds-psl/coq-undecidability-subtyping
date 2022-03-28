(** * Reduction from typechecking in the Normal System Fsub with arrows to typechecking in the full System Fsub with arrows *)
(* begin details : Imports *)
Require Import Fsub FsubN FsubN_to_Fsub Utils.Various_utils.
From Equations Require Import Equations.

Require Import Undecidability.Synthetic.Definitions.
(* end details *)

Section argument.

Fixpoint encode_term (t:term) : Fsub.term.
Proof. destruct t eqn:?.
  -exact (Fsub.var_term n).
  -apply Fsub.app. apply encode_term,t0_1. apply encode_term,t0_2.
  -apply Fsub.lam. apply encode_on,t0. apply encode_term,t1.
  -apply Fsub.tapp. apply encode_term,t0. apply encode_on,t1.
  -apply Fsub.tlam. apply encode_on,t0. apply encode_term,t1.
Defined.

Definition encoding : @ctx arrow_on * @ctx arrow_on * (term * type)
  -> list Fsub.type * list Fsub.type * (Fsub.term * Fsub.type).
Proof. intros [[Γ Δ] [t τ]]. split.
  -split. exact (map encode_on Γ). exact (map encode_on Δ).
  -split. exact (encode_term t). exact (encode_on τ).
Defined.

Fact chk_ctx_congr {Γ Γ' Δ Δ' t τ} : Δ=Δ' -> Γ=Γ' -> Δ;Γ |- t : τ -> Δ';Γ' |- t : τ.
Proof. congruence. Qed.

Fact encode_on_subst θ τ : encode_on (subst_type θ τ) = Fsub.subst_type (θ >> encode_on) (encode_on τ).
Proof. revert θ. depind τ; intro; cbn; auto.
  -inversion H. rewrite (DPI H1). cbn. now rewrite IHτ1,IHτ2.
  -rewrite IHτ1,IHτ2. unfold up_type_type.
   enough (((var_type var_zero, θ >> ren_type ↑) >> encode_on)
      =(Fsub.var_type 0, (θ >> encode_on) >> Fsub.ren_type ↑)) as ->. auto.
   fext. auto_case. apply encode_on_ren.
Qed.

Fact encode_arr {t σ τ} : encode_on t = Fsub.arr σ τ
  -> {σ0 & { τ0 & t=arr σ0 τ0 /\ encode_on σ0 = σ /\ encode_on τ0=τ}}.
Proof. depind t; try discriminate. inversion H. rewrite (DPI H1).
  intro. inversion H0. exists t1,t2. tauto.
Qed.

Fact encode_all {t σ τ} : encode_on t = Fsub.all σ τ
  -> {σ0 & { τ0 & t=all σ0 τ0 /\ encode_on σ0 = σ /\ encode_on τ0=τ}}.
Proof. depind t; try discriminate.
  -inversion H. rewrite (DPI H1). discriminate.
  -intro. inversion H. exists t1,t2. tauto.
Qed.

Derive Signature for chk.

End argument.

(** ** Synthetic Reduction 
*)


Theorem reduction : FsubN_TYPECHK ⪯  Fsub_TYPECHK.
Proof. exists encoding. intros [[Γ Δ] [σ τ]]. cbn. split.
  -intros [i H]. depind H; cbn.
    +eapply Subs. exact IHchkN. apply subN_iff_sub_on,H0.
    +rewrite nth_default_eq,<- map_nth,<-nth_default_eq. apply TVar.
    +now apply Abst.
    +eapply Inst; eassumption.
    +eapply TAbst. revert IHchkN. apply chk_ctx_congr.
      *repeat rewrite map_map. apply map_ext. intro. apply encode_on_ren.
      *rewrite <- map_cons. repeat rewrite map_map. apply map_ext. intro. apply encode_on_ren.
    +cbn in IHchkN. eapply TInst; try eassumption. apply subN_iff_sub_on,H0.
     rewrite H1. rewrite encode_on_subst. enough ((σ1.. >> encode_on)=(encode_on σ1, Fsub.var_type)) as ->. auto.
     fext. auto_case.
  -intro H.  depind H.
    +destruct (encode_on_inv σ) as [σ' Hs]. edestruct IHchk as [i HN].
     2:{ exists (S i). eapply NSubs. exact HN. apply subN_iff_sub_on. now rewrite Hs. }
     now rewrite Hs.
    +depind σ; try discriminate. inversion H. rewrite <- H2 in *.
     rewrite nth_default_eq in H0. change (Fsub.var_type n0) with (encode_on (var_type n0)) in H0.
     rewrite map_nth in H0. rewrite (encode_on_inj H0),<-nth_default_eq.
     exists 0. apply NTVar.
    +depind σ0; try discriminate. inversion H0. destruct (encode_arr H1) as [τ1 [τ2 [H5 [H6 H7]]]].
     rewrite H5. rewrite <- H3 in H6. rewrite (encode_on_inj H6).
     edestruct IHchk as [i HN]. 2:{ exists (S i). eapply NAbst,HN. }
     cbn. now rewrite H3,H4,H7.
    +destruct (encode_on_inv σ) as [σ' Hs]. depind σ0; try discriminate.
     inversion H1. edestruct IHchk1 as [i HN1]. 2: { edestruct IHchk2 as [j HN2].
     2: { exists (S (max i j)). eapply NInst. exact HN1. exact HN2. }
     rewrite H4. now erewrite Hs. } rewrite H3. cbn. now rewrite Hs.
    +depind σ0; try discriminate. inversion H0. destruct (encode_all H1) as [τ1 [τ2 [H5 [H6 H7]]]].
     rewrite H5. rewrite <- H3 in H6. rewrite (encode_on_inj H6).
     edestruct IHchk as [i HN]. 2:{ exists (S i). eapply NTAbst,HN. } cbn.
     rewrite H4,H7. repeat rewrite map_map. rewrite encode_on_ren,H3.
     enough ((fun x : type' => encode_on (ren_type ↑ x))=(fun x : type' => Fsub.ren_type ↑ (encode_on x))) as ->.
     auto. fext. intro. now rewrite encode_on_ren.
    +destruct (encode_on_inv σ) as [σ' Hs]. destruct (encode_on_inv τ) as [τ' Ht].
     depind σ0; try discriminate. inversion H2. edestruct IHchk as [i HN].
     2:{ exists (S i). eapply NTInst; try eassumption. apply subN_iff_sub_on. rewrite H5,Hs. exact H0.
     apply encode_on_inj. rewrite H1,encode_on_subst. enough ((σ1, Fsub.var_type)=(t0.. >> encode_on)) as ->.
     now rewrite Ht. fext. auto_case. } cbn. now rewrite H4,Hs,Ht.
Qed.
