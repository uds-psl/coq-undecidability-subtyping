(** * Modular syntax of types and terms *)

Require Export unscoped.

Section type.

Inductive arrow_flag := arrow_off | arrow_on.
Existing Class arrow_flag.
Existing Instance arrow_on | 1.
Existing Instance arrow_off | 0.

Inductive type'  : arrow_flag -> Type :=
  | var_type {b} : ( fin ) -> type' b
  | top {b} : type' b
  | arr : ( type' arrow_on  ) -> ( type' arrow_on  ) -> type' arrow_on
  | all {b} : ( type' b  ) -> ( type' b  ) -> type' b.
Arguments type' {_}.

Lemma congr_top `{arrow_flag} : top  = top  .
Proof. congruence. Qed.

Lemma congr_arr  { s0 : @type' arrow_on  } { s1 : @type' arrow_on  } { t0 : @type' arrow_on  } { t1 : @type' arrow_on  } (H1 : s0 = t0) (H2 : s1 = t1) : arr  s0 s1 = arr  t0 t1 .
Proof. congruence. Qed.

Lemma congr_all `{arrow_flag} { s0 : type'   } { s1 : type'   } { t0 : type'   } { t1 : type'   } (H1 : s0 = t0) (H2 : s1 = t1) : all  s0 s1 = all  t0 t1 .
Proof. congruence. Qed.

Definition upRen_type_type   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_type `{arrow_flag}  (xitype : ( fin ) -> fin) (s : type' ) : type'  :=
    match s return type'  with
    | var_type  s => (var_type ) (xitype s)
    | top   => top 
    | arr  s0 s1 => arr  ((ren_type xitype) s0) ((ren_type xitype) s1)
    | all  s0 s1 => all  ((ren_type xitype) s0) ((ren_type (upRen_type_type xitype)) s1)
    end.

Definition up_type_type  `{arrow_flag} (sigma : ( fin ) -> type' ) : ( fin ) -> type'  :=
  (scons) ((var_type ) (var_zero)) ((funcomp) (ren_type (shift)) sigma).

Fixpoint subst_type `{arrow_flag} (sigmatype : ( fin ) -> type' ) (s : type' ) : type'.
Proof. destruct s.
  -apply sigmatype,n.
  -exact top.
  -apply arr; apply (subst_type _ sigmatype). exact s1. exact s2.
  -apply all. apply (subst_type _ sigmatype),s1. apply (subst_type _ (up_type_type sigmatype)),s2.
Defined.

Definition upId_type_type `{arrow_flag} (sigma : ( fin ) -> type' ) (Eq : forall x, sigma x = (var_type ) x) : forall x, (up_type_type sigma) x = (var_type ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.
Fixpoint idSubst_type `{arrow_flag} (sigmatype : ( fin ) -> type' ) (Eqtype : forall x, sigmatype x = (var_type ) x) (s : type' ) : subst_type sigmatype s = s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply (idSubst_type _ _ Eqtype).
  -apply congr_all. apply (idSubst_type _ _ Eqtype). apply idSubst_type,upId_type_type,Eqtype.
Defined.

Definition upExtRen_type_type   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_type_type xi) x = (upRen_type_type zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_type `{arrow_flag}  (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (Eqtype : forall x, xitype x = zetatype x) (s : type' ) : ren_type xitype s = ren_type zetatype s.
Proof. destruct s.
  -apply (ap var_type (Eqtype n)).
  -apply congr_top.
  -apply congr_arr; apply extRen_type,Eqtype.
  -apply congr_all. apply extRen_type,Eqtype. apply extRen_type,upExtRen_type_type,Eqtype.
Defined.

Definition upExt_type_type `{arrow_flag}  (sigma : ( fin ) -> type' ) (tau : ( fin ) -> type' ) (Eq : forall x, sigma x = tau x) : forall x, (up_type_type sigma) x = (up_type_type tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_type `{arrow_flag}  (sigmatype : ( fin ) -> type' ) (tautype : ( fin ) -> type' ) (Eqtype : forall x, sigmatype x = tautype x) (s : type' ) : subst_type sigmatype s = subst_type tautype s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply ext_type,Eqtype.
  -apply congr_all. apply ext_type,Eqtype. apply ext_type,upExt_type_type,Eqtype.
Defined.

Definition up_ren_ren_type_type `{arrow_flag}   (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_type_type tau) (upRen_type_type xi)) x = (upRen_type_type theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_type `{arrow_flag}  (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (rhotype : ( fin ) -> fin) (Eqtype : forall x, ((funcomp) zetatype xitype) x = rhotype x) (s : type' ) : ren_type zetatype (ren_type xitype s) = ren_type rhotype s.
Proof. destruct s.
  -apply (ap var_type (Eqtype n)).
  -apply congr_top.
  -apply congr_arr; apply compRenRen_type,Eqtype.
  -apply congr_all. apply compRenRen_type,Eqtype. apply compRenRen_type,up_ren_ren,Eqtype.
Defined.

Definition up_ren_subst_type_type  `{arrow_flag}  (xi : ( fin ) -> fin) (tau : ( fin ) -> type' ) (theta : ( fin ) -> type' ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_type_type tau) (upRen_type_type xi)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_type `{arrow_flag}  (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type' ) (thetatype : ( fin ) -> type' ) (Eqtype : forall x, ((funcomp) tautype xitype) x = thetatype x) (s : type' ) : subst_type tautype (ren_type xitype s) = subst_type thetatype s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply compRenSubst_type,Eqtype.
  -apply congr_all. apply compRenSubst_type,Eqtype. apply compRenSubst_type,up_ren_subst_type_type,Eqtype.
Defined.

Definition up_subst_ren_type_type  `{arrow_flag}  (sigma : ( fin ) -> type' ) (zetatype : ( fin ) -> fin) (theta : ( fin ) -> type' ) (Eq : forall x, ((funcomp) (ren_type zetatype) sigma) x = theta x) : forall x, ((funcomp) (ren_type (upRen_type_type zetatype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_type (shift) (upRen_type_type zetatype) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_type zetatype (shift) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_type  `{arrow_flag}  (sigmatype : ( fin ) -> type' ) (zetatype : ( fin ) -> fin) (thetatype : ( fin ) -> type' ) (Eqtype : forall x, ((funcomp) (ren_type zetatype) sigmatype) x = thetatype x) (s : type' ) : ren_type zetatype (subst_type sigmatype s) = subst_type thetatype s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply compSubstRen_type,Eqtype.
  -apply congr_all. apply compSubstRen_type,Eqtype. apply compSubstRen_type,up_subst_ren_type_type,Eqtype.
Defined.

Definition up_subst_subst_type_type  `{arrow_flag}  (sigma : ( fin ) -> type' ) (tautype : ( fin ) -> type' ) (theta : ( fin ) -> type' ) (Eq : forall x, ((funcomp) (subst_type tautype) sigma) x = theta x) : forall x, ((funcomp) (subst_type (up_type_type tautype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_type (shift) (up_type_type tautype) ((funcomp) (up_type_type tautype) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_type tautype (shift) ((funcomp) (ren_type (shift)) tautype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_type `{arrow_flag}  (sigmatype : ( fin ) -> type' ) (tautype : ( fin ) -> type' ) (thetatype : ( fin ) -> type' ) (Eqtype : forall x, ((funcomp) (subst_type tautype) sigmatype) x = thetatype x) (s : type' ) : subst_type tautype (subst_type sigmatype s) = subst_type thetatype s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply compSubstSubst_type,Eqtype.
  -apply congr_all. apply compSubstSubst_type,Eqtype. apply compSubstSubst_type,up_subst_subst_type_type,Eqtype.
Defined.

Definition rinstInst_up_type_type `{arrow_flag}  (xi : ( fin ) -> fin) (sigma : ( fin ) -> type' ) (Eq : forall x, ((funcomp) (var_type ) xi) x = sigma x) : forall x, ((funcomp) (var_type ) (upRen_type_type xi)) x = (up_type_type sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_type `{arrow_flag}  (xitype : ( fin ) -> fin) (sigmatype : ( fin ) -> type' ) (Eqtype : forall x, ((funcomp) (var_type ) xitype) x = sigmatype x) (s : type' ) : ren_type xitype s = subst_type sigmatype s.
Proof. destruct s.
  -apply Eqtype.
  -apply congr_top.
  -apply congr_arr; apply rinst_inst_type,Eqtype.
  -apply congr_all. apply rinst_inst_type,Eqtype. apply rinst_inst_type,rinstInst_up_type_type,Eqtype.
Defined.

Lemma rinstInst_type  `{arrow_flag} (xitype : ( fin ) -> fin) : ren_type xitype = subst_type ((funcomp) (var_type ) xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_type xitype (_) (fun n => eq_refl) x)). Qed.

Lemma instId_type `{arrow_flag} : subst_type (var_type ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_type (var_type ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_type  `{arrow_flag} : @ren_type _  (id) = id .
Proof. exact ((eq_trans) (rinstInst_type ((id) (_))) instId_type). Qed.

Lemma varL_type `{arrow_flag}  (sigmatype : ( fin ) -> type' ) : (funcomp) (subst_type sigmatype) (var_type ) = sigmatype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_type `{arrow_flag}  (xitype : ( fin ) -> fin) : (funcomp) (ren_type xitype) (var_type ) = (funcomp) (var_type ) xitype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_type `{arrow_flag}   (sigmatype : ( fin ) -> type' ) (tautype : ( fin ) -> type' ) (s : type' ) : subst_type tautype (subst_type sigmatype s) = subst_type ((funcomp) (subst_type tautype) sigmatype) s .
Proof. exact (compSubstSubst_type sigmatype tautype (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_type  `{arrow_flag}  (sigmatype : ( fin ) -> type' ) (tautype : ( fin ) -> type' ) : (funcomp) (subst_type tautype) (subst_type sigmatype) = subst_type ((funcomp) (subst_type tautype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_type sigmatype tautype n)). Qed.

Lemma compRen_type `{arrow_flag}   (sigmatype : ( fin ) -> type' ) (zetatype : ( fin ) -> fin) (s : type' ) : ren_type zetatype (subst_type sigmatype s) = subst_type ((funcomp) (ren_type zetatype) sigmatype) s .
Proof. exact (compSubstRen_type sigmatype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_type  `{arrow_flag}  (sigmatype : ( fin ) -> type' ) (zetatype : ( fin ) -> fin) : (funcomp) (ren_type zetatype) (subst_type sigmatype) = subst_type ((funcomp) (ren_type zetatype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_type sigmatype zetatype n)). Qed.

Lemma renComp_type  `{arrow_flag}  (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type' ) (s : type' ) : subst_type tautype (ren_type xitype s) = subst_type ((funcomp) tautype xitype) s .
Proof. exact (compRenSubst_type xitype tautype (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_type  `{arrow_flag}  (xitype : ( fin ) -> fin) (tautype : ( fin ) -> type' ) : (funcomp) (subst_type tautype) (ren_type xitype) = subst_type ((funcomp) tautype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_type xitype tautype n)). Qed.

Lemma renRen_type  `{arrow_flag}  (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (s : type' ) : ren_type zetatype (ren_type xitype s) = ren_type ((funcomp) zetatype xitype) s .
Proof. exact (compRenRen_type xitype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_type  `{arrow_flag}  (xitype : ( fin ) -> fin) (zetatype : ( fin ) -> fin) : (funcomp) (ren_type zetatype) (ren_type xitype) = ren_type ((funcomp) zetatype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_type xitype zetatype n)). Qed.

End type.

Section term.

Inductive term  : Type :=
  | var_term : ( fin ) -> term  
  | app : ( term    ) -> ( term    ) -> term  
  | lam : ( @type' arrow_on  ) -> ( term    ) -> term  
  | tapp : ( term    ) -> ( @type' arrow_on   ) -> term  
  | tlam : ( @type' arrow_on   ) -> ( term    ) -> term  .

Lemma congr_app  { s0 : term    } { s1 : term    } { t0 : term    } { t1 : term    } (H1 : s0 = t0) (H2 : s1 = t1) : app   s0 s1 = app   t0 t1 .
Proof. congruence. Qed.

Lemma congr_lam  { s0 : @type' arrow_on   } { s1 : term    } { t0 : @type' arrow_on   } { t1 : term    } (H1 : s0 = t0) (H2 : s1 = t1) : lam   s0 s1 = lam   t0 t1 .
Proof. congruence. Qed.

Lemma congr_tapp  { s0 : term    } { s1 : @type' arrow_on   } { t0 : term    } { t1 : @type' arrow_on   } (H1 : s0 = t0) (H2 : s1 = t1) : tapp   s0 s1 = tapp   t0 t1 .
Proof. congruence. Qed.

Lemma congr_tlam  { s0 : @type' arrow_on   } { s1 : term    } { t0 : @type' arrow_on   } { t1 : term    } (H1 : s0 = t0) (H2 : s1 = t1) : tlam   s0 s1 = tlam   t0 t1 .
Proof. congruence. Qed.

Definition upRen_type_term   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  xi.

Definition upRen_term_type   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  xi.

Definition upRen_term_term   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_term   (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (s : term  ) : term   :=
    match s return term   with
    | var_term   s => (var_term  ) (xiterm s)
    | app   s0 s1 => app   ((ren_term xitype xiterm) s0) ((ren_term xitype xiterm) s1)
    | lam   s0 s1 => lam   ((ren_type xitype) s0) ((ren_term (upRen_term_type xitype) (upRen_term_term xiterm)) s1)
    | tapp   s0 s1 => tapp   ((ren_term xitype xiterm) s0) ((ren_type xitype) s1)
    | tlam   s0 s1 => tlam   ((ren_type xitype) s0) ((ren_term (upRen_type_type xitype) (upRen_type_term xiterm)) s1)
    end.

Definition up_type_term   (sigma : ( fin ) -> term  ) : ( fin ) -> term   :=
  (funcomp) (ren_term (shift) (id)) sigma.

Definition up_term_type   (sigma : ( fin ) -> @type' arrow_on ) : ( fin ) -> @type' arrow_on  :=
  (funcomp) (ren_type (id)) sigma.

Definition up_term_term   (sigma : ( fin ) -> term  ) : ( fin ) -> term   :=
  (scons) ((var_term  ) (var_zero)) ((funcomp) (ren_term (id) (shift)) sigma).

Fixpoint subst_term   (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (s : term  ) : term   :=
    match s return term   with
    | var_term   s => sigmaterm s
    | app   s0 s1 => app   ((subst_term sigmatype sigmaterm) s0) ((subst_term sigmatype sigmaterm) s1)
    | lam   s0 s1 => lam   ((subst_type sigmatype) s0) ((subst_term (up_term_type sigmatype) (up_term_term sigmaterm)) s1)
    | tapp   s0 s1 => tapp   ((subst_term sigmatype sigmaterm) s0) ((subst_type sigmatype) s1)
    | tlam   s0 s1 => tlam   ((subst_type sigmatype) s0) ((subst_term (up_type_type sigmatype) (up_type_term sigmaterm)) s1)
    end.

Definition upId_type_term  (sigma : ( fin ) -> term  ) (Eq : forall x, sigma x = (var_term  ) x) : forall x, (up_type_term sigma) x = (var_term  ) x :=
  fun n => (ap) (ren_term (shift) (id)) (Eq n).

Definition upId_term_type  (sigma : ( fin ) -> @type' arrow_on ) (Eq : forall x, sigma x = (var_type ) x) : forall x, (up_term_type sigma) x = (var_type ) x :=
  fun n => (ap) (ren_type (id)) (Eq n).

Definition upId_term_term  (sigma : ( fin ) -> term  ) (Eq : forall x, sigma x = (var_term  ) x) : forall x, (up_term_term sigma) x = (var_term  ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_term  (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (Eqtype : forall x, sigmatype x = (var_type ) x) (Eqterm : forall x, sigmaterm x = (var_term  ) x) (s : term  ) : subst_term sigmatype sigmaterm s = s :=
    match s return subst_term sigmatype sigmaterm s = s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((idSubst_term sigmatype sigmaterm Eqtype Eqterm) s0) ((idSubst_term sigmatype sigmaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((idSubst_type sigmatype Eqtype) s0) ((idSubst_term (up_term_type sigmatype) (up_term_term sigmaterm) (upId_term_type (_) Eqtype) (upId_term_term (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((idSubst_term sigmatype sigmaterm Eqtype Eqterm) s0) ((idSubst_type sigmatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((idSubst_type sigmatype Eqtype) s0) ((idSubst_term (up_type_type sigmatype) (up_type_term sigmaterm) (upId_type_type (_) Eqtype) (upId_type_term (_) Eqterm)) s1)
    end.

Definition upExtRen_type_term   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_type_term xi) x = (upRen_type_term zeta) x :=
  fun n => Eq n.

Definition upExtRen_term_type   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_type xi) x = (upRen_term_type zeta) x :=
  fun n => Eq n.

Definition upExtRen_term_term   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_term xi) x = (upRen_term_term zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_term   (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (Eqtype : forall x, xitype x = zetatype x) (Eqterm : forall x, xiterm x = zetaterm x) (s : term  ) : ren_term xitype xiterm s = ren_term zetatype zetaterm s :=
    match s return ren_term xitype xiterm s = ren_term zetatype zetaterm s with
    | var_term   s => (ap) (var_term  ) (Eqterm s)
    | app   s0 s1 => congr_app ((extRen_term xitype xiterm zetatype zetaterm Eqtype Eqterm) s0) ((extRen_term xitype xiterm zetatype zetaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((extRen_type xitype zetatype Eqtype) s0) ((extRen_term (upRen_term_type xitype) (upRen_term_term xiterm) (upRen_term_type zetatype) (upRen_term_term zetaterm) (upExtRen_term_type (_) (_) Eqtype) (upExtRen_term_term (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((extRen_term xitype xiterm zetatype zetaterm Eqtype Eqterm) s0) ((extRen_type xitype zetatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((extRen_type xitype zetatype Eqtype) s0) ((extRen_term (upRen_type_type xitype) (upRen_type_term xiterm) (upRen_type_type zetatype) (upRen_type_term zetaterm) (upExtRen_type_type (_) (_) Eqtype) (upExtRen_type_term (_) (_) Eqterm)) s1)
    end.

Definition upExt_type_term   (sigma : ( fin ) -> term  ) (tau : ( fin ) -> term  ) (Eq : forall x, sigma x = tau x) : forall x, (up_type_term sigma) x = (up_type_term tau) x :=
  fun n => (ap) (ren_term (shift) (id)) (Eq n).

Definition upExt_term_type   (sigma : ( fin ) -> @type' arrow_on ) (tau : ( fin ) -> @type' arrow_on ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_type sigma) x = (up_term_type tau) x :=
  fun n => (ap) (ren_type (id)) (Eq n).

Definition upExt_term_term   (sigma : ( fin ) -> term  ) (tau : ( fin ) -> term  ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_term   (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (Eqtype : forall x, sigmatype x = tautype x) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term  ) : subst_term sigmatype sigmaterm s = subst_term tautype tauterm s :=
    match s return subst_term sigmatype sigmaterm s = subst_term tautype tauterm s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((ext_term sigmatype sigmaterm tautype tauterm Eqtype Eqterm) s0) ((ext_term sigmatype sigmaterm tautype tauterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((ext_type sigmatype tautype Eqtype) s0) ((ext_term (up_term_type sigmatype) (up_term_term sigmaterm) (up_term_type tautype) (up_term_term tauterm) (upExt_term_type (_) (_) Eqtype) (upExt_term_term (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((ext_term sigmatype sigmaterm tautype tauterm Eqtype Eqterm) s0) ((ext_type sigmatype tautype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((ext_type sigmatype tautype Eqtype) s0) ((ext_term (up_type_type sigmatype) (up_type_term sigmaterm) (up_type_type tautype) (up_type_term tauterm) (upExt_type_type (_) (_) Eqtype) (upExt_type_term (_) (_) Eqterm)) s1)
    end.

Definition up_ren_ren_type_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_type_term tau) (upRen_type_term xi)) x = (upRen_type_term theta) x :=
  Eq.

Definition up_ren_ren_term_type    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_term_type tau) (upRen_term_type xi)) x = (upRen_term_type theta) x :=
  Eq.

Definition up_ren_ren_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_term_term tau) (upRen_term_term xi)) x = (upRen_term_term theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (rhotype : ( fin ) -> fin) (rhoterm : ( fin ) -> fin) (Eqtype : forall x, ((funcomp) zetatype xitype) x = rhotype x) (Eqterm : forall x, ((funcomp) zetaterm xiterm) x = rhoterm x) (s : term  ) : ren_term zetatype zetaterm (ren_term xitype xiterm s) = ren_term rhotype rhoterm s :=
    match s return ren_term zetatype zetaterm (ren_term xitype xiterm s) = ren_term rhotype rhoterm s with
    | var_term   s => (ap) (var_term  ) (Eqterm s)
    | app   s0 s1 => congr_app ((compRenRen_term xitype xiterm zetatype zetaterm rhotype rhoterm Eqtype Eqterm) s0) ((compRenRen_term xitype xiterm zetatype zetaterm rhotype rhoterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((compRenRen_type xitype zetatype rhotype Eqtype) s0) ((compRenRen_term (upRen_term_type xitype) (upRen_term_term xiterm) (upRen_term_type zetatype) (upRen_term_term zetaterm) (upRen_term_type rhotype) (upRen_term_term rhoterm) Eqtype (up_ren_ren (_) (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((compRenRen_term xitype xiterm zetatype zetaterm rhotype rhoterm Eqtype Eqterm) s0) ((compRenRen_type xitype zetatype rhotype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((compRenRen_type xitype zetatype rhotype Eqtype) s0) ((compRenRen_term (upRen_type_type xitype) (upRen_type_term xiterm) (upRen_type_type zetatype) (upRen_type_term zetaterm) (upRen_type_type rhotype) (upRen_type_term rhoterm) (up_ren_ren (_) (_) (_) Eqtype) Eqterm) s1)
    end.

Definition up_ren_subst_type_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> term  ) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_type_term tau) (upRen_type_term xi)) x = (up_type_term theta) x :=
  fun n => (ap) (ren_term (shift) (id)) (Eq n).

Definition up_ren_subst_term_type    (xi : ( fin ) -> fin) (tau : ( fin ) -> @type' arrow_on ) (theta : ( fin ) -> @type' arrow_on ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_term_type tau) (upRen_term_type xi)) x = (up_term_type theta) x :=
  fun n => (ap) (ren_type (id)) (Eq n).

Definition up_ren_subst_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> term  ) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_term_term tau) (upRen_term_term xi)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (thetatype : ( fin ) -> @type' arrow_on ) (thetaterm : ( fin ) -> term  ) (Eqtype : forall x, ((funcomp) tautype xitype) x = thetatype x) (Eqterm : forall x, ((funcomp) tauterm xiterm) x = thetaterm x) (s : term  ) : subst_term tautype tauterm (ren_term xitype xiterm s) = subst_term thetatype thetaterm s :=
    match s return subst_term tautype tauterm (ren_term xitype xiterm s) = subst_term thetatype thetaterm s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((compRenSubst_term xitype xiterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s0) ((compRenSubst_term xitype xiterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((compRenSubst_type xitype tautype thetatype Eqtype) s0) ((compRenSubst_term (upRen_term_type xitype) (upRen_term_term xiterm) (up_term_type tautype) (up_term_term tauterm) (up_term_type thetatype) (up_term_term thetaterm) (up_ren_subst_term_type (_) (_) (_) Eqtype) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((compRenSubst_term xitype xiterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s0) ((compRenSubst_type xitype tautype thetatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((compRenSubst_type xitype tautype thetatype Eqtype) s0) ((compRenSubst_term (upRen_type_type xitype) (upRen_type_term xiterm) (up_type_type tautype) (up_type_term tauterm) (up_type_type thetatype) (up_type_term thetaterm) (up_ren_subst_type_type (_) (_) (_) Eqtype) (up_ren_subst_type_term (_) (_) (_) Eqterm)) s1)
    end.

Definition up_subst_ren_type_term    (sigma : ( fin ) -> term  ) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (ren_term zetatype zetaterm) sigma) x = theta x) : forall x, ((funcomp) (ren_term (upRen_type_type zetatype) (upRen_type_term zetaterm)) (up_type_term sigma)) x = (up_type_term theta) x :=
  fun n => (eq_trans) (compRenRen_term (shift) (id) (upRen_type_type zetatype) (upRen_type_term zetaterm) ((funcomp) (shift) zetatype) ((funcomp) (id) zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_term zetatype zetaterm (shift) (id) ((funcomp) (shift) zetatype) ((funcomp) (id) zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_term (shift) (id)) (Eq n))).

Definition up_subst_ren_term_type    (sigma : ( fin ) -> @type' arrow_on ) (zetatype : ( fin ) -> fin) (theta : ( fin ) -> @type' arrow_on ) (Eq : forall x, ((funcomp) (ren_type zetatype) sigma) x = theta x) : forall x, ((funcomp) (ren_type (upRen_term_type zetatype)) (up_term_type sigma)) x = (up_term_type theta) x :=
  fun n => (eq_trans) (compRenRen_type (id) (upRen_term_type zetatype) ((funcomp) (id) zetatype) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compRenRen_type zetatype (id) ((funcomp) (id) zetatype) (fun x => eq_refl) (sigma n))) ((ap) (ren_type (id)) (Eq n))).

Definition up_subst_ren_term_term    (sigma : ( fin ) -> term  ) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (ren_term zetatype zetaterm) sigma) x = theta x) : forall x, ((funcomp) (ren_term (upRen_term_type zetatype) (upRen_term_term zetaterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_term (id) (shift) (upRen_term_type zetatype) (upRen_term_term zetaterm) ((funcomp) (id) zetatype) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_term zetatype zetaterm (id) (shift) ((funcomp) (id) zetatype) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (id) (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (thetatype : ( fin ) -> @type' arrow_on ) (thetaterm : ( fin ) -> term  ) (Eqtype : forall x, ((funcomp) (ren_type zetatype) sigmatype) x = thetatype x) (Eqterm : forall x, ((funcomp) (ren_term zetatype zetaterm) sigmaterm) x = thetaterm x) (s : term  ) : ren_term zetatype zetaterm (subst_term sigmatype sigmaterm s) = subst_term thetatype thetaterm s :=
    match s return ren_term zetatype zetaterm (subst_term sigmatype sigmaterm s) = subst_term thetatype thetaterm s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((compSubstRen_term sigmatype sigmaterm zetatype zetaterm thetatype thetaterm Eqtype Eqterm) s0) ((compSubstRen_term sigmatype sigmaterm zetatype zetaterm thetatype thetaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s0) ((compSubstRen_term (up_term_type sigmatype) (up_term_term sigmaterm) (upRen_term_type zetatype) (upRen_term_term zetaterm) (up_term_type thetatype) (up_term_term thetaterm) (up_subst_ren_term_type (_) (_) (_) Eqtype) (up_subst_ren_term_term (_) (_) (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((compSubstRen_term sigmatype sigmaterm zetatype zetaterm thetatype thetaterm Eqtype Eqterm) s0) ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s0) ((compSubstRen_term (up_type_type sigmatype) (up_type_term sigmaterm) (upRen_type_type zetatype) (upRen_type_term zetaterm) (up_type_type thetatype) (up_type_term thetaterm) (up_subst_ren_type_type (_) (_) (_) Eqtype) (up_subst_ren_type_term (_) (_) (_) (_) Eqterm)) s1)
    end.

Definition up_subst_subst_type_term    (sigma : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (subst_term tautype tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_type_type tautype) (up_type_term tauterm)) (up_type_term sigma)) x = (up_type_term theta) x :=
  fun n => (eq_trans) (compRenSubst_term (shift) (id) (up_type_type tautype) (up_type_term tauterm) ((funcomp) (up_type_type tautype) (shift)) ((funcomp) (up_type_term tauterm) (id)) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_term tautype tauterm (shift) (id) ((funcomp) (ren_type (shift)) tautype) ((funcomp) (ren_term (shift) (id)) tauterm) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (ren_term (shift) (id)) (Eq n))).

Definition up_subst_subst_term_type    (sigma : ( fin ) -> @type' arrow_on ) (tautype : ( fin ) -> @type' arrow_on ) (theta : ( fin ) -> @type' arrow_on ) (Eq : forall x, ((funcomp) (subst_type tautype) sigma) x = theta x) : forall x, ((funcomp) (subst_type (up_term_type tautype)) (up_term_type sigma)) x = (up_term_type theta) x :=
  fun n => (eq_trans) (compRenSubst_type (id) (up_term_type tautype) ((funcomp) (up_term_type tautype) (id)) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstRen_type tautype (id) ((funcomp) (ren_type (id)) tautype) (fun x => eq_refl) (sigma n))) ((ap) (ren_type (id)) (Eq n))).

Definition up_subst_subst_term_term    (sigma : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (theta : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (subst_term tautype tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_type tautype) (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_term (id) (shift) (up_term_type tautype) (up_term_term tauterm) ((funcomp) (up_term_type tautype) (id)) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_term tautype tauterm (id) (shift) ((funcomp) (ren_type (id)) tautype) ((funcomp) (ren_term (id) (shift)) tauterm) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (id) (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (thetatype : ( fin ) -> @type' arrow_on ) (thetaterm : ( fin ) -> term  ) (Eqtype : forall x, ((funcomp) (subst_type tautype) sigmatype) x = thetatype x) (Eqterm : forall x, ((funcomp) (subst_term tautype tauterm) sigmaterm) x = thetaterm x) (s : term  ) : subst_term tautype tauterm (subst_term sigmatype sigmaterm s) = subst_term thetatype thetaterm s :=
    match s return subst_term tautype tauterm (subst_term sigmatype sigmaterm s) = subst_term thetatype thetaterm s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((compSubstSubst_term sigmatype sigmaterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s0) ((compSubstSubst_term sigmatype sigmaterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s0) ((compSubstSubst_term (up_term_type sigmatype) (up_term_term sigmaterm) (up_term_type tautype) (up_term_term tauterm) (up_term_type thetatype) (up_term_term thetaterm) (up_subst_subst_term_type (_) (_) (_) Eqtype) (up_subst_subst_term_term (_) (_) (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((compSubstSubst_term sigmatype sigmaterm tautype tauterm thetatype thetaterm Eqtype Eqterm) s0) ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s0) ((compSubstSubst_term (up_type_type sigmatype) (up_type_term sigmaterm) (up_type_type tautype) (up_type_term tauterm) (up_type_type thetatype) (up_type_term thetaterm) (up_subst_subst_type_type (_) (_) (_) Eqtype) (up_subst_subst_type_term (_) (_) (_) (_) Eqterm)) s1)
    end.

Definition rinstInst_up_type_term   (xi : ( fin ) -> fin) (sigma : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (var_term  ) xi) x = sigma x) : forall x, ((funcomp) (var_term  ) (upRen_type_term xi)) x = (up_type_term sigma) x :=
  fun n => (ap) (ren_term (shift) (id)) (Eq n).

Definition rinstInst_up_term_type   (xi : ( fin ) -> fin) (sigma : ( fin ) -> @type' arrow_on ) (Eq : forall x, ((funcomp) (var_type ) xi) x = sigma x) : forall x, ((funcomp) (var_type ) (upRen_term_type xi)) x = (up_term_type sigma) x :=
  fun n => (ap) (ren_type (id)) (Eq n).

Definition rinstInst_up_term_term   (xi : ( fin ) -> fin) (sigma : ( fin ) -> term  ) (Eq : forall x, ((funcomp) (var_term  ) xi) x = sigma x) : forall x, ((funcomp) (var_term  ) (upRen_term_term xi)) x = (up_term_term sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (id) (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_term   (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (Eqtype : forall x, ((funcomp) (var_type ) xitype) x = sigmatype x) (Eqterm : forall x, ((funcomp) (var_term  ) xiterm) x = sigmaterm x) (s : term  ) : ren_term xitype xiterm s = subst_term sigmatype sigmaterm s :=
    match s return ren_term xitype xiterm s = subst_term sigmatype sigmaterm s with
    | var_term   s => Eqterm s
    | app   s0 s1 => congr_app ((rinst_inst_term xitype xiterm sigmatype sigmaterm Eqtype Eqterm) s0) ((rinst_inst_term xitype xiterm sigmatype sigmaterm Eqtype Eqterm) s1)
    | lam   s0 s1 => congr_lam ((rinst_inst_type xitype sigmatype Eqtype) s0) ((rinst_inst_term (upRen_term_type xitype) (upRen_term_term xiterm) (up_term_type sigmatype) (up_term_term sigmaterm) (rinstInst_up_term_type (_) (_) Eqtype) (rinstInst_up_term_term (_) (_) Eqterm)) s1)
    | tapp   s0 s1 => congr_tapp ((rinst_inst_term xitype xiterm sigmatype sigmaterm Eqtype Eqterm) s0) ((rinst_inst_type xitype sigmatype Eqtype) s1)
    | tlam   s0 s1 => congr_tlam ((rinst_inst_type xitype sigmatype Eqtype) s0) ((rinst_inst_term (upRen_type_type xitype) (upRen_type_term xiterm) (up_type_type sigmatype) (up_type_term sigmaterm) (rinstInst_up_type_type (_) (_) Eqtype) (rinstInst_up_type_term (_) (_) Eqterm)) s1)
    end.

Lemma rinstInst_term   (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) : ren_term xitype xiterm = subst_term ((funcomp) (var_type ) xitype) ((funcomp) (var_term  ) xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_term xitype xiterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) x)). Qed.

Lemma instId_term  : subst_term (var_type ) (var_term  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_type ) (var_term  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_term  : @ren_term     (id) (id) = id .
Proof. exact ((eq_trans) (rinstInst_term ((id) (_)) ((id) (_))) instId_term). Qed.

Lemma varL_term   (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) : (funcomp) (subst_term sigmatype sigmaterm) (var_term  ) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_term   (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) : (funcomp) (ren_term xitype xiterm) (var_term  ) = (funcomp) (var_term  ) xiterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (s : term  ) : subst_term tautype tauterm (subst_term sigmatype sigmaterm s) = subst_term ((funcomp) (subst_type tautype) sigmatype) ((funcomp) (subst_term tautype tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmatype sigmaterm tautype tauterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) : (funcomp) (subst_term tautype tauterm) (subst_term sigmatype sigmaterm) = subst_term ((funcomp) (subst_type tautype) sigmatype) ((funcomp) (subst_term tautype tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmatype sigmaterm tautype tauterm n)). Qed.

Lemma compRen_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (s : term  ) : ren_term zetatype zetaterm (subst_term sigmatype sigmaterm s) = subst_term ((funcomp) (ren_type zetatype) sigmatype) ((funcomp) (ren_term zetatype zetaterm) sigmaterm) s .
Proof. exact (compSubstRen_term sigmatype sigmaterm zetatype zetaterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compRen'_term    (sigmatype : ( fin ) -> @type' arrow_on ) (sigmaterm : ( fin ) -> term  ) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetatype zetaterm) (subst_term sigmatype sigmaterm) = subst_term ((funcomp) (ren_type zetatype) sigmatype) ((funcomp) (ren_term zetatype zetaterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_term sigmatype sigmaterm zetatype zetaterm n)). Qed.

Lemma renComp_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) (s : term  ) : subst_term tautype tauterm (ren_term xitype xiterm s) = subst_term ((funcomp) tautype xitype) ((funcomp) tauterm xiterm) s .
Proof. exact (compRenSubst_term xitype xiterm tautype tauterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renComp'_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (tautype : ( fin ) -> @type' arrow_on ) (tauterm : ( fin ) -> term  ) : (funcomp) (subst_term tautype tauterm) (ren_term xitype xiterm) = subst_term ((funcomp) tautype xitype) ((funcomp) tauterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_term xitype xiterm tautype tauterm n)). Qed.

Lemma renRen_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (s : term  ) : ren_term zetatype zetaterm (ren_term xitype xiterm s) = ren_term ((funcomp) zetatype xitype) ((funcomp) zetaterm xiterm) s .
Proof. exact (compRenRen_term xitype xiterm zetatype zetaterm (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma renRen'_term    (xitype : ( fin ) -> fin) (xiterm : ( fin ) -> fin) (zetatype : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetatype zetaterm) (ren_term xitype xiterm) = ren_term ((funcomp) zetatype xitype) ((funcomp) zetaterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_term xitype xiterm zetatype zetaterm n)). Qed.

End term.


















Global Instance Subst_type {f : arrow_flag}  :  Subst1 (( fin ) -> type' f ) (type' f) (type' f) := @subst_type f.

Global Instance Subst_term   : Subst2 (( fin ) -> type' arrow_on) (( fin ) -> term  ) (term  ) (term  ) := @subst_term     .

Global Instance Ren_type  {f : arrow_flag}  : Ren1 (( fin ) -> fin) (type' f) (type' f) := @ren_type f.

Global Instance Ren_term   : Ren2 (( fin ) -> fin) (( fin ) -> fin) (term  ) (term  ) := @ren_term     .

Global Instance VarInstance_type {f : arrow_flag} : Var (fin) (type' f) := @var_type  f.

Notation "x '__type'" := (var_type x) (at level 5, format "x __type") : subst_scope.

Notation "x '__type'" := (@ids (_) (_) VarInstance_type x) (at level 5, only printing, format "x __type") : subst_scope.

Notation "'var'" := (var_type) (only printing, at level 1) : subst_scope.

Global Instance VarInstance_term  : Var (fin) (term  ) := @var_term   .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_type X Y := up_type : ( X ) -> Y.

Notation "↑__type" := (up_type) (only printing) : subst_scope.

Class Up_term X Y := up_term : ( X ) -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__type" := (up_type_type) (only printing) : subst_scope.

Global Instance Up_type_type  {f : arrow_flag} : Up_type (_) (_) := @up_type_type f  .

Notation "↑__term" := (up_term_type) (only printing) : subst_scope.

Global Instance Up_term_type   : Up_type (_) (_) := @up_term_type   .

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Global Instance Up_term_term   : Up_term (_) (_) := @up_term_term    .

Notation "↑__type" := (up_type_term) (only printing) : subst_scope.

Global Instance Up_type_term   : Up_term (_) (_) := @up_type_term    .

(* Notation "s [ sigmatype ]" := (subst_type sigmatype s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "[ sigmatype ]" := (subst_type sigmatype) (at level 1, left associativity, only printing) : fscope.

(* Notation "s ⟨ xitype ⟩" := (ren_type xitype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitype ⟩" := (ren_type xitype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigmatype ; sigmaterm ]" := (subst_term sigmatype sigmaterm s) (at level 7, left associativity, only printing) : subst_scope. *)

Notation "[ sigmatype ; sigmaterm ]" := (subst_term sigmatype sigmaterm) (at level 1, left associativity, only printing) : fscope.

(* Notation "s ⟨ xitype ; xiterm ⟩" := (ren_term xitype xiterm s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xitype ; xiterm ⟩" := (ren_term xitype xiterm) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Subst_term,  Ren_type,  Ren_term,  VarInstance_type,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Subst_term,  Ren_type,  Ren_term,  VarInstance_type,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_type| progress rewrite ?compComp_type| progress rewrite ?compComp'_type| progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?rinstId_type| progress rewrite ?compRen_type| progress rewrite ?compRen'_type| progress rewrite ?renComp_type| progress rewrite ?renComp'_type| progress rewrite ?renRen_type| progress rewrite ?renRen'_type| progress rewrite ?rinstId_term| progress rewrite ?compRen_term| progress rewrite ?compRen'_term| progress rewrite ?renComp_term| progress rewrite ?renComp'_term| progress rewrite ?renRen_term| progress rewrite ?renRen'_term| progress rewrite ?varL_type| progress rewrite ?varL_term| progress rewrite ?varLRen_type| progress rewrite ?varLRen_term| progress (unfold up_ren, upRen_type_type, upRen_term_type, upRen_term_term, upRen_type_term, up_type_type, up_term_type, up_term_term, up_type_term)| progress (cbn [subst_type subst_term ren_type ren_term])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_type in *| progress rewrite ?compComp_type in *| progress rewrite ?compComp'_type in *| progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?rinstId_type in *| progress rewrite ?compRen_type in *| progress rewrite ?compRen'_type in *| progress rewrite ?renComp_type in *| progress rewrite ?renComp'_type in *| progress rewrite ?renRen_type in *| progress rewrite ?renRen'_type in *| progress rewrite ?rinstId_term in *| progress rewrite ?compRen_term in *| progress rewrite ?compRen'_term in *| progress rewrite ?renComp_term in *| progress rewrite ?renComp'_term in *| progress rewrite ?renRen_term in *| progress rewrite ?renRen'_term in *| progress rewrite ?varL_type in *| progress rewrite ?varL_term in *| progress rewrite ?varLRen_type in *| progress rewrite ?varLRen_term in *| progress (unfold up_ren, upRen_type_type, upRen_term_type, upRen_term_term, upRen_type_term, up_type_type, up_term_type, up_term_term, up_type_term in * )| progress (cbn [subst_type subst_term ren_type ren_term] in * )| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_type); try repeat (erewrite rinstInst_term).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_type); try repeat (erewrite <- rinstInst_term).

Definition type0 := type' arrow_off.
Definition type := type' arrow_on.

Arguments type' {_}.
