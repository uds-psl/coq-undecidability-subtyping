(** * Well-scoped syntax example *)

Require Export fintype.

Section type.
Inductive type (ntype : nat) : Type :=
  | var_type : (fin) (ntype) -> type (ntype)
  | all : type  (ntype) -> type  ((S) ntype) -> type (ntype).

Lemma congr_all { mtype : nat } { s0 : type  (mtype) } { s1 : type  ((S) mtype) } { t0 : type  (mtype) } { t1 : type  ((S) mtype) } (H1 : s0 = t0) (H2 : s1 = t1) : all (mtype) s0 s1 = all (mtype) t0 t1 .
Proof. congruence. Qed.

Definition upRen_type_type { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_type { mtype : nat } { ntype : nat } (xitype : (fin) (mtype) -> (fin) (ntype)) (s : type (mtype)) : type (ntype) :=
    match s return type (ntype) with
    | var_type (_) s => (var_type (ntype)) (xitype s)
    | all (_) s0 s1 => all (ntype) ((ren_type xitype) s0) ((ren_type (upRen_type_type xitype)) s1)
    end.

Definition up_type_type { m : nat } { ntype : nat } (sigma : (fin) (m) -> type (ntype)) : (fin) ((S) (m)) -> type ((S) ntype) :=
  (scons) ((var_type ((S) ntype)) (var_zero)) ((funcomp) (ren_type (shift)) sigma).

Fixpoint subst_type { mtype : nat } { ntype : nat } (sigmatype : (fin) (mtype) -> type (ntype)) (s : type (mtype)) : type (ntype) :=
    match s return type (ntype) with
    | var_type (_) s => sigmatype s
    | all (_) s0 s1 => all (ntype) ((subst_type sigmatype) s0) ((subst_type (up_type_type sigmatype)) s1)
    end.

Definition upId_type_type { mtype : nat } (sigma : (fin) (mtype) -> type (mtype)) (Eq : forall x, sigma x = (var_type (mtype)) x) : forall x, (up_type_type sigma) x = (var_type ((S) mtype)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_type { mtype : nat } (sigmatype : (fin) (mtype) -> type (mtype)) (Eqtype : forall x, sigmatype x = (var_type (mtype)) x) (s : type (mtype)) : subst_type sigmatype s = s :=
    match s return subst_type sigmatype s = s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((idSubst_type sigmatype Eqtype) s0) ((idSubst_type (up_type_type sigmatype) (upId_type_type (_) Eqtype)) s1)
    end.

Definition upExtRen_type_type { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_type_type xi) x = (upRen_type_type zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_type { mtype : nat } { ntype : nat } (xitype : (fin) (mtype) -> (fin) (ntype)) (zetatype : (fin) (mtype) -> (fin) (ntype)) (Eqtype : forall x, xitype x = zetatype x) (s : type (mtype)) : ren_type xitype s = ren_type zetatype s :=
    match s return ren_type xitype s = ren_type zetatype s with
    | var_type (_) s => (ap) (var_type (ntype)) (Eqtype s)
    | all (_) s0 s1 => congr_all ((extRen_type xitype zetatype Eqtype) s0) ((extRen_type (upRen_type_type xitype) (upRen_type_type zetatype) (upExtRen_type_type (_) (_) Eqtype)) s1)
    end.

Definition upExt_type_type { m : nat } { ntype : nat } (sigma : (fin) (m) -> type (ntype)) (tau : (fin) (m) -> type (ntype)) (Eq : forall x, sigma x = tau x) : forall x, (up_type_type sigma) x = (up_type_type tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_type { mtype : nat } { ntype : nat } (sigmatype : (fin) (mtype) -> type (ntype)) (tautype : (fin) (mtype) -> type (ntype)) (Eqtype : forall x, sigmatype x = tautype x) (s : type (mtype)) : subst_type sigmatype s = subst_type tautype s :=
    match s return subst_type sigmatype s = subst_type tautype s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((ext_type sigmatype tautype Eqtype) s0) ((ext_type (up_type_type sigmatype) (up_type_type tautype) (upExt_type_type (_) (_) Eqtype)) s1)
    end.

Definition up_ren_ren_type_type { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_type_type tau) (upRen_type_type xi)) x = (upRen_type_type theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) (rhotype : (fin) (mtype) -> (fin) (ltype)) (Eqtype : forall x, ((funcomp) zetatype xitype) x = rhotype x) (s : type (mtype)) : ren_type zetatype (ren_type xitype s) = ren_type rhotype s :=
    match s return ren_type zetatype (ren_type xitype s) = ren_type rhotype s with
    | var_type (_) s => (ap) (var_type (ltype)) (Eqtype s)
    | all (_) s0 s1 => congr_all ((compRenRen_type xitype zetatype rhotype Eqtype) s0) ((compRenRen_type (upRen_type_type xitype) (upRen_type_type zetatype) (upRen_type_type rhotype) (up_ren_ren (_) (_) (_) Eqtype)) s1)
    end.

Definition up_ren_subst_type_type { k : nat } { l : nat } { mtype : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> type (mtype)) (theta : (fin) (k) -> type (mtype)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_type_type tau) (upRen_type_type xi)) x = (up_type_type theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (tautype : (fin) (ktype) -> type (ltype)) (thetatype : (fin) (mtype) -> type (ltype)) (Eqtype : forall x, ((funcomp) tautype xitype) x = thetatype x) (s : type (mtype)) : subst_type tautype (ren_type xitype s) = subst_type thetatype s :=
    match s return subst_type tautype (ren_type xitype s) = subst_type thetatype s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((compRenSubst_type xitype tautype thetatype Eqtype) s0) ((compRenSubst_type (upRen_type_type xitype) (up_type_type tautype) (up_type_type thetatype) (up_ren_subst_type_type (_) (_) (_) Eqtype)) s1)
    end.

Definition up_subst_ren_type_type { k : nat } { ltype : nat } { mtype : nat } (sigma : (fin) (k) -> type (ltype)) (zetatype : (fin) (ltype) -> (fin) (mtype)) (theta : (fin) (k) -> type (mtype)) (Eq : forall x, ((funcomp) (ren_type zetatype) sigma) x = theta x) : forall x, ((funcomp) (ren_type (upRen_type_type zetatype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_type (shift) (upRen_type_type zetatype) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_type zetatype (shift) ((funcomp) (shift) zetatype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) (thetatype : (fin) (mtype) -> type (ltype)) (Eqtype : forall x, ((funcomp) (ren_type zetatype) sigmatype) x = thetatype x) (s : type (mtype)) : ren_type zetatype (subst_type sigmatype s) = subst_type thetatype s :=
    match s return ren_type zetatype (subst_type sigmatype s) = subst_type thetatype s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((compSubstRen_type sigmatype zetatype thetatype Eqtype) s0) ((compSubstRen_type (up_type_type sigmatype) (upRen_type_type zetatype) (up_type_type thetatype) (up_subst_ren_type_type (_) (_) (_) Eqtype)) s1)
    end.

Definition up_subst_subst_type_type { k : nat } { ltype : nat } { mtype : nat } (sigma : (fin) (k) -> type (ltype)) (tautype : (fin) (ltype) -> type (mtype)) (theta : (fin) (k) -> type (mtype)) (Eq : forall x, ((funcomp) (subst_type tautype) sigma) x = theta x) : forall x, ((funcomp) (subst_type (up_type_type tautype)) (up_type_type sigma)) x = (up_type_type theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_type (shift) (up_type_type tautype) ((funcomp) (up_type_type tautype) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_type tautype (shift) ((funcomp) (ren_type (shift)) tautype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_type (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (tautype : (fin) (ktype) -> type (ltype)) (thetatype : (fin) (mtype) -> type (ltype)) (Eqtype : forall x, ((funcomp) (subst_type tautype) sigmatype) x = thetatype x) (s : type (mtype)) : subst_type tautype (subst_type sigmatype s) = subst_type thetatype s :=
    match s return subst_type tautype (subst_type sigmatype s) = subst_type thetatype s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((compSubstSubst_type sigmatype tautype thetatype Eqtype) s0) ((compSubstSubst_type (up_type_type sigmatype) (up_type_type tautype) (up_type_type thetatype) (up_subst_subst_type_type (_) (_) (_) Eqtype)) s1)
    end.

Definition rinstInst_up_type_type { m : nat } { ntype : nat } (xi : (fin) (m) -> (fin) (ntype)) (sigma : (fin) (m) -> type (ntype)) (Eq : forall x, ((funcomp) (var_type (ntype)) xi) x = sigma x) : forall x, ((funcomp) (var_type ((S) ntype)) (upRen_type_type xi)) x = (up_type_type sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_type (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_type { mtype : nat } { ntype : nat } (xitype : (fin) (mtype) -> (fin) (ntype)) (sigmatype : (fin) (mtype) -> type (ntype)) (Eqtype : forall x, ((funcomp) (var_type (ntype)) xitype) x = sigmatype x) (s : type (mtype)) : ren_type xitype s = subst_type sigmatype s :=
    match s return ren_type xitype s = subst_type sigmatype s with
    | var_type (_) s => Eqtype s
    | all (_) s0 s1 => congr_all ((rinst_inst_type xitype sigmatype Eqtype) s0) ((rinst_inst_type (upRen_type_type xitype) (up_type_type sigmatype) (rinstInst_up_type_type (_) (_) Eqtype)) s1)
    end.

Lemma rinstInst_type { mtype : nat } { ntype : nat } (xitype : (fin) (mtype) -> (fin) (ntype)) : ren_type xitype = subst_type ((funcomp) (var_type (ntype)) xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_type xitype (_) (fun n => eq_refl) x)). Qed.

Lemma instId_type { mtype : nat } : subst_type (var_type (mtype)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_type (var_type (mtype)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_type { mtype : nat } : @ren_type (mtype) (mtype) (id) = id .
Proof. exact ((eq_trans) (rinstInst_type ((id) (_))) instId_type). Qed.

Lemma varL_type { mtype : nat } { ntype : nat } (sigmatype : (fin) (mtype) -> type (ntype)) : (funcomp) (subst_type sigmatype) (var_type (mtype)) = sigmatype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_type { mtype : nat } { ntype : nat } (xitype : (fin) (mtype) -> (fin) (ntype)) : (funcomp) (ren_type xitype) (var_type (mtype)) = (funcomp) (var_type (ntype)) xitype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (tautype : (fin) (ktype) -> type (ltype)) (s : type (mtype)) : subst_type tautype (subst_type sigmatype s) = subst_type ((funcomp) (subst_type tautype) sigmatype) s .
Proof. exact (compSubstSubst_type sigmatype tautype (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (tautype : (fin) (ktype) -> type (ltype)) : (funcomp) (subst_type tautype) (subst_type sigmatype) = subst_type ((funcomp) (subst_type tautype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_type sigmatype tautype n)). Qed.

Lemma compRen_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) (s : type (mtype)) : ren_type zetatype (subst_type sigmatype s) = subst_type ((funcomp) (ren_type zetatype) sigmatype) s .
Proof. exact (compSubstRen_type sigmatype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_type { ktype : nat } { ltype : nat } { mtype : nat } (sigmatype : (fin) (mtype) -> type (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) : (funcomp) (ren_type zetatype) (subst_type sigmatype) = subst_type ((funcomp) (ren_type zetatype) sigmatype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_type sigmatype zetatype n)). Qed.

Lemma renComp_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (tautype : (fin) (ktype) -> type (ltype)) (s : type (mtype)) : subst_type tautype (ren_type xitype s) = subst_type ((funcomp) tautype xitype) s .
Proof. exact (compRenSubst_type xitype tautype (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (tautype : (fin) (ktype) -> type (ltype)) : (funcomp) (subst_type tautype) (ren_type xitype) = subst_type ((funcomp) tautype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_type xitype tautype n)). Qed.

Lemma renRen_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) (s : type (mtype)) : ren_type zetatype (ren_type xitype s) = ren_type ((funcomp) zetatype xitype) s .
Proof. exact (compRenRen_type xitype zetatype (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_type { ktype : nat } { ltype : nat } { mtype : nat } (xitype : (fin) (mtype) -> (fin) (ktype)) (zetatype : (fin) (ktype) -> (fin) (ltype)) : (funcomp) (ren_type zetatype) (ren_type xitype) = ren_type ((funcomp) zetatype xitype) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_type xitype zetatype n)). Qed.

End type.

Arguments var_type {ntype}.

Arguments all {ntype}.

Global Instance Subst_type { mtype : nat } { ntype : nat } : Subst1 ((fin) (mtype) -> type (ntype)) (type (mtype)) (type (ntype)) := @subst_type (mtype) (ntype) .

Global Instance Ren_type { mtype : nat } { ntype : nat } : Ren1 ((fin) (mtype) -> (fin) (ntype)) (type (mtype)) (type (ntype)) := @ren_type (mtype) (ntype) .

Global Instance VarInstance_type { mtype : nat } : Var ((fin) (mtype)) (type (mtype)) := @var_type (mtype) .

Notation "x '__type'" := (var_type x) (at level 5, format "x __type") : subst_scope.

Notation "x '__type'" := (@ids (_) (_) VarInstance_type x) (at level 5, only printing, format "x __type") : subst_scope.

Notation "'var'" := (var_type) (only printing, at level 1) : subst_scope.

Class Up_type X Y := up_type : X -> Y.

Notation "↑__type" := (up_type) (only printing) : subst_scope.

Notation "↑__type" := (up_type_type) (only printing) : subst_scope.

Global Instance Up_type_type { m : nat } { ntype : nat } : Up_type (_) (_) := @up_type_type (m) (ntype) .

Notation "s [ sigmatype ]" := (subst_type sigmatype s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmatype ]" := (subst_type sigmatype) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xitype ⟩" := (ren_type xitype s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xitype ⟩" := (ren_type xitype) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Ren_type,  VarInstance_type.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_type,  Ren_type,  VarInstance_type in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_type| progress rewrite ?compComp_type| progress rewrite ?compComp'_type| progress rewrite ?rinstId_type| progress rewrite ?compRen_type| progress rewrite ?compRen'_type| progress rewrite ?renComp_type| progress rewrite ?renComp'_type| progress rewrite ?renRen_type| progress rewrite ?renRen'_type| progress rewrite ?varL_type| progress rewrite ?varLRen_type| progress (unfold up_ren, upRen_type_type, up_type_type)| progress (cbn [subst_type ren_type])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_type in *| progress rewrite ?compComp_type in *| progress rewrite ?compComp'_type in *| progress rewrite ?rinstId_type in *| progress rewrite ?compRen_type in *| progress rewrite ?compRen'_type in *| progress rewrite ?renComp_type in *| progress rewrite ?renComp'_type in *| progress rewrite ?renRen_type in *| progress rewrite ?renRen'_type in *| progress rewrite ?varL_type in *| progress rewrite ?varLRen_type in *| progress (unfold up_ren, upRen_type_type, up_type_type in *)| progress (cbn [subst_type ren_type] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_type).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_type).
