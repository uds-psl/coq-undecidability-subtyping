(** * Syntax for the rowing machines *)
Require Export fintype.
Require Import Vectors.Vector Lia.
Require Import Utils.Various_utils.
Import VectorNotations.


Section row.

Context {w : nat}.

Inductive row (nrow : nat) : Type :=
  | var_row : fin w -> (fin) (nrow) -> row (nrow)
  | abst : Vector.t (row  ((S) nrow)) w -> row (nrow)
  | halt : row (nrow).

(** ** Custom induction for rows *)
Fixpoint size {n} (r : row n) : nat:=
   match r with
   | abst _ t => S (vsum (map size t))
   | _ => 1
   end.

Fact lt_S {l k} : l < S k -> (l = k) + (l < k).
Proof. intros Hk. destruct (Compare_dec.lt_eq_lt_dec l k) as [[H|H]|H]; auto. lia.
Qed.

Lemma row_size_ind (P : forall nrow, row nrow -> Prop) :
  (forall nrow x, (forall mrow y, size y < size x -> P mrow y) -> P nrow x) ->
  forall nrow x, P nrow x.
Proof. intro H. intros. apply H. induction (size x); intros. lia. destruct (lt_S H0).
  -apply H. rewrite e. apply IHn.
  -apply IHn,l.
Qed.


Fact inSize {n} {t : Vector.t (row (S n)) w} {a} : In a t -> size a < size (abst _ t).
Proof. intro. cbn. assert (In (size a) (map size t)).
  { induction H. now apply In_cons_hd. now apply In_cons_tl. }
  pose (in_smaller _ _ H0). lia.
Qed.

Lemma row_vect_ind (P : forall nrow, row nrow -> Prop):
  (forall nrow (f : fin w) (f0 : fin nrow), P nrow (var_row nrow f f0)) ->
  (forall nrow (t : t (row (S nrow)) w), Forall (P (S nrow)) t -> P nrow (abst nrow t)) ->
  (forall nrow, P nrow (halt nrow)) ->
  forall nrow (r : row nrow), P nrow r.
Proof. intros Hv Ha Hh. eapply row_size_ind. destruct x; intros. 1,3: auto.
  apply Ha. apply Forall_forall. intros. apply H. now apply inSize.
Qed.

(** ** Modified Autosubst output 
Renamings and substitutions have an extra argument to access the vectors, this argument remains unchanged when the renaming or substitution is modified 
*)
Lemma congr_abst { mrow : nat } { s0 : Vector.t (row  ((S) mrow)) w } { t0 : Vector.t (row  ((S) mrow)) w } (H1 : s0 = t0) : abst (mrow) s0 = abst (mrow) t0 .
Proof. congruence. Qed.

Lemma congr_halt { mrow : nat } : halt (mrow) = halt (mrow) .
Proof. congruence. Qed.

Definition upRen_row_row { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) (s : row (mrow)) : row (nrow) :=
    match s return row (nrow) with
    | var_row (_) i s => (var_row (nrow) i) (xirow s)
    | abst (_) s0 => abst (nrow) (map (ren_row (upRen_row_row xirow)) s0)
    | halt (_)  => halt (nrow)
    end.

Definition up_row_row { m : nat } { nrow : nat } (sigma : fin w -> (fin) (m) -> row (nrow)) : fin w -> (fin) ((S) (m)) -> row ((S) nrow) :=
  fun i => (scons) ((var_row ((S) nrow) i) (var_zero)) ((funcomp) (ren_row (shift)) (sigma i)).

Fixpoint subst_row { mrow : nat } { nrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (nrow)) (s : row (mrow)) : row (nrow) :=
    match s return row (nrow) with
    | var_row (_) i s => sigmarow i s
    | abst (_) s0 => abst (nrow) (map (subst_row (up_row_row sigmarow)) s0)
    | halt (_)  => halt (nrow)
    end.

Definition upId_row_row { mrow : nat } (sigma : fin w -> (fin) (mrow) -> row (mrow)) (Eq : forall i x, sigma i x = (var_row (mrow) i) x) : forall i x, (up_row_row sigma) i x = (var_row ((S) mrow) i) x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_row (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint idSubst_row { mrow : nat } (sigmarow : (fin) (mrow) -> row (mrow)) (Eqrow : forall x, sigmarow x = (var_row (mrow)) x) (s : row (mrow)) : subst_row sigmarow s = s :=
    match s return subst_row sigmarow s = s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((idSubst_row (up_row_row sigmarow) (upId_row_row (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma idSubst_row' { mrow : nat } (s : row (mrow)):
  forall (sigmarow : fin w -> (fin) (mrow) -> row (mrow)) (Eqrow : forall i x, sigmarow i x = (var_row (mrow) i) x), subst_row sigmarow s = s.
Proof. apply (row_vect_ind (fun n (s : row n) => forall (sig : fin w -> fin n -> row n) (Eq : forall (i : fin w) (x : fin n), sig i x = var_row n i x), subst_row sig s = s)); intros.
  -apply Eq.
  -apply congr_abst. rewrite (map_ext_in _ _ _ id). apply map_id. unfold id. apply Forall_forall.
    apply (Forall_impl _ (fun s : row (S nrow) => forall sig : fin w -> fin (S nrow) -> row (S nrow), (forall (i : fin w) (x : fin (S nrow)), sig i x = var_row (S nrow) i x) -> subst_row sig s = s)); auto.
    intros. apply H0. apply (upId_row_row _ Eq).
  -apply congr_halt.
Defined.
Definition idSubst_row { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (mrow)) (Eqrow : forall i x, sigmarow i x = (var_row (mrow)i ) x) (s : row (mrow)) : subst_row sigmarow s = s.
Proof. now apply idSubst_row'. Defined.

Definition upExtRen_row_row { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_row_row xi) x = (upRen_row_row zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

(* Fixpoint extRen_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) (zetarow : (fin) (mrow) -> (fin) (nrow)) (Eqrow : forall x, xirow x = zetarow x) (s : row (mrow)) : ren_row xirow s = ren_row zetarow s :=
    match s return ren_row xirow s = ren_row zetarow s with
    | var_row (_) s => (ap) (var_row (nrow)) (Eqrow s)
    | abst (_) s0 => congr_abst ((extRen_row (upRen_row_row xirow) (upRen_row_row zetarow) (upExtRen_row_row (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma extRen_row' { mrow : nat } (s : row (mrow)) :
  forall (nrow : nat) (xirow : (fin) (mrow) -> (fin) (nrow)) (zetarow : (fin) (mrow) -> (fin) (nrow)) (Eqrow : forall x, xirow x = zetarow x), ren_row xirow s = ren_row zetarow s.
Proof. eapply (row_vect_ind (fun m r => forall n xi zeta (Eq : forall x, xi x = zeta x), ren_row xi r = ren_row zeta r)); intros.
  - apply (ap (var_row _ f) (Eq f0)).
  - apply congr_abst. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun r  => forall (n : nat) (xi zeta : fin (S nrow) -> fin n), (forall x : fin (S nrow), xi x = zeta x) -> ren_row xi r = ren_row zeta r) ); auto.
    intros. apply H0. apply upExtRen_row_row,Eq.
  - apply congr_halt.
Defined.
Definition extRen_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) (zetarow : (fin) (mrow) -> (fin) (nrow)) (Eqrow : forall x, xirow x = zetarow x) (s : row (mrow)) : ren_row xirow s = ren_row zetarow s.
Proof. now apply extRen_row'. Defined.

Definition upExt_row_row { m : nat } { nrow : nat } (sigma : fin w -> (fin) (m) -> row (nrow)) (tau : fin w -> (fin) (m) -> row (nrow)) (Eq : forall i x, sigma i x = tau i x) : forall i x, (up_row_row sigma) i x = (up_row_row tau) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_row (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint ext_row { mrow : nat } { nrow : nat } (sigmarow : (fin) (mrow) -> row (nrow)) (taurow : (fin) (mrow) -> row (nrow)) (Eqrow : forall x, sigmarow x = taurow x) (s : row (mrow)) : subst_row sigmarow s = subst_row taurow s :=
    match s return subst_row sigmarow s = subst_row taurow s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((ext_row (up_row_row sigmarow) (up_row_row taurow) (upExt_row_row (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma ext_row' { mrow : nat } (s : row (mrow)):
  forall (nrow :  nat) (sigmarow : fin w -> (fin) (mrow) -> row (nrow)) (taurow : fin w -> (fin) (mrow) -> row (nrow)) (Eqrow : forall i x, sigmarow i x = taurow i x), subst_row sigmarow s = subst_row taurow s.
Proof. apply (row_vect_ind (fun m r => forall (nrow : nat) (sigmarow taurow : fin w -> fin m -> row nrow) (Eq: forall (i : fin w) (x : fin m), sigmarow i x = taurow i x), subst_row sigmarow r = subst_row taurow r)); intros.
  - apply Eq.
  - apply congr_abst. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun r : row (S nrow) => forall (nrow0 : nat) (sigmarow taurow : fin w -> fin (S nrow) -> row nrow0), (forall (i : fin w) (x : fin (S nrow)), sigmarow i x = taurow i x) -> subst_row sigmarow r = subst_row taurow r)); auto.
    intros. apply H0. apply upExt_row_row,Eq.
  - apply congr_halt.
Defined.
Definition ext_row { mrow : nat } { nrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (nrow)) (taurow : fin w -> (fin) (mrow) -> row (nrow)) (Eqrow : forall i x, sigmarow i x = taurow i x) (s : row (mrow)) : subst_row sigmarow s = subst_row taurow s.
Proof. now apply ext_row'. Defined.


Definition up_ren_ren_row_row { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_row_row tau) (upRen_row_row xi)) x = (upRen_row_row theta) x :=
  up_ren_ren xi tau theta Eq.

(* Fixpoint compRenRen_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (rhorow : (fin) (mrow) -> (fin) (lrow)) (Eqrow : forall x, ((funcomp) zetarow xirow) x = rhorow x) (s : row (mrow)) : ren_row zetarow (ren_row xirow s) = ren_row rhorow s :=
    match s return ren_row zetarow (ren_row xirow s) = ren_row rhorow s with
    | var_row (_) s => (ap) (var_row (lrow)) (Eqrow s)
    | abst (_) s0 => congr_abst ((compRenRen_row (upRen_row_row xirow) (upRen_row_row zetarow) (upRen_row_row rhorow) (up_ren_ren (_) (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma compRenRen_row' m (s : row m):
  forall { krow : nat } { lrow : nat } (xirow : (fin) (m) -> (fin) (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (rhorow : (fin) (m) -> (fin) (lrow)) (Eqrow : forall x, ((funcomp) zetarow xirow) x = rhorow x), ren_row zetarow (ren_row xirow s) = ren_row rhorow s.
Proof. apply (row_vect_ind (fun m s => forall (krow lrow : nat) (xirow : fin m -> fin krow) (zetarow : fin krow -> fin lrow) (rhorow : fin m -> fin lrow) (Eq : forall x : fin m, (xirow >> zetarow) x = rhorow x), ren_row zetarow (ren_row xirow s) = ren_row rhorow s)); intros.
  - apply (ap (var_row lrow f) (Eq f0)).
  - apply congr_abst. rewrite map_map. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun s : row (S nrow) => forall (krow lrow : nat) (xirow : fin (S nrow) -> fin krow) (zetarow : fin krow -> fin lrow) (rhorow : fin (S nrow) -> fin lrow), (forall x : fin (S nrow), (xirow >> zetarow) x = rhorow x) -> ren_row zetarow (ren_row xirow s) = ren_row rhorow s)); auto.
    intros. apply H0. apply up_ren_ren,Eq.
  - apply congr_halt.
Defined.
Definition compRenRen_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (rhorow : (fin) (mrow) -> (fin) (lrow)) (Eqrow : forall x, ((funcomp) zetarow xirow) x = rhorow x) (s : row (mrow)) : ren_row zetarow (ren_row xirow s) = ren_row rhorow s.
Proof. now apply compRenRen_row'. Defined.

Definition up_ren_subst_row_row { k : nat } { l : nat } { mrow : nat } (xi : (fin) (k) -> (fin) (l)) (tau : fin w -> (fin) (l) -> row (mrow)) (theta : fin w -> (fin) (k) -> row (mrow)) (Eq : forall i x, ((funcomp) (tau i) xi) x = theta i x) : forall i x, ((funcomp) (up_row_row tau i) (upRen_row_row xi)) x = (up_row_row theta) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_row (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint compRenSubst_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (taurow : (fin) (krow) -> row (lrow)) (thetarow : (fin) (mrow) -> row (lrow)) (Eqrow : forall x, ((funcomp) taurow xirow) x = thetarow x) (s : row (mrow)) : subst_row taurow (ren_row xirow s) = subst_row thetarow s :=
    match s return subst_row taurow (ren_row xirow s) = subst_row thetarow s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((compRenSubst_row (upRen_row_row xirow) (up_row_row taurow) (up_row_row thetarow) (up_ren_subst_row_row (_) (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma compRenSubst_row' m (s : row m):
  forall { krow : nat } { lrow : nat } (xirow : (fin) m -> (fin) (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (thetarow : fin w -> (fin) m -> row (lrow)) (Eqrow : forall i x, ((funcomp) (taurow i) xirow) x = thetarow i x), subst_row taurow (ren_row xirow s) = subst_row thetarow s.
Proof. apply (row_vect_ind (fun m s => forall (krow lrow : nat) (xirow : fin m -> fin krow) (taurow : fin w -> fin krow -> row lrow) (thetarow : fin w -> fin m -> row lrow) (Eq : forall (i : fin w) (x : fin m), (xirow >> taurow i) x = thetarow i x), subst_row taurow (ren_row xirow s) = subst_row thetarow s)); intros.
  - apply Eq.
  - apply congr_abst. rewrite map_map. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun s : row (S nrow) => forall (krow lrow : nat) (xirow : fin (S nrow) -> fin krow) (taurow : fin w -> fin krow -> row lrow) (thetarow : fin w -> fin (S nrow) -> row lrow), (forall (i : fin w) (x : fin (S nrow)), (xirow >> taurow i) x = thetarow i x) -> subst_row taurow (ren_row xirow s) = subst_row thetarow s)); auto.
    intros. apply H0. apply up_ren_subst_row_row,Eq.
  - apply congr_halt.
Defined.
Definition compRenSubst_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (thetarow : fin w -> (fin) (mrow) -> row (lrow)) (Eqrow : forall i x, ((funcomp) (taurow i) xirow) x = thetarow i x) (s : row (mrow)) : subst_row taurow (ren_row xirow s) = subst_row thetarow s.
Proof. now apply compRenSubst_row'. Defined.

Definition up_subst_ren_row_row { k : nat } { lrow : nat } { mrow : nat } (sigma : fin w -> (fin) (k) -> row (lrow)) (zetarow : (fin) (lrow) -> (fin) (mrow)) (theta : fin w -> (fin) (k) -> row (mrow)) (Eq : forall i x, ((funcomp) (ren_row zetarow) (sigma i)) x = theta i x) : forall i x, ((funcomp) (ren_row (upRen_row_row zetarow)) (up_row_row sigma i)) x = (up_row_row theta) i x :=
  fun i n => match n with
  | Some fin_n => (eq_trans) (compRenRen_row (shift) (upRen_row_row zetarow) ((funcomp) (shift) zetarow) (fun x => eq_refl) (sigma i fin_n)) ((eq_trans) ((eq_sym) (compRenRen_row zetarow (shift) ((funcomp) (shift) zetarow) (fun x => eq_refl) (sigma i fin_n))) ((ap) (ren_row (shift)) (Eq i fin_n)))
  | None  => eq_refl
  end.

(* Fixpoint compSubstRen_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : (fin) (mrow) -> row (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (thetarow : (fin) (mrow) -> row (lrow)) (Eqrow : forall x, ((funcomp) (ren_row zetarow) sigmarow) x = thetarow x) (s : row (mrow)) : ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s :=
    match s return ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((compSubstRen_row (up_row_row sigmarow) (upRen_row_row zetarow) (up_row_row thetarow) (up_subst_ren_row_row (_) (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma compSubstRen_row' m (s : row m):
  forall { krow : nat } { lrow : nat } (sigmarow : fin w -> (fin) m -> row (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (thetarow : fin w -> (fin) m -> row (lrow)) (Eqrow : forall i x, ((funcomp) (ren_row zetarow) (sigmarow i)) x = thetarow i x), ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s.
Proof. apply (row_vect_ind (fun m s => forall (krow lrow : nat) (sigmarow : fin w -> fin m -> row krow) (zetarow : fin krow -> fin lrow) (thetarow : fin w -> fin m -> row lrow) (Eq: forall (i : fin w) (x : fin m), (sigmarow i >> ren_row zetarow) x = thetarow i x), ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s)); intros.
  - apply Eq.
  - apply congr_abst. rewrite map_map. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun s : row (S nrow) => forall (krow lrow : nat) (sigmarow : fin w -> fin (S nrow) -> row krow) (zetarow : fin krow -> fin lrow) (thetarow : fin w -> fin (S nrow) -> row lrow), (forall (i : fin w) (x : fin (S nrow)), (sigmarow i >> ren_row zetarow) x = thetarow i x) -> ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s)); auto.
   intros. apply H0. apply up_subst_ren_row_row,Eq.
  - apply congr_halt.
Defined.
Definition compSubstRen_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (thetarow : fin w -> (fin) (mrow) -> row (lrow)) (Eqrow : forall i x, ((funcomp) (ren_row zetarow) (sigmarow i)) x = thetarow i x) (s : row (mrow)) : ren_row zetarow (subst_row sigmarow s) = subst_row thetarow s.
Proof. now apply compSubstRen_row'. Defined.


(* Definition up_subst_subst_row_row { k : nat } { lrow : nat } { mrow : nat } (sigma : fin w -> (fin) (k) -> row (lrow)) (taurow : fin w -> (fin) (lrow) -> row (mrow)) (theta : fin w -> (fin) (k) -> row (mrow)) (Eq : forall i x, ((funcomp) (subst_row (taurow)) (sigma i)) x = theta i x) : forall i x, ((funcomp) (subst_row (up_row_row taurow)) (up_row_row sigma i)) x = (up_row_row theta) i x :=
  fun i n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_row (shift) (up_row_row taurow) ((funcomp) (up_row_row taurow) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_row taurow (shift) ((funcomp) (ren_row (shift)) taurow) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_row (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.
 *)
Definition up_subst_subst_row_row { k : nat } { lrow : nat } { mrow : nat } (sigma : fin w -> (fin) (k) -> row (lrow)) (taurow : fin w -> (fin) (lrow) -> row (mrow)) (theta : fin w -> (fin) (k) -> row (mrow)) (Eq : forall i x, ((funcomp) (subst_row (taurow)) (sigma i)) x = theta i x) : forall i x, ((funcomp) (subst_row (up_row_row taurow)) (up_row_row sigma i)) x = (up_row_row theta) i x.
Proof. intros i [j |]. 2: apply eq_refl. apply (eq_trans (compRenSubst_row ↑ (up_row_row taurow) (fun i => ↑ >> up_row_row taurow i) (fun _ _ => eq_refl) (sigma i j) )).
  apply (eq_trans (eq_sym (compSubstRen_row taurow ↑ (fun i => taurow i >> ren_row ↑) (fun _ _ => eq_refl) (sigma i j)))).
  apply (ap (ren_row ↑)), Eq.
Defined.

(* Fixpoint compSubstSubst_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : (fin) (mrow) -> row (krow)) (taurow : (fin) (krow) -> row (lrow)) (thetarow : (fin) (mrow) -> row (lrow)) (Eqrow : forall x, ((funcomp) (subst_row taurow) sigmarow) x = thetarow x) (s : row (mrow)) : subst_row taurow (subst_row sigmarow s) = subst_row thetarow s :=
    match s return subst_row taurow (subst_row sigmarow s) = subst_row thetarow s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((compSubstSubst_row (up_row_row sigmarow) (up_row_row taurow) (up_row_row thetarow) (up_subst_subst_row_row (_) (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma compSubstSubst_row' m (s : row m) :
  forall { krow : nat } { lrow : nat } (sigmarow : fin w -> (fin) m -> row (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (thetarow : fin w -> (fin) (m) -> row (lrow)) (Eqrow : forall i x, ((funcomp) (subst_row taurow) (sigmarow i)) x = thetarow i x), subst_row taurow (subst_row sigmarow s) = subst_row thetarow s.
Proof. apply (row_vect_ind (fun m s => forall (krow lrow : nat) (sigmarow : fin w -> fin m -> row krow) (taurow : fin w -> fin krow -> row lrow) (thetarow : fin w -> fin m -> row lrow) (Eq : forall (i : fin w) (x : fin m), (sigmarow i >> subst_row taurow) x = thetarow i x), subst_row taurow (subst_row sigmarow s) = subst_row thetarow s)); intros.
  -apply Eq.
  -apply congr_abst. rewrite map_map. apply map_ext_in. apply Forall_forall.
    apply (Forall_impl _ (fun s : row (S nrow) => forall (krow lrow : nat) (sigmarow : fin w -> fin (S nrow) -> row krow) (taurow : fin w -> fin krow -> row lrow) (thetarow : fin w -> fin (S nrow) -> row lrow), (forall (i : fin w) (x : fin (S nrow)), (sigmarow i >> subst_row taurow) x = thetarow i x) -> subst_row taurow (subst_row sigmarow s) = subst_row thetarow s)); auto.
    intros. apply H0. apply up_subst_subst_row_row,Eq.
  -apply congr_halt.
Defined.
Definition compSubstSubst_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (thetarow : fin w -> (fin) (mrow) -> row (lrow)) (Eqrow : forall i x, ((funcomp) (subst_row taurow) (sigmarow i)) x = thetarow i x) (s : row (mrow)) : subst_row taurow (subst_row sigmarow s) = subst_row thetarow s.
Proof. now apply compSubstSubst_row'. Defined.

Definition rinstInst_up_row_row { m : nat } { nrow : nat } (xi : (fin) (m) -> (fin) (nrow)) (sigma : fin w -> (fin) (m) -> row (nrow)) (Eq : forall i x, ((funcomp) (var_row (nrow) i) xi) x = sigma i x) : forall i x, ((funcomp) (var_row ((S) nrow) i) (upRen_row_row xi)) x = (up_row_row sigma) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_row (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint rinst_inst_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) (sigmarow : (fin) (mrow) -> row (nrow)) (Eqrow : forall x, ((funcomp) (var_row (nrow)) xirow) x = sigmarow x) (s : row (mrow)) : ren_row xirow s = subst_row sigmarow s :=
    match s return ren_row xirow s = subst_row sigmarow s with
    | var_row (_) s => Eqrow s
    | abst (_) s0 => congr_abst ((rinst_inst_row (upRen_row_row xirow) (up_row_row sigmarow) (rinstInst_up_row_row (_) (_) Eqrow)) s0)
    | halt (_)  => congr_halt 
    end. *)
Lemma rinst_inst_row' m (s : row m) :
  forall { nrow : nat } (xirow : (fin) (m) -> (fin) (nrow)) (sigmarow : fin w -> (fin) (m) -> row (nrow)) (Eqrow : forall i x, ((funcomp) (var_row (nrow) i) xirow) x = sigmarow i x), ren_row xirow s = subst_row sigmarow s.
Proof. apply (row_vect_ind (fun m s => forall (nrow : nat) (xirow : fin m -> fin nrow) (sigmarow : fin w -> fin m -> row nrow) (Eq : forall (i : fin w) (x : fin m), (xirow >> var_row nrow i) x = sigmarow i x), ren_row xirow s = subst_row sigmarow s)); intros.
  -apply Eq.
  -apply congr_abst. apply map_ext_in. apply Forall_forall.
   apply (Forall_impl _ (fun s : row (S nrow) => forall (nrow0 : nat) (xirow : fin (S nrow) -> fin nrow0) (sigmarow : fin w -> fin (S nrow) -> row nrow0), (forall (i : fin w) (x : fin (S nrow)), (xirow >> var_row nrow0 i) x = sigmarow i x) -> ren_row xirow s = subst_row sigmarow s)); auto.
    intros. apply H0. apply rinstInst_up_row_row,Eq.
  -apply congr_halt.
Defined.
Definition rinst_inst_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) (sigmarow : fin w -> (fin) (mrow) -> row (nrow)) (Eqrow : forall i x, ((funcomp) (var_row (nrow) i) xirow) x = sigmarow i x) (s : row (mrow)) : ren_row xirow s = subst_row sigmarow s.
Proof. now apply rinst_inst_row'. Defined.


Lemma rinstInst_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) : ren_row xirow = subst_row (fun i => (funcomp) (var_row (nrow) i) xirow) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_row xirow (_) (fun _ n => eq_refl) x)). Qed.

Lemma instId_row { mrow : nat } : subst_row (var_row (mrow)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_row (var_row (mrow)) (fun _ n => eq_refl) ((id) x))). Qed.

Lemma rinstId_row { mrow : nat } : @ren_row (mrow) (mrow) (id) = id .
Proof. exact ((eq_trans) (rinstInst_row ((id) (_))) instId_row). Qed.

Lemma varL_row { mrow : nat } { nrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (nrow)) : (fun i => (funcomp) (subst_row sigmarow) (var_row (mrow) i)) = sigmarow .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_row { mrow : nat } { nrow : nat } (xirow : (fin) (mrow) -> (fin) (nrow)) : (fun i => (funcomp) (ren_row xirow) (var_row (mrow) i)) = (fun i => (funcomp) (var_row (nrow) i) xirow) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (s : row (mrow)) : subst_row taurow (subst_row sigmarow s) = subst_row (fun i => (funcomp) (subst_row taurow) (sigmarow i)) s .
Proof. exact (compSubstSubst_row sigmarow taurow (_) (fun _ n => eq_refl) s). Qed.

Lemma compComp'_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) : (funcomp) (subst_row taurow) (subst_row sigmarow) = subst_row (fun i => (funcomp) (subst_row taurow) (sigmarow i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_row sigmarow taurow n)). Qed.

Lemma compRen_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (s : row (mrow)) : ren_row zetarow (subst_row sigmarow s) = subst_row (fun i => (funcomp) (ren_row zetarow) (sigmarow i)) s .
Proof. exact (compSubstRen_row sigmarow zetarow (_) (fun _ n => eq_refl) s). Qed.

Lemma compRen'_row { krow : nat } { lrow : nat } { mrow : nat } (sigmarow : fin w -> (fin) (mrow) -> row (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) : (funcomp) (ren_row zetarow) (subst_row sigmarow) = subst_row (fun i => (funcomp) (ren_row zetarow) (sigmarow i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_row sigmarow zetarow n)). Qed.

Lemma renComp_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) (s : row (mrow)) : subst_row taurow (ren_row xirow s) = subst_row (fun i => (funcomp) (taurow i) xirow) s .
Proof. exact (compRenSubst_row xirow taurow (_) (fun _ n => eq_refl) s). Qed.

Lemma renComp'_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (taurow : fin w -> (fin) (krow) -> row (lrow)) : (funcomp) (subst_row taurow) (ren_row xirow) = subst_row (fun i => (funcomp) (taurow i) xirow) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_row xirow taurow n)). Qed.

Lemma renRen_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) (s : row (mrow)) : ren_row zetarow (ren_row xirow s) = ren_row ((funcomp) zetarow xirow) s .
Proof. exact (compRenRen_row xirow zetarow (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_row { krow : nat } { lrow : nat } { mrow : nat } (xirow : (fin) (mrow) -> (fin) (krow)) (zetarow : (fin) (krow) -> (fin) (lrow)) : (funcomp) (ren_row zetarow) (ren_row xirow) = ren_row ((funcomp) zetarow xirow) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_row xirow zetarow n)). Qed.

End row.

Arguments var_row {w} {nrow}.

Arguments abst {w} {nrow}.

Arguments halt {w} {nrow}.

(* Global Instance Subst_row { mrow : nat } { nrow : nat } : Subst1 ((fin) (mrow) -> row (nrow)) (row (mrow)) (row (nrow)) := @subst_row (mrow) (nrow) . *)

(* Global Instance Ren_row { mrow : nat } { nrow : nat } : Ren1 ((fin) (mrow) -> (fin) (nrow)) (row (mrow)) (row (nrow)) := @ren_row (mrow) (nrow) . *)

(* Global Instance VarInstance_row { mrow : nat } : Var ((fin) (mrow)) (row (mrow)) := @var_row (mrow) . *)

(* Notation "x '__row'" := (var_row x) (at level 5, format "x __row") : subst_scope. *)

(* Notation "x '__row'" := (@ids (_) (_) VarInstance_row x) (at level 5, only printing, format "x __row") : subst_scope. *)

(* Notation "'var'" := (var_row) (only printing, at level 1) : subst_scope. *)

Class Up_row X Y := up_row : X -> Y.

(* Notation "↑__row" := (up_row) (only printing) : subst_scope. *)

(* Notation "↑__row" := (up_row_row) (only printing) : subst_scope. *)

(* Global Instance Up_row_row { m : nat } { nrow : nat } : Up_row (_) (_) := @up_row_row (m) (nrow) . *)

(* Notation "s [ sigmarow ]" := (subst_row sigmarow s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmarow ]" := (subst_row sigmarow) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xirow ⟩" := (ren_row xirow s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xirow ⟩" := (ren_row xirow) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2(* ,  Subst_row,  Ren_row,  VarInstance_row *).

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2(* ,  Subst_row,  Ren_row,  VarInstance_row *) in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_row| progress rewrite ?compComp_row| progress rewrite ?compComp'_row| progress rewrite ?rinstId_row| progress rewrite ?compRen_row| progress rewrite ?compRen'_row| progress rewrite ?renComp_row| progress rewrite ?renComp'_row| progress rewrite ?renRen_row| progress rewrite ?renRen'_row| progress rewrite ?varL_row| progress rewrite ?varLRen_row| progress (unfold up_ren, upRen_row_row, up_row_row)| progress (cbn [subst_row ren_row])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_row in *| progress rewrite ?compComp_row in *| progress rewrite ?compComp'_row in *| progress rewrite ?rinstId_row in *| progress rewrite ?compRen_row in *| progress rewrite ?compRen'_row in *| progress rewrite ?renComp_row in *| progress rewrite ?renComp'_row in *| progress rewrite ?renRen_row in *| progress rewrite ?renRen'_row in *| progress rewrite ?varL_row in *| progress rewrite ?varLRen_row in *| progress (unfold up_ren, upRen_row_row, up_row_row in *)| progress (cbn [subst_row ren_row] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_row).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_row).
