(** * Polarized syntax with polyadic binders *)

Require Export fintype.

Require Import Vectors.Vector Lia.
Require Import Utils.Various_utils.
Import VectorNotations.

Section ptypentype.
Context {w : nat} .

(** ** Syntax for types and contexts  *)
Inductive ptype (nntype : nat) : Type :=
  | top : ptype (nntype)
  | bAllN : (Vector.t (ntype  (nntype)) w) -> ntype  ((S) nntype) -> ptype (nntype)
 with ntype (nntype : nat) : Type :=
  | var_ntype : fin w -> (fin) (nntype) -> ntype (nntype)
  | uAllN : ptype  (S nntype) -> ntype (nntype).

Inductive ctx : nat -> Type :=
  | empty : ctx 0
  | add : forall {m : nat}, Vector.t (ntype m) w -> ctx m -> ctx (S m).

Definition nonEmptyCtx {m : nat} (Γ : ctx (S m)) : forall (P : ctx (S m) -> Type) (H : forall h t, P (add h t)), P Γ
  := match Γ with
    | add h t => fun P H => H h t
    | _ => fun x => False_rect (@IDProp) x
    end.

(** ** Custom induction for types
  Size induction is requiered to define the mutual induction principle.
*)

Fixpoint psize {m} (t : @ptype m) : nat := match t with
  | top _ => 1
  | bAllN _ v s => 1 + vsum (map nsize v) + nsize s
  end
with nsize {m} (s : @ntype m) : nat := match s with
  | var_ntype _ _ _ => 1
  | uAllN _ t => 1 + psize t
  end.

Lemma ptype_ntype_size_ind (P : forall m, @ptype m -> Prop) (Q : forall m, @ntype m -> Prop) : 
  (forall m t, (forall m' s, nsize s < psize t -> Q m' s) -> P m t) ->
  (forall m t, (forall m' s, psize s < nsize t -> P m' s) -> Q m t) ->
  forall m, (forall t, P m t) /\ (forall s, Q m s).
Proof. intros Hp Hq. split; intros; [apply Hp | apply Hq].
  -assert (H : forall n m s, nsize s < n -> Q m s).
   {intro. induction n; intros. exfalso. lia. apply Hq. intros. apply Hp. intros. apply IHn. lia. }
   apply H.
  -assert (H : forall n m s, psize s < n -> P m s).
   {intro. induction n; intros. exfalso. lia. apply Hp. intros. apply Hq. intros. apply IHn. lia. }
   apply H.
Qed.

Fact in_ns {m} a t s: In a t -> @nsize m a < psize (bAllN _ t s).
Proof. intro. cbn.
  assert (In (nsize a) (map nsize t)). { induction H; simpl. apply In_cons_hd. now apply In_cons_tl. }
  pose (in_smaller _ _ H0). lia.
Qed.

Lemma ptype_ntype_mutind : forall (P : forall m : nat, @ptype m -> Prop)
  (Q : forall m : nat, @ntype m -> Prop),
  (forall m : nat, P m (@top m)) ->
  (forall (m : nat) (t : Vector.t (@ntype m) w) (n : @ntype (S m)),
    Q (S m) n -> @Forall (@ntype m) (Q m) _ t ->  P m (@bAllN m t n)) ->
  (forall (m : nat) (t0 : fin m) (t : fin w), Q m (@var_ntype m t t0)) ->
  (forall (m : nat) (p : @ptype (S m)), P (S m) p -> Q m (@uAllN m p)) ->
  forall m : nat, (forall p : @ptype m, P m p) /\ (forall n : @ntype m, Q m n).
Proof. intros P Q Htop HbAllN Hvar HuAllN. eapply ptype_ntype_size_ind.
  -intros. destruct t. apply Htop. apply HbAllN. apply H. cbn. lia.
   apply Forall_forall. intros. apply H. now apply in_ns.
  -intros. destruct t. apply Hvar. apply HuAllN, H. cbn. lia.
Qed.

(** ** Modified Autosubst output 
Renamings and substitutions have an extra argument to access the vectors, this argument remains unchanged when the renaming or substitution is modified 
*)

Lemma congr_top { mntype : nat } : top (mntype) = top (mntype) .
Proof. congruence. Qed.

Lemma congr_bAllN { mntype : nat } { s0 : (Vector.t (ntype  (mntype)) w) } { s1 : ntype  ((S) mntype) } { t0 : (Vector.t (ntype  (mntype)) w) } { t1 : ntype  ((S) mntype) } (H1 : s0 = t0) (H2 : s1 = t1) : bAllN (mntype) s0 s1 = bAllN (mntype) t0 t1 .
Proof. congruence. Qed.

Lemma congr_uAllN { mntype : nat } { s0 : ptype  (S mntype) } { t0 : ptype  (S mntype) } (H1 : s0 = t0) : uAllN (mntype) s0 = uAllN (mntype) t0 .
Proof. congruence. Qed.

Definition upRen_ntype_ntype { m : nat } { n' : nat } (xi : (fin) (m) -> (fin) (n')) : (fin) ((S) (m)) -> (fin) ((S) (n')) := (up_ren) (xi).

Fixpoint ren_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (s : ptype (mntype)) : ptype (nntype) :=
    match s return ptype (nntype) with
    | top (_)  => top (nntype)
    | bAllN (_) s0 s1 => bAllN (nntype) (Vector.map (ren_ntype xintype) s0) ((ren_ntype (upRen_ntype_ntype xintype)) s1)
    end
 with ren_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (s : ntype (mntype)) : ntype (nntype) :=
    match s return ntype (nntype) with
    | var_ntype (_) i s => (var_ntype (nntype)) i (xintype s)
    | uAllN (_) s0 => uAllN (nntype) ((ren_ptype (upRen_ntype_ntype xintype)) s0)
    end.

Definition ctx_at {m} (Γ : ctx m) (i : fin w) (j : fin m) : ntype m.
Proof. induction Γ. contradiction. apply (ren_ntype ↑). destruct j. apply IHΓ, f. exact (nth' t i).
Defined.

Definition up_ntype_ntype { m : nat } { nntype : nat } (sigma : fin w -> (fin) (m) -> ntype (nntype)) : fin w -> (fin) ((S) (m)) -> ntype ((S) nntype) :=
  fun i => (scons) ((var_ntype ((S) nntype) i) (var_zero)) ((funcomp) (ren_ntype (shift)) (sigma i)).

Fixpoint subst_ptype { mntype : nat } { nntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (s : ptype (mntype)) : ptype (nntype) :=
    (match s return ptype (nntype) with
    | top (_)  => top (nntype)
    | bAllN (_) s0 s1 => bAllN (nntype) (Vector.map (subst_ntype sigmantype) s0) ((subst_ntype (up_ntype_ntype sigmantype)) s1)
    end)
 with subst_ntype { mntype : nat } { nntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (s : ntype (mntype)) : ntype (nntype) :=
    match s return ntype (nntype) with
    | var_ntype (_) i s => sigmantype i s
    | uAllN (_) s0 => uAllN (nntype) ((subst_ptype (up_ntype_ntype sigmantype)) s0)
    end.

(* Instantiations *)
Definition ninst {m} (v : Vector.t (ntype m) w) (s : ntype (S m)) : ntype m
  := subst_ntype (fun i : fin w => nth' v i .; var_ntype m i) s.

Definition pinst {m}  (v : Vector.t (ntype m) w) (s : ptype (S m)) : ptype m
  := subst_ptype (fun i : fin w => nth' v i .; var_ntype m i) s.



Definition upId_ntype_ntype { mntype : nat } (sigma : fin w -> (fin) (mntype) -> ntype (mntype)) (Eq : forall i x, sigma i x = (var_ntype (mntype) i) x) : forall i x, (up_ntype_ntype sigma i) x = (var_ntype ((S) mntype) i) x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_ntype (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint idSubst_ptype { mntype : nat } (sigmantype : fin n -> (fin) (mntype) -> ntype (mntype)) (Eqntype : forall i x, sigmantype i x = (var_ntype (mntype) i) x) (s : ptype (mntype)) : subst_ptype sigmantype s = s :=
    match s return subst_ptype sigmantype s = s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((idSubst_ntype sigmantype Eqntype) s0) ((idSubst_ntype (up_ntype_ntype sigmantype) (upId_ntype_ntype (_) Eqntype)) s1)
    end
 with idSubst_ntype { mntype : nat } (sigmantype : fin n -> (fin) (mntype) -> ntype (mntype)) (Eqntype : forall i x, sigmantype i x = (var_ntype (mntype) i) x) (s : ntype (mntype)) : subst_ntype sigmantype s = s :=
    match s return subst_ntype sigmantype s = s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((idSubst_ptype sigmantype Eqntype) s0)
    end. *)
(** In general each lemma is proved for both positive and negative types simultaneously with the mutual induction principle *)
Lemma idSubst_ptype_ntype : forall m,
   (forall s (sigmantype : fin w -> fin m -> ntype m) (Eq : forall i x, sigmantype i x = var_ntype m i x), subst_ptype sigmantype s = s)
/\ (forall s (sigmantype : fin w -> fin m -> ntype m) (Eq : forall i x, sigmantype i x = var_ntype m i x), subst_ntype sigmantype s = s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +rewrite (map_ext_in _ _ _ id). apply map_id. unfold id. apply Forall_forall. apply (Forall_impl _ (fun n0 : ntype m => forall sigmantype : fin w -> fin m -> ntype m, (forall i x, sigmantype i x = var_ntype m i x) -> subst_ntype sigmantype n0 = n0)); auto.
    +apply H. intros. apply (upId_ntype_ntype _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (upId_ntype_ntype _ Eq).
Qed.

(**  We can now define the lemma for positive and negative types individually *)
Definition idSubst_ptype { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (mntype)) (Eqntype : forall i x, sigmantype i x = (var_ntype (mntype) i) x) (s : ptype (mntype)) : subst_ptype sigmantype s = s.
Proof. destruct (idSubst_ptype_ntype mntype). now apply H. Defined.

Definition idSubst_ntype { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (mntype)) (Eqntype : forall i x, sigmantype i x = (var_ntype (mntype) i) x) (s : ntype (mntype)) : subst_ntype sigmantype s = s.
Proof. destruct (idSubst_ptype_ntype mntype). now apply H0. Defined.


Definition upExtRen_ntype_ntype { m : nat } { n' : nat } (xi : (fin) (m) -> (fin) (n')) (zeta : (fin) (m) -> (fin) (n')) (Eq : forall x, xi x = zeta x) : forall x, (upRen_ntype_ntype xi) x = (upRen_ntype_ntype zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

(* Fixpoint extRen_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (zetantype : (fin) (mntype) -> (fin) (nntype)) (Eqntype : forall x, xintype x = zetantype x) (s : ptype (mntype)) : ren_ptype xintype s = ren_ptype zetantype s :=
    match s return ren_ptype xintype s = ren_ptype zetantype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((extRen_ntype xintype zetantype Eqntzype) s0) ((extRen_ntype (upRen_ntype_ntype xintype) (upRen_ntype_ntype zetantype) (upExtRen_ntype_ntype (_) (_) Eqntype)) s1)
    end
 with extRen_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (zetantype : (fin) (mntype) -> (fin) (nntype)) (Eqntype : forall x, xintype x = zetantype x) (s : ntype (mntype)) : ren_ntype xintype s = ren_ntype zetantype s :=
    match s return ren_ntype xintype s = ren_ntype zetantype s with
    | var_ntype (_) s => (ap) (var_ntype (nntype)) (Eqntype s)
    | uAllN (_) s0 => congr_uAllN ((extRen_ptype xintype zetantype Eqntype) s0)
    end. *)
Lemma extRen_ptype_ntype : forall m,
   (forall s l (xintype : fin m -> fin l) (zetantype : fin m -> fin l) (Eqntype : forall x, xintype x = zetantype x), ren_ptype xintype s = ren_ptype zetantype s)
/\ (forall s l (xintype : fin m -> fin l) (zetantype : fin m -> fin l) (Eqntype : forall x, xintype x = zetantype x), ren_ntype xintype s = ren_ntype zetantype s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +apply map_ext_in. apply Forall_forall. apply (Forall_impl _ (fun n : ntype m => forall (l : nat) (xintype zetantype : fin m -> fin l), (forall x : fin m, xintype x = zetantype x) -> ren_ntype xintype n = ren_ntype zetantype n)); auto.
    +apply H. intros. apply (upExtRen_ntype_ntype _ _ Eqntype).
  -apply (ap (var_ntype l t)). apply Eqntype.
  -apply congr_uAllN. apply H. intros. apply (upExtRen_ntype_ntype _ _ Eqntype).
Qed.
Definition extRen_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (zetantype : (fin) (mntype) -> (fin) (nntype)) (Eqntype : forall x, xintype x = zetantype x) (s : ptype (mntype)) : ren_ptype xintype s = ren_ptype zetantype s.
Proof. destruct (extRen_ptype_ntype mntype). now apply H. Defined.
Definition extRen_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (zetantype : (fin) (mntype) -> (fin) (nntype)) (Eqntype : forall x, xintype x = zetantype x) (s : ntype (mntype)) : ren_ntype xintype s = ren_ntype zetantype s.
Proof. destruct (extRen_ptype_ntype mntype). now apply H0. Defined.


Definition upExt_ntype_ntype { m : nat } { nntype : nat } (sigma : fin w -> (fin) (m) -> ntype (nntype)) (tau : fin w -> (fin) (m) -> ntype (nntype)) (Eq : forall i x, sigma i x = tau i x) : forall i x, (up_ntype_ntype sigma) i x = (up_ntype_ntype tau) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_ntype (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint ext_ptype { mntype : nat } { nntype : nat } (sigmantype : (fin) (mntype) -> ntype (nntype)) (tauntype : (fin) (mntype) -> ntype (nntype)) (Eqntype : forall x, sigmantype x = tauntype x) (s : ptype (mntype)) : subst_ptype sigmantype s = subst_ptype tauntype s :=
    match s return subst_ptype sigmantype s = subst_ptype tauntype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((ext_ntype sigmantype tauntype Eqntype) s0) ((ext_ntype (up_ntype_ntype sigmantype) (up_ntype_ntype tauntype) (upExt_ntype_ntype (_) (_) Eqntype)) s1)
    end
 with ext_ntype { mntype : nat } { nntype : nat } (sigmantype : (fin) (mntype) -> ntype (nntype)) (tauntype : (fin) (mntype) -> ntype (nntype)) (Eqntype : forall x, sigmantype x = tauntype x) (s : ntype (mntype)) : subst_ntype sigmantype s = subst_ntype tauntype s :=
    match s return subst_ntype sigmantype s = subst_ntype tauntype s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((ext_ptype sigmantype tauntype Eqntype) s0)
    end. *)
Lemma ext_ptype_ntype : forall m,
    (forall s l (sig : fin w -> fin m -> ntype l) (tau : fin w -> fin m -> ntype l) (Eq : forall i x, sig i x = tau i x),
      subst_ptype sig s = subst_ptype tau s)
/\  (forall s l (sig : fin w -> fin m -> ntype l) (tau : fin w -> fin m -> ntype l) (Eq : forall i x, sig i x = tau i x),
      subst_ntype sig s = subst_ntype tau s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +apply map_ext_in. apply Forall_forall. apply (Forall_impl _ (fun n0 : ntype m => forall (l : nat) (sig tau : fin w -> fin m -> ntype l), (forall (i : fin w) (x : fin m), sig i x = tau i x) -> subst_ntype sig n0 = subst_ntype tau n0)); auto.
    +apply H. intros. apply (upExt_ntype_ntype _ _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (upExt_ntype_ntype _ _ Eq).
Qed.
Definition ext_ptype { mntype : nat } { nntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (tauntype : fin w -> (fin) (mntype) -> ntype (nntype)) (Eqntype : forall i x, sigmantype i x = tauntype i x) (s : ptype (mntype)) : subst_ptype sigmantype s = subst_ptype tauntype s.
Proof. destruct (ext_ptype_ntype mntype). now apply H. Defined.
Definition ext_ntype { mntype : nat } { nntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (tauntype : fin w -> (fin) (mntype) -> ntype (nntype)) (Eqntype : forall i x, sigmantype i x = tauntype i x) (s : ntype (mntype)) : subst_ntype sigmantype s = subst_ntype tauntype s.
Proof. destruct (ext_ptype_ntype mntype). now apply H0. Defined.


Definition up_ren_ren_ntype_ntype { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) (tau) (xi)) x = theta x) : forall x, ((funcomp) (upRen_ntype_ntype tau) (upRen_ntype_ntype xi)) x = (upRen_ntype_ntype theta) x :=
  up_ren_ren (xi) (tau) (theta) (Eq).

(* Fixpoint compRenRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (rhontype : (fin) (mntype) -> (fin) (lntype)) (Eqntype : forall x, ((funcomp) zetantype xintype) x = rhontype x) (s : ptype (mntype)) : ren_ptype zetantype (ren_ptype xintype s) = ren_ptype rhontype s :=
    match s return ren_ptype zetantype (ren_ptype xintype s) = ren_ptype rhontype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((compRenRen_ntype xintype zetantype rhontype Eqntype) s0) ((compRenRen_ntype (upRen_ntype_ntype xintype) (upRen_ntype_ntype zetantype) (upRen_ntype_ntype rhontype) (up_ren_ren (_) (_) (_) Eqntype)) s1)
    end
 with compRenRen_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (rhontype : (fin) (mntype) -> (fin) (lntype)) (Eqntype : forall x, ((funcomp) zetantype xintype) x = rhontype x) (s : ntype (mntype)) : ren_ntype zetantype (ren_ntype xintype s) = ren_ntype rhontype s :=
    match s return ren_ntype zetantype (ren_ntype xintype s) = ren_ntype rhontype s with
    | var_ntype (_) s => (ap) (var_ntype (lntype)) (Eqntype s)
    | uAllN (_) s0 => congr_uAllN ((compRenRen_ptype xintype zetantype rhontype Eqntype) s0)
    end. *)
Lemma compRenRen_ptype_ntype : forall m,
   (forall s k l (xi : fin m -> fin k) (zet : fin k -> fin l) (rho : fin m -> fin l)
      (Eq : forall x, funcomp (zet) (xi) x = rho x),
      ren_ptype zet (ren_ptype xi s) = ren_ptype rho s)
/\ (forall s k l (xi : fin m -> fin k) (zet : fin k -> fin l) (rho : fin m -> fin l)
      (Eq : forall x, funcomp (zet) (xi) x = rho x),
      ren_ntype zet (ren_ntype xi s) = ren_ntype rho s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +rewrite map_map. apply map_ext_in. apply Forall_forall. apply (Forall_impl _ (fun n : ntype m =>
        forall (k l : nat) (xi : fin m -> fin k) (zet : fin k -> fin l) (rho : fin m -> fin l),
        (forall x : fin m, (xi >> zet) x = rho x) -> ren_ntype zet (ren_ntype xi n) = ren_ntype rho n)); auto.
    +apply H. intros. apply (up_ren_ren _ _ _ Eq).
  -apply (ap (var_ntype l t)). apply Eq.
  -apply congr_uAllN. apply H. intros. apply (up_ren_ren _ _ _ (Eq)).
Qed.
Definition compRenRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (rhontype : (fin) (mntype) -> (fin) (lntype)) (Eqntype : forall x, ((funcomp) (zetantype) (xintype)) x = rhontype x) (s : ptype (mntype)) : ren_ptype zetantype (ren_ptype xintype s) = ren_ptype rhontype s.
Proof. destruct (compRenRen_ptype_ntype mntype). now apply H. Defined.
Definition compRenRen_ntype { kntype : nat } { lntype : nat } { mntype : nat }(xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (rhontype : (fin) (mntype) -> (fin) (lntype)) (Eqntype : forall x, ((funcomp) (zetantype) (xintype)) x = rhontype x) (s : ntype (mntype)) : ren_ntype zetantype (ren_ntype xintype s) = ren_ntype rhontype s.
Proof. destruct (compRenRen_ptype_ntype mntype). now apply H0. Defined.


Definition up_ren_subst_ntype_ntype { k : nat } { l : nat } { mntype : nat } (xi : (fin) (k) -> (fin) (l)) (tau : fin w -> (fin) (l) -> ntype (mntype)) (theta : fin w -> (fin) (k) -> ntype (mntype)) (Eq : forall i x, ((funcomp) (tau i) (xi)) x = theta i x) : forall i x, ((funcomp) (up_ntype_ntype tau i) (upRen_ntype_ntype xi)) x = (up_ntype_ntype theta) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_ntype (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint compRenSubst_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : (fin) (kntype) -> ntype (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) tauntype xintype) x = thetantype x) (s : ptype (mntype)) : subst_ptype tauntype (ren_ptype xintype s) = subst_ptype thetantype s :=
    match s return subst_ptype tauntype (ren_ptype xintype s) = subst_ptype thetantype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((compRenSubst_ntype xintype tauntype thetantype Eqntype) s0) ((compRenSubst_ntype (upRen_ntype_ntype xintype) (up_ntype_ntype tauntype) (up_ntype_ntype thetantype) (up_ren_subst_ntype_ntype (_) (_) (_) Eqntype)) s1)
    end
 with compRenSubst_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : (fin) (kntype) -> ntype (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) tauntype xintype) x = thetantype x) (s : ntype (mntype)) : subst_ntype tauntype (ren_ntype xintype s) = subst_ntype thetantype s :=
    match s return subst_ntype tauntype (ren_ntype xintype s) = subst_ntype thetantype s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((compRenSubst_ptype xintype tauntype thetantype Eqntype) s0)
    end. *)
Lemma compRenSubst_ptype_ntype : forall m,
   (forall s k l (xi : fin m -> fin k) (tau : fin w -> fin k -> ntype l) (theta : fin w -> fin m -> ntype l)
     (Eq : forall i x, (xi >> (tau i)) x = theta i x), subst_ptype tau (ren_ptype xi s) = subst_ptype theta s)
/\ (forall s k l (xi : fin m -> fin k) (tau : fin w -> fin k -> ntype l) (theta : fin w -> fin m -> ntype l)
     (Eq : forall i x, (xi >> (tau i)) x = theta i x), subst_ntype tau (ren_ntype xi s) = subst_ntype theta s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +rewrite map_map. apply map_ext_in. apply Forall_forall. apply (Forall_impl _ (fun n0 : ntype m =>
        forall (k l : nat) (xi : fin m -> fin k) (tau : fin w -> fin k -> ntype l)
          (theta : fin w -> fin m -> ntype l),
        (forall (i : fin w) (x : fin m), (xi >> tau i) x = theta i x) ->
        subst_ntype tau (ren_ntype xi n0) = subst_ntype theta n0)); auto.
    +apply H. intros. apply (up_ren_subst_ntype_ntype _ _ _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (up_ren_subst_ntype_ntype _ _ _ Eq).
Qed.
Definition compRenSubst_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (tauntype i) (xintype)) x = thetantype i x) (s : ptype (mntype)) : subst_ptype tauntype (ren_ptype xintype s) = subst_ptype thetantype s.
Proof. destruct (compRenSubst_ptype_ntype mntype). now apply H. Defined.
Definition compRenSubst_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (tauntype i) (xintype)) x = thetantype i x) (s : ntype (mntype)) : subst_ntype tauntype (ren_ntype xintype s) = subst_ntype thetantype s.
Proof. destruct (compRenSubst_ptype_ntype mntype). now apply H0. Defined.


Definition up_subst_ren_ntype_ntype { k : nat } { lntype : nat } { mntype : nat } (sigma : fin w -> (fin) (k) -> ntype (lntype)) (zetantype : (fin) (lntype) -> (fin) (mntype)) (theta : fin w -> (fin) (k) -> ntype (mntype)) (Eq : forall i x, ((funcomp) (ren_ntype zetantype) (sigma i)) x = theta i x) : forall i x, ((funcomp) (ren_ntype (upRen_ntype_ntype zetantype)) (up_ntype_ntype sigma i)) x = (up_ntype_ntype theta) i x :=
  fun i n => match n with
  | Some fin_n => (eq_trans) (compRenRen_ntype (shift) (upRen_ntype_ntype zetantype) ((funcomp) (shift) zetantype) (fun x => eq_refl) (sigma i fin_n)) ((eq_trans) ((eq_sym) (compRenRen_ntype zetantype (shift) ((funcomp) (shift) zetantype) (fun x => eq_refl) (sigma i fin_n))) ((ap) (ren_ntype (shift)) (Eq i fin_n)))
  | None  => eq_refl
  end.

(* Definition up_subst_ren_ntype_ntype { k : nat } { lntype : nat } { mntype : nat } (sigma : fin n -> (fin) (k) -> ntype (lntype)) (zetantype : (fin) (lntype) -> (fin) (mntype)) (theta : fin n -> (fin) (k) -> ntype (mntype)) (Eq : forall i x, ((funcomp) (ren_ntype zetantype) (sigma i)) x = theta i x) : forall i x, ((funcomp) (ren_ntype (upRen_ntype_ntype zetantype)) (up_ntype_ntype sigma i)) x = (up_ntype_ntype theta) i x
:= fun i x =>  match x as o return ((up_ntype_ntype sigma i >> ren_ntype (upRen_ntype_ntype zetantype)) o = up_ntype_ntype theta i o) with
 | Some fin_n => eq_trans (compRenRen_ntype (↑) (upRen_ntype_ntype zetantype)
          (fun (i0 : fin n) (x0 : fin lntype) => ↑ (zetantype i0 x0))
          (fun (i0 : fin n) (x0 : fin lntype) => eq_refl) 
          (sigma i fin_n))
       (eq_trans (eq_sym (compRenRen_ntype zetantype (fun _ : fin n => ↑)
                (fun (i0 : fin n) (x0 : fin lntype) => ↑ (zetantype i0 x0))
                (fun (i0 : fin n) (x0 : fin lntype) => eq_refl) 
                (sigma i fin_n)))
       (ap (ren_ntype (fun _ : fin n => ↑)) (Eq i fin_n)))
 | None => eq_refl
end. *)


(* Fixpoint compSubstRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) (ren_ntype zetantype) sigmantype) x = thetantype x) (s : ptype (mntype)) : ren_ptype zetantype (subst_ptype sigmantype s) = subst_ptype thetantype s :=
    match s return ren_ptype zetantype (subst_ptype sigmantype s) = subst_ptype thetantype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((compSubstRen_ntype sigmantype zetantype thetantype Eqntype) s0) ((compSubstRen_ntype (up_ntype_ntype sigmantype) (upRen_ntype_ntype zetantype) (up_ntype_ntype thetantype) (up_subst_ren_ntype_ntype (_) (_) (_) Eqntype)) s1)
    end
 with compSubstRen_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) (ren_ntype zetantype) sigmantype) x = thetantype x) (s : ntype (mntype)) : ren_ntype zetantype (subst_ntype sigmantype s) = subst_ntype thetantype s :=
    match s return ren_ntype zetantype (subst_ntype sigmantype s) = subst_ntype thetantype s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((compSubstRen_ptype sigmantype zetantype thetantype Eqntype) s0)
    end. *)
Lemma compSubstRen_ptype_ntype : forall m,
   (forall s k l (sig : fin w -> fin m -> ntype k) (zeta : fin k -> fin l) (theta : fin w -> fin m -> ntype l)
    (Eq : forall i x, ((sig i) >> (ren_ntype zeta)) x = theta i x), ren_ptype zeta (subst_ptype sig s) = subst_ptype theta s)
/\ (forall s k l (sig : fin w -> fin m -> ntype k) (zeta : fin k -> fin l) (theta : fin w -> fin m -> ntype l)
    (Eq : forall i x, ((sig i) >> (ren_ntype zeta)) x = theta i x), ren_ntype zeta (subst_ntype sig s) = subst_ntype theta s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +rewrite map_map. apply map_ext_in. apply Forall_forall. apply (Forall_impl _ (fun n0 : ntype m => forall (k l : nat) (sig : fin w -> fin m -> ntype k) (zeta : fin k -> fin l) (theta : fin w -> fin m -> ntype l), (forall (i : fin w) (x : fin m), (sig i >> ren_ntype zeta) x = theta i x) -> ren_ntype zeta (subst_ntype sig n0) = subst_ntype theta n0)); auto.
    +apply H. intros. apply (up_subst_ren_ntype_ntype _ _ _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (up_subst_ren_ntype_ntype _ _ _ Eq).
Qed.
Definition compSubstRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (ren_ntype zetantype) (sigmantype i)) x = thetantype i x) (s : ptype (mntype)) : ren_ptype zetantype (subst_ptype sigmantype s) = subst_ptype thetantype s.
Proof. destruct (compSubstRen_ptype_ntype mntype). now apply H. Defined.
Definition compSubstRen_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (ren_ntype zetantype) (sigmantype i)) x = thetantype i x) (s : ntype (mntype)) : ren_ntype zetantype (subst_ntype sigmantype s) = subst_ntype thetantype s.
Proof. destruct (compSubstRen_ptype_ntype mntype). now apply H0. Defined.


(* Definition up_subst_subst_ntype_ntype { k : nat } { lntype : nat } { mntype : nat } (sigma : (fin) (k) -> ntype (lntype)) (tauntype : (fin) (lntype) -> ntype (mntype)) (theta : (fin) (k) -> ntype (mntype)) (Eq : forall x, ((funcomp) (subst_ntype tauntype) sigma) x = theta x) : forall x, ((funcomp) (subst_ntype (up_ntype_ntype tauntype)) (up_ntype_ntype sigma)) x = (up_ntype_ntype theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_ntype (shift) (up_ntype_ntype tauntype) ((funcomp) (up_ntype_ntype tauntype) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_ntype tauntype (shift) ((funcomp) (ren_ntype (shift)) tauntype) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_ntype (shift)) (Eq fin_n)))
  | None  => eq_refl
  end. *)
Definition up_subst_subst_ntype_ntype { k : nat } { lntype : nat } { mntype : nat } (sigma : fin w -> (fin) (k) -> ntype (lntype)) (tauntype : fin w -> (fin) (lntype) -> ntype (mntype)) (theta : fin w -> (fin) (k) -> ntype (mntype)) (Eq : forall i x, ((funcomp) (subst_ntype tauntype) (sigma i)) x = theta i x) : forall i x, ((funcomp) (subst_ntype (up_ntype_ntype tauntype)) (up_ntype_ntype sigma i)) x = (up_ntype_ntype theta) i x
:= fun i x => match x as o return ((up_ntype_ntype sigma i >> subst_ntype (up_ntype_ntype tauntype)) o = up_ntype_ntype theta i o) with
 | Some fin_n => eq_trans
       (compRenSubst_ntype (↑) (up_ntype_ntype tauntype)
          (fun (i0 : fin w) (x0 : fin lntype) =>
           up_ntype_ntype tauntype i0 (↑ x0))
          (fun (i0 : fin w) (x0 : fin lntype) => eq_refl) 
          (sigma i fin_n))
       (eq_trans (eq_sym (compSubstRen_ntype tauntype (↑)
                (fun (i0 : fin w) (x0 : fin lntype) =>
                 ren_ntype (↑) (tauntype i0 x0))
                (fun (i0 : fin w) (x0 : fin lntype) => eq_refl) 
                (sigma i fin_n)))
          (ap (ren_ntype (↑)) (Eq i fin_n)))
 | None => eq_refl
 end.

(* Fixpoint compSubstSubst_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : (fin) (mntype) -> ntype (kntype)) (tauntype : (fin) (kntype) -> ntype (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) (subst_ntype tauntype) sigmantype) x = thetantype x) (s : ptype (mntype)) : subst_ptype tauntype (subst_ptype sigmantype s) = subst_ptype thetantype s :=
    match s return subst_ptype tauntype (subst_ptype sigmantype s) = subst_ptype thetantype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((compSubstSubst_ntype sigmantype tauntype thetantype Eqntype) s0) ((compSubstSubst_ntype (up_ntype_ntype sigmantype) (up_ntype_ntype tauntype) (up_ntype_ntype thetantype) (up_subst_subst_ntype_ntype (_) (_) (_) Eqntype)) s1)
    end
 with compSubstSubst_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : (fin) (mntype) -> ntype (kntype)) (tauntype : (fin) (kntype) -> ntype (lntype)) (thetantype : (fin) (mntype) -> ntype (lntype)) (Eqntype : forall x, ((funcomp) (subst_ntype tauntype) sigmantype) x = thetantype x) (s : ntype (mntype)) : subst_ntype tauntype (subst_ntype sigmantype s) = subst_ntype thetantype s :=
    match s return subst_ntype tauntype (subst_ntype sigmantype s) = subst_ntype thetantype s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((compSubstSubst_ptype sigmantype tauntype thetantype Eqntype) s0)
    end. *)
Lemma compSubstSubst_ptype_ntype : forall m,
   (forall s k l (sig : fin w -> fin m -> ntype k) (tau : fin w -> fin k -> ntype l) (theta : fin w -> fin m -> ntype l)
    (Eq : forall i x, (sig i >> subst_ntype tau) x = theta i x), subst_ptype tau (subst_ptype sig s) = subst_ptype theta s)
/\ (forall s k l (sig : fin w -> fin m -> ntype k) (tau : fin w -> fin k -> ntype l) (theta : fin w -> fin m -> ntype l)
    (Eq : forall i x, (sig i >> subst_ntype tau) x = theta i x), subst_ntype tau (subst_ntype sig s) = subst_ntype theta s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +rewrite map_map. apply map_ext_in,Forall_forall. apply (Forall_impl _ (fun n0 : ntype m => forall (k l : nat) (sig : fin w -> fin m -> ntype k) (tau : fin w -> fin k -> ntype l) (theta : fin w -> fin m -> ntype l), (forall (i : fin w) (x : fin m), (sig i >> subst_ntype tau) x = theta i x) -> subst_ntype tau (subst_ntype sig n0) = subst_ntype theta n0)); auto.
    +apply H. intros. apply (up_subst_subst_ntype_ntype _ _ _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (up_subst_subst_ntype_ntype _ _ _ Eq).
Qed.
Definition compSubstSubst_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (subst_ntype tauntype) (sigmantype i)) x = thetantype i x) (s : ptype (mntype)) : subst_ptype tauntype (subst_ptype sigmantype s) = subst_ptype thetantype s.
Proof. destruct (compSubstSubst_ptype_ntype mntype). now apply H. Defined.
Definition compSubstSubst_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (thetantype : fin w -> (fin) (mntype) -> ntype (lntype)) (Eqntype : forall i x, ((funcomp) (subst_ntype tauntype) (sigmantype i)) x = thetantype i x) (s : ntype (mntype)) : subst_ntype tauntype (subst_ntype sigmantype s) = subst_ntype thetantype s.
Proof. destruct (compSubstSubst_ptype_ntype mntype). now apply H0. Defined.

Definition rinstInst_up_ntype_ntype { m : nat } { nntype : nat } (xi : (fin) (m) -> (fin) (nntype)) (sigma : fin w -> (fin) (m) -> ntype (nntype)) (Eq : forall i x, ((funcomp) (var_ntype (nntype) i) (xi)) x = sigma i x) : forall i x, ((funcomp) (var_ntype ((S) nntype) i) (upRen_ntype_ntype xi)) x = (up_ntype_ntype sigma) i x :=
  fun i n => match n with
  | Some fin_n => (ap) (ren_ntype (shift)) (Eq i fin_n)
  | None  => eq_refl
  end.

(* Fixpoint rinst_inst_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (sigmantype : (fin) (mntype) -> ntype (nntype)) (Eqntype : forall x, ((funcomp) (var_ntype (nntype)) xintype) x = sigmantype x) (s : ptype (mntype)) : ren_ptype xintype s = subst_ptype sigmantype s :=
    match s return ren_ptype xintype s = subst_ptype sigmantype s with
    | top (_)  => congr_top 
    | bAllN (_) s0 s1 => congr_bAllN ((rinst_inst_ntype xintype sigmantype Eqntype) s0) ((rinst_inst_ntype (upRen_ntype_ntype xintype) (up_ntype_ntype sigmantype) (rinstInst_up_ntype_ntype (_) (_) Eqntype)) s1)
    end
 with rinst_inst_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (sigmantype : (fin) (mntype) -> ntype (nntype)) (Eqntype : forall x, ((funcomp) (var_ntype (nntype)) xintype) x = sigmantype x) (s : ntype (mntype)) : ren_ntype xintype s = subst_ntype sigmantype s :=
    match s return ren_ntype xintype s = subst_ntype sigmantype s with
    | var_ntype (_) s => Eqntype s
    | uAllN (_) s0 => congr_uAllN ((rinst_inst_ptype xintype sigmantype Eqntype) s0)
    end. *)
Lemma rinst_inst_ptype_ntype : forall m,
   (forall s l (xi : fin m -> fin l) (sig : fin w -> fin m -> ntype l) (Eq : forall i x, var_ntype l i (xi x) = sig i x),
      ren_ptype xi s = subst_ptype sig s)
/\ (forall s l (xi : fin m -> fin l) (sig : fin w -> fin m -> ntype l) (Eq : forall i x, var_ntype l i (xi x) = sig i x),
      ren_ntype xi s = subst_ntype sig s).
Proof. eapply ptype_ntype_mutind; intros.
  -apply congr_top.
  -apply congr_bAllN.
    +apply map_ext_in,Forall_forall. apply (Forall_impl _ (fun n0 : ntype m => forall (l : nat) (xi : fin m -> fin l) (sig : fin w -> fin m -> ntype l), (forall (i : fin w) (x : fin m), var_ntype l i (xi x) = sig i x) -> ren_ntype xi n0 = subst_ntype sig n0)); auto.
    +apply H. intros. apply (rinstInst_up_ntype_ntype _ _ Eq).
  -apply Eq.
  -apply congr_uAllN. apply H. intros. apply (rinstInst_up_ntype_ntype _ _ Eq).
Qed.
Definition rinst_inst_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (Eqntype : forall i x, ((funcomp) (var_ntype (nntype) i) (xintype)) x = sigmantype i x) (s : ptype (mntype)) : ren_ptype xintype s = subst_ptype sigmantype s.
Proof. destruct (rinst_inst_ptype_ntype mntype). now apply H. Defined.
Definition rinst_inst_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) (Eqntype : forall i x, ((funcomp) (var_ntype (nntype) i) (xintype)) x = sigmantype i x) (s : ntype (mntype)) : ren_ntype xintype s = subst_ntype sigmantype s.
Proof. destruct (rinst_inst_ptype_ntype mntype). now apply H0. Defined.


Lemma rinstInst_ptype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) : ren_ptype xintype = subst_ptype (fun i => (funcomp) (var_ntype (nntype) i) (xintype)).
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ptype xintype (_) (fun i n => eq_refl) x)). Qed.

Lemma rinstInst_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) : ren_ntype xintype = subst_ntype (fun i => (funcomp) (var_ntype (nntype) i) (xintype)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_ntype xintype (_) (fun _ n => eq_refl) x)). Qed.

Lemma instId_ptype { mntype : nat } : subst_ptype (fun i => var_ntype (mntype) i) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ptype (var_ntype (mntype)) (fun _ n => eq_refl) ((id) x))). Qed.

Lemma instId_ntype { mntype : nat } : subst_ntype (fun i => var_ntype (mntype) i) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_ntype (var_ntype (mntype)) (fun _ n => eq_refl) ((id) x))). Qed.

Lemma rinstId_ptype { mntype : nat } : @ren_ptype (mntype) (mntype) (id) = id .
Proof. exact ((eq_trans) (rinstInst_ptype ((id) (_))) instId_ptype). Qed.

Lemma rinstId_ntype { mntype : nat } : @ren_ntype (mntype) (mntype) (id) = id .
Proof. exact ((eq_trans) (rinstInst_ntype ((id) (_))) instId_ntype). Qed.

Lemma varL_ntype { mntype : nat } { nntype : nat } {i : fin w} (sigmantype : fin w -> (fin) (mntype) -> ntype (nntype)) : (fun i => funcomp (subst_ntype sigmantype) (var_ntype (mntype) i)) = sigmantype .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_ntype { mntype : nat } { nntype : nat } (xintype : (fin) (mntype) -> (fin) (nntype)) : (fun i => funcomp (ren_ntype xintype) (var_ntype (mntype) i)) = (fun i => funcomp (var_ntype (nntype) i) (xintype)).
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (s : ptype (mntype)) : subst_ptype tauntype (subst_ptype sigmantype s) = subst_ptype (fun i => (funcomp) (subst_ntype tauntype) (sigmantype i)) s .
Proof. exact (compSubstSubst_ptype sigmantype tauntype (_) (fun _ n => eq_refl) s). Qed.

Lemma compComp_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (s : ntype (mntype)) : subst_ntype tauntype (subst_ntype sigmantype s) = subst_ntype (fun i => (funcomp) (subst_ntype tauntype) (sigmantype i)) s .
Proof. exact (compSubstSubst_ntype sigmantype tauntype (_) (fun _ n => eq_refl) s). Qed.

Lemma compComp'_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) : (funcomp) (subst_ptype tauntype) (subst_ptype sigmantype) = subst_ptype (fun i => (funcomp) (subst_ntype tauntype) (sigmantype i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ptype sigmantype tauntype n)). Qed.

Lemma compComp'_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) : (funcomp) (subst_ntype tauntype) (subst_ntype sigmantype) = subst_ntype (fun i => (funcomp) (subst_ntype tauntype) (sigmantype i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_ntype sigmantype tauntype n)). Qed.

Lemma compRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (s : ptype (mntype)) : ren_ptype zetantype (subst_ptype sigmantype s) = subst_ptype (fun i => (funcomp) (ren_ntype zetantype) (sigmantype i)) s .
Proof. exact (compSubstRen_ptype sigmantype zetantype (_) (fun _ n => eq_refl) s). Qed.

Lemma compRen_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (s : ntype (mntype)) : ren_ntype zetantype (subst_ntype sigmantype s) = subst_ntype (fun i => (funcomp) (ren_ntype zetantype) (sigmantype i)) s .
Proof. exact (compSubstRen_ntype sigmantype zetantype (_) (fun _ n => eq_refl) s). Qed.

Lemma compRen'_ptype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) : (funcomp) (ren_ptype zetantype) (subst_ptype sigmantype) = subst_ptype (fun i => (funcomp) (ren_ntype zetantype) (sigmantype i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ptype sigmantype zetantype n)). Qed.

Lemma compRen'_ntype { kntype : nat } { lntype : nat } { mntype : nat } (sigmantype : fin w -> (fin) (mntype) -> ntype (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) : (funcomp) (ren_ntype zetantype) (subst_ntype sigmantype) = subst_ntype (fun i => (funcomp) (ren_ntype zetantype) (sigmantype i)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_ntype sigmantype zetantype n)). Qed.

Lemma renComp_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (s : ptype (mntype)) : subst_ptype tauntype (ren_ptype xintype s) = subst_ptype (fun i => (funcomp) (tauntype i) (xintype)) s .
Proof. exact (compRenSubst_ptype xintype tauntype (_) (fun _ n => eq_refl) s). Qed.

Lemma renComp_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) (s : ntype (mntype)) : subst_ntype tauntype (ren_ntype xintype s) = subst_ntype (fun i => (funcomp) (tauntype i) (xintype)) s .
Proof. exact (compRenSubst_ntype xintype tauntype (_) (fun _ n => eq_refl) s). Qed.

Lemma renComp'_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) : (funcomp) (subst_ptype tauntype) (ren_ptype xintype) = subst_ptype (fun i => (funcomp) (tauntype i) (xintype )) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ptype xintype tauntype n)). Qed.

Lemma renComp'_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (tauntype : fin w -> (fin) (kntype) -> ntype (lntype)) : (funcomp) (subst_ntype tauntype) (ren_ntype xintype) = subst_ntype (fun i => (funcomp) (tauntype i) (xintype)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_ntype xintype tauntype n)). Qed.

Lemma renRen_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) (s : ptype (mntype)) : ren_ptype zetantype (ren_ptype xintype s) = ren_ptype ((funcomp) (zetantype) (xintype)) s .
Proof. exact (compRenRen_ptype xintype zetantype (_) (fun n => eq_refl) s). Qed.

Lemma renRen_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype :(fin) (kntype) -> (fin) (lntype)) (s : ntype (mntype)) : ren_ntype zetantype (ren_ntype xintype s) = ren_ntype ((funcomp) (zetantype) (xintype)) s .
Proof. exact (compRenRen_ntype xintype zetantype (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_ptype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) : (funcomp) (ren_ptype zetantype) (ren_ptype xintype) = ren_ptype ((funcomp) (zetantype) (xintype)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ptype xintype zetantype n)). Qed.

Lemma renRen'_ntype { kntype : nat } { lntype : nat } { mntype : nat } (xintype : (fin) (mntype) -> (fin) (kntype)) (zetantype : (fin) (kntype) -> (fin) (lntype)) : (funcomp) (ren_ntype zetantype) (ren_ntype xintype) = ren_ntype ((funcomp) (zetantype) (xintype)) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_ntype xintype zetantype n)). Qed.

End ptypentype.

Arguments top {w} {nntype}.

Arguments bAllN {w} {nntype}.

Arguments var_ntype {w} {nntype}.

Arguments uAllN {w} {nntype}.
(*
Global Instance Subst_ptype { mntype : nat } { nntype : nat } : Subst1 ((fin) (mntype) -> ntype (nntype)) (ptype (mntype)) (ptype (nntype)) := @subst_ptype (mntype) (nntype) .

Global Instance Subst_ntype { mntype : nat } { nntype : nat } : Subst1 ((fin) (mntype) -> ntype (nntype)) (ntype (mntype)) (ntype (nntype)) := @subst_ntype (mntype) (nntype) .

Global Instance Ren_ptype { mntype : nat } { nntype : nat } : Ren1 ((fin) (mntype) -> (fin) (nntype)) (ptype (mntype)) (ptype (nntype)) := @ren_ptype (mntype) (nntype) .

Global Instance Ren_ntype { mntype : nat } { nntype : nat } : Ren1 ((fin) (mntype) -> (fin) (nntype)) (ntype (mntype)) (ntype (nntype)) := @ren_ntype (mntype) (nntype) .

Global Instance VarInstance_ntype { mntype : nat } : Var ((fin) (mntype)) (ntype (mntype)) := @var_ntype (mntype) .

Notation "x '__ntype'" := (var_ntype x) (at level 5, format "x __ntype") : subst_scope.

Notation "x '__ntype'" := (@ids (_) (_) VarInstance_ntype x) (at level 5, only printing, format "x __ntype") : subst_scope.

Notation "'var'" := (var_ntype) (only printing, at level 1) : subst_scope.

Class Up_ntype X Y := up_ntype : X -> Y.

Notation "↑__ntype" := (up_ntype) (only printing) : subst_scope.

Notation "↑__ntype" := (up_ntype_ntype) (only printing) : subst_scope.

Global Instance Up_ntype_ntype { m : nat } { nntype : nat } : Up_ntype (_) (_) := @up_ntype_ntype (m) (nntype) .
 *)
(* Notation "s [ sigmantype ]" := (subst_ptype sigmantype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmantype ]" := (subst_ptype sigmantype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xintype ⟩" := (ren_ptype xintype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xintype ⟩" := (ren_ptype xintype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s [ sigmantype ]" := (subst_ntype sigmantype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "[ sigmantype ]" := (subst_ntype sigmantype) (at level 1, left associativity, only printing) : fscope. *)

(* Notation "s ⟨ xintype ⟩" := (ren_ntype xintype s) (at level 7, left associativity, only printing) : subst_scope. *)

(* Notation "⟨ xintype ⟩" := (ren_ntype xintype) (at level 1, left associativity, only printing) : fscope. *)

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2(*,   Subst_ptype,  Subst_ntype,  Ren_ptype,  Ren_ntype,  VarInstance_ntype *).

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2(* ,  Subst_ptype,  Subst_ntype,  Ren_ptype,  Ren_ntype,  VarInstance_ntype *) in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_ptype| progress rewrite ?compComp_ptype| progress rewrite ?compComp'_ptype| progress rewrite ?instId_ntype| progress rewrite ?compComp_ntype| progress rewrite ?compComp'_ntype| progress rewrite ?rinstId_ptype| progress rewrite ?compRen_ptype| progress rewrite ?compRen'_ptype| progress rewrite ?renComp_ptype| progress rewrite ?renComp'_ptype| progress rewrite ?renRen_ptype| progress rewrite ?renRen'_ptype| progress rewrite ?rinstId_ntype| progress rewrite ?compRen_ntype| progress rewrite ?compRen'_ntype| progress rewrite ?renComp_ntype| progress rewrite ?renComp'_ntype| progress rewrite ?renRen_ntype| progress rewrite ?renRen'_ntype| progress rewrite ?varL_ntype| progress rewrite ?varLRen_ntype| progress (unfold up_ren, upRen_ntype_ntype, up_ntype_ntype)| progress (cbn [subst_ptype subst_ntype ren_ptype ren_ntype])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_ptype in *| progress rewrite ?compComp_ptype in *| progress rewrite ?compComp'_ptype in *| progress rewrite ?instId_ntype in *| progress rewrite ?compComp_ntype in *| progress rewrite ?compComp'_ntype in *| progress rewrite ?rinstId_ptype in *| progress rewrite ?compRen_ptype in *| progress rewrite ?compRen'_ptype in *| progress rewrite ?renComp_ptype in *| progress rewrite ?renComp'_ptype in *| progress rewrite ?renRen_ptype in *| progress rewrite ?renRen'_ptype in *| progress rewrite ?rinstId_ntype in *| progress rewrite ?compRen_ntype in *| progress rewrite ?compRen'_ntype in *| progress rewrite ?renComp_ntype in *| progress rewrite ?renComp'_ntype in *| progress rewrite ?renRen_ntype in *| progress rewrite ?renRen'_ntype in *| progress rewrite ?varL_ntype in *| progress rewrite ?varLRen_ntype in *| progress (unfold up_ren, upRen_ntype_ntype, up_ntype_ntype in *)| progress (cbn [subst_ptype subst_ntype ren_ptype ren_ntype] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_ptype); try repeat (erewrite rinstInst_ntype).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_ptype); try repeat (erewrite <- rinstInst_ntype).

Notation "⊤" := (top).
Notation "∀+ S « T »" := (bAllN S T).
Notation "∀- « T »" := (uAllN T).
