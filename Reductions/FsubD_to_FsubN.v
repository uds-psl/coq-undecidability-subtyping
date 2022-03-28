(** * Reduction from the Deterministic System Fsub to the Normal System Fsub *)
(* begin details : Imports *)
Require Import FsubN FsubD.
Require Import Lia Arith.
From Equations Require Import Equations.
Require Import Vector Utils.Various_utils.
Require Import Utils.psyntax Utils.syntax.
Import VectorNotations.
(* end details *)

Fact all_inj `{arrow_flag} {s1 s2 t1 t2} : all s1 s2 = all t1 t2 -> s1=t1 /\ s2=t2.
Proof. intro H1. inversion H1. split. apply (DPI H2). apply (DPI H3). Qed.

(** The flip property is immediate for the height-agnostic system *)
Definition neg (t : type0) : type0 := all t (var_type 0).
Derive Signature for subN.
Fact flipNeg Γ s t : (Γ |-N neg s <: neg t) <-> (Γ |-N t <: s).
Proof. unfold neg. split; intro.
  -depind H; try discriminate. destruct (all_inj H1) as [-> _]. destruct (all_inj H2) as [-> _]. auto.
  -apply NAll. auto. apply NRefl.
Qed.


(** ** Translation *)

Section argument.

Context {w:nat}.
Variable (Hw: 0<w).
Fixpoint mkBounded {n} (v : Vector.t type0 n) (b : type0) {struct v} : type0
  := match v with
  | [] => neg b
  | Vector.cons _ h n0 v0 => all h (mkBounded v0 b)
end.

Fixpoint mkUnbounded (n : nat)(b : type0) : type0
  := match n with
  | 0 => neg b 
  | S n => all top (mkUnbounded n b)
end.

Fixpoint iterShift (n:nat) (t: fin) : fin := match n with
  | 0 => t
  | S n0 => ↑(iterShift n0 t)
end.

Fixpoint addShiftings {n} i (v : Vector.t type0 n) : Vector.t type0 n :=
  match v in (t _ n0) return (t type0 n0) with
  | [] => []
  | Vector.cons _ h n0 v0 => ( ren_type (iterShift i) h :: addShiftings (S i) v0)%vector
  end.

Fixpoint ptranslation {n} (t : @ptype w n) : type0 := match t with
  | psyntax.top => syntax.top
  | bAllN t1 t2 => mkBounded (addShiftings 0 (Vector.map (ntranslation) t1)) (ntranslation t2)
  end
with ntranslation {n} (s: @ntype w n) : type0 := match s with
  | var_ntype i j => var_type (fins2nat i j)
  | uAllN t => mkUnbounded w (ptranslation t)
end.

(* begin details: Facts about the translation. *)
Fact nth'_addShiftings {l x} {v: Vector.t type0 l} (H : x<l) y :
  nth' (addShiftings y v) (nat2nif H) = ren_type (iterShift (l-S x+y)) (nth' v (nat2nif H)).
Proof. revert y. induction v; intro. lia. simpl. destruct (le_lt_dec n x); simpl.
  -assert (n-x+y=y). lia. now rewrite H0.
  -rewrite (nat2nif_ext _ l). rewrite (IHv l). assert (n-S x+S y=n-x+y). lia. now rewrite H0.
Qed.
Fact nth'_addShiftings' {l x} {v: Vector.t type0 l} (H : x<l) y :
  nth' (addShiftings y v) (nat2fin H) = ren_type (iterShift (x+y)) (nth' v (nat2fin H)).
Proof. revert x H y. induction v; intros. lia. destruct x. auto. simpl.
  rewrite IHv. now rewrite Nat.add_succ_r.
Qed.
Fact nth_addShiftings {l x y d} {v: Vector.t type0 l} : x<l ->
  nth x (to_list (addShiftings y v)) d = ren_type (iterShift (x+y)) (nth x (to_list v) d).
Proof. revert x y. induction v; intros. lia. destruct x. auto.
  change (to_list (h::v)) with (cons h (to_list v)). simpl addShiftings.
  change (to_list (ren_type (iterShift y) h :: addShiftings (S y) v)) with
    (cons (ren_type (iterShift y) h) (to_list (addShiftings (S y) v))).
  simpl nth. rewrite IHv. now rewrite Nat.add_succ_r. lia.
Qed.

Fixpoint ptrans_noVar {m i t} : var_type i <> @ptranslation m t.
Proof. destruct t. discriminate. simpl. induction t; simpl; discriminate.
Qed.

Fact mkBnd_noTop {n v b } : syntax.top <> @mkBounded n v b.
Proof. destruct v; discriminate. Qed.

Fact mkUnd_noVar {n i b} : var_type i <> @mkUnbounded n b.
Proof. destruct n; discriminate. Qed.

Fact mkBnd_noVar {n i v b} : var_type i <> @mkBounded n v b.
Proof. destruct v; discriminate. Qed.

Fact congr_mkUnbounded {n s t} : s=t -> mkUnbounded n s = mkUnbounded n t.
Proof. congruence. Qed.
Fact congr_mkBounded {n} {u v : Vector.t type0 n} {s t} : u=v -> s=t -> mkBounded u s = mkBounded v t.
Proof. congruence. Qed.

Fixpoint iterFnShift {m} n (i : fintype.fin m) {struct n} : fintype.fin (n+m).
Proof. destruct n.
  -exact i.
  -apply (fintype.shift),(iterFnShift _ _ i).
Defined.

Fixpoint iterLift (n : nat) (r : fin->fin) {struct n} : fin-> fin := match n with
  | 0 => r
  | S n0 => upRen_type_type (iterLift n0 r)
  end.

Fixpoint iterPLift (n : nat) {m m'} (r : fintype.fin m ->fintype.fin m') {struct n} : fintype.fin (n+m) ->fintype.fin (n+m').
Proof. destruct n.
  -exact r.
  -apply upRen_ntype_ntype,(iterPLift _ _ _ r).
Defined.

Fact iterShiftR n (t : type0) : ren_type (iterShift (S n)) t = ren_type ↑ (ren_type (iterShift n) t).
Proof. induction n.
  -change (iterShift 0) with (@id fin). asimpl. now simpl.
  -simpl in *. change (fun t0 : fin => ↑ (↑ (iterShift n t0))) with ((fun t : fin => ↑ (iterShift n t)) >> ↑).
   erewrite <- compRenRen_type; eauto.
Qed.

Fact iterShiftLR n (t: type0) : ren_type (iterShift n) (ren_type ↑ t) = ren_type ↑ (ren_type (iterShift n) t).
Proof. induction n.
  -change (iterShift 0) with (@id fin). asimpl. now simpl.
  -simpl in *.
   change (ren_type (fun t0 : fin => ↑ (iterShift n t0)) (ren_type ↑ t)) with (ren_type (iterShift n >> ↑) (ren_type ↑ t)).
   change (ren_type (fun t0 : fin => ↑ (iterShift n t0)) t) with (ren_type (iterShift n >> ↑) t ).
   assert (ren_type (iterShift n >> ↑) (ren_type ↑ t)=ren_type ↑ (ren_type (iterShift n) (ren_type ↑ t))).
   { erewrite <- compRenRen_type; try eauto. }
   assert (ren_type (iterShift n >> ↑) t = ren_type ↑ (ren_type (iterShift n) t)).
   { erewrite <- compRenRen_type. 2:eauto. auto. }
   rewrite H. rewrite IHn. now rewrite H0.
Qed.

Fact iterShiftAdd n m (t:type0) : ren_type (iterShift n) (ren_type (iterShift m) t) = ren_type (iterShift (n+m)) t.
Proof. revert n. induction m; intro.
  -change (iterShift 0) with (@id fin). rewrite Nat.add_0_r. now asimpl.
  -rewrite iterShiftR. rewrite iterShiftLR. rewrite <- iterShiftR. rewrite IHm. now rewrite Nat.add_succ_r.
Qed.

Fact iterLiftL n r : upRen_type_type (iterLift n r) = iterLift (S n) r.
Proof. auto. Qed.
Fact iterLiftLR n r : (upRen_type_type (iterLift n r)) = iterLift n (upRen_type_type r).
Proof. induction n; auto. simpl. now rewrite IHn. Qed.
Fact iterPnLiftL n {m m'} (r : fintype.fin m ->fintype.fin m') : upRen_ntype_ntype (iterPLift n r) = iterPLift (S n) r.
Proof. auto. Qed.

Fact iter_unfold' n x: iterShift n x = n+x.
Proof. induction n; simpl; [ change (fun i:fin=>i) with (@id fin) | rewrite IHn]; now asimpl.
Qed.
Fact iter_unfold n: iterShift n = fun i=>n+i.
Proof. fext. intro. apply iter_unfold'.
Qed.

Fact shif_lift n (t:type0): ren_type (iterShift (n+w)) t = ren_type (iterShift n >> iterLift n (iterShift w)) t.
Proof. induction n.
  -change (iterShift 0) with (@id fin). asimpl. now simpl.
  -change (S n+w) with (S (n+w)). rewrite iterShiftR. rewrite IHn.
   erewrite compRenRen_type; eauto.
Qed.

Fact ren_Ubnd r n t : ren_type r (mkUnbounded n t) = mkUnbounded n (ren_type (iterLift n r) t).
Proof. revert r. induction n; intro; simpl. auto. apply congr_all. auto. rewrite IHn. now rewrite iterLiftLR. Qed.

Fixpoint renBounds {n} r (v : Vector.t type0 n) : Vector.t type0 n :=
  match v in (t _ n0) return (t type0 n0) with
  | [] => []
  | Vector.cons _ h n0 v0 => ( ren_type r h :: renBounds (upRen_type_type r) v0)%vector
  end.
Fact nth'_renBounds {l x} {v: Vector.t type0 l} (H : x<l) r : nth' (renBounds r v) (nat2fin H) = (nth' v (nat2fin H)) ⟨iterLift x r⟩.
Proof. revert x H r. induction v; intros. lia. destruct x. auto.
  simpl. rewrite IHv. now rewrite iterLiftLR.
Qed.

Fact ren_Bnd {n} r (v:Vector.t type0 n) i t : ren_type r (mkBounded (addShiftings i v) t) = mkBounded (renBounds r (addShiftings i v)) (ren_type (iterLift n r) t).
Proof. revert r i. induction v; intros; simpl. auto. apply congr_all. auto. rewrite IHv. now rewrite iterLiftLR. Qed.


Definition tRen {n m} (r : fintype.fin n -> fintype.fin m) :  fin -> fin.
Proof. intros x. destruct (le_lt_dec (w*n) x). exact x. destruct (nat2fins l) as [i j]. exact (fins2nat i (r j)).
Defined.

Fact aux i j n : i < w -> j < (S n) -> w * (S n) <= j * w + i -> False.
Proof. intro. revert j. induction n; intros.
  -assert (j=0). lia. rewrite H2 in H1. simpl in H1. lia.
  -revert H1. rewrite (@Nat.mul_comm w). destruct j. lia. simpl. intro. apply (IHn (S j)).
    { destruct (le_lt_dec n j). assert (j=n). lia. rewrite H2 in H1. lia. lia. } lia.
Qed.

Fixpoint tRen_char {n m} (i: fintype.fin w) (j: fintype.fin n) (r : fintype.fin n -> fintype.fin m) {struct n}: tRen r (fins2nat i j) = fins2nat i (r j).
Proof. destruct n. contradiction. unfold tRen. destruct (le_lt_dec (w * S n) (fins2nat i j)).
  {exfalso. revert l. unfold fins2nat. destruct (nif2nat i) as [i' [H0 H1]]. destruct (fin2nat' j) as [j' [H2 H3]]. now apply (aux i' j' n). }
  now rewrite n2fs_unfold.
Qed.

Fact iterL_ge {r n x} : n<=x -> iterLift n r x = iterShift n (r (x-n)).
Proof. revert x. induction n; intros.
  -simpl. now rewrite Nat.sub_0_r.
  -destruct x; simpl. lia. unfold funcomp. erewrite IHn. auto. lia.
Qed.
Fact iterL_lt {r n x} : x<n -> iterLift n r x = x.
Proof. revert x. induction n. lia. intros. simpl. asimpl.
  destruct x; simpl. auto. asimpl. rewrite IHn; lia.
Qed.

Fact renBounds_shifts {n m r s} {t : Vector.t (@ntype w m) n} (Hrs : forall x, x < w * m -> r x = s x ) :
Vector.Forall (fun n => forall r s, (forall x, x < w * m -> r x = s x) -> (ntranslation n) ⟨r⟩ = (ntranslation n) ⟨s⟩) t->
renBounds r (addShiftings 0 (Vector.map ntranslation t)) = renBounds s (addShiftings 0 (Vector.map ntranslation t)).
Proof. intro. apply ext_nth'. intro. destruct (fin2nat' i) as [x [Hx <-]].
  repeat rewrite nth'_renBounds. repeat rewrite nth'_addShiftings'. rewrite nth'_map. rewrite Nat.add_0_r.
  rewrite iter_unfold. asimpl. unfold funcomp. 
  edestruct (@Forall_nth' (@ntype w m)
    (fun t => ren_type (fun x0 : fin => iterLift x r (x + x0)) (ntranslation t)=ren_type (fun x0 : fin => iterLift x s (x + x0)) (ntranslation t)) n t).
  apply H0. clear H0 H1. revert H. eapply Vector.Forall_impl. intros. apply H.
  intros. destruct (le_lt_dec x (x+x0)).
  -repeat erewrite iterL_ge; auto. rewrite minus_plus. rewrite Hrs; auto.
  -repeat erewrite iterL_lt; auto.
Qed.
Fact ext_lift {m r s} (Hrs : forall x, x < w * m -> r x = s x ) {x} (Hx: x < w * S m): iterLift w r x = iterLift w s x.
Proof. destruct (le_lt_dec w x).
  -repeat rewrite (iterL_ge l). repeat rewrite iter_unfold. erewrite Hrs. auto. lia.
  -now repeat rewrite (iterL_lt l).
Qed.

Fact ext_trans : forall m,
    (forall (t: @ptype w m) r s, (forall x, x<w*m -> r x = s x) -> ren_type r (ptranslation t) = ren_type s (ptranslation t))
/\  (forall (t: @ntype w m) r s, (forall x, x<w*m -> r x = s x) -> ren_type r (ntranslation t) = ren_type s (ntranslation t)).
Proof. eapply ptype_ntype_mutind; intros; simpl. auto.
  -repeat rewrite ren_Bnd. apply congr_mkBounded. apply renBounds_shifts,H0. exact H1. apply H. now apply ext_lift.
  -asimpl. now rewrite (H _ (fins2nat_lt t t0)).
  -repeat rewrite ren_Ubnd. apply congr_mkUnbounded. apply H. now apply ext_lift.
Qed.

Fact tRen_up {n m} (r : fintype.fin m -> fintype.fin n) x : x < w * S m -> tRen (upRen_ntype_ntype r) x = iterLift w (tRen r) x.
Proof. intro. unfold tRen. destruct (le_lt_dec (w * S m) x). lia. clear H. unfold nat2fins.
  destruct (nat2fins' l) as [i [j H]]. rewrite <- H. destruct j; simpl.
  - unfold axioms.funcomp. change Datatypes.Some with (@fintype.shift m) in *. repeat rewrite fs2nS.
    erewrite iterL_ge. 2: lia. rewrite minus_plus. destruct (le_lt_dec (w * m) (fins2nat i f)).
    {exfalso. pose (fins2nat_lt i f). lia. } rewrite <- iter_unfold. destruct (nat2fins' l0) as [i' [j' H']].
    now destruct (fins2nat_eq H') as [-> ->].
  - erewrite iterL_lt. auto. apply (@fins2nat_0lt _ m).
Qed.

Fact shifts_ren {n m m'} {t:Vector.t (@ntype w m) n} (r : fintype.fin m -> fintype.fin m')
  (Hv:Vector.Forall (fun n : ntype m => forall (n0 : fin) (r : fintype.fin m -> fintype.fin n0), ntranslation (ren_ntype r n) = (ntranslation n) ⟨tRen r⟩) t) :
  addShiftings 0 (Vector.map ntranslation (Vector.map (ren_ntype r) t)) = renBounds (tRen r) (addShiftings 0 (Vector.map ntranslation t)).
Proof. apply ext_nth'. intro. destruct (fin2nat' i) as [x [Hx <-]].
  rewrite nth'_renBounds. repeat rewrite nth'_addShiftings'. rewrite Vector.map_map. repeat rewrite nth'_map.
  rewrite Nat.add_0_r. rewrite iter_unfold. asimpl. edestruct (@Forall_nth' (@ntype w m)
    (fun t => ren_type (fun i : fin => x + i) (ntranslation (ren_ntype r t))=ren_type ((fun i : fin => x + i) >> iterLift x (tRen r)) (ntranslation t))).
  apply H. clear H H0. revert Hv. eapply Vector.Forall_impl. intros. rewrite H.
  asimpl. apply ext_trans. intros. unfold funcomp. rewrite iterL_ge. 2: apply Nat.le_add_r.
  rewrite minus_plus. now rewrite <- iter_unfold'.
Qed.

Fact trans_ren : forall m,
    (forall (t: @ptype w m) n (r: fintype.fin m -> fintype.fin n),
      ptranslation (ren_ptype r t) = ren_type (tRen r) (ptranslation t))
/\  (forall (t: @ntype w m) n (r: fintype.fin m -> fintype.fin n),
      ntranslation (ren_ntype r t) = ren_type (tRen r) (ntranslation t)).
Proof. eapply ptype_ntype_mutind; intros; simpl. auto.
  -rewrite ren_Bnd. apply congr_mkBounded.
    +apply shifts_ren,H0.
    +rewrite H. apply ext_trans, tRen_up.
  -asimpl. now rewrite tRen_char.
  -rewrite ren_Ubnd. apply congr_mkUnbounded. rewrite H. apply ext_trans,tRen_up.
Qed.

Fact ntransUp {m} (t: @ntype w m) : ntranslation (ren_ntype fintype.shift t) = ren_type (iterShift w) (ntranslation t).
Proof. destruct (trans_ren m). rewrite H0. apply ext_trans. rewrite iter_unfold.
  intros. unfold tRen. destruct (le_lt_dec (w * m) x). lia. clear H H0 H1.
  revert l. generalize m. induction m0. lia.
  intro. unfold nat2fins. destruct (nat2fins' l) as [i [j H]].
  rewrite fs2nS. now rewrite H.
Qed.


Fact cons_comp {X} {x:X} f (g : X->X) : g x .: (f >> g) = (x.:f) >> g.
Proof. now asimpl. Qed.

Fixpoint foldAdd {n} (v : Vector.t type0 n) (Γ : list type0) {struct v} : list type0.
Proof. destruct v. exact Γ. apply (foldAdd _ v (map (ren_type ↑) (h :: Γ))). Defined.

Fact length_foldAdd {n Γ} {v : Vector.t type0 n} : length (foldAdd v Γ) = n + length Γ.
Proof. revert Γ. induction v; intro; simpl. auto. rewrite IHv. simpl. rewrite map_length. now rewrite Nat.add_succ_r.
Qed.

Fixpoint foldAdd_ge {l d} {v : Vector.t type0 l} {Γ : list type0} {i : unscoped.fin} : l<=i ->
  nth i (foldAdd v Γ) d = nth (i-l) (map (ren_type (iterShift l)) Γ) d.
Proof. destruct v; intros; simpl. change (fun t : fin => t) with (@id fin). asimpl. now rewrite <- minus_n_O,map_id.
  destruct i. lia. simpl. rewrite foldAdd_ge. 2: lia. assert (S i-n=S (i-n)). lia. rewrite H0. simpl.
  rewrite map_map. assert (forall {A x d1} {l1 l2 : list A}, l1 =l2 -> nth x l1 d1 = nth x l2 d1) by congruence.
  eapply H1. apply map_ext. intro. rewrite iterShiftLR. erewrite compRenRen_type; eauto.
Qed.

Fixpoint foldAdd_lt {l d} {v : Vector.t type0 l} {Γ : list type0} {i : unscoped.fin} (H:i<l) :
  nth i (foldAdd v Γ) d = ren_type (iterShift (S i)) (nth (l-S i) (to_list v) d).
Proof. induction v. lia. simpl foldAdd. destruct (le_lt_dec n i).
  -rewrite (foldAdd_ge l). assert (i=n). lia. rewrite H0. repeat rewrite Nat.sub_diag. rewrite <- map_cons.
   rewrite map_map. change (to_list (h::v)) with (cons h (to_list v)). simpl.
   erewrite  compRenRen_type; eauto. intro. unfold funcomp. rewrite iter_unfold'.
   change ↑ with S. apply Nat.add_succ_r.
  -rewrite (foldAdd_lt _ _ _ _ _ l). rewrite Nat.sub_succ_l. 2:lia.
   change (to_list (h::v)) with (cons h (to_list v)). now simpl.
Qed.

Fact congr_NORM `{arrow_flag} : forall Γ Γ' s s' t t', Γ=Γ' -> s=s' -> t=t' -> Γ |-N s <: t -> Γ' |-N s'<: t'.
Proof. congruence. Qed.

Fact comp_assoc {A B C D} {f:A->B} {g:B->C} {h:C->D} : f >> (g >> h) = (f >> g) >> h.
Proof. now fext. Qed.

(* end details *)

Fixpoint mkCtx {m} (Γ : @ctx w m) : list type0.
Proof. destruct Γ. exact nil. apply (map (ren_type (iterShift w))). apply Datatypes.app.
  -eapply rev,to_list,(Vector.map ntranslation),t.
  -eapply mkCtx,Γ.
Defined.

Fact length_mkCtx {m} (Γ : @ctx w m) : length (mkCtx Γ) = m*w.
Proof. induction Γ; simpl. auto. rewrite map_length. rewrite app_length. rewrite rev_length.
  rewrite length_to_list. change (@type' arrow_off) with type0. now rewrite IHΓ.
Qed.

Fact mkCtx_eq {m i j} {Γ : @ctx w m} : nth_default (var_type (fins2nat i j)) (mkCtx Γ) (fins2nat i j) = ntranslation (ctx_at Γ i j).
Proof. induction Γ. contradiction. destruct j.
  -change (Datatypes.Some f) with (fintype.shift f). rewrite fs2nS. simpl.
   rewrite map_app. rewrite nth_default_eq. rewrite app_nth2. 
   assert (length (list_map (@ren_type arrow_off (iterShift w))
        (@rev (@type' arrow_off) (@to_list (@type' arrow_off) w
          (@Vector.map (@ntype w m) type0 (@ntranslation m) w t)))) = w) as ->.
   { rewrite map_length. rewrite rev_length. now rewrite length_to_list. }
   assert (w + fins2nat i f - w = fins2nat i f) as ->. lia.
   assert (@var_type arrow_off (w + fins2nat i f) = ren_type (iterShift w) (var_type (fins2nat i f))) as -> by reflexivity.
   rewrite map_nth. rewrite <- nth_default_eq. rewrite IHΓ. now rewrite ntransUp.
   rewrite map_length. rewrite rev_length. rewrite length_to_list. lia.
  -simpl. unfold fins2nat. destruct (nif2nat i) as [x [Hxw Hi]]. simpl. rewrite nth_default_eq.
   rewrite map_app. rewrite app_nth1. erewrite nth_indep'. rewrite to_list_map.
   rewrite rev_nth. erewrite nth_indep'. rewrite ntransUp.
   erewrite nth_nth'. now rewrite <- Hi.
   rewrite map_length. now rewrite length_to_list. 
   rewrite map_length. rewrite length_to_list. lia.
   rewrite map_length. now rewrite length_to_list.
   rewrite rev_length. now rewrite length_to_list.
   rewrite map_length. rewrite rev_length. now rewrite length_to_list.
   Unshelve. exact top. apply uAllN. exact psyntax.top.
Qed.

(** ** Reduction 
The proof is split in two general cases, namely when w=0 and when w>0. *)

(** As per the assumption of this section this is the proof for w>0.
*)

Fact load {l} {Γ} {t1 : Vector.t type0 l} {s t2}: foldAdd t1 Γ |-N t2 <: s ->
  Γ |-N mkUnbounded l s <: mkBounded t1 t2.
Proof.  revert Γ s t2. induction t1; simpl; intros.
   -now apply flipNeg.
  -apply NAll. apply NTop. now apply IHt1.
Qed.

Lemma d2n {m} (Γ :@ctx w m) s t : (exists h, Γ |-D h; s <: t) ->
  mkCtx Γ |-N ntranslation s <: ptranslation t.
Proof. intros [h H]. induction H; simpl; try constructor. now rewrite mkCtx_eq.
  apply load. revert IHsubD. apply congr_NORM; auto.
  simpl. rewrite map_app. eapply nth_ext.
  -rewrite app_length. repeat rewrite map_length. now rewrite rev_length, length_to_list, length_foldAdd.
  -rewrite app_length. repeat rewrite map_length. rewrite rev_length,length_to_list,length_mkCtx.
   intros. destruct (le_lt_dec w n).
    +erewrite app_nth2. rewrite map_length, rev_length, length_to_list. now rewrite (foldAdd_ge l).
     now rewrite map_length,rev_length,length_to_list.
    +erewrite app_nth1. erewrite map_nth, rev_nth, length_to_list. rewrite (foldAdd_lt l).
     rewrite nth_addShiftings, iterShiftAdd. assert (S n + (w-S n+0)=w) as -> by lia.
     erewrite nth_indep. eauto. rewrite length_to_list. lia. lia. rewrite length_to_list. lia.
     now rewrite map_length,rev_length,length_to_list. Unshelve. exact top.
Qed.

(** at this point we need the height of the derivations in the Normal System *)
(* begin details : height indexed system *)
Reserved Notation "Γ '|-IN' i ; s <: t" (at level 68, i, s, t at next level).
Inductive iSub : forall {b:arrow_flag}, (list (@type' b)) -> nat -> @type' b -> @type' b-> Prop:=
  | iTop {b: arrow_flag} Γ s : Γ |-IN 0; s <: syntax.top
  | iRefl {b: arrow_flag} Γ n : Γ |-IN 0; var_type n <: var_type n
  | iVar {b: arrow_flag} Γ s n i : Γ |-IN i; nth_default (var_type n) Γ n <: s -> Γ |-IN (S i); var_type n <: s
  | iArr Γ {s1 s2 t1 t2 i} j : Γ |-IN j; t1 <: s1 -> Γ |-IN i; s2 <: t2 ->
       Γ |-IN (S (max i j)); (arr s1 s2) <: (arr t1 t2)
  | iAll {b: arrow_flag} Γ {s1 s2 t1 t2 i} j : Γ |-IN j; t1 <: s1 -> map (ren_type ↑) (cons t1 Γ) |-IN i; s2 <: t2 ->
       Γ |-IN (S (max i j)); (all s1 s2) <: (all t1 t2)
  where "Γ '|-IN' i ; s <: t" := (iSub Γ i s t).
Derive Signature for iSub.

Fact norm_in `{arrow_flag} {Γ} {s t} : Γ |-N s <: t -> exists i, Γ |-IN i; s <: t.
Proof. induction 1. 1,3: exists 0. constructor. constructor. 
  -destruct IHsubN. exists (S x). now constructor.
  -destruct IHsubN1. destruct IHsubN2. exists (S (max x0 x)). now apply iArr.
  -destruct IHsubN1. destruct IHsubN2. exists (S (max x0 x)). now apply iAll.
Qed.

Fact in_norm `{arrow_flag} {Γ s t i} : Γ |-IN i; s <: t -> Γ |-N s <: t.
Proof. induction 1; now constructor. Qed.

Fact congr_IN `{arrow_flag} {i0 i1 Γ0 Γ1 s0 s1 t0 t1} : i0=i1 -> Γ0=Γ1 -> s0=s1 -> t0=t1 ->
   Γ0 |-IN i0; s0 <: t0 -> Γ1 |-IN i1; s1 <: t1.
Proof. congruence. Qed.

Fact in_load {Γ n p s i} {t : Vector.t type0 n} : Γ |-IN i; mkUnbounded n p <: mkBounded t s ->
  exists j, foldAdd t Γ |-IN j; s <: p /\ j<i.
Proof. revert i Γ. induction t; simpl; intros.
  -unfold neg in H. depind H; try discriminate.
   exists j. split. 2:apply le_lt_n_Sm,Nat.le_max_r.
   destruct (all_inj H1) as [-> _]. destruct (all_inj H2) as [-> _]. auto.
  -depind H; try discriminate. clear IHiSub1 IHiSub2.
   destruct (all_inj H1). destruct (all_inj H2).
   rewrite <- H4 in H0. rewrite <- H6 in H0. destruct (IHt _ _ H0) as [j' [Hj' Hji]].
   exists j'. split. now rewrite H5. apply (Nat.lt_trans _ i _ Hji),le_lt_n_Sm,Nat.le_max_l.
Qed.
(* end details *)

Lemma n2d {m} (Γ :@ctx w m) s t : mkCtx Γ |-N ntranslation s <: ptranslation t
  -> exists h, Γ |-D h; s <: t.
Proof. intro. destruct (norm_in H) as [n Hin]. clear H.
  revert m Γ s t Hin. induction n using Wf_nat.lt_wf_ind; intros.
  destruct t. eexists. constructor. destruct s.
  -simpl ntranslation in Hin. inversion Hin. apply DPI in H5. exfalso. apply (mkBnd_noTop H5).
   apply DPI in H5. exfalso. apply (mkBnd_noVar H5).
   assert (Hn : i<n). rewrite <- H3. auto. edestruct (H i Hn _ Γ (ctx_at Γ f f0) (bAllN t n0)).
   simpl. rewrite <- (DPI H0). rewrite <- (DPI H4). revert H5. apply congr_IN; auto.
   rewrite (DPI H0). now erewrite mkCtx_eq.
   exists (S x). now apply DVar.
  -simpl in *. destruct (in_load Hin) as [j [Hj Hji]]. edestruct (H j Hji).
   2: { exists (S x). apply DAllNeg. exact H0. } revert Hj. apply congr_IN; auto.
   simpl. rewrite map_app. eapply nth_ext.
   { rewrite length_foldAdd,app_length. repeat rewrite map_length. now rewrite rev_length,length_to_list. }
   rewrite length_foldAdd, length_mkCtx. intros. destruct (le_lt_dec w n1).
    +rewrite (foldAdd_ge l),app_nth2,map_length,rev_length,length_to_list. auto.
     rewrite map_length,rev_length,length_to_list. auto.
    +rewrite (foldAdd_lt l),app_nth1,nth_addShiftings,iterShiftAdd,map_rev,rev_nth.
     erewrite map_nth. assert (S n1 + (w - S n1 + 0)=w) as -> by lia.
     rewrite map_length,length_to_list. erewrite nth_indep. eauto.
     rewrite length_to_list. lia. now rewrite map_length,length_to_list. lia.
     now rewrite map_length,rev_length,length_to_list.
     Unshelve. exact top.
Qed.

End argument.


(** For w=0 the polarized syntax collapses, there are no variables and quantifiers bind nothing, therefore the translation are Top flipped any number of times.
The reduction is trivial. *)
Section argument0.

Lemma d2n0 {m} (Γ :@ctx 0 m) s t : (exists h, Γ |-D h; s<:t) ->
  mkCtx Γ |-N ntranslation s <: ptranslation t.
Proof. intros [h H]. induction H. constructor. contradiction. rewrite (isNil t1). unfold ptranslation. unfold ntranslation. simpl.
  apply flipNeg. revert IHsubD. simpl. change (fun t : fin => t) with (@id fin). asimpl. apply congr_NORM; auto.
  rewrite map_id. rewrite (isNil t1). now simpl.
Qed.

Lemma n2d0 {m} (Γ :@ctx 0 m) s t : mkCtx Γ |-N ntranslation s <: ptranslation t -> 
  (exists h, Γ |-D h; s<:t).
Proof. intro. destruct (norm_in H) as [i Hin]. clear H.
  revert m Γ s t Hin. induction i using Wf_nat.lt_wf_ind; intros.
  destruct t. eexists. constructor. destruct s. contradiction. revert Hin.
  unfold ntranslation. unfold ptranslation. rewrite (isNil t). simpl. unfold neg.
  intro. inversion Hin. edestruct (H j). rewrite <- H4. apply le_lt_n_Sm,Nat.le_max_r.
  2: { exists (S x). apply DAllNeg. exact H9. }
  revert H6. apply congr_IN. auto. simpl. asimpl. rewrite map_id. now rewrite (DPI H0).
  now rewrite (DPI H5). now rewrite (DPI H1).
Qed.

End argument0.


(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Definition translation : {w : fin & {m : fin & (@ctx w m * (@ntype w m * @ptype w m))%type}} ->
      (@FsubN.ctx arrow_off * (type0 * type0))%type.
Proof. intros [w [m [Γ [s t]]]]. split. exact (mkCtx Γ). split.
  exact (ntranslation s). exact (ptranslation t).
Defined.

Theorem reduction : FsubD_SUBTYPE ⪯  FsubN_off_SUBTYPE.
Proof.
  exists translation.
  unfold FsubN_SUBTYPE. intros [[|w] [m [Γ [s t]]]]; cbn.
  -split; [ apply d2n0 | apply n2d0].
  -split; [ apply d2n | apply n2d]; apply Nat.lt_0_succ.
Qed.
