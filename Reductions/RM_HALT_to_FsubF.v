(** * Reduction from Rowing Machines to Flattened System Fsub *)

(* begin details : Imports *)
Require Import RM FsubF.
Require Import Utils.psyntax Utils.RM_facts Utils.Various_utils.
From Equations Require Import Equations.
Require Import Relations Vector Lia.
Import VectorNotations.
(* end details *)

(** ** Translation *)

Section argument.
Context {w : nat}.

Definition row2ntype {m} : @row (S w) m -> @ntype (S (S w)) m.
Proof. intros r. refine (row_rec (fun _ _ _ => _) _ _ _ _ m r).
  -intros m' i j. exact (var_ntype (shift i) j).
  -intros m' v H. apply uAllN. apply bAllN. apply cons. exact (var_ntype var_zero var_zero).
   apply (map H). exact (proj1_sig (mkvect' (S w))).
   apply (ren_ntype ↑), H, None.
  -intros. apply uAllN. exact top.
Defined.

Fact row2ntype_unfold {m} (ρ : @row (S w) m): row2ntype ρ = match ρ with
  | var_row i j => var_ntype (↑ i) j
  | abst t => uAllN (bAllN (var_ntype var_zero var_zero :: map row2ntype t) (ren_ntype ↑ (row2ntype (nth' t None))))
  | halt => uAllN top
end.
Proof. destruct ρ; unfold row2ntype; rewrite row_rec_unfold; auto.
  apply congr_uAllN,congr_bAllN; auto.
  apply congr_cons. auto. destruct (mkvect' (S w)). simpl. apply ext_nth'.
  intro. repeat rewrite nth'_map. now rewrite e.
Qed.

Opaque row2ntype.

Definition sigma (n : nat) : @ntype (S n) 0  := uAllN (
  bAllN (map (fun i => var_ntype i var_zero) (proj1_sig (mkvect' (S n)))) (var_ntype var_zero (↑ var_zero))).

Definition RM2type  (R : @RM w) : ptype 0 := caseS' R (fun _ => ptype _)
   (fun h _ => bAllN (sigma (S w) :: map row2ntype R) (ren_ntype ↑ (row2ntype h))).

(* begin details : Utilities for the translation *)

Fact subst_sigma n σ: subst_ntype σ (sigma n) = sigma n.
Proof. now apply idSubst_ntype. Qed.


Fact ninst_up {w' n} v t : @ninst w' n v (ren_ntype ↑ t) = t.
Proof. unfold ninst. rewrite (compRenSubst_ntype _ _ (fun i => var_ntype i)). now apply idSubst_ntype. auto.
Qed.

Fact pinst_sigma : forall (t1 : @ntype (S (S w)) 0) t,
  pinst (t1::t) (bAllN (map (fun i => var_ntype i var_zero) (proj1_sig (mkvect' (S (S w))))) (var_ntype var_zero (↑ var_zero)))
  = bAllN (t1::t) (ren_ntype ↑ t1).
Proof. intros. destruct (mkvect' (S (S w))). simpl. unfold pinst. asimpl.
  rewrite map_map. apply congr_bAllN.
  -apply ext_nth'. intro. rewrite nth'_map. rewrite e. now simpl.
  -now apply extRen_ntype.
Qed.

Fact congr_F : forall n (s : @ntype (S n) 0) t1 t2 h, t1=t2-> |-F h; s <: t1 -> |-F h; s <: t2.
Proof. congruence. Qed.

Fact congr_up : (forall w n (s t : @ntype w n), s=t -> ren_ntype ↑ s = ren_ntype ↑ t).
Proof. congruence. Qed.

Fixpoint upSigma {m} : @ntype (S (S w)) m.
Proof. destruct m. apply sigma. apply (ren_ntype ↑),upSigma.
Defined.

Fact subst_up : (forall w n (σ : fin w -> fin (S n) -> ntype n) t, subst_ntype (up_ntype_ntype σ) (ren_ntype ↑ t) = ren_ntype ↑ (subst_ntype σ t)).
Proof. intros. erewrite (compRenSubst_ntype _ _ (fun i j => ren_ntype ↑ (σ i j))). 2: auto.
  erewrite (compSubstRen_ntype _ _ (fun i j => ren_ntype ↑ (σ i j))); auto.
Qed.

Fixpoint upSubstRow {m} (σ : fin (S w) -> fin 1 -> @row (S w) 0) {struct m} : fin (S w) -> fin (S m) -> @row (S w) m.
Proof. destruct m. exact σ. apply up_row_row,upSubstRow,σ. Defined.

Fixpoint upSubstNType {m} (σ : fin (S (S w)) -> fin 1 -> @ntype (S (S w)) 0) {struct m} : fin (S (S w)) -> fin (S m) -> @ntype (S (S w)) m.
Proof. destruct m. exact σ. apply up_ntype_ntype,upSubstNType,σ. Defined.

Fact row_rec_Swm (P : forall m, @row (S w) m -> Type)
  (Hv: forall m i j, P m (var_row i j))
  (Ha: forall m v, (forall i, P (S m) (nth' v i)) -> P m (abst v) )
  (Ht: forall m, P m halt) : forall m r, P m r.
Proof. assert (Hsize : forall (P : forall m, @row (S w) m -> Type) m, (forall m x, (forall m y, size y < size x -> P m y) -> P m x)-> forall x, P m x).
  { intros. apply X. induction (size x); intros. lia. destruct (lt_S _ _ H). apply X. rewrite e. apply IHn. apply IHn,l. }
  intros. eapply Hsize. destruct x. 1,3: auto. intros. apply Ha. intro. apply X,inSize,In_nth'.
Qed.

Fact trans_ren {m n} (r : @row (S w) m) (s : fin m -> fin n) : row2ntype (ren_row s r) = ren_ntype s (row2ntype r).
Proof. revert n s. revert m r. refine (row_rec_Swm _ _ _ _); intros; repeat rewrite row2ntype_unfold. 1,3: auto.
  apply congr_uAllN,congr_bAllN.
  - simpl. apply congr_cons. auto. repeat rewrite map_map. apply ext_nth'.
    intro. repeat rewrite nth'_map. now rewrite (H i (S n) _).
  - rewrite nth'_map. rewrite <- row2ntype_unfold.
    rewrite (H None (S n) _). erewrite compRenRen_ntype. 2: eauto. fold (@ren_ntype (S (S w))). 
    erewrite compRenRen_ntype. 2:eauto. apply extRen_ntype. unfold funcomp.
    destruct x; simpl; unfold funcomp; simpl; unfold funcomp; auto.
Qed.

Fact row_rec_SwSm (P : forall m, @row (S w) (S m) -> Type)
  (Hv: forall m i j, P m (var_row i j))
  (Ha: forall m v, (forall i, P (S m) (nth' v i)) -> P m (abst v) )
  (Ht: forall m, P m halt) : forall m r, P m r.
Proof. assert (Hsize : forall (P : forall m, @row (S w) (S m) -> Type) m, (forall m x, (forall m y, size y < size x -> P m y) -> P m x)-> forall x, P m x).
  { intros. apply X. induction (size x); intros. lia. destruct (lt_S _ _ H). apply X. rewrite e. apply IHn. apply IHn,l. }
  intros. eapply Hsize. destruct x. 1,3: auto. intros. apply Ha. intro. apply X,inSize,In_nth'.
Qed.

Fact trans_subst {m} (R : Vector.t (@row (S w) 0) (S w)) (r : @row (S w) (S m)) : row2ntype (subst_row (upSubstRow (fun i => nth' R i .; (fun j : fin 0 => False_rect _ j))) r) = subst_ntype (upSubstNType (fun i => nth' (sigma (S w) :: map row2ntype R) i .; var_ntype i)) (row2ntype r).
Proof. revert R. revert r. revert m. refine (row_rec_SwSm _ _ _ _ ); intros.
  -unfold subst_row. symmetry. rewrite row2ntype_unfold. asimpl. induction m.
    destruct j. contradiction. simpl. now rewrite nth'_map. destruct j. 2: auto. simpl. unfold funcomp.
    rewrite trans_ren. simpl in IHm. now rewrite (IHm f).
  -simpl. repeat rewrite row2ntype_unfold. apply congr_uAllN,congr_bAllN.
    +simpl. apply congr_cons. auto. repeat rewrite map_map. apply ext_nth'. intro. repeat rewrite nth'_map.
      pose (H i R). simpl in e. now rewrite e.
    +rewrite nth'_map. repeat rewrite <- row2ntype_unfold. fold (@subst_ntype (S (S w))).
      pose (H None). simpl in e. rewrite e. now rewrite subst_up.
  -now repeat rewrite row2ntype_unfold.
Qed.

Fixpoint trans_subst' ρ ρ' ρ1' i : row2ntype (subst_row (fun i0 : fin (S w) => match i0 with
    | Some f => nth' ρ f
    | None => abst (ρ1' :: ρ')
    end .; (fun j : fin 0 => False_rect (row 0) j)) match i with Some f => nth' ρ' f | None => ρ1' end) =
subst_ntype (fun i0 : fin (S (S w)) => match i0 with 
   | Some (Some f0) => nth' (map row2ntype ρ) f0
   | Some None => row2ntype (abst (ρ1' :: ρ'))
   | None => sigma (S w)
   end .; var_ntype i0) (row2ntype match i with | Some f => nth' ρ' f | None => ρ1' end).
Proof.
  pose (@trans_subst 0 ((abst (ρ1'::ρ'))::ρ)  (nth' (ρ1' :: ρ') i)). now simpl in *.
Qed.

Fact congr_in : forall w (s1 : @ntype w 0 ) t1 s2 t2 h,  s1=s2 -> t1=t2 -> |-F h; s1 <: t1 -> |-F h; s2 <: t2.
Proof. congruence. Qed.

Fact map_mkVect ρ ρ1 : ((VectorDef.map (fun x : (fin (S (S w))) => (match x with
       | Some (Some f0) => nth' (map row2ntype ρ) f0
       | Some None => row2ntype ρ1
       | None => sigma (S w)
       end .; var_ntype x) var_zero) (proj1_sig (mkvect' (S (S w))))) = sigma (S w) :: map row2ntype (ρ1 :: ρ)).
Proof. destruct (mkvect' (S (S w))). simpl. apply ext_nth'. intro. rewrite nth'_map. now rewrite e. Qed.

Fact ext_cons : forall A B (f:A->B) n h (tl : Vector.t A n), map f (h::tl) = (f h) :: (map f tl).
Proof. auto. Qed.
(* end details *)
(** ** Reduction *)

Derive Signature for subF.
Lemma step2flat {R R' : @RM w} h : step_to R R' -> 
  |-F h; sigma (S w) <: RM2type R' <-> |-F S (S h); sigma (S w) <: RM2type R.
Proof.
  unfold step_to. unfold RM.step. destruct (hd R) eqn:rH. contradiction. 2: discriminate.
  inversion 1. clear H H1. unfold RM2type.
  apply (caseSEq t). intros ρ1' ρ' Ht. simpl. apply (caseSEq R). intros ρ1 ρ HR. simpl. split.
  -intro.  apply FAllNeg. rewrite ninst_up. rewrite pinst_sigma.
    rewrite HR in rH. simpl in rH. rewrite rH at 1. rewrite row2ntype_unfold. apply FAllNeg.
    rewrite ninst_up. rewrite Ht at 2. simpl. unfold pinst. 
    revert H. repeat rewrite <- ext_cons. rewrite <- HR. apply congr_in. auto. apply congr_bAllN.
    + simpl. apply congr_cons. auto. repeat rewrite <- ext_cons. rewrite <- Ht. repeat rewrite map_map.
      apply ext_nth'. intro. repeat rewrite nth'_map. rewrite HR. rewrite rH. rewrite Ht.
      pose (trans_subst' ρ ρ' ρ1' i). now simpl in *.
    + simpl. rewrite (subst_up (S (S w)) 0). apply congr_up. rewrite HR.
      assert (ρ1' = nth' t None). now rewrite Ht. rewrite H. rewrite rH. rewrite Ht.
      pose (trans_subst' ρ ρ' ρ1' None). now simpl in *.
  -intro H. rewrite <- ext_cons in H. rewrite <- HR in *. depind H. clear IHsubF.
   inversion H1. rewrite <- H4 in H. rewrite ninst_up in H. unfold pinst in H. simpl in rH.
   rewrite rH in H at 1. rewrite row2ntype_unfold in H. remember (ρ1' :: ρ').
   rewrite <- H3 in H. rewrite <- ext_cons in H. (* remember (ρ1 ::ρ) as R. *)
   asimpl in H. inversion H0. rewrite <- H5 in H. inversion H. revert H8. rewrite map_map. apply congr_in.
    + unfold ninst. asimpl. apply subst_sigma.
    + repeat rewrite <- ext_cons. remember (ρ1' :: ρ'). remember (abst t :: ρ) as R.
      rewrite map_mkVect. apply congr_bAllN.
      ++ simpl. apply congr_cons. auto. repeat rewrite map_map. apply ext_nth'. intro. repeat rewrite nth'_map.
         rewrite rH. rewrite Heqt. rewrite Heqt4. pose (trans_subst' ρ ρ' ρ1' i0). now simpl in *.
      ++assert (ρ1' = nth' t None). rewrite Heqt. now rewrite Heqt4. rewrite H8. rewrite Heqt. rewrite Heqt4.
        remember None. simpl. change (option (fin w)) with (fin (S w)). rewrite rH. rewrite Heqt. rewrite Heqt4.
        erewrite  (trans_subst'). now erewrite <- subst_up.
Qed.

Lemma halt2flat (R : @RM w) : halting R -> |-F 2; sigma (S w) <: RM2type R.
Proof. unfold halting. unfold RM.step. destruct (hd R) eqn:rH. contradiction. discriminate. intros _.
  apply (caseSEq R). intros. rewrite H in rH. simpl in *. rewrite rH. simpl. apply FAllNeg,FAllNeg,FTop.
Qed.

Lemma flat2RM_HALT (R : @RM w) : (exists h, |-F h; sigma (S w) <: RM2type R) -> 
  @halting w R \/ (exists s : @RM w, R ~|> s).
Proof. intros [n H]. revert H. revert R. induction n using Wf_nat.lt_wf_ind.
  intro. apply (caseSEq R). intros ρ ρs HR Hin. destruct n. inversion Hin.
  destruct n. inversion Hin. inversion H3. destruct ρ. contradiction. 2: now left.
  apply (caseSEq t). intros ρ' ρs' Ht. assert (Hn: n<S(S n)). auto.
  edestruct (H n Hn (map (subst_row (fun i => nth' R i .; fun j:fin 0 => False_rect _ j))  t)).
  -assert (Hstep : step_to R (map (subst_row (fun i => nth' R i .; fun j:fin 0 => False_rect _ j))  t)).
   { unfold step_to. unfold RM.step. now rewrite HR. }
   destruct (step2flat n Hstep). apply H1. now rewrite HR.
  -right. exists (map (subst_row (fun i => nth' R i .; fun j:fin 0 => False_rect _ j)) t). split. 2: auto.
   constructor. unfold step_to. unfold RM.step. rewrite HR. now rewrite Ht.
  -right. destruct H0 as [S HS]. destruct HS. exists S. split. 2: auto.
   apply (Relation_Operators.t1n_trans _ _ _ (map (subst_row (fun i => nth' R i .; fun j:fin 0 => False_rect _ j)) t)).
   2: auto. unfold step_to. unfold RM.step. rewrite HR. now rewrite Ht.
Qed.

End argument.

(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : RM_HALT ⪯  FsubF_SUBTYPE.
Proof. exists (fun wR : {w & @RM w} => let (w, R) := wR in
  existT (fun n => (@ntype n 0 * @ptype n 0)%type) (S (S w)) (sigma (S w), @RM2type w R)).
  intro wR. destruct wR as [w R]. unfold RM_HALT. simpl. split.
  -destruct 1. exists 2. now apply halt2flat. destruct H as [R' [HR HR']].
   induction HR. exists 4. apply (step2flat _ H). now apply halt2flat.
   destruct (IHHR HR') as [h H']. exists (S (S h)). now apply (step2flat _ H).
  -apply flat2RM_HALT.
Qed.
