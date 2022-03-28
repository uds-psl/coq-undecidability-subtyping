(** * Reduction from Counter Machines to Rowing Machines *)
(* begin details : Imports *)
Require Import CM2 RM Utils.CM2_facts Utils.RM_facts Utils.Various_utils.
Require Import Lia Vectors.Vector Vectors.Fin Relations.
Import VectorNotations.
(* end details *)
(** ** Translation *)
Section argument.
Context {w : nat}.

(* begin details : Basic definitions for the translation *)

Definition rid {n} : Vector.t (@row (5+w) (S n)) (5+w) := map (fun i => var_row i var_zero) (proj1_sig (mkvect' (5+w))).
Lemma rId i {n} : nth' (@rid n) i = var_row i var_zero.
Proof. unfold rid. rewrite (nth'_map); auto. destruct (mkvect' (5+w)). simpl. now rewrite e. Qed.

Fixpoint R' {m} n (p : fin m) {struct n} : fin (n + m).
Proof. destruct n; simpl. exact p. apply Some,R',p. Defined.

Fact tl_nth' {n A} {v : Vector.t A (S n)} {f : fin n} : nth' v (Some f) = nth' (tl v) f.
Proof. now apply (Vector.caseS' v). Qed.

Fact hd_nth' {n A} {v : Vector.t A (S n)} : hd v = nth' v None.
Proof. now apply (Vector.caseS' v). Qed.

Definition tail {n} := tl (tl (tl (tl (tl (@rid n))))).
Lemma tailP (i : fin w) {n} : nth' (@tail n) i = nth' rid (R' 5 i).
Proof. unfold R'. unfold tail. now repeat rewrite <- tl_nth'. Qed.

Definition mkrow {n} (r0 r1 r2 r3 r4 : @row (5+w) (S n)) : @row (5+w) n := abst (r0::r1::r2::r3::r4::tail).

Lemma subst_tail {n} (σ: fin (5+w) -> fin (S n) -> row n) t : (forall j, σ (↑(↑(↑(↑(↑ j))))) var_zero=nth' t j) -> map (subst_row σ) tail = t.
Proof. intro. apply ext_nth'. intro. rewrite nth'_map. rewrite tailP. rewrite rId. apply (H i).
Qed.

Lemma substS_tail {σ : fin (5+w) -> fin 1 -> row 1 } : map (subst_row (up_row_row σ)) tail = tail.
Proof. apply ext_nth'. intro. rewrite nth'_map. rewrite tailP. now rewrite rId. Qed.

Fixpoint encode_A n := match n with
  | 0 => mkrow (@var_row (5+w) 1 (Some (Some (Some None))) None) (@var_row (5+w) 1 (Some None) None) (@var_row (5+w) 1 (Some (Some None)) None) halt halt
  | S n => mkrow (@var_row (5+w) 1 (Some (Some (Some (Some None)))) None) (ren_row shift (encode_A n)) (@var_row (5+w) 1 (Some (Some None)) None) halt halt
  end.

Fixpoint encode_B n := match n with
  | 0 => mkrow (@var_row (5+w) 1 (Some (Some (Some None))) None) (@var_row (5+w) 1 (Some None) None) (@var_row (5+w) 1 (Some (Some None)) None) halt halt
  | S n => mkrow (@var_row (5+w) 1 (Some (Some (Some (Some None)))) None) (@var_row (5+w) 1 (Some None) None) (ren_row shift (encode_B n)) halt halt
  end.

Lemma subst_encode_A σ n : subst_row σ (encode_A n) = encode_A n.
Proof. now apply idSubst_row. Qed.

Lemma subst_encode_B σ n : subst_row σ (encode_B n) = encode_B n.
Proof. now apply idSubst_row. Qed.

Definition var_one {n} := shift (@var_zero n).
Definition var_two {n} := shift (@var_one n).
Definition var_three {n} := shift (@var_two n).
Definition var_four {n} := shift (@var_three n).

Definition t1n_trans := Relation_Operators.t1n_trans.

Fact congr_some {X} {x1 x2 : X} : x1=x2 -> Some x1 = Some x2.
Proof. congruence. Qed.

(* end details *)

Definition translate_inst (i : @Instruction w) : @row (5+w) 0.
Proof. destruct i eqn:iH. 1,2: destruct b.
  -eapply (mkrow (var_row (R' 5 s) var_zero) (var_row var_one var_zero) _ halt halt). Unshelve.
   eapply (mkrow (var_row var_four var_zero) (var_row var_one var_zero) (var_row var_two var_one) halt halt).
  -eapply (mkrow (var_row (R' 5 s) var_zero) _ (var_row var_two var_zero) halt halt). Unshelve.
   eapply (mkrow (var_row var_four var_zero) (var_row var_one var_one) (var_row var_two var_zero) halt halt).
  -eapply (mkrow (var_row var_two var_zero) (var_row var_one var_zero) (var_row var_two var_zero) (var_row (R' 5 s) var_zero) (var_row (R' 5 s0) var_zero)).
  -eapply (mkrow (var_row var_one var_zero) (var_row var_one var_zero) (var_row var_two var_zero) (var_row (R' 5 s) var_zero) (var_row (R' 5 s0) var_zero)).
  -exact halt.
Defined.
Definition translation (M : CM2) (x : Config) : RM :=
  [ translate_inst (nth' M (state x)) ; encode_A (value1 x); encode_B (value2 x); halt; halt ] ++ map translate_inst M.

(** ** Reduction *)
Lemma step_fwd M x y : CM2.step_to M x y -> (translation M x) ~~> (translation M y).
Proof. unfold CM2.step_to. unfold CM2.step.
  destruct (nth' M (state x)) eqn:nthH; intro; inversion H. clear H H1.
  -apply t1n_step. unfold step_to. unfold step. cbn. rewrite nthH.
   destruct b; simpl.
    + apply congr_some,congr_cons. now rewrite nth'_map. apply congr_cons. auto.
      unfold mkrow. apply congr_cons. apply congr_abst. repeat apply congr_cons; auto.
      apply ext_nth'. intro. rewrite nth'_map. repeat rewrite tailP. now repeat rewrite rId.
      repeat apply congr_cons; auto. apply subst_tail. now intro.
    + apply congr_some,congr_cons. now rewrite nth'_map. apply congr_cons. unfold mkrow.
      apply congr_abst. repeat apply congr_cons; auto.
      apply ext_nth'. intro. rewrite nth'_map. repeat rewrite tailP. now repeat rewrite rId.
      repeat apply congr_cons; auto. apply subst_tail. now intro.
  -destruct b.
    +destruct (value2 x) eqn:vH; unfold translation; rewrite nthH; simpl; unfold step_to; unfold step; simpl.
      ++eapply t1n_trans. simpl. reflexivity.
        apply t1n_step. rewrite vH. simpl. apply congr_some,congr_cons. now rewrite nth'_map.
        repeat apply congr_cons; auto. apply subst_tail. intro. cbn. repeat rewrite nth'_map.
        rewrite tailP. rewrite rId. simpl. now rewrite nth'_map.
      ++eapply t1n_trans. simpl. reflexivity.
        apply t1n_step. rewrite vH. simpl. apply congr_some,congr_cons. now rewrite nth'_map.
        repeat apply congr_cons; auto. erewrite compRenSubst_row. now apply idSubst_row. contradiction.
        apply subst_tail. intro. cbn. repeat rewrite nth'_map. rewrite tailP. rewrite rId. simpl. now rewrite nth'_map.
    +destruct (value1 x) eqn:vH; unfold translation; rewrite nthH; simpl; unfold step_to; unfold step; simpl.
      ++eapply t1n_trans. simpl. reflexivity.
        apply t1n_step. rewrite vH. simpl. apply congr_some,congr_cons. now rewrite nth'_map.
        repeat apply congr_cons; auto. apply subst_tail. intro. cbn. repeat rewrite nth'_map.
        rewrite tailP. rewrite rId. simpl. now rewrite nth'_map.
      ++eapply t1n_trans. simpl. reflexivity.
        apply t1n_step. rewrite vH. simpl. apply congr_some,congr_cons. now rewrite nth'_map.
        repeat apply congr_cons; auto. erewrite compRenSubst_row. now apply idSubst_row. contradiction.
        apply subst_tail. intro. cbn. repeat rewrite nth'_map.
        rewrite tailP. rewrite rId. simpl. now rewrite nth'_map.
Qed.

Lemma halt M x : CM2.halting M x <-> RM.halting (translation M x).
Proof. unfold translation. split; intro.
  -apply CM2_facts.halting_char in H. apply RM_facts.halting_char. simpl. now rewrite H.
  -apply RM_facts.halting_char in H. simpl in H. unfold translate_inst in H.
   destruct (nth' M (state x)) eqn:nH; unfold mkrow in H.
   1,2 : destruct b; exfalso; discriminate.
   now apply CM2_facts.halting_char.
Qed.

Theorem forwards M x :  (exists y, M // x |> y) -> (exists r, (translation M x) ~|> r).
Proof. intros [y [rn H]]. exists (translation M y). induction rn.
    +split. now apply step_fwd. now apply halt.
    +destruct (IHrn H). split. 2: now apply halt.
     apply clos_trans_t1n.
     eapply t_trans; apply clos_t1n_trans.
     apply step_fwd. now instantiate (1:=y). assumption.
Qed.

Lemma step_bwd M x r : RM.step_to (translation M x) r -> exists y, CM2.step_to M x y.
Proof. unfold step_to. unfold step.
  destruct (nth' M (state x)) eqn:nthH; unfold translation; rewrite nthH; simpl; intro; [clear H | clear H | ].
  -exists (mkConfig s ((if b then 0 else 1)+(value1 x)) ((if b then 1 else 0)+(value2 x))).
   unfold CM2.step_to. unfold CM2.step. now rewrite nthH.
  -destruct b.
    +destruct (value2 x) eqn:vH;
     [exists (mkConfig s (value1 x) 0) | exists (mkConfig s0 (value1 x) n)];
     unfold CM2.step_to; unfold CM2.step; rewrite nthH; now rewrite vH.
    +destruct (value1 x) eqn:vH;
     [exists (mkConfig s 0 (value2 x)) | exists (mkConfig s0 n (value2 x))];
     unfold CM2.step_to; unfold CM2.step; rewrite nthH; now rewrite vH.
  -exfalso. discriminate.
Qed.

Theorem backwards M x r n : stepind (translation M x) r n -> RM.halting r -> (exists y, M // x |> y).
Proof.
  revert x.
  induction n as [n IH] using Wf_nat.lt_wf_ind.
  intros x st rH.
  destruct (step (translation M x)) eqn:stx.
    2: { exfalso. destruct st as [r0 s0 H |r0 s0 r n H ]; unfold step_to in H; rewrite H in stx; discriminate. }
  destruct (step_bwd _ _ _ stx) as [y xy].
  destruct (toStepind _ _ (step_fwd _ _ _ xy)) as [m txty].
  destruct (compTrace _ _ _ _ _ st txty rH) as [ mn | ].
    2: { exists y. split. now apply t1n_step. apply halt. now rewrite <- H. }
  assert (nm : n-m<n). { pose (non0step _ _ _ txty). lia. }
  destruct (IH (n-m) nm y (getTrace _ _ _ _ _ st txty mn) rH) as [y' [yy' Hy]].
  exists y'. split; try auto.
  now apply (t1n_trans _ _ _ y).
Qed.

Theorem fwd_bwd M x : (exists y, M// x |> y) <-> (exists r, (translation M x) ~|> r).
Proof. split.
  -now apply forwards.
  -intros [r [rs rH]]. destruct (toStepind _ _ rs) as [n ns]. now apply (backwards _ _ r n).
Qed.

End argument.

(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : CM2_HALT ⪯  RM_HALT.
Proof.
 exists (fun M' => match M' with existT _ w M => existT _ (5+w) (translation M {| state := var_zero; value1 := 0; value2 := 0 |}) end).
  intros [w M]. split.
  -intros [ Hy | H ]. left. now apply halt. right. now apply fwd_bwd.
  -intros [ Hr | H ]. left. now apply halt. right. now apply fwd_bwd.
Qed.
