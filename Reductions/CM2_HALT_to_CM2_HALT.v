(** * Reduction from Counter Machines as defined in the Undecidability library to Counter Machines as defined by Pierce *)

(* begin details : Imports *)
From Undecidability.CounterMachines Require Import CM2.
From Undecidability.CounterMachines.Util Require Import CM2_facts.
From Undecidability.Shared.Libs.PSL Require Import Vectors.

Require Import CM2 Utils.CM2_facts Utils.uCM2_facts Utils.Various_utils.
Require Import Lia Arith Vectors.Vector Vectors.Fin Relations.
Import VectorNotations.
(* end details *)


(** ** Translation  *)

(** The translation of instructions depends on the position of the instruction in the program *)
Section argument.
Variable M : Cm2.
Definition w := length M.

Definition t_state (x : CounterMachines.CM2.State) : @State (S w) :=
  match le_lt_dec w x with
  | left _ => proj1_sig (lastF w)
  | right H => injS (nat2fin H)
  end.

Definition t_config (x : uConfig) : @CM2.Config (S w) := mkConfig (t_state (uState x)) (uV1 x) (uV2 x).

Definition translation_at (i : nat) (inst : uInst) : @Instruction (S w) := 
  match inst with
  | CounterMachines.CM2.inc b => inc b (t_state (S i))
  | CounterMachines.CM2.dec b s => dec b (t_state (S i)) (t_state s)
  end.

Definition translate_inst (i : fintype.fin w) : @Instruction (S w).
Proof. destruct (fin2nat i) as [x H]. apply translation_at. exact x. apply (lnth M x H). Defined.

Definition Mt : @CM2 (S w) := shiftin halt (tabulate' translate_inst).

Fact t_init : t_config (umkConfig 0 0 0) = mkConfig fintype.var_zero 0 0.
Proof. destruct M eqn:MH; unfold t_config; unfold t_state; unfold w; rewrite MH; now simpl.
Qed.

(** *** Characterization of the translated machine *)
Fact no_halt n i : translation_at n i <> halt.
Proof. unfold translation_at. destruct n; destruct i; intro; discriminate.
Qed.

Lemma Mt_at_some s i : List.nth_error M s = Some i -> nth' Mt (t_state s)=translation_at s i.
Proof. intros nthH. unfold t_state. destruct (le_lt_dec w s).
  -exfalso. apply List.nth_error_None in l. now rewrite nthH in l.
  -unfold Mt. rewrite nth'_shiftin. rewrite nth'_tabulate. unfold translate_inst.
   destruct (fin2nat (nat2fin l)) as [x H] eqn:f2nH. eapply (f_equal (@proj1_sig _ _)) in f2nH.
    rewrite f2n_n2f in f2nH. simpl in *. rewrite f2nH in nthH.
    assert (forall X l i (x:X) H, List.nth_error l i = Some x -> lnth l i H = x).
    { induction l0; simpl. intros. lia. intros. destruct i0; simpl in H1. now inversion H1. now apply IHl0. }
    rewrite (H0 _ _ _ _ _ nthH). now rewrite f2nH.
Qed.

Lemma Mt_at_none s : List.nth_error M s = None <-> nth' Mt (@t_state s)=halt.
Proof. unfold t_state. destruct (le_lt_dec w s).
  -destruct (lastF w). simpl. rewrite e. unfold Mt. rewrite shiftin_last.
   split; try auto. intro. now apply List.nth_error_None.
  -unfold Mt. rewrite nth'_shiftin. rewrite nth'_tabulate.
   split; intro; exfalso. apply List.nth_error_None in H. unfold w in l. lia.
    revert H. unfold translate_inst. destruct (fin2nat (nat2fin l)). apply no_halt.
Qed.

(** ** Reduction *)
Lemma halt x : uHalting M x <-> halting Mt (t_config x).
Proof. split; intro.
  -apply haltingP in H. apply halting_char. apply Mt_at_none. now apply List.nth_error_None.
  -apply halting_char in H. apply haltingP. apply List.nth_error_None. now apply Mt_at_none.
Qed.

Lemma step_fwd x y : uStep_to M x y -> step_to Mt (t_config x) (t_config y).
Proof. intros [st nh]. assert (uState x < w).
    { destruct (le_lt_dec w (uState x)). 2: lia. exfalso. apply haltingP in l. now rewrite l in st. }
  destruct (List.nth_error M (uState x)) eqn:nthH;
  unfold uStep in st; unfold CounterMachines.CM2.step in st; unfold uState in nthH; rewrite nthH in st.
  2: contradiction. unfold step_to. unfold step. simpl. unfold uState. rewrite (Mt_at_some nthH).
  destruct i eqn:iH; rewrite <- st; unfold t_config. auto.
  destruct b.
    +destruct (CounterMachines.CM2.value2 x) eqn:v2; unfold uV2; rewrite v2; now unfold t_config.
    +destruct (CounterMachines.CM2.value1 x) eqn:v1; unfold uV1; rewrite v1; now unfold t_config.
Qed.

Theorem forwards x y : M /// x |> y -> Mt // (t_config x) |> (t_config y).
Proof. intros [xy yH]. induction xy.
  -split. apply t1n_step. now apply step_fwd. now apply halt.
  -split. apply (Relation_Operators.t1n_trans _ _ _ (t_config y)). now apply step_fwd.
   apply (proj1 (IHxy yH)). now apply halt.
Qed.

Lemma step_bwd x y : step_to Mt (t_config x) y -> exists y', uStep_to M x y'.
Proof. unfold t_config. unfold step_to. unfold step. simpl.
  intro. unfold uStep. unfold CounterMachines.CM2.step.
  destruct (List.nth_error M (CounterMachines.CM2.state x)) eqn:nthH.
  2: { unfold uState in H. rewrite (proj1 (Mt_at_none _) nthH) in H. discriminate. }
  destruct i.
  -exists (umkConfig (S (uState x)) ((if b then 0 else 1) + uV1 x) ((if b then 1 else 0) + uV2 x)). split.
    unfold uStep. unfold CounterMachines.CM2.step. rewrite nthH. reflexivity.
    intro. apply (f_equal uState) in H0. simpl in H0. lia.
  -destruct b.
    +destruct (CounterMachines.CM2.value2 x) eqn:v2.
      *exists (umkConfig (S (uState x)) (uV1 x) 0). split.
       unfold uStep. unfold CounterMachines.CM2.step. rewrite nthH. rewrite v2. reflexivity.
       intro. apply (f_equal uState) in H0. simpl in H0. lia.
      *exists (umkConfig s (uV1 x) n). split.
       unfold uStep. unfold CounterMachines.CM2.step. rewrite nthH. rewrite v2. reflexivity.
       intro. apply (f_equal uV2) in H0. unfold uV2 in H0. simpl in H0. rewrite v2 in H0. lia.
    +destruct (CounterMachines.CM2.value1 x) eqn:v1.
      *exists (umkConfig (S (uState x)) 0 (uV2 x)). split.
       unfold uStep. unfold CounterMachines.CM2.step. rewrite nthH. rewrite v1. reflexivity.
       intro. apply (f_equal uState) in H0. simpl in H0. lia.
      *exists (umkConfig s n (uV2 x)). split.
       unfold uStep. unfold CounterMachines.CM2.step. rewrite nthH. rewrite v1. reflexivity.
       intro. apply (f_equal uV1) in H0. unfold uV1 in H0. simpl in H0. rewrite v1 in H0. lia.
Qed.

Theorem backwards x z n : stepind Mt (t_config x) z n -> halting Mt z -> exists y, M /// x |> y.
Proof. revert x.
  induction n as [n IH] using Wf_nat.lt_wf_ind.
  intros x st Hz.
   destruct (step Mt (t_config x)) eqn:stx.
  2: { exfalso. apply (step_not_halting _ _ _ _ st stx). }
  destruct (step_bwd stx) as [y xy]. pose (txy := step_fwd xy).
  assert (stepind Mt (t_config x) (t_config y) 1). { now apply step1. }
  destruct (compTrace _ _ _ _ _ _ st H Hz).
  2: { exists y. split. now apply t1n_step. apply halt. now rewrite <- H0. }
  assert (n>1). { lia. }
  assert (n-1<n). {lia. }
  pose (getTrace _ _ _ _ _ _ st H H1). destruct (IH (n-1) H2 y s Hz) as [z' [yz zH']].
  exists z'. split. now apply (Relation_Operators.t1n_trans _ _ _ y). apply zH'.
Qed.

Theorem fwd_bwd x : (exists y, M /// x |> y) <-> (exists y, Mt // (t_config x) |> y).
Proof. split.
  -intros [y yH]. exists (t_config y). now apply forwards.
  -intros [y [xy yH]]. destruct (toStepind _ _ _ xy) as [n st]. now apply (backwards st).
Qed.

End argument.



(** *** Synthetic reduction *)
Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : CounterMachines.CM2.CM2_HALT ⪯ CM2_HALT.
Proof.
  exists (fun M => existT _ (length M) (@Mt M)).
  intro M. unfold CounterMachines.CM2.CM2_HALT. unfold CM2_HALT.
  remember (CounterMachines.CM2.mkConfig 0 0 0) as x.
  split.
  -intros [n H]. unfold CounterMachines.CM2.halting in H.
   remember (Init.Nat.iter n (CounterMachines.CM2.step M) x) as y in H.
   symmetry in Heqy. simpl. rewrite <- t_init. destruct (iter_rel _ _ _ _ Heqy).
    +left. apply halt. unfold umkConfig. rewrite <- Heqx.
     unfold uHalting. unfold CounterMachines.CM2.halting. now rewrite H0.
    +right. apply fwd_bwd. exists y. split. unfold umkConfig. now rewrite <- Heqx. apply H.
  -simpl. intros [ H0 | [y [xy yH]] ]. exists 0. simpl. apply halt. rewrite <- t_init in H0. now rewrite Heqx.
   rewrite <- t_init in xy. destruct (toStepind _ _ _ xy) as [n st]. destruct (backwards st yH) as [y' xy'].
   apply (rHalt_halt _ _ y'). now rewrite Heqx.
Qed.
