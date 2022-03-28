(** * General facts of Counter Machines as defined in the Undecidability library *)
From Undecidability.CounterMachines Require Import CM2 Util.CM2_facts.
Require Import Arith Lia Relations.

Definition uInst := Instruction.
Definition uConfig := Config.
Definition umkConfig := mkConfig.
Definition uState := state.
Definition uV1 := value1.
Definition uV2 := value2.
Definition uStep := step.
Definition uHalting := halting.

Definition uStep_to M x y : Prop := step M x = y /\ x<>y.

Notation "M /// x ~> y " := (clos_trans_1n _ (uStep_to M) x y) (at level 70, no associativity).
Notation "M /// x |> y " := (M///x~>y /\ halting M y) (at level 70, no associativity).

Fixpoint halt_forever M x n : halting M x -> Nat.iter n (step M) x = x.
Proof. intro. destruct n; simpl; try auto. rewrite (halt_forever M x n H). assumption.
Defined.

Fact no_halt M x n m : m<n -> ~halting M (Nat.iter n (step M) x) -> ~halting M (Nat.iter m (step M) x).
Proof. intros. intro. apply H0. apply (halting_monotone m n). lia. assumption. Qed.

Fact eq_config_dec (x y : Config) : {x=y} + {x<>y}.
Proof. destruct x. destruct y.
  destruct (eq_nat_dec state state0).
    -destruct (eq_nat_dec value1 value0).
      +destruct (eq_nat_dec value2 value3). left. rewrite e. rewrite e0. rewrite e1. reflexivity.
        right. intro. apply (f_equal uV2) in H. simpl in H. contradiction.
      +right. intro. apply (f_equal uV1) in H. simpl in H. contradiction.
    -right. intro. apply (f_equal uState) in H. simpl in H. contradiction.
Qed.

Fact halt_dec M x : {halting M x} + {~halting M x}.
Proof. destruct (eq_config_dec (step M x) x). now left. now right.
Qed.

Definition tn1_trans := Relation_Operators.tn1_trans.

Fixpoint iter_rel M n x y : Nat.iter n (step M) x = y -> x=y \/  M /// x ~> y.
Proof. destruct n; simpl. tauto.
intros H. remember (Nat.iter n (step M) x) as z in H. symmetry in Heqz. destruct (eq_config_dec z y).
  -rewrite <- e. now apply (iter_rel M n x z).
  -destruct (iter_rel M n x z Heqz); right.
   rewrite H0. apply t1n_step. now split.
   apply clos_trans_t1n, clos_tn1_trans.
   apply (tn1_trans _ _ _ z). now split.
   now apply clos_trans_tn1,clos_t1n_trans.
Defined.

Fixpoint iter_S M x n : Nat.iter (S n) (step M) x = Nat.iter n (step M) (step M x).
Proof. destruct n; simpl. auto. rewrite <- (iter_S M x n). auto.
Defined.

Fact rHalt_halt M x y : M /// x |> y -> exists n, halting M (Nat.iter n (step M) x).
Proof. destruct 1 as [xy yH]. induction xy.
  -exists 1. destruct H. simpl. now rewrite H.
  -destruct (IHxy yH) as [n nH].
   exists (S n). rewrite iter_S. now rewrite (proj1 H).
Defined.

(** ** Synthetic Undecidability *)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines
  Require Import CM2 Reductions.MM2_HALTING_to_CM2_HALT.

From Undecidability.MinskyMachines
  Require Import MM2 MM2_undec.

Lemma CM2_HALT_undec : undecidable CM2_HALT.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exact MM2_HALTING_to_CM2_HALT.reduction.
Qed.