(** * Undecidability of the halting problem of 2 Counter Machines a la Pierce *)

Require Import Undecidability.Synthetic.Undecidability.

From Undecidability.CounterMachines
  Require Import CM2 CM2_undec.

Require Import CM2 Reductions.CM2_HALT_to_CM2_HALT.

Lemma CM2_HALT_undec : undecidable CM2_HALT.
Proof.
  apply (undecidability_from_reducibility CM2_HALT_undec).
  exact CM2_HALT_to_CM2_HALT.reduction.
Qed.