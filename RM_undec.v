(** * Undecidability of the halting problem of Rowing Machines *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import RM CM2_undec.
Require Import Reductions.CM2_Halt_to_RM_Halt.

Lemma RM_HALT_undec : undecidable RM_HALT.
Proof.
  apply (undecidability_from_reducibility CM2_HALT_undec).
  exact CM2_Halt_to_RM_Halt.reduction.
Qed.