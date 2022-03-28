(** * Undecidability of the subtyping problem of System Fsub without arrow types *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Fsub_na FsubN FsubN_undec FsubD FsubF RM CM2.
Require Import Reductions.FsubN_to_Fsub.
Require Import Reductions.FsubD_to_FsubN.
Require Import Reductions.FsubF_to_FsubD.
Require Import Reductions.RM_HALT_to_FsubF.
Require Import Reductions.CM2_Halt_to_RM_Halt.
Require Import Reductions.CM2_HALT_to_CM2_HALT.

From Undecidability.CounterMachines
  Require Import CM2 CM2_undec.

Theorem Fsub'_SUBTYPE_undec : undecidable Fsub'_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility CM2_HALT_undec).
  eapply reduces_transitive. exact CM2_HALT_to_CM2_HALT.reduction.
  eapply reduces_transitive. exact CM2_Halt_to_RM_Halt.reduction.
  eapply reduces_transitive. exact RM_HALT_to_FsubF.reduction.
  eapply reduces_transitive. exact FsubF_to_FsubD.reduction.
  eapply reduces_transitive. exact FsubD_to_FsubN.reduction.
  exact FsubN_to_Fsub.reduction_off.
Qed.

Check Fsub'_SUBTYPE_undec.