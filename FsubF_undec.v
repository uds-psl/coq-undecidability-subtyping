(** * Undecidability of the subtyping problem of System FsubF *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import RM_undec FsubF.
Require Import Reductions.RM_HALT_to_FsubF.

Lemma FsubF_SUBTYPE_undec : undecidable FsubF_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility RM_HALT_undec).
  exact RM_HALT_to_FsubF.reduction.
Qed.