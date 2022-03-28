(** * Undecidability of the subtyping problem of System FsubD *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import FsubF_undec FsubD.
Require Import Reductions.FsubF_to_FsubD.

Lemma FsubD_SUBTYPE_undec : undecidable FsubD_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility FsubF_SUBTYPE_undec).
  exact FsubF_to_FsubD.reduction.
Qed.