(** * Undecidability of the subtyping and typechecking problems of System FsubN *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import FsubD_undec FsubN.
Require Import Reductions.FsubD_to_FsubN Reductions.FsubN_to_FsubNchk.

Lemma FsubN_off_SUBTYPE_undec : undecidable FsubN_off_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility FsubD_SUBTYPE_undec).
  exact FsubD_to_FsubN.reduction.
Qed.

Lemma FsubN_on_SUBTYPE_undec : undecidable FsubN_on_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility FsubN_off_SUBTYPE_undec).
  eapply reduces_transitive. exact reduction_off2gen. exact reduction_gen2on.
Qed.

Theorem FsubN_TYPECHK_undec : undecidable FsubN_TYPECHK.
Proof. 
  apply (undecidability_from_reducibility FsubN_on_SUBTYPE_undec).
  exact FsubN_to_FsubNchk.reduction.
Qed.

