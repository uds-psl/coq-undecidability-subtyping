(** * Undecidability of the subtyping and typechecking problems of System Fsub *)

Require Import Undecidability.Synthetic.Undecidability.

Require Import Fsub FsubN_undec.
Require Import FsubNchk_to_Fsubchk.


Theorem Fsub_SUBTYPE_undec : undecidable Fsub_SUBTYPE.
Proof.
  apply (undecidability_from_reducibility FsubN_on_SUBTYPE_undec).
  exact FsubN_to_Fsub.reduction_on.
Qed.

Theorem Fsub_TYPECHK_undec : undecidable Fsub_TYPECHK.
Proof.
  apply (undecidability_from_reducibility FsubN_TYPECHK_undec).
  exact FsubNchk_to_Fsubchk.reduction.
Qed.

Check Fsub_SUBTYPE_undec.
Check Fsub_TYPECHK_undec.
Print Assumptions Fsub_TYPECHK_undec.