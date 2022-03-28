(** * (Flattened) System Fsub definition and subtyping problem *)

Require Import Utils.psyntax.

Reserved Notation "|-F i ; s <: t" (at level 68, i, s, t at next level).

Inductive subF {w} : nat -> @ntype w 0 -> @ptype w 0 -> Prop :=
  | FTop s : |-F 0; s <: top
  | FAllNeg s t1 t2 i : |-F i; ninst t1 t2  <: pinst t1 s  ->
      |-F S i; uAllN s <: bAllN t1 t2
  where "|-F i ; A <: B" := (subF i A B).

Definition FsubF_SUBTYPE : {w : nat & ( @ntype w 0 * @ptype w 0 )%type} -> Prop
  := fun ntt => let (w, s0) := ntt in let (s, t) := s0
    in exists h, |-F h; s <: t.