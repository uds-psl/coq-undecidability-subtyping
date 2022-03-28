(** * (Deterministic) System Fsub definition and subtyping problem *)

Require Export Utils.psyntax.

Reserved Notation "Γ |-D i ; s <: t" (at level 68, i, s, t at next level).

Inductive subD {w m} (Γ : ctx m) : nat -> @ntype w m -> @ptype w m -> Prop :=
  | DTop s : Γ |-D 0; s <: top
  | DVar i j t h : Γ |-D h; ctx_at Γ i j <: t ->
      Γ |-D S h; var_ntype i j <: t
  | DAllNeg s t1 t2 i : add t1 Γ |-D i; t2 <: s ->
      Γ |-D S i; uAllN s <: bAllN t1 t2
  where "Γ |-D i ; A <: B" := (subD Γ i A B).


Definition FsubD_SUBTYPE : {w : nat & {m : nat & (@ctx w m * (@ntype w m * @ptype w m))%type}} -> Prop
  := fun nctt => let (w, s0) := nctt in let (m, p) := s0 in let (Γ, p0) := p in let (s, t) := p0
    in exists h, Γ |-D h; s <: t.
