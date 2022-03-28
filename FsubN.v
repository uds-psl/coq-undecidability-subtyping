(** * (Normal) System Fsub definition and subtyping problem *)

Require Import Coq.Lists.List.
Require Export Utils.syntax.

Reserved Notation " Δ ; Γ |-N i ; s : t" (at level 68, Γ, i, s, t at next level).
Reserved Notation " Γ |-N s <: t"  (at level 68, s, t at next level).

Definition ctx `{arrow_flag} := list type'.

Inductive subN : forall (b: arrow_flag), @ctx b -> @type' b -> @type' b -> Prop:=
  | NRefl {b: arrow_flag} Γ n : Γ |-N var_type n <: var_type n
  | NVar {b: arrow_flag} Γ s n : Γ |-N nth_default (var_type n) Γ n <: s -> Γ |-N var_type n <: s
  | NTop {b: arrow_flag} Γ s : Γ |-N s <: top
  | NArr Γ s1 s2 t1 t2: Γ |-N t1 <: s1 -> Γ |-N s2 <: t2 ->
      Γ |-N (arr s1 s2) <: (arr t1 t2)
  | NAll {b: arrow_flag} Γ s1 s2 t1 t2: Γ |-N t1 <: s1 -> map (ren_type ↑) (t1 :: Γ) |-N s2 <: t2  ->
      Γ |-N (all s1 s2) <: (all t1 t2)
  where " Γ |-N s <: t" := (subN _ Γ s t).

Notation "Γ |-N+ s <: t" := (subN arrow_on Γ s t) (at level 68, s, t at next level).
Notation "Γ |-N' s <: t" := (subN arrow_off Γ s t) (at level 68, s, t at next level).

Inductive chkN (Δ : @ctx arrow_on) (Γ : @ctx arrow_on) : nat -> term -> type -> Prop :=
  | NSubs t σ τ i : Δ; Γ |-Ni; t : σ -> Γ |-N+ σ <: τ -> Δ; Γ |-N S i; t : τ
  | NTVar n : Δ; Γ |-N0; var_term n : nth_default (var_type n) Δ n
  | NAbst t σ τ i : σ::Δ; Γ |-Ni; t : τ ->
      Δ; Γ|-N S i; lam σ t : arr σ τ
  | NInst t u σ τ i j: Δ; Γ |-Ni; t : arr σ τ -> Δ; Γ |-Nj; u : σ -> 
      Δ; Γ |-N S (max i j); app t u : τ
  | NTAbst t σ τ i: map (ren_type ↑) Δ; map (ren_type ↑) (σ :: Γ) |-Ni; t : τ ->
      Δ; Γ |-N S i; tlam σ t : all σ τ
  | NTInst t σ σ1 τ τ1 i: Δ; Γ |-Ni; t : all σ τ -> Γ |-N+ σ1 <: σ -> τ1=subst_type (σ1 ..) τ ->
      Δ; Γ |-N S i; tapp t σ1 : τ1
  where " Δ ; Γ |-N i ; s : t" := (chkN Δ Γ i s t).

Definition FsubN_SUBTYPE : {b:arrow_flag & (@ctx b * (@type' b * @type' b))%type} -> Prop
  := fun bctt => let (b,ctt):=bctt in let (Γ,tt):=ctt in let (s,t):=tt
    in Γ |-N s <: t.

Definition FsubN_off_SUBTYPE : (@ctx arrow_off * (@type' arrow_off * @type' arrow_off))%type -> Prop
  := fun ctt => let (Γ, tt) := ctt in let (σ, τ) := tt
    in Γ |-N' σ <: τ.

Definition FsubN_on_SUBTYPE : (@ctx arrow_on * (@type' arrow_on * @type' arrow_on))%type -> Prop
  := fun ctt => let (Γ, tt) := ctt in let (σ, τ) := tt
    in Γ |-N+ σ <: τ.

Definition FsubN_TYPECHK : (ctx * ctx) * (term * type) -> Prop
  := fun cctt => let (cc, tt) := cctt in let (Δ, Γ) := cc in let (t, τ) := tt
    in exists i, Δ ; Γ |-Ni; t : τ.