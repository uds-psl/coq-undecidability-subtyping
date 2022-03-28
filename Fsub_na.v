(** * System Fsub subtyping without arrow types *)

Require Export unscoped.

Reserved Notation " Γ |-' s <: t" (at level 68, s, t at next level).

(** ** Syntax of types *)

Inductive type : Type :=
  | var_type : fin -> type
  | top : type
  | all : type -> type -> type.

Fixpoint ren_type (ξ : fin -> fin) (t : type) : type  :=
  match t return type with
  | var_type n => var_type (ξ n)
  | top  => top
  | all t0 t1 => all (ren_type ξ t0) (ren_type (up_ren ξ) t1)
  end.

Fixpoint subst_type (θ : fin -> type) (t : type) : type  :=
  match t return type with
  | var_type n => θ n
  | top  => top
  | all t0 t1 => all (subst_type θ t0) (subst_type (var_type 0 .: θ >> ren_type ↑) t1)
  end.


(** ** Subtyping relation *)

Inductive sub' (Γ : list type) : type -> type -> Prop :=
  | Refl τ : Γ |-' τ <: τ
  | Trans σ τ υ : Γ |-' σ <: τ -> Γ |-' τ <: υ ->
      Γ |-' σ <: υ
  | Top τ : Γ |-' τ <: top
  | Var n : Γ |-' var_type n <: nth_default (var_type n) Γ n
  | All σ1 σ2 τ1 τ2 : Γ |-' τ1 <: σ1 -> map (ren_type ↑) (τ1 :: Γ) |-' σ2 <: τ2  ->
      Γ |-' (all σ1 σ2) <: (all τ1 τ2)
  where "Γ |-' σ <: τ" := (sub' Γ σ τ).

(** ** Subtyping problem *)

Definition Fsub'_SUBTYPE : (list type * (type * type)) -> Prop
  := fun ctt => let (Γ, tt) := ctt in let (σ, τ) := tt
    in Γ |-' σ <: τ.