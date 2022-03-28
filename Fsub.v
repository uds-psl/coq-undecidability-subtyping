(** * System Fsub subtyping and typechecking problem *)

Require Export unscoped.

Reserved Notation " Δ ; Γ |- s : t" (at level 68, Γ, s, t at next level).
Reserved Notation " Γ |- s <: t" (at level 68, s, t at next level).

(** ** Syntax of types and terms *)

Inductive type : Type :=
  | var_type : fin -> type
  | top : type
  | arr : type -> type -> type
  | all : type -> type -> type.

Inductive term : Type :=
  | var_term : fin -> term
  | lam : type -> term -> term
  | app : term -> term -> term
  | tlam : type -> term -> term
  | tapp : term -> type -> term.

Fixpoint ren_type (ξ : fin -> fin) (t : type) : type  :=
  match t return type with
  | var_type n => var_type (ξ n)
  | top  => top
  | arr t0 t1 => arr (ren_type ξ t0) (ren_type ξ t1)
  | all t0 t1 => all (ren_type ξ t0) (ren_type (up_ren ξ) t1)
  end.

Fixpoint ren_term (ξ_type : fin -> fin) (ξ_term : fin -> fin) (t : term) : term :=
  match t return term with
  | var_term n => var_term (ξ_term n)
  | lam t0 t1 => lam (ren_type ξ_type t0) (ren_term ξ_type (up_ren ξ_term) t1)
  | app t0 t1 => app (ren_term ξ_type ξ_term t0) (ren_term ξ_type ξ_term t1)
  | tlam t0 t1 => tlam (ren_type ξ_type t0) (ren_term (up_ren ξ_type) ξ_term t1)
  | tapp t0 t1 => tapp (ren_term ξ_type ξ_term t0) (ren_type ξ_type t1)
  end.

Fixpoint subst_type (θ : fin -> type) (t : type) : type  :=
  match t return type with
  | var_type n => θ n
  | top  => top
  | arr t0 t1 => arr (subst_type θ t0) (subst_type θ t1)
  | all t0 t1 => all (subst_type θ t0) (subst_type (var_type 0 .: θ >> ren_type ↑) t1)
  end.

Fixpoint subst_term (θ_type : fin -> type) (θ_term : fin -> term) (t : term) : term :=
  match t return term with
  | var_term n => θ_term n
  | app t0 t1 => app (subst_term θ_type θ_term t0) (subst_term θ_type θ_term t1)
  | lam t0 t1 => lam (subst_type θ_type t0) (subst_term θ_type (var_term 0 .: θ_term >> ren_term id ↑) t1)
  | tapp t0 t1 => tapp (subst_term θ_type θ_term t0) (subst_type θ_type t1)
  | tlam t0 t1 => tlam (subst_type θ_type t0) (subst_term (var_type 0 .: θ_type >> ren_type ↑) (θ_term >> ren_term ↑ id) t1)
  end.

(** ** Subtyping and typechecking relations *)

Inductive sub (Γ : list type) : type -> type -> Prop :=
  | Refl τ : Γ |- τ <: τ
  | Trans σ τ υ : Γ |- σ <: τ -> Γ |- τ <: υ ->
      Γ |- σ <: υ
  | Top τ : Γ |- τ <: top
  | Var n : Γ |- var_type n <: nth_default (var_type n) Γ n
  | Arr σ1 σ2 τ1 τ2 : Γ |- τ1 <: σ1 -> Γ |- σ2 <: τ2  ->
      Γ |- (arr σ1 σ2) <: (arr τ1 τ2)
  | All σ1 σ2 τ1 τ2 : Γ |- τ1 <: σ1 -> map (ren_type ↑) (τ1 :: Γ) |- σ2 <: τ2  ->
      Γ |- (all σ1 σ2) <: (all τ1 τ2)
  where "Γ |- σ <: τ" := (sub Γ σ τ).


Inductive chk (Δ : list type) (Γ : list type) : term -> type -> Prop :=
  | Subs t σ τ : Δ;Γ |- t : σ -> Γ |- σ <: τ ->
      Δ;Γ |- t : τ
  | TVar n : Δ;Γ |- var_term n : nth_default (var_type n) Δ n
  | Abst t σ τ : σ::Δ;Γ |- t : τ ->
      Δ;Γ |- lam σ t : arr σ τ
  | Inst t u σ τ : Δ;Γ |- t : arr σ τ -> Δ;Γ |- u : σ -> 
      Δ;Γ |- app t u : τ
  | TAbst t σ τ : map (ren_type ↑) Δ; map (ren_type ↑) (σ :: Γ) |- t : τ ->
      Δ;Γ |- tlam σ t : all σ τ
  | TInst t σ σ1 τ τ1 : Δ;Γ |- t : all σ τ -> Γ |- σ1 <: σ -> τ1=subst_type (σ1.:var_type) τ ->
      Δ;Γ |- tapp t σ1 : τ1
  where " Δ ; Γ  |- t : τ" := (chk Δ Γ t τ).

(** ** Subtyping and typechecking problems *)

Definition Fsub_SUBTYPE : (list type * (type * type))-> Prop
  := fun ctt => let (Γ, tt) := ctt in let (σ, τ) := tt
    in Γ |- σ <: τ.

Definition Fsub_TYPECHK : (list type * list type) * (term * type) -> Prop
  := fun cctt => let (cc, tt) := cctt in let (Δ, Γ) := cc in let (t, τ) := tt
    in Δ;Γ |- t : τ.