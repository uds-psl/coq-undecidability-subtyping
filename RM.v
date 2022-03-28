(** * Rowing machine definition and halting problem *)
Require Import Vectors.Vector Vectors.Fin Vectors.VectorEq.
Require Import Arith Relations Lia.
Import VectorNotations.
Require Export Utils.row.
Require Import Utils.Various_utils.

Section RM.
Context {w : nat}.

Definition RM := Vector.t (@row (S w) 0) (S w).

Definition step (r : RM) : option RM := match Vector.hd r with
  | var_row _ i => False_rect _ i
  | abst t => Some (Vector.map (subst_row (fun i => nth' r i .; fun j:fin 0 => False_rect _ j)) t)
  | halt => None
  end.

Definition step_to (r s : RM) := step r = Some s.
Definition halting (r : RM) := step r = None.

End RM.


Notation "x ~~> y " := (clos_trans_1n _ step_to x y) (at level 70, no associativity).
Notation "x ~|> y " := (x~~>y /\ RM.halting y ) (at level 70, no associativity).

Definition RM_HALT (R : {w & @RM w}) : Prop := let r := projT2 R in
  halting r \/ exists s, r ~|> s.

