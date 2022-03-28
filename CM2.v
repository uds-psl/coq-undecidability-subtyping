(** * Counter machine definition and halting problem *)
Require Import Vectors.Vector Utils.headers.fintype Utils.Various_utils.
Require Import Relations.
Section CM2.

Context {w : nat}.
Definition State : Set := fin w.
Record Config : Set := mkConfig { state : State; value1 : nat; value2 : nat }.

Inductive Instruction : Set := 
  | inc : bool -> State -> Instruction
  | dec : bool -> State -> State -> Instruction
  | halt : Instruction.

Definition CM2 : Set := Vector.t Instruction w.

Definition step (M: CM2) (x: Config) : option Config :=
  match nth' M (state x) with
  | halt => None
  | inc b x' => Some {| state := x'; 
       value1 := (if b then 0 else 1) + (value1 x);
       value2 := (if b then 1 else 0) + (value2 x) |}
  | dec b x' y => Some (
    if b then
      match value2 x with
      | 0 => {| state := x'; value1 := value1 x; value2 := 0 |}
      | S n => {| state := y; value1 := value1 x; value2 := n |}
      end
    else
      match value1 x with
      | 0 => {| state := x'; value1 := 0; value2 := value2 x |}
      | S n => {| state := y; value1 := n; value2 := value2 x |}
      end)
  end.

Definition halting (M : CM2) (x: Config) : Prop := step M x = None.

Definition step_to M x y := step M x = Some y.
End CM2.

Notation "M // x ~> y " := (clos_trans_1n _ (step_to M) x y) (at level 70, no associativity).
Notation "M // x |> y " := (M//x~>y /\ CM2.halting M y) (at level 70, no associativity).

Definition CM2_HALT (M : {w & @CM2 (S w)}) : Prop := let x := mkConfig var_zero 0 0 in let m := projT2 M in
  halting m x \/ exists y, m // x |> y.