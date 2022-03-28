(** * General facts of Counter Machines as defined by Pierce *)
Require Import CM2.
Require Import Lia Relations Vectors.Vector Utils.Various_utils.

Section CM2_facts.
Context {w:nat}.

Variable M : @CM2 w.

Lemma step_det r s0 s1 : step_to M r s0 -> step_to M r s1 -> s0=s1.
Proof. unfold step_to. intros. rewrite H in H0. now inversion H0. Qed.


Inductive stepind : Config -> Config -> nat -> Prop :=
  | step1 x y : step_to M x y -> stepind x y 1
  | stepS x y z n: step_to M x y -> stepind y z n -> stepind x z (S n).

Fixpoint toStepind  x y (xy : M // x ~> y) : exists n, stepind x y n.
Proof. destruct xy.
  -exists 1. now apply step1.
  -destruct (toStepind y z xy) as [n yz].
   exists (S n). now apply (stepS _ y).
Defined.

Lemma non0step x y n : (stepind x y n) -> 0<n.
Proof. destruct 1; lia. Qed.

Fixpoint getTrace x y y' m n (xy : stepind x y n) (xy' : stepind x y' m) : n > m -> stepind y' y (n-m).
Proof. intro. destruct xy; destruct xy'; simpl. 1,2: exfalso; lia.
  -rewrite (step_det _ _ _ H1 H0). assert (n0:n-0=n). { lia. } now rewrite n0.
  -assert (nH: n>n0). { lia. } apply (getTrace y z z0); try auto. now rewrite (step_det _ _ _ H0 H1).
Defined.

Fixpoint compTrace x y y' m n (xy : stepind x y n) (xy' : stepind x y' m) (yH : halting M y) : m<n \/ y=y'.
Proof. destruct xy; destruct xy'.
  -right. now apply (step_det _ _ _ H H0).
  -exfalso. rewrite (step_det _ _ _ H0 H) in xy'. unfold halting in yH.
    destruct xy'; unfold step_to in H1; rewrite H1 in yH; discriminate.
  -left. pose (non0step _ _ _ xy). lia.
  -rewrite (step_det _ _ _ H0 H) in xy'. destruct (compTrace _ _ _ _ _ xy xy' yH). left. lia. now right.
Defined.

Lemma halting_char x : halting M x <-> nth' M (state x) = halt.
Proof. unfold halting. unfold step.
  destruct (nth' M (state x)) eqn:nH. 1,2 : (split; intro; exfalso; discriminate). tauto.
Qed.

Fact step_not_halting x y n : stepind x y n -> ~ halting M x.
Proof. destruct 1; unfold halting; intro Hs; unfold step_to in H; rewrite H in Hs; discriminate.
Qed.

End CM2_facts.
