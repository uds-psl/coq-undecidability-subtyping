(** * General facts of Rowing Machines *)
Require Import RM Utils.Various_utils.
Require Import Lia Relations Vectors.Vector Arith.
Require Import Logic.Eqdep_dec.
Import VectorNotations.
Require axioms.

Section RM_facts.

Context {w:nat}.

Lemma step_det (r s0 s1 : @RM w) : step_to r s0 -> step_to r s1 -> s0=s1.
Proof. unfold step_to. intros. rewrite H in H0. now inversion H0. Qed.


Inductive stepind : (@RM w) -> (@RM w) -> nat -> Prop :=
  | step1 x y : step_to x y -> stepind x y 1
  | stepS x y z n: step_to x y -> stepind y z n -> stepind x z (S n).

Fixpoint toStepind  (x y : RM) (xy : clos_trans_1n _ step_to x y) : exists n, stepind x y n.
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

Fixpoint compTrace (x y y' : RM ) m n (xy : stepind x y n) (xy' : stepind x y' m) (yH : halting y) : m<n \/ y=y'.
Proof. destruct xy; destruct xy'.
  -right. now apply (step_det _ _ _ H H0).
  -exfalso. rewrite (step_det _ _ _ H0 H) in xy'. unfold halting in yH.
    destruct xy'; unfold step_to in H1; rewrite H1 in yH; discriminate.
  -left. pose (non0step _ _ _ xy). lia.
  -rewrite (step_det _ _ _ H0 H) in xy'. destruct (compTrace _ _ _ _ _ xy xy' yH). left. lia. now right.
Defined.

Lemma halting_char r : @halting w r <-> hd r = halt.
Proof. unfold halting. unfold step. destruct (hd r) eqn:hH.
  -contradiction.
  -split; intro; exfalso; discriminate.
  -tauto.
Qed.

End RM_facts.

Section row_facts.
Import axioms.
Import VectorNotations.

Fact lt_S l k : l < S k -> (l = k) + (l < k).
Proof. intros Hk. destruct (Compare_dec.lt_eq_lt_dec l k) as [[H|H]|H]; auto. lia.
Qed.

Lemma row_size_rec (P : forall w m, @row w m -> Type) : forall w m,
  (forall m x, (forall m y, size y < size x -> P w m y) -> P w m x) ->
  forall x, P w m x.
Proof. intros w m H r. apply H. induction (size r); intros. lia. destruct (lt_S _ _ H0).
  -apply H. rewrite e. apply IHn.
  -apply IHn,l.
Defined.

Fact row_size_rec_unfold P w F m r : row_size_rec P w m F r = F m r (fun m s H => row_size_rec P w m F s).
Proof. unfold row_size_rec at 1. f_equal. fext. intros m' x Hx. induction (size r); cbn. lia.
  destruct (lt_S _ _ Hx) as [<-|H]. reflexivity. apply IHn.
Qed.


Lemma row_rec (P : forall w m, @row w m -> Type) w
  (Hv: forall m i j, P w m (var_row i j))
  (Ha: forall m v, (forall i, P w (S m) (nth' v i)) -> P w m (abst v) )
  (Ht: forall m, P w m halt) : forall m r, P w m r.
Proof. intros. eapply row_size_rec. destruct x. 1,3: auto.
  intro H. apply Ha. intro. apply H,inSize,In_nth'.
Defined.

Fact row_rec_unfold {P w Hv Ha Hh m r} : row_rec P w Hv Ha Hh m r = match r with
  | var_row i j => Hv m i j
  | abst v => Ha m v (fun i => row_rec P w Hv Ha Hh (S m) (nth' v i))
  | halt => Hh m
  end.
Proof. destruct r; unfold row_rec; now rewrite row_size_rec_unfold.
Qed.

End row_facts.

