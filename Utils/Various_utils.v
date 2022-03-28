(** * Utilities for vectors *)
Require Import Lia Arith Vectors.Vector Vectors.Fin Relations Eqdep_dec Logic.Eqdep.
Require Import fintype.
Import VectorNotations.

Fact DPI {X} {p : X -> Type} {x u v} : existT p x u = existT p x v -> u = v.
Proof. intro. now apply eq_dep_eq,eq_sigT_eq_dep. Qed.

Fact congr_cons : forall n A a1 a2 (v1 v2 : Vector.t A n), a1=a2 -> v1=v2 -> a1::v1 = a2::v2.
Proof. congruence. Qed.

Definition isNil {A} (t : Vector.t A 0) : t = []
  := match t with [] => eq_refl end.

(** ** Accessing a vector of length _n_ with an element of _I^n_. *)
Fixpoint nth' {A} {n} (v : Vector.t A n) (i : fin n) {struct v} : A.
Proof. destruct n. contradiction. destruct i.
  -apply (Vector.caseS (fun n _ => fin n -> A) (fun _ n t j => nth' _ n t j) v), f.
  -apply (Vector.caseS (fun _ _ => A) (fun h _ _ => h) v).
Defined.

Fixpoint nth'_map {m} {A B} {f : A -> B} {v} {i : fin m} {struct m} : nth' (Vector.map f v) i = f (nth' v i).
Proof. destruct m. contradiction. apply (Vector.caseS' v). intros. simpl. destruct i; auto.
Qed.

(** A vector that has its index at each position *)
Definition mkvect' n : { v : Vector.t (fin n) n | forall i, nth' v i = i}.
Proof. induction n as [ | n [v vH] ].
  -exists []. contradiction.
  -exists (Vector.cons _ var_zero _ (Vector.map shift v)).
   destruct i; cbn; auto. rewrite nth'_map. now rewrite vH.
Qed.

Fact In_nth' {A n} (v : Vector.t A n) i : Vector.In (nth' v i) v.
Proof. induction v. contradiction.
  destruct i; simpl. apply In_cons_tl,IHv. apply In_cons_hd.
Qed.

Definition caseSEq {A} {n : nat} (v : Vector.t A (S n)) : forall (P : Vector.t A (S n) -> Type)
  (H : forall h t, v=Vector.cons _ h _ t -> P (Vector.cons _ h _ t)), P v :=
  match v with
  | Vector.cons _ h _ t => fun P H => H h t eq_refl
  | _ => fun devil => False_rect (@IDProp) devil
  end.

Fact ext_nth' {n A }{u v : Vector.t A n} : (forall i, nth' u i = nth' v i) -> u=v.
Proof. induction n. intro. rewrite isNil. now rewrite (isNil u).
  apply (caseSEq u). intros h t Hu. apply (caseSEq v). intros h' t' Hv. intro.
  apply congr_cons. apply (H None). apply IHn. intro. apply (H (Some i)).
Qed.

Fixpoint lastF w : { i : fin (S w) | forall A (v : Vector.t A (S w)), nth' v i = Vector.last v}.
Proof. destruct w.
  -exists None. intros. apply (@Vector.caseS' _ _ v). intros. now rewrite (isNil t).
  -destruct (lastF w) as [i H]. exists (Some i). intros. apply (@Vector.caseS' _ _ v). intros. simpl. apply H.
Defined.

(** ** Utilities for elements of _I^n_. *)
Fixpoint R {n} (m:nat) (i : fintype.fin n) {struct m} : fintype.fin (m+n).
Proof. destruct m. exact i.  apply fintype.shift, (R _ _ i).
Defined.

Fixpoint nat2fin {w i} (H : i<w) : fin w.
Proof. destruct w. exfalso. now apply (Lt.lt_n_0 i). destruct i.
  -exact None.
  -apply Some,(nat2fin w i),Lt.lt_S_n,H.
Defined.

Fixpoint nat2fin_ext {w i} (H H': i<w) : nat2fin H = nat2fin H'.
Proof. destruct w. exfalso. now apply (Lt.lt_n_0 i). destruct i; simpl. auto.
  now rewrite (nat2fin_ext _ _ (Lt.lt_S_n i w H) (Lt.lt_S_n i w H')).
Qed.

Fixpoint nat2nif {w i} (H : i<w) {struct w} : fin w.
Proof. destruct w. exfalso. now apply (Lt.lt_n_0 i). destruct (le_lt_dec (S w) (S i)). exact None.
  apply Some,(nat2nif _ i). now apply lt_S_n.
Defined.

Fact nat2nif_ext {w i} (H H': i<w) : nat2nif H = nat2nif H'.
Proof. destruct w. exfalso. now apply (Lt.lt_n_0 i). simpl. destruct i; simpl; auto.
Qed.

(* Fixpoint nat2nif_fin {w i} (H: w - S i < w) (H' : i<w) {struct w}: nat2fin H = nat2nif H'.
Proof. destruct w. exfalso. now apply (Lt.lt_n_0 i). revert H. assert (S w - S i=w-i). lia. rewrite H. clear H.
  simpl nat2nif. destruct (le_lt_dec w i).
  -assert (w-i=0). lia. rewrite H. intro. now cbn.
  -simpl. intro. destruct (w-i) eqn:wiH. lia.
Qed. *)

Fact nth'_nat2nif_tl {A n x h} {tl : Vector.t A n} (H:x<S n) (H':x<n) : nth' (h::tl)%vector (nat2nif H) = nth' tl (nat2nif H').
Proof. simpl. destruct (le_lt_dec n x); simpl. lia. now rewrite (nat2nif_ext _ H').
Qed.

Fact nth'_nat2nif_hd {A n h} {tl : Vector.t A n} (H:n<S n) : nth' (h::tl)%vector (nat2nif H) = h.
Proof. simpl. destruct (le_lt_dec n n); auto. lia.
Qed.

Fixpoint fin2nat {n} (i : fin n ) {struct n} : {x : nat | x<n }.
Proof. destruct n. contradiction. destruct i. destruct (fin2nat _ f). exists (S x). now apply Lt.lt_n_S.
  exists 0. apply PeanoNat.Nat.lt_0_succ.
Defined.

Fixpoint fin2nat' {n} (i : fin n ) {struct n} : {x : nat | {H : x<n | nat2fin H = i}}.
Proof. destruct n. contradiction. destruct i. 2: { exists 0. now exists (PeanoNat.Nat.lt_0_succ _). }
  destruct (fin2nat' _ f) as [x [H1 H2]]. exists (S x). exists (Lt.lt_n_S _ _ H1).
  simpl. rewrite (nat2fin_ext _ H1). now rewrite H2.
Defined.

Fixpoint nif2nat {n} (i : fin n ) {struct n} : {x : nat | {H : x<n | nat2nif H = i}}.
Proof. destruct n. contradiction. destruct i.
  -destruct (nif2nat _ f) as [x [H1 H2]]. exists x. exists (Nat.lt_lt_succ_r _ _ H1). simpl.
   destruct (le_lt_dec n x); simpl. lia. rewrite (nat2nif_ext _ H1). now rewrite H2.
  -exists n. exists (Nat.lt_succ_diag_r n). simpl. destruct (le_lt_dec n n); simpl. auto. lia.
Defined.

Fixpoint injS {n} : fintype.fin n -> fintype.fin (S n).
Proof. destruct n. contradiction. destruct 1. apply Some,injS,f. apply None.
Defined.

Fixpoint tabulate' {X n} (f : fintype.fin n -> X) {struct n} : Vector.t X n.
Proof. destruct n; constructor. apply f,None. apply tabulate'. intro. apply f,Some,H.
Defined.

Fixpoint nth'_shiftin {n A i x} {v : Vector.t A n}: nth' (shiftin x v) (injS i) = nth' v i.
Proof. destruct n. contradiction. apply (caseSEq v). intros. simpl. destruct i. 2: auto.
  apply nth'_shiftin.
Defined.

Fixpoint nth'_tabulate {X n} {i : fintype.fin n} {f : fintype.fin n -> X} {struct n} : nth' (tabulate' f) i = f i.
Proof. destruct n. contradiction. destruct i; unfold tabulate'; simpl. apply nth'_tabulate. auto.
Defined.

Fixpoint f2n_n2f {w x} {H: x<w} : proj1_sig (fin2nat (nat2fin H)) = x.
Proof. destruct w. lia. unfold nat2fin. destruct x.  now simpl. fold (@nat2fin w). simpl.
  specialize (f2n_n2f w x (lt_S_n x w H)). revert f2n_n2f. destruct (fin2nat (nat2fin (lt_S_n x w H))). simpl. congruence.
Qed.

Section fins.
Context {w:nat}.

Definition fins2nat {n} (i: fintype.fin w) (j: fintype.fin n) : nat.
Proof. destruct (nif2nat i). destruct (fin2nat' j). exact (x0*w+x). Defined.

Fact fs2nS {n} i (j: fintype.fin n): fins2nat i (fintype.shift j) = w+(fins2nat i j).
Proof. revert i. induction n. contradiction. destruct j; simpl; intro. 
  -specialize (IHn f i). unfold fins2nat in *. destruct (nif2nat i) as [x [Hxw Hi]]. simpl in *.
   destruct (fin2nat' f) as [y [Hyw Hj]]. lia.
  -unfold fins2nat. destruct (nif2nat i). simpl. lia.
Qed.
Fact fs2n0 {n x} (H:x<w) : fins2nat (nat2nif H) (@fintype.var_zero (S n)) = x.
Proof. unfold fins2nat. simpl. destruct (nif2nat (nat2nif H)) as [y [H1 H2]].
  revert x H y H1 H2. generalize w. induction w0; intros. lia. simpl in H2.
  destruct (le_lt_dec w0 y);destruct (le_lt_dec w0 x); simpl in H2. 2,3: discriminate.
  -enough (y=w0 /\ x=w0) by lia. split; lia.
  -inversion H2. apply (IHw0 _ _ _ _ H3).
Qed.

Definition nat2fins' {n x} (H: x<w*n) : {i:fintype.fin w &{j:fintype.fin n & fins2nat i j = x}}.
Proof. revert x H. induction n; intros. lia. destruct (le_lt_dec w x).
  -edestruct (IHn (x-w)) as [i [j Hij]]; try lia. exists i,(fintype.shift j).
   rewrite fs2nS. rewrite Hij. lia.
  -exists (nat2nif l),fintype.var_zero. apply (@fs2n0 n).
Qed.
Definition nat2fins {n x} : x<w*n -> (fintype.fin w)*(fintype.fin n).
Proof. intro. destruct (nat2fins' H) as [i [j _]]. exact (pair i j). Defined.

Fact fins2nat_0lt {m} (i : fintype.fin w) : (fins2nat i (@fintype.var_zero  m)) < w.
Proof. unfold fins2nat. destruct (nif2nat i) as [x [Hx H0]]. now simpl. Qed.
Fact fins2nat_lt {m} (i : fintype.fin w) (j : fintype.fin m) : (fins2nat i j) < w*m.
Proof. induction m. contradiction. destruct j.
  - change Datatypes.Some with (@fintype.shift m). rewrite fs2nS. specialize (IHm f). lia.
  - change Datatypes.None with (@fintype.var_zero m). pose (@fins2nat_0lt m i).
    enough (forall x, x<w -> x<w*S m) by auto. lia.
Qed.

Fixpoint fins2nat_eq {n i i'} {j j':fintype.fin n} {struct n} : fins2nat i' j' = fins2nat i j -> i=i' /\ j=j'.
Proof. destruct n. contradiction. destruct j; destruct j';
  change Datatypes.Some with (@fintype.shift n); change Datatypes.None with (@fintype.var_zero n);
  repeat rewrite fs2nS; intro.
  -apply plus_reg_l in H. now destruct (fins2nat_eq _ _ _ _ _ H) as [-> ->].
  -pose (@fins2nat_0lt n i'). rewrite H in l. lia.
  -pose (@fins2nat_0lt n i). rewrite <- H in l. lia.
  -split; auto. revert H. unfold fins2nat. cbn.
   destruct (nif2nat i') as [x0 [Hx0 <-]].
   destruct (nif2nat i) as [x1 [Hx1 <-]]. intro. revert Hx0 Hx1. rewrite H.
   intros. apply nat2nif_ext.
Qed.

Fact n2fs_unfold {n} {i: fintype.fin w} {j: fintype.fin n} {H : fins2nat i j < w*n} : nat2fins H = (pair i j).
Proof. unfold nat2fins. destruct (nat2fins' H) as [i' [j' H']]. destruct (fins2nat_eq H'). congruence.
Qed.

End fins.

Fixpoint lnth {A} (l : list A) n (H: n<length l): A.
Proof. destruct l; simpl in H. exfalso. lia. destruct n.
  -exact a.
  -apply (lnth A l n). now apply Lt.lt_S_n.
Defined.

Fixpoint lnth_some {A} (l : list A) i s (H : s < length l) : List.nth_error l s = Some i -> lnth l s H = i.
Proof. intros ntH. destruct l; simpl in H. exfalso. lia. destruct s; simpl in ntH; inversion ntH; simpl.
  -reflexivity.
  -now apply lnth_some.
Defined.

Fixpoint vsum {n} (v : Vector.t nat n) : nat := match n as n0 return (Vector.t nat n0 -> nat) with
 | 0 => fun _ : Vector.t nat 0 => 0
 | S n0 => fun v0 : Vector.t nat (S n0) => Vector.caseS' v0 (fun _ : Vector.t nat (S n0) => nat)
       (fun (h : nat) (t : Vector.t nat n0) => h + vsum  t)
 end v.

Fact in_smaller {n} x (v : Vector.t nat n) : Vector.In x v -> x <= vsum v.
Proof. induction 1; simpl; lia.
Qed.

Fact Forall_nth' {A P n} {v : Vector.t A n}: Vector.Forall P v <-> forall i (Hi : i < n), P (nth' v (nat2fin Hi)).
Proof. split; induction n as [|n IHn].
  - intros HF i Hi; inversion Hi.
  - intros HF i Hi. rewrite (eta v) in *. inversion HF as [| ? ? ? ? ? Heq1 [Heq2 He]]; subst.
    apply (inj_pair2_eq_dec _ Nat.eq_dec) in He ; subst. destruct i; simpl. auto. now apply IHn.
  - intros. rewrite (isNil v). constructor.
  - intros HP. rewrite (eta v) in HP. rewrite (eta v); constructor.
    + specialize HP with 0 (Nat.lt_0_succ n). now simpl in HP.
    + apply IHn; intros i Hi. specialize HP with (S i) (proj1 (Nat.succ_lt_mono _ _) Hi).
      simpl in HP. erewrite nat2fin_ext. eauto.
Qed.

(** ** Utilities for lists *)
Section lists.

Context {A B : Type}.

Fact nthd_cons {d n h} {l:list A} : nth_default d (h::l) (S n) = nth_default d l n.
Proof. repeat rewrite nth_default_eq. now simpl. Qed.

Fact map_nthd {f:A->B} : forall l d n, nth_default (f d) (map f l) n = f (nth_default d l n).
Proof. intros. repeat rewrite nth_default_eq. now rewrite map_nth. Qed.

Fact length_to_list {n} {v:Vector.t A n} : length (to_list v) = n.
Proof. induction v. now simpl.
  assert (to_list (h::v)=cons h (to_list v)) as -> by reflexivity.
  simpl. now rewrite IHv.
Qed.
Fact to_list_map {n} {v:Vector.t A n} {f:A->B} : to_list (Vector.map f v) = map f (to_list v).
Proof. induction v. now simpl.
  assert (to_list (h::v)=cons h (to_list v)) as -> by reflexivity. simpl.
  rewrite <- IHv. reflexivity.
Qed.
Fact nth_indep' {n l b d} {f:A->B} : n<length l -> nth n (map f l) b = f (nth n l d).
Proof. intro. erewrite nth_indep. now erewrite map_nth. now rewrite map_length.
Qed.
Fact nth_nth' {n x d m} {v:Vector.t A n} (H:x<n) : n=m -> nth (m-S x) (to_list v) d = nth' v (nat2nif H).
Proof. revert m. induction n; intros. lia. apply (caseSEq v). intros.
  assert (to_list (h::t)=cons h (to_list t)) as -> by reflexivity. simpl.
  destruct (le_lt_dec n x); simpl.
  -assert ((S x)=m) as -> by lia. now rewrite Nat.sub_diag.
  -destruct m. discriminate. erewrite nat2nif_ext. erewrite <- IHn.
   destruct (S m - S x) eqn:Hxn. { exfalso. lia. }
   now assert (n0=n-S x) as -> by lia. auto. Unshelve. auto.
Qed.

End lists.