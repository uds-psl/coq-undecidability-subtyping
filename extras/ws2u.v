(** * Encoding of well-scoped syntax as unscoped syntax *)

Require Import utype wstype.
Require Import Lia Arith Utils.Various_utils Program.Equality.

Inductive closed : utype.type -> nat -> Prop :=
  | cVar x n : x<n -> closed (utype.var_type x) n
  | cAll s t n : closed s n -> closed t (S n) -> closed (utype.all s t) n.

Fixpoint encode {n : nat} (t : wstype.type n) : utype.type :=
  match t with
   | var_type f => let s := fin2nat f in let (x, _) := s in utype.var_type x
   | all t1 t2 => utype.all (encode t1) (encode t2)
   end.

Notation "⟦ t ⟧" := (encode t).

Definition encode_ren {n m : nat} (ξ : fin n -> fin m) : nat -> nat.
Proof. intro x. destruct (le_lt_dec n x) as [ |H].
  - exact x.
  - eapply fin2nat,ξ,(nat2fin H).
Defined.

Notation "« r »" := (encode_ren r).

Fact wellscoped_closed {n} (t : wstype.type n) : closed ⟦t⟧ n.
Proof. induction t; simpl.
  -destruct (fin2nat f). now apply cVar.
  -now apply cAll.
Qed.


Fact bext_ren (n:nat) (t : utype.type) (Hc : closed t n) (ξ ξ' : nat -> nat) (Hx : forall x, x<n -> ξ x = ξ' x) :
  utype.ren_type ξ t = utype.ren_type ξ' t.
Proof. revert n Hc ξ ξ' Hx. induction t; intros; depind Hc; simpl.
  -now rewrite (Hx n H).
  -apply utype.congr_all.
    +eapply IHt1. exact Hc1. exact Hx.
    +eapply IHt2. exact Hc2. intros. destruct (le_lt_dec n x).
      *assert (x=n) as -> by lia. destruct n; simpl; auto. unfold unscoped.funcomp. now rewrite Hx.
      *destruct x; simpl; auto. unfold unscoped.funcomp. rewrite Hx. auto. lia.
Qed.

Lemma ext_ren_upto (n:nat) (ξ ξ' : nat -> nat) (Hx : forall x, x<n -> ξ x = ξ' x) (t : wstype.type n) :
  utype.ren_type ξ ⟦t⟧ = utype.ren_type ξ' ⟦t⟧.
Proof. apply (bext_ren n). apply wellscoped_closed. assumption.
Qed.

Fact n2f_S {n m} (H : S n < S m) (H': n<m) : nat2fin H = shift (nat2fin H').
Proof. simpl. now rewrite (nat2fin_ext _ H'). Qed.

Fixpoint f2n_n2f' {n x} {f : fin n} {H : x<n} {struct n}: fin2nat f = exist (fun x => x < n) x H -> nat2fin H = f.
Proof. intro. destruct n. contradiction. unfold nat2fin. destruct x.
  { destruct f. simpl in *.  destruct (fin2nat f). discriminate. auto. }
  fold (@nat2fin n). destruct f. 2: simpl in *; discriminate. f_equal. apply f2n_n2f'.
  simpl in *. destruct (fin2nat f).
Admitted.

Theorem encoding_ren {n m : nat} (ξ : fin n -> fin m) (t : wstype.type n) :
  ⟦ wstype.ren_type ξ t ⟧ = utype.ren_type «ξ»  ⟦t⟧.
Proof. revert m ξ. induction t; intros; simpl.
  -destruct (fin2nat f) eqn:Hf. simpl. unfold encode_ren. destruct (le_lt_dec ntype x).
   exfalso. lia. rewrite (nat2fin_ext _ l). enough (nat2fin l=f). rewrite H. now destruct (fin2nat (ξ f)).
   now apply f2n_n2f'.
  -apply utype.congr_all. apply IHt1. rewrite IHt2. eapply ext_ren_upto.
   intros. destruct x. simpl. unfold encode_ren. destruct (le_lt_dec (S ntype) 0); now simpl.
   simpl. unfold unscoped.funcomp. unfold encode_ren. destruct (le_lt_dec ntype x). lia.
   destruct (le_lt_dec (S ntype) (S x)). lia. rewrite (n2f_S _ l). simpl.
   now destruct (fin2nat (ξ (nat2fin l))).
Qed.



Definition encode_subst {n m : nat} (ξ : fin n -> wstype.type m) : nat -> utype.type.
Proof. intro x. destruct (le_lt_dec n x) as [ |H].
  - apply utype.var_type,x.
  - eapply encode,ξ,(nat2fin H).
Defined.

Notation "[| s |]" := (encode_subst s).

Fact bext_subst (n:nat) (t : utype.type) (Hc : closed t n) (θ θ' : nat -> utype.type) (Hx : forall x, x<n -> θ x = θ' x) :
  utype.subst_type θ t = utype.subst_type θ' t.
Proof. revert n Hc θ θ' Hx. induction t; intros; depind Hc; simpl.
  -now apply Hx.
  -apply utype.congr_all.
    +eapply IHt1. exact Hc1. exact Hx.
    +eapply IHt2. exact Hc2. intros. destruct (le_lt_dec n x).
      *assert (x=n) as -> by lia. destruct n; simpl; auto. unfold unscoped.funcomp. now rewrite Hx.
      *destruct x; simpl; auto. unfold unscoped.funcomp. rewrite Hx. auto. lia.
Qed.

Lemma ext_subst_upto (n:nat) (θ θ' : nat -> utype.type) (Hx : forall x, x<n -> θ x = θ' x) (t : wstype.type n) :
  utype.subst_type θ ⟦t⟧ = utype.subst_type θ' ⟦t⟧.
Proof. apply (bext_subst n). apply wellscoped_closed. assumption.
Qed.

Theorem encoding_subst {n m : nat} (θ : fin n -> wstype.type m) (t : wstype.type n) :
   ⟦ wstype.subst_type θ t ⟧ = utype.subst_type [|θ|]  ⟦t⟧.
Proof. revert m θ. induction t; intros; simpl.
  -destruct (fin2nat f) eqn:Hf. simpl. unfold encode_subst. destruct (le_lt_dec ntype x).
   lia. rewrite (nat2fin_ext _ l). enough (nat2fin l=f). now rewrite H. now apply f2n_n2f'.
  -apply utype.congr_all. apply IHt1. rewrite IHt2. eapply ext_subst_upto.
   intros. destruct x. simpl. unfold encode_subst. destruct (le_lt_dec (S ntype) 0); now simpl.
   simpl. unfold unscoped.funcomp. unfold encode_subst. destruct (le_lt_dec ntype x). lia.
   destruct (le_lt_dec (S ntype) (S x)). lia. rewrite (n2f_S _ l). simpl.
   unfold funcomp. rewrite encoding_ren. apply ext_ren_upto. intros.
   unfold encode_ren. destruct (le_lt_dec m x0). lia. simpl.
   destruct (fin2nat (nat2fin l1)) eqn:Hf2n. f_equal. auto. rewrite <- (@f2n_n2f _ _ l1).
   now rewrite Hf2n.
Qed.