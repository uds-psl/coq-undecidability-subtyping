(** * Encoding of polyadic syntax as well-scoped syntax *)

Require Import wstype ptype.
Require Import Lia Arith Utils.Various_utils Program.Equality.

Section polyadic.

Context {w:nat}.

Fixpoint iterShift {m} (n:nat) (t: fin m) : fin (n+m) := match n with
  | 0 => t
  | S n0 => ↑(iterShift n0 t)
end.

Fixpoint mkAll {n m} (v : Vector.t (wstype.type m) n) (b : wstype.type (m+w)) {struct v} : n<=w -> wstype.type ((w-n)+m).
Proof. intro. destruct v.
  -rewrite Nat.sub_0_r,Nat.add_comm. exact b.
  -apply wstype.all. exact (wstype.ren_type (iterShift (w-S n)) h).
   assert (S (w - S n + m)=w-n+m) as -> by lia. eapply (mkAll _ _ v b). lia.
Defined.

Fixpoint encode {n : nat} (t : @ptype.type w n) : wstype.type (w*n).
Proof. destruct t.
  -eapply wstype.var_type,nat2fin,(fins2nat_lt f0 f).
  -rewrite <- plus_O_n,(minus_diag_reverse w). apply (mkAll (Vector.map (encode _) t)). rewrite mult_n_Sm. exact (encode _ t0). lia.
Defined.

Notation "⟦ t ⟧" := (encode t).

Definition encode_ren {n m : nat} (ξ : fin n -> fin m) : fin (w*n) -> fin (w*m).
Proof. intro xi. destruct (fin2nat xi) as [j Hj]. destruct (nat2fins Hj) as [i x]. apply ξ in x.
  eapply nat2fin. apply (fins2nat_lt i x).
Defined.
Notation "« r »" := (encode_ren r).

Fact ext_ren (n m:nat) (t : wstype.type n) (ξ ξ' : fin n -> fin m) (Hx : forall x, ξ x = ξ' x) :
  wstype.ren_type ξ t = wstype.ren_type ξ' t.
Proof. now apply extRen_type.
Qed.

Theorem encoding_ren {n m : nat} (ξ : fin n -> fin m) (t : @ptype.type w n) :
  ⟦ ptype.ren_type ξ t ⟧ = wstype.ren_type «ξ»  ⟦t⟧.
Proof. revert m ξ. induction t; intros.
  -simpl. unfold encode_ren. destruct (fin2nat (nat2fin (fins2nat_lt f0 f))) eqn:H.
   eapply (ap (@proj1_sig _ _)) in H. rewrite f2n_n2f in H. simpl in H.
   revert l. rewrite <- H. intro. now rewrite n2fs_unfold.
  -simpl ren_type. unfold encode. apply utype.congr_all. apply IHt1. rewrite IHt2. eapply ext_ren.
   intros. destruct x. simpl. unfold encode_ren. destruct (le_lt_dec (S ntype) 0); now simpl.
   simpl. unfold unscoped.funcomp. unfold encode_ren. destruct (le_lt_dec ntype x). lia.
   destruct (le_lt_dec (S ntype) (S x)). lia. simpl.
   now destruct (fin2nat (ξ (nat2fin l))).
Qed.

Definition encode_subst {n m : nat} (θ: fin n -> fin w -> @ptype.type w m) : fin (w*n) -> wstype.type (w*m).
Proof. intro ix. destruct (fin2nat ix) as [j Hj]. destruct (nat2fins Hj) as [i x].
  exact ⟦ θ x i ⟧.
Defined.

Notation "[| s |]" := (encode_subst s).

Fact ext_subst (n m:nat) (t : wstype.type n) (θ θ' : fin n -> wstype.type m) (Hx : forall x, θ x = θ' x) :
  wstype.subst_type θ t = wstype.subst_type θ' t.
Proof. now apply ext_type.
Qed.

Theorem encoding_subst {n m : nat} (θ: fin n -> fin w -> @ptype.type w m) (t : @ptype.type w n) :
   ⟦ ptype.subst_type θ t ⟧ = wstype.subst_type [|θ|]  ⟦t⟧.
Proof. revert m θ. induction t; intros; simpl.
  -unfold encode_subst. destruct (fin2nat (nat2fin (fins2nat_lt f0 f))) eqn:H.
   eapply (ap (@proj1_sig _ _)) in H. rewrite f2n_n2f in H. simpl in H.
   revert l. rewrite <- H. intro. now rewrite n2fs_unfold.
  -simpl subst_type. unfold encode. apply utype.congr_all. apply IHt1. rewrite IHt2. eapply ext_subst.
   intros. destruct x. simpl. unfold encode_subst. destruct (le_lt_dec (S ntype) 0); now simpl.
   simpl. unfold unscoped.funcomp. unfold encode_subst. destruct (le_lt_dec ntype x). lia.
   destruct (le_lt_dec (S ntype) (S x)). lia. simpl.
   unfold funcomp. rewrite encoding_ren. apply ext_ren. intros.
   unfold encode_ren. destruct (le_lt_dec m x0). lia. simpl.
   destruct (fin2nat (nat2fin l1)) eqn:Hf2n. f_equal. auto. rewrite <- (@f2n_n2f _ _ l1).
   now rewrite Hf2n. 
Qed.

End polyadic.