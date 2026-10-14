(** Checked Iris contracts for the concrete byte kernels. *)
From Coq Require Import ZArith String List Lia Bool.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.aes_ige Require Import bytes program.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition table_value (entries : list (nat * Z)) x :=
  fold_right (fun ni rest => if Z.eqb x (Z.of_nat (fst ni)) then snd ni else rest) 0 entries.
Definition table_term entries :=
  fold_right (fun ni rest => If (eq (Var "x") (int (Z.of_nat (fst ni))))
    (int (snd ni)) rest) (int 0) entries.
Lemma table_subst entries x : subst "x" (LitV (LitInt x)) (table_term entries) =
  fold_right (fun ni rest => If (eq (int x) (int (Z.of_nat (fst ni))))
    (int (snd ni)) rest) (int 0) entries.
Proof. induction entries as [|[n v] es IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma table_wp entries x :
  ⊢ WP subst "x" (LitV (LitInt x)) (table_term entries)
    {{ v, ⌜v = LitV (LitInt (table_value entries x))⌝ }}.
Proof.
  rewrite table_subst. induction entries as [|[n y] es IH]; simpl.
  - iApply wp_value'; done.
  - iApply (wp_bind [IfCtx (int y)
      (fold_right (fun ni rest => If (eq (int x) (int (Z.of_nat (fst ni)))) (int (snd ni)) rest) (int 0) es)]).
    iApply wp_binop; [reflexivity|]. iIntros "!> _".
    destruct (decide (x = Z.of_nat n)) as [E|E].
    + subst x. rewrite bool_decide_true; last done. iApply wp_if_true.
      rewrite Z.eqb_refl. iApply wp_value'; done.
    + rewrite bool_decide_false; last done. iApply wp_if_false.
      rewrite (proj2 (Z.eqb_neq _ _) E). iApply IH.
Qed.
Fixpoint group_value (fuel base : nat) table x :=
 match fuel with O => 0 | S fuel =>
 if Z.leb x (Z.of_nat (base+15)) then
   table_value (combine (seq base (length (firstn 16 table))) (firstn 16 table)) x
 else group_value fuel (base+16) (skipn 16 table) x end.
Lemma groups_wp fuel base table x :
 ⊢ WP subst "x" (LitV (LitInt x)) (table_groups fuel base table)
 {{ v, ⌜v = LitV (LitInt (group_value fuel base table x))⌝ }}.
Proof.
 revert base table. induction fuel as [|fuel IH]; intros base table; simpl.
 - iApply wp_value'; done.
 - iApply (wp_bind [IfCtx
     (subst "x" (LitV (LitInt x)) (table_leaf base (firstn 16 table)))
     (subst "x" (LitV (LitInt x)) (table_groups fuel (base+16) (skipn 16 table)))]).
   iApply wp_binop; [reflexivity|]. iIntros "!> _".
   destruct (decide (x <= Z.of_nat (base+15))) as [E|E].
   + rewrite bool_decide_true; last done. rewrite (proj2 (Z.leb_le _ _) E).
     iApply wp_if_true. iApply table_wp.
   + rewrite bool_decide_false; last done. rewrite (proj2 (Z.leb_gt x (Z.of_nat (base+15))) ltac:(lia)).
     iApply wp_if_false. iApply IH.
Qed.
Lemma sbox_table_value x : byte x -> group_value 16 0 sbox_table x = sbox x.
Proof.
 intros H. apply Z.eqb_eq.
 apply (byte_check (fun x => Z.eqb (group_value 16 0 sbox_table x) (sbox x))).
 - vm_compute. reflexivity.
 - exact H.
Qed.
Lemma inv_sbox_table_value x : byte x -> group_value 16 0 inv_sbox_table x = inv_sbox x.
Proof.
 intros H. apply Z.eqb_eq.
 apply (byte_check (fun x => Z.eqb (group_value 16 0 inv_sbox_table x) (inv_sbox x))).
 - vm_compute. reflexivity.
 - exact H.
Qed.
Theorem sbox_wp x : byte x ->
  ⊢ WP call1 sbox_body (int x) {{ v, ⌜v = LitV (LitInt (sbox x))⌝ }}.
Proof.
 intros H. unfold call1. iApply (wp_bind [AppLCtx (int x)]).
 iApply wp_rec. iIntros "!> _". iApply wp_app.
 rewrite <- (sbox_table_value x H). iApply groups_wp.
Qed.
Theorem inv_sbox_wp x : byte x ->
  ⊢ WP call1 inv_sbox_body (int x) {{ v, ⌜v = LitV (LitInt (inv_sbox x))⌝ }}.
Proof.
 intros H. unfold call1. iApply (wp_bind [AppLCtx (int x)]).
 iApply wp_rec. iIntros "!> _". iApply wp_app.
 rewrite <- (inv_sbox_table_value x H). iApply groups_wp.
Qed.
Definition xtime_arith x :=
 let d := Z.land (x+x) 255 in if Z.eqb (Z.land x 128) 0 then d else Z.lxor d 27.
Lemma xtime_correspondence x : byte x -> xtime_arith x = xtime x.
Proof. intros H. apply Z.eqb_eq.
 apply (byte_check (fun x => Z.eqb (xtime_arith x) (xtime x))).
 - vm_compute. reflexivity.
 - exact H.
Qed.
Theorem xtime_wp x : byte x ->
  ⊢ WP call1 xtime_body (int x) {{ v, ⌜v = LitV (LitInt (xtime x))⌝ }}.
Proof.
 intros H. rewrite <- (xtime_correspondence x H). unfold call1, xtime_body, xtime_arith.
 hm_pure. destruct (decide (Z.land x 128 = 0)) as [E|E].
 - rewrite bool_decide_true; last done. iApply wp_if_true.
   rewrite (proj2 (Z.eqb_eq _ _) E). iApply wp_value'; done.
 - rewrite bool_decide_false; last done. iApply wp_if_false.
   rewrite (proj2 (Z.eqb_neq _ _) E). hm_pure. done.
Qed.
End proofs.
