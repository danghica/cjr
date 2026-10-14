(** Buffer ownership and concrete CJR transformation contracts. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.aes_ige Require Import bytes block program refinement.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition pv p := Val (LitV (LitPtr p)).
Definition block_at `{!cjrGS Σ} (p : Z) (b : block) : iProp Σ :=
  RawId (p+0) ↦ᵣ LitV (LitInt (a0 (c0 b))) ∗
  RawId (p+1) ↦ᵣ LitV (LitInt (a1 (c0 b))) ∗
  RawId (p+2) ↦ᵣ LitV (LitInt (a2 (c0 b))) ∗
  RawId (p+3) ↦ᵣ LitV (LitInt (a3 (c0 b))) ∗
  RawId (p+4) ↦ᵣ LitV (LitInt (a0 (c1 b))) ∗
  RawId (p+5) ↦ᵣ LitV (LitInt (a1 (c1 b))) ∗
  RawId (p+6) ↦ᵣ LitV (LitInt (a2 (c1 b))) ∗
  RawId (p+7) ↦ᵣ LitV (LitInt (a3 (c1 b))) ∗
  RawId (p+8) ↦ᵣ LitV (LitInt (a0 (c2 b))) ∗
  RawId (p+9) ↦ᵣ LitV (LitInt (a1 (c2 b))) ∗
  RawId (p+10) ↦ᵣ LitV (LitInt (a2 (c2 b))) ∗
  RawId (p+11) ↦ᵣ LitV (LitInt (a3 (c2 b))) ∗
  RawId (p+12) ↦ᵣ LitV (LitInt (a0 (c3 b))) ∗
  RawId (p+13) ↦ᵣ LitV (LitInt (a1 (c3 b))) ∗
  RawId (p+14) ↦ᵣ LitV (LitInt (a2 (c3 b))) ∗
  RawId (p+15) ↦ᵣ LitV (LitInt (a3 (c3 b))).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma sbox_app_wp x : byte x ->
 ⊢ WP App (Val (RecV None (Some "x") sbox_body)) (int x)
 {{v, ⌜v = LitV (LitInt (sbox x))⌝}}.
Proof. intros H. iApply wp_app. rewrite <- (sbox_table_value x H). iApply groups_wp. Qed.
Lemma inv_sbox_app_wp x : byte x ->
 ⊢ WP App (Val (RecV None (Some "x") inv_sbox_body)) (int x)
 {{v, ⌜v = LitV (LitInt (inv_sbox x))⌝}}.
Proof. intros H. iApply wp_app. rewrite <- (inv_sbox_table_value x H). iApply groups_wp. Qed.
Lemma xtime_app_wp x : byte x ->
 ⊢ WP App (Val (RecV None (Some "x") xtime_body)) (int x)
 {{v, ⌜v = LitV (LitInt (xtime x))⌝}}.
Proof.
 intros H. rewrite <- (xtime_correspondence x H). iApply wp_app.
 unfold xtime_body, xtime_arith. hm_pure.
 destruct (decide (Z.land x 128 = 0)) as [E|E].
 - rewrite bool_decide_true; last done. iApply wp_if_true.
   rewrite (proj2 (Z.eqb_eq _ _) E). iApply wp_value'; done.
 - rewrite bool_decide_false; last done. iApply wp_if_false.
   rewrite (proj2 (Z.eqb_neq _ _) E). hm_pure. done.
Qed.
Lemma sbox_body_src_closed v : subst "src" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite sbox_body_src_closed : aes_subst.
Lemma sbox_body_dst_closed v : subst "dst" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite sbox_body_dst_closed : aes_subst.
Lemma sbox_body_args_closed v : subst "args" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite sbox_body_args_closed : aes_subst.
Lemma inv_sbox_body_src_closed v : subst "src" v inv_sbox_body = inv_sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite inv_sbox_body_src_closed : aes_subst.
Lemma inv_sbox_body_dst_closed v : subst "dst" v inv_sbox_body = inv_sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite inv_sbox_body_dst_closed : aes_subst.
Lemma inv_sbox_body_args_closed v : subst "args" v inv_sbox_body = inv_sbox_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite inv_sbox_body_args_closed : aes_subst.
Lemma xtime_body_src_closed v : subst "src" v xtime_body = xtime_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite xtime_body_src_closed : aes_subst.
Lemma xtime_body_dst_closed v : subst "dst" v xtime_body = xtime_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite xtime_body_dst_closed : aes_subst.
Lemma xtime_body_args_closed v : subst "args" v xtime_body = xtime_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite xtime_body_args_closed : aes_subst.
Opaque sbox_body inv_sbox_body xtime_body.
Ltac byte_goal := repeat first [tauto | apply bx_byte | apply sbox_byte | apply inv_sbox_byte | apply xtime_byte].
Ltac aes_head := first [
  match goal with
  | |- envs_entails _ (WP App (Val (RecV None (Some "x") sbox_body)) (Val (LitV (LitInt ?x))) {{_}}) =>
      iApply (wp_wand with "[]"); [iApply sbox_app_wp; byte_goal|iIntros (?) "%E"; subst]
  | |- envs_entails _ (WP App (Val (RecV None (Some "x") inv_sbox_body)) (Val (LitV (LitInt ?x))) {{_}}) =>
      iApply (wp_wand with "[]"); [iApply inv_sbox_app_wp; byte_goal|iIntros (?) "%E"; subst]
  | |- envs_entails _ (WP App (Val (RecV None (Some "x") xtime_body)) (Val (LitV (LitInt ?x))) {{_}}) =>
      iApply (wp_wand with "[]"); [iApply xtime_app_wp; byte_goal|iIntros (?) "%E"; subst]
  | |- envs_entails _ (WP Load (Val (LitV (LitPtr ?p))) {{_}}) =>
      iApply (wp_load p with "[$]"); iIntros "!> _ ?"
  | |- envs_entails _ (WP Store (Val (LitV (LitPtr ?p))) (Val ?v) {{_}}) =>
      iApply (wp_store p with "[$]"); iIntros "!> _ ?"
  end | hm_head ].
Ltac aes_run := iStartProof; repeat (simpl; autorewrite with aes_subst; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => aes_head) end);
 simpl; cbn [fill fill_item].
Theorem copy_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP invoke copy_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (b)}}.
Proof.
  block_destruct b; block_destruct old.
 
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, copy_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, xor, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem shift_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP invoke shift_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (shift_rows b)}}.
Proof.
  block_destruct b; block_destruct old.
 
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, shift_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, shift_rows, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem inv_shift_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP invoke inv_shift_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (inv_shift_rows b)}}.
Proof.
  block_destruct b; block_destruct old.
 
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, inv_shift_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, inv_shift_rows, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem sub_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP invoke sub_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (sub_bytes b)}}.
Proof.
 intros Hb. block_destruct b; block_destruct old.
 unfold block_bytes, column_bytes in Hb; simpl in Hb.
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, sub_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, sub_bytes, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem inv_sub_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP invoke inv_sub_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (inv_sub_bytes b)}}.
Proof.
 intros Hb. block_destruct b; block_destruct old.
 unfold block_bytes, column_bytes in Hb; simpl in Hb.
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, inv_sub_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, inv_sub_bytes, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem mix_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP invoke mix_body [pv p; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at q (mix_columns b)}}.
Proof.
 intros Hb. block_destruct b; block_destruct old.
 unfold block_bytes, column_bytes in Hb; simpl in Hb.
 iIntros "Hs Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, mix_body, args, seqs, pv, put, get, ptr, int, unit_e,
   xb, eq, ab, plus, sb, isb, xt.
 aes_run. iSplit; [done|]. unfold block_at, mix_columns, bmap, cmap, mix; simpl; iFrame.
Qed.
Theorem xor_wp p k q b key old :
 block_at p b -∗ block_at k key -∗ block_at q old -∗
 WP invoke xor_body [pv p; pv k; pv q]
 {{v, ⌜v = LitV LitUnit⌝ ∗ block_at p b ∗ block_at k key ∗ block_at q (xor b key)}}.
Proof.
 block_destruct b; block_destruct key; block_destruct old.
 iIntros "Hs Hk Hd". iEval (unfold block_at; simpl) in "Hs".
 iEval (unfold block_at; simpl) in "Hk". iEval (unfold block_at; simpl) in "Hd".
 iDestruct "Hs" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hk" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)". iDestruct "Hd" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)".
 unfold invoke, xor_body, args, seqs, pv, put, get, ptr, int, unit_e, xb.
 aes_run. iSplit; [done|]. unfold block_at, xor, cxor; simpl; iFrame.
Qed.
End proofs.
