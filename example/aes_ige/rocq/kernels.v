(** Complete routine refinement, built from the transformation contracts. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics array.
From cjr.aes_ige Require Import bytes block aes ige program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
#[local] Hint Rewrite memory.sbox_body_src_closed memory.sbox_body_dst_closed memory.sbox_body_args_closed memory.inv_sbox_body_src_closed memory.inv_sbox_body_dst_closed memory.inv_sbox_body_args_closed memory.xtime_body_src_closed memory.xtime_body_dst_closed memory.xtime_body_args_closed : aes_subst.
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
Opaque sbox_body inv_sbox_body xtime_body.
Lemma copy_app_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") copy_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma shift_app_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") shift_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma inv_shift_app_wp p q b old :
 
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") inv_shift_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma sub_app_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") sub_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma inv_sub_app_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") inv_sub_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma mix_app_wp p q b old :
 block_bytes b ->
 block_at p b -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") mix_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q)]))
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
Lemma xor_app_wp p k q b key old :
 block_at p b -∗ block_at k key -∗ block_at q old -∗
 WP App (Val (RecV None (Some "args") xor_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr k); LitV (LitPtr q)]))
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

Local Transparent sbox_body inv_sbox_body xtime_body.
Lemma copy_body_closed_src v : subst "src" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_src : complete_subst.
Lemma copy_body_closed_dst v : subst "dst" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_dst : complete_subst.
Lemma copy_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_schedule : complete_subst.
Lemma copy_body_closed_nr v : subst "nr" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_nr : complete_subst.
Lemma copy_body_closed_work v : subst "work" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_work : complete_subst.
Lemma copy_body_closed_args v : subst "args" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_args : complete_subst.
Lemma copy_body_closed_key v : subst "key" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_key : complete_subst.
Lemma copy_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_keyLen : complete_subst.
Lemma copy_body_closed_len v : subst "len" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_len : complete_subst.
Lemma copy_body_closed_iv v : subst "iv" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_iv : complete_subst.
Lemma copy_body_closed_i v : subst "i" v (Rec None (Some "args") copy_body) = Rec None (Some "args") copy_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite copy_body_closed_i : complete_subst.
Lemma xor_body_closed_src v : subst "src" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_src : complete_subst.
Lemma xor_body_closed_dst v : subst "dst" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_dst : complete_subst.
Lemma xor_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_schedule : complete_subst.
Lemma xor_body_closed_nr v : subst "nr" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_nr : complete_subst.
Lemma xor_body_closed_work v : subst "work" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_work : complete_subst.
Lemma xor_body_closed_args v : subst "args" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_args : complete_subst.
Lemma xor_body_closed_key v : subst "key" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_key : complete_subst.
Lemma xor_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_keyLen : complete_subst.
Lemma xor_body_closed_len v : subst "len" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_len : complete_subst.
Lemma xor_body_closed_iv v : subst "iv" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_iv : complete_subst.
Lemma xor_body_closed_i v : subst "i" v (Rec None (Some "args") xor_body) = Rec None (Some "args") xor_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite xor_body_closed_i : complete_subst.
Lemma sub_body_closed_src v : subst "src" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_src : complete_subst.
Lemma sub_body_closed_dst v : subst "dst" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_dst : complete_subst.
Lemma sub_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_schedule : complete_subst.
Lemma sub_body_closed_nr v : subst "nr" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_nr : complete_subst.
Lemma sub_body_closed_work v : subst "work" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_work : complete_subst.
Lemma sub_body_closed_args v : subst "args" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_args : complete_subst.
Lemma sub_body_closed_key v : subst "key" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_key : complete_subst.
Lemma sub_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_keyLen : complete_subst.
Lemma sub_body_closed_len v : subst "len" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_len : complete_subst.
Lemma sub_body_closed_iv v : subst "iv" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_iv : complete_subst.
Lemma sub_body_closed_i v : subst "i" v (Rec None (Some "args") sub_body) = Rec None (Some "args") sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite sub_body_closed_i : complete_subst.
Lemma inv_sub_body_closed_src v : subst "src" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_src : complete_subst.
Lemma inv_sub_body_closed_dst v : subst "dst" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_dst : complete_subst.
Lemma inv_sub_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_schedule : complete_subst.
Lemma inv_sub_body_closed_nr v : subst "nr" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_nr : complete_subst.
Lemma inv_sub_body_closed_work v : subst "work" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_work : complete_subst.
Lemma inv_sub_body_closed_args v : subst "args" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_args : complete_subst.
Lemma inv_sub_body_closed_key v : subst "key" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_key : complete_subst.
Lemma inv_sub_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_keyLen : complete_subst.
Lemma inv_sub_body_closed_len v : subst "len" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_len : complete_subst.
Lemma inv_sub_body_closed_iv v : subst "iv" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_iv : complete_subst.
Lemma inv_sub_body_closed_i v : subst "i" v (Rec None (Some "args") inv_sub_body) = Rec None (Some "args") inv_sub_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_sub_body_closed_i : complete_subst.
Lemma shift_body_closed_src v : subst "src" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_src : complete_subst.
Lemma shift_body_closed_dst v : subst "dst" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_dst : complete_subst.
Lemma shift_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_schedule : complete_subst.
Lemma shift_body_closed_nr v : subst "nr" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_nr : complete_subst.
Lemma shift_body_closed_work v : subst "work" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_work : complete_subst.
Lemma shift_body_closed_args v : subst "args" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_args : complete_subst.
Lemma shift_body_closed_key v : subst "key" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_key : complete_subst.
Lemma shift_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_keyLen : complete_subst.
Lemma shift_body_closed_len v : subst "len" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_len : complete_subst.
Lemma shift_body_closed_iv v : subst "iv" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_iv : complete_subst.
Lemma shift_body_closed_i v : subst "i" v (Rec None (Some "args") shift_body) = Rec None (Some "args") shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite shift_body_closed_i : complete_subst.
Lemma inv_shift_body_closed_src v : subst "src" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_src : complete_subst.
Lemma inv_shift_body_closed_dst v : subst "dst" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_dst : complete_subst.
Lemma inv_shift_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_schedule : complete_subst.
Lemma inv_shift_body_closed_nr v : subst "nr" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_nr : complete_subst.
Lemma inv_shift_body_closed_work v : subst "work" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_work : complete_subst.
Lemma inv_shift_body_closed_args v : subst "args" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_args : complete_subst.
Lemma inv_shift_body_closed_key v : subst "key" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_key : complete_subst.
Lemma inv_shift_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_keyLen : complete_subst.
Lemma inv_shift_body_closed_len v : subst "len" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_len : complete_subst.
Lemma inv_shift_body_closed_iv v : subst "iv" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_iv : complete_subst.
Lemma inv_shift_body_closed_i v : subst "i" v (Rec None (Some "args") inv_shift_body) = Rec None (Some "args") inv_shift_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite inv_shift_body_closed_i : complete_subst.
Lemma mix_body_closed_src v : subst "src" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_src : complete_subst.
Lemma mix_body_closed_dst v : subst "dst" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_dst : complete_subst.
Lemma mix_body_closed_schedule v : subst "schedule" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_schedule : complete_subst.
Lemma mix_body_closed_nr v : subst "nr" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_nr : complete_subst.
Lemma mix_body_closed_work v : subst "work" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_work : complete_subst.
Lemma mix_body_closed_args v : subst "args" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_args : complete_subst.
Lemma mix_body_closed_key v : subst "key" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_key : complete_subst.
Lemma mix_body_closed_keyLen v : subst "keyLen" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_keyLen : complete_subst.
Lemma mix_body_closed_len v : subst "len" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_len : complete_subst.
Lemma mix_body_closed_iv v : subst "iv" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_iv : complete_subst.
Lemma mix_body_closed_i v : subst "i" v (Rec None (Some "args") mix_body) = Rec None (Some "args") mix_body.
Proof. reflexivity. Qed.
#[export] Hint Rewrite mix_body_closed_i : complete_subst.
Lemma copy_body_subst_src v : subst "src" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_src : complete_subst.
Lemma copy_body_subst_dst v : subst "dst" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_dst : complete_subst.
Lemma copy_body_subst_schedule v : subst "schedule" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_schedule : complete_subst.
Lemma copy_body_subst_nr v : subst "nr" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_nr : complete_subst.
Lemma copy_body_subst_work v : subst "work" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_work : complete_subst.
Lemma copy_body_subst_key v : subst "key" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_key : complete_subst.
Lemma copy_body_subst_keyLen v : subst "keyLen" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_keyLen : complete_subst.
Lemma copy_body_subst_len v : subst "len" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_len : complete_subst.
Lemma copy_body_subst_iv v : subst "iv" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_iv : complete_subst.
Lemma copy_body_subst_i v : subst "i" v copy_body = copy_body.
Proof. pose proof (copy_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v copy_body) = Rec None (Some "args") copy_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite copy_body_subst_i : complete_subst.
Lemma xor_body_subst_src v : subst "src" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_src : complete_subst.
Lemma xor_body_subst_dst v : subst "dst" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_dst : complete_subst.
Lemma xor_body_subst_schedule v : subst "schedule" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_schedule : complete_subst.
Lemma xor_body_subst_nr v : subst "nr" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_nr : complete_subst.
Lemma xor_body_subst_work v : subst "work" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_work : complete_subst.
Lemma xor_body_subst_key v : subst "key" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_key : complete_subst.
Lemma xor_body_subst_keyLen v : subst "keyLen" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_keyLen : complete_subst.
Lemma xor_body_subst_len v : subst "len" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_len : complete_subst.
Lemma xor_body_subst_iv v : subst "iv" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_iv : complete_subst.
Lemma xor_body_subst_i v : subst "i" v xor_body = xor_body.
Proof. pose proof (xor_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v xor_body) = Rec None (Some "args") xor_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite xor_body_subst_i : complete_subst.
Lemma sub_body_subst_src v : subst "src" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_src : complete_subst.
Lemma sub_body_subst_dst v : subst "dst" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_dst : complete_subst.
Lemma sub_body_subst_schedule v : subst "schedule" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_schedule : complete_subst.
Lemma sub_body_subst_nr v : subst "nr" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_nr : complete_subst.
Lemma sub_body_subst_work v : subst "work" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_work : complete_subst.
Lemma sub_body_subst_key v : subst "key" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_key : complete_subst.
Lemma sub_body_subst_keyLen v : subst "keyLen" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_keyLen : complete_subst.
Lemma sub_body_subst_len v : subst "len" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_len : complete_subst.
Lemma sub_body_subst_iv v : subst "iv" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_iv : complete_subst.
Lemma sub_body_subst_i v : subst "i" v sub_body = sub_body.
Proof. pose proof (sub_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v sub_body) = Rec None (Some "args") sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite sub_body_subst_i : complete_subst.
Lemma inv_sub_body_subst_src v : subst "src" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_src : complete_subst.
Lemma inv_sub_body_subst_dst v : subst "dst" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_dst : complete_subst.
Lemma inv_sub_body_subst_schedule v : subst "schedule" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_schedule : complete_subst.
Lemma inv_sub_body_subst_nr v : subst "nr" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_nr : complete_subst.
Lemma inv_sub_body_subst_work v : subst "work" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_work : complete_subst.
Lemma inv_sub_body_subst_key v : subst "key" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_key : complete_subst.
Lemma inv_sub_body_subst_keyLen v : subst "keyLen" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_keyLen : complete_subst.
Lemma inv_sub_body_subst_len v : subst "len" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_len : complete_subst.
Lemma inv_sub_body_subst_iv v : subst "iv" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_iv : complete_subst.
Lemma inv_sub_body_subst_i v : subst "i" v inv_sub_body = inv_sub_body.
Proof. pose proof (inv_sub_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v inv_sub_body) = Rec None (Some "args") inv_sub_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_sub_body_subst_i : complete_subst.
Lemma shift_body_subst_src v : subst "src" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_src : complete_subst.
Lemma shift_body_subst_dst v : subst "dst" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_dst : complete_subst.
Lemma shift_body_subst_schedule v : subst "schedule" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_schedule : complete_subst.
Lemma shift_body_subst_nr v : subst "nr" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_nr : complete_subst.
Lemma shift_body_subst_work v : subst "work" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_work : complete_subst.
Lemma shift_body_subst_key v : subst "key" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_key : complete_subst.
Lemma shift_body_subst_keyLen v : subst "keyLen" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_keyLen : complete_subst.
Lemma shift_body_subst_len v : subst "len" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_len : complete_subst.
Lemma shift_body_subst_iv v : subst "iv" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_iv : complete_subst.
Lemma shift_body_subst_i v : subst "i" v shift_body = shift_body.
Proof. pose proof (shift_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v shift_body) = Rec None (Some "args") shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite shift_body_subst_i : complete_subst.
Lemma inv_shift_body_subst_src v : subst "src" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_src : complete_subst.
Lemma inv_shift_body_subst_dst v : subst "dst" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_dst : complete_subst.
Lemma inv_shift_body_subst_schedule v : subst "schedule" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_schedule : complete_subst.
Lemma inv_shift_body_subst_nr v : subst "nr" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_nr : complete_subst.
Lemma inv_shift_body_subst_work v : subst "work" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_work : complete_subst.
Lemma inv_shift_body_subst_key v : subst "key" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_key : complete_subst.
Lemma inv_shift_body_subst_keyLen v : subst "keyLen" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_keyLen : complete_subst.
Lemma inv_shift_body_subst_len v : subst "len" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_len : complete_subst.
Lemma inv_shift_body_subst_iv v : subst "iv" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_iv : complete_subst.
Lemma inv_shift_body_subst_i v : subst "i" v inv_shift_body = inv_shift_body.
Proof. pose proof (inv_shift_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v inv_shift_body) = Rec None (Some "args") inv_shift_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite inv_shift_body_subst_i : complete_subst.
Lemma mix_body_subst_src v : subst "src" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_src v) as H.
 change (Rec None (Some "args") (subst "src" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_src : complete_subst.
Lemma mix_body_subst_dst v : subst "dst" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_dst v) as H.
 change (Rec None (Some "args") (subst "dst" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_dst : complete_subst.
Lemma mix_body_subst_schedule v : subst "schedule" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_schedule v) as H.
 change (Rec None (Some "args") (subst "schedule" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_schedule : complete_subst.
Lemma mix_body_subst_nr v : subst "nr" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_nr v) as H.
 change (Rec None (Some "args") (subst "nr" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_nr : complete_subst.
Lemma mix_body_subst_work v : subst "work" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_work v) as H.
 change (Rec None (Some "args") (subst "work" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_work : complete_subst.
Lemma mix_body_subst_key v : subst "key" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_key v) as H.
 change (Rec None (Some "args") (subst "key" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_key : complete_subst.
Lemma mix_body_subst_keyLen v : subst "keyLen" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_keyLen v) as H.
 change (Rec None (Some "args") (subst "keyLen" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_keyLen : complete_subst.
Lemma mix_body_subst_len v : subst "len" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_len v) as H.
 change (Rec None (Some "args") (subst "len" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_len : complete_subst.
Lemma mix_body_subst_iv v : subst "iv" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_iv v) as H.
 change (Rec None (Some "args") (subst "iv" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_iv : complete_subst.
Lemma mix_body_subst_i v : subst "i" v mix_body = mix_body.
Proof. pose proof (mix_body_closed_i v) as H.
 change (Rec None (Some "args") (subst "i" v mix_body) = Rec None (Some "args") mix_body) in H. exact (f_equal (fun e => match e with Rec _ _ b => b | _ => unit_e end) H). Qed.
#[export] Hint Rewrite mix_body_subst_i : complete_subst.

Opaque sbox_body inv_sbox_body xtime_body copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.

Local Opaque xor sub_bytes inv_sub_bytes shift_rows inv_shift_rows mix_columns inv_mix_columns.
