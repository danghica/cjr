(** Closed cipher closures under IGE parameter substitution. *)
From Coq Require Import ZArith List String.
From cjr Require Import primitive_laws.
From cjr.aes_ige Require Import program kernels.
Import ListNotations.
Open Scope string_scope.
Opaque copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
Lemma encrypt_body_subst_src v : subst "src" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_dst v : subst "dst" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_len v : subst "len" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_iv v : subst "iv" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_schedule v : subst "schedule" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_nr v : subst "nr" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_work v : subst "work" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_subst_i v : subst "i" v encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma encrypt_body_stack_i l : subst_var "i" l encrypt_body = encrypt_body.
Proof. unfold encrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl.
Local Transparent copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
reflexivity.
Local Opaque copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
Qed.
Lemma decrypt_body_subst_src v : subst "src" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_dst v : subst "dst" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_len v : subst "len" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_iv v : subst "iv" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_schedule v : subst "schedule" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_nr v : subst "nr" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_work v : subst "work" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_subst_i v : subst "i" v decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl; autorewrite with complete_subst; reflexivity. Qed.
Lemma decrypt_body_stack_i l : subst_var "i" l decrypt_body = decrypt_body.
Proof. unfold decrypt_body, args, choose_rounds, encrypt_branch, decrypt_branch, enc_round, dec_round, sub, shift, mx, xx, imx, isub, ishift, seqs, invoke, ptr, rkey, work, tmp, int, eq, bool_e, unit_e; simpl.
Local Transparent copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
reflexivity.
Local Opaque copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
Qed.
