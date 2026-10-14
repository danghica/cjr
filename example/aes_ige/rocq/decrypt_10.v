(** Refinement of complete AES and IGE routines. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics array.
From cjr.aes_ige Require Import bytes block aes ige program refinement memory kernels routines.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Local Opaque block_at xor sub_bytes inv_sub_bytes shift_rows inv_shift_rows mix_columns inv_mix_columns encrypt_schedule decrypt_schedule encrypt_tail decrypt_tail round unround final_round unfinal_round.
Opaque sbox_body inv_sbox_body xtime_body copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma decrypt_10_body_wp p q s w b old a d k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 :
 block_bytes b -> Forall block_bytes [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] ->
 block_at p b -∗ block_at q old -∗ schedule_at s [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] -∗
 block_at w a -∗ block_at (w+16) d -∗
 WP subst "args" (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt 10); LitV (LitPtr w)]) decrypt_body
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗
 block_at q (decrypt_schedule [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] b) ∗ schedule_at s [k0;k1;k2;k3;k4;k5;k6;k7;k8;k9;k10] ∗ work_at w}}.
Proof.
 intros Hb Hks.
 repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
 iIntros "Hs Hd Hk Hw Ht".
 iEval (unfold schedule_at; rewrite !big_sepL_cons big_sepL_nil; cbn) in "Hk".
 iDestruct "Hk" as "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _)".
 unfold invoke, decrypt_body, args, choose_rounds, decrypt_branch, dec_round,
 ishift, isub, xx, imx, mx, rkey, work, tmp, seqs, pv, ptr, int, bool_e, unit_e, eq.
 complete_run. iSplit; [done|].
 Local Transparent decrypt_schedule decrypt_tail unround unfinal_round.
 cbn [decrypt_schedule decrypt_tail]. unfold unround, unfinal_round.
 Local Opaque decrypt_schedule decrypt_tail unround unfinal_round.
 unfold schedule_at, work_at. rewrite !big_sepL_cons big_sepL_nil.
 rewrite <- ?mix_three_inv.
 repeat match goal with H : @Logic.eq block ?state ?rhs |- _ =>
   is_var state; progress rewrite <- H
 end.
 iFrame; try (iExists _, _; iFrame).
Qed.
End proofs.
