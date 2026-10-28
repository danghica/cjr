(** Preparation of the padded HMAC key, parameterized by SHA-1. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory crypto_bounds.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition prepare_hmac_key p n kb :=
 If (le (int n) (int 64)) (copy (pv p) (pv kb) (int n))
 (Seq (call sha_body [pv p;int n;pv kb]) unit_e).
Lemma replicate_repeat_zero n : replicate n 0%Z = repeat 0%Z n.
Proof. induction n; simpl; [done|rewrite IHn; done]. Qed.
Opaque sha_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem prepare_hmac_key_wp p key kb :
 (length key <= 128)%nat ->
 (array.array_cells p key -∗ array.array_cells kb (replicate 64 0%Z) -∗
 WP call sha_body [pv p;int (Z.of_nat (length key));pv kb]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells p key ∗
 array.array_cells kb (sha1 key ++ replicate 44 0%Z)}}) ->
 array.array_cells p key -∗ array.array_cells kb (replicate 64 0%Z) -∗
 WP prepare_hmac_key p (Z.of_nat (length key)) kb
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p key ∗ array.array_cells kb (hmac_key_block key)}}.
Proof.
 intros Hlen Hsha. iIntros "Hkey Hkb". unfold prepare_hmac_key, le, op.
 iApply (wp_bind [IfCtx _ _]). iApply wp_binop; [reflexivity|]. iIntros "!> _".
 destruct (le_dec (length key) 64) as [Hshort|Hlong].
 - rewrite bool_decide_true; last lia. iApply wp_if_true.
   iApply (wp_wand with "[Hkey Hkb]").
   { iApply (copy_wp with "Hkey Hkb"); simpl; lia. }
   iIntros (u) "[%Hu [Hkey Hkb]]". iFrame "Hkey". iSplit; [done|].
   unfold hmac_key_block, hmac_key. assert (Htest : (64 <? length key)%nat = false) by (apply Nat.ltb_ge; lia). rewrite Htest.
   rewrite take_ge; last lia. rewrite drop_replicate. rewrite <- replicate_repeat_zero. iExact "Hkb".
 - rewrite bool_decide_false; last lia. iApply wp_if_false.
   iApply (wp_bind [SeqCtx unit_e]). iApply (wp_wand with "[Hkey Hkb]").
   { iApply (Hsha with "Hkey Hkb"). }
   iIntros (u) "[%Hu [Hkey Hkb]]". subst u. iApply wp_seq. iApply wp_value'.
   iFrame "Hkey". iSplit; [done|].
   unfold hmac_key_block, hmac_key. assert (Htest : (64 <? length key)%nat = true) by (apply Nat.ltb_lt; lia). rewrite Htest.
   rewrite sha1_output_length. rewrite <- replicate_repeat_zero. iExact "Hkb".
Qed.
End proofs.
