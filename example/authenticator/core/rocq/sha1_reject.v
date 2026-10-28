(** SHA-1 rejection contracts never write to the destination or other framed memory. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_hmac sha1_entry.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
#[local] Hint Rewrite sha_byte_closed_src sha_byte_closed_n sha_byte_closed_dst
 sha_round_closed_src sha_round_closed_n sha_round_closed_dst : entry_subst.
Opaque byte_body round_body model.sha1.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem sha_application_reject_bytes_wp p words q n (P : iProp Σ) :
 (n <= length words)%nat -> (n <= 2048)%nat ->
 ~ Forall model.byte (take n words) ->
 array.array_cells p words -∗ P -∗
 WP sha_application p (Z.of_nat n) q
 {{u, ⌜u = LitV (LitBool false)⌝ ∗ array.array_cells p words ∗ P}}.
Proof.
 intros Hn Hmax Hbad. iIntros "Hs HP". unfold sha_application. iApply wp_app.
 unfold sha_body, args, range, both, le, pv, int, v, op. sha_entry_admin.
 iApply (wp_bind [IfCtx _ _]). hm_args. autorewrite with entry_subst.
 iApply (wp_wand with "[Hs]").
 { iApply (bytes_reduced_wp p words n with "Hs"). exact Hn. }
 iIntros (u) "[%Hu Hs]". subst u.
 assert (Hfalse : bytes_test (take n words) = false).
 { destruct (bytes_test (take n words)) eqn:Htest; last done.
   apply bytes_test_spec in Htest. contradiction. }
 rewrite Hfalse. iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
Theorem sha_application_reject_size_wp p n q (P : iProp Σ) : n < 0 \/ 2048 < n ->
 P -∗ WP sha_application p n q {{u, ⌜u = LitV (LitBool false)⌝ ∗ P}}.
Proof.
 intros Hbad. iIntros "HP". unfold sha_application. iApply wp_app.
 unfold sha_body, args, range, both, le, pv, int, v, op.
 destruct (decide (0 <= n)) as [Hlo|Hlo]; sha_entry_admin; iFrame; done.
Qed.
Theorem sha_call_reject_bytes_wp p words q n (P : iProp Σ) :
 (n <= length words)%nat -> (n <= 2048)%nat ->
 ~ Forall model.byte (take n words) ->
 array.array_cells p words -∗ P -∗
 WP call sha_body [pv p;int (Z.of_nat n);pv q]
 {{u, ⌜u = LitV (LitBool false)⌝ ∗ array.array_cells p words ∗ P}}.
Proof.
 intros Hn Hmax Hbad. iIntros "Hs HP". unfold call, pv, int. hm_args.
 iApply (sha_application_reject_bytes_wp with "Hs HP"); done.
Qed.
End proofs.
