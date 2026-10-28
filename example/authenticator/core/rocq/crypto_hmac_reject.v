(** HMAC validates two input views sequentially, so they may overlap. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_hmac crypto_hmac_inputs crypto_hotp crypto_hmac_entry.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Opaque byte_body sha_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hmac_application_reject_bytes heap keyp key msgp msg dst :
 buffer_in heap keyp key -> buffer_in heap msgp msg ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat ->
 (~ Forall byte key \/ ~ Forall byte msg) ->
 input_cells heap -∗
 WP hmac_application keyp (Z.of_nat (length key)) msgp (Z.of_nat (length msg)) dst
 {{u, ⌜u = LitV (LitBool false)⌝ ∗ input_cells heap}}.
Proof.
 intros Hkeyview Hmsgview Hkeylen Hmsglen Hbad.
 iIntros "Hheap". unfold hmac_application. iApply wp_app.
 unfold hmac_body, args, range, both, le, pv, int, v, op. hmac_entry_admin.
 rewrite hmac_byte_closed_key hmac_byte_closed_keyLen hmac_byte_closed_msg hmac_byte_closed_msgLen hmac_byte_closed_dst.
 rewrite hmac_sha_closed_key hmac_sha_closed_keyLen hmac_sha_closed_msg hmac_sha_closed_msgLen hmac_sha_closed_dst.
 iApply (wp_bind [IfCtx _ _]). hmac_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap keyp key Hkeyview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u.
 hmac_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap msgp msg Hmsgview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u.
 hmac_args.
 assert (Hfalse : (bytes_test key && bytes_test msg)%bool = false).
 { destruct (bytes_test key) eqn:Hkeytest; destruct (bytes_test msg) eqn:Hmsgtest; try done.
   exfalso. destruct Hbad as [Hbad|Hbad]; apply Hbad, bytes_test_spec; assumption. }
 rewrite Hfalse. iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
End proofs.
