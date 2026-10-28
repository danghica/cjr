(** Rejection paths compose without allocating or modifying caller buffers. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_refinement crypto_hmac_reject crypto_hotp crypto_hotp_entry crypto_totp.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Opaque hmac_body byte_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hotp_application_reject_size key keyLen counter digits :
 keyLen < 1 \/ 128 < keyLen ->
 ⊢ WP hotp_application key keyLen counter digits {{u, ⌜u = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hbad. unfold hotp_application. iApply wp_app.
 unfold hotp_body, args, range, both, le, eq, int, v, op.
 destruct (decide (1 <= keyLen)); destruct (decide (keyLen <= 128));
 destruct (decide (digits = 6)); try lia; auth_pure; done.
Qed.
Theorem totp_application_reject_size key keyLen timestamp period digits :
 keyLen < 1 \/ 128 < keyLen -> valid_parameters digits period -> 0 <= timestamp ->
 ⊢ WP totp_application key keyLen timestamp period digits {{u, ⌜u = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hbad Hparams Htime.
 iApply (totp_application_from_hotp_wp key keyLen timestamp period digits emp%I
   (fun u => ⌜u = LitV (LitInt (-1))⌝)%I with "[] []"); try assumption.
 - iIntros "_". iApply hotp_application_reject_size. exact Hbad.
 - done.
Qed.
Theorem totp_call_reject_key_size key keyLen timestamp period digits :
 keyLen < 1 \/ 128 < keyLen ->
 ⊢ WP call totp_body [pv key;int keyLen;int timestamp;int period;int digits]
 {{u, ⌜u = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hbad. destruct (decide (valid_parameters digits period /\ 0 <= timestamp)) as [[Hp Ht]|Hinvalid].
 - unfold call, pv, int. hm_args. iApply totp_application_reject_size; assumption.
 - iApply totp_reject_parameters. unfold valid_parameters in Hinvalid. lia.
Qed.
Theorem hotp_call_reject_bytes p key counter digits :
 (1 <= length key <= 128)%nat -> 0 <= counter -> digits = 6 \/ digits = 8 ->
 ~ Forall byte key ->
 array.array_cells p key -∗
 WP call hotp_body [pv p;int (Z.of_nat (length key));int counter;int digits]
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hcounter Hdigits Hbytes. iIntros "Hkey".
 unfold call, pv, int. hm_args. iApply (hotp_application_reject_bytes with "Hkey"); assumption.
Qed.
Theorem hmac_call_reject_bytes heap keyp key msgp msg dst :
 buffer_in heap keyp key -> buffer_in heap msgp msg ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat ->
 (~ Forall byte key \/ ~ Forall byte msg) ->
 input_cells heap -∗
 WP call hmac_body [pv keyp;int (Z.of_nat (length key));pv msgp;int (Z.of_nat (length msg));pv dst]
 {{u, ⌜u = LitV (LitBool false)⌝ ∗ input_cells heap}}.
Proof.
 intros Hkeyview Hmsgview Hlen Hmsglen Hbad. iIntros "Hheap".
 unfold call, pv, int. hm_args. iApply (hmac_application_reject_bytes with "Hheap"); assumption.
Qed.
End proofs.
