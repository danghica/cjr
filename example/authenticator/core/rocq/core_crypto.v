(** Closed implementation contracts for the public cryptographic operations.
    The SHA-1 premise of the modular HMAC/OTP proofs is instantiated here by
    the actual verified SHA-1 routine. Caller inputs and destination suffixes
    are preserved; temporary allocations are freed by the implementation. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory
 crypto_hmac crypto_hmac_entry crypto_hotp crypto_hotp_entry crypto_totp
 crypto_composition crypto_reject_composition sha1_entry.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem core_sha1_wp src words dst old n :
 (n <= length words)%nat -> (n <= 2048)%nat -> (20 <= length old)%nat ->
 Forall byte (take n words) ->
 array.array_cells src words -∗ array.array_cells dst old -∗
 WP call sha_body [pv src;int (Z.of_nat n);pv dst]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells src words ∗
 array.array_cells dst (sha1 (take n words) ++ drop 20 old)}}.
Proof.
 intros Hn Hmax Hout Hbytes. iIntros "Hs Hd".
 iApply (sha_call_from_application with "Hs Hd"); try assumption.
 apply sha_refinement_proved.
Qed.
Theorem core_hmac_application_wp heap keyp key msgp msg dst old :
 buffer_in heap keyp key -> buffer_in heap msgp msg ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 input_cells heap -∗ array.array_cells dst old -∗
 WP hmac_application keyp (Z.of_nat (length key)) msgp (Z.of_nat (length msg)) dst
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ input_cells heap ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hkeyview Hmsgview Hlen Hmsglen Hold Hkeybytes Hmsgbytes. iIntros "Hheap Hd".
 iApply (hmac_application_inputs_wp with "Hheap Hd"); try assumption.
 apply sha_refinement_proved.
Qed.
Theorem core_hmac_wp heap keyp key msgp msg dst old :
 buffer_in heap keyp key -> buffer_in heap msgp msg ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 input_cells heap -∗ array.array_cells dst old -∗
 WP call hmac_body [pv keyp;int (Z.of_nat (length key));pv msgp;int (Z.of_nat (length msg));pv dst]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ input_cells heap ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hkeyview Hmsgview Hlen Hmsglen Hold Hkeybytes Hmsgbytes. iIntros "Hheap Hd".
 iApply (hmac_call_inputs_sha_wp with "Hheap Hd"); try assumption.
 apply sha_refinement_proved.
Qed.
Theorem core_hotp_application_wp p key counter digits :
 (1 <= length key <= 128)%nat -> 0 <= counter -> digits = 6 \/ digits = 8 -> Forall byte key ->
 array.array_cells p key -∗
 WP hotp_application p (Z.of_nat (length key)) counter digits
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hcounter Hdigits Hbytes. iIntros "Hkey".
 iApply (hotp_sha_wp with "Hkey"); try assumption. apply sha_refinement_proved.
Qed.
Theorem core_hotp_wp p key counter digits :
 (1 <= length key <= 128)%nat -> 0 <= counter -> digits = 6 \/ digits = 8 -> Forall byte key ->
 array.array_cells p key -∗
 WP call hotp_body [pv p;int (Z.of_nat (length key));int counter;int digits]
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hcounter Hdigits Hbytes. iIntros "Hkey".
 iApply (hotp_call_sha_wp with "Hkey"); try assumption. apply sha_refinement_proved.
Qed.
Theorem core_totp_application_wp p key timestamp period digits :
 (1 <= length key <= 128)%nat -> Forall byte key -> valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP totp_application p (Z.of_nat (length key)) timestamp period digits
 {{u, ⌜u = LitV (LitInt (totp key timestamp period digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hbytes Hparams Htime. iIntros "Hkey".
 iApply (totp_sha_wp with "Hkey"); try assumption. apply sha_refinement_proved.
Qed.
Theorem core_totp_wp p key timestamp period digits :
 (1 <= length key <= 128)%nat -> Forall byte key -> valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP call totp_body [pv p;int (Z.of_nat (length key));int timestamp;int period;int digits]
 {{u, ⌜u = LitV (LitInt (totp key timestamp period digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hbytes Hparams Htime. iIntros "Hkey".
 iApply (totp_call_sha_wp with "Hkey"); try assumption. apply sha_refinement_proved.
Qed.
End proofs.
