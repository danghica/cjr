(** SHA-1 refinement suffices for complete HMAC/HOTP/TOTP success contracts.
    SHA-1 is an explicit premise, and must be instantiated by its heap proof. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_hmac crypto_hmac_entry crypto_hotp crypto_hotp_entry crypto_totp.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hmac_call_inputs_sha_wp heap keyp key msgp msg dst old :
 buffer_in heap keyp key -> buffer_in heap msgp msg -> sha_refinement ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 input_cells heap -∗ array.array_cells dst old -∗
 WP call hmac_body [pv keyp;int (Z.of_nat (length key));pv msgp;int (Z.of_nat (length msg));pv dst]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ input_cells heap ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hkeyview Hmsgview Hsha Hlen Hmsglen Hold Hkeybytes Hmsgbytes.
 iIntros "Hheap Hd". unfold call, pv, int. hm_args.
 iApply (hmac_application_inputs_wp with "Hheap Hd"); assumption.
Qed.
Theorem hmac_call_sha_wp keyp key msgp msg dst old :
 sha_refinement ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 array.array_cells keyp key -∗ array.array_cells msgp msg -∗ array.array_cells dst old -∗
 WP call hmac_body [pv keyp;int (Z.of_nat (length key));pv msgp;int (Z.of_nat (length msg));pv dst]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells keyp key ∗ array.array_cells msgp msg ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hsha Hlen Hmsglen Hold Hkeybytes Hmsgbytes.
 iIntros "Hkey Hmsg Hd". unfold call, pv, int. hm_args.
 iApply (hmac_application_wp with "Hkey Hmsg Hd"); assumption.
Qed.
Theorem hotp_sha_wp p key counter digits :
 sha_refinement -> (1 <= length key <= 128)%nat -> 0 <= counter ->
 digits = 6 \/ digits = 8 -> Forall byte key ->
 array.array_cells p key -∗
 WP hotp_application p (Z.of_nat (length key)) counter digits
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hsha Hkeylen Hcounter Hdigits Hbytes. iIntros "Hkey".
 iApply (hotp_application_wp with "Hkey"); try assumption.
 intros msg dst message old Hmessage Hold Hmessagebytes.
 iIntros "Hkey Hmsg Hd". iApply (wp_wand with "[Hkey Hmsg Hd]").
 { pose proof (hmac_application_wp p key msg message dst old Hsha Hkeylen
     ltac:(lia) ltac:(lia) Hbytes Hmessagebytes) as Hmac.
   rewrite Hmessage in Hmac. iApply (Hmac with "Hkey Hmsg Hd"). }
 iIntros (u) "[%Hu [Hkey [Hmsg Hd]]]". iFrame "Hkey Hmsg". iSplit; [done|].
 rewrite drop_ge; last lia. rewrite app_nil_r. iExact "Hd".
Qed.
Theorem hotp_call_sha_wp p key counter digits :
 sha_refinement -> (1 <= length key <= 128)%nat -> 0 <= counter ->
 digits = 6 \/ digits = 8 -> Forall byte key ->
 array.array_cells p key -∗
 WP call hotp_body [pv p;int (Z.of_nat (length key));int counter;int digits]
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hsha Hkeylen Hcounter Hdigits Hbytes. iIntros "Hkey".
 iApply hotp_call_from_application_wp. iApply (hotp_sha_wp with "Hkey"); assumption.
Qed.
Theorem totp_sha_wp p key timestamp period digits :
 sha_refinement -> (1 <= length key <= 128)%nat -> Forall byte key ->
 valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP totp_application p (Z.of_nat (length key)) timestamp period digits
 {{u, ⌜u = LitV (LitInt (totp key timestamp period digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hsha Hlen Hbytes Hparams Htime. iIntros "Hkey".
 iApply (totp_application_from_hotp_wp with "[] Hkey"); try assumption.
 iIntros "Hkey". iApply (hotp_sha_wp with "Hkey"); try assumption.
 - apply Z.quot_pos; destruct Hparams as [_ Hp]; lia.
 - destruct Hparams as [Hd _]. exact Hd.
Qed.
Theorem totp_call_sha_wp p key timestamp period digits :
 sha_refinement -> (1 <= length key <= 128)%nat -> Forall byte key ->
 valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP call totp_body [pv p;int (Z.of_nat (length key));int timestamp;int period;int digits]
 {{u, ⌜u = LitV (LitInt (totp key timestamp period digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hsha Hlen Hbytes Hparams Htime. iIntros "Hkey".
 unfold call, pv, int. hm_args. iApply (totp_sha_wp with "Hkey"); assumption.
Qed.
Theorem totp_reject_bytes_wp p key timestamp period digits :
 (1 <= length key <= 128)%nat -> ~ Forall byte key ->
 valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP totp_application p (Z.of_nat (length key)) timestamp period digits
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hbytes Hparams Htime. iIntros "Hkey".
 iApply (totp_application_from_hotp_wp with "[] Hkey"); try assumption.
 iIntros "Hkey". iApply (hotp_application_reject_bytes with "Hkey"); try assumption.
 - apply Z.quot_pos; destruct Hparams as [_ Hp]; lia.
 - destruct Hparams as [Hd _]. exact Hd.
Qed.
Theorem totp_call_reject_bytes_wp p key timestamp period digits :
 (1 <= length key <= 128)%nat -> ~ Forall byte key ->
 valid_parameters digits period -> 0 <= timestamp ->
 array.array_cells p key -∗
 WP call totp_body [pv p;int (Z.of_nat (length key));int timestamp;int period;int digits]
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hbytes Hparams Htime. iIntros "Hkey".
 unfold call, pv, int. hm_args. iApply (totp_reject_bytes_wp with "Hkey"); assumption.
Qed.
End proofs.
