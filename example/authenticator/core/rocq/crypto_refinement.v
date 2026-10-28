(** Cryptographic boundary contracts and modular composition of TOTP.
    The modular theorem does not assert an unproved HOTP implementation: its
    supplied weakest precondition must be discharged by the HOTP refinement. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Opaque sha_body byte_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hmac_reject_size key keyLen msg msgLen dst :
 keyLen < 1 \/ 128 < keyLen \/ msgLen < 0 \/ 1024 < msgLen ->
 ⊢ WP call hmac_body [pv key; int keyLen; pv msg; int msgLen; pv dst]
 {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros Hbad. unfold call, hmac_body, args, range, both, le, pv, int, v, op.
 destruct (decide (1 <= keyLen)); destruct (decide (keyLen <= 128));
 destruct (decide (0 <= msgLen)); destruct (decide (msgLen <= 1024));
 try lia; auth_pure; done.
Qed.
Opaque hmac_body.
Theorem hotp_reject_parameters key keyLen counter digits :
 keyLen < 1 \/ 128 < keyLen \/ counter < 0 \/ (digits <> 6 /\ digits <> 8) ->
 ⊢ WP call hotp_body [pv key; int keyLen; int counter; int digits]
 {{v, ⌜v = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hbad. unfold call, hotp_body, args, range, both, le, eq, pv, int, v, op.
 destruct (decide (1 <= keyLen)); destruct (decide (keyLen <= 128));
 destruct (decide (0 <= counter)); destruct (decide (digits = 6));
 destruct (decide (digits = 8)); try lia; auth_pure; done.
Qed.
Opaque hotp_body.
Theorem totp_reject_parameters key keyLen timestamp period digits :
 timestamp < 0 \/ period < 1 \/ 2147483647 < period \/ (digits <> 6 /\ digits <> 8) ->
 ⊢ WP call totp_body [pv key; int keyLen; int timestamp; int period; int digits]
 {{v, ⌜v = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hbad. unfold call, totp_body, args, parameters, range, both, le, eq, pv, int, v, op.
 destruct (decide (1 <= period)); destruct (decide (period <= 2147483647));
 destruct (decide (0 <= timestamp)); destruct (decide (digits = 6));
 destruct (decide (digits = 8)); try lia; auth_pure; done.
Qed.
End proofs.
