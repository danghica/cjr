(** Whole HOTP success contract, with an explicit HMAC implementation premise. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory crypto_hotp crypto_totp.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Lemma byte_closed_key x : subst "key" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma byte_closed_keyLen x : subst "keyLen" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma byte_closed_counter x : subst "counter" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma byte_closed_digits x : subst "digits" x byte_body = byte_body. Proof. reflexivity. Qed.
Transparent hmac_body hotp_body.
Lemma hmac_closed_key x : subst "key" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Lemma hmac_closed_keyLen x : subst "keyLen" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Lemma hmac_closed_counter x : subst "counter" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Lemma hmac_closed_digits x : subst "digits" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Opaque byte_body hmac_body.
Ltac hotp_entry_admin := iStartProof; repeat (
 simpl; cbn [fill fill_item];
 try (rewrite bool_decide_true; [|lia]);
 try (rewrite bool_decide_false; [|lia]);
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
 match goal with
 | |- envs_entails _ (WP If (Val (LitV (LitBool true))) _ _ {{_}}) => iApply wp_if_true
 | |- envs_entails _ (WP If (Val (LitV (LitBool false))) _ _ {{_}}) => iApply wp_if_false
 end | hm_admin_head]) end); simpl; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hotp_application_wp p key counter digits :
 (1 <= length key <= 128)%nat -> 0 <= counter ->
 digits = 6 \/ digits = 8 -> Forall model.byte key ->
 (forall msg dst message old,
  length message = 8%nat -> length old = 20%nat -> Forall byte message ->
  array.array_cells p key -∗ array.array_cells msg message -∗ array.array_cells dst old -∗
  WP hmac_application p (Z.of_nat (length key)) msg 8 dst
  {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells p key ∗ array.array_cells msg message ∗
   array.array_cells dst (hmac_sha1 key message)}}) ->
 array.array_cells p key -∗
 WP hotp_application p (Z.of_nat (length key)) counter digits
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hcounter Hdigits Hbytes Hhmac. iIntros "Hkey".
 unfold hotp_application. iApply wp_app.
 unfold hotp_body, args, range, both, le, eq, pv, int, v, op.
 hotp_entry_admin.
 rewrite byte_closed_key byte_closed_keyLen byte_closed_counter byte_closed_digits.
 rewrite hmac_closed_key hmac_closed_keyLen hmac_closed_counter hmac_closed_digits.
 destruct Hdigits as [Hdigits | Hdigits]; subst digits; hotp_entry_admin.
 all: iApply (wp_bind [IfCtx _ _]); iApply (wp_wand with "[Hkey]").
 all: try (iApply (bytes_wp p key (length key) with "Hkey"); lia).
 all: iIntros (u) "[%Hu Hkey]"; subst u.
 all: rewrite take_ge; last lia.
 all: assert (Htrue : bytes_test key = true) by (apply bytes_test_spec; exact Hbytes).
 all: rewrite Htrue; iApply wp_if_true.
 all: iApply (hotp_compute_wp with "Hkey"); [exact Hcounter|auto|exact Hhmac].
Qed.
Theorem hotp_application_reject_bytes p key counter digits :
 (1 <= length key <= 128)%nat -> 0 <= counter ->
 digits = 6 \/ digits = 8 -> ~ Forall model.byte key ->
 array.array_cells p key -∗
 WP hotp_application p (Z.of_nat (length key)) counter digits
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hlen Hcounter Hdigits Hbytes. iIntros "Hkey".
 unfold hotp_application. iApply wp_app.
 unfold hotp_body, args, range, both, le, eq, pv, int, v, op.
 hotp_entry_admin.
 rewrite byte_closed_key byte_closed_keyLen byte_closed_counter byte_closed_digits.
 rewrite hmac_closed_key hmac_closed_keyLen hmac_closed_counter hmac_closed_digits.
 destruct Hdigits as [Hdigits | Hdigits]; subst digits; hotp_entry_admin.
 all: iApply (wp_bind [IfCtx _ _]); iApply (wp_wand with "[Hkey]").
 all: try (iApply (bytes_wp p key (length key) with "Hkey"); lia).
 all: iIntros (u) "[%Hu Hkey]"; subst u.
 all: rewrite take_ge; last lia.
 all: assert (Hfalse : bytes_test key = false) by
  (destruct (bytes_test key) eqn:Htest; [exfalso; apply Hbytes, bytes_test_spec; exact Htest|reflexivity]).
 all: rewrite Hfalse; iApply wp_if_false; iApply wp_value'; iFrame; done.
Qed.
End proofs.
