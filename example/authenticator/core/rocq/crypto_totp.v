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

Lemma hotp_body_closed_key x : subst "key" x hotp_body = hotp_body. Proof. reflexivity. Qed.
Lemma hotp_body_closed_keyLen x : subst "keyLen" x hotp_body = hotp_body. Proof. reflexivity. Qed.
Lemma hotp_body_closed_timestamp x : subst "timestamp" x hotp_body = hotp_body. Proof. reflexivity. Qed.
Lemma hotp_body_closed_period x : subst "period" x hotp_body = hotp_body. Proof. reflexivity. Qed.
Lemma hotp_body_closed_digits x : subst "digits" x hotp_body = hotp_body. Proof. reflexivity. Qed.
Opaque hotp_body.
Ltac totp_admin := iStartProof; repeat (
 simpl; cbn [fill fill_item];
 try (rewrite bool_decide_true; [|lia]);
 try (rewrite bool_decide_false; [|lia]);
 match goal with |- envs_entails _ (WP ?e {{?Phi}}) => hm_focus e ltac:(fun _ => first [
 match goal with
 | |- envs_entails _ (WP BinOp DivOp (Val (LitV (LitInt _))) (Val (LitV (LitInt ?d))) {{_}}) =>
   iApply wp_div; [lia|iIntros "!> _"]
 | |- envs_entails _ (WP If (Val (LitV (LitBool true))) _ _ {{_}}) => iApply wp_if_true
 | |- envs_entails _ (WP If (Val (LitV (LitBool false))) _ _ {{_}}) => iApply wp_if_false
 end | hm_args_head]) end);
 simpl; cbn [fill fill_item].
Definition hotp_application key keyLen counter digits :=
 App (Val (RecV None (Some "args") hotp_body))
 (Val (StructV [LitV (LitPtr key);LitV (LitInt keyLen);LitV (LitInt counter);LitV (LitInt digits)])).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
(** A caller may keep any resources in [P]; the implementation only forwards
    the counter and the HOTP result. *)
Definition totp_application key keyLen timestamp period digits :=
 App (Val (RecV None (Some "args") totp_body))
 (Val (StructV [LitV (LitPtr key);LitV (LitInt keyLen);LitV (LitInt timestamp);LitV (LitInt period);LitV (LitInt digits)])).
Theorem totp_application_from_hotp_wp key keyLen timestamp period digits (P : iProp Σ) (Phi : val -> iProp Σ) :
 valid_parameters digits period -> 0 <= timestamp ->
 (P -∗ WP hotp_application key keyLen (Z.quot timestamp period) digits {{Phi}}) -∗
 P -∗ WP totp_application key keyLen timestamp period digits {{Phi}}.
Proof.
 intros [[Hd|Hd] Hp] Htimestamp; subst digits;
 iIntros "Hhotp HP"; unfold totp_body, args, parameters, range, both, le, eq;
 unfold totp_application; unfold call; unfold pv, int, v, op;
 iApply wp_app; simpl;
 totp_admin.
 all: rewrite hotp_body_closed_key hotp_body_closed_keyLen hotp_body_closed_timestamp hotp_body_closed_period hotp_body_closed_digits.
 all: iApply ("Hhotp" with "HP").
Qed.
Theorem totp_from_hotp_wp key keyLen timestamp period digits (P : iProp Σ) (Phi : val -> iProp Σ) :
 valid_parameters digits period -> 0 <= timestamp ->
 (P -∗ WP hotp_application key keyLen (Z.quot timestamp period) digits {{Phi}}) -∗
 P -∗ WP call totp_body [pv key; int keyLen; int timestamp; int period; int digits] {{Phi}}.
Proof.
 intros [[Hd|Hd] Hp] Htimestamp; subst digits;
 iIntros "Hhotp HP"; unfold totp_body, args, parameters, range, both, le, eq;
 unfold call; unfold pv, int, v, op;
 hm_args; iApply wp_app; simpl;
 totp_admin.
 all: rewrite hotp_body_closed_key hotp_body_closed_keyLen hotp_body_closed_timestamp hotp_body_closed_period hotp_body_closed_digits.
 all: iApply ("Hhotp" with "HP").
Qed.
Theorem hotp_call_from_application_wp key keyLen counter digits (Phi : val -> iProp Σ) :
 WP hotp_application key keyLen counter digits {{Phi}} -∗
 WP call hotp_body [pv key; int keyLen; int counter; int digits] {{Phi}}.
Proof.
 iIntros "H". unfold call, pv, int. hm_args. iExact "H".
Qed.
Theorem totp_model_from_hotp_wp p key timestamp period digits :
 valid_parameters digits period -> 0 <= timestamp ->
 (array.array_cells p key -∗
   WP hotp_application p (Z.of_nat (length key)) (Z.quot timestamp period) digits
   {{u, ⌜u = LitV (LitInt (model.hotp key (Z.quot timestamp period) digits))⌝ ∗ array.array_cells p key}}) -∗
 array.array_cells p key -∗
 WP call totp_body [pv p;int (Z.of_nat (length key));int timestamp;int period;int digits]
 {{u, ⌜u = LitV (LitInt (model.totp key timestamp period digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hp Ht. iIntros "Hhotp Hkey".
 iApply (totp_from_hotp_wp with "Hhotp Hkey"); assumption.
Qed.
End proofs.
