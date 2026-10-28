(** Invalid scalar metadata is rejected before any input or session access. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem rename_length_rejected_wp session id label labelLen issuer issuerLen (P : iProp Σ) :
 ~(1 <= labelLen <= 128 /\ 0 <= issuerLen <= 128) ->
 P -∗ WP call rename_body [pv session;int id;pv label;int labelLen;pv issuer;int issuerLen]
 {{u, ⌜u = LitV (LitBool false)⌝ ∗ P}}.
Proof.
 intros Hinvalid. iIntros "HP".
 unfold call at 1. unfold rename_body,args. hm_args. iApply wp_app. hm_pure.
 match goal with |- envs_entails _ (WP If (Val (LitV (LitBool ?guard))) _ _ {{_}}) =>
 assert (Hguard : guard = false) end.
 { apply Bool.not_true_is_false. repeat rewrite Bool.andb_true_iff.
   intros [[Hlo Hhi] [Hilo Hihi]].
   apply bool_decide_eq_true in Hlo,Hhi,Hilo,Hihi. tauto. }
 rewrite Hguard. iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
Theorem enroll_parameters_rejected_wp session label labelLen issuer issuerLen secret secretLen digits period (P : iProp Σ) :
 ~(valid_parameters digits period /\ 1 <= labelLen <= 128 /\
    0 <= issuerLen <= 128 /\ 2 <= secretLen <= 208) ->
 P -∗ WP call add_body [pv session;pv label;int labelLen;pv issuer;int issuerLen;
     pv secret;int secretLen;int digits;int period]
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ P}}.
Proof.
 intros Hinvalid. iIntros "HP".
 unfold call at 1. unfold add_body,args. hm_args. iApply wp_app. hm_pure.
 destruct (bool_decide (digits=6)) eqn:Hd6;
 [iApply wp_if_true|iApply wp_if_false]; hm_pure.
 all: match goal with |- envs_entails _ (WP If (Val (LitV (LitBool ?guard))) _ _ {{_}}) =>
 assert (Hguard : guard = false) end.
 all: try (apply Bool.not_true_is_false; repeat rewrite Bool.andb_true_iff;
   intros Hguard; repeat match goal with H : _ /\ _ |- _ => destruct H end;
   repeat match goal with H : bool_decide _ = true |- _ => apply bool_decide_eq_true in H end;
   apply Hinvalid; unfold valid_parameters; tauto).
 all: rewrite Hguard; iApply wp_if_false; iApply wp_value'; iFrame; done.
Qed.
End proofs.
