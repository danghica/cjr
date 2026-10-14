(** Invalid arguments return before any raw-buffer access. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics array.
From cjr.aes_ige Require Import program memory syntax ige_syntax.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Opaque encrypt_branch decrypt_branch ige_iteration.
Ltac reject_admin := iStartProof; repeat (cbn [fill fill_item]; simpl;
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) =>
 hm_focus e ltac:(fun _ => first [iApply wp_if_true|iApply wp_if_false|hm_head]) end);
 cbn [fill fill_item]; simpl.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem encrypt_invalid_rounds_wp p q s nr w : nr <> 10 -> nr <> 12 -> nr <> 14 ->
 ⊢ WP invoke encrypt_body [pv p;pv q;pv s;int nr;pv w] {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros H10 H12 H14. unfold invoke, encrypt_body, args, choose_rounds, pv, int, eq, bool_e.
 reject_admin. rewrite bool_decide_false; [|exact H10]. iApply wp_if_false.
 reject_admin. rewrite bool_decide_false; [|exact H12]. iApply wp_if_false.
 reject_admin. rewrite bool_decide_false; [|exact H14]. iApply wp_if_false.
 reject_admin. done.
Qed.
Theorem decrypt_invalid_rounds_wp p q s nr w : nr <> 10 -> nr <> 12 -> nr <> 14 ->
 ⊢ WP invoke decrypt_body [pv p;pv q;pv s;int nr;pv w] {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros H10 H12 H14. unfold invoke, decrypt_body, args, choose_rounds, pv, int, eq, bool_e.
 reject_admin. rewrite bool_decide_false; [|exact H10]. iApply wp_if_false.
 reject_admin. rewrite bool_decide_false; [|exact H12]. iApply wp_if_false.
 reject_admin. rewrite bool_decide_false; [|exact H14]. iApply wp_if_false.
 reject_admin. done.
Qed.
Theorem ige_invalid_length_wp enc p q n vptr s nr w : n < 0 \/ Z.rem n 16 <> 0 ->
 ⊢ WP invoke (ige_body enc) [pv p;pv q;int n;pv vptr;pv s;int nr;pv w]
 {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros Hbad. unfold invoke, ige_body, args, pv, int, eq, le, bool_e.
 reject_admin. destruct (decide (0 <= n)) as [Hn|Hn].
 - rewrite bool_decide_true; [|exact Hn]. iApply wp_if_true. reject_admin.
   rewrite bool_decide_false; [|destruct Hbad; lia]. iApply wp_if_false.
   reject_admin. done.
 - rewrite bool_decide_false; [|exact Hn]. iApply wp_if_false. reject_admin. done.
Qed.
Theorem ige_invalid_rounds_wp enc p q n vptr s nr w : nr <> 10 -> nr <> 12 -> nr <> 14 ->
 ⊢ WP invoke (ige_body enc) [pv p;pv q;int n;pv vptr;pv s;int nr;pv w]
 {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros H10 H12 H14. destruct (decide (0 <= n)) as [Hn|Hn].
 2: { iApply ige_invalid_length_wp. left. lia. }
 destruct (decide (Z.rem n 16 = 0)) as [Hrem|Hrem].
 2: { iApply ige_invalid_length_wp. right. exact Hrem. }
 unfold invoke, ige_body, args, pv, int, eq, le, bool_e, valid_rounds.
 reject_admin. rewrite bool_decide_true; [|exact Hn]. iApply wp_if_true.
 reject_admin. rewrite Hrem. reject_admin.
 rewrite bool_decide_false; [|exact H10]. iApply wp_if_false. reject_admin.
 rewrite bool_decide_false; [|exact H12]. iApply wp_if_false. reject_admin.
 rewrite bool_decide_false; [|exact H14]. iApply wp_if_false. reject_admin. done.
Qed.
End proofs.
