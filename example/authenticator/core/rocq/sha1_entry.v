(** Exported SHA-1 application contract: validation, prefix capacities, success and atomic rejection. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_hmac sha1_compute.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Lemma sha_byte_closed_src x : subst "src" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma sha_byte_closed_n x : subst "n" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma sha_byte_closed_dst x : subst "dst" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma sha_round_closed_src x : subst "src" x round_body = round_body. Proof. reflexivity. Qed.
Lemma sha_round_closed_n x : subst "n" x round_body = round_body. Proof. reflexivity. Qed.
Lemma sha_round_closed_dst x : subst "dst" x round_body = round_body. Proof. reflexivity. Qed.
#[local] Hint Rewrite sha_byte_closed_src sha_byte_closed_n sha_byte_closed_dst
 sha_round_closed_src sha_round_closed_n sha_round_closed_dst : entry_subst.
Opaque byte_body round_body model.sha1.
Ltac sha_entry_admin := iStartProof; repeat (
 simpl; autorewrite with entry_subst; cbn [fill fill_item];
 try (rewrite bool_decide_true; [|lia]);
 try (rewrite bool_decide_false; [|lia]);
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
 match goal with
 | |- envs_entails _ (WP If (Val (LitV (LitBool true))) _ _ {{_}}) => iApply wp_if_true
 | |- envs_entails _ (WP If (Val (LitV (LitBool false))) _ _ {{_}}) => iApply wp_if_false
 end | hm_admin_head]) end); simpl; autorewrite with entry_subst; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem sha_application_success_wp p words q dst n :
 (n <= length words)%nat -> (n <= 2048)%nat -> (20 <= length dst)%nat ->
 Forall model.byte (take n words) ->
 array.array_cells p words -∗ array.array_cells q dst -∗
 WP sha_application p (Z.of_nat n) q
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells p words ∗
   array.array_cells q (model.sha1 (take n words) ++ drop 20 dst)}}.
Proof.
 intros Hn Hmax Hdst Hbytes. iIntros "Hs Hd". unfold sha_application. iApply wp_app.
 unfold sha_body, args, range, both, le, pv, int, v, op. sha_entry_admin.
 iApply (wp_bind [IfCtx _ _]). hm_args. autorewrite with entry_subst.
 iApply (wp_wand with "[Hs]").
 { iApply (bytes_reduced_wp p words n with "Hs"). exact Hn. }
 iIntros (u) "[%Hu Hs]". subst u.
 assert (Hgood : bytes_test (take n words) = true) by (apply bytes_test_spec;exact Hbytes).
 rewrite Hgood. iApply wp_if_true.
 iDestruct (cells_slice_acc p words 0 n with "Hs") as "[Hs Hclose]"; first lia.
 iEval (rewrite ?drop_0 ?Z.add_0_r) in "Hs Hclose".
 iApply (wp_wand with "[Hs Hd]").
 { assert (Hprefix : length (take n words) = n) by (rewrite length_take Nat.min_l;lia).
   assert (Hbound : (length (take n words) <= 2048)%nat) by lia.
   pose proof (sha_compute_wp p (take n words) q dst Hbound Hdst) as Hcompute.
   rewrite Hprefix in Hcompute. iApply (Hcompute with "Hs Hd"). }
 iIntros (u) "[%Hu [Hs Hd]]".
 iDestruct ("Hclose" $! (take n words) with "[] Hs") as "Hs".
 { iPureIntro. rewrite length_take Nat.min_l;lia. }
 iEval (rewrite ?take_0 ?app_nil_l ?Nat.add_0_l take_drop) in "Hs".
 iFrame. done.
Qed.
Theorem sha_refinement_proved : sha_refinement.
Proof. intros p words q dst n Hn Hmax Hdst Hbytes. iApply sha_application_success_wp; done. Qed.
End proofs.
