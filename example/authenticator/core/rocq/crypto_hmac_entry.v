(** HMAC validates two input views sequentially, so they may overlap. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory input_memory crypto_hmac crypto_hmac_inputs crypto_hotp.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Lemma hmac_byte_closed_key x : subst "key" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma hmac_byte_closed_keyLen x : subst "keyLen" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma hmac_byte_closed_msg x : subst "msg" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma hmac_byte_closed_msgLen x : subst "msgLen" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma hmac_byte_closed_dst x : subst "dst" x byte_body = byte_body. Proof. reflexivity. Qed.
Lemma hmac_sha_closed_key x : subst "key" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma hmac_sha_closed_keyLen x : subst "keyLen" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma hmac_sha_closed_msg x : subst "msg" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma hmac_sha_closed_msgLen x : subst "msgLen" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma hmac_sha_closed_dst x : subst "dst" x sha_body = sha_body. Proof. reflexivity. Qed.
Opaque byte_body sha_body.
Ltac hmac_entry_admin := iStartProof; repeat (
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
Theorem hmac_application_inputs_wp heap keyp key msgp msg dst old :
 buffer_in heap keyp key -> buffer_in heap msgp msg -> sha_refinement ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 input_cells heap -∗ array.array_cells dst old -∗
 WP hmac_application keyp (Z.of_nat (length key)) msgp (Z.of_nat (length msg)) dst
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ input_cells heap ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hkeyview Hmsgview Hsha Hkeylen Hmsglen Hold Hkeybytes Hmsgbytes.
 iIntros "Hheap Hd". unfold hmac_application. iApply wp_app.
 unfold hmac_body, args, range, both, le, pv, int, v, op. hmac_entry_admin.
 rewrite hmac_byte_closed_key hmac_byte_closed_keyLen hmac_byte_closed_msg hmac_byte_closed_msgLen hmac_byte_closed_dst.
 rewrite hmac_sha_closed_key hmac_sha_closed_keyLen hmac_sha_closed_msg hmac_sha_closed_msgLen hmac_sha_closed_dst.
 iApply (wp_bind [IfCtx _ _]). hmac_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap keyp key Hkeyview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u.
 assert (Hkeytrue : bytes_test key = true) by (apply bytes_test_spec; exact Hkeybytes).
 rewrite Hkeytrue. hmac_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap msgp msg Hmsgview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u.
 assert (Hmsgtrue : bytes_test msg = true) by (apply bytes_test_spec; exact Hmsgbytes).
 rewrite Hmsgtrue. hmac_entry_admin.
 iApply (hmac_compute_inputs_wp with "Hheap Hd"); try assumption; lia.
Qed.
Theorem hmac_application_wp keyp key msgp msg dst old :
 sha_refinement ->
 (1 <= length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 array.array_cells keyp key -∗ array.array_cells msgp msg -∗ array.array_cells dst old -∗
 WP hmac_application keyp (Z.of_nat (length key)) msgp (Z.of_nat (length msg)) dst
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells keyp key ∗ array.array_cells msgp msg ∗
 array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hsha Hkeylen Hmsglen Hold Hkeybytes Hmsgbytes.
 iIntros "Hkey Hmsg Hd". unfold hmac_application. iApply wp_app.
 unfold hmac_body, args, range, both, le, pv, int, v, op. hmac_entry_admin.
 rewrite hmac_byte_closed_key hmac_byte_closed_keyLen hmac_byte_closed_msg hmac_byte_closed_msgLen hmac_byte_closed_dst.
 rewrite hmac_sha_closed_key hmac_sha_closed_keyLen hmac_sha_closed_msg hmac_sha_closed_msgLen hmac_sha_closed_dst.
 iApply (wp_bind [IfCtx _ _]). hmac_args.
 iApply (wp_wand with "[Hkey]").
 { iApply (bytes_reduced_wp keyp key (length key) with "Hkey"). lia. }
 iIntros (u) "[%Hu Hkey]". subst u. rewrite take_ge; last lia.
 assert (Hkeytrue : bytes_test key = true) by (apply bytes_test_spec; exact Hkeybytes).
 rewrite Hkeytrue. hmac_args.
 iApply (wp_wand with "[Hmsg]").
 { iApply (bytes_reduced_wp msgp msg (length msg) with "Hmsg"). lia. }
 iIntros (u) "[%Hu Hmsg]". subst u. rewrite take_ge; last lia.
 assert (Hmsgtrue : bytes_test msg = true) by (apply bytes_test_spec; exact Hmsgbytes).
 rewrite Hmsgtrue. hmac_entry_admin.
 iApply (hmac_compute_wp with "Hkey Hmsg Hd"); try assumption; lia.
Qed.
End proofs.
