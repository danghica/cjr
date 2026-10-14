(** Public AES block refinement and implementation-level inverse contracts. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.aes_ige Require Import bytes block aes program memory kernels routines encrypt_10 encrypt_12 encrypt_14 decrypt_10 decrypt_12 decrypt_14 calls.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition supported_rounds (n : nat) := (n=10 \/ n=12 \/ n=14)%nat.
Ltac expose_list xs count Hlen :=
 lazymatch count with
 | O => destruct xs as [|? ?]; [|simpl in Hlen; lia]
 | S ?count => let k := fresh "key" in let tail := fresh "keys" in
   destruct xs as [|k tail]; [simpl in Hlen; lia|]; expose_list tail count Hlen
 end.
Definition block_cipher (enc : bool) key b := if enc then encrypt key b else decrypt key b.
Definition block_body (enc : bool) := if enc then encrypt_body else decrypt_body.
Lemma block_cipher_range enc key b : block_bytes b -> block_bytes (block_cipher enc key b).
Proof. destruct enc; [apply encrypt_bytes|apply decrypt_bytes]. Qed.
Lemma block_cipher_inverse enc key b : block_bytes b -> block_cipher (negb enc) key (block_cipher enc key b) = b.
Proof. destruct enc; [apply decrypt_encrypt|apply encrypt_decrypt]. Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem encrypt_schedule_body_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP subst "args" (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]) encrypt_body
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (encrypt_schedule ks b) ∗
 schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. destruct Hnr as [Hnr|[Hnr|Hnr]]; subst nr.
 - expose_list ks 11%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (encrypt_10_body_wp with "Hs Hd Hk Hw Ht"); assumption.
 - expose_list ks 13%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (encrypt_12_body_wp with "Hs Hd Hk Hw Ht"); assumption.
 - expose_list ks 15%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (encrypt_14_body_wp with "Hs Hd Hk Hw Ht"); assumption.
Qed.
Theorem decrypt_schedule_body_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP subst "args" (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]) decrypt_body
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (decrypt_schedule ks b) ∗
 schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. destruct Hnr as [Hnr|[Hnr|Hnr]]; subst nr.
 - expose_list ks 11%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (decrypt_10_body_wp with "Hs Hd Hk Hw Ht"); assumption.
 - expose_list ks 13%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (decrypt_12_body_wp with "Hs Hd Hk Hw Ht"); assumption.
 - expose_list ks 15%nat Hlen. iIntros "Hs Hd Hk Hw". iDestruct "Hw" as (a d) "[Hw Ht]".
   iApply (decrypt_14_body_wp with "Hs Hd Hk Hw Ht"); assumption.
Qed.
Theorem encrypt_schedule_app_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP App (Val (RecV None (Some "args") encrypt_body)) (Val (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]))
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (encrypt_schedule ks b) ∗ schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. iIntros "Hs Hd Hk Hw". iApply wp_app.
 iApply (encrypt_schedule_body_wp with "Hs Hd Hk Hw"); assumption.
Qed.
Theorem encrypt_schedule_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP invoke encrypt_body [pv p; pv q; pv s; int (Z.of_nat nr); pv w]
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (encrypt_schedule ks b) ∗ schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. iIntros "Hs Hd Hk Hw". iApply (invoke_from_app encrypt_body [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]).
 iApply (encrypt_schedule_app_wp with "Hs Hd Hk Hw"); assumption.
Qed.
Theorem decrypt_schedule_app_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP App (Val (RecV None (Some "args") decrypt_body)) (Val (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]))
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (decrypt_schedule ks b) ∗ schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. iIntros "Hs Hd Hk Hw". iApply wp_app.
 iApply (decrypt_schedule_body_wp with "Hs Hd Hk Hw"); assumption.
Qed.
Theorem decrypt_schedule_wp p q s w ks nr b old :
 supported_rounds nr -> length ks = S nr -> Forall block_bytes ks -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s ks -∗ work_at w -∗
 WP invoke decrypt_body [pv p; pv q; pv s; int (Z.of_nat nr); pv w]
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (decrypt_schedule ks b) ∗ schedule_at s ks ∗ work_at w}}.
Proof.
 intros Hnr Hlen Hks Hb. iIntros "Hs Hd Hk Hw". iApply (invoke_from_app decrypt_body [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat nr)); LitV (LitPtr w)]).
 iApply (decrypt_schedule_app_wp with "Hs Hd Hk Hw"); assumption.
Qed.
Lemma key_supported_rounds key : valid_key key -> supported_rounds (rounds_of_length (length key)).
Proof.
 intros [Hlen Hb]. destruct Hlen as [Hlen|[Hlen|Hlen]]; rewrite Hlen; unfold supported_rounds, rounds_of_length; simpl; auto.
Qed.
Theorem encrypt_block_wp p q s w key b old : valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP invoke encrypt_body [pv p; pv q; pv s; int (Z.of_nat (rounds_of_length (length key))); pv w]
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (encrypt key b) ∗
 schedule_at s (key_schedule key) ∗ work_at w}}.
Proof.
 intros Hkey Hb. apply encrypt_schedule_wp; [apply key_supported_rounds|apply key_schedule_length|apply schedule_bytes|]; assumption.
Qed.
Theorem decrypt_block_wp p q s w key b old : valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP invoke decrypt_body [pv p; pv q; pv s; int (Z.of_nat (rounds_of_length (length key))); pv w]
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (decrypt key b) ∗
 schedule_at s (key_schedule key) ∗ work_at w}}.
Proof.
 intros Hkey Hb. apply decrypt_schedule_wp; [apply key_supported_rounds|apply key_schedule_length|apply schedule_bytes|]; assumption.
Qed.
Theorem encrypt_block_app_wp p q s w key b old : valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP App (Val (RecV None (Some "args") encrypt_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat (rounds_of_length (length key)))); LitV (LitPtr w)]))
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (encrypt key b) ∗ schedule_at s (key_schedule key) ∗ work_at w}}.
Proof.
 intros Hkey Hb. apply encrypt_schedule_app_wp; [apply key_supported_rounds|apply key_schedule_length|apply schedule_bytes|]; assumption.
Qed.
Theorem decrypt_block_app_wp p q s w key b old : valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP App (Val (RecV None (Some "args") decrypt_body))
 (Val (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitPtr s); LitV (LitInt (Z.of_nat (rounds_of_length (length key)))); LitV (LitPtr w)]))
 {{v, ⌜v = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (decrypt key b) ∗ schedule_at s (key_schedule key) ∗ work_at w}}.
Proof.
 intros Hkey Hb. apply decrypt_schedule_app_wp; [apply key_supported_rounds|apply key_schedule_length|apply schedule_bytes|]; assumption.
Qed.
Theorem block_cipher_wp enc p q s w key b old : valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q old -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP invoke (block_body enc) [pv p;pv q;pv s;int (Z.of_nat (rounds_of_length (length key)));pv w]
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (block_cipher enc key b) ∗
 schedule_at s (key_schedule key) ∗ work_at w}}.
Proof. destruct enc; [apply encrypt_block_wp|apply decrypt_block_wp]. Qed.
Theorem block_implementation_roundtrip enc p q r s w key b oldq oldr :
 valid_key key -> block_bytes b ->
 block_at p b -∗ block_at q oldq -∗ block_at r oldr -∗ schedule_at s (key_schedule key) -∗ work_at w -∗
 WP Seq
 (invoke (block_body enc) [pv p;pv q;pv s;int (Z.of_nat (rounds_of_length (length key)));pv w])
 (invoke (block_body (negb enc)) [pv q;pv r;pv s;int (Z.of_nat (rounds_of_length (length key)));pv w])
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ block_at p b ∗ block_at q (block_cipher enc key b) ∗
 block_at r b ∗ schedule_at s (key_schedule key) ∗ work_at w}}.
Proof.
 intros Hkey Hb. iIntros "Hp Hq Hr Hschedule Hwork".
 iApply (wp_bind [SeqCtx (invoke (block_body (negb enc)) [pv q;pv r;pv s;int (Z.of_nat (rounds_of_length (length key)));pv w])]).
 iApply (wp_wand with "[Hp Hq Hschedule Hwork]").
 { iApply (block_cipher_wp with "Hp Hq Hschedule Hwork"); assumption. }
 iIntros (result) "(%E & Hp & Hq & Hschedule & Hwork)". subst result. iApply wp_seq.
 iApply (wp_wand with "[Hq Hr Hschedule Hwork]").
 { iApply (block_cipher_wp with "Hq Hr Hschedule Hwork"); [assumption|apply block_cipher_range; assumption]. }
 iIntros (result) "(%E & Hq & Hr & Hschedule & Hwork)".
 iEval (rewrite block_cipher_inverse; [|assumption]) in "Hr". iFrame. done.
Qed.
End proofs.
