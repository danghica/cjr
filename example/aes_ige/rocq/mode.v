(** Direction-parametric algebra for the concrete AES IGE specification. *)
From Coq Require Import ZArith List Lia.
From cjr.aes_ige Require Import bytes block aes ige.
Import ListNotations.
Definition ige_spec (enc : bool) key xs v := if enc then ige_encrypt key xs v else ige_decrypt key xs v.
Definition ige_step (enc : bool) key b v := if enc then enc_step key b v else dec_step key b v.
Definition next_iv (enc : bool) (b out : block) := if enc then (out,b) else (b,out).
Lemma ige_spec_step enc key b bs v :
 ige_spec enc key (b::bs) v =
 let out := ige_step enc key b v in
 let '(outs,final) := ige_spec enc key bs (next_iv enc b out) in (out::outs,final).
Proof. destruct enc; reflexivity. Qed.
Lemma ige_step_range enc key b v : block_bytes b -> iv_bytes v -> block_bytes (ige_step enc key b v).
Proof. destruct enc; [apply enc_step_bytes|apply dec_step_bytes]. Qed.
Lemma next_iv_range enc key b v : block_bytes b -> iv_bytes v ->
 iv_bytes (next_iv enc b (ige_step enc key b v)).
Proof. destruct enc; unfold next_iv, ige_step, iv_bytes; simpl; intros; split; auto using enc_step_bytes, dec_step_bytes. Qed.
Theorem ige_spec_length enc key xs v : length (fst (ige_spec enc key xs v)) = length xs.
Proof. destruct enc; [apply ige_encrypt_length|apply ige_decrypt_length]. Qed.
Theorem ige_spec_range enc key xs v : Forall block_bytes xs -> iv_bytes v ->
 Forall block_bytes (fst (ige_spec enc key xs v)) /\ iv_bytes (snd (ige_spec enc key xs v)).
Proof. destruct enc; [apply ige_encrypt_range|apply ige_decrypt_range]. Qed.
Theorem ige_spec_inverse enc key xs v : Forall block_bytes xs -> iv_bytes v ->
 ige_spec (negb enc) key (fst (ige_spec enc key xs v)) v = (xs,snd (ige_spec enc key xs v)).
Proof. destruct enc; [apply ige_decrypt_encrypt|apply ige_encrypt_decrypt]. Qed.
Theorem ige_spec_chunks enc key xs ys v :
 ige_spec enc key (xs++ys) v =
 let '(first,middle) := ige_spec enc key xs v in
 let '(second,final) := ige_spec enc key ys middle in (first++second,final).
Proof. destruct enc; [apply ige_encrypt_chunks|apply ige_decrypt_chunks]. Qed.
Theorem ige_spec_empty enc key v : ige_spec enc key [] v = ([],v).
Proof. destruct enc; reflexivity. Qed.
