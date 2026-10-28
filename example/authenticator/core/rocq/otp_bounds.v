(** Int64 bounds for HMAC buffers, counter encoding and OTP truncation. *)
From Coq Require Import ZArith List Lia.
From stdpp Require Import list.
From cjr.authenticator Require Import model crypto_bounds sha1_bounds.
Import ListNotations.
Open Scope Z_scope.
Lemma encoding_denominator_bound width i : (width <= 8)%nat -> (i < width)%nat ->
 0 < 256^Z.of_nat (width-1-i) <= 72057594037927936.
Proof.
 intros Hw Hi. split; [apply Z.pow_pos_nonneg; lia|].
 change 72057594037927936 with (256^7). apply Z.pow_le_mono_r; lia.
Qed.
Lemma encoding_denominator_int64 width i : (width <= 8)%nat -> (i < width)%nat ->
 int64 (256^Z.of_nat (width-1-i)).
Proof. intros Hw Hi. pose proof (encoding_denominator_bound width i Hw Hi). unfold int64. lia. Qed.
Lemma encoding_quotient_int64 x width i : 0 <= x -> int64 x ->
 (width <= 8)%nat -> (i < width)%nat ->
 int64 (Z.quot x (256^Z.of_nat (width-1-i))).
Proof.
 intros Hx H64 Hw Hi. destruct (encoding_denominator_bound width i Hw Hi) as [Hd Hmax].
 assert (Hq : 0 <= Z.quot x (256^Z.of_nat (width-1-i)) <= x).
 { split; [apply Z.quot_pos; lia|apply Z.quot_le_upper_bound; nia]. }
 unfold int64 in *. lia.
Qed.
Lemma encoding_byte_int64 x width i : 0 <= x ->
 (width <= 8)%nat -> (i < width)%nat ->
 byte (Z.rem (Z.quot x (256^Z.of_nat (width-1-i))) 256) /\
 int64 (Z.rem (Z.quot x (256^Z.of_nat (width-1-i))) 256).
Proof.
 intros Hx Hw Hi. pose proof (encoding_denominator_bound width i Hw Hi) as Hd.
 assert (Hq : 0 <= Z.quot x (256^Z.of_nat (width-1-i))) by (apply Z.quot_pos; lia).
 assert (Hr : 0 <= Z.rem (Z.quot x (256^Z.of_nat (width-1-i))) 256 < 256)
 by (apply Z.rem_bound_pos; lia).
 unfold byte, int64. lia.
Qed.
Lemma hmac_xor_intermediates_int64 x : byte x ->
 int64 (Z.lxor x 54) /\ int64 (Z.lxor x 92).
Proof.
 intros Hx. pose proof (xor_byte x 54 Hx ltac:(unfold byte;lia)).
 pose proof (xor_byte x 92 Hx ltac:(unfold byte;lia)). unfold byte, int64 in *. lia.
Qed.
Lemma hmac_size_intermediates_int64 keyLen msgLen i :
 1 <= keyLen <= 128 -> 0 <= msgLen <= 1024 -> 0 <= i < 64 ->
 Forall int64 [keyLen;msgLen;msgLen+64;i+1;64+i].
Proof.
 intros Hkey Hmsg Hi. repeat (apply List.Forall_cons; [unfold int64;lia|]). apply List.Forall_nil.
Qed.
Lemma otp_truncation_indices_int64 digest j : 0 <= j < 4 ->
 let off := Z.land (nth 19 digest 0%Z) 15 in
 int64 off /\ int64 (off+j) /\ 0 <= off+j < 20.
Proof.
 intros Hj. pose proof (truncation_offset digest). unfold int64. lia.
Qed.
Lemma otp_truncation_assembly_int64 digest j :
 Forall byte digest -> (j < 4)%nat ->
 let off := Z.to_nat (Z.land (nth 19 digest 0%Z) 15) in
 int64 (be_word (firstn j (skipn off digest))*256) /\
 int64 (be_word (firstn j (skipn off digest))*256+nth j (skipn off digest) 0%Z).
Proof.
 intros Hbytes Hj off. apply be_word_step_int64; [apply Forall_drop;exact Hbytes|exact Hj].
Qed.
Lemma otp_truncate_int64 digest : int64 (truncate digest).
Proof. pose proof (truncate_range digest). unfold int64. lia. Qed.
Lemma remaining_int64 timestamp period : 0 <= timestamp -> 1 <= period <= 2147483647 ->
 int64 (remaining timestamp period).
Proof.
 intros Ht Hp. pose proof (remaining_range timestamp period Ht ltac:(lia)). unfold int64. lia.
Qed.
