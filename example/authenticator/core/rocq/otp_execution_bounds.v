(** Public HMAC/OTP inputs establish the preconditions of every nested
    cryptographic invocation and therefore of the SHA execution bounds. *)
From Coq Require Import ZArith List Lia.
From stdpp Require Import list.
From cjr.authenticator Require Import model crypto_bounds otp_bounds sha_execution_bounds.
Import ListNotations.
Open Scope Z_scope.
Definition hmac_inner_message key msg :=
 map (fun b => Z.lxor b 54) (hmac_key_block key) ++ msg.
Definition hmac_outer_message key msg :=
 map (fun b => Z.lxor b 92) (hmac_key_block key) ++ sha1 (hmac_inner_message key msg).
Lemma reachable_hmac_key_block key : Forall byte key ->
 length (hmac_key_block key) = 64%nat /\ Forall byte (hmac_key_block key).
Proof. intros Hbytes. split; [apply hmac_key_block_length|apply hmac_key_block_bytes;exact Hbytes]. Qed.
Lemma reachable_hmac_inner key msg : Forall byte key -> Forall byte msg ->
 (length msg <= 1024)%nat ->
 Forall byte (hmac_inner_message key msg) /\ (length (hmac_inner_message key msg) <= 1088)%nat.
Proof.
 intros Hkey Hmsg Hlen. unfold hmac_inner_message. split.
 - apply Forall_app. split; [apply hmac_pad_bytes; [exact Hkey|unfold byte;lia]|exact Hmsg].
 - apply hmac_inner_length. exact Hlen.
Qed.
Lemma reachable_hmac_outer key msg : Forall byte key ->
 Forall byte (hmac_outer_message key msg) /\ length (hmac_outer_message key msg) = 84%nat.
Proof.
 intros Hkey. unfold hmac_outer_message, hmac_inner_message. split.
 - apply Forall_app. split; [apply hmac_pad_bytes; [exact Hkey|unfold byte;lia]|apply sha1_output_bytes].
 - apply hmac_outer_length.
Qed.
Lemma reachable_hmac_sha_invocation key msg source :
 (length key <= 128)%nat -> (length msg <= 1024)%nat -> Forall byte key -> Forall byte msg ->
 In source [key;hmac_inner_message key msg;hmac_outer_message key msg] ->
 Forall byte source /\ (length source <= 2048)%nat.
Proof.
 intros Hkeylen Hmsglen Hkeybytes Hmsgbytes [Hsource|[Hsource|[Hsource|Hnone]]]; try contradiction;
 subst source.
 - split; [exact Hkeybytes|lia].
 - destruct (reachable_hmac_inner key msg Hkeybytes Hmsgbytes Hmsglen) as [Hbytes Hlen]. split; [exact Hbytes|lia].
 - destruct (reachable_hmac_outer key msg Hkeybytes) as [Hbytes Hlen]. split; [exact Hbytes|lia].
Qed.
Lemma reachable_hmac_sha_round key msg source block t :
 (length key <= 128)%nat -> (length msg <= 1024)%nat -> Forall byte key -> Forall byte msg ->
 In source [key;hmac_inner_message key msg;hmac_outer_message key msg] ->
 (block < length (padding source)/64)%nat -> (t <= 80)%nat ->
 Forall word (sha_reachable_round source block t).
Proof. intros. apply reachable_round_words. Qed.
Lemma reachable_hmac_sha_scalar_bounds key msg source block t :
 (length key <= 128)%nat -> (length msg <= 1024)%nat -> Forall byte key -> Forall byte msg ->
 In source [key;hmac_inner_message key msg;hmac_outer_message key msg] ->
 (block < length (padding source)/64)%nat -> (t < 80)%nat ->
 let st := sha_reachable_round source block t in
 let w := nth t (sha_reachable_schedule source block) 0%Z in
 let a := nth 0 st 0%Z in let b := nth 1 st 0%Z in let c := nth 2 st 0%Z in
 let d := nth 3 st 0%Z in let e := nth 4 st 0%Z in
 Forall int64
 [a*2^5; Z.quot a (2^(32-5)); a*2^5+Z.quot a (2^(32-5));
  b*2^30; Z.quot b (2^(32-30)); b*2^30+Z.quot b (2^(32-30));
  sha_f t b c d; sha_k t;
  rol32 a 5+sha_f t b c d; rol32 a 5+sha_f t b c d+e;
  rol32 a 5+sha_f t b c d+e+sha_k t; rol32 a 5+sha_f t b c d+e+sha_k t+w].
Proof.
 intros Hkeylen Hmsglen Hkey Hmsg Hsource Hblock Ht.
 apply reachable_round_scalar_bounds; try assumption.
 destruct (reachable_hmac_sha_invocation key msg source Hkeylen Hmsglen Hkey Hmsg Hsource) as [Hbytes Hlen].
 exact Hbytes.
Qed.
Lemma reachable_hmac_digest key msg :
 Forall byte (hmac_sha1 key msg) /\ length (hmac_sha1 key msg) = 20%nat.
Proof. split; [apply hmac_output_bytes|apply hmac_output_length]. Qed.
Lemma reachable_hotp_hmac_invocation key counter :
 (1 <= length key <= 128)%nat -> Forall byte key -> 0 <= counter ->
 Forall byte key /\ (1 <= length key <= 128)%nat /\
 Forall byte (be_bytes 8 counter) /\ length (be_bytes 8 counter) = 8%nat /\
 (length (be_bytes 8 counter) <= 1024)%nat.
Proof.
 intros Hlen Hkey Hcounter. split; [exact Hkey|]. split; [exact Hlen|].
 split; [apply be_bytes_are_bytes;exact Hcounter|]. rewrite be_bytes_length. lia.
Qed.
Lemma reachable_hotp_counter_encoding counter :
 0 <= counter -> int64 counter ->
 forall i, (i < 8)%nat ->
 int64 (256^Z.of_nat (8-1-i)) /\
 int64 (Z.quot counter (256^Z.of_nat (8-1-i))) /\
 int64 (Z.rem (Z.quot counter (256^Z.of_nat (8-1-i))) 256).
Proof.
 intros Hcounter H64 i Hi. split; [apply encoding_denominator_int64;lia|]. split.
 - apply encoding_quotient_int64; assumption || lia.
 - apply encoding_byte_int64; assumption || lia.
Qed.
Lemma reachable_hotp_truncation key counter :
 let digest := hmac_sha1 key (be_bytes 8 counter) in
 Forall byte digest /\ length digest = 20%nat /\
 (Z.to_nat (Z.land (nth 19 digest 0%Z) 15)+4 <= length digest)%nat /\
 int64 (truncate digest).
Proof.
 intros digest. split; [apply hmac_output_bytes|]. split; [apply hmac_output_length|].
 split; [apply truncation_access, hmac_output_length|apply otp_truncate_int64].
Qed.
Lemma reachable_totp_hotp_invocation timestamp period digits :
 valid_parameters digits period -> 0 <= timestamp -> int64 timestamp ->
 0 <= Z.quot timestamp period /\ int64 (Z.quot timestamp period) /\ (digits = 6 \/ digits = 8).
Proof.
 intros [Hdigits Hperiod] Htime H64.
 destruct (totp_counter_range timestamp period Htime H64 ltac:(lia)) as [Hnonnegative Hcounter64].
 split; [exact Hnonnegative|]. split; assumption.
Qed.
Lemma reachable_otp_result_int64 key timestamp period digits :
 valid_parameters digits period -> int64 (totp key timestamp period digits).
Proof. intros [Hdigits Hperiod]. apply hotp_int64. exact Hdigits. Qed.
Lemma reachable_hmac_pad_scalar_bounds key i :
 Forall byte key -> (i < 64)%nat ->
 int64 (Z.lxor (nth i (hmac_key_block key) 0%Z) 54) /\
 int64 (Z.lxor (nth i (hmac_key_block key) 0%Z) 92).
Proof.
 intros Hkey Hi. apply hmac_xor_intermediates_int64.
 apply (proj1 (Forall_nth byte 0%Z (hmac_key_block key))).
 - apply hmac_key_block_bytes. exact Hkey.
 - rewrite hmac_key_block_length. exact Hi.
Qed.
Lemma reachable_hmac_copy_index_bounds count i :
 0 <= count <= 1024 -> 0 <= i < count ->
 Forall int64 [i;i+1;64+i].
Proof.
 intros Hcount Hi. repeat (apply List.Forall_cons; [unfold int64;lia|]). apply List.Forall_nil.
Qed.
