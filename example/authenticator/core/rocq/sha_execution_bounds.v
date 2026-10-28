(** Reachable SHA-1 model states supply every bounded-arithmetic premise.
    These are exactly [hash_blocks], [rounds_state], and [schedule_more] used
    in the heap-loop invariants. Extraction/compiler correctness stays trusted. *)
From Coq Require Import ZArith List Lia.
From stdpp Require Import list.
From cjr.authenticator Require Import model padding sha1_memory round_model sha1_blocks sha1_compute sha1_bounds otp_bounds.
Import ListNotations.
Open Scope Z_scope.
Definition sha_reachable_state msg block := hash_blocks block (padding msg) initial.
Definition sha_reachable_block msg block := firstn 64 (skipn (64*block) (padding msg)).
Definition sha_reachable_schedule msg block := schedule_more 64 (message_words (sha_reachable_block msg block)).
Definition sha_reachable_round msg block t :=
 rounds_state (sha_reachable_schedule msg block) t (sha_reachable_state msg block).
Lemma reachable_padding_bytes msg : Forall byte msg -> Forall byte (padding msg).
Proof. apply padding_bytes. Qed.
Lemma reachable_padding_capacity msg : (length msg <= 2048)%nat ->
 (length (padding msg) <= 2112)%nat /\ (length (padding msg) mod 64 = 0)%nat.
Proof.
 intros Hlen. rewrite padding_length. split; [apply padded_size_capacity;exact Hlen|apply padded_size_alignment].
Qed.
Lemma reachable_block_length msg block : (block < length (padding msg)/64)%nat ->
 length (sha_reachable_block msg block) = 64%nat.
Proof.
 intros Hblock. unfold sha_reachable_block. rewrite length_firstn, length_skipn.
 apply Nat.min_l. pose proof (Nat.div_mod (length (padding msg)) 64 ltac:(lia)). nia.
Qed.
Lemma reachable_block_bytes msg block : Forall byte msg ->
 Forall byte (sha_reachable_block msg block).
Proof. intros Hmsg. apply Forall_take, Forall_drop, padding_bytes. exact Hmsg. Qed.
Lemma reachable_hash_state_words msg block : Forall word (sha_reachable_state msg block).
Proof. apply hash_blocks_words, initial_words. Qed.
Lemma reachable_hash_state_length msg block : length (sha_reachable_state msg block) = 5%nat.
Proof. unfold sha_reachable_state. apply hash_blocks_length. reflexivity. Qed.
Lemma reachable_hash_transition msg block :
 sha_reachable_state msg (S block) = compress (sha_reachable_state msg block) (sha_reachable_block msg block).
Proof. apply hash_blocks_right. Qed.
Lemma reachable_schedule_words msg block : Forall byte msg ->
 (block < length (padding msg)/64)%nat -> Forall word (sha_reachable_schedule msg block).
Proof.
 intros Hmsg Hblock. apply schedule_words; [rewrite reachable_block_length;lia|apply reachable_block_bytes;exact Hmsg].
Qed.
Lemma reachable_schedule_length msg block : length (sha_reachable_schedule msg block) = 80%nat.
Proof. apply schedule_length. Qed.
Lemma reachable_round_words msg block t : Forall word (sha_reachable_round msg block t).
Proof. apply rounds_state_words, reachable_hash_state_words. Qed.
Lemma reachable_round_length msg block t : length (sha_reachable_round msg block t) = 5%nat.
Proof. apply rounds_state_length, reachable_hash_state_length. Qed.
Lemma reachable_round_transition msg block t : (t < 80)%nat ->
 sha_reachable_round msg block (S t) =
 sha_round (sha_reachable_round msg block t) (t, sha_reachable_schedule msg block !!! t).
Proof.
 intros Ht. unfold sha_reachable_round. apply rounds_state_step.
 rewrite reachable_schedule_length. exact Ht.
Qed.
Lemma word_nth_default xs i : Forall word xs -> word (nth i xs 0%Z).
Proof.
 intros Hxs. destruct (lt_dec i (length xs)) as [Hi|Hi].
 - apply (proj1 (Forall_nth word 0%Z xs) Hxs). exact Hi.
 - rewrite nth_overflow by lia. unfold word. lia.
Qed.
Lemma reachable_round_scalar_bounds msg block t :
 Forall byte msg -> (block < length (padding msg)/64)%nat -> (t < 80)%nat ->
 let st := sha_reachable_round msg block t in
 let w := nth t (sha_reachable_schedule msg block) 0%Z in
 let a := nth 0 st 0%Z in let b := nth 1 st 0%Z in let c := nth 2 st 0%Z in
 let d := nth 3 st 0%Z in let e := nth 4 st 0%Z in
 Forall int64
 [a*2^5; Z.quot a (2^(32-5)); a*2^5+Z.quot a (2^(32-5));
  b*2^30; Z.quot b (2^(32-30)); b*2^30+Z.quot b (2^(32-30));
  sha_f t b c d; sha_k t;
  rol32 a 5+sha_f t b c d; rol32 a 5+sha_f t b c d+e;
  rol32 a 5+sha_f t b c d+e+sha_k t; rol32 a 5+sha_f t b c d+e+sha_k t+w].
Proof.
 intros Hmsg Hblock Ht st w a b c d e. apply sha_round_intermediates_int64.
 - apply word_nth_default, reachable_schedule_words; assumption.
 - apply word_nth_default, reachable_round_words.
 - apply word_nth_default, reachable_round_words.
 - apply word_nth_default, reachable_round_words.
 - apply word_nth_default, reachable_round_words.
 - apply word_nth_default, reachable_round_words.
Qed.
Lemma reachable_schedule_rotate_bounds msg block i :
 Forall byte msg -> (block < length (padding msg)/64)%nat -> (16 <= i < 80)%nat ->
 let ws := sha_reachable_schedule msg block in
 let x := Z.lxor (nth (i-3) ws 0%Z) (Z.lxor (nth (i-8) ws 0%Z)
            (Z.lxor (nth (i-14) ws 0%Z) (nth (i-16) ws 0%Z))) in
 word x /\ int64 (x*2^1) /\ int64 (Z.quot x (2^(32-1))) /\
 int64 (x*2^1+Z.quot x (2^(32-1))).
Proof.
 intros Hmsg Hblock Hi ws x.
 assert (Hws : Forall word ws) by (apply reachable_schedule_words;assumption).
 assert (Hx : word x).
 { unfold x. apply lxor_word; [apply word_nth_default;exact Hws|].
   apply lxor_word; [apply word_nth_default;exact Hws|].
   apply lxor_word; apply word_nth_default;exact Hws. }
 split; [exact Hx|]. apply rotate_unmasked_bounds; [exact Hx|lia].
Qed.
Lemma reachable_assembly_bounds msg block i j :
 Forall byte msg -> (block < length (padding msg)/64)%nat -> (i < 16)%nat -> (j < 4)%nat ->
 let bytes := skipn (4*i) (sha_reachable_block msg block) in
 int64 (be_word (firstn j bytes)*256) /\
 int64 (be_word (firstn j bytes)*256+nth j bytes 0%Z).
Proof.
 intros Hmsg Hblock Hi Hj bytes. apply be_word_step_int64; [|exact Hj].
 apply Forall_drop, reachable_block_bytes. exact Hmsg.
Qed.
Lemma reachable_feed_forward_bounds msg block i : (i < 5)%nat ->
 int64 (nth i (sha_reachable_state msg block) 0%Z + nth i (sha_reachable_round msg block 80) 0%Z).
Proof.
 intros Hi. apply sha_feed_forward_int64; apply word_nth_default;
 [apply reachable_hash_state_words|apply reachable_round_words].
Qed.
Lemma reachable_digest_encoding_bounds msg i j :
 (i < 5)%nat -> (j < 4)%nat ->
 let x := nth i (sha_reachable_state msg (length (padding msg)/64)) 0%Z in
 int64 (256^Z.of_nat (4-1-j)) /\
 int64 (Z.quot x (256^Z.of_nat (4-1-j))) /\
 int64 (Z.rem (Z.quot x (256^Z.of_nat (4-1-j))) 256).
Proof.
 intros Hi Hj x. assert (Hx : word x) by (apply word_nth_default, reachable_hash_state_words).
 split; [apply encoding_denominator_int64;lia|]. split.
 - apply encoding_quotient_int64; [unfold word in Hx;lia|apply word_int64;exact Hx|lia|exact Hj].
 - apply encoding_byte_int64; [unfold word in Hx;lia|lia|exact Hj].
Qed.

Lemma reachable_schedule_prefix_words msg block fuel : Forall byte msg ->
 (block < length (padding msg)/64)%nat ->
 Forall word (schedule_more fuel (message_words (sha_reachable_block msg block))).
Proof.
 intros Hmsg Hblock. apply schedule_more_words, message_words_words.
 - rewrite reachable_block_length; lia.
 - apply reachable_block_bytes. exact Hmsg.
Qed.
Lemma reachable_schedule_expansion_bounds msg block fuel :
 Forall byte msg -> (block < length (padding msg)/64)%nat -> (fuel < 64)%nat ->
 let ws := schedule_more fuel (message_words (sha_reachable_block msg block)) in
 let i := length ws in
 let x := Z.lxor (nth (i-3) ws 0%Z) (Z.lxor (nth (i-8) ws 0%Z)
            (Z.lxor (nth (i-14) ws 0%Z) (nth (i-16) ws 0%Z))) in
 word x /\ int64 (x*2^1) /\ int64 (Z.quot x (2^(32-1))) /\
 int64 (x*2^1+Z.quot x (2^(32-1))) /\
 Forall int64 [Z.of_nat i;Z.of_nat i-3;Z.of_nat i-8;Z.of_nat i-14;Z.of_nat i-16;Z.of_nat i+1].
Proof.
 intros Hmsg Hblock Hfuel ws i x.
 assert (Hws : Forall word ws) by (apply reachable_schedule_prefix_words;assumption).
 assert (Hi : (16 <= i < 80)%nat).
 { unfold i, ws. rewrite schedule_more_length, message_words_length. lia. }
 assert (Hx : word x).
 { unfold x. apply lxor_word; [apply word_nth_default;exact Hws|].
   apply lxor_word; [apply word_nth_default;exact Hws|].
   apply lxor_word; apply word_nth_default;exact Hws. }
 destruct (rotate_unmasked_bounds x 1 Hx ltac:(lia)) as [Hmul [Hdiv Hadd]].
 split; [exact Hx|]. split; [exact Hmul|]. split; [exact Hdiv|]. split; [exact Hadd|].
 apply sha_schedule_indices_int64. lia.
Qed.
Definition sha_allocated_padding msg := padding msg ++ drop (padded_size (length msg)) (replicate 2112 0%Z).
Lemma allocated_padding_bytes msg : Forall byte msg -> Forall byte (sha_allocated_padding msg).
Proof.
 intros Hbytes. unfold sha_allocated_padding. apply Forall_app. split.
 - apply padding_bytes. exact Hbytes.
 - apply Forall_drop, Forall_replicate. unfold byte. lia.
Qed.
Lemma allocated_padding_length msg : (length msg <= 2048)%nat ->
 length (sha_allocated_padding msg) = 2112%nat.
Proof.
 intros Hmsg. unfold sha_allocated_padding. rewrite length_app, padding_length, length_drop, length_replicate.
 pose proof (padded_size_capacity _ Hmsg). lia.
Qed.
Lemma allocated_hash_state_bridge msg block : (block <= length (padding msg)/64)%nat ->
 hash_blocks block (sha_allocated_padding msg) initial = sha_reachable_state msg block.
Proof.
 intros Hblock. apply hash_blocks_prefix_suffix.
 pose proof (Nat.div_mod (length (padding msg)) 64 ltac:(lia)). nia.
Qed.
Lemma allocated_block_bridge msg block : (block < length (padding msg)/64)%nat ->
 firstn 64 (skipn (64*block) (sha_allocated_padding msg)) = sha_reachable_block msg block.
Proof.
 intros Hblock. unfold sha_allocated_padding, sha_reachable_block.
 assert (Hroom : (64*block+64 <= length (padding msg))%nat).
 { pose proof (Nat.div_mod (length (padding msg)) 64 ltac:(lia)). nia. }
 rewrite drop_app_le; [|lia]. rewrite take_app_le; [reflexivity|rewrite length_drop;lia].
Qed.
Lemma reachable_native_cursor_bounds msg block : (length msg <= 2048)%nat ->
 (block < length (padding msg)/64)%nat ->
 0 <= Z.of_nat (64*block) <= 2048.
Proof.
 intros Hmsg Hblock. assert (Hcap : (length (padding msg) <= 2112)%nat).
 { rewrite padding_length. apply padded_size_capacity. exact Hmsg. }
 assert (Hcount : (length (padding msg)/64 <= 33)%nat).
 { apply Nat.Div0.div_le_upper_bound; lia. }
 nia.
Qed.
Lemma reachable_load_index_bounds msg block i j : (length msg <= 2048)%nat ->
 (block < length (padding msg)/64)%nat -> 0 <= i < 16 -> 0 <= j < 4 ->
 Forall int64 [4*i;Z.of_nat (64*block)+4*i;Z.of_nat (64*block)+4*i+j;i+1].
Proof.
 intros Hmsg Hblock Hi Hj. apply sha_load_indices_int64; try assumption.
 apply (reachable_native_cursor_bounds msg block); assumption.
Qed.
