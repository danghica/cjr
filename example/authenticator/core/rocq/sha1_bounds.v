(** Every arithmetic intermediate used by the SHA-1 CJR routines fits Int64.
    These lemmas cover the unmasked operations, not merely masked results. *)
From Coq Require Import ZArith List Lia.
From stdpp Require Import list.
From cjr.authenticator Require Import model round_model.
Import ListNotations.
Open Scope Z_scope.
Lemma word_log2 x : word x -> Z.log2 x < 32.
Proof.
 unfold word. intros Hx. destruct (Z.eq_dec x 0) as [->|Hne]; [cbn; lia|].
 apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_word x y : word x -> word y -> word (Z.land x y).
Proof.
 intros Hx Hy. pose proof (word_log2 x Hx). pose proof (word_log2 y Hy).
 unfold word in *. assert (Hnonneg : 0 <= Z.land x y) by (apply Z.land_nonneg; lia).
 split; [exact Hnonneg|]. destruct (Z.eq_dec (Z.land x y) 0) as [->|Hne]; [lia|].
 apply (Z.log2_lt_pow2 (Z.land x y) 32); [lia|].
 pose proof (Z.log2_land x y ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma lxor_word x y : word x -> word y -> word (Z.lxor x y).
Proof.
 intros Hx Hy. pose proof (word_log2 x Hx). pose proof (word_log2 y Hy).
 unfold word in *. assert (Hnonneg : 0 <= Z.lxor x y) by (apply Z.lxor_nonneg; lia).
 split; [exact Hnonneg|]. destruct (Z.eq_dec (Z.lxor x y) 0) as [->|Hne]; [lia|].
 apply (Z.log2_lt_pow2 (Z.lxor x y) 32); [lia|].
 pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma sha_ch_word b c d : word b -> word c -> word d -> word (sha_ch b c d).
Proof.
 intros Hb Hc Hd. unfold sha_ch. apply lxor_word.
 - apply land_word; assumption.
 - apply land_word; [apply lxor_word; [exact Hb|unfold word; lia]|exact Hd].
Qed.
Lemma sha_parity_word b c d : word b -> word c -> word d -> word (sha_parity b c d).
Proof. intros Hb Hc Hd. unfold sha_parity. apply lxor_word; [exact Hb|apply lxor_word; assumption]. Qed.
Lemma sha_maj_word b c d : word b -> word c -> word d -> word (sha_maj b c d).
Proof.
 intros Hb Hc Hd. unfold sha_maj. repeat apply lxor_word; apply land_word; assumption.
Qed.
Lemma sha_f_word t b c d : word b -> word c -> word d -> word (sha_f t b c d).
Proof.
 intros Hb Hc Hd. unfold sha_f.
 destruct (t <? 20)%nat; [apply sha_ch_word; assumption|].
 destruct (t <? 40)%nat; [apply sha_parity_word; assumption|].
 destruct (t <? 60)%nat; [apply sha_maj_word; assumption|apply sha_parity_word; assumption].
Qed.
Lemma sha_k_word t : word (sha_k t).
Proof.
 unfold sha_k. destruct (t <? 20)%nat; [unfold word; lia|].
 destruct (t <? 40)%nat; [unfold word; lia|].
 destruct (t <? 60)%nat; unfold word; lia.
Qed.
Lemma word_int64 x : word x -> int64 x.
Proof. unfold word, int64. lia. Qed.
Lemma rotate_powers_int64 n : 0 <= n <= 30 ->
 int64 (2^n) /\ int64 (2^(32-n)).
Proof.
 intros Hn. assert (Hnlo : 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
 assert (Hnhi : 2^n <= 2^30) by (apply Z.pow_le_mono_r; lia).
 assert (Hdlo : 0 < 2^(32-n)) by (apply Z.pow_pos_nonneg; lia).
 assert (Hdhi : 2^(32-n) <= 2^32) by (apply Z.pow_le_mono_r; lia).
 change (2^30) with 1073741824 in Hnhi. change (2^32) with 4294967296 in Hdhi.
 unfold int64. lia.
Qed.
Lemma rotate_div_bounds x n : word x -> 0 <= n <= 30 ->
 0 <= Z.quot x (2^(32-n)) <= x.
Proof.
 intros Hx Hn. unfold word in Hx.
 assert (Hd : 0 < 2^(32-n)) by (apply Z.pow_pos_nonneg; lia).
 split; [apply Z.quot_pos; lia|apply Z.quot_le_upper_bound; nia].
Qed.
Lemma rotate_unmasked_bounds x n : word x -> 0 <= n <= 30 ->
 int64 (x * 2^n) /\ int64 (Z.quot x (2^(32-n))) /\
 int64 (x * 2^n + Z.quot x (2^(32-n))).
Proof.
 intros Hx Hn. pose proof (rotate_div_bounds x n Hx Hn) as Hq.
 assert (Hp : 0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
 assert (Hpmax : 2^n <= 2^30) by (apply Z.pow_le_mono_r; lia).
 change (2^30) with 1073741824 in Hpmax.
 unfold word in Hx. unfold int64. nia.
Qed.
Lemma sha_sum_prefix_int64 a b c d e :
 word a -> word b -> word c -> word d -> word e ->
 int64 (a+b) /\ int64 (a+b+c) /\ int64 (a+b+c+d) /\ int64 (a+b+c+d+e).
Proof. unfold word, int64. lia. Qed.
Lemma sha_round_addition_int64 t w a b c d e :
 word w -> word a -> word b -> word c -> word d -> word e ->
 int64 (rol32 a 5 + sha_f t b c d) /\
 int64 (rol32 a 5 + sha_f t b c d + e) /\
 int64 (rol32 a 5 + sha_f t b c d + e + sha_k t) /\
 int64 (rol32 a 5 + sha_f t b c d + e + sha_k t + w).
Proof.
 intros Hw Ha Hb Hc Hd He. apply sha_sum_prefix_int64; auto using rol32_word, sha_f_word, sha_k_word.
Qed.
Lemma sha_feed_forward_int64 x y : word x -> word y -> int64 (x+y).
Proof. unfold word, int64. lia. Qed.
Lemma be_word_prefix_bound xs count : Forall byte xs -> (count <= 4)%nat ->
 0 <= be_word (firstn count xs) < 4294967296.
Proof.
 intros Hbytes Hcount. pose proof (be_fold_bound (firstn count xs) 0 (Forall_take byte count xs Hbytes) ltac:(lia)) as Hbound.
 assert (Hp : 256^Z.of_nat (length (firstn count xs)) <= 256^4).
 { apply Z.pow_le_mono_r; [lia|rewrite length_firstn; lia]. }
 change (256^4) with 4294967296 in Hp. unfold be_word. nia.
Qed.
Lemma be_word_step_int64 xs count : Forall byte xs -> (count < 4)%nat ->
 int64 (be_word (firstn count xs) * 256) /\
 int64 (be_word (firstn count xs) * 256 + nth count xs 0%Z).
Proof.
 intros Hbytes Hcount. pose proof (be_word_prefix_bound xs count Hbytes ltac:(lia)) as Hacc.
 assert (Hbyte : byte (nth count xs 0%Z)).
 { destruct (lt_dec count (length xs)) as [Hlt|Hge].
   - apply (proj1 (Forall_nth byte 0%Z xs) Hbytes). exact Hlt.
   - rewrite nth_overflow by lia. unfold byte. lia. }
 unfold byte in Hbyte. unfold int64. nia.
Qed.
Lemma rotate_exponent_int64 n : 0 <= n <= 30 -> int64 (32-n).
Proof. unfold int64. lia. Qed.
Lemma sha_round_intermediates_int64 t w a b c d e :
 word w -> word a -> word b -> word c -> word d -> word e ->
 Forall int64
 [a*2^5; Z.quot a (2^(32-5)); a*2^5+Z.quot a (2^(32-5));
  b*2^30; Z.quot b (2^(32-30)); b*2^30+Z.quot b (2^(32-30));
  sha_f t b c d; sha_k t;
  rol32 a 5+sha_f t b c d;
  rol32 a 5+sha_f t b c d+e;
  rol32 a 5+sha_f t b c d+e+sha_k t;
  rol32 a 5+sha_f t b c d+e+sha_k t+w].
Proof.
 intros Hw Ha Hb Hc Hd He.
 destruct (rotate_unmasked_bounds a 5 Ha ltac:(lia)) as [Ha1 [Ha2 Ha3]].
 destruct (rotate_unmasked_bounds b 30 Hb ltac:(lia)) as [Hb1 [Hb2 Hb3]].
 destruct (sha_round_addition_int64 t w a b c d e Hw Ha Hb Hc Hd He) as [Hs1 [Hs2 [Hs3 Hs4]]].
 assert (Hf : int64 (sha_f t b c d)) by (apply word_int64, sha_f_word; assumption).
 assert (Hk : int64 (sha_k t)) by (apply word_int64, sha_k_word).
 repeat (apply List.Forall_cons; [assumption|]). apply List.Forall_nil.
Qed.
Lemma sha_schedule_xor_words x3 x8 x14 x16 :
 word x3 -> word x8 -> word x14 -> word x16 ->
 word (Z.lxor x14 x16) /\ word (Z.lxor x8 (Z.lxor x14 x16)) /\
 word (Z.lxor x3 (Z.lxor x8 (Z.lxor x14 x16))).
Proof. intros H3 H8 H14 H16. split; [repeat apply lxor_word; assumption|].
 split; repeat apply lxor_word; assumption. Qed.
Lemma sha_schedule_indices_int64 t : 16 <= t < 80 ->
 Forall int64 [t;t-3;t-8;t-14;t-16;t+1].
Proof. intros Ht. repeat (apply List.Forall_cons; [unfold int64; lia|]). apply List.Forall_nil. Qed.
Lemma sha_load_indices_int64 block i j :
 0 <= block <= 2048 -> 0 <= i < 16 -> 0 <= j < 4 ->
 Forall int64 [4*i;block+4*i;block+4*i+j;i+1].
Proof. intros Hb Hi Hj. repeat (apply List.Forall_cons; [unfold int64; lia|]). apply List.Forall_nil. Qed.
Lemma sha_padding_arithmetic_int64 n : 0 <= n <= 2048 ->
 Forall int64 [n+72;Z.quot (n+72) 64;Z.quot (n+72) 64*64;n*8;
               Z.quot (n+72) 64*64-8;n+1].
Proof.
 intros Hn. assert (Hq : 0 <= Z.quot (n+72) 64 <= 33).
 { split; [apply Z.quot_pos; lia|].
   assert (Hlt : Z.quot (n+72) 64 < 34) by (apply Z.quot_lt_upper_bound; lia). lia. }
 repeat (apply List.Forall_cons; [unfold int64; lia|]). apply List.Forall_nil.
Qed.
Lemma sha_block_arithmetic_int64 block total :
 64 <= total <= 2112 -> 0 <= block < total ->
 Forall int64 [total-1;block+64;total-8;block+63].
Proof. intros Htotal Hblock. repeat (apply List.Forall_cons; [unfold int64; lia|]). apply List.Forall_nil. Qed.
