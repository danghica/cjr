(** Pure executable SHA-1 / HMAC / HOTP / TOTP specifications.
    Bytes are logical words, matching CJR's existing raw-buffer convention. *)
From Coq Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Definition byte x := 0 <= x < 256.
Definition word x := 0 <= x < 4294967296.
Definition mask32 x := Z.land x 4294967295.
Definition rol32 x n := mask32 (x * 2^n + Z.quot x (2^(32-n))).
Definition sha_ch b c d := Z.lxor (Z.land b c) (Z.land (Z.lxor b 4294967295) d).
Definition sha_parity b c d := Z.lxor b (Z.lxor c d).
Definition sha_maj b c d := Z.lxor (Z.lxor (Z.land b c) (Z.land b d)) (Z.land c d).
Definition sha_f t := if (t <? 20)%nat then sha_ch else
  if (t <? 40)%nat then sha_parity else if (t <? 60)%nat then sha_maj else sha_parity.
Definition sha_k t := if (t <? 20)%nat then 1518500249 else
  if (t <? 40)%nat then 1859775393 else if (t <? 60)%nat then 2400959708 else 3395469782.
Definition be_word (xs : list Z) := fold_left (fun a x => a*256+x) xs 0.
Definition be_bytes (n : nat) x := map (fun i => Z.rem (Z.quot x (256 ^ Z.of_nat (n-1-i))) 256) (seq 0 n).
Definition initial := [1732584193;4023233417;2562383102;271733878;3285377520].
Definition message_words block := map (fun i => be_word (firstn 4 (skipn (4*i) block))) (seq 0 16).
Fixpoint schedule_more fuel ws := match fuel with
| O => ws
| S fuel => let i := length ws in
  let w := rol32 (Z.lxor (nth (i-3) ws 0) (Z.lxor (nth (i-8) ws 0)
    (Z.lxor (nth (i-14) ws 0) (nth (i-16) ws 0)))) 1 in
  schedule_more fuel (ws ++ [w]) end.
Definition sha_round (st : list Z) (tw : nat * Z) :=
 let '(t,w) := tw in
 let a := nth 0 st 0 in let b := nth 1 st 0 in let c := nth 2 st 0 in
 let d := nth 3 st 0 in let e := nth 4 st 0 in
 [mask32 (rol32 a 5 + sha_f t b c d + e + sha_k t + w); a; rol32 b 30; c; d].
Definition compress st block :=
 let ws := schedule_more 64 (message_words block) in
 map (fun xy => mask32 (fst xy + snd xy))
   (combine st (fold_left sha_round (combine (seq 0 80) ws) st)).
Definition padding msg :=
 let n := length msg in msg ++ [128] ++ repeat 0 ((55 + 64 - n mod 64) mod 64) ++ be_bytes 8 (Z.of_nat n * 8).
Fixpoint hash_blocks fuel msg st := match fuel with
| O => st | S fuel => hash_blocks fuel (skipn 64 msg) (compress st (firstn 64 msg)) end.
Definition sha1 msg := flat_map (be_bytes 4) (hash_blocks (length (padding msg) / 64) (padding msg) initial).
Definition hmac_sha1 key msg :=
 let k := if (64 <? length key)%nat then sha1 key else key in
 let block := k ++ repeat 0 (64-length k) in
 sha1 (map (fun b => Z.lxor b 92) block ++ sha1 (map (fun b => Z.lxor b 54) block ++ msg)).
Definition truncate digest :=
 let off := Z.to_nat (Z.land (nth 19 digest 0) 15) in
 Z.land (be_word (firstn 4 (skipn off digest))) 2147483647.
Definition hotp key counter digits := Z.rem (truncate (hmac_sha1 key (be_bytes 8 counter))) (10^digits).
Definition totp key timestamp period digits := hotp key (Z.quot timestamp period) digits.
Definition remaining timestamp period := period - Z.rem timestamp period.
Definition valid_parameters digits period := (digits = 6 \/ digits = 8) /\ 1 <= period <= 2147483647.
Definition int64 x := -9223372036854775808 <= x <= 9223372036854775807.
Lemma mask32_word x : word (mask32 x).
Proof.
 unfold word, mask32. change 4294967295 with (Z.ones 32).
 rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma rol32_word x n : word (rol32 x n).
Proof. apply mask32_word. Qed.
Lemma sha_round_words st tw : Forall word st -> Forall word (sha_round st tw).
Proof.
 intros H. destruct tw as [t w]. unfold sha_round.
 assert (Hnth : forall i, word (nth i st 0)).
 { intros i. destruct (lt_dec i (length st)).
   - apply (proj1 (Forall_nth word st) H). assumption.
   - rewrite nth_overflow by lia. unfold word; lia. }
 repeat (apply Forall_cons); try apply Forall_nil; auto using mask32_word, rol32_word.
Qed.
Lemma sha_add_int64 a b c d e : word a -> word b -> word c -> word d -> word e -> int64 (a+b+c+d+e).
Proof. unfold word, int64. lia. Qed.
Lemma rotate_product_int64 x n : word x -> 0 <= n <= 30 -> int64 (x * 2^n).
Proof.
 intros Hx Hn. assert (0 < 2^n) by (apply Z.pow_pos_nonneg; lia).
 assert (2^n <= 2^30) by (apply Z.pow_le_mono_r; lia).
 unfold word, int64 in *. assert (2^30 = 1073741824) by reflexivity. nia.
Qed.
Lemma remaining_range timestamp period : 0 <= timestamp -> 0 < period -> 1 <= remaining timestamp period <= period.
Proof.
 intros Ht Hp. unfold remaining. rewrite Z.rem_mod_nonneg by lia.
 pose proof (Z.mod_pos_bound timestamp period Hp). lia.
Qed.
Lemma time_counter_bounds timestamp period : 0 <= timestamp <= 9223372036854775807 -> 0 < period ->
 0 <= Z.quot timestamp period <= 9223372036854775807.
Proof.
 intros Ht Hp. rewrite Z.quot_div_nonneg by lia.
 split; [apply Z.div_pos; lia|].
 assert (timestamp / period <= timestamp) by (apply Z.div_le_upper_bound; nia). lia.
Qed.
(** Zero-length messages, SHA-1's two-block padding edge, and RFC examples. *)
Example sha1_empty : sha1 [] = [218;57;163;238;94;107;75;13;50;85;191;239;149;96;24;144;175;216;7;9].
Proof. vm_compute. reflexivity. Qed.
Example sha1_abc : sha1 [97;98;99] = [169;153;62;54;71;6;129;106;186;62;37;113;120;80;194;108;156;208;216;157].
Proof. vm_compute. reflexivity. Qed.
Definition rfc_key := [49;50;51;52;53;54;55;56;57;48;49;50;51;52;53;54;55;56;57;48].
Example rfc_hotp_0 : hotp rfc_key 0 6 = 755224.
Proof. vm_compute. reflexivity. Qed.
Example rfc_totp_59 : totp rfc_key 59 30 8 = 94287082.
Proof. vm_compute. reflexivity. Qed.

Lemma be_bytes_length n x : length (be_bytes n x) = n.
Proof. unfold be_bytes. rewrite length_map, length_seq. reflexivity. Qed.
Lemma be_bytes_are_bytes n x : 0 <= x -> Forall byte (be_bytes n x).
Proof.
 intros Hx. unfold be_bytes. apply Forall_forall. intros b Hb.
 apply in_map_iff in Hb as [i [<- Hi]]. unfold byte.
 apply Z.rem_bound_pos; [apply Z.quot_pos|]; try lia.
Qed.
Lemma sha_round_length st tw : length (sha_round st tw) = 5%nat.
Proof. destruct tw; reflexivity. Qed.
Lemma fold_round_length rounds st : length st = 5%nat ->
 length (fold_left sha_round rounds st) = 5%nat.
Proof.
 revert st. induction rounds as [|tw rounds IH]; intros st H; simpl; [exact H|].
 apply IH. apply sha_round_length.
Qed.
Lemma compress_length st block : length st = 5%nat -> length (compress st block) = 5%nat.
Proof.
 intros H. unfold compress. rewrite length_map, length_combine, fold_round_length by exact H.
 rewrite H. reflexivity.
Qed.
Lemma compress_words st block : Forall word (compress st block).
Proof.
 unfold compress. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as [p [<- Hp]].
 apply mask32_word.
Qed.
Lemma hash_blocks_length fuel msg st : length st = 5%nat -> length (hash_blocks fuel msg st) = 5%nat.
Proof.
 revert msg st. induction fuel; intros msg st H; simpl; [exact H|].
 apply IHfuel. apply compress_length. exact H.
Qed.
Lemma hash_blocks_words fuel msg st : Forall word st -> Forall word (hash_blocks fuel msg st).
Proof.
 revert msg st. induction fuel; intros msg st H; simpl; [exact H|].
 apply IHfuel. apply compress_words.
Qed.
Lemma initial_words : Forall word initial.
Proof. unfold initial, word. repeat (apply Forall_cons); try apply Forall_nil; lia. Qed.
Lemma digest_bytes st : Forall word st -> Forall byte (flat_map (be_bytes 4) st).
Proof.
 intros H. induction H; simpl; [constructor|].
 change (Forall byte (be_bytes 4 x ++ flat_map (be_bytes 4) l)).
 apply Forall_app; split; [apply be_bytes_are_bytes; unfold word in *; lia|assumption].
Qed.
Theorem sha1_output_bytes msg : Forall byte (sha1 msg).
Proof. unfold sha1. apply digest_bytes, hash_blocks_words, initial_words. Qed.
Lemma digest_length st : length (flat_map (be_bytes 4) st) = (4 * length st)%nat.
Proof.
 induction st as [|x xs IH]; [reflexivity|].
 change (length (be_bytes 4 x ++ flat_map (be_bytes 4) xs) = (4 * S (length xs))%nat).
 rewrite length_app, be_bytes_length, IH. lia.
Qed.
Theorem sha1_output_length msg : length (sha1 msg) = 20%nat.
Proof. unfold sha1. rewrite digest_length, hash_blocks_length; reflexivity. Qed.
Theorem hmac_output_bytes key msg : Forall byte (hmac_sha1 key msg).
Proof. unfold hmac_sha1. apply sha1_output_bytes. Qed.
Theorem hmac_output_length key msg : length (hmac_sha1 key msg) = 20%nat.
Proof. unfold hmac_sha1. apply sha1_output_length. Qed.
Lemma truncate_range digest : 0 <= truncate digest < 2147483648.
Proof.
 unfold truncate. change 2147483647 with (Z.ones 31).
 rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Theorem hotp_range key counter digits : 0 <= digits -> 0 <= hotp key counter digits < 10^digits.
Proof.
 intros Hd. unfold hotp. apply Z.rem_bound_pos.
 - pose proof (truncate_range (hmac_sha1 key (be_bytes 8 counter))). lia.
 - apply Z.pow_pos_nonneg; lia.
Qed.
Theorem totp_range key timestamp period digits : 0 <= digits -> 0 <= totp key timestamp period digits < 10^digits.
Proof. apply hotp_range. Qed.

(** The padded buffer has room for the terminator and length suffix, fits the
    allocated 2112 words, and is a whole number of SHA-1 blocks. *)
Lemma padded_length_arithmetic n :
 (n <= 2048)%nat ->
 (n + 9 <= n + 1 + (55 + 64 - n mod 64) mod 64 + 8 <= 2112)%nat /\
 ((n + 1 + (55 + 64 - n mod 64) mod 64 + 8) mod 64 = 0)%nat.
Proof.
 intros Hn. pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as Hr.
 pose proof (Nat.div_mod n 64 ltac:(lia)) as Hdiv.
 destruct (le_dec (n mod 64) 55) as [Hlo|Hhi].
 - assert (Hm : ((55+64-n mod 64) mod 64 = 55-n mod 64)%nat).
   { replace (55+64-n mod 64)%nat with ((55-n mod 64)+1*64)%nat by lia.
     rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia. }
   rewrite Hm. split; [lia|].
   replace (n+1+(55-n mod 64)+8)%nat with ((n/64+1)*64)%nat by lia.
   apply Nat.Div0.mod_mul.
 - assert (Hm : ((55+64-n mod 64) mod 64 = 119-n mod 64)%nat).
   { apply Nat.mod_small. lia. }
   rewrite Hm. split; [lia|].
   replace (n+1+(119-n mod 64)+8)%nat with ((n/64+2)*64)%nat by lia.
   apply Nat.Div0.mod_mul.
Qed.
