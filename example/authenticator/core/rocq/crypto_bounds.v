(** Buffer and integer bounds used by HMAC and dynamic truncation. *)
From Coq Require Import ZArith List Lia.
From cjr.authenticator Require Import model.
Import ListNotations.
Open Scope Z_scope.
Definition hmac_key key := if (64 <? length key)%nat then sha1 key else key.
Definition hmac_key_block key := hmac_key key ++ repeat 0 (64 - length (hmac_key key)).
Lemma hmac_key_length key : (length (hmac_key key) <= 64)%nat.
Proof.
 unfold hmac_key. destruct (64 <? length key)%nat eqn:Hkey.
 - rewrite sha1_output_length. lia.
 - apply Nat.ltb_ge in Hkey. exact Hkey.
Qed.
Lemma hmac_key_block_length key : length (hmac_key_block key) = 64%nat.
Proof.
 unfold hmac_key_block. rewrite length_app, repeat_length.
 pose proof (hmac_key_length key). lia.
Qed.
Lemma hmac_key_bytes key : Forall byte key -> Forall byte (hmac_key key).
Proof.
 intros H. unfold hmac_key. destruct (64 <? length key)%nat; [apply sha1_output_bytes|exact H].
Qed.
Lemma hmac_key_block_bytes key : Forall byte key -> Forall byte (hmac_key_block key).
Proof.
 intros H. unfold hmac_key_block. apply Forall_app. split.
 - apply hmac_key_bytes. exact H.
 - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. unfold byte. lia.
Qed.
Lemma xor_byte x y : byte x -> byte y -> byte (Z.lxor x y).
Proof.
 unfold byte. intros Hx Hy. split.
 - apply Z.lxor_nonneg. lia.
 - destruct (Z.eq_dec (Z.lxor x y) 0) as [Hz|Hz]; [lia|].
   assert (Hpos : 0 < Z.lxor x y) by (pose proof (Z.lxor_nonneg x y); lia).
   apply (Z.log2_lt_pow2 (Z.lxor x y) 8 Hpos).
   assert (Hxlog : Z.log2 x < 8).
   { destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.log2_lt_pow2; lia. }
   assert (Hylog : Z.log2 y < 8).
   { destruct (Z.eq_dec y 0); [subst; cbn; lia|]. apply Z.log2_lt_pow2; lia. }
   pose proof (Z.log2_lxor x y ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma hmac_pad_bytes key c : Forall byte key -> byte c ->
 Forall byte (map (fun b => Z.lxor b c) (hmac_key_block key)).
Proof.
 intros Hkey Hc. apply Forall_forall. intros x Hx.
 apply in_map_iff in Hx as [b [<- Hb]]. apply xor_byte; [|exact Hc].
 eapply Forall_forall; [apply hmac_key_block_bytes; exact Hkey|exact Hb].
Qed.
Lemma hmac_inner_length key msg :
 (length msg <= 1024)%nat ->
 (length (map (fun b => Z.lxor b 54) (hmac_key_block key) ++ msg) <= 1088)%nat.
Proof. intros H. rewrite length_app, length_map, hmac_key_block_length. lia. Qed.
Lemma hmac_outer_length key msg :
 length (map (fun b => Z.lxor b 92) (hmac_key_block key) ++
 sha1 (map (fun b => Z.lxor b 54) (hmac_key_block key) ++ msg)) = 84%nat.
Proof. rewrite length_app, length_map, hmac_key_block_length, sha1_output_length. reflexivity. Qed.
Lemma hmac_key_block_model key msg : hmac_sha1 key msg =
 sha1 (map (fun b => Z.lxor b 92) (hmac_key_block key) ++
 sha1 (map (fun b => Z.lxor b 54) (hmac_key_block key) ++ msg)).
Proof. reflexivity. Qed.
Lemma truncation_offset (digest : list Z) :
 0 <= Z.land (nth 19 digest 0%Z) 15 < 16.
Proof.
 change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
 apply Z.mod_pos_bound. lia.
Qed.
Lemma truncation_access (digest : list Z) : length digest = 20%nat ->
 (Z.to_nat (Z.land (nth 19 digest 0%Z) 15) + 4 <= length digest)%nat.
Proof. intros H. pose proof (truncation_offset digest). lia. Qed.
Lemma hotp_int64 key counter digits :
 digits = 6 \/ digits = 8 -> int64 (hotp key counter digits).
Proof.
 intros [Hd | Hd]; subst digits.
 - pose proof (hotp_range key counter 6 ltac:(lia)). unfold int64. cbn in *. lia.
 - pose proof (hotp_range key counter 8 ltac:(lia)). unfold int64. cbn in *. lia.
Qed.
Lemma totp_counter_range timestamp period :
 0 <= timestamp -> int64 timestamp -> 1 <= period ->
 0 <= Z.quot timestamp period /\ int64 (Z.quot timestamp period).
Proof.
 intros Ht H64 Hp. assert (Hnonneg : 0 <= Z.quot timestamp period) by (apply Z.quot_pos; lia).
 assert (Hle : Z.quot timestamp period <= timestamp) by (apply Z.quot_le_upper_bound; nia).
 unfold int64 in *. lia.
Qed.
