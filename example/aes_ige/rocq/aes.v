(** FIPS 197 key expansion and concrete AES rounds for all three key sizes. *)
From Coq Require Import ZArith List Lia.
From cjr.aes_ige Require Import bytes block.
Import ListNotations.
Open Scope Z_scope.
Definition read_col xs n := Col (mask (nth n xs 0)) (mask (nth (n+1) xs 0))
  (mask (nth (n+2) xs 0)) (mask (nth (n+3) xs 0)).
Definition read_block xs n := Block (read_col xs n) (read_col xs (n+4))
  (read_col xs (n+8)) (read_col xs (n+12)).
Definition col_list c := [a0 c; a1 c; a2 c; a3 c].
Definition block_list b := col_list (c0 b) ++ col_list (c1 b) ++ col_list (c2 b) ++ col_list (c3 b).
Definition rotate_word c := Col (a1 c) (a2 c) (a3 c) (a0 c).
Definition rcon i := nth (i-1) [1;2;4;8;16;32;64;128;27;54] 0.
Fixpoint expand_words fuel nk i (ws : list column) : list column :=
  match fuel with O => ws | S fuel =>
    let t := nth (i-1) ws (Col 0 0 0 0) in
    let t := if Nat.eqb (i mod nk) 0 then
      cxor (cmap sbox (rotate_word t)) (Col (rcon (i/nk)) 0 0 0)
      else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool
      then cmap sbox t else t in
    expand_words fuel nk (S i) (ws ++ [cxor (nth (i-nk) ws (Col 0 0 0 0)) t]) end.
Definition nk_of_length n := if Nat.eqb n 16 then 4%nat else
  if Nat.eqb n 24 then 6%nat else if Nat.eqb n 32 then 8%nat else 0%nat.
Definition rounds_of_length n := if Nat.eqb n 16 then 10%nat else
  if Nat.eqb n 24 then 12%nat else if Nat.eqb n 32 then 14%nat else 0%nat.
Definition expanded_key key :=
  let nk := nk_of_length (length key) in let nr := rounds_of_length (length key) in
  if Nat.eqb nk 0 then [] else
    flat_map col_list (expand_words (4*(nr+1)-nk) nk nk
      (map (fun i => read_col key (4*i)) (seq 0 nk))).
Definition key_schedule key :=
  map (fun i => read_block (expanded_key key) (16*i))
    (seq 0 (S (rounds_of_length (length key)))).
Definition round k b := xor (mix_columns (shift_rows (sub_bytes b))) k.
Definition unround k b := inv_sub_bytes (inv_shift_rows (inv_mix_columns (xor b k))).
Definition final_round k b := xor (shift_rows (sub_bytes b)) k.
Definition unfinal_round k b := inv_sub_bytes (inv_shift_rows (xor b k)).
Fixpoint encrypt_tail ks b := match ks with
  | [] => b | [k] => final_round k b | k::ks => encrypt_tail ks (round k b) end.
Fixpoint decrypt_tail ks b := match ks with
  | [] => b | [k] => unfinal_round k b | k::ks => unround k (decrypt_tail ks b) end.
Definition encrypt_schedule ks b := match ks with
  | [] => b | k::ks => encrypt_tail ks (xor b k) end.
Definition decrypt_schedule ks b := match ks with
  | [] => b | k::ks => xor (decrypt_tail ks b) k end.
Definition encrypt key := encrypt_schedule (key_schedule key).
Definition decrypt key := decrypt_schedule (key_schedule key).
Definition valid_key key := (length key = 16 \/ length key = 24 \/ length key = 32)%nat /\ Forall byte key.
Lemma read_block_bytes xs n : block_bytes (read_block xs n).
Proof. unfold read_block, read_col, block_bytes, column_bytes; simpl;
  repeat split; apply mask_byte. Qed.
Lemma schedule_bytes key : Forall block_bytes (key_schedule key).
Proof. unfold key_schedule. apply Forall_map. apply Forall_forall.
  intros; apply read_block_bytes. Qed.
Lemma round_bytes k b : block_bytes k -> block_bytes b -> block_bytes (round k b).
Proof. intros. apply xor_bytes; [apply mix_columns_bytes, shift_bytes, sub_bytes_range|]; assumption. Qed.
Lemma unround_bytes k b : block_bytes k -> block_bytes b -> block_bytes (unround k b).
Proof. intros. apply inv_sub_bytes_range, inv_shift_bytes, inv_mix_columns_bytes, xor_bytes; assumption. Qed.
Lemma final_bytes k b : block_bytes k -> block_bytes b -> block_bytes (final_round k b).
Proof. intros. apply xor_bytes; [apply shift_bytes, sub_bytes_range|]; assumption. Qed.
Lemma unfinal_bytes k b : block_bytes k -> block_bytes b -> block_bytes (unfinal_round k b).
Proof. intros. apply inv_sub_bytes_range, inv_shift_bytes, xor_bytes; assumption. Qed.
Lemma round_inverse k b : block_bytes b -> unround k (round k b) = b.
Proof. intros H. unfold unround, round. rewrite xor_cancel, mix_columns_inverse, shift_inverse.
  apply sub_inverse; assumption. Qed.
Lemma inverse_round k b : block_bytes k -> block_bytes b -> round k (unround k b) = b.
Proof. intros Hk Hb. unfold round, unround.
  rewrite inverse_sub by (apply inv_shift_bytes, inv_mix_columns_bytes, xor_bytes; assumption).
  rewrite inverse_shift, inverse_mix_columns, xor_cancel. reflexivity. Qed.
Lemma final_inverse k b : block_bytes b -> unfinal_round k (final_round k b) = b.
Proof. intros H. unfold unfinal_round, final_round. rewrite xor_cancel, shift_inverse.
  apply sub_inverse; assumption. Qed.
Lemma inverse_final k b : block_bytes k -> block_bytes b -> final_round k (unfinal_round k b) = b.
Proof. intros Hk Hb. unfold unfinal_round, final_round.
  rewrite inverse_sub by (apply inv_shift_bytes, xor_bytes; assumption).
  rewrite inverse_shift, xor_cancel. reflexivity. Qed.
Lemma encrypt_tail_bytes ks b : Forall block_bytes ks -> block_bytes b -> block_bytes (encrypt_tail ks b).
Proof. revert b; induction ks as [|k ks IH]; intros b; simpl; intros H Hb; [assumption|].
  inversion H; subst. destruct ks; [apply final_bytes; assumption|apply IH; [assumption|apply round_bytes; assumption]]. Qed.
Lemma decrypt_tail_bytes ks b : Forall block_bytes ks -> block_bytes b -> block_bytes (decrypt_tail ks b).
Proof. revert b; induction ks as [|k ks IH]; intros b; simpl; intros H Hb; [assumption|].
  inversion H; subst. destruct ks; [apply unfinal_bytes|apply unround_bytes; [assumption|apply IH]]; assumption. Qed.
Lemma tail_inverse ks b : Forall block_bytes ks -> block_bytes b ->
  decrypt_tail ks (encrypt_tail ks b) = b.
Proof. revert b; induction ks as [|k ks IH]; intros b; simpl; intros H Hb; [reflexivity|].
  inversion H; subst. destruct ks as [|k' ks']; [apply final_inverse; assumption|].
  change (unround k (decrypt_tail (k'::ks') (encrypt_tail (k'::ks') (round k b))) = b).
  rewrite IH by (try apply round_bytes; assumption). apply round_inverse; assumption. Qed.
Lemma inverse_tail ks b : Forall block_bytes ks -> block_bytes b ->
  encrypt_tail ks (decrypt_tail ks b) = b.
Proof. revert b; induction ks as [|k ks IH]; intros b; simpl; intros H Hb; [reflexivity|].
  inversion H; subst. destruct ks as [|k' ks']; [apply inverse_final; assumption|].
  change (encrypt_tail (k'::ks') (round k (unround k (decrypt_tail (k'::ks') b))) = b).
  rewrite inverse_round by (try apply decrypt_tail_bytes; assumption). apply IH; assumption. Qed.
Theorem decrypt_encrypt key b : block_bytes b -> decrypt key (encrypt key b) = b.
Proof. intros Hb. unfold decrypt, encrypt, decrypt_schedule, encrypt_schedule.
  destruct (key_schedule key) as [|k ks] eqn:Hks; [reflexivity|].
  pose proof (schedule_bytes key) as H. rewrite Hks in H. inversion H; subst.
  rewrite tail_inverse by (try apply xor_bytes; assumption). apply xor_cancel. Qed.
Theorem encrypt_decrypt key b : block_bytes b -> encrypt key (decrypt key b) = b.
Proof. intros Hb. unfold decrypt, encrypt, decrypt_schedule, encrypt_schedule.
  destruct (key_schedule key) as [|k ks] eqn:Hks; [reflexivity|].
  pose proof (schedule_bytes key) as H. rewrite Hks in H. inversion H; subst.
  rewrite xor_cancel. apply inverse_tail; assumption. Qed.
Theorem encrypt_bytes key b : block_bytes b -> block_bytes (encrypt key b).
Proof. intros Hb. unfold encrypt, encrypt_schedule.
  destruct (key_schedule key) as [|k ks] eqn:Hks; [assumption|].
  pose proof (schedule_bytes key) as H. rewrite Hks in H. inversion H; subst.
  apply encrypt_tail_bytes; [assumption|apply xor_bytes; assumption]. Qed.
Theorem decrypt_bytes key b : block_bytes b -> block_bytes (decrypt key b).
Proof. intros Hb. unfold decrypt, decrypt_schedule.
  destruct (key_schedule key) as [|k ks] eqn:Hks; [assumption|].
  pose proof (schedule_bytes key) as H. rewrite Hks in H. inversion H; subst.
  apply xor_bytes; [apply decrypt_tail_bytes|]; assumption. Qed.
Theorem encrypt_injective key x y : block_bytes x -> block_bytes y ->
  encrypt key x = encrypt key y -> x = y.
Proof. intros Hx Hy E. rewrite <- (decrypt_encrypt key x Hx), E, decrypt_encrypt by assumption. reflexivity. Qed.
Theorem decrypt_injective key x y : block_bytes x -> block_bytes y ->
  decrypt key x = decrypt key y -> x = y.
Proof. intros Hx Hy E. rewrite <- (encrypt_decrypt key x Hx), E, encrypt_decrypt by assumption. reflexivity. Qed.
Theorem encrypt_surjective key y : block_bytes y -> exists x, block_bytes x /\ encrypt key x = y.
Proof. intros H. exists (decrypt key y). split; [apply decrypt_bytes|apply encrypt_decrypt]; assumption. Qed.
Theorem decrypt_surjective key y : block_bytes y -> exists x, block_bytes x /\ decrypt key x = y.
Proof. intros H. exists (encrypt key y). split; [apply encrypt_bytes|apply decrypt_encrypt]; assumption. Qed.
Theorem block_length b : length (block_list b) = 16%nat.
Proof. destruct b as [[? ? ? ?] [? ? ? ?] [? ? ? ?] [? ? ? ?]]; reflexivity. Qed.

Lemma expand_words_length fuel nk i ws :
 length (expand_words fuel nk i ws) = (length ws + fuel)%nat.
Proof.
 revert nk i ws. induction fuel; intros; [simpl; lia|].
 cbn [expand_words]. rewrite IHfuel, length_app. simpl. lia.
Qed.
Lemma flatten_words_length ws : length (flat_map col_list ws) = (4 * length ws)%nat.
Proof. induction ws; simpl; [reflexivity|]. unfold col_list in *; simpl in *; lia. Qed.
Theorem expanded_key_length key : valid_key key ->
 length (expanded_key key) = (16 * (rounds_of_length (length key)+1))%nat.
Proof.
 intros [Hlen Hbytes]. unfold expanded_key.
 destruct Hlen as [Hlen|[Hlen|Hlen]]; rewrite Hlen;
 cbn [nk_of_length rounds_of_length Nat.eqb];
 rewrite flatten_words_length, expand_words_length, length_map, length_seq; reflexivity.
Qed.
Theorem key_schedule_length key : valid_key key ->
 length (key_schedule key) = S (rounds_of_length (length key)).
Proof. intros _. unfold key_schedule. rewrite length_map, length_seq. reflexivity. Qed.
Lemma read_col_bytes xs i : column_bytes (read_col xs i).
Proof. unfold read_col, column_bytes; simpl. repeat split; apply mask_byte. Qed.
Lemma nth_col_bytes ws i : Forall column_bytes ws -> column_bytes (nth i ws (Col 0 0 0 0)).
Proof. revert i. induction ws; intros i H; destruct i; simpl;
 try (unfold column_bytes, byte; simpl; lia).
 - inversion H; assumption.
 - apply IHws. inversion H; assumption.
Qed.
Lemma cmap_sbox_bytes c : column_bytes c -> column_bytes (cmap sbox c).
Proof. destruct c; unfold column_bytes, cmap; simpl; intros H.
 repeat split; apply sbox_byte; tauto. Qed.
Lemma rotate_word_bytes c : column_bytes c -> column_bytes (rotate_word c).
Proof. destruct c; unfold column_bytes, rotate_word; simpl; tauto. Qed.
Lemma cxor_bytes c d : column_bytes c -> column_bytes d -> column_bytes (cxor c d).
Proof. destruct c,d; unfold column_bytes,cxor; simpl; intros Hc Hd.
 repeat split; apply bx_byte; tauto. Qed.
Lemma rcon_byte i : byte (rcon i).
Proof.
 unfold rcon. destruct i as [|i]; [unfold byte; simpl; lia|].
 simpl. do 10 (destruct i as [|i]; [unfold byte; simpl; lia|]).
 destruct i; unfold byte; simpl; lia.
Qed.
Lemma expand_words_bytes fuel nk i ws : Forall column_bytes ws ->
 Forall column_bytes (expand_words fuel nk i ws).
Proof.
 revert nk i ws. induction fuel; intros nk i ws H; [exact H|].
 cbn [expand_words]. apply IHfuel, Forall_app. split; [exact H|].
 constructor; [|constructor]. apply cxor_bytes; [apply nth_col_bytes; exact H|].
 destruct (Nat.eqb (i mod nk) 0).
 - apply cxor_bytes.
   + apply cmap_sbox_bytes, rotate_word_bytes, nth_col_bytes; exact H.
   + unfold column_bytes; simpl. split; [apply rcon_byte|]. unfold byte; lia.
 - destruct (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool;
   [apply cmap_sbox_bytes|]; apply nth_col_bytes; exact H.
Qed.
Lemma flatten_words_bytes ws : Forall column_bytes ws -> Forall byte (flat_map col_list ws).
Proof.
 induction ws; intros H; [constructor|]. inversion H; subst.
 change (Forall byte (col_list a ++ flat_map col_list ws)). apply Forall_app. split; [|apply IHws; assumption].
 destruct a; unfold col_list, column_bytes in *; simpl in *.
 repeat (constructor; [tauto|]); constructor.
Qed.
Theorem expanded_key_bytes key : Forall byte (expanded_key key).
Proof.
 unfold expanded_key. destruct (Nat.eqb (nk_of_length (length key)) 0); [constructor|].
 apply flatten_words_bytes, expand_words_bytes. apply Forall_map, Forall_forall.
 intros; apply read_col_bytes.
Qed.

(** The exponentiation used by the S-box really is inversion in GF(2^8). *)
Lemma gf_inverse_certificate : forallb (fun x =>
 if Z.eqb x 0 then Z.eqb (gf_pow 254 x) 0
 else Z.eqb (gf_mul x (gf_pow 254 x)) 1) byte_values = true.
Proof. vm_compute. reflexivity. Qed.
Theorem gf_inverse_nonzero x : byte x -> x <> 0 -> gf_mul x (gf_pow 254 x) = 1.
Proof.
 intros Hx Hnz. pose proof (byte_check _ gf_inverse_certificate x Hx) as H.
 change ((if Z.eqb x 0 then Z.eqb (gf_pow 254 x) 0 else Z.eqb (gf_mul x (gf_pow 254 x)) 1) = true) in H.
 rewrite (proj2 (Z.eqb_neq _ _) Hnz) in H. apply Z.eqb_eq; assumption.
Qed.
Theorem gf_inverse_zero : gf_pow 254 0 = 0.
Proof. vm_compute. reflexivity. Qed.
