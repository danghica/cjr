(** SHA-1's aligned block cursor and pure fold correspondence. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From cjr.authenticator Require Import model padding sha1_blocks.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Lemma block_cursor_divisible i : 0 <= i -> i mod 64 = 0 ->
 Z.to_nat i = (64 * (Z.to_nat i / 64))%nat.
Proof.
 intros Hi Halign. apply Z.mod_divide in Halign; last lia.
 destruct Halign as [k Hk].
 assert (Hkpos : 0 <= k) by nia.
 assert (Hik : i = 64*k) by nia. rewrite Hik Z2Nat.inj_mul; [|lia|lia].
 change (64 * Z.to_nat k = 64 * (64 * Z.to_nat k / 64))%nat.
 rewrite Nat.mul_comm Nat.div_mul; lia.
Qed.
Lemma block_cursor_next i : 0 <= i ->
 (Z.to_nat (i+64) / 64 = S (Z.to_nat i / 64))%nat.
Proof.
 intros Hi. rewrite Z2Nat.inj_add; [|lia|lia].
 pose proof (Nat.div_mod (Z.to_nat i) 64 ltac:(lia)) as Hdiv.
 pose proof (Nat.mod_upper_bound (Z.to_nat i) 64 ltac:(lia)) as Hmod.
 symmetry. apply Nat.div_unique with (r := (Z.to_nat i mod 64)%nat); lia.
Qed.
Lemma block_cursor_step msg st i : 0 <= i -> i mod 64 = 0 ->
 model.compress (model.hash_blocks (Z.to_nat i/64) msg st)
   (firstn 64 (skipn (Z.to_nat i) msg)) =
 model.hash_blocks (Z.to_nat (i+64)/64) msg st.
Proof.
 intros Hi Halign. rewrite block_cursor_next; last done.
 rewrite hash_blocks_right. rewrite <- (block_cursor_divisible i Hi Halign). done.
Qed.
Lemma padding_blocks_cursor msg :
 (64 * (length (model.padding msg) / 64) = length (model.padding msg))%nat.
Proof.
 pose proof (padded_size_alignment (length msg)) as Halign.
 rewrite <- padding_length in Halign.
 pose proof (Nat.div_mod (length (model.padding msg)) 64 ltac:(lia)). lia.
Qed.
Lemma block_cursor_room i total : 0 <= i < Z.of_nat total -> i mod 64 = 0 ->
 (total mod 64 = 0)%nat -> (Z.to_nat i + 64 <= total)%nat.
Proof.
 intros Hi Halign Htotal.
 pose proof (block_cursor_divisible i ltac:(lia) Halign) as Hcursor.
 pose proof (Nat.div_mod total 64 ltac:(lia)) as Hdiv.
 rewrite Htotal in Hdiv.
 assert (Hless : (Z.to_nat i < total)%nat) by lia. nia.
Qed.
