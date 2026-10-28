(** SHA-1 padding arithmetic and the correspondence of native length calculation. *)
From Coq Require Import ZArith List Lia Bool.
From cjr.authenticator Require Import model.
Import ListNotations.
Open Scope Z_scope.
Definition padded_size (n : nat) := ((n+72)/64*64)%nat.
Lemma padded_size_formula n :
 padded_size n = (n+1+(55+64-n mod 64) mod 64+8)%nat.
Proof.
 pose proof (Nat.mod_upper_bound n 64 ltac:(lia)) as Hr.
 pose proof (Nat.div_mod n 64 ltac:(lia)) as Hdiv.
 unfold padded_size. destruct (le_dec (n mod 64) 55) as [Hlo|Hhi].
 - assert (Hm : ((55+64-n mod 64) mod 64 = 55-n mod 64)%nat).
   { replace (55+64-n mod 64)%nat with ((55-n mod 64)+1*64)%nat by lia.
     rewrite Nat.Div0.mod_add. apply Nat.mod_small. lia. }
   assert (Hq : (n/64+1 = (n+72)/64)%nat).
   { apply Nat.div_unique with (r := (n mod 64+8)%nat); lia. }
   rewrite <- Hq. rewrite Hm. lia.
 - assert (Hm : ((55+64-n mod 64) mod 64 = 119-n mod 64)%nat).
   { apply Nat.mod_small. lia. }
   assert (Hq : (n/64+2 = (n+72)/64)%nat).
   { apply Nat.div_unique with (r := (n mod 64-56)%nat); lia. }
   rewrite <- Hq. rewrite Hm. lia.
Qed.
Lemma padding_length msg : length (model.padding msg) = padded_size (length msg).
Proof.
 unfold model.padding. repeat rewrite length_app.
 rewrite repeat_length, model.be_bytes_length.
 change ((length msg + (1 + ((55+64-length msg mod 64) mod 64 + 8)))%nat =
   padded_size (length msg)).
 rewrite padded_size_formula. lia.
Qed.
Lemma padded_size_capacity n : (n <= 2048)%nat -> (n+9 <= padded_size n <= 2112)%nat.
Proof. intros Hn. rewrite padded_size_formula. apply model.padded_length_arithmetic in Hn. tauto. Qed.
Lemma padded_size_alignment n : (padded_size n mod 64 = 0)%nat.
Proof. unfold padded_size. apply Nat.Div0.mod_mul. Qed.
Lemma padding_block_count msg :
 (length (model.padding msg)/64 = (length msg+72)/64)%nat.
Proof. rewrite padding_length. unfold padded_size. rewrite Nat.div_mul; lia. Qed.
Lemma padded_size_native n :
 Z.of_nat (padded_size n) = Z.quot (Z.of_nat n + 72) 64 * 64.
Proof.
 unfold padded_size. rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
 rewrite Z.quot_div_nonneg by lia. reflexivity.
Qed.
Lemma padding_bytes msg : Forall model.byte msg -> Forall model.byte (model.padding msg).
Proof.
 intros Hmsg. unfold model.padding. repeat rewrite Forall_app. repeat split.
 - exact Hmsg.
 - constructor; [unfold model.byte;lia|constructor].
 - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. unfold model.byte. lia.
 - apply model.be_bytes_are_bytes. lia.
Qed.
