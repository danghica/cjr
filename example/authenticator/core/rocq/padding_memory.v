(** Heap construction of SHA-1 padding, including the unused zero-filled suffix. *)
From Coq Require Import ZArith List Lia String.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory encoding padding.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition terminated msg := msg ++ [128] ++ replicate (2111-length msg) 0.
Lemma padding_terminator msg : (length msg <= 2048)%nat ->
 <[length msg := 128]> (msg ++ drop (length msg) (replicate 2112 0)) = terminated msg.
Proof.
 intros Hlen. rewrite drop_replicate insert_app_r_alt; last lia.
 rewrite Nat.sub_diag. unfold terminated.
 replace (2112-length msg)%nat with (S (2111-length msg)) by lia. reflexivity.
Qed.
Lemma terminated_length msg : (length msg <= 2048)%nat -> length (terminated msg) = 2112%nat.
Proof. intros Hlen. unfold terminated. rewrite !length_app length_replicate. simpl. lia. Qed.
Lemma terminated_prefix msg : (length msg <= 2048)%nat ->
 take (padded_size (length msg)-8) (terminated msg) =
 msg ++ [128] ++ replicate ((55+64-length msg mod 64) mod 64) 0.
Proof.
 intros Hlen. pose proof (padded_size_capacity _ Hlen) as Hcap.
 unfold terminated. rewrite take_app_ge; last lia.
 rewrite take_app_ge; last (simpl;lia).
 rewrite take_replicate Nat.min_l; last lia.
 rewrite padded_size_formula. cbn [length]. repeat f_equal. lia.
Qed.
Lemma terminated_suffix msg : (length msg <= 2048)%nat ->
 drop (padded_size (length msg)-8+8) (terminated msg) =
 drop (padded_size (length msg)) (replicate 2112 0).
Proof.
 intros Hlen. pose proof (padded_size_capacity _ Hlen) as Hcap.
 unfold terminated. rewrite !drop_app_ge; try (rewrite ?length_app; simpl;lia).
 rewrite !drop_replicate. cbn [length]. f_equal. lia.
Qed.
Lemma repeat_zero n : replicate n (0 : Z) = repeat 0 n.
Proof. induction n; simpl; congruence. Qed.
Lemma padding_heap_result msg : (length msg <= 2048)%nat ->
 (take (padded_size (length msg)-8) (terminated msg) ++
   model.be_bytes 8 (Z.of_nat (length msg)*8)) ++
   drop (padded_size (length msg)-8+8) (terminated msg) =
 model.padding msg ++ drop (padded_size (length msg)) (replicate 2112 0).
Proof.
 intros Hlen. rewrite (terminated_prefix msg Hlen) (terminated_suffix msg Hlen).
 unfold model.padding. rewrite repeat_zero !app_assoc. reflexivity.
Qed.
Definition prepare_padding p q n := seqs
 [copy (pv p) (pv q) (int (Z.of_nat n));
  put (pv q) (int (Z.of_nat n)) (int 128);
  emit_be (pv q) (int (Z.of_nat (padded_size n-8))) (int (Z.of_nat n*8)) 8] unit_e.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem prepare_padding_wp p q msg : (length msg <= 2048)%nat ->
 array.array_cells p msg -∗ array.array_cells q (replicate 2112 0) -∗
 WP prepare_padding p q (length msg)
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p msg ∗
   array.array_cells q (model.padding msg ++ drop (padded_size (length msg)) (replicate 2112 0))}}.
Proof.
 intros Hlen. iIntros "Hs Hpad". unfold prepare_padding, seqs.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hs Hpad]").
 { iApply (copy_wp with "Hs Hpad"); rewrite ?length_replicate; lia. }
 iIntros (u) "[%Hu [Hs Hpad]]". subst u. iApply wp_seq.
 rewrite take_ge; last lia.
 iApply (wp_bind [SeqCtx _]). unfold put, ptr, add, int, pv, op. auth_pure.
 assert (Hout : (length msg < length (msg ++ drop (length msg) (replicate 2112 (0 : Z))))%nat).
 { rewrite length_app length_drop length_replicate. lia. }
 destruct (lookup_lt_is_Some_2 _ _ Hout) as [old Hold].
 iDestruct (big_sepL_insert_acc with "Hpad") as "[Hcell Hclose]"; [exact Hold|].
 iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
 iDestruct ("Hclose" $! 128 with "Hcell") as "Hpad".
 rewrite padding_terminator; last done. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hpad]").
 { iApply (emit_be_wp with "Hpad"). rewrite terminated_length; last done.
   pose proof (padded_size_capacity _ Hlen). lia. }
 iIntros (u) "[%Hu Hpad]". subst u. iApply wp_seq. iApply wp_value'.
 rewrite padding_heap_result; last done. iFrame. done.
Qed.
End proofs.
