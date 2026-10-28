(** SHA-1's native arithmetic padding expressions, with a continuation. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory encoding encoding_arithmetic padding padding_memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition native_padding p q n rest := seqs
 [copy (pv p) (pv q) (int (Z.of_nat n));
  put (pv q) (int (Z.of_nat n)) (int 128);
  emit_be (pv q) (sub (int (Z.of_nat (padded_size n))) (int 8)) (mul (int (Z.of_nat n)) (int 8)) 8] rest.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem native_padding_wp p q msg rest (Phi : val_cjr -> iProp Σ) : (length msg <= 2048)%nat ->
 array.array_cells p msg -∗ array.array_cells q (replicate 2112 0) -∗
 (array.array_cells p msg -∗ array.array_cells q
   (model.padding msg ++ drop (padded_size (length msg)) (replicate 2112 0)) -∗ WP rest {{Phi}}) -∗
 WP native_padding p q (length msg) rest {{Phi}}.
Proof.
 intros Hlen. iIntros "Hs Hpad Hrest". unfold native_padding, seqs.
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
 { iApply (emit_be_arithmetic_wp q (terminated msg) (padded_size (length msg)) 8 (Z.of_nat (length msg)) 8 8 with "Hpad").
   - pose proof (padded_size_capacity _ Hlen). lia.
   - rewrite terminated_length; last done.
   pose proof (padded_size_capacity _ Hlen). lia. }
 iIntros (u) "[%Hu Hpad]". subst u. iApply wp_seq. rewrite padding_heap_result; last done.
 iApply ("Hrest" with "Hs Hpad").
Qed.
End proofs.
