(** Big-endian emission from an owned mutable local, as used by SHA-1. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory encoding.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition stack_encoding_steps p start width l indices :=
 map (fun i => put (pv p) (add (int (Z.of_nat start)) (int (Z.of_nat i)))
   (rem (div (StackLoad (Val (LitV (LitStack l))))
     (int (256 ^ Z.of_nat (width-1-i)))) (int 256))) indices.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem stack_encoding_steps_wp p words start width l x indices :
 Forall (fun i => (start+i < length words)%nat) indices ->
 StackId l ↦ₛ LitV (LitInt x) -∗ array.array_cells p words -∗
 WP seqs (stack_encoding_steps p start width l indices) unit_e
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt x) ∗
   array.array_cells p (encoding_updates start width x indices words)}}.
Proof.
 revert words. induction indices as [|i indices IH]; intros words Hbounds.
 - iIntros "Hl Hwords". simpl. iApply wp_value'. iFrame. done.
 - inversion Hbounds as [|? ? Hi Hrest]; subst.
   iIntros "Hl Hwords". cbn [stack_encoding_steps seqs map fold_right].
   iApply (wp_bind [SeqCtx (seqs (stack_encoding_steps p start width l indices) unit_e)]).
   unfold put, ptr, pv, add, rem, div, int, op. memory_admin. auth_pure.
   destruct (lookup_lt_is_Some_2 words (start+i)%nat Hi) as [old Hold].
   iDestruct (big_sepL_insert_acc with "Hwords") as "[Hcell Hclose]"; [exact Hold|].
   rewrite Nat2Z.inj_add. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" $! (encoded_byte width x i) with "Hcell") as "Hwords".
   iApply wp_seq. iApply (IH with "Hl Hwords").
   rewrite Forall_forall in Hrest. rewrite Forall_forall.
   intros j Hj. rewrite length_insert. apply Hrest. exact Hj.
Qed.
Theorem emit_be_stack_wp p words start l x width :
 (start+width <= length words)%nat ->
 StackId l ↦ₛ LitV (LitInt x) -∗ array.array_cells p words -∗
 WP emit_be (pv p) (int (Z.of_nat start)) (StackLoad (Val (LitV (LitStack l)))) width
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt x) ∗ array.array_cells p
   ((take start words ++ model.be_bytes width x) ++ drop (start+width) words)}}.
Proof.
 intros Hbounds. iIntros "Hl Hwords".
 iApply (wp_wand with "[Hl Hwords]").
 { iApply (stack_encoding_steps_wp p words start width l x (seq 0 width) with "Hl Hwords").
   rewrite Forall_forall. intros i Hi. apply elem_of_seq in Hi. lia. }
 iIntros (u) "[%Hu [Hl Hwords]]".
 rewrite encoding_updates_prefix; [|lia|exact Hbounds].
 rewrite (take_ge (model.be_bytes width x) width); last (rewrite model.be_bytes_length; lia).
 iFrame. done.
Qed.
End proofs.
