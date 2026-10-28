(** Big-endian output whose start and value use the arithmetic expressions in SHA padding. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory encoding.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition arithmetic_encoding_steps p total count width x y indices :=
 map (fun i => put (pv p)
   (add (sub (int (Z.of_nat total)) (int (Z.of_nat count))) (int (Z.of_nat i)))
   (rem (div (mul (int x) (int y)) (int (256 ^ Z.of_nat (width-1-i)))) (int 256))) indices.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem arithmetic_encoding_steps_wp p words total count width x y indices :
 (count <= total)%nat -> Forall (fun i => (total-count+i < length words)%nat) indices ->
 array.array_cells p words -∗
 WP seqs (arithmetic_encoding_steps p total count width x y indices) unit_e
 {{u, ⌜u = LitV LitUnit⌝ ∗
   array.array_cells p (encoding_updates (total-count) width (x*y) indices words)}}.
Proof.
 intros Htotal. revert words. induction indices as [|i indices IH]; intros words Hbounds.
 - iIntros "Hwords". simpl. iApply wp_value'. iFrame. done.
 - inversion Hbounds as [|? ? Hi Hrest]; subst.
   iIntros "Hwords". cbn [arithmetic_encoding_steps seqs map fold_right].
   iApply (wp_bind [SeqCtx (seqs (arithmetic_encoding_steps p total count width x y indices) unit_e)]).
   unfold put, ptr, pv, add, sub, mul, rem, div, int, op. auth_pure.
   destruct (lookup_lt_is_Some_2 words (total-count+i)%nat Hi) as [old Hold].
   iDestruct (big_sepL_insert_acc with "Hwords") as "[Hcell Hclose]"; [exact Hold|].
   rewrite Nat2Z.inj_add Nat2Z.inj_sub; last lia.
   iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" $! (encoded_byte width (x*y) i) with "Hcell") as "Hwords".
   iApply wp_seq. iApply (IH with "Hwords").
   rewrite Forall_forall in Hrest. rewrite Forall_forall.
   intros j Hj. rewrite length_insert. apply Hrest. exact Hj.
Qed.
Theorem emit_be_arithmetic_wp p words total count x y width :
 (count <= total)%nat -> (total-count+width <= length words)%nat ->
 array.array_cells p words -∗
 WP emit_be (pv p) (sub (int (Z.of_nat total)) (int (Z.of_nat count))) (mul (int x) (int y)) width
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p
   ((take (total-count) words ++ model.be_bytes width (x*y)) ++ drop (total-count+width) words)}}.
Proof.
 intros Htotal Hbounds. iIntros "Hwords".
 iApply (wp_wand with "[Hwords]").
 { iApply (arithmetic_encoding_steps_wp p words total count width x y (seq 0 width) with "Hwords"); first done.
   rewrite Forall_forall. intros i Hi. apply elem_of_seq in Hi. lia. }
 iIntros (u) "[%Hu Hwords]".
 rewrite encoding_updates_prefix; [|lia|exact Hbounds].
 rewrite (take_ge (model.be_bytes width (x*y)) width); last (rewrite model.be_bytes_length; lia).
 iFrame. done.
Qed.
End proofs.
