(** The concrete 64-byte block loop refines the pure SHA-1 block fold. *)
From Coq Require Import ZArith List Lia String.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory sha1_memory round_model sha1_rounds sha1_compress sha1_blocks sha1_iteration.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition hash_loop p w block h0 h1 h2 h3 h4 total :=
 While (stride_test block (Z.of_nat total))
   (Seq (compression_bound p w block h0 h1 h2 h3 h4) (stride_increment block 64)).
Opaque model.hash_blocks model.compress model.schedule_more round_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hash_loop_wp p pad w old block h0 h1 h2 h3 h4 total initial :
 (total <= length pad)%nat -> (total mod 64 = 0)%nat -> length old = 80%nat ->
 StackId block ↦ₛ LitV (LitInt 0) -∗ state_at h0 h1 h2 h3 h4 initial -∗
 array.array_cells p pad -∗ array.array_cells w old -∗
 WP hash_loop p w block h0 h1 h2 h3 h4 total
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId block ↦ₛ LitV (LitInt (Z.of_nat total)) ∗
   state_at h0 h1 h2 h3 h4 (model.hash_blocks (total/64) pad initial) ∗
   array.array_cells p pad ∗ ∃ ws, ⌜length ws = 80%nat⌝ ∗ array.array_cells w ws}}.
Proof.
 intros Hpad Htotal Hold. iIntros "Hl Hhash Hpad Hw". unfold hash_loop.
 set (I := fun i : Z => (⌜i mod 64 = 0⌝ ∗
   state_at h0 h1 h2 h3 h4 (model.hash_blocks (Z.to_nat i/64) pad initial) ∗
   array.array_cells p pad ∗ ∃ ws, ⌜length ws = 80%nat⌝ ∗ array.array_cells w ws)%I).
 iApply (wp_wand with "[Hl Hhash Hpad Hw]").
 { iApply (stride_while_wp block 64 (Z.of_nat total) _ I 0 with "Hl [Hhash Hpad Hw]").
   - lia.
   - lia.
   - rewrite Z.sub_0_r. pose proof (Nat2Z.inj_mod total 64) as Hz.
     rewrite Htotal in Hz. exact (eq_sym Hz).
   - intros i Hi. iIntros "Hl [%Halign [Hhash [Hpad Hws]]]".
     iDestruct "Hws" as (ws) "[%Hws Hw]".
     assert (Hbase : (Z.to_nat i+64 <= length pad)%nat).
     { pose proof (block_cursor_room i total Hi Halign Htotal). lia. }
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     iApply (wp_wand with "[Hl Hhash Hpad Hw]").
     { iApply (compression_wp p pad w ws (Z.to_nat i) block h0 h1 h2 h3 h4
         with "[Hl] Hhash Hpad Hw"); [exact Hbase|lia|].
       rewrite Hki. iExact "Hl". }
     iIntros (u) "[%Hu [Hl [Hhash [Hpad Hw]]]]".
     rewrite Hki. iFrame "Hl". unfold I.
     iSplit.
     { iPureIntro. apply Z.mod_divide; first lia.
       apply Z.mod_divide in Halign; last lia. destruct Halign as [k Hk].
       exists (k+1). nia. }
     rewrite block_cursor_step; [|lia|exact Halign].
     iFrame "Hhash Hpad". iExists _. iFrame "Hw".
     iPureIntro. rewrite length_app schedule_length length_drop Hws. lia.
   - unfold I. rewrite hash_blocks_zero. iFrame. iSplit; first done.
     done. }
 iIntros (u) "[%Hu [Hl [_ [Hhash [Hpad Hws]]]]]".
 unfold I. rewrite Nat2Z.id. iFrame. done.
Qed.
End proofs.
