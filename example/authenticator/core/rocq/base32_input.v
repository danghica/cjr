(** Base32 port contract over reusable, potentially overlapping input views. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import program memory input_memory base32_contracts.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem base32_view_application_wp heap src chars dst dst_words :
 buffer_in heap src chars -> (128 <= length dst_words)%nat ->
 input_cells heap -∗ array.array_cells dst dst_words -∗
 WP base32_application src (Z.of_nat (length chars)) dst
 {{u, input_cells heap ∗
   match base32.decode chars with
   | None => ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells dst dst_words
   | Some decoded => ⌜u = LitV (LitInt (Z.of_nat (length decoded)))⌝ ∗
     array.array_cells dst (decoded ++ drop (length decoded) dst_words)
   end}}.
Proof.
 intros Hview Hcapacity. iIntros "Hheap Hdst".
 iDestruct (input_buffer_acc heap src chars Hview with "Hheap") as "[Hsrc Hclose]".
 iApply (wp_wand with "[Hsrc Hdst]").
 { iApply (base32_application_wp with "Hsrc Hdst"). exact Hcapacity. }
 iIntros (u) "[Hsrc Hresult]".
 iDestruct ("Hclose" with "Hsrc") as "Hheap". iFrame.
Qed.
End proofs.
