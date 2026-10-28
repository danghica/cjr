(** Enrollment capacity/identifier guards and commit composition. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory input_memory sessions account_slots account_enroll.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition available_slot words :=
 default 0 (words !! 1%nat) <= 15 -> exists i, (i<16)%nat /\ slot_identifier words i = 0.
Definition enroll_decoded_result (words : list Z) n :=
 if bool_decide (1 <= n) then
 if bool_decide (default 0 (words !! 1%nat) <= 15) then
 if bool_decide (default 0 (words !! 0%nat) <= 9223372036854775806)
 then default 0 (words !! 0%nat) else -3 else -2 else -1.
Definition enroll_decoded_words words label issuer decoded n digits period :=
 if bool_decide (1 <= n) then
 if bool_decide (default 0 (words !! 1%nat) <= 15) then
 if bool_decide (default 0 (words !! 0%nat) <= 9223372036854775806)
 then enrolled_words words (Z.to_nat (first_free_slot words 16)) label issuer
   (take (Z.to_nat n) decoded) digits period else words else words else words.
Definition enroll_decoded_body p lp labelLen ip issuerLen dp n digits period :=
 If (le (int 1) (int n))
  (If (le (get (pv p) (int 1)) (int 15))
   (If (le (get (pv p) (int 0)) (int 9223372036854775806))
    (enroll_slot_body p lp labelLen ip issuerLen dp n digits period) (int (-3))) (int (-2))) (int (-1)).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem enroll_decoded_wp heap p words lp label ip issuer dp decoded n digits period :
 length words = 6242%nat -> (length label <=128)%nat -> (length issuer <=128)%nat ->
 (1 <= n -> (Z.to_nat n <=128)%nat /\ (Z.to_nat n <=length decoded)%nat) ->
 buffer_in heap lp label -> buffer_in heap ip issuer -> available_slot words ->
 input_cells heap -∗ array.array_cells p words -∗ array.array_cells dp decoded -∗
 WP enroll_decoded_body p lp (Z.of_nat (length label)) ip (Z.of_nat (length issuer)) dp n digits period
 {{u, ⌜u = LitV (LitInt (enroll_decoded_result words n))⌝ ∗ input_cells heap ∗
   array.array_cells dp decoded ∗ array.array_cells p (enroll_decoded_words words label issuer decoded n digits period)}}.
Proof.
 intros Hlen Hlabel Hissuer Hdecoded Hlabelview Hissuerview Havailable.
 iIntros "Hheap Hs Hd". unfold enroll_decoded_body,le,get,ptr,pv,int,op. hm_pure.
 destruct (bool_decide (1<=n)) eqn:Hpositive.
 - apply bool_decide_eq_true in Hpositive. iApply wp_if_true. hm_pure.
   assert (Hcountpos : (1<length words)%nat) by (rewrite Hlen; change (1<6242)%nat; vm_compute; lia).
   destruct (lookup_lt_is_Some_2 words 1 Hcountpos) as [count Hcount].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hcount|].
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". hm_pure.
   destruct (bool_decide (count<=15)) eqn:Hroom.
   + apply bool_decide_eq_true in Hroom. iApply wp_if_true. hm_pure.
     assert (Hidpos : (0<length words)%nat) by lia.
     destruct (lookup_lt_is_Some_2 words 0 Hidpos) as [id Hid].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hid|].
     iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hs". hm_pure.
     destruct (bool_decide (id<=9223372036854775806)) eqn:Hnext.
     * apply bool_decide_eq_true in Hnext. iApply wp_if_true.
       destruct (Hdecoded Hpositive) as [Hmax Hbuffer].
       assert (Hn : n = Z.of_nat (Z.to_nat n)) by lia. rewrite {1}Hn.
       iApply (wp_wand with "[Hheap Hs Hd]").
       { iApply (enroll_slot_wp heap p words lp label ip issuer dp decoded (Z.to_nat n) digits period
          Hlen Hlabel Hissuer Hmax Hbuffer Hlabelview Hissuerview with "Hheap Hs Hd").
         apply Havailable. rewrite Hcount. cbn [default]. exact Hroom. }
       iIntros (u) "[%Hu [Hheap [Hd Hs]]]".
       unfold enroll_decoded_result,enroll_decoded_words.
       rewrite (bool_decide_true (1<=n) Hpositive) Hcount Hid. cbn [default].
       rewrite (bool_decide_true (count<=15) Hroom)
         (bool_decide_true (id<=9223372036854775806) Hnext).
       iFrame. rewrite Hid in Hu. cbn [default] in Hu. done.
     * apply bool_decide_eq_false in Hnext. iApply wp_if_false. iApply wp_value'.
       unfold enroll_decoded_result,enroll_decoded_words.
       rewrite (bool_decide_true (1<=n) Hpositive) Hcount Hid. cbn [default].
       rewrite (bool_decide_true (count<=15) Hroom)
         (bool_decide_false (id<=9223372036854775806) Hnext). iFrame. done.
   + apply bool_decide_eq_false in Hroom. iApply wp_if_false. iApply wp_value'.
     unfold enroll_decoded_result,enroll_decoded_words.
     rewrite (bool_decide_true (1<=n) Hpositive) Hcount. cbn [default].
     rewrite (bool_decide_false (count<=15) Hroom). iFrame. done.
 - apply bool_decide_eq_false in Hpositive. iApply wp_if_false. iApply wp_value'.
   unfold enroll_decoded_result,enroll_decoded_words.
   rewrite (bool_decide_false (1<=n) Hpositive). iFrame. done.
Qed.
End proofs.
