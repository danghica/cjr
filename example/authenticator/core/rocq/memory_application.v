(** Reduced function applications and exact buffer-slice composition.
    These specifications let callers evaluate computed pointer arguments before
    applying a separately checked callee contract. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition slice_write (dst : list Z) offset (replacement : list Z) :=
 take offset dst ++ replacement ++ drop (offset+length replacement) dst.
Lemma slice_restore (words : list Z) offset count :
 take offset words ++ take count (drop offset words) ++ drop (offset+count) words = words.
Proof. rewrite app_assoc take_take_drop. apply take_drop. Qed.
Lemma slice_write_length dst offset replacement :
 (offset + length replacement <= length dst)%nat ->
 length (slice_write dst offset replacement) = length dst.
Proof. intros Hbounds. unfold slice_write. rewrite !length_app length_take length_drop. lia. Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem copy_reduced_wp p q src dst n :
 (n <= length src)%nat -> (n <= length dst)%nat ->
 array.array_cells p src -∗ array.array_cells q dst -∗
 WP App (Val (RecV None (Some "args") copy_body))
   (Val (StructV [LitV (LitPtr p); LitV (LitPtr q); LitV (LitInt (Z.of_nat n))]))
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p src ∗
       array.array_cells q (take n src ++ drop n dst)}}.
Proof.
 intros Hsrc Hdst. iIntros "Hs Hd".
 iApply wp_app. unfold copy_body, args. hm_pure.
 set (I := fun i : Z => (array.array_cells p src ∗
   array.array_cells q (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst))%I).
 iApply (wp_wand with "[Hs Hd]").
 { iApply (loop_wp "copyI" 0 (Z.of_nat n)
     (put (pv q) (v "copyI") (get (pv p) (v "copyI"))) I with "[Hs Hd]").
   - intros l i Hi. iIntros "Hl [Hs Hd]".
     unfold put, get, ptr, pv, v. cbn [subst_var subst_var_val].
     rewrite bool_decide_true; last done. memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hks : (Z.to_nat i < length src)%nat) by lia.
     destruct (lookup_lt_is_Some_2 src (Z.to_nat i) Hks) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hx Hclose]"; [exact Hx|].
     rewrite Hki. iApply (wp_load with "Hx"). iIntros "!> _ Hx".
     iDestruct ("Hclose" with "Hx") as "Hs". memory_admin.
     assert (Hkd : (Z.to_nat i < length (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst))%nat).
     { rewrite length_app length_take length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hkd) as [old Hold].
     iDestruct (big_sepL_insert_acc with "Hd") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! x with "Hcell") as "Hd".
     assert (Hfill : <[Z.to_nat i := x]>
       (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst) =
       take (S (Z.to_nat i)) src ++ drop (S (Z.to_nat i)) dst).
     { apply prefix_write_step; [exact Hx|lia]. }
     iAssert (array.array_cells q
       (take (S (Z.to_nat i)) src ++ drop (S (Z.to_nat i)) dst)) with "[Hd]" as "Hd".
     { rewrite <- Hfill. iExact "Hd". }
     iFrame "Hl Hs". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r. iExact "Hd".
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hs Hd]]". unfold I. rewrite Nat2Z.id. iFrame. done.
Qed.
Theorem copy_slices_reduced_wp p q src dst source_offset dest_offset n :
 (source_offset+n <= length src)%nat -> (dest_offset+n <= length dst)%nat ->
 array.array_cells p src -∗ array.array_cells q dst -∗
 WP App (Val (RecV None (Some "args") copy_body))
   (Val (StructV [LitV (LitPtr (p + Z.of_nat source_offset));
     LitV (LitPtr (q + Z.of_nat dest_offset)); LitV (LitInt (Z.of_nat n))]))
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p src ∗
  array.array_cells q (slice_write dst dest_offset (take n (drop source_offset src)))}}.
Proof.
 intros Hsrc Hdst. iIntros "Hs Hd".
 iDestruct (cells_slice_acc p src source_offset n Hsrc with "Hs") as "[Hs Hsrc]".
 iDestruct (cells_slice_acc q dst dest_offset n Hdst with "Hd") as "[Hd Hdst]".
 iApply (wp_wand with "[Hs Hd]").
 { iApply (copy_reduced_wp _ _ _ _ n with "Hs Hd"); rewrite length_take length_drop; lia. }
 iIntros (u) "[%Hu [Hs Hd]]".
 assert (Hsrc_len : length (take n (drop source_offset src)) = n).
 { rewrite length_take length_drop. lia. }
 assert (Hdst_len : length (take n (drop dest_offset dst)) = n).
 { rewrite length_take length_drop. lia. }
 assert (Hout : take n (take n (drop source_offset src)) ++ drop n (take n (drop dest_offset dst)) = take n (drop source_offset src)).
 { rewrite take_take Nat.min_id.
   assert (Hdrop : drop n (take n (drop dest_offset dst)) = []).
   { apply drop_ge. rewrite length_take. lia. }
   rewrite Hdrop. apply app_nil_r. }
 iEval (rewrite Hout) in "Hd".
 iDestruct ("Hsrc" $! (take n (drop source_offset src)) with "[] Hs") as "Hs".
 { done. }
 iEval (rewrite slice_restore) in "Hs".
 iDestruct ("Hdst" $! (take n (drop source_offset src)) with "[] Hd") as "Hd".
 { done. }
 unfold slice_write. rewrite Hsrc_len. iFrame. done.
Qed.
Theorem zero_reduced_wp p dst n : (n <= length dst)%nat ->
 array.array_cells p dst -∗
 WP App (Val (RecV None (Some "args") zero_body))
   (Val (StructV [LitV (LitPtr p); LitV (LitInt (Z.of_nat n))]))
 {{u, ⌜u = LitV LitUnit⌝ ∗
       array.array_cells p (replicate n 0%Z ++ drop n dst)}}.
Proof.
 intros Hdst. iIntros "Hd". iApply wp_app. unfold zero_body, args. hm_pure.
 set (I := fun i : Z => array.array_cells p
   (take (Z.to_nat i) (replicate n 0%Z) ++ drop (Z.to_nat i) dst)).
 iApply (wp_wand with "[Hd]").
 { iApply (loop_wp "zeroI" 0 (Z.of_nat n)
     (put (pv p) (v "zeroI") (int 0)) I with "[Hd]").
   - intros l i Hi. iIntros "Hl Hd".
     unfold put, ptr, pv, v. cbn [subst_var subst_var_val].
     rewrite bool_decide_true; last done. memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hkd : (Z.to_nat i < length
       (take (Z.to_nat i) (replicate n 0%Z) ++ drop (Z.to_nat i) dst))%nat).
     { rewrite length_app length_take length_replicate length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hkd) as [old Hold].
     iDestruct (big_sepL_insert_acc with "Hd") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! 0 with "Hcell") as "Hd".
     assert (Hfill : <[Z.to_nat i := 0]>
       (take (Z.to_nat i) (replicate n 0%Z) ++ drop (Z.to_nat i) dst) =
       take (S (Z.to_nat i)) (replicate n 0%Z) ++ drop (S (Z.to_nat i)) dst).
     { apply prefix_write_step; [apply lookup_replicate_2|]; lia. }
     iAssert (array.array_cells p
       (take (S (Z.to_nat i)) (replicate n 0%Z) ++ drop (S (Z.to_nat i)) dst))
       with "[Hd]" as "Hd".
     { rewrite <- Hfill. iExact "Hd". }
     iFrame "Hl". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r. iExact "Hd".
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu Hd]". unfold I.
 rewrite Nat2Z.id take_ge; last (rewrite length_replicate; lia).
 iFrame. done.
Qed.
End proofs.
