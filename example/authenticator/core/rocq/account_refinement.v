(** Concrete account operations and the layout boundary to the abstract model. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory memory_application sessions accounts account_model.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition cleared_slot words index :=
 take (2 + 390*index) words ++ replicate 390 0%Z ++ drop (2+390*index+390) words.
Definition removed_words words id :=
 let found := scan_identifiers words id 16 in
 if bool_decide (0 <= found) then
 let cleared := cleared_slot words (Z.to_nat found) in
 <[1%nat := default 0 (words !! 1%nat) - 1]> cleared
 else words.
Lemma cleared_slot_length words index :
 (2+390*index+390 <= length words)%nat -> length (cleared_slot words index) = length words.
Proof.
 intros Hbound. unfold cleared_slot. rewrite !length_app length_replicate length_take length_drop. lia.
Qed.
Lemma cleared_slot_header words index :
 (2 <= length words)%nat -> cleared_slot words index !! 1%nat = words !! 1%nat.
Proof.
 intros Hlen. unfold cleared_slot. rewrite lookup_app_l.
 - rewrite lookup_take; [reflexivity|lia].
 - rewrite length_take. lia.
Qed.
Opaque scan_identifiers.
Lemma cleared_slot_zero words index j :
 (2+390*index+390 <= length words)%nat -> (j < 390)%nat ->
 cleared_slot words index !! (2+390*index+j)%nat = Some 0%Z.
Proof.
 intros Hbounds Hj. unfold cleared_slot.
 rewrite lookup_app_r; last (rewrite length_take; lia).
 rewrite length_take Nat.min_l; last lia.
 replace (2+390*index+j-(2+390*index))%nat with j by lia.
 rewrite lookup_app_l; last (rewrite length_replicate; lia).
 apply lookup_replicate_2. exact Hj.
Qed.
Lemma removed_words_cleared words id j :
 length words = 6242%nat -> 0 <= scan_identifiers words id 16 -> (j < 390)%nat ->
 removed_words words id !! (2+390*Z.to_nat (scan_identifiers words id 16)+j)%nat = Some 0%Z.
Proof.
 intros Hlen Hfound Hj. unfold removed_words. rewrite bool_decide_true; last exact Hfound.
 cbn zeta. rewrite list_lookup_insert_ne; last (intros H; lia).
 apply cleared_slot_zero; last exact Hj.
 pose proof (scan_identifiers_range words id 16) as Hrange.
 rewrite Hlen. change (2+390*Z.to_nat (scan_identifiers words id 16)+390 <= 2+390*16)%nat. lia.
Qed.
Theorem removed_secret_zero words id j :
 length words = 6242%nat -> 0 <= scan_identifiers words id 16 -> (j < 128)%nat ->
 removed_words words id !!
 (2+390*Z.to_nat (scan_identifiers words id 16)+262+j)%nat = Some 0%Z.
Proof.
 intros Hlen Hfound Hj.
 replace (2+390*Z.to_nat (scan_identifiers words id 16)+262+j)%nat with
 (2+390*Z.to_nat (scan_identifiers words id 16)+(262+j))%nat by lia.
 apply removed_words_cleared; [exact Hlen|exact Hfound|lia].
Qed.
Definition slot_offset index := (2+390*index)%nat.
Definition metadata_lengths_valid (words : list Z) := forall index, (index < 16)%nat ->
 0 <= default 0 (words !! (slot_offset index+3)%nat) <= 128 /\
 0 <= default 0 (words !! (slot_offset index+4)%nat) <= 128.
Definition metadata_words words index dst :=
 let offset := slot_offset index in
 let label_length := Z.to_nat (default 0 (words !! (offset+3)%nat)) in
 let issuer_length := Z.to_nat (default 0 (words !! (offset+4)%nat)) in
 let dst1 := slice_write dst 0 (take 4 (drop (offset+1) words)) in
 let dst2 := slice_write dst1 4 (take label_length (drop (offset+6) words)) in
 slice_write dst2 132 (take issuer_length (drop (offset+134) words)).
Definition read_words words id dst :=
 let found := scan_identifiers words id 16 in
 if bool_decide (0 <= found) then metadata_words words (Z.to_nat found) dst else dst.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma zero_body_session_closed x : subst "session" x zero_body = zero_body.
Proof. reflexivity. Qed.
Lemma zero_body_id_closed x : subst "id" x zero_body = zero_body.
Proof. reflexivity. Qed.
Lemma zero_body_index_closed x : subst "index" x zero_body = zero_body.
Proof. reflexivity. Qed.
Lemma copy_body_session_closed x : subst "session" x copy_body = copy_body.
Proof. reflexivity. Qed.
Lemma copy_body_id_closed x : subst "id" x copy_body = copy_body.
Proof. reflexivity. Qed.
Lemma copy_body_index_closed x : subst "index" x copy_body = copy_body.
Proof. reflexivity. Qed.
Lemma copy_body_entry_closed x : subst "entry" x copy_body = copy_body.
Proof. reflexivity. Qed.
Opaque zero_body copy_body.
#[local] Hint Rewrite zero_body_session_closed zero_body_id_closed zero_body_index_closed copy_body_session_closed copy_body_id_closed copy_body_index_closed copy_body_entry_closed : account_subst.
Ltac account_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with account_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
   hm_focus e ltac:(fun _ => first [iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item]; autorewrite with account_subst.
Theorem session_remove_wp p words id : length words = 6242%nat ->
 array.array_cells p words -∗
 WP call remove_body [pv p; int id]
 {{u, ⌜u = LitV (LitBool (bool_decide (0 <= scan_identifiers words id 16)))⌝ ∗
       array.array_cells p (removed_words words id)}}.
Proof.
 intros Hlen. iIntros "Hs". unfold call at 1. unfold remove_body, args.
 hm_args. iApply wp_app. simpl. hm_admin.
 match goal with |- envs_entails _ (WP Let ?x ?e ?b {{_}}) =>
   iApply (wp_bind [LetCtx x b]) end.
 iApply (wp_wand with "[Hs]").
 { iApply (session_find_wp p words id Hlen with "Hs"). }
 iIntros (u) "[%Hu Hs]". subst u. hm_pure.
 destruct (bool_decide (0 <= scan_identifiers words id 16)) eqn:Hfound.
 - apply bool_decide_eq_true in Hfound. iApply wp_if_true.
   pose proof (scan_identifiers_range words id 16) as Hrange.
   set (index := Z.to_nat (scan_identifiers words id 16)).
   assert (Hindex : (index < 16)%nat) by (unfold index; lia).
   assert (Hki : Z.of_nat index = scan_identifiers words id 16) by (unfold index; lia).
   set (offset := (2+390*index)%nat).
   assert (Hbounds : (offset+390 <= length words)%nat) by (unfold offset; rewrite Hlen; change (2+390*index+390 <= 2+390*16)%nat; lia).
   iDestruct (cells_slice_acc p words offset 390 Hbounds with "Hs") as "[Hslot Hclose]".
   match goal with |- envs_entails _ (WP Seq ?e ?b {{_}}) =>
     iApply (wp_bind [SeqCtx b]) end.
   account_args.
   assert (Haddr : p + (2 + scan_identifiers words id 16 * 390) = p + Z.of_nat offset).
   { unfold offset. rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. ring. }
   rewrite Haddr.
   iApply (wp_wand with "[Hslot]").
   { iApply (zero_reduced_wp _ _ 390 with "Hslot").
     rewrite length_take length_drop. lia. }
   iIntros (u) "[%Hu Hslot]". subst u.
   assert (Hdrop : drop 390 (take 390 (drop offset words)) = []).
   { apply drop_ge. rewrite length_take. lia. }
   iEval (rewrite Hdrop app_nil_r) in "Hslot".
   iDestruct ("Hclose" $! (replicate 390 0%Z) with "[] Hslot") as "Hs".
   { iPureIntro. apply length_replicate. }
   iApply wp_seq. hm_pure.
   iAssert (array.array_cells p (cleared_slot words index)) with "[Hs]" as "Hs".
   { iExact "Hs". }
   assert (Hheader : (1 < length words)%nat) by (rewrite Hlen; change (1<6242)%nat; lia).
   destruct (lookup_lt_is_Some_2 words 1 Hheader) as [count Hcount].
   assert (Hclearcount : cleared_slot words index !! 1%nat = Some count).
   { rewrite cleared_slot_header; [exact Hcount|lia]. }
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hclearcount|].
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". hm_pure.
   iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Hclearcount|].
   iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" $! (count-1) with "Hcell") as "Hs". hm_pure.
   rewrite /removed_words bool_decide_true; last exact Hfound.
   rewrite Hcount. simpl. iFrame. done.
 - apply bool_decide_eq_false in Hfound. iApply wp_if_false. iApply wp_value'.
   rewrite /removed_words bool_decide_false; last exact Hfound. iFrame. done.
Qed.
Theorem session_new_representation_wp :
 ⊢ WP new_body {{u, ∃ p,
 ⌜u = LitV (LitPtr p)⌝ ∗ array.array_cells p (1::replicate 6241 0%Z) ∗
 RawId p ↦ᵦ 6242 ∗ ⌜represents_session (1::replicate 6241 0%Z) empty_session⌝}}.
Proof.
 iApply (wp_wand with "[]"); [iApply session_new_wp|].
 iIntros (u) "H". iDestruct "H" as (p) "[%Hu [Hs Hb]]".
 iExists p. iFrame. iSplit; [done|]. iPureIntro. apply initialized_session_representation.
Qed.
Theorem session_read_wp p q words dst id :
 length words = 6242%nat -> (260 <= length dst)%nat -> metadata_lengths_valid words ->
 array.array_cells p words -∗ array.array_cells q dst -∗
 WP call read_body [pv p; int id; pv q]
 {{u, ⌜u = LitV (LitBool (bool_decide (0 <= scan_identifiers words id 16)))⌝ ∗
   array.array_cells p words ∗ array.array_cells q (read_words words id dst)}}.
Proof.
 intros Hlen Hdst Hmeta. iIntros "Hs Hd".
 unfold call at 1. unfold read_body, args. hm_args. iApply wp_app. simpl. hm_admin.
 match goal with |- envs_entails _ (WP Let ?x ?e ?b {{_}}) =>
   iApply (wp_bind [LetCtx x b]) end.
 iApply (wp_wand with "[Hs]").
 { iApply (session_find_wp p words id Hlen with "Hs"). }
 iIntros (u) "[%Hu Hs]". subst u. hm_pure.
 destruct (bool_decide (0 <= scan_identifiers words id 16)) eqn:Hfound.
 - apply bool_decide_eq_true in Hfound. iApply wp_if_true.
   pose proof (scan_identifiers_range words id 16) as Hrange.
   set (index := Z.to_nat (scan_identifiers words id 16)).
   assert (Hindex : (index < 16)%nat) by (unfold index; lia).
   assert (Hki : Z.of_nat index = scan_identifiers words id 16) by (unfold index; lia).
   set (offset := slot_offset index).
   assert (Hbound : (offset+390 <= length words)%nat).
   { unfold offset, slot_offset. rewrite Hlen. change (2+390*index+390 <= 2+390*16)%nat. lia. }
   account_args.
   assert (Haddr : p + (2 + scan_identifiers words id 16 * 390) = p + Z.of_nat offset).
   { unfold offset, slot_offset. rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. ring. }
   rewrite Haddr.
   replace (p+Z.of_nat offset+1) with (p+Z.of_nat (offset+1)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_wand with "[Hs Hd]").
   { pose proof (copy_slices_reduced_wp p q words dst (offset+1) 0 4 ltac:(lia) ltac:(lia)) as Hcopy.
     simpl in Hcopy. rewrite Z.add_0_r in Hcopy. iApply (Hcopy with "Hs Hd"). }
   iIntros (u) "[%Hu [Hs Hd]]". subst u. iApply wp_seq.
   set (dst1 := slice_write dst 0 (take 4 (drop (offset+1) words))).
   assert (Hdst1 : length dst1 = length dst).
   { unfold dst1. apply slice_write_length. rewrite length_take. lia. }
   account_args.
   assert (Hlabelindex : (offset+3 < length words)%nat) by lia.
   destruct (lookup_lt_is_Some_2 words _ Hlabelindex) as [label_length Hlabel].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hlabel|].
   replace (p+Z.of_nat offset+3) with (p+Z.of_nat (offset+3)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". account_args.
   destruct (Hmeta index Hindex) as [Hlabelbound Hissuerbound].
   change (0 <= default 0 (words !! (offset+3)%nat) <= 128) in Hlabelbound.
   rewrite Hlabel in Hlabelbound. simpl in Hlabelbound.
   assert (Hlabelnat : Z.of_nat (Z.to_nat label_length) = label_length) by lia.
   replace (p+Z.of_nat offset+6) with (p+Z.of_nat (offset+6)) by (rewrite Nat2Z.inj_add; simpl; ring).
   rewrite <- Hlabelnat at 1.
   iApply (wp_wand with "[Hs Hd]").
   { iApply (copy_slices_reduced_wp p q words dst1 (offset+6) 4 (Z.to_nat label_length) with "Hs Hd"); lia. }
   iIntros (u) "[%Hu [Hs Hd]]". subst u. iApply wp_seq.
   set (dst2 := slice_write dst1 4 (take (Z.to_nat label_length) (drop (offset+6) words))).
   assert (Hdst2 : length dst2 = length dst).
   { unfold dst2. rewrite <- Hdst1. apply slice_write_length. rewrite length_take. lia. }
   account_args.
   assert (Hissuerindex : (offset+4 < length words)%nat) by lia.
   destruct (lookup_lt_is_Some_2 words _ Hissuerindex) as [issuer_length Hissuer].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hissuer|].
   replace (p+Z.of_nat offset+4) with (p+Z.of_nat (offset+4)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". account_args.
   change (0 <= default 0 (words !! (offset+4)%nat) <= 128) in Hissuerbound.
   rewrite Hissuer in Hissuerbound. simpl in Hissuerbound.
   assert (Hissuernat : Z.of_nat (Z.to_nat issuer_length) = issuer_length) by lia.
   replace (p+Z.of_nat offset+134) with (p+Z.of_nat (offset+134)) by (rewrite Nat2Z.inj_add; simpl; ring).
   rewrite <- Hissuernat at 1.
   iApply (wp_wand with "[Hs Hd]").
   { iApply (copy_slices_reduced_wp p q words dst2 (offset+134) 132 (Z.to_nat issuer_length) with "Hs Hd"); lia. }
   iIntros (u) "[%Hu [Hs Hd]]". subst u. hm_pure.
   rewrite /read_words bool_decide_true; last exact Hfound.
   fold index. unfold metadata_words. fold offset. rewrite Hlabel Hissuer. simpl.
   fold dst1. fold dst2. iFrame. done.
 - apply bool_decide_eq_false in Hfound. iApply wp_if_false. iApply wp_value'.
   rewrite /read_words bool_decide_false; last exact Hfound. iFrame. done.
Qed.
End proofs.
