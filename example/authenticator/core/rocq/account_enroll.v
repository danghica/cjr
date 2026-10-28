(** Enrollment commits validated bytes to the first vacant physical slot. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory memory_application
 input_memory sessions account_slots base32 base32_contracts base32_input.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Set Printing Depth 20.
Definition enrolled_words words index label issuer secret digits period :=
 let offset := (2+390*index)%nat in
 let id := default 0 (words !! 0%nat) in
 let metadata :=
  <[(offset+5)%nat:=Z.of_nat (length secret)]>
  (<[(offset+4)%nat:=Z.of_nat (length issuer)]>
  (<[(offset+3)%nat:=Z.of_nat (length label)]>
  (<[(offset+2)%nat:=period]>
  (<[(offset+1)%nat:=digits]>
  (<[(offset+0)%nat:=id]> words))))) in
 let labeled := slice_write metadata (offset+6) label in
 let issued := slice_write labeled (offset+134) issuer in
 let filled := slice_write issued (offset+262) secret in
 <[1%nat:=default 0 (words !! 1%nat)+1]>
 (<[0%nat:=id+1]> filled).
Definition enroll_bound_name name :=
 name="session" \/ name="label" \/ name="labelLen" \/ name="issuer" \/ name="issuerLen" \/
 name="secret" \/ name="secretLen" \/ name="digits" \/ name="period" \/ name="decoded" \/
 name="n" \/ name="freeSlot" \/ name="entry" \/ name="id".
Transparent copy_body zero_body byte_body.
Lemma copy_body_enroll_closed name x : enroll_bound_name name -> subst name x copy_body = copy_body.
Proof. intros H; unfold enroll_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Lemma zero_body_enroll_closed name x : enroll_bound_name name -> subst name x zero_body = zero_body.
Proof. intros H; unfold enroll_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Lemma byte_body_enroll_closed name x : enroll_bound_name name -> subst name x byte_body = byte_body.
Proof. intros H; unfold enroll_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Lemma copy_body_freeSlot_closed l : subst_var "freeSlot" l copy_body = copy_body.
Proof. reflexivity. Qed.
Opaque copy_body zero_body byte_body first_free_slot.
#[local] Hint Rewrite copy_body_enroll_closed zero_body_enroll_closed byte_body_enroll_closed
 using (unfold enroll_bound_name; tauto) : enroll_subst.
#[local] Hint Rewrite copy_body_freeSlot_closed : enroll_subst.
Ltac enroll_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with enroll_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item]; autorewrite with enroll_subst.
Ltac enroll_slot_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with enroll_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackLoad _ {{_}}) =>
    iApply (wp_stack_load with "Hf"); iIntros "!> _ Hf" end |
   iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item]; autorewrite with enroll_subst.
Ltac enroll_write p offset k :=
 iEval (fold array.array_cells) in "Hs";
 let htype := iTypeOf "Hs" in
 let current := lazymatch htype with Some (_, ([∗ list] k ↦ y ∈ ?ws, _)%I) => ws | Some (_, array.array_cells _ ?ws) => ws end in
 let Hindex := fresh "Hwrite_index" in
 assert (Hindex : (offset+k < length current)%nat) by (rewrite ?length_insert; lia);
 let old := fresh "old" in let Hold := fresh "Hwrite_lookup" in
 destruct (lookup_lt_is_Some_2 current _ Hindex) as [old Hold];
 iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Hold|];
 let Hptr := fresh "Hwrite_pointer" in
 assert (Hptr : p+Z.of_nat (offset+k) = p+Z.of_nat offset+Z.of_nat k)
   by (rewrite Nat2Z.inj_add; ring);
 iEval (rewrite Hptr) in "Hcell";
 iEval (rewrite Hptr) in "Hclose";
 iApply (wp_store with "Hcell"); iIntros "!> _ Hcell";
 iDestruct ("Hclose" with "Hcell") as "Hs"; enroll_args.
Definition enroll_slot_body p lp labelLen ip issuerLen dp secretLen digits period :=
 vars [("freeSlot",int (-1))]
 (Seq (loop "i" (int 0) (int 16)
  (If (both (eq (v "freeSlot") (int (-1))) (eq (get (slot (pv p) (v "i")) (int 0)) (int 0)))
   (Assign "freeSlot" (v "i")) unit_e))
 (lets [("entry",slot (pv p) (v "freeSlot"));("id",get (pv p) (int 0))]
  (seqs [put (v "entry") (int 0) (v "id");put (v "entry") (int 1) (int digits);
   put (v "entry") (int 2) (int period);put (v "entry") (int 3) (int labelLen);
   put (v "entry") (int 4) (int issuerLen);put (v "entry") (int 5) (int secretLen);
   copy (pv lp) (ptr (v "entry") (int 6)) (int labelLen);
   copy (pv ip) (ptr (v "entry") (int 134)) (int issuerLen);
   copy (pv dp) (ptr (v "entry") (int 262)) (int secretLen);
   put (pv p) (int 0) (add (v "id") (int 1));
   put (pv p) (int 1) (add (get (pv p) (int 1)) (int 1))] (v "id")))).
Lemma slice_write_lookup_before dst offset replacement i :
 (i < offset)%nat -> (i < length dst)%nat ->
 slice_write dst offset replacement !! i = dst !! i.
Proof.
 intros Hoffset Hlength. unfold slice_write. rewrite lookup_app_l; last (rewrite length_take; lia).
 rewrite lookup_take; [reflexivity|exact Hoffset].
Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem enroll_slot_wp heap p words lp label ip issuer dp decoded n digits period :
 length words = 6242%nat -> (length label <=128)%nat -> (length issuer <=128)%nat ->
 (n <= 128)%nat -> (n <= length decoded)%nat ->
 buffer_in heap lp label -> buffer_in heap ip issuer ->
 (exists i, (i<16)%nat /\ slot_identifier words i = 0) ->
 input_cells heap -∗ array.array_cells p words -∗ array.array_cells dp decoded -∗
 WP enroll_slot_body p lp (Z.of_nat (length label)) ip (Z.of_nat (length issuer)) dp
   (Z.of_nat n) digits period
 {{u, ⌜u = LitV (LitInt (default 0 (words !! 0%nat)))⌝ ∗ input_cells heap ∗
   array.array_cells dp decoded ∗ array.array_cells p
    (enrolled_words words (Z.to_nat (first_free_slot words 16)) label issuer (take n decoded) digits period)}}.
Proof.
 intros Hlen Hlabel Hissuer Hn Hdecoded Hlabelview Hissuerview Hfree.
 iIntros "Hheap Hs Hd". unfold enroll_slot_body,vars.
 iApply wp_var_bind. iIntros (found) "Hf". cbn [subst_var subst_var_val].
 autorewrite with enroll_subst.
 match goal with |- envs_entails _ (WP Seq ?e ?body {{_}}) =>
  iApply (wp_bind [SeqCtx body]) end.
 iApply (wp_wand with "[Hf Hs]").
 { iApply (free_slot_loop_wp p words found Hlen with "Hf Hs"). }
 iIntros (u) "[%Hu [Hf Hs]]". subst u. iApply wp_seq.
 unfold lets,seqs,slot,ptr,get,put,copy,v,int,add,mul,op,pv.
 cbn [subst_var subst_var_val]. autorewrite with enroll_subst.
 enroll_slot_args.
 assert (Hheader : (0 < length words)%nat) by (rewrite Hlen; change (0<6242)%nat; vm_compute; lia).
 destruct (lookup_lt_is_Some_2 words 0 Hheader) as [id Hid].
 iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hid|].
 iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
 iDestruct ("Hclose" with "Hcell") as "Hs". hm_pure.
 pose proof (first_free_slot_exists words 16 Hfree) as Hrange.
 set (index := Z.to_nat (first_free_slot words 16)).
 assert (Hindex : (index < 16)%nat) by (unfold index; lia).
 assert (Hki : Z.of_nat index = first_free_slot words 16) by (unfold index; lia).
 set (offset := (2+390*index)%nat).
 assert (Hbound : (offset+390 <= length words)%nat).
 { unfold offset. rewrite Hlen. change (2+390*index+390 <= 2+390*16)%nat. lia. }
 assert (Haddr : p+(2+first_free_slot words 16*390) = p+Z.of_nat offset).
 { unfold offset. rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. ring. }
 rewrite Haddr.
 enroll_write p offset (0%nat).
 enroll_write p offset (1%nat).
 enroll_write p offset (2%nat).
 enroll_write p offset (3%nat).
 enroll_write p offset (4%nat).
 enroll_write p offset (5%nat).
 enroll_args.
 set (metadata := <[(offset+5)%nat:=Z.of_nat n]>
  (<[(offset+4)%nat:=Z.of_nat (length issuer)]>
  (<[(offset+3)%nat:=Z.of_nat (length label)]>
  (<[(offset+2)%nat:=period]>
  (<[(offset+1)%nat:=digits]> (<[(offset+0)%nat:=id]> words)))))).
 iAssert (array.array_cells p metadata) with "[Hs]" as "Hs".
 { unfold metadata. iExact "Hs". }

 assert (Hmetadata : length metadata = length words) by (unfold metadata; rewrite !length_insert; reflexivity).
 replace (p+Z.of_nat offset+6) with (p+Z.of_nat (offset+6)) by (rewrite Nat2Z.inj_add; simpl; ring).
 iApply (wp_wand with "[Hheap Hs]").
 { iApply (copy_view_slice_reduced_wp heap lp label p metadata (offset+6) (length label)
     Hlabelview ltac:(lia) ltac:(lia) with "Hheap Hs"). }
 iIntros (u) "[%Hu [Hheap Hs]]". subst u.
 assert (Htake_label : take (length label) label = label) by (apply take_ge; lia).
 iEval (rewrite Htake_label) in "Hs".
 set (labeled := slice_write metadata (offset+6) label).
 assert (Hlabeled : length labeled = length words).
 { unfold labeled. rewrite <- Hmetadata. apply slice_write_length. lia. }
 iApply wp_seq. enroll_args.
 replace (p+Z.of_nat offset+134) with (p+Z.of_nat (offset+134)) by (rewrite Nat2Z.inj_add; simpl; ring).
 iApply (wp_wand with "[Hheap Hs]").
 { iApply (copy_view_slice_reduced_wp heap ip issuer p labeled (offset+134) (length issuer)
     Hissuerview ltac:(lia) ltac:(lia) with "Hheap Hs"). }
 iIntros (u) "[%Hu [Hheap Hs]]". subst u.
 assert (Htake_issuer : take (length issuer) issuer = issuer) by (apply take_ge; lia).
 iEval (rewrite Htake_issuer) in "Hs".
 set (issued := slice_write labeled (offset+134) issuer).
 assert (Hissued : length issued = length words).
 { unfold issued. rewrite <- Hlabeled. apply slice_write_length. lia. }
 iApply wp_seq. enroll_args.
 replace (p+Z.of_nat offset+262) with (p+Z.of_nat (offset+262)) by (rewrite Nat2Z.inj_add; simpl; ring).
 iApply (wp_wand with "[Hd Hs]").
 { pose proof (copy_slices_reduced_wp dp p decoded issued 0 (offset+262) n ltac:(lia) ltac:(lia)) as Hcopy.
   simpl in Hcopy. rewrite Z.add_0_r in Hcopy. iApply (Hcopy with "Hd Hs"). }
 iIntros (u) "[%Hu [Hd Hs]]". subst u.
 set (filled := slice_write issued (offset+262) (take n decoded)).
 assert (Hsecretlen : length (take n decoded) = n) by (rewrite length_take; lia).
 assert (Hfilled : length filled = length words).
 { unfold filled. rewrite <- Hissued. apply slice_write_length. rewrite Hsecretlen. lia. }
 iApply wp_seq. hm_pure.
 iAssert (array.array_cells p filled) with "[Hs]" as "Hs".
 { iExact "Hs". }
 assert (Hheader0 : (0 < length filled)%nat) by lia.
 destruct (lookup_lt_is_Some_2 filled 0 Hheader0) as [oldhead Holdhead].
 iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Holdhead|].
 iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
 iDestruct ("Hclose" $! (id+1) with "Hcell") as "Hs". enroll_args.
 assert (Hcountpos : (1 < length words)%nat) by (rewrite Hlen; change (1<6242)%nat; vm_compute; lia).
 destruct (lookup_lt_is_Some_2 words 1 Hcountpos) as [count Hcount].
 assert (Hfilledcount : filled !! 1%nat = Some count).
 { unfold filled. rewrite slice_write_lookup_before; [|unfold offset;lia|lia].
   unfold issued. rewrite slice_write_lookup_before; [|unfold offset;lia|lia].
   unfold labeled. rewrite slice_write_lookup_before; [|unfold offset;lia|lia].
   unfold metadata. rewrite !list_lookup_insert_ne; try (unfold offset;lia). exact Hcount. }
 assert (Hcountcurrent : (<[(0+0)%nat:=id+1]> filled) !! 1%nat = Some count).
 { rewrite list_lookup_insert_ne; [exact Hfilledcount|lia]. }
 iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hcountcurrent|].
 iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
 iDestruct ("Hclose" with "Hcell") as "Hs". hm_pure.
 iDestruct (big_sepL_insert_acc with "Hs") as "[Hcell Hclose]"; [exact Hcountcurrent|].
 iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
 iDestruct ("Hclose" $! (count+1) with "Hcell") as "Hs". enroll_args.
 rewrite /enrolled_words. fold offset. rewrite Hid Hcount. simpl.
 rewrite Hsecretlen. fold metadata labeled issued filled.
 iExists (LitV (LitInt (first_free_slot words 16))). iFrame. done.
Qed.
End proofs.
