(** Read-only input views over one finite owned heap. Different views may
    overlap; exclusive raw ownership is acquired only one view at a time. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import array hm_tactics.
From cjr.authenticator Require Import program refinement memory memory_application.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition buffer_in (heap : gmap Z Z) p (xs : list Z) :=
 forall i x, xs !! i = Some x -> heap !! (p+Z.of_nat i) = Some x.
Section proofs.
Context `{!cjrGS Σ}.
Definition input_cells (heap : gmap Z Z) : iProp Σ :=
 [∗ map] address ↦ x ∈ heap, RawId address ↦ᵣ LitV (LitInt x).
Lemma input_buffer_acc heap p xs : buffer_in heap p xs ->
 input_cells heap -∗ array.array_cells p xs ∗
 (array.array_cells p xs -∗ input_cells heap).
Proof.
 revert heap p. induction xs as [|x xs IH]; intros heap p Hview.
 - iIntros "Hheap". rewrite /array.array_cells big_sepL_nil. iFrame. auto.
 - assert (Hhead : heap !! p = Some x).
   { specialize (Hview 0%nat x eq_refl). rewrite Z.add_0_r in Hview. exact Hview. }
   assert (Htail : buffer_in (delete p heap) (p+1) xs).
   { intros i y Hy. rewrite lookup_delete_ne; last (intros H; lia).
     replace (p+1+Z.of_nat i) with (p+Z.of_nat (S i)) by (rewrite Nat2Z.inj_succ; lia).
     apply (Hview (S i) y). exact Hy. }
   iIntros "Hheap". rewrite /input_cells (big_sepM_delete _ heap p x Hhead).
   iDestruct "Hheap" as "[Hhead Htail]".
   iDestruct (IH (delete p heap) (p+1) Htail with "Htail") as "[Htail Hclose]".
   assert (Hcells : array.array_cells p (x::xs) ⊣⊢
     RawId p ↦ᵣ LitV (LitInt x) ∗ array.array_cells (p+1) xs).
   { unfold array.array_cells. rewrite big_sepL_cons Z.add_0_r.
     f_equiv. apply big_sepL_proper. intros i y Hy.
     rewrite Nat2Z.inj_succ. replace (p+Z.succ (Z.of_nat i)) with (p+1+Z.of_nat i) by lia. done. }
   iSplitL "Hhead Htail".
   + rewrite Hcells. iFrame.
   + iIntros "Hcells". rewrite Hcells. iDestruct "Hcells" as "[Hhead Htail]".
     iDestruct ("Hclose" with "Htail") as "Htail". iFrame.
Qed.
End proofs.
Section application_proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem bytes_reduced_wp p xs n : (n <= length xs)%nat ->
 array.array_cells p xs -∗
 WP App (Val (RecV None (Some "args") byte_body))
   (Val (StructV [LitV (LitPtr p); LitV (LitInt (Z.of_nat n))]))
 {{u, ⌜u = LitV (LitBool (bytes_test (take n xs)))⌝ ∗ array.array_cells p xs}}.
Proof.
 intros Hn. iIntros "Hs". iApply wp_app. unfold byte_body, args. hm_pure.
 iApply wp_var_bind. iIntros (valid) "Hv".
 cbn [subst_var subst_var_val].
 iApply (wp_bind [SeqCtx (StackLoad (Val (LitV (LitStack valid))))]).
 set (I := fun i : Z => (StackId valid ↦ₛ
    LitV (LitBool (bytes_test (take (Z.to_nat i) xs))) ∗ array.array_cells p xs)%I).
 iApply (wp_wand with "[Hv Hs]").
 { iApply (loop_wp "i" 0 (Z.of_nat n)
     (If (range (get (pv p) (v "i")) 0 255) unit_e
       (StackAssign (Val (LitV (LitStack valid))) no)) I with "[Hv Hs]").
   - intros l i Hi. iIntros "Hl [Hv Hs]".
     unfold range, both, le, get, ptr, pv, v, int, op, unit_e, no.
     cbn [subst_var subst_var_val]. rewrite bool_decide_true; last done.
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hk : (Z.to_nat i < length xs)%nat) by lia.
     destruct (lookup_lt_is_Some_2 xs (Z.to_nat i) Hk) as [x Hx].
     do 2 (iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]";
       [exact Hx|]; rewrite Hki;
       iApply (wp_load with "Hcell"); iIntros "!> _ Hcell";
       iDestruct ("Hclose" with "Hcell") as "Hs"; memory_admin).
     fold (byte_test x). unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r (bytes_test_step xs (Z.to_nat i) x Hx).
     destruct (byte_test x) eqn:Hbyte.
     + iApply wp_if_true. iApply wp_value'. rewrite Bool.andb_true_r. iFrame.
     + iApply wp_if_false. rewrite Bool.andb_false_r.
       iApply (wp_stack_assign with "Hv"). iIntros "!> _ Hv". iFrame.
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hv Hs]]". subst u. unfold I. rewrite Nat2Z.id.
 iApply wp_seq. iApply (wp_stack_load with "Hv"). iIntros "!> _ Hv".
 iExists (LitV (LitBool (bytes_test (take n xs)))). iFrame. done.
Qed.
Theorem bytes_view_reduced_wp heap p xs : buffer_in heap p xs ->
 input_cells heap -∗
 WP App (Val (RecV None (Some "args") byte_body))
   (Val (StructV [LitV (LitPtr p); LitV (LitInt (Z.of_nat (length xs)))]))
 {{u, ⌜u = LitV (LitBool (bytes_test xs))⌝ ∗ input_cells heap}}.
Proof.
 intros Hview. iIntros "Hheap".
 iDestruct (input_buffer_acc heap p xs Hview with "Hheap") as "[Hs Hclose]".
 iApply (wp_wand with "[Hs]").
 { iApply (bytes_reduced_wp p xs (length xs) with "Hs"). lia. }
 iIntros (u) "[%Hu Hs]". iDestruct ("Hclose" with "Hs") as "Hheap".
 rewrite take_ge in Hu; last lia. iFrame. done.
Qed.
Theorem copy_view_slice_reduced_wp heap p xs q dst offset n :
 buffer_in heap p xs -> (n <= length xs)%nat -> (offset+n <= length dst)%nat ->
 input_cells heap -∗ array.array_cells q dst -∗
 WP App (Val (RecV None (Some "args") copy_body))
   (Val (StructV [LitV (LitPtr p); LitV (LitPtr (q+Z.of_nat offset)); LitV (LitInt (Z.of_nat n))]))
 {{u, ⌜u = LitV LitUnit⌝ ∗ input_cells heap ∗
   array.array_cells q (slice_write dst offset (take n xs))}}.
Proof.
 intros Hview Hsrc Hdst. iIntros "Hheap Hd".
 iDestruct (input_buffer_acc heap p xs Hview with "Hheap") as "[Hs Hclose]".
 iApply (wp_wand with "[Hs Hd]").
 { pose proof (copy_slices_reduced_wp p q xs dst 0 offset n ltac:(lia) Hdst) as Hcopy.
   simpl in Hcopy. rewrite Z.add_0_r in Hcopy. iApply (Hcopy with "Hs Hd"). }
 iIntros (u) "[%Hu [Hs Hd]]". iDestruct ("Hclose" with "Hs") as "Hheap".
 iFrame. done.
Qed.
End application_proofs.

