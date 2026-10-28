(** First-vacant-slot selection used by enrollment. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory sessions.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Fixpoint first_free_slot words count : Z :=
 match count with
 | O => -1
 | S i => let previous := first_free_slot words i in
   if bool_decide (previous = -1) && bool_decide (slot_identifier words i = 0)
   then Z.of_nat i else previous
 end.
Lemma first_free_slot_range words count :
 first_free_slot words count = -1 \/ 0 <= first_free_slot words count < Z.of_nat count.
Proof.
 induction count as [|i IH]; cbn [first_free_slot]; [auto|].
 destruct (_ && _)%bool; [right; lia|destruct IH; [auto|right;lia]].
Qed.
Lemma first_free_slot_vacant words count :
 0 <= first_free_slot words count ->
 slot_identifier words (Z.to_nat (first_free_slot words count)) = 0.
Proof.
 induction count as [|i IH]; cbn [first_free_slot]; [lia|].
 destruct (_ && _)%bool eqn:Htest; [|exact IH].
 intros _. apply Bool.andb_true_iff in Htest as [Hprevious Hcurrent].
 rewrite Nat2Z.id. apply bool_decide_eq_true in Hcurrent. exact Hcurrent.
Qed.
Lemma first_free_slot_absent words count :
 first_free_slot words count = -1 <->
 forall i, (i<count)%nat -> slot_identifier words i <> 0.
Proof.
 induction count as [|i IH]; cbn [first_free_slot].
 - split; [intros _ j Hj; lia|auto].
 - destruct (bool_decide (first_free_slot words i = -1)) eqn:Hprevious.
   + apply bool_decide_eq_true in Hprevious. simpl.
     destruct (bool_decide (slot_identifier words i = 0)) eqn:Hcurrent.
     * apply bool_decide_eq_true in Hcurrent. split; [lia|].
       intros H. specialize (H i ltac:(lia)). contradiction.
     * apply bool_decide_eq_false in Hcurrent. split.
       { intros _ j Hj. destruct (decide (j=i)) as [->|Hne]; [exact Hcurrent|]. apply (proj1 IH Hprevious). lia. }
       { intros _. exact Hprevious. }
   + apply bool_decide_eq_false in Hprevious. simpl. split; [contradiction|].
     intros H. exfalso. apply Hprevious. apply (proj2 IH). intros j Hj. apply H. lia.
Qed.
Lemma first_free_slot_exists words count :
 (exists i, (i<count)%nat /\ slot_identifier words i = 0) ->
 0 <= first_free_slot words count < Z.of_nat count.
Proof.
 intros [i [Hi Hzero]]. destruct (first_free_slot_range words count) as [Hnone|Hrange]; [|exact Hrange].
 pose proof (proj1 (first_free_slot_absent words count) Hnone i Hi) as Hne. contradiction.
Qed.
Definition free_slot_loop p found :=
 loop "i" (int 0) (int 16)
  (If (both (eq (StackLoad (Val (LitV (LitStack found)))) (int (-1)))
    (eq (get (slot (pv p) (v "i")) (int 0)) (int 0)))
   (StackAssign (Val (LitV (LitStack found))) (v "i")) unit_e).
Opaque first_free_slot.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem free_slot_loop_wp p words found : length words = 6242%nat ->
 StackId found ↦ₛ LitV (LitInt (-1)) -∗ array.array_cells p words -∗
 WP free_slot_loop p found
 {{u, ⌜u = LitV LitUnit⌝ ∗
  StackId found ↦ₛ LitV (LitInt (first_free_slot words 16)) ∗ array.array_cells p words}}.
Proof.
 intros Hlen. iIntros "Hf Hs". unfold free_slot_loop.
 set (I := fun i : Z => (StackId found ↦ₛ
   LitV (LitInt (first_free_slot words (Z.to_nat i))) ∗ array.array_cells p words)%I).
 iApply (wp_wand with "[Hf Hs]").
 { iApply (loop_wp "i" 0 16
  (If (both (eq (StackLoad (Val (LitV (LitStack found)))) (int (-1)))
    (eq (get (slot (pv p) (v "i")) (int 0)) (int 0)))
   (StackAssign (Val (LitV (LitStack found))) (v "i")) unit_e) I with "[Hf Hs]").
   - intros l i Hi. iIntros "Hl [Hf Hs]".
     unfold both,eq,get,slot,ptr,pv,v,int,op,add,mul,unit_e.
     cbn [subst_var subst_var_val]. rewrite bool_decide_true; last done.
     match goal with |- envs_entails _ (WP ?e {{_}}) =>
      hm_focus e ltac:(fun _ => iApply (wp_stack_load with "Hf"); iIntros "!> _ Hf") end.
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hindex : (2+390*Z.to_nat i < length words)%nat).
     { rewrite Hlen. change (2+390*Z.to_nat i < 2+390*16)%nat. lia. }
     destruct (lookup_lt_is_Some_2 words _ Hindex) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hx|].
     assert (Haddr : p+Z.of_nat (2+390*Z.to_nat i) = p+(2+i*390)+0).
     { rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. change (p+(2+390*i)=p+(2+i*390)+0). ring. }
     rewrite Haddr. iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hs". memory_admin.
     unfold I. rewrite Z2Nat.inj_add; [|lia|lia]. simpl. rewrite Nat.add_1_r.
     change (first_free_slot words (S (Z.to_nat i))) with
       (if bool_decide (first_free_slot words (Z.to_nat i) = -1) &&
         bool_decide (slot_identifier words (Z.to_nat i) = 0)
        then Z.of_nat (Z.to_nat i) else first_free_slot words (Z.to_nat i)).
     unfold slot_identifier. rewrite Hx. simpl.
     destruct (bool_decide (first_free_slot words (Z.to_nat i) = -1) && bool_decide (x=0))%bool.
     + iApply wp_if_true. iApply (wp_bind [StackAssignRCtx (LitV (LitStack found))]).
       iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
       iApply (wp_stack_assign with "Hf"). iIntros "!> _ Hf". rewrite Hki. iFrame.
     + iApply wp_if_false. iApply wp_value'. iFrame.
   - lia.
   - unfold I. change (first_free_slot words 0) with (-1). iFrame.
 }
 iIntros (u) "[%Hu [Hf Hs]]". subst u. iFrame. done.
Qed.
End proofs.
