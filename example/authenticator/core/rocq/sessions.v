(** Concrete session-slot lookup, independent of frontend and platform types. *)
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
Definition slot_identifier (words : list Z) (i : nat) :=
 default 0 (words !! (2 + 390*i)%nat).
Fixpoint scan_identifiers (words : list Z) (id : Z) (count : nat) : Z :=
 match count with
 | O => -1
 | S i => if bool_decide (1 <= id) && bool_decide (slot_identifier words i = id)
          then Z.of_nat i else scan_identifiers words id i
 end.
Lemma scan_identifiers_range words id count :
 scan_identifiers words id count = -1 \/ 0 <= scan_identifiers words id count < Z.of_nat count.
Proof.
 induction count as [|i IH]; simpl; [auto|].
 destruct (_ && _)%bool; [right; lia|]. destruct IH; [auto|right;lia].
Qed.
Lemma scan_identifiers_present words id count :
 0 <= scan_identifiers words id count ->
 exists i, (i < count)%nat /\ scan_identifiers words id count = Z.of_nat i /\
   1 <= id /\ slot_identifier words i = id.
Proof.
 induction count as [|i IH]; cbn [scan_identifiers]; [lia|].
 destruct (_ && _)%bool eqn:Htest.
 - apply Bool.andb_true_iff in Htest as [Hid Hslot].
   apply bool_decide_eq_true in Hid. apply bool_decide_eq_true in Hslot.
   intros _. exists i. repeat split; auto; lia.
 - intros Hge. destruct (IH Hge) as [j [Hj Hrest]].
   exists j. split; [lia|exact Hrest].
Qed.
Lemma scan_identifiers_absent words id count :
 scan_identifiers words id count = -1 <->
 forall i, (i < count)%nat -> id < 1 \/ slot_identifier words i <> id.
Proof.
 induction count as [|i IH]; cbn [scan_identifiers].
 - split; [intros _ j Hj; lia|auto].
 - destruct (_ && _)%bool eqn:Htest.
   + apply Bool.andb_true_iff in Htest as [Hid Hslot].
     apply bool_decide_eq_true in Hid. apply bool_decide_eq_true in Hslot.
     split; [lia|]. intros Hall. specialize (Hall i ltac:(lia)). destruct Hall; [lia|contradiction].
   + assert (Hlast : id < 1 \/ slot_identifier words i <> id).
     { apply Bool.andb_false_iff in Htest as [Hid|Hslot].
       - apply bool_decide_eq_false in Hid. left. lia.
       - apply bool_decide_eq_false in Hslot. right. exact Hslot. }
     rewrite IH. split.
     * intros Hall j Hj. destruct (decide (j=i)) as [->|Hne]; [exact Hlast|apply Hall;lia].
     * intros Hall j Hj. apply Hall. lia.
Qed.
Fixpoint live_identifiers (words : list Z) (count : nat) : list Z :=
 match count with
 | O => []
 | S i => let ids := live_identifiers words i in
   let id := slot_identifier words i in
   if bool_decide (1 <= id) then ids ++ [id] else ids
 end.
Lemma live_identifiers_length words count :
 (length (live_identifiers words count) <= count)%nat.
Proof.
 induction count as [|i IH]; simpl; [lia|].
 destruct (bool_decide _); [rewrite length_app; simpl; lia|lia].
Qed.
Lemma append_prefix_write (ids dst : list Z) x :
 (length ids < length dst)%nat ->
 <[length ids := x]> (ids ++ drop (length ids) dst) =
 (ids ++ [x]) ++ drop (S (length ids)) dst.
Proof.
 intros Hlen. destruct (lookup_lt_is_Some_2 dst (length ids) Hlen) as [old Hold].
 rewrite (drop_S dst old (length ids) Hold) insert_app_r_alt; last lia.
 rewrite Nat.sub_diag. simpl. rewrite <- app_assoc. done.
Qed.
Lemma live_identifiers_zero words : live_identifiers words 0 = [].
Proof. reflexivity. Qed.
Lemma live_identifiers_succ words i :
 live_identifiers words (S i) =
 if bool_decide (1 <= slot_identifier words i)
 then live_identifiers words i ++ [slot_identifier words i]
 else live_identifiers words i.
Proof. reflexivity. Qed.
Lemma live_identifiers_positive words count :
 Forall (fun id => 1 <= id) (live_identifiers words count).
Proof.
 induction count as [|i IH]; cbn [live_identifiers]; [constructor|].
 destruct (bool_decide (1 <= slot_identifier words i)) eqn:Hlive; [|exact IH].
 apply bool_decide_eq_true in Hlive. apply Forall_app. split; [exact IH|].
 constructor; [exact Hlive|constructor].
Qed.
Opaque live_identifiers.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem session_find_wp p words id : length words = 6242%nat ->
 array.array_cells p words -∗
 WP call program.find_body [pv p; int id]
 {{u, ⌜u = LitV (LitInt (scan_identifiers words id 16))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hlen. iIntros "Hs". unfold call, program.find_body, args. hm_pure.
 iApply wp_var_bind. iIntros (found) "Hf".
 cbn [subst_var subst_var_val].
 iApply (wp_bind [SeqCtx (StackLoad (Val (LitV (LitStack found))))]).
 set (I := fun i : Z => (StackId found ↦ₛ
   LitV (LitInt (scan_identifiers words id (Z.to_nat i))) ∗ array.array_cells p words)%I).
 iApply (wp_wand with "[Hf Hs]").
 { iApply (loop_wp "i" 0 16
     (If (both (le (int 1) (int id))
       (eq (get (slot (pv p) (v "i")) (int 0)) (int id)))
       (StackAssign (Val (LitV (LitStack found))) (v "i")) unit_e) I with "[Hf Hs]").
   - intros l i Hi. iIntros "Hl [Hf Hs]".
     unfold both, le, eq, get, slot, ptr, pv, v, int, op, add, mul, unit_e.
     cbn [subst_var subst_var_val]. rewrite bool_decide_true; last done.
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hindex : (2 + 390 * Z.to_nat i < length words)%nat).
     { rewrite Hlen. change (2 + 390 * Z.to_nat i < 2 + 390 * 16)%nat. lia. }
     destruct (lookup_lt_is_Some_2 words _ Hindex) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hx|].
     assert (Haddr : p + Z.of_nat (2 + 390 * Z.to_nat i) = p + (2 + i * 390) + 0).
     { rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki.
       change (p + (2 + 390 * i) = p + (2 + i * 390) + 0). ring. }
     rewrite Haddr. iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hs". memory_admin.
     unfold I. rewrite Z2Nat.inj_add; [|lia|lia]. simpl.
     rewrite Nat.add_1_r. cbn [scan_identifiers]. unfold slot_identifier.
     rewrite Hx. simpl.
     destruct (bool_decide (1 <= id) && bool_decide (x = id))%bool eqn:Htest.
     + iApply wp_if_true.
       iApply (wp_bind [StackAssignRCtx (LitV (LitStack found))]).
       iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
       iApply (wp_stack_assign with "Hf"). iIntros "!> _ Hf".
       rewrite Hki. iFrame.
     + iApply wp_if_false. iApply wp_value'. iFrame.
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hf Hs]]". subst u.
 iApply wp_seq. iApply (wp_stack_load with "Hf"). iIntros "!> _ Hf".
 iExists (LitV (LitInt (scan_identifiers words id 16))). iFrame. done.
Qed.
Theorem session_list_wp p words q dst :
 length words = 6242%nat -> (16 <= length dst)%nat ->
 array.array_cells p words -∗ array.array_cells q dst -∗
 WP call list_body [pv p; pv q]
 {{u, ⌜u = LitV (LitInt (Z.of_nat (length (live_identifiers words 16))))⌝ ∗
   array.array_cells p words ∗ array.array_cells q
     (live_identifiers words 16 ++ drop (length (live_identifiers words 16)) dst)}}.
Proof.
 intros Hlen Hdst. iIntros "Hs Hd". unfold call, list_body, args. hm_pure.
 iApply wp_var_bind. iIntros (count) "Hc".
 cbn [subst_var subst_var_val].
 iApply (wp_bind [SeqCtx (StackLoad (Val (LitV (LitStack count))))]).
 set (I := fun i : Z =>
   (StackId count ↦ₛ LitV (LitInt (Z.of_nat (length (live_identifiers words (Z.to_nat i))))) ∗
    array.array_cells p words ∗ array.array_cells q
      (live_identifiers words (Z.to_nat i) ++
       drop (length (live_identifiers words (Z.to_nat i))) dst))%I).
 iApply (wp_wand with "[Hc Hs Hd]").
 { iApply (loop_wp "i" 0 16
     (Let (Some "id") (get (slot (pv p) (v "i")) (int 0))
       (If (le (int 1) (v "id"))
         (Seq (put (pv q) (StackLoad (Val (LitV (LitStack count)))) (v "id"))
           (StackAssign (Val (LitV (LitStack count)))
             (add (StackLoad (Val (LitV (LitStack count)))) (int 1)))) unit_e))
      I with "[Hc Hs Hd]").
   - intros l i Hi. iIntros "Hl [Hc [Hs Hd]]".
     unfold get, slot, ptr, pv, v, int, op, add, mul, lets, seqs, put, le, unit_e.
     cbn [subst_var subst_var_val binds op ptr].
     rewrite (bool_decide_eq_false_2 ("i" = "id") ltac:(discriminate)).
     rewrite (bool_decide_eq_true_2 ("i" = "i") eq_refl).
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hindex : (2 + 390 * Z.to_nat i < length words)%nat).
     { rewrite Hlen. change (2 + 390 * Z.to_nat i < 2 + 390 * 16)%nat. lia. }
     destruct (lookup_lt_is_Some_2 words _ Hindex) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hx|].
     assert (Haddr : p + Z.of_nat (2 + 390 * Z.to_nat i) = p + (2 + i * 390) + 0).
     { rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki.
       change (p + (2 + 390 * i) = p + (2 + i * 390) + 0). ring. }
     rewrite Haddr. iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hs". memory_admin.
     unfold I. rewrite Z2Nat.inj_add; [|lia|lia]. simpl.
     rewrite Nat.add_1_r live_identifiers_succ. unfold slot_identifier. rewrite Hx. simpl.
     set (ids := live_identifiers words (Z.to_nat i)). fold ids.
     assert (Hids : (length ids < length dst)%nat).
     { pose proof (live_identifiers_length words (Z.to_nat i)). unfold ids. lia. }
     destruct (bool_decide (1 <= x)) eqn:Hlive.
     + iApply wp_if_true.
       match goal with |- envs_entails _ (WP ?e {{_}}) =>
         hm_focus e ltac:(fun _ => iApply (wp_stack_load with "Hc"); iIntros "!> _ Hc") end.
       memory_admin.
       assert (Hout : (length ids < length (ids ++ drop (length ids) dst))%nat).
       { rewrite length_app length_drop. lia. }
       destruct (lookup_lt_is_Some_2 _ _ Hout) as [old Hold].
       iDestruct (big_sepL_insert_acc with "Hd") as "[Hcell Hclose]"; [exact Hold|].
       iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
       iDestruct ("Hclose" $! x with "Hcell") as "Hd".
       iAssert (array.array_cells q ((ids ++ [x]) ++ drop (S (length ids)) dst))
         with "[Hd]" as "Hd".
       { rewrite <- (append_prefix_write ids dst x Hids). iExact "Hd". }
       iApply wp_seq.
       iApply (wp_bind [StackAssignRCtx (LitV (LitStack count))]).
       iApply (wp_bind [BinOpLCtx PlusOp (int 1)]).
       iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
       iApply wp_binop; [reflexivity|]. iIntros "!> _".
       iApply (wp_stack_assign with "Hc"). iIntros "!> _ Hc".
       rewrite length_app. simpl. rewrite Nat.add_1_r Nat2Z.inj_succ.
       iFrame.
     + iApply wp_if_false. iApply wp_value'. iFrame.
   - lia.
   - unfold I. rewrite live_identifiers_zero. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hc [Hs Hd]]]". subst u.
 iApply wp_seq. iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
 iExists (LitV (LitInt (Z.of_nat (length (live_identifiers words 16))))).
 iFrame. done.
Qed.
End proofs.
