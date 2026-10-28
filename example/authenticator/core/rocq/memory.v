(** Owned-buffer loop contracts shared by the cryptographic and session proofs. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import ectx_lifting.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition pv p := Val (LitV (LitPtr p)).
Lemma prefix_write_step (src dst : list Z) i x :
 src !! i = Some x -> (i < length dst)%nat ->
 <[i := x]> (take i src ++ drop i dst) = take (S i) src ++ drop (S i) dst.
Proof.
 intros Hsrc Hlen. assert (Hsrc_len : (i < length src)%nat) by (eapply lookup_lt_Some; eauto).
 destruct (lookup_lt_is_Some_2 dst i Hlen) as [old Hold].
 rewrite (take_S_r src i x Hsrc). rewrite (drop_S dst old i Hold).
 rewrite insert_app_r_alt; last (rewrite length_take; lia).
 rewrite length_take Nat.min_l; last lia.
 rewrite Nat.sub_diag. simpl. rewrite <- app_assoc. reflexivity.
Qed.
Lemma free_cells_lookup base n m z :
 free_cells base n m !! RawId z =
 if decide (base <= z < base + Z.of_nat n) then None else m !! RawId z.
Proof.
 induction n as [|n IH].
 - simpl. case_decide; [lia|done].
 - cbn [free_cells]. rewrite Nat2Z.inj_succ.
   destruct (decide (z = base + Z.of_nat n)) as [->|Hne].
   + rewrite lookup_delete decide_True; [done|lia].
   + rewrite lookup_delete_ne; last (intros E; injection E; lia).
     rewrite IH. clear IH. case_decide; case_decide; try done; lia.
Qed.
Lemma wf_free_block σ base n :
 cjr_blocks σ !! RawId base = Some n -> state_wf σ ->
 state_wf (set_blocks (delete (RawId base) (cjr_blocks σ))
   (set_raw (free_cells base n (cjr_raw σ)) σ)).
Proof.
 intros Hlen [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
 - intros z Hz. apply elem_of_dom in Hz as [x Hx].
   rewrite free_cells_lookup in Hx. case_decide; first discriminate.
   apply Hr. apply elem_of_dom. eauto.
 - intros z Hz. rewrite dom_delete in Hz. apply Hb. set_solver.
 - intros z k Hk. destruct (decide (z=base)) as [->|Hne].
   + rewrite lookup_delete in Hk. discriminate.
   + rewrite lookup_delete_ne in Hk; last (intros E; injection E; lia).
     destruct (Hc z k Hk) as [Hlimit Hcells]. split; [done|].
     intros i Hi. destruct (Hcells i Hi) as [x Hx].
     rewrite free_cells_lookup. case_decide; last eauto.
     destruct (Hd base n z k Hlen Hk) as [Hdis|Hdis]; lia.
 - intros b1 n1 b2 n2 H1 H2 Hne.
   destruct (decide (b1=base)) as [->|Hne1]; first (rewrite lookup_delete in H1; discriminate).
   destruct (decide (b2=base)) as [->|Hne2]; first (rewrite lookup_delete in H2; discriminate).
   rewrite lookup_delete_ne in H1; last (intros E; injection E; lia).
   rewrite lookup_delete_ne in H2; last (intros E; injection E; lia).
   eapply Hd; eauto.
Qed.
Definition byte_test (x : Z) : bool := bool_decide (0 <= x) && bool_decide (x <= 255).
Definition bytes_test (xs : list Z) : bool := forallb byte_test xs.
Lemma bytes_test_step xs i x : xs !! i = Some x ->
 bytes_test (take (S i) xs) = (bytes_test (take i xs) && byte_test x)%bool.
Proof.
 intros Hx. rewrite (take_S_r xs i x Hx). unfold bytes_test.
 rewrite forallb_app. simpl. rewrite Bool.andb_true_r. done.
Qed.
Lemma bytes_test_spec xs : bytes_test xs = true <-> Forall model.byte xs.
Proof.
 unfold bytes_test. rewrite forallb_forall List.Forall_forall.
 split; intros Htest x Hin; specialize (Htest x Hin).
 - unfold byte_test in Htest. apply Bool.andb_true_iff in Htest as [Hlo Hhi].
   apply bool_decide_eq_true in Hlo. apply bool_decide_eq_true in Hhi.
   unfold model.byte. lia.
 - unfold model.byte in Htest. unfold byte_test.
   apply Bool.andb_true_iff. split; apply bool_decide_eq_true; lia.
Qed.
Ltac memory_admin :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackLoad _ {{_}}) =>
    iApply (wp_stack_load with "Hl"); iIntros "!> _ Hl" end | hm_head]) end);
 simpl; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma cells_app p xs ys :
 array.array_cells p (xs ++ ys) ⊣⊢
 array.array_cells p xs ∗ array.array_cells (p + Z.of_nat (length xs)) ys.
Proof.
 unfold array.array_cells. rewrite big_sepL_app.
 f_equiv. apply big_sepL_proper. intros i x Hi.
 rewrite Nat2Z.inj_add. replace (p + (length xs + i)) with (p + length xs + i) by lia.
 done.
Qed.
Lemma cells_slice_acc p xs offset count :
 (offset + count <= length xs)%nat ->
 array.array_cells p xs -∗
 array.array_cells (p + Z.of_nat offset) (take count (drop offset xs)) ∗
 (∀ replacement : list Z, ⌜length replacement = count⌝ -∗
   array.array_cells (p + Z.of_nat offset) replacement -∗
   array.array_cells p
     (take offset xs ++ replacement ++ drop (offset + count) xs)).
Proof.
 intros Hbounds. iIntros "Hcells".
 rewrite <- (take_drop offset xs) at 1.
 rewrite cells_app length_take Nat.min_l; last lia.
 rewrite <- (take_drop count (drop offset xs)) at 1.
 rewrite cells_app length_take length_drop Nat.min_l; last lia.
 rewrite drop_drop.
 iDestruct "Hcells" as "[Hprefix [Hslice Hsuffix]]".
 iFrame "Hslice". iIntros (replacement) "%Hlength Hreplacement".
 rewrite cells_app length_take Nat.min_l; last lia.
 iFrame "Hprefix". rewrite cells_app Hlength. iFrame "Hreplacement".
 replace (offset + count)%nat with (count + offset)%nat by lia.
 iExact "Hsuffix".
Qed.
Lemma free_cells_update base (xs : list Z) m :
 ghost_map_auth cjr_raw_name 1 m -∗ array.array_cells base xs -∗
 |==> ghost_map_auth cjr_raw_name 1 (free_cells base (length xs) m).
Proof.
 revert m. induction xs as [|x xs IH] using rev_ind; intros m.
 - simpl. iIntros "$ _". done.
 - iIntros "Hr Hcells". unfold array.array_cells.
   rewrite big_sepL_app big_sepL_singleton Nat.add_0_r.
   iDestruct "Hcells" as "[Hpre Hlast]".
   iMod (IH with "Hr Hpre") as "Hr".
   iMod (ghost_map_delete with "Hr Hlast") as "Hr".
   rewrite length_app. simpl. rewrite Nat.add_1_r. simpl. done.
Qed.
Theorem buffer_alloc_wp n : (0 < n)%nat ->
 ⊢ WP Alloc (int (Z.of_nat n))
 {{u, ∃ p, ⌜u = LitV (LitPtr p)⌝ ∗ RawId p ↦ᵦ n ∗
     array.array_cells p (replicate n 0%Z)}}.
Proof.
 intros Hn. unfold int. iApply wp_alloc; [lia|].
 iIntros (p) "Hcells Hblock". iExists p.
 iEval (rewrite Nat2Z.id) in "Hcells Hblock".
 iFrame "Hblock". iSplit; [done|].
 iApply (array.seq_zero_cells with "Hcells").
Qed.
Theorem buffer_free_wp p xs :
 array.array_cells p xs -∗ RawId p ↦ᵦ length xs -∗
 WP Free (pv p) {{u, ⌜u = LitV LitUnit⌝}}.
Proof.
 iIntros "Hcells Hblock". unfold pv.
 iApply wp_lift_atomic_base_step_no_fork; [done|].
 iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
 iDestruct (ghost_map_lookup with "Hb Hblock") as %Hlen.
 iModIntro. iSplit.
 { iPureIntro. eexists [], (Val (LitV LitUnit)), _, [].
   eapply (FreeS p (length xs)). exact Hlen. }
 iIntros "!>" (e2 σ2 efs Hstep) "_".
 assert (Hgood : base_step (Free (Val (LitV (LitPtr p)))) σ []
   (Val (LitV LitUnit))
   (set_blocks (delete (RawId p) (cjr_blocks σ))
     (set_raw (free_cells p (length xs) (cjr_raw σ)) σ)) []).
 { eapply (FreeS p (length xs)). exact Hlen. }
 destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
 iMod (free_cells_update with "Hr Hcells") as "Hr".
 iMod (ghost_map_delete with "Hb Hblock") as "Hb".
 iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
 { iFrame. iPureIntro. eapply wf_free_block; eauto. }
 done.
Qed.
Theorem loop_wp name start stop body (I : Z -> iProp Σ) :
 (forall l i, 0 <= i < stop ->
   StackId l ↦ₛ LitV (LitInt i) -∗ I i -∗
   WP subst_var name l body
   {{u, StackId l ↦ₛ LitV (LitInt i) ∗ I (i+1)}}) ->
 0 <= start <= stop ->
 I start -∗ WP loop name (int start) (int stop) body
 {{u, ⌜u = LitV LitUnit⌝ ∗ I stop}}.
Proof.
 intros Hstep Hrange. iIntros "HI". unfold loop, int.
 iApply wp_var_bind. iIntros (l) "Hl".
 cbn [subst_var subst_var_val le sub v add int op].
 rewrite bool_decide_true; last done.
 iLöb as "IH" forall (start Hrange).
 iApply wp_while.
 iApply (wp_bind [IfCtx
   (Seq (Seq (subst_var name l body) (counter_increment l))
     (While (BinOp LeOp (StackLoad (Val (LitV (LitStack l))))
       (BinOp MinusOp (Val (LitV (LitInt stop))) (Val (LitV (LitInt 1)))))
       (Seq (subst_var name l body) (counter_increment l)))) unit_e]).
 iApply (wp_bind [BinOpLCtx LeOp
   (BinOp MinusOp (Val (LitV (LitInt stop))) (Val (LitV (LitInt 1))))]).
 iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
 iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt start))]).
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 destruct (decide (start <= stop-1)) as [Hlt|Hend].
 - rewrite bool_decide_true; last done. iApply wp_if_true.
   iApply (wp_bind [SeqCtx (While
     (BinOp LeOp (StackLoad (Val (LitV (LitStack l))))
       (BinOp MinusOp (Val (LitV (LitInt stop))) (Val (LitV (LitInt 1)))))
     (Seq (subst_var name l body) (counter_increment l)))]).
   iApply (wp_bind [SeqCtx (counter_increment l)]).
   iApply (wp_wand with "[Hl HI]").
   { iApply (Hstep l start with "Hl HI"). lia. }
   iIntros (u) "[Hl HI]". iApply wp_seq.
   unfold counter_increment. iApply (wp_bind [StackAssignRCtx (LitV (LitStack l))]).
   iApply (wp_bind [BinOpLCtx PlusOp (int 1)]).
   iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
   iApply wp_binop; [reflexivity|]. iIntros "!> _".
   iApply (wp_stack_assign with "Hl"). iIntros "!> _ Hl".
   iApply wp_seq. iApply ("IH" $! (start+1) with "[] HI Hl"). iPureIntro. lia.
 - rewrite bool_decide_false; last done. iApply wp_if_false.
   assert (start=stop) by lia. subst start. iApply wp_value'.
   iExists (LitV (LitInt stop)). iFrame. done.
Qed.
Theorem copy_wp p q src dst n :
 (n <= length src)%nat -> (n <= length dst)%nat ->
 array.array_cells p src -∗ array.array_cells q dst -∗
 WP call copy_body [pv p; pv q; int (Z.of_nat n)]
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p src ∗
       array.array_cells q (take n src ++ drop n dst)}}.
Proof.
 intros Hsrc Hdst. iIntros "Hs Hd".
 unfold call, copy_body, args. hm_pure.
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
Theorem zero_wp p dst n : (n <= length dst)%nat ->
 array.array_cells p dst -∗
 WP call zero_body [pv p; int (Z.of_nat n)]
 {{u, ⌜u = LitV LitUnit⌝ ∗
       array.array_cells p (replicate n 0%Z ++ drop n dst)}}.
Proof.
 intros Hdst. iIntros "Hd". unfold call, zero_body, args. hm_pure.
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
Theorem bytes_wp p xs n : (n <= length xs)%nat ->
 array.array_cells p xs -∗
 WP call byte_body [pv p; int (Z.of_nat n)]
 {{u, ⌜u = LitV (LitBool (bytes_test (take n xs)))⌝ ∗ array.array_cells p xs}}.
Proof.
 intros Hn. iIntros "Hs". unfold call, byte_body, args. hm_pure.
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
Theorem session_new_wp :
 ⊢ WP new_body {{u, ∃ p, ⌜u = LitV (LitPtr p)⌝ ∗ RawId p ↦ᵦ 6242%nat ∗
     array.array_cells p (1 :: replicate 6241 0%Z)}}.
Proof.
 unfold new_body, lets.
 iApply (wp_bind [LetCtx (Some "session")
   (Seq (put (v "session") (int 0) (int 1)) (v "session"))]).
 iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 6242). vm_compute. lia. }
 iIntros (u) "H". iDestruct "H" as (p) "[%Hu [Hb Hcells]]". subst u.
 iApply wp_let. cbn [subst subst_val put v ptr int].
 iApply (wp_bind [SeqCtx (pv p)]).
 iApply (wp_wand with "[Hcells]").
 { iApply (buffer_put_wp p (replicate 6242 0%Z) 0 0 1 with "Hcells"). reflexivity. }
 iIntros (u) "[%Hu Hcells]". subst u. iApply wp_seq. iApply wp_value'.
 iExists p. iFrame "Hb". iSplit; [done|]. iExact "Hcells".
Qed.
Theorem session_destroy_wp p xs : length xs = 6242%nat ->
 array.array_cells p xs -∗ RawId p ↦ᵦ 6242%nat -∗
 WP call destroy_body [pv p] {{u, ⌜u = LitV LitUnit⌝}}.
Proof.
 intros Hlen. iIntros "Hcells Hb". unfold call, destroy_body, args.
 (* Keep the helper closed while reducing the outer function's arguments. *)
 unfold zero. hm_args.
 iApply wp_app. hm_admin.
 iApply (wp_bind [SeqCtx (Free (pv p))]).
 iApply (wp_wand with "[Hcells]").
 { iApply (zero_wp p xs 6242 with "Hcells"). lia. }
 iIntros (u) "[%Hu Hcells]". subst u. iApply wp_seq.
 iEval (rewrite <- Hlen; rewrite drop_all; rewrite app_nil_r) in "Hcells".
 iApply (buffer_free_wp with "Hcells [Hb]").
 rewrite length_replicate Hlen. iExact "Hb".
Qed.
End proofs.
