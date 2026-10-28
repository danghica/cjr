(** Owned-buffer refinements of SHA-1 schedule construction. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory encoding.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition word4_at (words : list Z) offset := model.be_word (take 4 (drop offset words)).
Definition schedule_seed words base := map (fun i => word4_at words (base+4*i)%nat) (seq 0 16).
Lemma take4_at (words : list Z) offset : (offset+4 <= length words)%nat ->
 take 4 (drop offset words) =
 [words !!! offset; words !!! (S offset); words !!! (S (S offset)); words !!! (S (S (S offset)))].
Proof.
 intros Hlen.
 rewrite (drop_S words (words !!! offset) offset); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S words (words !!! S offset) (S offset)); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S words (words !!! S (S offset)) (S (S offset))); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S words (words !!! S (S (S offset))) (S (S (S offset)))); last (apply list_lookup_lookup_total_lt; lia).
 reflexivity.
Qed.
Lemma word4_at_value words offset : (offset+4 <= length words)%nat ->
 word4_at words offset =
 (((0 * 256 + words !!! offset) * 256 + words !!! (S offset)) * 256 +
   words !!! (S (S offset))) * 256 + words !!! (S (S (S offset))).
Proof.
 intros Hlen. unfold word4_at, model.be_word. rewrite (take4_at words offset Hlen).
 reflexivity.
Qed.
Lemma schedule_seed_length words base : length (schedule_seed words base) = 16%nat.
Proof. unfold schedule_seed. rewrite length_map length_seq. done. Qed.
Lemma schedule_seed_lookup words base i : (i < 16)%nat ->
 schedule_seed words base !! i = Some (word4_at words (base+4*i)%nat).
Proof.
 intros Hi. unfold schedule_seed.
 change (((fun j => word4_at words (base+4*j)%nat) <$> seq 0 16) !! i = Some (word4_at words (base+4*i)%nat)).
 rewrite list_lookup_fmap (lookup_seq_lt 0 16 i Hi). reflexivity.
Qed.
Lemma schedule_seed_model words base :
 schedule_seed words base = model.message_words (take 64 (drop base words)).
Proof.
 unfold schedule_seed, model.message_words, word4_at.
 apply map_ext_in. intros i Hi. apply in_seq in Hi.
 rewrite (take_drop_commute (take 64 (drop base words)) 4 (4*i)%nat).
 rewrite take_take. rewrite Nat.min_l; last lia.
 rewrite <- take_drop_commute.
 rewrite drop_drop. replace (4*i+base)%nat with (base+4*i)%nat by lia. done.
Qed.
Definition load_schedule_operand pad w base_expr :=
 loop "loadT" (int 0) (int 16)
   (put (pv w) (v "loadT")
     (fold_left (fun acc j => add (mul acc (int 256))
       (get (pv pad) (add base_expr
         (add (mul (v "loadT") (int 4)) (int j))))) [0;1;2;3] (int 0))).
Definition load_schedule pad w base :=
 load_schedule_operand pad w (int (Z.of_nat base)).
Ltac schedule_admin :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackLoad _ {{_}}) =>
    first [iApply (wp_stack_load with "Hblock"); iIntros "!> _ Hblock"
          |iApply (wp_stack_load with "Hl"); iIntros "!> _ Hl"] end | hm_head]) end);
 simpl; cbn [fill fill_item].

Definition schedule_next (ws : list Z) :=
 let i := length ws in model.rol32
   (Z.lxor (nth (i-3) ws 0) (Z.lxor (nth (i-8) ws 0)
     (Z.lxor (nth (i-14) ws 0) (nth (i-16) ws 0)))) 1.
Lemma schedule_next_value ws :
 schedule_next ws = model.rol32
   (Z.lxor (nth (length ws-3) ws 0) (Z.lxor (nth (length ws-8) ws 0)
     (Z.lxor (nth (length ws-14) ws 0) (nth (length ws-16) ws 0)))) 1.
Proof. reflexivity. Qed.
Lemma schedule_more_left n ws :
 model.schedule_more (S n) ws = model.schedule_more n (ws ++ [schedule_next ws]).
Proof. reflexivity. Qed.
Lemma schedule_more_zero ws : model.schedule_more 0 ws = ws.
Proof. reflexivity. Qed.
Lemma schedule_more_length n ws : length (model.schedule_more n ws) = (length ws+n)%nat.
Proof.
 revert ws. induction n as [|n IH]; intros ws.
 - rewrite schedule_more_zero Nat.add_0_r. done.
 - rewrite schedule_more_left IH length_app. simpl. lia.
Qed.
Lemma schedule_more_right n ws :
 model.schedule_more (S n) ws = model.schedule_more n ws ++ [schedule_next (model.schedule_more n ws)].
Proof.
 revert ws. induction n as [|n IH]; intros ws.
 - reflexivity.
 - rewrite (schedule_more_left (S n) ws) (IH (ws ++ [schedule_next ws])).
   rewrite (schedule_more_left n ws). done.
Qed.
Lemma expand_write_step (prefix tail : list Z) k x : (k < length tail)%nat ->
 <[length prefix := x]> (prefix ++ drop k tail) = (prefix ++ [x]) ++ drop (S k) tail.
Proof.
 intros Hlen. destruct (lookup_lt_is_Some_2 tail k Hlen) as [old Hold].
 rewrite (drop_S tail old k Hold) insert_app_r_alt; last lia.
 rewrite Nat.sub_diag. simpl. rewrite <- app_assoc. done.
Qed.
Definition expand_schedule w :=
 loop "expandT" (int 16) (int 80)
   (put (pv w) (v "expandT") (rol
     (xor (get (pv w) (sub (v "expandT") (int 3)))
       (xor (get (pv w) (sub (v "expandT") (int 8)))
         (xor (get (pv w) (sub (v "expandT") (int 14)))
           (get (pv w) (sub (v "expandT") (int 16)))))) 1)).
Lemma load_schedule_is_source p q base :
 subst "pad" (LitV (LitPtr p))
   (subst "w" (LitV (LitPtr q))
     (subst "block" (LitV (LitInt (Z.of_nat base)))
       (match program.sha_compress with Seq first _ => first | _ => unit_e end))) =
 load_schedule p q base.
Proof. reflexivity. Qed.
Lemma expand_schedule_is_source q :
 subst "w" (LitV (LitPtr q))
   (match program.sha_compress with Seq _ (Seq second _) => second | _ => unit_e end) =
 expand_schedule q.
Proof. reflexivity. Qed.
Lemma load_schedule_stack_is_source p q block :
 subst "pad" (LitV (LitPtr p))
   (subst "w" (LitV (LitPtr q))
     (subst_var "block" block
       (match program.sha_compress with Seq first _ => first | _ => unit_e end))) =
 load_schedule_operand p q (StackLoad (Val (LitV (LitStack block)))).
Proof. reflexivity. Qed.
Lemma schedule_prefix_is_source p q block :
 let bind e := subst "pad" (LitV (LitPtr p))
   (subst "w" (LitV (LitPtr q)) (subst_var "block" block e)) in
 bind program.sha_compress =
 seqs [load_schedule_operand p q (StackLoad (Val (LitV (LitStack block)))); expand_schedule q]
   (bind (match program.sha_compress with Seq _ (Seq _ rest) => rest | _ => unit_e end)).
Proof. reflexivity. Qed.
Opaque schedule_seed word4_at model.schedule_more schedule_next.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem load_schedule_wp p pad q old base :
 (base+64 <= length pad)%nat -> (16 <= length old)%nat ->
 array.array_cells p pad -∗ array.array_cells q old -∗
 WP load_schedule p q base
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p pad ∗
   array.array_cells q (schedule_seed pad base ++ drop 16 old)}}.
Proof.
 intros Hpadlen Holdlen. iIntros "Hpad Hw". unfold load_schedule.
 set (I := fun i : Z => (array.array_cells p pad ∗
   array.array_cells q (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old))%I).
 iApply (wp_wand with "[Hpad Hw]").
 { iApply (loop_wp "loadT" 0 16 _ I with "[Hpad Hw]").
   - intros l i Hi. iIntros "Hl [Hpad Hw]".
     cbn [subst_var subst_var_val].
     unfold put, get, ptr, pv, add, mul, int, op, v.
     cbn [subst_var subst_var_val fold_left].
     rewrite (bool_decide_eq_true_2 ("loadT" = "loadT") eq_refl).
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     let load_byte j :=
       let index := constr:((base + 4 * Z.to_nat i + j)%nat) in
       let Hlookup := fresh "Hlookup" in
       assert (Hlookup : pad !! index = Some (pad !!! index)) by
         (apply list_lookup_lookup_total_lt; lia);
       iDestruct (big_sepL_lookup_acc with "Hpad") as "[Hcell Hclose]"; [exact Hlookup|];
       let Haddr := fresh "Haddr" in
       assert (Haddr : p + Z.of_nat index = p + (Z.of_nat base + (i*4 + Z.of_nat j))) by
         lia;
       rewrite Haddr; iApply (wp_load with "Hcell"); iIntros "!> _ Hcell";
       iDestruct ("Hclose" with "Hcell") as "Hpad"; memory_admin
     in load_byte 0%nat; load_byte 1%nat; load_byte 2%nat; load_byte 3%nat.
     match goal with |- envs_entails _ (WP Store _ (Val (LitV (LitInt ?value))) {{_}}) =>
       assert (Hword : value = word4_at pad (base+4*Z.to_nat i)%nat) by
         (rewrite word4_at_value; [repeat first [reflexivity | lia | progress f_equal]|lia]);
       rewrite Hword end.
     assert (Hout : (Z.to_nat i < length
       (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old))%nat).
     { rewrite length_app length_take schedule_seed_length length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hout) as [oldword Hold].
     iDestruct (big_sepL_insert_acc with "Hw") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (word4_at pad (base+4*Z.to_nat i)%nat) with "Hcell") as "Hw".
     assert (Hwrite : <[Z.to_nat i := word4_at pad (base+4*Z.to_nat i)%nat]>
       (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old) =
       take (S (Z.to_nat i)) (schedule_seed pad base) ++ drop (S (Z.to_nat i)) old).
     { apply prefix_write_step; [apply schedule_seed_lookup|]; lia. }
     iAssert (array.array_cells q
       (take (S (Z.to_nat i)) (schedule_seed pad base) ++ drop (S (Z.to_nat i)) old))
       with "[Hw]" as "Hw".
     { rewrite <- Hwrite. iExact "Hw". }
     iFrame "Hl Hpad". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r. iExact "Hw".
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hpad Hw]]". unfold I.
 rewrite (take_ge (schedule_seed pad base) 16); last (rewrite schedule_seed_length;lia).
 iFrame. done.
Qed.
Theorem load_schedule_stack_wp p pad q old base block :
 (base+64 <= length pad)%nat -> (16 <= length old)%nat ->
 StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) -∗
 array.array_cells p pad -∗ array.array_cells q old -∗
 WP load_schedule_operand p q (StackLoad (Val (LitV (LitStack block))))
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) ∗
   array.array_cells p pad ∗
   array.array_cells q (schedule_seed pad base ++ drop 16 old)}}.
Proof.
 intros Hpadlen Holdlen. iIntros "Hblock Hpad Hw". unfold load_schedule_operand.
 set (I := fun i : Z => (StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) ∗
   array.array_cells p pad ∗
   array.array_cells q (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old))%I).
 iApply (wp_wand with "[Hblock Hpad Hw]").
 { iApply (loop_wp "loadT" 0 16 _ I with "[Hblock Hpad Hw]").
   - intros l i Hi. iIntros "Hl [Hblock [Hpad Hw]]".
     cbn [subst_var subst_var_val].
     unfold put, get, ptr, pv, add, mul, int, op, v.
     cbn [subst_var subst_var_val fold_left].
     rewrite (bool_decide_eq_true_2 ("loadT" = "loadT") eq_refl).
     schedule_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     let load_byte j :=
       let index := constr:((base + 4 * Z.to_nat i + j)%nat) in
       let Hlookup := fresh "Hlookup" in
       assert (Hlookup : pad !! index = Some (pad !!! index)) by
         (apply list_lookup_lookup_total_lt; lia);
       iDestruct (big_sepL_lookup_acc with "Hpad") as "[Hcell Hclose]"; [exact Hlookup|];
       let Haddr := fresh "Haddr" in
       assert (Haddr : p + Z.of_nat index = p + (Z.of_nat base + (i*4 + Z.of_nat j))) by
         lia;
       rewrite Haddr; iApply (wp_load with "Hcell"); iIntros "!> _ Hcell";
       iDestruct ("Hclose" with "Hcell") as "Hpad"; schedule_admin
     in load_byte 0%nat; load_byte 1%nat; load_byte 2%nat; load_byte 3%nat.
     match goal with |- envs_entails _ (WP Store _ (Val (LitV (LitInt ?value))) {{_}}) =>
       assert (Hword : value = word4_at pad (base+4*Z.to_nat i)%nat) by
         (rewrite word4_at_value; [repeat first [reflexivity | lia | progress f_equal]|lia]);
       rewrite Hword end.
     assert (Hout : (Z.to_nat i < length
       (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old))%nat).
     { rewrite length_app length_take schedule_seed_length length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hout) as [oldword Hold].
     iDestruct (big_sepL_insert_acc with "Hw") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (word4_at pad (base+4*Z.to_nat i)%nat) with "Hcell") as "Hw".
     assert (Hwrite : <[Z.to_nat i := word4_at pad (base+4*Z.to_nat i)%nat]>
       (take (Z.to_nat i) (schedule_seed pad base) ++ drop (Z.to_nat i) old) =
       take (S (Z.to_nat i)) (schedule_seed pad base) ++ drop (S (Z.to_nat i)) old).
     { apply prefix_write_step; [apply schedule_seed_lookup|]; lia. }
     iAssert (array.array_cells q
       (take (S (Z.to_nat i)) (schedule_seed pad base) ++ drop (S (Z.to_nat i)) old))
       with "[Hw]" as "Hw".
     { rewrite <- Hwrite. iExact "Hw". }
     iFrame "Hl Hblock Hpad". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r. iExact "Hw".
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hblock [Hpad Hw]]]". unfold I.
 rewrite (take_ge (schedule_seed pad base) 16); last (rewrite schedule_seed_length;lia).
 iFrame. done.
Qed.
Theorem expand_schedule_wp q seed tail :
 length seed = 16%nat -> (64 <= length tail)%nat ->
 array.array_cells q (seed ++ tail) -∗
 WP expand_schedule q
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells q (model.schedule_more 64 seed ++ drop 64 tail)}}.
Proof.
 intros Hseed Htail. iIntros "Hw". unfold expand_schedule.
 set (I := fun i : Z => (⌜16 <= i <= 80⌝ ∗ array.array_cells q
   (model.schedule_more (Z.to_nat i-16) seed ++ drop (Z.to_nat i-16) tail))%I).
 iApply (wp_wand with "[Hw]").
 { iApply (loop_wp "expandT" 16 80 _ I with "[Hw]").
   - intros l i Hi. iIntros "Hl [%Hrange Hw]".
     unfold put, get, ptr, pv, xor, sub, v, int, op.
     cbn [subst_var subst_var_val]. rewrite (bool_decide_eq_true_2 ("expandT" = "expandT") eq_refl).
     memory_admin.
     set (k := (Z.to_nat i-16)%nat).
     set (prefix := model.schedule_more k seed). fold prefix.
     assert (Hplen : length prefix = Z.to_nat i).
     { unfold prefix. rewrite schedule_more_length Hseed. unfold k. lia. }
     assert (Hki : Z.of_nat (length prefix) = i) by lia.
     let read_schedule d :=
       let index := constr:((length prefix-d)%nat) in
       let Hlookup := fresh "Hlookup" in
       assert (Hlookup : (prefix ++ drop k tail) !! index = Some (nth index prefix 0)) by
         (rewrite lookup_app_l; [|lia];
          rewrite (nth_lookup_Some prefix index 0 (prefix !!! index)
            (list_lookup_lookup_total_lt prefix index ltac:(lia)));
          apply list_lookup_lookup_total_lt; lia);
       iDestruct (big_sepL_lookup_acc with "Hw") as "[Hcell Hclose]"; [exact Hlookup|];
       let Haddr := fresh "Haddr" in
       assert (Haddr : q + Z.of_nat index = q + (i-Z.of_nat d)) by lia;
       rewrite Haddr; iApply (wp_load with "Hcell"); iIntros "!> _ Hcell";
       iDestruct ("Hclose" with "Hcell") as "Hw"; memory_admin
     in do 2 (read_schedule 3%nat; read_schedule 8%nat; read_schedule 14%nat; read_schedule 16%nat).
     auth_pure.
     match goal with |- envs_entails _ (WP Store _ (Val (LitV (LitInt ?value))) {{_}}) =>
       assert (Hnext : value = schedule_next prefix) by
         (rewrite schedule_next_value; unfold model.rol32, model.mask32; reflexivity);
       rewrite Hnext end.
     assert (Hklen : (k < length tail)%nat) by (unfold k;lia).
     assert (Hout : (length prefix < length (prefix ++ drop k tail))%nat).
     { rewrite length_app length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hout) as [oldword Hold].
     iDestruct (big_sepL_insert_acc with "Hw") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (schedule_next prefix) with "Hcell") as "Hw".
     iAssert (array.array_cells q ((prefix ++ [schedule_next prefix]) ++ drop (S k) tail))
       with "[Hw]" as "Hw".
     { rewrite <- (expand_write_step prefix tail k _ Hklen). iExact "Hw". }
     unfold I. rewrite Z2Nat.inj_add; [|lia|lia]. simpl.
     assert (Hstep : (Z.to_nat i+1-16)%nat = S k) by (unfold k;lia).
     rewrite Hstep schedule_more_right. fold prefix.
     iFrame "Hl Hw". iPureIntro. lia.
   - lia.
   - unfold I. rewrite schedule_more_zero. simpl. iFrame. iPureIntro. lia.
 }
 iIntros (u) "[%Hu [_ Hw]]". iFrame. done.
Qed.
Theorem schedule_prefix_wp p pad q old base block rest (Φ : val_cjr -> iProp Σ) :
 (base+64 <= length pad)%nat -> (80 <= length old)%nat ->
 StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) -∗
 array.array_cells p pad -∗ array.array_cells q old -∗
 (StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) -∗ array.array_cells p pad -∗
   array.array_cells q
     (model.schedule_more 64 (model.message_words (take 64 (drop base pad))) ++ drop 80 old) -∗
   WP rest {{Φ}}) -∗
 WP seqs [load_schedule_operand p q (StackLoad (Val (LitV (LitStack block)))); expand_schedule q]
   rest {{Φ}}.
Proof.
 intros Hpad Hsize. iIntros "Hblock Hpad Hw Hrest". cbn [seqs fold_right].
 iApply (wp_bind [SeqCtx (Seq (expand_schedule q) rest)]).
 iApply (wp_wand with "[Hblock Hpad Hw]").
 { iApply (load_schedule_stack_wp p pad q old base block with "Hblock Hpad Hw"); lia. }
 iIntros (u) "[%Hu [Hblock [Hpad Hw]]]". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx rest]). iApply (wp_wand with "[Hw]").
 { iApply (expand_schedule_wp q (schedule_seed pad base) (drop 16 old) with "Hw").
   - apply schedule_seed_length.
   - rewrite length_drop. lia. }
 iIntros (u) "[%Hu Hw]". subst u. iApply wp_seq.
 iApply ("Hrest" with "Hblock Hpad [Hw]").
 rewrite <- schedule_seed_model. iEval (rewrite drop_drop) in "Hw". iExact "Hw".
Qed.
End proofs.
