(** Whole enrollment routine: validate, canonically decode, commit, scrub/free. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory memory_application input_memory
 sessions account_slots account_enroll account_enroll_guard account_validation base32 base32_contracts base32_input.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition enrollment_numbers (label issuer chars : list Z) digits period :=
 valid_parameters digits period /\ (1 <= length label <=128)%nat /\
 (length issuer<=128)%nat /\ (2<=length chars<=208)%nat.
Definition enrollment_result words label issuer chars digits period :=
 if bool_decide (enrollment_numbers label issuer chars digits period) then
 if bytes_test label && bytes_test issuer then
 match base32.decode chars with
 | None => -1
 | Some secret => enroll_decoded_result words (Z.of_nat (length secret))
 end else -1 else -1.
Definition enrollment_words words label issuer chars digits period :=
 if bool_decide (enrollment_numbers label issuer chars digits period) then
 if bytes_test label && bytes_test issuer then
 match base32.decode chars with
 | None => words
 | Some secret => enroll_decoded_words words label issuer secret (Z.of_nat (length secret)) digits period
 end else words else words.
Definition checked_parameters digits period :=
 both (If (eq (int digits) (int 6)) yes (eq (int digits) (int 8))) (range (int period) 1 2147483647).
Transparent base32_body base32_value_body copy_body.
Lemma base32_body_enroll_closed name x : enroll_bound_name name -> subst name x base32_body = base32_body.
Proof. intros H; unfold enroll_bound_name in H; repeat destruct H as [->|H]; try subst name; reflexivity. Qed.
Transparent zero_body.
Lemma zero_body_result_closed x : subst "result" x zero_body = zero_body.
Proof. reflexivity. Qed.
Opaque byte_body copy_body zero_body base32_body.
#[local] Hint Rewrite copy_body_enroll_closed zero_body_enroll_closed byte_body_enroll_closed
 base32_body_enroll_closed using (unfold enroll_bound_name; tauto) : enroll_subst.
#[local] Hint Rewrite zero_body_result_closed : enroll_subst.
Ltac enroll_to_guard :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with enroll_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 lazymatch e with If _ _ _ => fail | _ => hm_focus e ltac:(fun _ => hm_admin_head) end end);
 simpl; cbn [fill fill_item]; autorewrite with enroll_subst.
Definition enrollment_cleanup p result :=
 seqs [zero (pv p) (int 128);Free (pv p)] (int result).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma checked_parameters_wp digits period : valid_parameters digits period ->
 ⊢ WP checked_parameters digits period {{u, ⌜u = LitV (LitBool true)⌝}}.
Proof.
 intros [[Hd|Hd] [Hlo Hhi]]; subst digits; unfold checked_parameters,range,both,eq,le,int,op,yes; auth_pure; done.
Qed.
Lemma enrollment_cleanup_wp p decoded result : length decoded =128%nat ->
 array.array_cells p decoded -∗ RawId p ↦ᵦ128%nat -∗
 WP enrollment_cleanup p result {{u, ⌜u = LitV (LitInt result)⌝}}.
Proof.
 intros Hlen. iIntros "Hd Hb". unfold enrollment_cleanup,seqs,zero.
 iApply (wp_bind [SeqCtx (Seq (Free (pv p)) (int result))]).
 iApply (wp_wand with "[Hd]").
 { iApply (zero_wp p decoded 128 with "Hd"). lia. }
 iIntros (u) "[%Hu Hd]". subst u. iApply wp_seq.
 assert (Hdrop : drop 128 decoded = []) by (apply drop_ge; lia).
 iEval (rewrite Hdrop app_nil_r) in "Hd".
 iApply (wp_bind [SeqCtx (int result)]).
 iApply (wp_wand with "[Hd Hb]").
 { iApply (buffer_free_wp p (replicate 128 0%Z) with "Hd Hb"); rewrite length_replicate; lia. }
 iIntros (u) "%Hu". subst u. iApply wp_seq. iApply wp_value'. done.
Qed.
Theorem session_enroll_valid_numbers_wp heap p words lp label ip issuer sp chars digits period :
 length words =6242%nat -> enrollment_numbers label issuer chars digits period -> available_slot words ->
 buffer_in heap lp label -> buffer_in heap ip issuer -> buffer_in heap sp chars ->
 input_cells heap -∗ array.array_cells p words -∗
 WP call add_body [pv p;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer));
  pv sp;int (Z.of_nat (length chars));int digits;int period]
 {{u, ⌜u = LitV (LitInt (enrollment_result words label issuer chars digits period))⌝ ∗
 input_cells heap ∗ array.array_cells p (enrollment_words words label issuer chars digits period)}}.
Proof.
 intros Hlen Hnumbers Havailable Hlabelview Hissuerview Hsecretview.
 destruct Hnumbers as [Hparams [Hlabel [Hissuer Hchars]]].
 assert (Hnumbers : enrollment_numbers label issuer chars digits period) by (exact (conj Hparams (conj Hlabel (conj Hissuer Hchars)))).
 iIntros "Hheap Hs".
 unfold enrollment_result,enrollment_words. rewrite (bool_decide_true _ Hnumbers).
 unfold call at 1. unfold add_body,args. hm_args. iApply wp_app. enroll_to_guard.
 match goal with |- envs_entails _ (WP If (BinOp AndOp ?params ?rest) ?good ?bad {{_}}) =>
   iApply (wp_bind [BinOpLCtx AndOp rest;IfCtx good bad]) end.
 iApply (wp_wand with "[]").
 { iApply (checked_parameters_wp digits period Hparams). }
 iIntros (u) "%Hu". subst u. enroll_args.
 repeat (rewrite bool_decide_true; [|lia]).
 iApply wp_if_true. enroll_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap lp label Hlabelview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u. enroll_args.
 iApply (wp_wand with "[Hheap]").
 { iApply (bytes_view_reduced_wp heap ip issuer Hissuerview with "Hheap"). }
 iIntros (u) "[%Hu Hheap]". subst u. enroll_args.
 destruct (bytes_test label && bytes_test issuer)%bool eqn:Hbytes.
 - iApply wp_if_true.
   match goal with |- envs_entails _ (WP Let ?x (Alloc ?n) ?body {{_}}) =>
     iApply (wp_bind [LetCtx x body]) end.
   iApply (wp_wand with "[]").
   { iApply (buffer_alloc_wp 128). lia. }
   iIntros (u) "Hall". iDestruct "Hall" as (dp) "[%Hu [Hb Hd]]". subst u.
   iApply wp_let. cbn [subst_binder subst subst_val]. autorewrite with enroll_subst. enroll_args.
   iApply (wp_wand with "[Hheap Hd]").
   { iApply (base32_view_application_wp heap sp chars dp (replicate 128 0%Z)
      Hsecretview with "Hheap Hd"). rewrite length_replicate. lia. }
   iIntros (u) "[Hheap Hdecode]".
   set (n := match base32.decode chars with Some secret => Z.of_nat (length secret) | None => -1 end).
   set (tmp := match base32.decode chars with Some secret => secret ++ drop (length secret) (replicate 128 0%Z)
     | None => replicate 128 0%Z end).
   iAssert (⌜u = LitV (LitInt n)⌝ ∗ array.array_cells dp tmp)%I with "[Hdecode]" as "[%Hu Hd]".
   { unfold n,tmp. destruct (base32.decode chars); iExact "Hdecode". }
   subst u.
   assert (Htmp : length tmp =128%nat).
   { unfold tmp. destruct (base32.decode chars) as [secret|] eqn:Hdecode.
     - pose proof (decode_length chars secret Hdecode). rewrite length_app length_drop length_replicate. lia.
     - apply length_replicate. }
   assert (Hn : 1<=n -> (Z.to_nat n<=128)%nat /\ (Z.to_nat n<=length tmp)%nat).
   { unfold n. destruct (base32.decode chars) as [secret|] eqn:Hdecode.
     - pose proof (decode_length chars secret Hdecode). rewrite Nat2Z.id Htmp. lia.
     - lia. }
   iApply wp_let. cbn [subst_binder subst subst_val]. autorewrite with enroll_subst.
   match goal with |- envs_entails _ (WP Let ?x ?body ?rest {{_}}) =>
     iApply (wp_bind [LetCtx x rest]) end.
   iApply (wp_wand with "[Hheap Hs Hd]").
   { iApply (enroll_decoded_wp heap p words lp label ip issuer dp tmp n digits period Hlen
      ltac:(lia) Hissuer Hn Hlabelview Hissuerview Havailable with "Hheap Hs Hd"). }
   iIntros (result) "[%Hresult [Hheap [Hd Hs]]]". subst result.
   iApply wp_let. cbn [subst_binder subst subst_val]. autorewrite with enroll_subst.
   iApply (wp_wand with "[Hd Hb]").
   { iApply (enrollment_cleanup_wp dp tmp (enroll_decoded_result words n) Htmp with "Hd Hb"). }
   iIntros (u) "%Hu".
   assert (Hresult : enroll_decoded_result words n =
     match base32.decode chars with None => -1 | Some secret => enroll_decoded_result words (Z.of_nat (length secret)) end).
   { unfold n. destruct (base32.decode chars); [reflexivity|]. unfold enroll_decoded_result. rewrite bool_decide_false; [reflexivity|lia]. }
   assert (Hwords : enroll_decoded_words words label issuer tmp n digits period =
     match base32.decode chars with None => words | Some secret =>
       enroll_decoded_words words label issuer secret (Z.of_nat (length secret)) digits period end).
   { unfold n,tmp. destruct (base32.decode chars) as [secret|] eqn:Hdecode.
     - unfold enroll_decoded_words. rewrite !Nat2Z.id take_app_length.
       rewrite (take_ge secret (length secret) ltac:(lia)). reflexivity.
     - unfold enroll_decoded_words. rewrite bool_decide_false; [reflexivity|lia]. }
   iEval (rewrite Hwords) in "Hs". iFrame. iPureIntro. rewrite Hu Hresult. reflexivity.
 - iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
Theorem session_enroll_wp heap p words lp label ip issuer sp chars digits period :
 length words =6242%nat -> available_slot words ->
 buffer_in heap lp label -> buffer_in heap ip issuer -> buffer_in heap sp chars ->
 input_cells heap -∗ array.array_cells p words -∗
 WP call add_body [pv p;pv lp;int (Z.of_nat (length label));pv ip;int (Z.of_nat (length issuer));
  pv sp;int (Z.of_nat (length chars));int digits;int period]
 {{u, ⌜u = LitV (LitInt (enrollment_result words label issuer chars digits period))⌝ ∗
 input_cells heap ∗ array.array_cells p (enrollment_words words label issuer chars digits period)}}.
Proof.
 intros Hlen Havailable Hlabelview Hissuerview Hsecretview. iIntros "Hheap Hs".
 destruct (decide (enrollment_numbers label issuer chars digits period)) as [Hnumbers|Hnumbers].
 - iApply (session_enroll_valid_numbers_wp with "Hheap Hs"); assumption.
 - unfold enrollment_result,enrollment_words. rewrite (bool_decide_false _ Hnumbers).
   iApply (enroll_parameters_rejected_wp p lp (Z.of_nat (length label)) ip
    (Z.of_nat (length issuer)) sp (Z.of_nat (length chars)) digits period
    (input_cells heap ∗ array.array_cells p words)%I with "[Hheap Hs]").
   + intros Hvalid. apply Hnumbers. unfold enrollment_numbers. destruct Hvalid as [Hp Hrest]. split; [exact Hp|lia].
   + iFrame.
Qed.
End proofs.
