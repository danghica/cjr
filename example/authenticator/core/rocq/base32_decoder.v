(** Atomic destination commit and whole-function canonical Base32 contract. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory memory_application base32_stream base32_refinement.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition commit_e valid padding symbols acc out scratch dst n :=
 Seq (If (validation_e valid padding symbols acc out n)
       (copy (pv scratch) (pv dst) (stack_get out))
       (StackAssign (stack_e valid) no))
 (lets [("result",If (stack_get valid) (stack_get out) (int (-1)))]
   (Seq (Free (pv scratch)) (v "result"))).
Lemma validation_output_bounds st n : validation_result st n = true ->
 scan_valid st = true /\ (1 <= length (emitted (scan_bits st)) <= 128)%nat.
Proof.
 unfold validation_result. intros H.
 assert (Hv : scan_valid st = true) by (repeat rewrite Bool.andb_true_iff in H; tauto).
 assert (Hlo : bool_decide (1 <= Z.of_nat (length (emitted (scan_bits st)))) = true)
   by (repeat rewrite Bool.andb_true_iff in H; tauto).
 assert (Hhi : bool_decide (Z.of_nat (length (emitted (scan_bits st))) <= 128) = true)
   by (repeat rewrite Bool.andb_true_iff in H; tauto).
 apply bool_decide_eq_true in Hlo,Hhi. split; [exact Hv|lia].
Qed.
Ltac b32_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [b32_load | hm_args_head]) end);
 simpl; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem commit_wp valid padding symbols acc bits out scratch dst n st tail dst_words :
 (length (emitted (scan_bits st)) + length tail = 130)%nat ->
 (128 <= length dst_words)%nat ->
 scan_cells valid padding symbols acc bits out st -∗
 array.array_cells scratch (emitted (scan_bits st) ++ tail) -∗ RawId scratch ↦ᵦ 130%nat -∗
 array.array_cells dst dst_words -∗
 WP commit_e valid padding symbols acc out scratch dst n
 {{u, scan_cells valid padding symbols acc bits out
   (Scan (validation_result st n) (scan_padding st) (scan_symbols st) (scan_bits st)) ∗
 if validation_result st n then
   ⌜u = LitV (LitInt (Z.of_nat (length (emitted (scan_bits st)))))⌝ ∗
   array.array_cells dst (emitted (scan_bits st) ++ drop (length (emitted (scan_bits st))) dst_words)
 else ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells dst dst_words}}.
Proof.
 intros Hscratchlen Hdstlen. iIntros "Hstate Hscratch Hblock Hdst".
 unfold commit_e.
 iApply (wp_bind [SeqCtx (lets [("result",If (stack_get valid) (stack_get out) (int (-1)))]
   (Seq (Free (pv scratch)) (v "result"))) ]).
 iApply (wp_bind [IfCtx (copy (pv scratch) (pv dst) (stack_get out)) (StackAssign (stack_e valid) no)]).
 iApply (wp_wand with "[Hstate]"). { iApply (validation_wp with "Hstate"). }
 iIntros (u) "[%Hu Hstate]". subst u.
 destruct (validation_result st n) eqn:Haccept.
 - iApply wp_if_true.
   destruct (validation_output_bounds st n Haccept) as [Hvalid Hout].
   iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
   unfold copy,call,pv,stack_get,stack_e. b32_args.
   iApply (wp_wand with "[Hscratch Hdst]").
   { iApply (copy_reduced_wp with "Hscratch Hdst"); rewrite ?length_app; lia. }
   iIntros (u) "[%Hu [Hscratch Hdst]]". subst u.
   iEval (rewrite take_app_length) in "Hdst".
   unfold lets,stack_get,stack_e,pv,v,int. simpl.
   b32_admin. rewrite Hvalid. b32_admin.
   iApply (wp_bind [SeqCtx (int (Z.of_nat (length (emitted (scan_bits st)))))]).
   iApply (wp_wand with "[Hscratch Hblock]").
   { iApply (buffer_free_wp with "Hscratch [Hblock]"). rewrite length_app Hscratchlen. iExact "Hblock". }
   iIntros (u) "%Hu". subst u. b32_admin. unfold scan_cells; simpl. iFrame. done.
 - iApply wp_if_false.
   iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
   unfold lets,stack_get,stack_e,pv,v,int,no. simpl. b32_admin.
   iApply (wp_bind [SeqCtx (int (-1))]).
   iApply (wp_wand with "[Hscratch Hblock]").
   { iApply (buffer_free_wp with "Hscratch [Hblock]"). rewrite length_app Hscratchlen. iExact "Hblock". }
   iIntros (u) "%Hu". subst u. b32_admin. unfold scan_cells; simpl. iFrame. done.
Qed.
Theorem base32_application_valid_size_wp src chars dst dst_words :
 (2 <= length chars <= 208)%nat -> (128 <= length dst_words)%nat ->
 array.array_cells src chars -∗ array.array_cells dst dst_words -∗
 WP App (Val (RecV None (Some "args") base32_body))
   (Val (StructV [LitV (LitPtr src); LitV (LitInt (Z.of_nat (length chars))); LitV (LitPtr dst)]))
 {{u, array.array_cells src chars ∗
   match base32.decode chars with
   | None => ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells dst dst_words
   | Some decoded => ⌜u = LitV (LitInt (Z.of_nat (length decoded)))⌝ ∗
     array.array_cells dst (decoded ++ drop (length decoded) dst_words)
   end}}.
Proof.
 intros Hlen Hdstlen. iIntros "Hsrc Hdst".
 iApply wp_app. unfold base32_body,args. hm_admin.
 unfold range,both,le,int,op. auth_pure.
 rewrite (bool_decide_true (2 <= Z.of_nat (length chars)) ltac:(lia))
   (bool_decide_true (Z.of_nat (length chars) <= 208) ltac:(lia)). simpl.
 iApply wp_if_true. hm_take.
 iApply (wp_wand with "[]"). { iApply (buffer_alloc_wp 130). lia. }
 iIntros (u) "H". iDestruct "H" as (scratch) "[%Hu [Hblock Hscratch]]". subst u.
 iApply wp_let. cbn [subst subst_val].
 iApply wp_var_bind. iIntros (valid) "Hv". cbn [subst_var subst_var_val].
 iApply wp_var_bind. iIntros (padding) "Hp". cbn [subst_var subst_var_val].
 iApply wp_var_bind. iIntros (symbols) "Hs". cbn [subst_var subst_var_val].
 iApply wp_var_bind. iIntros (acc) "Ha". cbn [subst_var subst_var_val].
 iApply wp_var_bind. iIntros (bits) "Hb". cbn [subst_var subst_var_val].
 iApply wp_var_bind. iIntros (out) "Ho". cbn [subst_var subst_var_val].
 lazymatch goal with |- envs_entails ?Γ (WP _ {{?Φ}}) =>
 change (envs_entails Γ (WP Seq (scan_loop valid padding symbols acc bits out src scratch (length chars))
   (commit_e valid padding symbols acc out scratch dst (length chars)) {{Φ}})) end.

 iApply (wp_bind [SeqCtx (commit_e valid padding symbols acc out scratch dst (length chars))]).
 iApply (wp_wand with "[Hv Hp Hs Ha Hb Ho Hsrc Hscratch]").
 { iApply (scan_loop_wp with "[Hv Hp Hs Ha Hb Ho] Hsrc Hscratch"); [lia|rewrite length_replicate; done|].
   unfold scan_cells,initial_scan. simpl. iFrame. }
 iIntros (u) "[%Hu [Hstate [Hsrc Hscratch]]]". subst u.
 iDestruct "Hscratch" as (tail) "[%Htail Hscratch]". iApply wp_seq.
 iApply (wp_wand with "[Hstate Hscratch Hblock Hdst]").
 { iApply (commit_wp with "Hstate Hscratch Hblock Hdst"); auto. }
 iIntros (u) "[Hstate Hdst]".
 iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
 iExists _. iFrame "Ho". iExists _. iFrame "Hb".
 iExists _. iFrame "Ha". iExists _. iFrame "Hs".
 iExists _. iFrame "Hp". iExists _. iFrame "Hv Hsrc".
 pose proof (base32_stream.scan_decode chars) as Hdecode.
 assert (Hsize : ((2 <=? length chars) && (length chars <=? 208))%nat = true).
 { apply Bool.andb_true_iff. split; apply Nat.leb_le; lia. }
 rewrite Hsize in Hdecode.
 pose proof (validation_finish chars (scan chars)) as Hfinish.
 rewrite Hdecode -Hfinish.
 destruct (validation_result (scan chars) (length chars)); iExact "Hdst".
Qed.
End proofs.
