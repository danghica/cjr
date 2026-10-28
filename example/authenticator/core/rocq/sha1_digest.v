(** Output of the five owned SHA-1 state words into the caller's digest buffer. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory encoding encoding_stack sha1_rounds.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition digest_emission p h0 h1 h2 h3 h4 := seqs
 [emit_be (pv p) (int 0) (StackLoad (Val (LitV (LitStack h0)))) 4;
  emit_be (pv p) (int 4) (StackLoad (Val (LitV (LitStack h1)))) 4;
  emit_be (pv p) (int 8) (StackLoad (Val (LitV (LitStack h2)))) 4;
  emit_be (pv p) (int 12) (StackLoad (Val (LitV (LitStack h3)))) 4;
  emit_be (pv p) (int 16) (StackLoad (Val (LitV (LitStack h4)))) 4] unit_e.
Lemma emission_append (prefix old : list Z) start (bytes : list Z) : length prefix = start ->
 (start <= length old)%nat ->
 (take start (prefix ++ drop start old) ++ bytes) ++ drop (start+length bytes) (prefix ++ drop start old) =
 (prefix ++ bytes) ++ drop (start+length bytes) old.
Proof.
 intros Hprefix Hlen. rewrite take_app_length'; last lia.
 rewrite drop_app_ge; last lia. rewrite drop_drop. rewrite Hprefix.
 replace (start+(start+length bytes-start))%nat with (start+length bytes)%nat by lia. done.
Qed.
Lemma emission_append_four (prefix old : list Z) start x : length prefix = start ->
 (start <= length old)%nat ->
 (take start (prefix ++ drop start old) ++ model.be_bytes 4 x) ++
   drop (start+4) (prefix ++ drop start old) =
 (prefix ++ model.be_bytes 4 x) ++ drop (start+4) old.
Proof.
 intros Hprefix Hlen. pose proof (emission_append prefix old start (model.be_bytes 4 x) Hprefix Hlen) as H.
 rewrite model.be_bytes_length in H. exact H.
Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem digest_emission_wp p words h0 h1 h2 h3 h4 st : (20 <= length words)%nat ->
 state_at h0 h1 h2 h3 h4 st -∗ array.array_cells p words -∗
 WP digest_emission p h0 h1 h2 h3 h4
 {{u, ⌜u = LitV LitUnit⌝ ∗ state_at h0 h1 h2 h3 h4 st ∗
   array.array_cells p (flat_map (model.be_bytes 4) st ++ drop 20 words)}}.
Proof.
 intros Hlen. iIntros "Hstate Hd".
 iDestruct "Hstate" as (av bv cv dv ev) "[%Hst [Ha [Hb [Hc [Hdstate He]]]]]". subst st.
 unfold digest_emission. cbn [seqs fold_right].
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Ha Hd]").
 { iApply (emit_be_stack_wp p words 0 h0 av 4 with "Ha Hd"). lia. }
 iIntros (u) "[%Hu [Ha Hd]]". subst u. iApply wp_seq.
 iEval (rewrite take_0 app_nil_l Nat.add_0_l) in "Hd".
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hb Hd]").
 { iApply (emit_be_stack_wp p _ 4 h1 bv 4 with "Hb Hd").
   rewrite !length_app !model.be_bytes_length length_drop. lia. }
 iIntros (u) "[%Hu [Hb Hd]]". subst u. iApply wp_seq.
 iEval (rewrite emission_append_four; [|rewrite ?length_app ?model.be_bytes_length;lia|lia]) in "Hd".
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hc Hd]").
 { iApply (emit_be_stack_wp p _ 8 h2 cv 4 with "Hc Hd").
   rewrite !length_app !model.be_bytes_length length_drop. lia. }
 iIntros (u) "[%Hu [Hc Hd]]". subst u. iApply wp_seq.
 iEval (rewrite emission_append_four; [|rewrite ?length_app ?model.be_bytes_length;lia|lia]) in "Hd".
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hdstate Hd]").
 { iApply (emit_be_stack_wp p _ 12 h3 dv 4 with "Hdstate Hd").
   rewrite !length_app !model.be_bytes_length length_drop. lia. }
 iIntros (u) "[%Hu [Hdstate Hd]]". subst u. iApply wp_seq.
 iEval (rewrite emission_append_four; [|rewrite ?length_app ?model.be_bytes_length;lia|lia]) in "Hd".
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[He Hd]").
 { iApply (emit_be_stack_wp p _ 16 h4 ev 4 with "He Hd").
   rewrite !length_app !model.be_bytes_length length_drop. lia. }
 iIntros (u) "[%Hu [He Hd]]". subst u. iApply wp_seq.
 iEval (rewrite emission_append_four; [|rewrite ?length_app ?model.be_bytes_length;lia|lia]) in "Hd".
 iApply wp_value'. iSplit; first done. iSplitL "Ha Hb Hc Hdstate He".
 - iExists _,_,_,_,_. iFrame. done.
 - cbn [flat_map]. rewrite app_nil_r !app_assoc.
   iExact "Hd".
Qed.
End proofs.
