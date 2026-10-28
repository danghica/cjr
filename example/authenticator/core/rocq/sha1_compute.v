(** Complete successful SHA-1 heap computation, including both temporary frees. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory padding padding_memory padding_native sha1_blocks sha1_iteration sha1_memory round_model sha1_rounds sha1_compress sha1_state.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Fixpoint sha_strip_lets n e := match n,e with S n, Let _ _ rest => sha_strip_lets n rest | _,_ => e end.
Definition sha_compute_source := match sha_strip_lets 3 sha_body with
 | If _ (If _ success _) _ => success | _ => unit_e end.
Definition sha_compute p n q := subst "src" (LitV (LitPtr p))
 (subst "n" (LitV (LitInt n)) (subst "dst" (LitV (LitPtr q)) sha_compute_source)).
Lemma hash_blocks_prefix_suffix fuel msg suffix st :
 (64*fuel <= length msg)%nat ->
 model.hash_blocks fuel (msg++suffix) st = model.hash_blocks fuel msg st.
Proof.
 revert msg st. induction fuel as [|fuel IH]; intros msg st Hlen; first done.
 rewrite !hash_blocks_left. rewrite take_app_le; last lia.
 rewrite drop_app_le; last lia. apply IH. rewrite length_drop. lia.
Qed.
Lemma padded_hash_result msg :
 flat_map (model.be_bytes 4)
   (model.hash_blocks (padded_size (length msg)/64)
     (model.padding msg ++ drop (padded_size (length msg)) (replicate 2112 0)) model.initial) = model.sha1 msg.
Proof.
 unfold model.sha1. rewrite padding_length.
 rewrite hash_blocks_prefix_suffix; first done.
 rewrite padding_length. pose proof (Nat.div_mod (padded_size (length msg)) 64 ltac:(lia)). nia.
Qed.
#[local] Hint Rewrite round_closed_pad round_closed_w : compute_subst.
Opaque round_body model.hash_blocks model.sha1 model.schedule_more.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem sha_compute_wp p msg q dst : (length msg <= 2048)%nat -> (20 <= length dst)%nat ->
 array.array_cells p msg -∗ array.array_cells q dst -∗
 WP sha_compute p (Z.of_nat (length msg)) q
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells p msg ∗
   array.array_cells q (model.sha1 msg ++ drop 20 dst)}}.
Proof.
 intros Hlen Hdst. iIntros "Hs Hd".
 unfold sha_compute, sha_compute_source, sha_strip_lets, sha_body, args.
 simpl. autorewrite with compute_subst.
 iApply (wp_bind [LetCtx (Some "pad") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 2112). lia. }
 iIntros (u) "[%pad [%Hu [Hpadblock Hpad]]]". subst u. iApply wp_let.
 simpl. autorewrite with compute_subst.
 iApply (wp_bind [LetCtx (Some "w") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 80). lia. }
 iIntros (u) "[%w [%Hu [Hwblock Hw]]]". subst u. iApply wp_let.
 simpl. autorewrite with compute_subst.
 iApply (wp_bind [LetCtx (Some "total") _]).
 iApply (wp_bind [BinOpLCtx MulOp (int 64)]).
 iApply (wp_bind [BinOpLCtx DivOp (int 64)]).
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 iApply wp_div; [lia|]. iIntros "!> _".
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 rewrite <- padded_size_native. iApply wp_let. simpl. autorewrite with compute_subst.
 match goal with |- envs_entails ?Delta (WP _ {{?Phi}}) =>
   change (envs_entails Delta (WP native_padding p pad (length msg)
     (seqs [sha_state pad w q (padded_size (length msg));Free (pv w);Free (pv pad)] yes) {{Phi}})) end.
 iApply (native_padding_wp with "Hs Hpad [Hd Hw Hpadblock Hwblock]"); first done.
 iIntros "Hs Hpad". cbn [seqs fold_right].
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hpad Hw Hd]").
 { iApply (sha_state_wp with "Hpad Hw Hd").
   - rewrite length_app padding_length length_drop length_replicate. lia.
   - apply padded_size_alignment.
   - reflexivity.
   - exact Hdst. }
 iIntros (u) "[%Hu [Hpad [Hws Hd]]]". subst u. iApply wp_seq.
 iDestruct "Hws" as (ws) "[%Hws Hw]".
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hw Hwblock]").
 { iApply (buffer_free_wp with "Hw [Hwblock]"). rewrite Hws. iExact "Hwblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hpad Hpadblock]").
 { iApply (buffer_free_wp with "Hpad [Hpadblock]").
   rewrite length_app padding_length length_drop length_replicate.
     pose proof (padded_size_capacity _ Hlen) as Hcap.
     replace (padded_size (length msg) + (2112-padded_size (length msg)))%nat with 2112%nat by lia.
     iExact "Hpadblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq. iApply wp_value'.
 iEval (rewrite padded_hash_result) in "Hd". iFrame. done.
Qed.
End proofs.
