(** HMAC heap composition with SHA-1 as an explicit refinement premise. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory memory_calls crypto_bounds crypto_buffers crypto_hmac_key.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition sha_application src n dst :=
 App (Val (RecV None (Some "args") sha_body))
 (Val (StructV [LitV (LitPtr src);LitV (LitInt n);LitV (LitPtr dst)])).
Definition hmac_compute key keyLen msg msgLen dst :=
 lets [("kb",Alloc (int 64));("inner",Alloc (int 1088));("outer",Alloc (int 84));("digest",Alloc (int 20))]
 (seqs [If (le (int keyLen) (int 64)) (copy (pv key) (v "kb") (int keyLen))
    (Seq (call sha_body [pv key;int keyLen;v "kb"]) unit_e);
   loop "i" (int 0) (int 64) (seqs
    [put (v "inner") (v "i") (xor (get (v "kb") (v "i")) (int 54))]
    (put (v "outer") (v "i") (xor (get (v "kb") (v "i")) (int 92))));
   copy (pv msg) (ptr (v "inner") (int 64)) (int msgLen);
   call sha_body [v "inner";add (int msgLen) (int 64);v "digest"];
   copy (v "digest") (ptr (v "outer") (int 64)) (int 20);
   call sha_body [v "outer";int 84;pv dst];
   Free (v "digest");Free (v "outer");Free (v "inner");Free (v "kb")] yes).
Definition hmac_compute_source :=
 match skip_let_bindings 5 hmac_body with
 | If _ (If _ success _) _ => success | _ => unit_e end.
Lemma hmac_compute_is_source key keyLen msg msgLen dst :
 subst "key" (LitV (LitPtr key)) (subst "keyLen" (LitV (LitInt keyLen))
 (subst "msg" (LitV (LitPtr msg)) (subst "msgLen" (LitV (LitInt msgLen))
 (subst "dst" (LitV (LitPtr dst)) hmac_compute_source)))) = hmac_compute key keyLen msg msgLen dst.
Proof. reflexivity. Qed.
Lemma sha_closed_kb x : subst "kb" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma sha_closed_inner x : subst "inner" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma sha_closed_outer x : subst "outer" x sha_body = sha_body. Proof. reflexivity. Qed.
Lemma sha_closed_digest x : subst "digest" x sha_body = sha_body. Proof. reflexivity. Qed.
Opaque sha_body model.sha1 hmac_key_block.
Ltac hmac_args := iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) => hm_focus e ltac:(fun _ =>
 first [iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition sha_refinement := forall src words dst old n,
 (n <= length words)%nat -> (n <= 2048)%nat -> (20 <= length old)%nat ->
 Forall byte (take n words) ->
 array.array_cells src words -∗ array.array_cells dst old -∗
 WP sha_application src (Z.of_nat n) dst
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells src words ∗
   array.array_cells dst (sha1 (take n words) ++ drop 20 old)}}.
Theorem sha_call_from_application src words dst old n :
 sha_refinement ->
 (n <= length words)%nat -> (n <= 2048)%nat -> (20 <= length old)%nat ->
 Forall byte (take n words) ->
 array.array_cells src words -∗ array.array_cells dst old -∗
 WP call sha_body [pv src;int (Z.of_nat n);pv dst]
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells src words ∗
   array.array_cells dst (sha1 (take n words) ++ drop 20 old)}}.
Proof.
 intros Hsha Hn Hmax Hout Hbytes. iIntros "Hs Hd". unfold call, pv, int. hmac_args.
 iApply (Hsha with "Hs Hd"); assumption.
Qed.
Theorem hmac_compute_wp keyp key msgp msg dst old :
 sha_refinement ->
 (length key <= 128)%nat -> (length msg <= 1024)%nat -> (20 <= length old)%nat ->
 Forall byte key -> Forall byte msg ->
 array.array_cells keyp key -∗ array.array_cells msgp msg -∗ array.array_cells dst old -∗
 WP hmac_compute keyp (Z.of_nat (length key)) msgp (Z.of_nat (length msg)) dst
 {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells keyp key ∗ array.array_cells msgp msg ∗
   array.array_cells dst (hmac_sha1 key msg ++ drop 20 old)}}.
Proof.
 intros Hsha Hkeylen Hmsglen Hold Hkeybytes Hmsgbytes. iIntros "Hkey Hmsg Hd".
 unfold hmac_compute, lets.
 iApply (wp_bind [LetCtx (Some "kb") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 64). lia. }
 iIntros (u) "[%kb [%Hu [Hkbblock Hkb]]]". subst u. iApply wp_let. simpl. rewrite !sha_closed_kb.
 iApply (wp_bind [LetCtx (Some "inner") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 1088). lia. }
 iIntros (u) "[%inner [%Hu [Hinnerblock Hinner]]]". subst u. iApply wp_let. simpl. rewrite !sha_closed_inner.
 iApply (wp_bind [LetCtx (Some "outer") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 84). lia. }
 iIntros (u) "[%outer [%Hu [Houterblock Houter]]]". subst u. iApply wp_let. simpl. rewrite !sha_closed_outer.
 iApply (wp_bind [LetCtx (Some "digest") _]). iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 20). lia. }
 iIntros (u) "[%digest [%Hu [Hdigestblock Hdigest]]]". subst u. iApply wp_let. simpl. rewrite !sha_closed_digest.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hkey Hkb]").
 { iApply (prepare_hmac_key_wp with "Hkey Hkb"); [exact Hkeylen|].
   iIntros "Hkey Hkb". iApply (wp_wand with "[Hkey Hkb]").
   { iApply (sha_call_from_application _ _ _ _ (length key) Hsha with "Hkey Hkb");
     try (rewrite take_ge; [exact Hkeybytes|lia]); simpl; lia. }
   iIntros (u) "[%Hu [Hkey Hkb]]". iFrame "Hkey". iSplit; [done|].
   rewrite take_ge; last lia. iExact "Hkb". }
 iIntros (u) "[%Hu [Hkey Hkb]]". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hkb Hinner Houter]").
 { iApply (xor_pad_loop_wp kb inner outer (hmac_key_block key) (replicate 1088 0%Z)
   (replicate 84 0%Z) with "Hkb Hinner Houter");
   try (rewrite hmac_key_block_length; lia); rewrite length_replicate; lia. }
 iIntros (u) "[%Hu [Hkb [Hinner Houter]]]". subst u. iApply wp_seq.
 iEval (rewrite take_ge; last (rewrite hmac_key_block_length; lia)) in "Hinner Houter".
 iEval (rewrite drop_replicate) in "Hinner Houter".
 set (ipad := map (fun b => Z.lxor b 54) (hmac_key_block key)).
 set (opad := map (fun b => Z.lxor b 92) (hmac_key_block key)).
 assert (Hipadlen : length ipad = 64%nat) by (unfold ipad; rewrite length_map hmac_key_block_length; done).
 assert (Hopadlen : length opad = 64%nat) by (unfold opad; rewrite length_map hmac_key_block_length; done).
 iDestruct (cells_app with "Hinner") as "[Hipad Hinner]".
 iApply (wp_bind [SeqCtx _]).
 hmac_args. iEval (rewrite Hipadlen) in "Hinner".
 iApply (wp_wand with "[Hmsg Hinner]").
 { iApply (copy_application_wp msgp (inner+64) msg (replicate 1024 0%Z) (length msg) with "Hmsg Hinner");
   rewrite ?length_replicate; lia. }
 iIntros (u) "[%Hu [Hmsg Hinner]]". subst u. iApply wp_seq.
 iEval (rewrite take_ge; last lia) in "Hinner".
 iAssert (array.array_cells inner (ipad ++ (msg ++ drop (length msg) (replicate 1024 0%Z))))
  with "[Hipad Hinner]" as "Hinner".
 { iApply cells_app. rewrite Hipadlen. iFrame. }
 iApply (wp_bind [SeqCtx _]). hmac_args.
 replace (Z.of_nat (length msg) + 64) with (Z.of_nat (64 + length msg)) by lia.
 iApply (wp_wand with "[Hinner Hdigest]").
 { iApply (Hsha inner (ipad ++ (msg ++ drop (length msg) (replicate 1024 0%Z))) digest (replicate 20 0%Z) (64+length msg)%nat with "Hinner Hdigest").
   - rewrite length_app length_app Hipadlen length_drop length_replicate. lia.
   - lia.
   - rewrite length_replicate. lia.
   - replace (64 + length msg)%nat with (length ipad + length msg)%nat by lia.
     rewrite app_assoc. rewrite <- length_app. rewrite take_app_length.
     apply Forall_app. split; [apply hmac_pad_bytes; [exact Hkeybytes|unfold byte; lia]|exact Hmsgbytes]. }
 iIntros (u) "[%Hu [Hinner Hdigest]]". subst u. iApply wp_seq.
 assert (Hprefix : take (64+length msg)%nat (ipad ++ (msg ++ drop (length msg) (replicate 1024 0%Z))) = ipad ++ msg).
 { replace (64+length msg)%nat with (length ipad + length msg)%nat by lia.
   rewrite app_assoc. rewrite <- length_app. apply take_app_length. }
 iEval (rewrite Hprefix drop_replicate; simpl; rewrite app_nil_r) in "Hdigest".
 iDestruct (cells_app with "Houter") as "[Hopad Houter]".
 iEval (rewrite Hopadlen) in "Houter".
 iApply (wp_bind [SeqCtx _]). hmac_args.
 iApply (wp_wand with "[Hdigest Houter]").
 { iApply (copy_application_wp digest (outer+64) (sha1 (ipad++msg)) (replicate 20 0%Z) 20 with "Hdigest Houter");
   rewrite ?sha1_output_length ?length_replicate; lia. }
 iIntros (u) "[%Hu [Hdigest Houter]]". subst u. iApply wp_seq.
 iEval (rewrite take_ge; last (rewrite sha1_output_length; lia); simpl; rewrite app_nil_r) in "Houter".
 iAssert (array.array_cells outer (opad ++ sha1 (ipad ++ msg))) with "[Hopad Houter]" as "Houter".
 { iApply cells_app. rewrite Hopadlen. iFrame. }
 iApply (wp_bind [SeqCtx _]). hmac_args.
 iApply (wp_wand with "[Houter Hd]").
 { iApply (Hsha outer (opad ++ sha1 (ipad ++ msg)) dst old 84%nat with "Houter Hd").
   - rewrite length_app Hopadlen sha1_output_length. lia.
   - lia.
   - exact Hold.
   - rewrite take_ge; last (rewrite length_app Hopadlen sha1_output_length; lia).
     apply Forall_app. split; [apply hmac_pad_bytes; [exact Hkeybytes|unfold byte; lia]|apply sha1_output_bytes]. }
 iIntros (u) "[%Hu [Houter Hd]]". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hdigest Hdigestblock]").
 { iApply (buffer_free_wp with "Hdigest [Hdigestblock]"). rewrite sha1_output_length. iExact "Hdigestblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Houter Houterblock]").
 { iApply (buffer_free_wp with "Houter [Houterblock]"). rewrite length_app Hopadlen sha1_output_length. iExact "Houterblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hinner Hinnerblock]").
 { iApply (buffer_free_wp with "Hinner [Hinnerblock]").
   assert (Hsize : length (ipad ++ (msg ++ drop (length msg) (replicate 1024 0%Z))) = 1088%nat).
   { rewrite length_app length_app Hipadlen length_drop length_replicate. lia. }
   rewrite Hsize. iExact "Hinnerblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq.
 iApply (wp_bind [SeqCtx _]). iApply (wp_wand with "[Hkb Hkbblock]").
 { iApply (buffer_free_wp with "Hkb [Hkbblock]"). rewrite hmac_key_block_length. iExact "Hkbblock". }
 iIntros (u) "%Hu". subst u. iApply wp_seq. iApply wp_value'.
 iFrame "Hkey Hmsg". iSplit; [done|].
 iEval (rewrite take_ge; last (rewrite length_app Hopadlen sha1_output_length; lia)) in "Hd".
 rewrite hmac_key_block_model. iExact "Hd".
Qed.
End proofs.
