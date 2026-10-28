(** HOTP allocation and truncation composition, parameterized by HMAC. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory encoding crypto_bounds crypto_truncate crypto_buffers.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition hmac_application key keyLen msg msgLen dst :=
 App (Val (RecV None (Some "args") hmac_body))
 (Val (StructV [LitV (LitPtr key);LitV (LitInt keyLen);LitV (LitPtr msg);LitV (LitInt msgLen);LitV (LitPtr dst)])).
Definition hotp_compute key keyLen counter digits :=
 lets [("msg",Alloc (int 8));("digest",Alloc (int 20))]
 (seqs [emit_be (v "msg") (int 0) (int counter) 8;
   call hmac_body [pv key;int keyLen;v "msg";int 8;v "digest"]]
 (lets [("off",band (get (v "digest") (int 19)) (int 15));
   ("binary",band (fold_left (fun acc j => add (mul acc (int 256))
     (get (v "digest") (add (v "off") (int j)))) [0;1;2;3] (int 0)) (int 2147483647));
   ("code",rem (v "binary") (If (eq (int digits) (int 6)) (int 1000000) (int 100000000)))]
  (seqs [Free (v "digest");Free (v "msg")] (v "code")))).
Definition hotp_compute_source :=
 match skip_let_bindings 4 hotp_body with
 | If _ (If _ success _) _ => success | _ => unit_e end.
Lemma hotp_compute_is_source key keyLen counter digits :
 subst "key" (LitV (LitPtr key)) (subst "keyLen" (LitV (LitInt keyLen))
 (subst "counter" (LitV (LitInt counter)) (subst "digits" (LitV (LitInt digits)) hotp_compute_source))) =
 hotp_compute key keyLen counter digits.
Proof. reflexivity. Qed.
Lemma hmac_closed_msg x : subst "msg" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Lemma hmac_closed_digest x : subst "digest" x hmac_body = hmac_body. Proof. reflexivity. Qed.
Opaque hmac_body model.hmac_sha1.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem hotp_compute_wp p key counter digits :
 0 <= counter -> digits = 6 \/ digits = 8 ->
 (forall msg dst message old,
  length message = 8%nat -> length old = 20%nat -> Forall byte message ->
  array.array_cells p key -∗ array.array_cells msg message -∗ array.array_cells dst old -∗
  WP hmac_application p (Z.of_nat (length key)) msg 8 dst
  {{u, ⌜u = LitV (LitBool true)⌝ ∗ array.array_cells p key ∗ array.array_cells msg message ∗
   array.array_cells dst (hmac_sha1 key message)}}) ->
 array.array_cells p key -∗
 WP hotp_compute p (Z.of_nat (length key)) counter digits
 {{u, ⌜u = LitV (LitInt (hotp key counter digits))⌝ ∗ array.array_cells p key}}.
Proof.
 intros Hcounter Hd Hhmac. iIntros "Hkey". unfold hotp_compute, lets.
 iApply (wp_bind [LetCtx (Some "msg") _]).
 iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 8). lia. }
 iIntros (u) "[%msg [%Hu [Hmsgblock Hmsg]]]". subst u.
 iApply wp_let. simpl. rewrite hmac_closed_msg.
 iApply (wp_bind [LetCtx (Some "digest") _]).
 iApply (wp_wand with "[]").
 { iApply (buffer_alloc_wp 20). lia. }
 iIntros (u) "[%digest [%Hu [Hdigestblock Hdigest]]]". subst u.
 iApply wp_let. simpl. rewrite hmac_closed_digest.
 iApply (wp_bind [SeqCtx _]).
 iApply (wp_wand with "[Hmsg]").
 { iApply (emit_be_wp msg (replicate 8 0%Z) 0 counter 8 with "Hmsg"). simpl. lia. }
 iIntros (u) "[%Hu Hmsg]". subst u. iApply wp_seq.
 iEval (simpl) in "Hmsg".
 iApply (wp_bind [SeqCtx _]).
 hm_args. iApply (wp_wand with "[Hkey Hmsg Hdigest]").
 { iApply (Hhmac with "Hkey Hmsg Hdigest"); [reflexivity|reflexivity|].
   change (Forall byte (be_bytes 8 counter)). apply be_bytes_are_bytes. exact Hcounter. }
 iIntros (u) "[%Hu [Hkey [Hmsg Hdigest]]]". subst u. iApply wp_seq.
 set (mac := hmac_sha1 key (be_bytes 8 counter)).
 iEval (fold (be_bytes 8 counter); fold mac) in "Hdigest".
 iApply (wp_bind [LetCtx (Some "off") _]).
 iApply (wp_bind [BinOpLCtx BitAndOp (int 15)]).
 iApply (wp_wand with "[Hdigest]").
 { iApply (buffer_get_wp digest mac 19 (mac !!! 19%nat) with "Hdigest").
   apply list_lookup_lookup_total_lt. unfold mac. rewrite hmac_output_length. lia. }
 iIntros (u) "[%Hu Hdigest]". subst u.
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 iApply wp_let. simpl.
 iApply (wp_bind [LetCtx (Some "binary") _]).
 assert (Hnth : mac !!! 19%nat = nth 19 mac 0%Z).
 { symmetry. apply nth_lookup_Some, list_lookup_lookup_total_lt.
   unfold mac. rewrite hmac_output_length. lia. }
 rewrite Hnth.
 assert (Hoff : Z.of_nat (Z.to_nat (Z.land (nth 19 mac 0%Z) 15)) = Z.land (nth 19 mac 0%Z) 15).
 { pose proof (truncation_offset mac). lia. }
 iApply (wp_wand with "[Hdigest]").
 { rewrite <- Hoff. iApply (truncate_word_wp with "Hdigest").
   apply truncation_access. unfold mac. apply hmac_output_length. }
 iIntros (u) "[%Hu Hdigest]". subst u. iApply wp_let. simpl.
 destruct Hd as [Hd | Hd]; subst digits; auth_pure.
 all: iApply (wp_bind [SeqCtx _]); iApply (wp_wand with "[Hdigest Hdigestblock]").
 all: try (iApply (buffer_free_wp with "Hdigest [Hdigestblock]");
   unfold mac; rewrite hmac_output_length; iExact "Hdigestblock").
 all: iIntros (u) "%Hu"; subst u; iApply wp_seq.
 all: iApply (wp_bind [SeqCtx _]); iApply (wp_wand with "[Hmsg Hmsgblock]").
 all: try (iApply (buffer_free_wp with "Hmsg Hmsgblock")).
 all: iIntros (u) "%Hu"; subst u; iApply wp_seq; iApply wp_value'; iFrame; done.
Qed.
End proofs.
