(** Public whole-function Base32 contracts, including atomic rejection. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory base32_stream base32_refinement base32_decoder.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition base32_application src n dst :=
 App (Val (RecV None (Some "args") base32_body))
  (Val (StructV [LitV (LitPtr src); LitV (LitInt n); LitV (LitPtr dst)])).
Lemma decode_length chars decoded : base32.decode chars = Some decoded ->
 (1 <= length decoded <= 128)%nat.
Proof.
 unfold base32.decode.
 destruct ((2 <=? length chars) && (length chars <=? 208))%nat; [|discriminate].
 destruct (base32.read_symbols chars) as [[ds pad]|]; [|discriminate].
 destruct (((length ds mod 8 =? 1) || (length ds mod 8 =? 3) || (length ds mod 8 =? 6))%nat); [discriminate|].
 destruct ((pad =? 0)%nat || ((length chars mod 8 =? 0) && (1 <=? pad) && (pad <=? 6))%nat); [|discriminate].
 destruct (base32.decode_values ds 0 0) as [bytes tail].
 destruct ((((1 <=? length bytes) && (length bytes <=? 128))%nat) && (tail =? 0)%Z) eqn:Hout; [|discriminate].
 intros Hdecoded. inversion Hdecoded; subst decoded.
 apply Bool.andb_true_iff in Hout as [Hlength Htail].
 apply Bool.andb_true_iff in Hlength as [Hlo Hhi].
 apply Nat.leb_le in Hlo,Hhi. lia.
Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem base32_application_reject_size_wp src n dst : n < 2 \/ 208 < n ->
 ⊢ WP base32_application src n dst {{u, ⌜u = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hn. unfold base32_application. iApply wp_app.
 unfold base32_body,args,range,both,le,int,v,op.
 destruct (decide (2 <= n)) as [Hlo|Hlo]; auth_pure; done.
Qed.
Theorem base32_application_wp src chars dst dst_words :
 (128 <= length dst_words)%nat ->
 array.array_cells src chars -∗ array.array_cells dst dst_words -∗
 WP base32_application src (Z.of_nat (length chars)) dst
 {{u, array.array_cells src chars ∗
   match base32.decode chars with
   | None => ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells dst dst_words
   | Some decoded => ⌜u = LitV (LitInt (Z.of_nat (length decoded)))⌝ ∗
     array.array_cells dst (decoded ++ drop (length decoded) dst_words)
   end}}.
Proof.
 intros Hdst. iIntros "Hsrc Hdst".
 destruct (decide (2 <= length chars <= 208)%nat) as [Hgood|Hbad].
 - iApply (base32_application_valid_size_wp with "Hsrc Hdst"); auto.
 - iApply (wp_wand with "[]").
   { iApply base32_application_reject_size_wp. lia. }
   iIntros (u) "%Hu". iFrame "Hsrc".
   unfold base32.decode.
   assert (Hsize : ((2 <=? length chars) && (length chars <=? 208))%nat = false).
   { apply Bool.andb_false_iff. destruct (decide (2 <= length chars)%nat);
     [right|left]; apply Nat.leb_gt; lia. }
   rewrite Hsize. iFrame. done.
Qed.
Theorem base32_decode_wp src chars dst dst_words :
 (128 <= length dst_words)%nat ->
 array.array_cells src chars -∗ array.array_cells dst dst_words -∗
 WP call base32_body [pv src; int (Z.of_nat (length chars)); pv dst]
 {{u, array.array_cells src chars ∗
   match base32.decode chars with
   | None => ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells dst dst_words
   | Some decoded => ⌜u = LitV (LitInt (Z.of_nat (length decoded)))⌝ ∗
     array.array_cells dst (decoded ++ drop (length decoded) dst_words)
   end}}.
Proof.
 intros Hdst. iIntros "Hsrc Hdst". unfold call. hm_args.
 iApply (base32_application_wp with "Hsrc Hdst"). exact Hdst.
Qed.
End proofs.
