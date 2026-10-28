(** Dynamic truncation reads exactly the four bytes selected by byte 19. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory crypto_bounds.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition truncate_word p offset := band
 (fold_left (fun acc j => add (mul acc (int 256))
   (get (pv p) (add (int offset) (int j)))) [0;1;2;3] (int 0)) (int 2147483647).
Definition truncate_digest p := Let (Some "off") (band (get (pv p) (int 19)) (int 15))
 (band (fold_left (fun acc j => add (mul acc (int 256))
   (get (pv p) (add (v "off") (int j)))) [0;1;2;3] (int 0)) (int 2147483647)).
Lemma four_nth_at (xs : list Z) i : (i+4 <= length xs)%nat ->
 firstn 4 (skipn i xs) = [xs !!! i; xs !!! S i; xs !!! S (S i); xs !!! S (S (S i))].
Proof.
 intros Hlen.
 rewrite (drop_S xs (xs !!! i) i); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S xs (xs !!! S i) (S i)); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S xs (xs !!! S (S i)) (S (S i))); last (apply list_lookup_lookup_total_lt; lia).
 cbn [take].
 rewrite (drop_S xs (xs !!! S (S (S i))) (S (S (S i)))); last (apply list_lookup_lookup_total_lt; lia).
 reflexivity.
Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem truncate_word_wp p digest offset :
 (offset+4 <= length digest)%nat ->
 array.array_cells p digest -∗
 WP truncate_word p (Z.of_nat offset)
 {{u, ⌜u = LitV (LitInt (Z.land (be_word (firstn 4 (skipn offset digest))) 2147483647))⌝ ∗
 array.array_cells p digest}}.
Proof.
 intros Hlen. iIntros "Hd".
 unfold truncate_word, band, add, mul, get, ptr, pv, int, op. cbn [fold_left].
 memory_admin.
 assert (Hread : forall j, (j < 4)%nat -> digest !! (offset+j)%nat = Some (digest !!! (offset+j)%nat)).
 { intros j Hj. apply list_lookup_lookup_total_lt. lia. }
 do 4 (match goal with
 | |- envs_entails _ (WP Load (Val (LitV (LitPtr (?p0 + (Z.of_nat ?off + ?j))))) {{_}}) =>
   let k := eval compute in (Z.to_nat j) in
   let Hlookup := fresh "Hlookup" in
   assert (Hlookup := Hread k ltac:(lia));
   iDestruct (big_sepL_lookup_acc with "Hd") as "[Hcell Hclose]"; [exact Hlookup|];
   replace (p0 + (Z.of_nat off + j)) with (p0 + Z.of_nat (off+k)) by lia;
   iApply (wp_load with "Hcell"); iIntros "!> _ Hcell";
   iDestruct ("Hclose" with "Hcell") as "Hd"; memory_admin
 end).
 iFrame. iPureIntro. rewrite (four_nth_at digest offset Hlen). rewrite Nat.add_0_r !Nat.add_succ_r !Nat.add_0_r. reflexivity.
Qed.
Theorem truncate_digest_wp p digest : length digest = 20%nat ->
 array.array_cells p digest -∗
 WP truncate_digest p
 {{u, ⌜u = LitV (LitInt (model.truncate digest))⌝ ∗ array.array_cells p digest}}.
Proof.
 intros Hlen. iIntros "Hd". unfold truncate_digest.
 iApply (wp_bind [LetCtx (Some "off") _]).
 unfold band, op. iApply (wp_bind [BinOpLCtx BitAndOp (int 15)]).
 iApply (wp_wand with "[Hd]").
 { iApply (buffer_get_wp p digest 19 (nth 19 digest 0%Z) with "Hd").
   assert (Hlookup : digest !! 19%nat = Some (digest !!! 19%nat)) by
     (apply list_lookup_lookup_total_lt; lia).
   rewrite (nth_lookup_Some digest 19 0%Z (digest !!! 19%nat) Hlookup). exact Hlookup. }
 iIntros (u) "[%Hu Hd]". subst u.
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 iApply wp_let. simpl.
 assert (Hoff : Z.of_nat (Z.to_nat (Z.land (nth 19 digest 0%Z) 15)) = Z.land (nth 19 digest 0%Z) 15).
 { pose proof (truncation_offset digest). lia. }
match goal with |- envs_entails ?Delta _ => change (envs_entails Delta (WP truncate_word p (Z.land (nth 19 digest 0%Z) 15)
 {{u, ⌜u = LitV (LitInt (model.truncate digest))⌝ ∗ array.array_cells p digest}})%I) end.
 rewrite <- Hoff. iApply (truncate_word_wp with "Hd"). apply truncation_access. exact Hlen.
Qed.
End proofs.
