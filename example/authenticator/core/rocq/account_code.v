(** Concrete session dispatch into the cryptographic port. This modular
    contract requires the caller to supply the precise TOTP implementation WP. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory sessions crypto_totp crypto_hmac crypto_composition memory_application sha1_entry.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Lemma totp_body_session_closed x : subst "session" x totp_body = totp_body.
Proof. reflexivity. Qed.
Lemma totp_body_id_closed x : subst "id" x totp_body = totp_body.
Proof. reflexivity. Qed.
Lemma totp_body_timestamp_closed x : subst "timestamp" x totp_body = totp_body.
Proof. reflexivity. Qed.
Lemma totp_body_index_closed x : subst "index" x totp_body = totp_body.
Proof. reflexivity. Qed.
Lemma totp_body_entry_closed x : subst "entry" x totp_body = totp_body.
Proof. reflexivity. Qed.
Opaque totp_body scan_identifiers.
#[local] Hint Rewrite totp_body_session_closed totp_body_id_closed totp_body_timestamp_closed
 totp_body_index_closed totp_body_entry_closed : code_subst.
Ltac code_args :=
 iStartProof; repeat (simpl; cbn [fill fill_item]; autorewrite with code_subst;
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [iApply wp_offset; iIntros "!> _" | hm_args_head]) end);
 simpl; cbn [fill fill_item]; autorewrite with code_subst.
Definition entry_offset index := (2+390*index)%nat.
Definition entry_secret words index :=
 take (Z.to_nat (default 0 (words !! (entry_offset index+5)%nat)))
  (drop (entry_offset index+262) words).
Definition code_slots_valid (words : list Z) := forall index,
 (index < 16)%nat -> 1 <= slot_identifier words index ->
 1 <= default 0 (words !! (entry_offset index+5)%nat) <= 128 /\
 Forall byte (entry_secret words index) /\
 valid_parameters (default 0 (words !! (entry_offset index+1)%nat))
                  (default 0 (words !! (entry_offset index+2)%nat)).
Definition session_code_value words id timestamp :=
 let found := scan_identifiers words id 16 in
 if bool_decide (0 <= found) then
 model.totp (entry_secret words (Z.to_nat found)) timestamp
  (default 0 (words !! (entry_offset (Z.to_nat found)+2)%nat))
  (default 0 (words !! (entry_offset (Z.to_nat found)+1)%nat))
 else -1.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem session_code_from_totp_wp p words id timestamp (Phi : val -> iProp Σ) :
 length words = 6242%nat ->
 (∀ index : nat, ⌜(index < 16)%nat⌝ -∗
   ⌜scan_identifiers words id 16 = Z.of_nat index⌝ -∗
   array.array_cells p words -∗
   WP totp_application (p+Z.of_nat (2+390*index+262))
     (default 0 (words !! (2+390*index+5)%nat)) timestamp
     (default 0 (words !! (2+390*index+2)%nat))
     (default 0 (words !! (2+390*index+1)%nat)) {{Phi}}) -∗
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, if bool_decide (0 <= scan_identifiers words id 16) then Phi u
      else ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hlen. iIntros "Htotp Hs".
 unfold call at 1. unfold code_body,args. hm_args. iApply wp_app. simpl. hm_admin.
 match goal with |- envs_entails _ (WP Let ?x ?e ?b {{_}}) =>
   iApply (wp_bind [LetCtx x b]) end.
 iApply (wp_wand with "[Hs]").
 { iApply (session_find_wp p words id Hlen with "Hs"). }
 iIntros (u) "[%Hu Hs]". subst u. hm_pure.
 destruct (bool_decide (0 <= scan_identifiers words id 16)) eqn:Hfound.
 - apply bool_decide_eq_true in Hfound. iApply wp_if_true.
   pose proof (scan_identifiers_range words id 16) as Hrange.
   set (index := Z.to_nat (scan_identifiers words id 16)).
   assert (Hindex : (index < 16)%nat) by (unfold index; lia).
   assert (Hki : Z.of_nat index = scan_identifiers words id 16) by (unfold index; lia).
   set (offset := (2+390*index)%nat).
   assert (Hbound : (offset+390 <= length words)%nat).
   { unfold offset. rewrite Hlen. change (2+390*index+390 <= 2+390*16)%nat. lia. }
   code_args.
   assert (Haddr : p + (2 + scan_identifiers words id 16 * 390) = p + Z.of_nat offset).
   { unfold offset. rewrite Nat2Z.inj_add Nat2Z.inj_mul Hki. ring. }
   rewrite Haddr.
   assert (Hsecretindex : (offset+5 < length words)%nat) by lia.
   destruct (lookup_lt_is_Some_2 words _ Hsecretindex) as [secret_length Hsecret].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hsecret|].
   replace (p+Z.of_nat offset+5) with (p+Z.of_nat (offset+5)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". code_args.
   assert (Hperiodindex : (offset+2 < length words)%nat) by lia.
   destruct (lookup_lt_is_Some_2 words _ Hperiodindex) as [period Hperiod].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hperiod|].
   replace (p+Z.of_nat offset+2) with (p+Z.of_nat (offset+2)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". code_args.
   assert (Hdigitsindex : (offset+1 < length words)%nat) by lia.
   destruct (lookup_lt_is_Some_2 words _ Hdigitsindex) as [digits Hdigits].
   iDestruct (big_sepL_lookup_acc with "Hs") as "[Hcell Hclose]"; [exact Hdigits|].
   replace (p+Z.of_nat offset+1) with (p+Z.of_nat (offset+1)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
   iDestruct ("Hclose" with "Hcell") as "Hs". code_args.
   replace (p+Z.of_nat offset+262) with (p+Z.of_nat (offset+262)) by (rewrite Nat2Z.inj_add; simpl; ring).
   iSpecialize ("Htotp" $! index with "[] []").
   { done. }
   { iPureIntro. symmetry. exact Hki. }
   iEval (fold offset; rewrite Hsecret Hperiod Hdigits; simpl; unfold totp_application) in "Htotp".
   iApply ("Htotp" with "Hs").
 - iApply wp_if_false. iApply wp_value'. iFrame. done.
Qed.
Theorem session_code_absent_wp p words id timestamp :
 length words = 6242%nat -> scan_identifiers words id 16 < 0 ->
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hlen Habsent. iIntros "Hs".
 iApply (wp_wand with "[Hs]").
 { iApply (session_code_from_totp_wp p words id timestamp
     (fun _ => False%I) Hlen with "[] Hs").
   iIntros (index) "%Hindex %Hfound Hs". iExFalso. iPureIntro. lia. }
 iIntros (u) "H". rewrite bool_decide_false; [iExact "H"|lia].
Qed.
Theorem session_code_sha_wp p words id timestamp :
 sha_refinement -> length words = 6242%nat -> code_slots_valid words -> 0 <= timestamp ->
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u = LitV (LitInt (session_code_value words id timestamp))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hsha Hlen Hvalid Htime. iIntros "Hs".
 iApply (wp_wand with "[Hs]").
 { iApply (session_code_from_totp_wp p words id timestamp
   (fun u => ⌜u = LitV (LitInt (session_code_value words id timestamp))⌝ ∗ array.array_cells p words)%I
   Hlen with "[] Hs").
   iIntros (index) "%Hindex %Hfound Hs".
   assert (Hnonnegative : 0 <= scan_identifiers words id 16) by lia.
   destruct (scan_identifiers_present words id 16 Hnonnegative) as [selected [Hselected [Hsame [Hid Hslot]]]].
   assert (Hselectedindex : selected = index) by lia. subst selected.
   assert (Hpositive : 1 <= slot_identifier words index) by lia.
   destruct (Hvalid index Hindex Hpositive) as [Hkeylen [Hkeybytes Hparams]].
   set (offset := entry_offset index).
   set (count := Z.to_nat (default 0 (words !! (offset+5)%nat))).
   assert (Hcount : (1 <= count <= 128)%nat) by (unfold count,offset in *; lia).
   assert (Hbound : (offset+262+count <= length words)%nat).
   { unfold offset,entry_offset. rewrite Hlen. change (2+390*index+262+count <= 2+390*16)%nat. lia. }
   assert (Hsecretlen : length (entry_secret words index) = count).
   { unfold entry_secret. fold offset count. rewrite length_take length_drop. lia. }
   iDestruct (cells_slice_acc p words (offset+262) count Hbound with "Hs") as "[Hkey Hclose]".
   iAssert (array.array_cells (p+Z.of_nat (offset+262)) (entry_secret words index)) with "[Hkey]" as "Hkey".
   { iExact "Hkey". }
   assert (Hrawlen : default 0 (words !! (offset+5)%nat) = Z.of_nat (length (entry_secret words index))).
   { rewrite Hsecretlen. unfold count. lia. }
   iApply (wp_wand with "[Hkey]").
   { change (default 0 (words !! (offset+5)%nat)) with
       (default 0 (words !! (entry_offset index+5)%nat)) in Hrawlen.
     rewrite Hrawlen.
     iApply (totp_sha_wp with "Hkey"); try assumption.
     rewrite Hsecretlen. exact Hcount. }
   iIntros (u) "[%Hu Hkey]".
   iDestruct ("Hclose" $! (entry_secret words index) with "[] Hkey") as "Hs".
   { done. }
   iEval (rewrite slice_restore) in "Hs".
   iFrame. iPureIntro. rewrite Hu. unfold session_code_value.
   rewrite bool_decide_true; last exact Hnonnegative. rewrite Hfound Nat2Z.id. reflexivity.
 }
 iIntros (u) "H". destruct (bool_decide (0 <= scan_identifiers words id 16)) eqn:Hfound.
 - iExact "H".
 - iDestruct "H" as "[%Hu Hs]". iFrame. iPureIntro. rewrite Hu.
   unfold session_code_value. rewrite Hfound. reflexivity.
Qed.
Opaque hotp_body.
Transparent totp_body.
Theorem totp_negative_preserves_wp key keyLen timestamp period digits (P : iProp Σ) :
 timestamp < 0 -> P -∗
 WP totp_application key keyLen timestamp period digits
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ P}}.
Proof.
 intros Hnegative. iIntros "HP".
 unfold totp_application,totp_body,args,parameters,range,both,le,eq,pv,int,v,op.
 iApply wp_app. hm_pure.
 destruct (bool_decide (digits=6)) eqn:Hd6;
 [iApply wp_if_true|iApply wp_if_false]; hm_pure.
 all: rewrite (bool_decide_false (0 <= timestamp) ltac:(lia)).
 all: rewrite Bool.andb_false_r; iApply wp_if_false; iApply wp_value'; iFrame; done.
Qed.
Theorem session_code_negative_wp p words id timestamp :
 length words = 6242%nat -> timestamp < 0 ->
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hlen Hnegative. iIntros "Hs".
 iApply (wp_wand with "[Hs]").
 { iApply (session_code_from_totp_wp p words id timestamp
     (fun u => ⌜u = LitV (LitInt (-1))⌝ ∗ array.array_cells p words)%I Hlen with "[] Hs").
   iIntros (index) "%Hindex %Hfound Hs".
   iApply (totp_negative_preserves_wp with "Hs"). exact Hnegative. }
 iIntros (u) "H". destruct (bool_decide (0 <= scan_identifiers words id 16)); iExact "H".
Qed.
Theorem session_code_checked_sha_wp p words id timestamp :
 sha_refinement -> length words = 6242%nat -> code_slots_valid words ->
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u = LitV (LitInt (if bool_decide (0 <= timestamp)
    then session_code_value words id timestamp else -1))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hsha Hlen Hvalid. iIntros "Hs".
 destruct (decide (0 <= timestamp)) as [Htime|Htime].
 - rewrite bool_decide_true; last exact Htime. iApply (session_code_sha_wp with "Hs"); assumption.
 - rewrite bool_decide_false; last exact Htime. iApply (session_code_negative_wp with "Hs"); try assumption; lia.
Qed.
Theorem session_code_wp p words id timestamp :
 length words = 6242%nat -> code_slots_valid words ->
 array.array_cells p words -∗
 WP call code_body [pv p;int id;int timestamp]
 {{u, ⌜u = LitV (LitInt (if bool_decide (0 <= timestamp)
    then session_code_value words id timestamp else -1))⌝ ∗ array.array_cells p words}}.
Proof.
 intros Hlen Hvalid. iIntros "Hs".
 iApply (session_code_checked_sha_wp with "Hs"); try assumption.
 apply sha_refinement_proved.
Qed.
End proofs.
