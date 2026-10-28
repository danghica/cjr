(** Int64 bounds for the fixed session layout and guarded header mutations. *)
From Coq Require Import ZArith List Lia.
From cjr.authenticator Require Import model program sessions account_slots.
From iris.prelude Require Import options.
Open Scope Z_scope.
Lemma slot_offset_int64 i j : 0 <= i < 16 -> 0 <= j < 390 ->
 2 <= 2+i*390+j < 6242 /\ model.int64 (2+i*390+j).
Proof. unfold model.int64. nia. Qed.
Lemma slot_arithmetic_int64 i : 0 <= i < 16 ->
 model.int64 (i*390) /\ model.int64 (2+i*390).
Proof. unfold model.int64. nia. Qed.
Lemma metadata_copy_offset_int64 i n : 0 <= i < 16 -> 0 <= n <= 128 ->
 model.int64 (2+i*390+6+n) /\ model.int64 (2+i*390+134+n) /\
 model.int64 (2+i*390+262+n).
Proof. unfold model.int64. nia. Qed.
Lemma identifier_increment_int64 id : 1 <= id <= 9223372036854775806 ->
 1 < id+1 <= 9223372036854775807 /\ model.int64 (id+1).
Proof. unfold model.int64. lia. Qed.
Lemma enrollment_count_increment_int64 count : 0 <= count <= 15 ->
 1 <= count+1 <= 16 /\ model.int64 (count+1).
Proof. unfold model.int64. lia. Qed.
Lemma removal_count_decrement_int64 count : 1 <= count <= 16 ->
 0 <= count-1 <= 15 /\ model.int64 (count-1).
Proof. unfold model.int64. lia. Qed.
Lemma listing_counter_increment_int64 count : 0 <= count <= 15 ->
 model.int64 (count+1).
Proof. unfold model.int64. lia. Qed.
Lemma bounded_loop_increment_int64 i limit : 0 <= i < limit -> limit <= 6242 ->
 0 <= i+1 <= limit /\ model.int64 (i+1).
Proof. unfold model.int64. lia. Qed.
Lemma scan_slot_index_int64 words id :
 model.int64 (scan_identifiers words id 16).
Proof.
 pose proof (scan_identifiers_range words id 16). unfold model.int64. lia.
Qed.
Lemma vacant_slot_index_int64 words : model.int64 (first_free_slot words 16).
Proof.
 pose proof (first_free_slot_range words 16). unfold model.int64. lia.
Qed.
