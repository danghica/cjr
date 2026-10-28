(** Concrete SHA-1 round iteration and its five owned local state words. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory sha1_memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition rounds_state words count st :=
 fold_left model.sha_round (combine (seq 0 count) (take count words)) st.
Lemma combine_snoc_equal {A B} (xs : list A) (ys : list B) x y :
 length xs = length ys -> combine (xs ++ [x]) (ys ++ [y]) = combine xs ys ++ [(x,y)].
Proof.
 revert ys. induction xs as [|a xs IH]; intros [|b ys] Hlen; simpl in *; try discriminate.
 - reflexivity.
 - f_equal. apply IH. lia.
Qed.
Lemma rounds_state_zero words st : rounds_state words 0 st = st.
Proof. reflexivity. Qed.
Lemma rounds_state_step words i st : (i < length words)%nat ->
 rounds_state words (S i) st = model.sha_round (rounds_state words i st) (i, words !!! i).
Proof.
 intros Hi. unfold rounds_state. rewrite seq_S.
 rewrite (take_S_r words i (words !!! i) (list_lookup_lookup_total_lt words i Hi)).
 rewrite combine_snoc_equal; last (rewrite length_seq length_take Nat.min_l; lia).
 rewrite fold_left_app. simpl. done.
Qed.
Lemma rounds_state_length words count st : length st = 5%nat ->
 length (rounds_state words count st) = 5%nat.
Proof. intros Hlen. unfold rounds_state. apply model.fold_round_length. exact Hlen. Qed.
Lemma round_body_t_closed l : subst_var "t" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma message_words_length block : length (model.message_words block) = 16%nat.
Proof. unfold model.message_words. rewrite length_map length_seq. done. Qed.
Lemma schedule_length block :
 length (model.schedule_more 64 (model.message_words block)) = 80%nat.
Proof. rewrite schedule_more_length message_words_length. done. Qed.
Lemma compress_rounds st block :
 model.compress st block =
 map (fun xy => model.mask32 (fst xy+snd xy))
   (combine st (rounds_state (model.schedule_more 64 (model.message_words block)) 80 st)).
Proof.
 unfold model.compress, rounds_state. rewrite take_ge; last (rewrite schedule_length;lia).
 done.
Qed.
Lemma rounds_state_words words count st : Forall model.word st ->
 Forall model.word (rounds_state words count st).
Proof.
 intros Hst. unfold rounds_state. generalize (combine (seq 0 count) (take count words)) as rounds.
 intros rounds. revert st Hst. induction rounds as [|tw rounds IH]; intros st Hst; simpl.
 - exact Hst.
 - apply IH, model.sha_round_words. exact Hst.
Qed.
Lemma be_fold_bound xs acc : Forall model.byte xs -> 0 <= acc ->
 0 <= fold_left (fun a x => a*256+x) xs acc < (acc+1)*256^(Z.of_nat (length xs)).
Proof.
 intros Hxs. revert acc. induction Hxs as [|x xs Hx Hxs IH]; intros acc Hacc.
 - simpl. lia.
 - cbn [fold_left length]. unfold model.byte in Hx.
   assert (Hnext : 0 <= acc*256+x) by nia.
   specialize (IH _ Hnext). rewrite Nat2Z.inj_succ Z.pow_succ_r; last lia.
   assert (Hpow : 0 < 256^Z.of_nat (length xs)) by (apply Z.pow_pos_nonneg;lia).
   nia.
Qed.
Lemma be_word_four xs : length xs = 4%nat -> Forall model.byte xs -> model.word (model.be_word xs).
Proof.
 intros Hlen Hbytes. pose proof (be_fold_bound xs 0 Hbytes ltac:(lia)) as Hbound.
 rewrite Hlen in Hbound. unfold model.word, model.be_word. change (0 <= fold_left
   (fun a x => a*256+x) xs 0 < 4294967296). exact Hbound.
Qed.
Lemma message_words_words block : (64 <= length block)%nat -> Forall model.byte block ->
 Forall model.word (model.message_words block).
Proof.
 intros Hlen Hbytes. unfold model.message_words. apply Forall_forall.
 intros x Hx. apply elem_of_list_fmap in Hx as [i [-> Hi]].
 apply elem_of_seq in Hi. apply be_word_four.
 - change (length (take 4 (drop (4*i) block)) = 4%nat).
   rewrite length_take length_drop Nat.min_l; lia.
 - apply Forall_take, Forall_drop. exact Hbytes.
Qed.
Lemma schedule_more_words fuel ws : Forall model.word ws ->
 Forall model.word (model.schedule_more fuel ws).
Proof.
 revert ws. induction fuel as [|fuel IH]; intros ws Hws.
 - exact Hws.
 - rewrite schedule_more_left. apply IH. apply Forall_app. split; first exact Hws.
   constructor; last constructor. unfold schedule_next. apply model.rol32_word.
Qed.
Lemma schedule_words block : (64 <= length block)%nat -> Forall model.byte block ->
 Forall model.word (model.schedule_more 64 (model.message_words block)).
Proof. intros Hlen Hbytes. apply schedule_more_words, message_words_words; done. Qed.
