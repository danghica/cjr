(** Column/block views of the same caller-owned expanded-key buffer. *)
From Coq Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.aes_ige Require Import bytes block aes program memory expansion routines key_layout.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Definition columns_block cs i := Block
 (nth (4*i) cs (Col 0 0 0 0)) (nth (4*i+1) cs (Col 0 0 0 0))
 (nth (4*i+2) cs (Col 0 0 0 0)) (nth (4*i+3) cs (Col 0 0 0 0)).
Definition column_schedule cs count := map (columns_block cs) (seq 0 count).
Lemma read_block_columns cs i : Forall column_bytes cs -> (4*i+3 < length cs)%nat ->
 read_block (flatten_cols cs) (16*i) = columns_block cs i.
Proof.
 intros Hb Hlen. unfold read_block, columns_block.
 replace (16*i)%nat with (4*(4*i))%nat by lia.
 replace (4*(4*i)+4)%nat with (4*(4*i+1))%nat by lia.
 replace (4*(4*i)+8)%nat with (4*(4*i+2))%nat by lia.
 replace (4*(4*i)+12)%nat with (4*(4*i+3))%nat by lia.
 repeat rewrite read_col_flatten; try assumption; try lia. reflexivity.
Qed.
Lemma column_schedule_model keys nk nr :
 (nk=4 /\ nr=10 \/ nk=6 /\ nr=12 \/ nk=8 /\ nr=14)%nat ->
 length keys = nk -> Forall column_bytes keys ->
 key_schedule (flatten_cols keys) = column_schedule (expand_words (4*(nr+1)-nk) nk nk keys) (nr+1).
Proof.
 intros Hsizes Hlen Hb. unfold key_schedule, column_schedule.
 rewrite (expanded_key_columns keys nk nr Hb Hlen Hsizes).
 assert (Hnr : rounds_of_length (length (flatten_cols keys)) = nr).
 { unfold flatten_cols. rewrite flatten_words_length Hlen.
   destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; reflexivity. }
 rewrite Hnr. replace (S nr) with (nr+1)%nat by lia.
 apply map_ext_in. intros i Hi. apply in_seq in Hi. apply read_block_columns.
 - apply expand_words_bytes; assumption.
 - rewrite expand_words_length Hlen. destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; lia.
Qed.
Lemma column_schedule_four a b c d rest count :
 column_schedule (a::b::c::d::rest) (S count) = Block a b c d :: column_schedule rest count.
Proof.
 unfold column_schedule. simpl seq. simpl List.map.
 change (Block a b c d :: map (columns_block (a::b::c::d::rest)) (seq (S 0) count) =
         Block a b c d :: map (columns_block rest) (seq 0 count)).
 rewrite <- seq_shift. rewrite map_map. f_equal. apply map_ext. intros i. unfold columns_block.
 replace (4*S i)%nat with (S (S (S (S (4*i))))) by lia.
 replace (S (S (S (S (4*i))))+1)%nat with (S (S (S (S (4*i+1))))) by lia.
 replace (S (S (S (S (4*i))))+2)%nat with (S (S (S (S (4*i+2))))) by lia.
 replace (S (S (S (S (4*i))))+3)%nat with (S (S (S (S (4*i+3))))) by lia.
 reflexivity.
Qed.
Section ownership.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma words_at_cons p c cs : words_at p (c::cs) ⊣⊢ col_at p c ∗ words_at (p+4) cs.
Proof.
 unfold words_at. rewrite big_sepL_cons. cbn [Z.of_nat Z.mul]. rewrite Z.add_0_r.
 f_equiv. apply big_sepL_proper. intros i v Hi.
 replace (p+4*Z.of_nat (S i)) with (p+4+4*Z.of_nat i) by lia. reflexivity.
Qed.
Lemma words_at_app p cs ds : words_at p (cs++ds) ⊣⊢
 words_at p cs ∗ words_at (p+4*Z.of_nat (length cs)) ds.
Proof.
 unfold words_at. rewrite big_sepL_app. f_equiv. apply big_sepL_proper. intros i v Hi.
 replace (p+4*Z.of_nat (length cs+i)) with (p+4*Z.of_nat (length cs)+4*Z.of_nat i) by lia. reflexivity.
Qed.
Lemma words_at_four p a b c d rest : words_at p (a::b::c::d::rest) ⊣⊢
 block_at p (Block a b c d) ∗ words_at (p+16) rest.
Proof.
 rewrite !words_at_cons. unfold col_at, block_at. simpl.
 rewrite <- !Z.add_assoc. simpl. rewrite ?Z.add_0_r.
 iSplit.
 - iIntros "((? & ? & ? & ?) & (? & ? & ? & ?) & (? & ? & ? & ?) & (? & ? & ? & ?) & ?)". iFrame.
 - iIntros "((? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?) & ?)". iFrame.

Qed.
Lemma schedule_at_cons p b bs : schedule_at p (b::bs) ⊣⊢ block_at p b ∗ schedule_at (p+16) bs.
Proof.
 unfold schedule_at. rewrite big_sepL_cons. cbn [Z.of_nat Z.mul]. rewrite Z.add_0_r.
 f_equiv. apply big_sepL_proper. intros i v Hi.
 replace (p+16*Z.of_nat (S i)) with (p+16+16*Z.of_nat i) by lia. reflexivity.
Qed.
Lemma words_at_schedule p cs count : length cs = (4*count)%nat ->
 words_at p cs ⊣⊢ schedule_at p (column_schedule cs count).
Proof.
 revert p cs. induction count as [|count IH]; intros p cs Hlen.
 - destruct cs; [|simpl in Hlen; lia]. unfold words_at, schedule_at, column_schedule. simpl. reflexivity.
 - destruct cs as [|a cs]; [simpl in Hlen; lia|].
   destruct cs as [|b cs]; [simpl in Hlen; lia|].
   destruct cs as [|c cs]; [simpl in Hlen; lia|].
   destruct cs as [|d cs]; [simpl in Hlen; lia|].
   rewrite words_at_four column_schedule_four schedule_at_cons. f_equiv. apply IH. simpl in Hlen; lia.
Qed.
Theorem key_expansion_schedule_wp p q keys old nk nr :
 (nk=4 /\ nr=10 \/ nk=6 /\ nr=12 \/ nk=8 /\ nr=14)%nat ->
 length keys = nk -> Forall column_bytes keys -> length old = 60%nat ->
 words_at p keys -∗ words_at q old -∗
 WP invoke expand_body [eptr p;program.int (Z.of_nat (4*nk));eptr q]
 {{result, ⌜result = LitV (LitInt (Z.of_nat nr))⌝ ∗ words_at p keys ∗
 schedule_at q (key_schedule (flatten_cols keys)) ∗
 words_at (q+16*Z.of_nat (nr+1)) (skipn (4*(nr+1)) old)}}.
Proof.
 intros Hsizes Hlen Hb Hold. iIntros "Hkeys Hmem".
 iApply (wp_wand with "[Hkeys Hmem]").
 { iApply (expand_key_wp p q keys old nk nr with "Hkeys Hmem"); assumption. }
 iIntros (result) "(%E & Hkeys & Hmem)".
 iEval (rewrite words_at_app) in "Hmem". iDestruct "Hmem" as "[Hschedule Htail]".
 assert (Hexpanded : length (expand_words (4*(nr+1)-nk) nk nk keys) = (4*(nr+1))%nat).
 { rewrite expand_words_length Hlen. destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; reflexivity. }
 iEval (rewrite Hexpanded) in "Htail".
 iEval (rewrite (words_at_schedule q _ (nr+1) Hexpanded)) in "Hschedule".
 rewrite (column_schedule_model keys nk nr Hsizes Hlen Hb).
 replace (q+4*Z.of_nat (4*(nr+1))) with (q+16*Z.of_nat (nr+1)) by lia.
 iFrame. done.
Qed.
Theorem expand_supported_key_wp p q key old : valid_key key -> length old = 60%nat ->
 words_at p (key_columns key) -∗ words_at q old -∗
 WP invoke expand_body [eptr p;program.int (Z.of_nat (length key));eptr q]
 {{result, ⌜result = LitV (LitInt (Z.of_nat (rounds_of_length (length key))))⌝ ∗
 words_at p (key_columns key) ∗ schedule_at q (key_schedule key) ∗
 words_at (q+16*Z.of_nat (rounds_of_length (length key)+1))
  (skipn (4*(rounds_of_length (length key)+1)) old)}}.
Proof.
 intros Hkey Hold. destruct (valid_key_columns key Hkey) as [Hlen [Hb Hflat]].
 assert (Hsizes : (nk_of_length (length key)=4 /\ rounds_of_length (length key)=10 \/
 nk_of_length (length key)=6 /\ rounds_of_length (length key)=12 \/
 nk_of_length (length key)=8 /\ rounds_of_length (length key)=14)%nat).
 { destruct Hkey as [Hkey _]. destruct Hkey as [Hkey|[Hkey|Hkey]]; rewrite Hkey; simpl; auto. }
 assert (Hkeylen : (4*nk_of_length (length key))%nat = length key).
 { destruct Hkey as [Hkey _]. destruct Hkey as [Hkey|[Hkey|Hkey]]; rewrite Hkey; reflexivity. }
 iIntros "Hkey Hmem".
 iPoseProof (key_expansion_schedule_wp p q (key_columns key) old
  (nk_of_length (length key)) (rounds_of_length (length key)) Hsizes Hlen Hb Hold
  with "Hkey Hmem") as "Hcall".
 iEval (rewrite Hkeylen Hflat) in "Hcall". iExact "Hcall".
Qed.
End ownership.
