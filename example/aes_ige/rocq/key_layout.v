(** Every supported byte key has the column representation used by expansion. *)
From Coq Require Import ZArith List Lia.
From cjr.aes_ige Require Import bytes block aes expansion.
Import ListNotations.
Fixpoint key_columns xs := match xs with
 | a::b::c::d::rest => Col a b c d :: key_columns rest
 | _ => [] end.
Lemma key_columns_layout count xs : length xs = (4*count)%nat ->
 length (key_columns xs) = count /\ flatten_cols (key_columns xs) = xs.
Proof.
 revert xs. induction count as [|count IH]; intros xs Hlen.
 - destruct xs; [simpl; auto|simpl in Hlen; lia].
 - destruct xs as [|a xs]; [simpl in Hlen; lia|].
   destruct xs as [|b xs]; [simpl in Hlen; lia|].
   destruct xs as [|c xs]; [simpl in Hlen; lia|].
   destruct xs as [|d xs]; [simpl in Hlen; lia|].
   specialize (IH xs ltac:(simpl in Hlen; lia)). destruct IH as [IHlen IHflat].
   split; [simpl; lia|]. change (a::b::c::d::flatten_cols (key_columns xs) = a::b::c::d::xs).
   rewrite IHflat. reflexivity.
Qed.
Lemma key_columns_bytes xs : Forall byte xs -> Forall column_bytes (key_columns xs).
Proof.
 revert xs. fix IH 1. intros xs H.
 destruct xs as [|a xs]; [constructor|].
 destruct xs as [|b xs]; [constructor|].
 destruct xs as [|c xs]; [constructor|].
 destruct xs as [|d xs]; [constructor|].
 repeat match goal with H : Forall _ (_::_) |- _ => inversion H; subst; clear H end.
 constructor; [unfold column_bytes; simpl; tauto|apply IH; assumption].
Qed.
Theorem valid_key_columns key : valid_key key ->
 length (key_columns key) = nk_of_length (length key) /\
 Forall column_bytes (key_columns key) /\ flatten_cols (key_columns key) = key.
Proof.
 intros [Hlen Hb]. assert (Hcolumns := key_columns_bytes key Hb).
 destruct Hlen as [Hlen|[Hlen|Hlen]].
 - destruct (key_columns_layout 4 key ltac:(lia)) as [Hn Hflat]. rewrite Hlen. simpl. auto.
 - destruct (key_columns_layout 6 key ltac:(lia)) as [Hn Hflat]. rewrite Hlen. simpl. auto.
 - destruct (key_columns_layout 8 key ltac:(lia)) as [Hn Hflat]. rewrite Hlen. simpl. auto.
Qed.
