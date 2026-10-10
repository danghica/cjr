(** All arithmetic performed by the implementation fits signed Int64. *)
From Coq Require Import ZArith Lia.
From cjr.quadtree.spec Require Import model.
Local Open Scope Z_scope.
Definition int64 (z : Z) := -9223372036854775808 <= z <= 9223372036854775807.
Definition box_bounds b := 0 <= xmin b <= xmax b /\ xmax b <= 1073741824 /\
  0 <= ymin b <= ymax b /\ ymax b <= 1073741824.
Lemma domain_bounds d : (d <= 30)%nat -> box_bounds (domain d).
Proof. intros Hd. pose proof (width_bound d Hd). pose proof (width_positive d). unfold box_bounds, domain; simpl; lia. Qed.
Lemma stored_bounds_int64 b : box_bounds b ->
  int64 (xmin b) /\ int64 (ymin b) /\ int64 (xmax b) /\ int64 (ymax b).
Proof. unfold box_bounds, int64; intuition lia. Qed.
Lemma midpoint_bounds d b : square (S d) b -> box_bounds b ->
  xmin b <= midx d b <= xmax b /\ ymin b <= midy d b <= ymax b.
Proof.
  unfold square, box_bounds, midx, midy. rewrite width_succ.
  pose proof (width_positive d). intuition lia.
Qed.
Lemma midpoint_int64 d b : square (S d) b -> box_bounds b ->
  int64 (xmin b + width d) /\ int64 (ymin b + width d).
Proof.
  intros Hs Hb. pose proof (midpoint_bounds d b Hs Hb).
  unfold box_bounds, int64, midx, midy in *. intuition lia.
Qed.
Lemma child_bounds d b k : square (S d) b -> box_bounds b -> box_bounds (child_box d b k).
Proof.
  intros Hs Hb. pose proof (midpoint_bounds d b Hs Hb).
  destruct k; unfold child_box, box_bounds in *; simpl; intuition lia.
Qed.
Lemma doubling_int64 d : (d < 30)%nat -> int64 (width d + width d).
Proof.
  intros Hd. pose proof (width_bound (S d) ltac:(lia)). pose proof (width_positive d).
  rewrite width_succ in *. unfold int64; lia.
Qed.
Lemma power_result_int64 d : (d <= 30)%nat -> int64 (width d).
Proof. intros Hd. pose proof (width_bound d Hd). pose proof (width_positive d). unfold int64; lia. Qed.
Lemma decrement_int64 d : (d < 30)%nat -> int64 (Z.of_nat (S d) - 1) /\ Z.of_nat (S d) - 1 = Z.of_nat d.
Proof. intros Hd. rewrite Nat2Z.inj_succ. unfold int64. split; lia. Qed.
Lemma leaf_coordinates_int64 b p : box_bounds b -> in_rect b p -> int64 (fst p) /\ int64 (snd p).
Proof. unfold box_bounds, in_rect, int64; intuition lia. Qed.
Fixpoint all_bounds d b t {struct t} := box_bounds b /\ match t with
  Branch ll lr ul ur => match d with 0%nat=>False | S h=>
    all_bounds h (child_box h b LL) ll /\ all_bounds h (child_box h b LR) lr /\
    all_bounds h (child_box h b UL) ul /\ all_bounds h (child_box h b UR) ur end
  | _=>True end.
Lemma valid_all_bounds d b t : square d b -> box_bounds b -> valid d b t -> all_bounds d b t.
Proof.
  revert d b. induction t; intros d b Hs Hb Hv; simpl; try tauto.
  destruct d; first contradiction. destruct Hv as [H1 [H2 [H3 H4]]].
  split; first assumption.
  split; first exact (IHt1 d _ (child_square d b LL Hs) (child_bounds d b LL Hs Hb) H1).
  split; first exact (IHt2 d _ (child_square d b LR Hs) (child_bounds d b LR Hs Hb) H2).
  split; [exact (IHt3 d _ (child_square d b UL Hs) (child_bounds d b UL Hs Hb) H3)|exact (IHt4 d _ (child_square d b UR Hs) (child_bounds d b UR Hs Hb) H4)].
Qed.
Lemma root_all_bounds d t : (d <= 30)%nat -> valid d (domain d) t -> all_bounds d (domain d) t.
Proof. intros Hd Hv. apply valid_all_bounds; eauto using root_square, domain_bounds. Qed.
