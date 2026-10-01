(** Most frequent integer of an initialized array. The concrete algorithm
    sorts (value, original-index) records, then reduces each equal-value run.
    The mathematical interface is over unbounded integers and lists. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import list.
From iris.prelude Require Import options.
Import ListNotations.

Definition mf_pair := (Z * nat)%type.

Definition pair_before (p q : mf_pair) : Prop :=
  (fst p < fst q)%Z \/ (fst p = fst q /\ (snd p <= snd q)%nat).

Fixpoint mf_pairs (xs : list Z) (i : nat) : list mf_pair :=
  match xs with
  | [] => []
  | x :: xs' => (x, i) :: mf_pairs xs' (S i)
  end.

Definition mf_frequency (x : Z) (xs : list Z) : nat :=
  count_occ Z.eq_dec xs x.

Fixpoint mf_first_index (x : Z) (xs : list Z) : option nat :=
  match xs with
  | [] => None
  | y :: ys => if Z.eq_dec x y then Some 0%nat else option_map S (mf_first_index x ys)
  end.

Definition mf_first_index_or_len (x : Z) (xs : list Z) : nat :=
  match mf_first_index x xs with Some i => i | None => length xs end.

Definition most_frequent_spec (xs : list Z) (answer : option Z) : Prop :=
  match xs, answer with
  | [], None => True
  | [], Some _ => False
  | _ :: _, None => False
  | _ :: _, Some x =>
      (mf_frequency x xs > 0)%nat /\
      (forall y, mf_frequency y xs <= mf_frequency x xs)%nat /\
      (forall y, mf_frequency y xs = mf_frequency x xs ->
         mf_first_index_or_len x xs <= mf_first_index_or_len y xs)%nat
  end.

Lemma most_frequent_empty : most_frequent_spec [] None.
Proof. done. Qed.

Lemma mf_first_index_head x xs :
  mf_first_index x (x :: xs) = Some 0%nat.
Proof. simpl. destruct (Z.eq_dec x x); congruence. Qed.

Lemma mf_first_index_or_len_head x xs :
  mf_first_index_or_len x (x :: xs) = 0%nat.
Proof. unfold mf_first_index_or_len. rewrite mf_first_index_head. done. Qed.

Lemma mf_first_index_or_len_skip a x xs :
  x <> a ->
  mf_first_index_or_len x (a :: xs) = S (mf_first_index_or_len x xs).
Proof.
  intros Hneq. unfold mf_first_index_or_len. simpl.
  destruct (Z.eq_dec x a); [congruence|].
  destruct (mf_first_index x xs); simpl; done.
Qed.

Lemma mf_frequency_head x xs :
  mf_frequency x (x :: xs) = S (mf_frequency x xs).
Proof. unfold mf_frequency. simpl. destruct (Z.eq_dec x x); congruence. Qed.

(** A pure executable selector used as an independent Gallina oracle: it
    considers candidates in input order, retaining the earlier candidate on
    equal frequencies. The CJR implementation is intended to perform the same choice
    after sorting value/index pairs. *)
Fixpoint mf_choose (xs candidates : list Z) : option Z :=
  match candidates with
  | [] => None
  | x :: rest =>
      match mf_choose xs rest with
      | None => Some x
      | Some y =>
          if Nat.leb (mf_frequency y xs) (mf_frequency x xs)
          then Some x else Some y
      end
  end.

Lemma mf_choose_none xs candidates :
  mf_choose xs candidates = None <-> candidates = [].
Proof.
  induction candidates as [|x rest IH]; simpl; [done|].
  destruct (mf_choose xs rest); simpl; [|done].
  destruct (Nat.leb (mf_frequency z xs) (mf_frequency x xs)); done.
Qed.

Lemma mf_choose_sound xs candidates :
  match mf_choose xs candidates with
  | None => candidates = []
  | Some x => In x candidates /\
      (forall y, In y candidates -> mf_frequency y xs <= mf_frequency x xs)%nat /\
      (forall y, In y candidates -> mf_frequency y xs = mf_frequency x xs ->
        mf_first_index_or_len x candidates <= mf_first_index_or_len y candidates)%nat
  end.
Proof.
  induction candidates as [|a rest IH]; simpl; [done|].
  destruct (mf_choose xs rest) as [b|] eqn:Hrest.
  - destruct (Nat.leb (mf_frequency b xs) (mf_frequency a xs)) eqn:Hcmp.
    + destruct IH as [_ [Hmax _]].
      split.
      * by left.
      * split.
        -- intros y [->|Hy].
           ++ lia.
           ++ specialize (Hmax y Hy). apply Nat.leb_le in Hcmp. lia.
        -- intros y _ _. rewrite mf_first_index_or_len_head. lia.
    + destruct IH as [Hin [Hmax Hfirst]].
      split; [by right|]. split.
      * intros y [->|Hy]; [apply Nat.leb_gt in Hcmp; lia|by apply Hmax].
      * intros y [->|Hy] Hfreq; [apply Nat.leb_gt in Hcmp; lia|].
        rewrite !mf_first_index_or_len_skip; last first.
        { intro Heq. subst b. apply Nat.leb_gt in Hcmp. lia. }
        { intro Heq. subst y. apply Nat.leb_gt in Hcmp. lia. }
        pose proof (Hfirst y Hy Hfreq) as Hidx. lia.
  -
    apply mf_choose_none in Hrest. subst rest.
    split; [by left|]. split.
    + intros y [->|[]]; lia.
    + intros y [->|[]] _. rewrite !mf_first_index_or_len_head. done.
Qed.

Lemma mf_frequency_pos_mem x xs :
  (0 < mf_frequency x xs)%nat -> In x xs.
Proof.
  unfold mf_frequency. intros Hpos.
  apply (proj2 (count_occ_In Z.eq_dec xs x)). exact Hpos.
Qed.

Lemma mf_frequency_not_mem x xs :
  ~ In x xs -> mf_frequency x xs = 0%nat.
Proof.
  unfold mf_frequency. intros Hnot.
  apply (proj1 (count_occ_not_In Z.eq_dec xs x)). exact Hnot.
Qed.

Theorem mf_choose_correct xs : most_frequent_spec xs (mf_choose xs xs).
Proof.
  destruct xs as [|x xs']; [simpl; exact most_frequent_empty|].
  pose proof (mf_choose_sound (x :: xs') (x :: xs')) as Hsound.
  destruct (mf_choose (x :: xs') (x :: xs')) as [best|] eqn:Hbest; [|].
  - simpl in Hsound.
    change ((mf_frequency best (x :: xs') > 0)%nat /\
      (forall y, (mf_frequency y (x :: xs') <= mf_frequency best (x :: xs'))%nat) /\
      (forall y, mf_frequency y (x :: xs') = mf_frequency best (x :: xs') ->
        mf_first_index_or_len best (x :: xs') <= mf_first_index_or_len y (x :: xs'))).
    change (In best (x :: xs') /\
      (forall y, In y (x :: xs') -> mf_frequency y (x :: xs') <= mf_frequency best (x :: xs'))%nat /\
      (forall y, In y (x :: xs') -> mf_frequency y (x :: xs') = mf_frequency best (x :: xs') ->
        mf_first_index_or_len best (x :: xs') <= mf_first_index_or_len y (x :: xs'))%nat) in Hsound.
    destruct Hsound as [Hin [Hmax Hfirst]].
    assert (0 < mf_frequency best (x :: xs'))%nat as Hpos.
    { unfold mf_frequency. apply (proj1 (count_occ_In Z.eq_dec (x :: xs') best)). exact Hin. }
    split.
    + exact Hpos.
    + split.
      * intros y. destruct (in_dec Z.eq_dec y (x :: xs')) as [Hy|Hnot].
        -- by apply Hmax.
        -- pose proof (mf_frequency_not_mem y (x :: xs') Hnot) as Hy0. lia.
      * intros y Heq.
        assert (Hy : In y (x :: xs')).
        { apply mf_frequency_pos_mem. rewrite Heq. exact Hpos. }
        apply Hfirst; [exact Hy|exact Heq].
  - apply mf_choose_none in Hbest. discriminate.
Qed.

(** * Concrete CJR terms
    Parallel arrays implement records; every swap moves both fields.
    The group-loop guard uses If because CJR AndOp is eager. *)
From Coq Require Import String.
From cjr Require Import lang.
From cjr.examples Require Import array.
Local Open Scope string_scope.

Definition mf_swap_body : expr :=
 (Let (Some "values") (StructLoad (Var "args") 0)
 (Let (Some "indices") (StructLoad (Var "args") 1)
 (Let (Some "i") (StructLoad (Var "args") 2)
 (Let (Some "j") (StructLoad (Var "args") 3)
 (Let (Some "x") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Var "i")]))
 (Let (Some "xi") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (Var "i")]))
 (Let (Some "y") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Var "j")]))
 (Let (Some "yi") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (Var "j")]))
 (Let None (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "values"); (Var "i"); (Var "y")]))
 (Let None (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "indices"); (Var "i"); (Var "yi")]))
 (Let None (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "values"); (Var "j"); (Var "x")]))
 (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "indices"); (Var "j"); (Var "xi")]))))))))))))).

Definition mf_partition_body : expr :=
 (Let (Some "values") (StructLoad (Var "args") 0)
 (Let (Some "indices") (StructLoad (Var "args") 1)
 (Let (Some "lo") (StructLoad (Var "args") 2)
 (Let (Some "hi") (StructLoad (Var "args") 3)
 (Let (Some "pv") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (BinOp MinusOp (Var "hi") (Val (LitV (LitInt 1))))]))
 (Let (Some "pi") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (BinOp MinusOp (Var "hi") (Val (LitV (LitInt 1))))]))
 (VarBind "i" (Var "lo")
 (VarBind "j" (Var "lo")
 (Let None (While (BinOp LeOp (BinOp PlusOp (Var "j") (Val (LitV (LitInt 1)))) (BinOp MinusOp (Var "hi") (Val (LitV (LitInt 1)))))
 (Let (Some "v") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Var "j")]))
 (Let (Some "ix") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (Var "j")]))
 (Let None (If (If (BinOp LeOp (Var "v") (Var "pv"))
 (If (BinOp LeOp (Var "pv") (Var "v"))
 (BinOp LeOp (Var "ix") (Var "pi"))
 (Val (LitV (LitBool true))))
 (Val (LitV (LitBool false))))
 (Let None (App (Rec None (Some "args") mf_swap_body) (Struct [] [(Var "values"); (Var "indices"); (Var "i"); (Var "j")]))
 (Assign "i" (BinOp PlusOp (Var "i") (Val (LitV (LitInt 1))))))
 (Val (LitV LitUnit)))
 (Assign "j" (BinOp PlusOp (Var "j") (Val (LitV (LitInt 1)))))))))
 (Let None (App (Rec None (Some "args") mf_swap_body) (Struct [] [(Var "values"); (Var "indices"); (Var "i"); (BinOp MinusOp (Var "hi") (Val (LitV (LitInt 1))))]))
 (Var "i"))))))))))).

Definition mf_qsort_body : expr :=
 (Let (Some "values") (StructLoad (Var "args") 0)
 (Let (Some "indices") (StructLoad (Var "args") 1)
 (Let (Some "lo") (StructLoad (Var "args") 2)
 (Let (Some "hi") (StructLoad (Var "args") 3)
 (If (BinOp LeOp (BinOp PlusOp (Var "lo") (Val (LitV (LitInt 1)))) (BinOp MinusOp (Var "hi") (Val (LitV (LitInt 1)))))
 (Let (Some "p") (App (Rec None (Some "args") mf_partition_body) (Struct [] [(Var "values"); (Var "indices"); (Var "lo"); (Var "hi")]))
 (Let None (App (Var "pairQsort") (Struct [] [(Var "values"); (Var "indices"); (Var "lo"); (Var "p")]))
 (App (Var "pairQsort") (Struct [] [(Var "values"); (Var "indices"); (BinOp PlusOp (Var "p") (Val (LitV (LitInt 1)))); (Var "hi")]))))
 (Val (LitV LitUnit))))))).

Definition mf_body : expr :=
 (Let (Some "n") (App (Rec None (Some "a") array.length_body) (Var "input"))
 (If (BinOp EqOp (Var "n") (Val (LitV (LitInt 0))))
 (Struct [] [(Val (LitV (LitBool false))); (Val (LitV (LitInt 0)))])
 (Let (Some "values") (App (Rec None (Some "n") array.make_body) (Var "n"))
 (Let (Some "indices") (App (Rec None (Some "n") array.make_body) (Var "n"))
 (Let None (VarBind "copyAt" (Val (LitV (LitInt 0)))
 (While (BinOp LeOp (BinOp PlusOp (Var "copyAt") (Val (LitV (LitInt 1)))) (Var "n"))
 (Let None (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "values"); (Var "copyAt"); (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "input"); (Var "copyAt")]))]))
 (Let None (App (Rec None (Some "args") array.set_body) (Struct [] [(Var "indices"); (Var "copyAt"); (Var "copyAt")]))
 (Assign "copyAt" (BinOp PlusOp (Var "copyAt") (Val (LitV (LitInt 1)))))))))
 (Let None (App (Rec (Some "pairQsort") (Some "args") mf_qsort_body) (Struct [] [(Var "values"); (Var "indices"); (Val (LitV (LitInt 0))); (Var "n")]))
 (VarBind "bestValue" (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Val (LitV (LitInt 0)))]))
 (VarBind "bestCount" (Val (LitV (LitInt 0)))
 (VarBind "bestFirst" (Var "n")
 (VarBind "start" (Val (LitV (LitInt 0)))
 (Let None (While (BinOp LeOp (BinOp PlusOp (Var "start") (Val (LitV (LitInt 1)))) (Var "n"))
 (Let (Some "value") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Var "start")]))
 (VarBind "end" (BinOp PlusOp (Var "start") (Val (LitV (LitInt 1))))
 (VarBind "first" (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (Var "start")]))
 (Let None (While (If (BinOp LeOp (BinOp PlusOp (Var "end") (Val (LitV (LitInt 1)))) (Var "n"))
 (BinOp EqOp (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "values"); (Var "end")])) (Var "value"))
 (Val (LitV (LitBool false))))
 (Let (Some "ix") (App (Rec None (Some "args") array.get_body) (Struct [] [(Var "indices"); (Var "end")]))
 (Let None (If (BinOp LeOp (BinOp PlusOp (Var "ix") (Val (LitV (LitInt 1)))) (Var "first"))
 (Assign "first" (Var "ix"))
 (Val (LitV LitUnit)))
 (Assign "end" (BinOp PlusOp (Var "end") (Val (LitV (LitInt 1))))))))
 (Let (Some "count") (BinOp MinusOp (Var "end") (Var "start"))
 (Let None (If (If (BinOp LeOp (BinOp PlusOp (Var "bestCount") (Val (LitV (LitInt 1)))) (Var "count"))
 (Val (LitV (LitBool true)))
 (If (BinOp EqOp (Var "bestCount") (Var "count"))
 (BinOp LeOp (BinOp PlusOp (Var "first") (Val (LitV (LitInt 1)))) (Var "bestFirst"))
 (Val (LitV (LitBool false)))))
 (Let None (Assign "bestValue" (Var "value"))
 (Let None (Assign "bestCount" (Var "count"))
 (Assign "bestFirst" (Var "first"))))
 (Val (LitV LitUnit)))
 (Assign "start" (Var "end")))))))))
 (Let None (Free (FieldLoad (Var "values") 1))
 (Let None (Free (FieldLoad (Var "indices") 1))
 (Struct [] [(Val (LitV (LitBool true))); (Var "bestValue")])))))))))))))).

(** * Paired Lomuto model
    These definitions follow the existing scalar Lomuto algorithm, swapping
    whole records rather than only their values. *)
From cjr.examples Require Import qsort.
From stdpp Require Import list_monad.

Definition mf_pair_leb (p q : mf_pair) : bool :=
  if Z.leb (fst p) (fst q) then
    if Z.leb (fst q) (fst p) then Nat.leb (snd p) (snd q) else true
  else false.

Lemma mf_pair_leb_spec p q : mf_pair_leb p q = true <-> pair_before p q.
Proof.
  destruct p as [x i], q as [y j]. unfold mf_pair_leb, pair_before; simpl.
  destruct (Z.leb x y) eqn:Hxy; destruct (Z.leb y x) eqn:Hyx;
    try apply Z.leb_le in Hxy; try apply Z.leb_gt in Hxy;
    try apply Z.leb_le in Hyx; try apply Z.leb_gt in Hyx;
    try (split; intros; lia).
  rewrite Nat.leb_le. split; intros; intuition lia.
Qed.

Definition mf_pair_swap (xs : list mf_pair) (i j : nat) : list mf_pair :=
  match xs !! i, xs !! j with
  | Some x, Some y => <[i := y]> (<[j := x]> xs)
  | _, _ => xs
  end.

Definition mf_pair_eq_dec (p q : mf_pair) : {p = q} + {p <> q} := decide (p = q).
Opaque mf_pair_eq_dec.

Lemma mf_count_insert (xs : list mf_pair) i y x z :
  xs !! i = Some y ->
  count_occ (mf_pair_eq_dec) (<[i:=x]> xs) z + (if mf_pair_eq_dec z y then 1 else 0)
    = count_occ (mf_pair_eq_dec) xs z + (if mf_pair_eq_dec z x then 1 else 0).
Proof.
  revert i. induction xs as [|h xs IH]; intros [|i] Hi; simplify_eq/=.
  - destruct (mf_pair_eq_dec z y), (mf_pair_eq_dec z x), (mf_pair_eq_dec y z), (mf_pair_eq_dec x z);
      simpl; try congruence; lia.
  - destruct (mf_pair_eq_dec h z), (mf_pair_eq_dec z h); simpl;
      rewrite (IH i Hi); reflexivity.
Qed.

Lemma mf_pair_swap_perm xs i j : mf_pair_swap xs i j ≡ₚ xs.
Proof.
  unfold mf_pair_swap. destruct (xs !! i) as [x|] eqn:Hi; [|done].
  destruct (xs !! j) as [y|] eqn:Hj; [|done].
  destruct (decide (i = j)) as [->|Hne].
  { assert (x = y) as -> by congruence. rewrite list_insert_insert list_insert_id; done. }
  apply (Permutation_count_occ mf_pair_eq_dec). intros z.
  assert ((<[j:=x]> xs) !! i = Some x) as Hi1.
  { rewrite list_lookup_insert_ne; done. }
  pose proof (mf_count_insert xs j y x z Hj).
  pose proof (mf_count_insert (<[j:=x]> xs) i x y z Hi1). lia.
Qed.

Fixpoint mf_lomuto (fuel : nat) (xs : list mf_pair) (pivot : mf_pair)
    (i j bound : nat) : list mf_pair * nat :=
  match fuel with
  | O => (xs, i)
  | S fuel =>
    if Nat.ltb j bound then
      match xs !! j with
      | Some v => if mf_pair_leb v pivot then
          mf_lomuto fuel (mf_pair_swap xs i j) pivot (S i) (S j) bound
        else mf_lomuto fuel xs pivot i (S j) bound
      | None => (xs, i)
      end
    else (xs, i)
  end.

Lemma mf_lomuto_perm fuel xs pivot i j bound :
  fst (mf_lomuto fuel xs pivot i j bound) ≡ₚ xs.
Proof.
  revert xs i j. induction fuel as [|fuel IH]; intros xs i j; simpl; [done|].
  destruct (Nat.ltb j bound); [|done]. destruct (xs !! j); [|done].
  destruct (mf_pair_leb m pivot); [|apply IH].
  etrans; [apply IH|apply mf_pair_swap_perm].
Qed.

Definition mf_partition (xs : list mf_pair) (lo hi : nat) : list mf_pair * nat :=
  match xs !! (hi - 1)%nat with
  | Some pivot =>
      let '(ys, p) := mf_lomuto ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat in
      (mf_pair_swap ys p (hi - 1)%nat, p)
  | None => (xs, lo)
  end.

Lemma mf_partition_perm xs lo hi : fst (mf_partition xs lo hi) ≡ₚ xs.
Proof.
  unfold mf_partition. destruct (xs !! (hi - 1)%nat) as [pivot|]; [|done].
  pose proof (mf_lomuto_perm ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat) as H.
  destruct (mf_lomuto ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat) as [ys p].
  simpl in *. etrans; [apply mf_pair_swap_perm|exact H].
Qed.

Fixpoint mf_qsort_slice (fuel : nat) (xs : list mf_pair) (lo hi : nat) : list mf_pair :=
  match fuel with
  | O => xs
  | S fuel => if Nat.leb hi (lo + 1)%nat then xs else
      let '(ys, p) := mf_partition xs lo hi in
      mf_qsort_slice fuel (mf_qsort_slice fuel ys lo p) (S p) hi
  end.
Definition mf_qsort (xs : list mf_pair) := mf_qsort_slice (length xs) xs 0%nat (length xs).

Lemma mf_qsort_slice_perm fuel xs lo hi : mf_qsort_slice fuel xs lo hi ≡ₚ xs.
Proof.
  revert xs lo hi. induction fuel as [|fuel IH]; intros xs lo hi; simpl; [done|].
  destruct (Nat.leb hi (lo + 1)%nat); [done|].
  pose proof (mf_partition_perm xs lo hi) as H.
  destruct (mf_partition xs lo hi) as [ys p]. simpl in H.
  etrans; [apply IH|]. etrans; [apply IH|exact H].
Qed.

Theorem mf_qsort_perm xs : mf_qsort xs ≡ₚ xs.
Proof. apply mf_qsort_slice_perm. Qed.

(** A mathematical encoding transports the scalar quicksort theorem to the
    lexicographic order. This encoding is proof-only: generated Int64 code
    compares fields directly and never multiplies input values by a width. *)
Definition mf_bounded (width : nat) (xs : list mf_pair) :=
  forall p, In p xs -> (snd p < width)%nat.
Definition mf_rank (width : nat) (p : mf_pair) : Z :=
  (fst p * Z.of_nat width + Z.of_nat (snd p))%Z.

Lemma mf_bounded_perm width xs ys :
  xs ≡ₚ ys -> mf_bounded width xs -> mf_bounded width ys.
Proof.
  intros Hp Hb p Hin. apply Hb.
  apply (Permutation_in p (Permutation_sym Hp)). exact Hin.
Qed.

Lemma mf_rank_order width p q :
  (snd p < width)%nat -> (snd q < width)%nat ->
  (mf_rank width p <= mf_rank width q)%Z <-> pair_before p q.
Proof.
  destruct p as [x i], q as [y j]. unfold mf_rank, pair_before; simpl.
  intros Hi Hj. split.
  - intros H. destruct (Z_lt_ge_dec x y) as [Hlt|Hge]; [by left|].
    right.
    assert (Z.of_nat i < Z.of_nat width)%Z by lia.
    assert (Z.of_nat j < Z.of_nat width)%Z by lia.
    assert (0 < Z.of_nat width)%Z by lia.
    assert (x = y) as -> by nia. split; [done|nia].
  - intros [Hlt|[-> Hle]]; [|lia].
    assert (Z.of_nat i < Z.of_nat width)%Z by lia.
    assert (Z.of_nat j < Z.of_nat width)%Z by lia.
    assert (0 < Z.of_nat width)%Z by lia. nia.
Qed.

Lemma mf_rank_compare width p q :
  (snd p < width)%nat -> (snd q < width)%nat ->
  mf_pair_leb p q = Z.leb (mf_rank width p) (mf_rank width q).
Proof.
  intros Hp Hq. apply eq_true_iff_eq.
  rewrite mf_pair_leb_spec Z.leb_le. symmetry. apply mf_rank_order; done.
Qed.

Lemma mf_swap_map (f : mf_pair -> Z) xs i j :
  f <$> mf_pair_swap xs i j = qsort.swap_list (f <$> xs) i j.
Proof.
  unfold mf_pair_swap, qsort.swap_list.
  rewrite !list_lookup_fmap.
  destruct (xs !! i), (xs !! j); simpl; try done.
  by rewrite !list_fmap_insert.
Qed.

Lemma mf_lomuto_map width fuel xs pivot i j bound :
  mf_bounded width xs -> (snd pivot < width)%nat ->
  let '(ys, p) := mf_lomuto fuel xs pivot i j bound in
  qsort.lomuto fuel (mf_rank width <$> xs) (mf_rank width pivot) i j bound =
    (mf_rank width <$> ys, p).
Proof.
  revert xs i j. induction fuel as [|fuel IH]; intros xs i j Hb Hp; simpl; [done|].
  destruct (Nat.ltb j bound); [|done]. rewrite list_lookup_fmap.
  destruct (xs !! j) as [v|] eqn:Hv; simpl; [|done].
  assert (snd v < width)%nat as Hvb.
  { apply Hb. apply elem_of_list_In. eapply elem_of_list_lookup_2; exact Hv. }
  rewrite <- (mf_rank_compare width v pivot Hvb Hp).
  destruct (mf_pair_leb v pivot).
  - rewrite <- mf_swap_map. apply IH; [|done].
    eapply mf_bounded_perm; [apply Permutation_sym, mf_pair_swap_perm|exact Hb].
  - apply IH; done.
Qed.

Lemma mf_partition_map width xs lo hi :
  mf_bounded width xs ->
  let '(ys, p) := mf_partition xs lo hi in
  qsort.partition_list (mf_rank width <$> xs) lo hi = (mf_rank width <$> ys, p).
Proof.
  intros Hb. unfold mf_partition, qsort.partition_list.
  rewrite list_lookup_fmap. destruct (xs !! (hi - 1)%nat) as [pivot|] eqn:Hp; simpl; [|done].
  assert (snd pivot < width)%nat as Hpb.
  { apply Hb. apply elem_of_list_In. eapply elem_of_list_lookup_2; exact Hp. }
  pose proof (mf_lomuto_map width ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat Hb Hpb) as H.
  destruct (mf_lomuto ((hi - 1) - lo)%nat xs pivot lo lo (hi - 1)%nat) as [ys p].
  rewrite H. simpl. rewrite mf_swap_map. done.
Qed.

Lemma mf_qsort_slice_map width fuel xs lo hi :
  mf_bounded width xs ->
  mf_rank width <$> mf_qsort_slice fuel xs lo hi =
    qsort.qsort_slice fuel (mf_rank width <$> xs) lo hi.
Proof.
  revert xs lo hi. induction fuel as [|fuel IH]; intros xs lo hi Hb; simpl; [done|].
  destruct (Nat.leb hi (lo + 1)%nat); [done|].
  pose proof (mf_partition_map width xs lo hi Hb) as H.
  pose proof (mf_partition_perm xs lo hi) as Hperm.
  destruct (mf_partition xs lo hi) as [ys p]. rewrite H. simpl in Hperm.
  assert (mf_bounded width ys) as Hy.
  { eapply mf_bounded_perm; [apply Permutation_sym; exact Hperm|exact Hb]. }
  rewrite IH; last first.
  { eapply mf_bounded_perm; [apply Permutation_sym, mf_qsort_slice_perm|exact Hy]. }
  rewrite IH; done.
Qed.

Theorem mf_qsort_sorted width xs :
  mf_bounded width xs ->
  forall i j p q, (i < j)%nat -> (j < length xs)%nat ->
    mf_qsort xs !! i = Some p -> mf_qsort xs !! j = Some q -> pair_before p q.
Proof.
  intros Hb i j p q Hij Hj Hp Hq.
  assert (mf_bounded width (mf_qsort xs)) as Hb'.
  { eapply mf_bounded_perm; [apply Permutation_sym, mf_qsort_perm|exact Hb]. }
  assert (snd p < width)%nat as Hpb.
  { apply Hb'. apply elem_of_list_In. eapply elem_of_list_lookup_2; exact Hp. }
  assert (snd q < width)%nat as Hqb.
  { apply Hb'. apply elem_of_list_In. eapply elem_of_list_lookup_2; exact Hq. }
  apply (proj1 (mf_rank_order width p q Hpb Hqb)).
  assert (mf_rank width <$> mf_qsort xs = qsort.qsort (mf_rank width <$> xs)) as Hmap.
  { unfold mf_qsort, qsort.qsort. rewrite length_fmap. apply mf_qsort_slice_map; done. }
  pose proof (qsort.qsort_sorted (mf_rank width <$> xs)) as Hsorted.
  unfold qsort.slice_sorted in Hsorted. rewrite <- Hmap in Hsorted.
  eapply Hsorted; [lia|exact Hij|by rewrite length_fmap| |].
  - rewrite list_lookup_fmap Hp. done.
  - rewrite list_lookup_fmap Hq. done.
Qed.

(** * Iris kernel: the empty branch needs only the array length field.
    It does not require an impossible zero-word raw allocation. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.

Lemma mf_empty_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} o :
  ObjId o ↦ₒ[0] LitV (LitInt 0) -∗
  WP App (Rec None (Some "input") mf_body) (Val (LitV (LitObj o)))
    {{ v, ⌜v = StructV [LitV (LitBool false); LitV (LitInt 0)]⌝ ∗
           ObjId o ↦ₒ[0] LitV (LitInt 0) }}.
Proof.
  iIntros "Hlen".
  iApply (wp_bind [AppLCtx (Val (LitV (LitObj o))) ]).
  iApply wp_rec. iIntros "!> _". iApply wp_app.
  unfold mf_body. simpl.
  match goal with |- context [Let (Some "n") ?e ?k] =>
    iApply (wp_bind [LetCtx (Some "n") k]) end.
  iApply (wp_bind [AppLCtx (Val (LitV (LitObj o))) ]).
  iApply wp_rec. iIntros "!> _". iApply wp_app. simpl.
  iApply (wp_field_load with "Hlen"). iIntros "!> _ Hlen".
  iApply wp_let. simpl.
  match goal with |- context [If ?c ?e1 ?e2] => iApply (wp_bind [IfCtx e1 e2]) end.
  iApply wp_binop; [done|]. iIntros "!> _".
  iApply wp_if_true.
  iApply array.wp_struct_step. iApply array.wp_struct_step.
  iApply wp_struct_done. iIntros "!> _". iFrame. done.
Qed.

Lemma mf_pairs_values xs offset : fst <$> mf_pairs xs offset = xs.
Proof.
  revert offset. induction xs as [|a xs IH]; intros offset; [done|].
  change (a :: (fst <$> mf_pairs xs (S offset)) = a :: xs).
  f_equal. apply IH.
Qed.

Lemma mf_pairs_lookup xs offset k :
  mf_pairs xs offset !! k = (fun v => (v, (offset + k)%nat)) <$> (xs !! k).
Proof.
  revert offset k. induction xs as [|a xs IH]; intros offset k.
  - destruct k; reflexivity.
  - destruct k as [|k].
    + change (Some (a, offset) = Some (a, (offset + 0)%nat)). rewrite Nat.add_0_r. done.
    + change (mf_pairs xs (S offset) !! k =
        (fun v => (v, (offset + S k)%nat)) <$> (xs !! k)).
      rewrite IH. replace (S offset + k)%nat with (offset + S k)%nat by lia. done.
Qed.

Lemma mf_pairs_bounded xs offset : mf_bounded (offset + length xs)%nat (mf_pairs xs offset).
Proof.
  intros [x idx] Hin.
  apply elem_of_list_In in Hin. apply elem_of_list_lookup_1 in Hin.
  destruct Hin as [k Hk]. rewrite mf_pairs_lookup in Hk.
  destruct (xs !! k) as [v|] eqn:Hv; simpl in Hk; [|discriminate].
  pose proof (lookup_lt_Some xs k v Hv). inversion Hk; subst. simpl. lia.
Qed.

Definition mf_sorted_pairs xs := mf_qsort (mf_pairs xs 0%nat).

Theorem mf_sorted_pairs_ordered xs i j p q :
  (i < j)%nat -> (j < length xs)%nat ->
  mf_sorted_pairs xs !! i = Some p -> mf_sorted_pairs xs !! j = Some q -> pair_before p q.
Proof.
  unfold mf_sorted_pairs. intros Hij Hj Hp Hq.
  eapply (mf_qsort_sorted (length xs)); [|exact Hij| |exact Hp|exact Hq].
  - pose proof (mf_pairs_bounded xs 0%nat) as H. simpl in H. exact H.
  - assert (length (mf_pairs xs 0%nat) = length xs) as ->.
    { rewrite <- (mf_pairs_values xs 0%nat) at 2. rewrite length_fmap. done. }
    exact Hj.
Qed.

Theorem mf_sorted_pairs_frequency xs x :
  mf_frequency x (fst <$> mf_sorted_pairs xs) = mf_frequency x xs.
Proof.
  unfold mf_frequency, mf_sorted_pairs.
  pose proof (Permutation_map fst (mf_qsort_perm (mf_pairs xs 0%nat))) as H.
  change ((fst <$> mf_qsort (mf_pairs xs 0%nat)) ≡ₚ (fst <$> mf_pairs xs 0%nat)) in H.
  rewrite mf_pairs_values in H.
  exact ((proj1 (Permutation_count_occ Z.eq_dec _ _)) H x).
Qed.

Theorem mf_sorted_pairs_origin xs p :
  In p (mf_sorted_pairs xs) ->
  exists k, xs !! k = Some (fst p) /\ snd p = k.
Proof.
  intros Hin. unfold mf_sorted_pairs in Hin.
  apply (Permutation_in p (mf_qsort_perm (mf_pairs xs 0%nat))) in Hin.
  apply elem_of_list_In in Hin. apply elem_of_list_lookup_1 in Hin.
  destruct Hin as [k Hk]. rewrite mf_pairs_lookup in Hk. simpl in Hk.
  destruct (xs !! k) as [v|] eqn:Hv; simpl in Hk; [|discriminate].
  inversion Hk; subst p. exists k. simpl. done.
Qed.

(** * Selection among run summaries
    A summary contains (value, (count, minimum original index)). *)
Definition mf_summary := (Z * (nat * nat))%type.
Definition mf_summary_count (s : mf_summary) := fst (snd s).
Definition mf_summary_first (s : mf_summary) := snd (snd s).
Definition mf_score (p q : mf_summary) : Prop :=
  (mf_summary_count q <= mf_summary_count p)%nat /\
  (mf_summary_count q = mf_summary_count p ->
    (mf_summary_first p <= mf_summary_first q)%nat).
Definition mf_score_leb (p q : mf_summary) : bool :=
  Nat.ltb (mf_summary_count q) (mf_summary_count p) ||
    (Nat.eqb (mf_summary_count q) (mf_summary_count p) &&
      Nat.leb (mf_summary_first p) (mf_summary_first q)).

Lemma mf_score_leb_spec p q : mf_score_leb p q = true <-> mf_score p q.
Proof.
  unfold mf_score_leb, mf_score.
  rewrite Bool.orb_true_iff Bool.andb_true_iff Nat.ltb_lt Nat.eqb_eq Nat.leb_le.
  intuition lia.
Qed.
Lemma mf_score_refl p : mf_score p p.
Proof. unfold mf_score. intuition lia. Qed.
Lemma mf_score_trans p q r : mf_score p q -> mf_score q r -> mf_score p r.
Proof. unfold mf_score. intros [Hp Hi] [Hq Hj]. split; [lia|]. intros Heq. apply Nat.le_trans with (mf_summary_first q); [apply Hi|apply Hj]; lia. Qed.
Lemma mf_score_total p q : mf_score p q \/ mf_score q p.
Proof.
  unfold mf_score.
  destruct (Nat.lt_trichotomy (mf_summary_count p) (mf_summary_count q)) as [H|[H|H]];
    [right; intuition lia| |left; intuition lia].
  destruct (Nat.le_ge_cases (mf_summary_first p) (mf_summary_first q)); intuition lia.
Qed.

Fixpoint mf_best_summary (runs : list mf_summary) : option mf_summary :=
  match runs with
  | [] => None
  | p :: rest => match mf_best_summary rest with
    | None => Some p
    | Some q => if mf_score_leb p q then Some p else Some q
    end
  end.

Lemma mf_best_summary_none runs : mf_best_summary runs = None <-> runs = [].
Proof.
  destruct runs; simpl; [done|]. destruct (mf_best_summary runs); [|done].
  destruct (mf_score_leb m m0); done.
Qed.

Lemma mf_best_summary_sound runs :
  match mf_best_summary runs with
  | None => runs = []
  | Some best => In best runs /\ forall s, In s runs -> mf_score best s
  end.
Proof.
  induction runs as [|p rest IH]; simpl; [done|].
  destruct (mf_best_summary rest) as [q|] eqn:Hq.
  - destruct IH as [Hmem Hmax]. destruct (mf_score_leb p q) eqn:Hcmp.
    + apply mf_score_leb_spec in Hcmp. split; [by left|].
      intros s [->|Hs]; [apply mf_score_refl|].
      eapply mf_score_trans; [exact Hcmp|apply Hmax; exact Hs].
    + assert (mf_score q p) as Hqp.
      { destruct (mf_score_total p q) as [H|H]; [|done].
        apply mf_score_leb_spec in H. congruence. }
      split; [by right|]. intros s [->|Hs]; [done|apply Hmax; exact Hs].
  - apply mf_best_summary_none in Hq. subst rest.
    split; [by left|]. intros s [->|[]]. apply mf_score_refl.
Qed.

Definition mf_summary_valid xs s : Prop :=
  mf_summary_count s = mf_frequency (fst s) xs /\
  mf_summary_first s = mf_first_index_or_len (fst s) xs /\
  (0 < mf_summary_count s)%nat.
Definition mf_summaries_complete xs runs : Prop :=
  (forall s, In s runs -> mf_summary_valid xs s) /\
  (forall x, In x xs -> exists s, In s runs /\ fst s = x).

(** This theorem proves the selection stage. Its precondition must still be
    established for the summaries actually produced by the CJR group scan. *)
Theorem mf_summary_selection_correct xs runs :
  mf_summaries_complete xs runs ->
  most_frequent_spec xs (fst <$> mf_best_summary runs).
Proof.
  intros [Hvalid Hcomplete]. pose proof (mf_best_summary_sound runs) as Hsound.
  destruct (mf_best_summary runs) as [best|] eqn:Hbest.
  - destruct Hsound as [Hin Hmax]. destruct (Hvalid best Hin) as [Hcount [Hfirst Hpos]].
    assert (In (fst best) xs) as Hmem.
    { apply mf_frequency_pos_mem. rewrite <- Hcount. done. }
    destruct xs as [|a xs]; [done|].
    change ((mf_frequency (fst best) (a :: xs) > 0)%nat /\
      (forall y, (mf_frequency y (a :: xs) <= mf_frequency (fst best) (a :: xs))%nat) /\
      (forall y, mf_frequency y (a :: xs) = mf_frequency (fst best) (a :: xs) ->
        mf_first_index_or_len (fst best) (a :: xs) <= mf_first_index_or_len y (a :: xs))%nat).
    split; [rewrite <- Hcount; done|]. split.
    + intros y. destruct (in_dec Z.eq_dec y (a :: xs)) as [Hy|Hnot].
      * destruct (Hcomplete y Hy) as [s [Hs Hsy]].
        destruct (Hvalid s Hs) as [Hsc _].
        pose proof (proj1 (Hmax s Hs)) as Hle. rewrite Hcount Hsc Hsy in Hle. done.
      * rewrite (mf_frequency_not_mem y (a :: xs) Hnot). lia.
    + intros y Heq. assert (In y (a :: xs)) as Hy.
      { apply mf_frequency_pos_mem. rewrite Heq. rewrite <- Hcount. done. }
      destruct (Hcomplete y Hy) as [s [Hs Hsy]].
      destruct (Hvalid s Hs) as [Hsc [Hsf _]].
      destruct (Hmax s Hs) as [_ Htie].
      rewrite <- Hfirst. rewrite <- Hsy, <- Hsf.
      apply Htie. rewrite Hsc Hcount Hsy. done.
  - apply mf_best_summary_none in Hbest. subst runs.
    destruct xs as [|a xs]; [done|].
    destruct (Hcomplete a (or_introl eq_refl)) as [s [[] _]].
Qed.

(** * Functional run scan
    Structural recursion groups adjacent equal values. It summarizes the
    same maximal runs visited by the forward imperative scan, without
    re-counting candidates against the whole input. *)
From Coq Require Import Sorting.Sorted.

Definition mf_single_summary (p : mf_pair) : mf_summary := (fst p, (1%nat, snd p)).
Definition mf_extend_summary (p : mf_pair) (s : mf_summary) : mf_summary :=
  (fst p, (S (mf_summary_count s), Nat.min (snd p) (mf_summary_first s))).

Fixpoint mf_run_summaries (pairs : list mf_pair) : list mf_summary :=
  match pairs with
  | [] => []
  | p :: ps =>
    match mf_run_summaries ps with
    | [] => [mf_single_summary p]
    | s :: rest => if Z.eq_dec (fst p) (fst s)
        then mf_extend_summary p s :: rest
        else mf_single_summary p :: s :: rest
    end
  end.

Definition mf_pair_summary_valid (pairs : list mf_pair) (s : mf_summary) : Prop :=
  mf_summary_count s = mf_frequency (fst s) (fst <$> pairs) /\
  (0 < mf_summary_count s)%nat /\
  In (fst s, mf_summary_first s) pairs /\
  (forall i, In (fst s, i) pairs -> (mf_summary_first s <= i)%nat).

Lemma mf_frequency_cons_other a x xs :
  a <> x -> mf_frequency x (a :: xs) = mf_frequency x xs.
Proof. intros H. unfold mf_frequency. simpl. destruct (Z.eq_dec a x); congruence. Qed.

Lemma mf_pair_summary_skip p ps s :
  fst p <> fst s -> mf_pair_summary_valid ps s ->
  mf_pair_summary_valid (p :: ps) s.
Proof.
  destruct p as [x idx]. intros Hneq [Hcount [Hpos [Hmem Hmin]]]. cbn [fst] in Hneq.
  unfold mf_pair_summary_valid.
  change (mf_summary_count s = mf_frequency (fst s) (x :: (fst <$> ps)) /\
    (0 < mf_summary_count s)%nat /\ In (fst s, mf_summary_first s) ((x,idx)::ps) /\
    (forall i, In (fst s,i) ((x,idx)::ps) -> (mf_summary_first s <= i)%nat)).
  rewrite mf_frequency_cons_other; [|done].
  split; [done|]. split; [done|]. split; [by right|].
  intros i [Heq|Hin]; [inversion Heq; congruence|by apply Hmin].
Qed.

Lemma mf_pair_summary_extend p ps s :
  fst p = fst s -> mf_pair_summary_valid ps s ->
  mf_pair_summary_valid (p :: ps) (mf_extend_summary p s).
Proof.
  destruct p as [x idx]. intros Hsame [Hcount [Hpos [Hmem Hmin]]].
  unfold mf_pair_summary_valid, mf_extend_summary, mf_summary_count, mf_summary_first in *.
  cbn [fst snd] in *.
  change (S (fst (snd s)) = mf_frequency x (x :: (fst <$> ps)) /\
    (0 < S (fst (snd s)))%nat /\
    In (x, Nat.min idx (snd (snd s))) ((x,idx)::ps) /\
    (forall i, In (x,i) ((x,idx)::ps) -> (Nat.min idx (snd (snd s)) <= i)%nat)).
  rewrite <- Hsame in Hcount, Hmem, Hmin. rewrite mf_frequency_head.
  split; [by rewrite Hcount|]. split; [lia|]. split.
  - destruct (Nat.le_ge_cases idx (snd (snd s))) as [Hle|Hle].
    + rewrite Nat.min_l; [by left|done].
    + rewrite Nat.min_r; [by right|done].
  - intros i [Heq|Hin].
    + inversion Heq; subst. apply Nat.le_min_l.
    + apply Nat.le_trans with (snd (snd s)); [apply Nat.le_min_r|apply Hmin; done].
Qed.

Lemma mf_run_summaries_nil pairs : mf_run_summaries pairs = [] <-> pairs = [].
Proof.
  destruct pairs; simpl; [done|]. destruct (mf_run_summaries pairs); [done|].
  destruct (Z.eq_dec (fst m) (fst m0)); done.
Qed.

Lemma mf_run_summaries_head p ps :
  exists s rest, mf_run_summaries (p :: ps) = s :: rest /\ fst s = fst p.
Proof.
  simpl. destruct (mf_run_summaries ps) as [|s rest].
  - exists (mf_single_summary p), []. done.
  - destruct (Z.eq_dec (fst p) (fst s)).
    + exists (mf_extend_summary p s), rest. done.
    + exists (mf_single_summary p), (s :: rest). done.
Qed.

Definition mf_values_sorted := StronglySorted (fun p q : mf_pair => (fst p <= fst q)%Z).

Lemma mf_sorted_head_absent p q ps :
  mf_values_sorted (p :: q :: ps) -> fst p <> fst q ->
  forall i, ~ In (fst p, i) (q :: ps).
Proof.
  intros Hsort Hneq i Hin.
  inversion Hsort as [|? ? Htail Hallp]; subst.
  inversion Htail as [|? ? Hrest Hallq]; subst.
  rewrite List.Forall_forall in Hallp.
  rewrite List.Forall_forall in Hallq.
  pose proof (Hallp q (or_introl eq_refl)) as Hpq.
  destruct Hin as [Heq|Hin].
  { pose proof (f_equal fst Heq) as H. simpl in H. congruence. }
  pose proof (Hallq (fst p, i) Hin) as Hqp. simpl in Hqp. lia.
Qed.

Definition mf_run_result (pairs : list mf_pair) (runs : list mf_summary) : Prop :=
  (forall s, In s runs -> mf_pair_summary_valid pairs s) /\
  List.NoDup (map fst runs) /\
  (forall p, In p pairs -> exists s, In s runs /\ fst s = fst p).

Lemma mf_single_summary_valid p : mf_pair_summary_valid [p] (mf_single_summary p).
Proof.
  destruct p as [x i]. unfold mf_pair_summary_valid, mf_single_summary,
    mf_summary_count, mf_summary_first. cbn [fst snd].
  change (1%nat = mf_frequency x [x] /\ (0 < 1)%nat /\
    In (x,i) [(x,i)] /\ (forall j, In (x,j) [(x,i)] -> (i <= j)%nat)).
  rewrite mf_frequency_head. unfold mf_frequency. simpl.
  repeat split; try lia; try (by left). intros j [H|[]]. inversion H. lia.
Qed.

Theorem mf_run_summaries_sound pairs :
  mf_values_sorted pairs -> mf_run_result pairs (mf_run_summaries pairs).
Proof.
  induction pairs as [|p ps IH]; intros Hsorted.
  - split; [intros s []|]. split; [constructor|intros p []].
  - inversion Hsorted as [|? ? Htail Hall]; subst.
    destruct ps as [|q qs].
    + simpl. split.
      * intros s [<-|[]]. apply mf_single_summary_valid.
      * split; [constructor; [intros []|constructor]|].
        intros r [<-|[]]. exists (mf_single_summary p). split; [by left|done].
    + specialize (IH Htail).
      destruct (mf_run_summaries_head q qs) as [s [rest [Hgroups Hhead]]].
      rewrite Hgroups in IH. destruct IH as [Hvalid [Hdup Hcomplete]].
      change (mf_run_result (p :: q :: qs)
        (match mf_run_summaries (q :: qs) with
         | [] => [mf_single_summary p]
         | t :: ts => if Z.eq_dec (fst p) (fst t) then mf_extend_summary p t :: ts
             else mf_single_summary p :: t :: ts
         end)).
      rewrite Hgroups.
      destruct (Z.eq_dec (fst p) (fst s)) as [Hsame|Hdiff].
      * assert (forall t, In t rest -> fst p <> fst t) as Hother.
        { inversion Hdup as [|? ? Hnot Hrest]; subst.
          intros t Ht Heq. apply Hnot. apply in_map_iff.
          exists t. split; [congruence|done]. }
        split.
        -- intros t [<-|Ht].
           ++ apply mf_pair_summary_extend; [done|]. apply Hvalid. by left.
           ++ apply mf_pair_summary_skip; [apply Hother; done|]. apply Hvalid. by right.
        -- split.
           ++ change (List.NoDup (fst p :: map fst rest)). rewrite Hsame. exact Hdup.
           ++ intros r [<-|Hr].
              ** exists (mf_extend_summary p s). split; [by left|done].
              ** destruct (Hcomplete r Hr) as [t [[Ht|Ht] Htr]].
                 --- subst t. exists (mf_extend_summary p s). split; [by left|]. simpl. congruence.
                 --- exists t. split; [by right|done].
      * assert (forall i, ~ In (fst p,i) (q :: qs)) as Habsent.
        { apply (mf_sorted_head_absent p q qs Hsorted). congruence. }
        assert (forall t, In t (s :: rest) -> fst p <> fst t) as Hother.
        { intros t Ht Heq. destruct (Hvalid t Ht) as [_ [_ [Hmem _]]].
          rewrite <- Heq in Hmem. apply (Habsent (mf_summary_first t)). exact Hmem. }
        assert (mf_pair_summary_valid (p :: q :: qs) (mf_single_summary p)) as Hpvalid.
        { unfold mf_pair_summary_valid, mf_single_summary, mf_summary_count, mf_summary_first.
          cbn [fst snd].
          change (1%nat = mf_frequency (fst p) (fst p :: (fst <$> (q :: qs))) /\
            (0 < 1)%nat /\ In (fst p,snd p) (p :: q :: qs) /\
            (forall i, In (fst p,i) (p :: q :: qs) -> (snd p <= i)%nat)).
          rewrite mf_frequency_head.
          assert (mf_frequency (fst p) (fst <$> (q :: qs)) = 0%nat) as Hz.
          { apply mf_frequency_not_mem. intros Hin.
            change (In (fst p) (map fst (q :: qs))) in Hin.
            apply in_map_iff in Hin. destruct Hin as [[x i] [Heq Hmem]].
            simpl in Heq. subst x. apply (Habsent i). exact Hmem. }
          rewrite Hz. split; [done|]. split; [lia|]. split.
          - left. by destruct p.
          - intros i [Heq|Hin].
            + pose proof (f_equal snd Heq) as H. simpl in H. lia.
            + exfalso. apply (Habsent i). exact Hin. }
        split.
        -- intros t [<-|Ht]; [exact Hpvalid|].
           apply mf_pair_summary_skip; [apply Hother; done|apply Hvalid; done].
        -- split.
           ++ change (List.NoDup (fst p :: map fst (s :: rest))). constructor; [|exact Hdup].
              intros Hin. apply in_map_iff in Hin. destruct Hin as [t [Heq Ht]].
              apply (Hother t Ht). congruence.
           ++ intros r [<-|Hr].
              ** exists (mf_single_summary p). split; [by left|done].
              ** destruct (Hcomplete r Hr) as [t [Ht Htr]]. exists t. split; [by right|done].
Qed.

Lemma mf_values_sorted_from_lookup pairs :
  (forall i j p q, (i < j)%nat -> (j < length pairs)%nat ->
    pairs !! i = Some p -> pairs !! j = Some q -> (fst p <= fst q)%Z) ->
  mf_values_sorted pairs.
Proof.
  induction pairs as [|p ps IH]; intros H; [constructor|].
  constructor.
  - apply IH. intros i j x y Hij Hj Hx Hy.
    apply (H (S i) (S j) x y); simpl; [lia|lia|done|done].
  - apply List.Forall_forall. intros q Hin.
    apply elem_of_list_In in Hin. apply elem_of_list_lookup_1 in Hin.
    destruct Hin as [j Hj].
    apply (H 0%nat (S j) p q); simpl; [lia| |done|done].
    pose proof (lookup_lt_Some ps j q Hj). lia.
Qed.

Lemma mf_sorted_pairs_length xs : length (mf_sorted_pairs xs) = length xs.
Proof.
  unfold mf_sorted_pairs.
  rewrite (Permutation_length (mf_qsort_perm (mf_pairs xs 0%nat))).
  pose proof (f_equal (@length Z) (mf_pairs_values xs 0%nat)) as H.
  rewrite length_fmap in H. done.
Qed.

Lemma mf_sorted_pairs_values_sorted xs : mf_values_sorted (mf_sorted_pairs xs).
Proof.
  apply mf_values_sorted_from_lookup. intros i j p q Hij Hj Hp Hq.
  rewrite mf_sorted_pairs_length in Hj.
  pose proof (mf_sorted_pairs_ordered xs i j p q Hij Hj Hp Hq) as H.
  unfold pair_before in H. destruct H as [H|[H _]]; lia.
Qed.

Lemma mf_first_index_attained x xs :
  In x xs -> xs !! mf_first_index_or_len x xs = Some x.
Proof.
  induction xs as [|a xs IH]; intros Hin; [done|].
  destruct (Z.eq_dec x a) as [->|Hneq].
  - rewrite mf_first_index_or_len_head. done.
  - rewrite mf_first_index_or_len_skip; [|done].
    change (xs !! mf_first_index_or_len x xs = Some x).
    apply IH. destruct Hin as [H|H]; [congruence|done].
Qed.

Lemma mf_first_index_minimum x xs i :
  xs !! i = Some x -> (mf_first_index_or_len x xs <= i)%nat.
Proof.
  revert i. induction xs as [|a xs IH]; intros [|i] Hi; [done|done| |].
  - simpl in Hi. inversion Hi; subst. rewrite mf_first_index_or_len_head. lia.
  - destruct (Z.eq_dec x a) as [->|Hneq].
    + rewrite mf_first_index_or_len_head. lia.
    + rewrite mf_first_index_or_len_skip; [|done]. simpl in Hi.
      pose proof (IH i Hi). lia.
Qed.

Lemma mf_sorted_pairs_contains xs x i :
  xs !! i = Some x -> In (x,i) (mf_sorted_pairs xs).
Proof.
  intros Hi. unfold mf_sorted_pairs.
  apply (Permutation_in (x,i) (Permutation_sym (mf_qsort_perm (mf_pairs xs 0%nat)))).
  apply elem_of_list_In. eapply elem_of_list_lookup_2 with i.
  rewrite mf_pairs_lookup Hi. simpl. done.
Qed.

Theorem mf_run_summaries_complete xs :
  mf_summaries_complete xs (mf_run_summaries (mf_sorted_pairs xs)).
Proof.
  pose proof (mf_run_summaries_sound (mf_sorted_pairs xs) (mf_sorted_pairs_values_sorted xs)) as H.
  destruct H as [Hvalid [_ Hcomplete]]. split.
  - intros s Hin. destruct (Hvalid s Hin) as [Hcount [Hpos [Hmem Hmin]]].
    unfold mf_summary_valid. rewrite mf_sorted_pairs_frequency in Hcount.
    split; [done|]. split; [|done].
    destruct (mf_sorted_pairs_origin xs (fst s,mf_summary_first s) Hmem) as [i [Hi Hidx]].
    cbn [fst snd] in Hi, Hidx.
    assert (xs !! mf_summary_first s = Some (fst s)) as Hlookup by congruence.
    pose proof (mf_first_index_minimum (fst s) xs (mf_summary_first s) Hlookup) as Hle.
    assert (In (fst s) xs) as Hmember.
    { apply mf_frequency_pos_mem. rewrite <- Hcount. exact Hpos. }
    pose proof (mf_first_index_attained (fst s) xs Hmember) as Hfirst.
    pose proof (mf_sorted_pairs_contains xs (fst s) (mf_first_index_or_len (fst s) xs) Hfirst) as Hrecord.
    specialize (Hmin _ Hrecord). lia.
  - intros x Hin.
    pose proof (mf_first_index_attained x xs Hin) as Hfirst.
    pose proof (mf_sorted_pairs_contains xs x (mf_first_index_or_len x xs) Hfirst) as Hrecord.
    destruct (Hcomplete (x,mf_first_index_or_len x xs) Hrecord) as [s [Hs Hsx]].
    exists s. split; [done|exact Hsx].
Qed.

Definition mf_sort_scan xs : option Z :=
  fst <$> mf_best_summary (mf_run_summaries (mf_sorted_pairs xs)).

Theorem mf_sort_scan_correct xs : most_frequent_spec xs (mf_sort_scan xs).
Proof.
  apply mf_summary_selection_correct. apply mf_run_summaries_complete.
Qed.

Example mf_sort_scan_empty : mf_sort_scan [] = None.
Proof. reflexivity. Qed.
Example mf_sort_scan_interleaved_tie : mf_sort_scan [8%Z;3%Z;3%Z;8%Z] = Some 8%Z.
Proof. vm_compute. reflexivity. Qed.
Example mf_sort_scan_three_way_tie : mf_sort_scan [5%Z;9%Z;(-1)%Z;9%Z;(-1)%Z;5%Z] = Some 5%Z.
Proof. vm_compute. reflexivity. Qed.

(** The first-occurrence tie rule determines a unique answer. *)
Theorem most_frequent_spec_unique xs a b :
  most_frequent_spec xs a -> most_frequent_spec xs b -> a = b.
Proof.
  destruct xs as [|v xs]; destruct a as [x|]; destruct b as [y|];
    try done; try (simpl; tauto).
  intros [Hx [Hmaxx Hfirstx]] [Hy [Hmaxy Hfirsty]].
  assert (mf_frequency x (v::xs) = mf_frequency y (v::xs)) as Heq.
  { pose proof (Hmaxx y). pose proof (Hmaxy x). lia. }
  pose proof (Hfirstx y (eq_sym Heq)) as Hxy.
  pose proof (Hfirsty x Heq) as Hyx.
  assert (mf_first_index_or_len x (v::xs) = mf_first_index_or_len y (v::xs)) as Hidx by lia.
  assert (In x (v::xs)) as Hinx by (apply mf_frequency_pos_mem; exact Hx).
  assert (In y (v::xs)) as Hiny by (apply mf_frequency_pos_mem; exact Hy).
  pose proof (mf_first_index_attained x (v::xs) Hinx) as Hlookupx.
  pose proof (mf_first_index_attained y (v::xs) Hiny) as Hlookupy.
  rewrite Hidx in Hlookupx. congruence.
Qed.

(** Whole-buffer cleanup used by the concrete final two Free expressions. *)
From iris.proofmode Require Import environments.
From cjr.examples Require Import mf_memory hm_tactics.

Lemma mf_release_array_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs a :
  is_array xs a -∗
  WP Free (FieldLoad (Val a) 1) {{ v, ⌜v = LitV LitUnit⌝ }}.
Proof.
  iIntros "Ha".
  iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
  rewrite Ha. iApply (wp_bind [FreeCtx]).
  iApply (wp_field_load with "Hptr"). iIntros "!> _ Hptr".
  iApply (mf_wp_free_block base (LitV ∘ LitInt <$> xs) with "[Hblk] [Hcells]").
  - by rewrite length_fmap.
  - by rewrite big_sepL_fmap.
  - iIntros "!> _". done.
Qed.

Definition mf_cleanup (a b : val) (answer : Z) : expr :=
  Let None (Free (FieldLoad (Val a) 1))
    (Let None (Free (FieldLoad (Val b) 1))
      (Struct [] [Val (LitV (LitBool true)); Val (LitV (LitInt answer))])).

Lemma mf_cleanup_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} input inp xs a ys b answer :
  is_array input inp -∗ is_array xs a -∗ is_array ys b -∗
  WP mf_cleanup a b answer
    {{ v, ⌜v = StructV [LitV (LitBool true); LitV (LitInt answer)]⌝ ∗ is_array input inp }}.
Proof.
  iIntros "Hinput Ha Hb". unfold mf_cleanup.
  hm_take. iApply (wp_wand with "[Ha]"). { iApply (mf_release_array_wp with "Ha"). }
  iIntros (v) "%Hv". subst v. hm_admin.
  hm_take. iApply (wp_wand with "[Hb]"). { iApply (mf_release_array_wp with "Hb"). }
  iIntros (v) "%Hv". subst v. hm_admin. iFrame. done.
Qed.

Lemma mf_get_value_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs o i x :
  xs !! i = Some x ->
  is_array xs (LitV (LitObj o)) -∗
  WP App (Val (RecV None (Some "args") array.get_body))
    (Val (StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i))]))
    {{ v, ⌜v = LitV (LitInt x)⌝ ∗ is_array xs (LitV (LitObj o)) }}.
Proof.
  iIntros (Hi) "Ha".
  iDestruct "Ha" as (o' base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
  inversion Ha; subst o'. unfold array.get_body. hm_pure. hm_take.
  iApply (wp_field_load with "Hptr"). iIntros "!> _ Hptr". hm_pure.
  iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
  iApply (wp_load with "Hi"). iIntros "!> _ Hi".
  iDestruct ("Hclose" with "Hi") as "Hcells".
  iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
Qed.

Lemma mf_set_value_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs o i old x :
  xs !! i = Some old ->
  is_array xs (LitV (LitObj o)) -∗
  WP App (Val (RecV None (Some "args") array.set_body))
    (Val (StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i)); LitV (LitInt x)]))
    {{ v, ⌜v = LitV LitUnit⌝ ∗ is_array (<[i:=x]> xs) (LitV (LitObj o)) }}.
Proof.
  iIntros (Hi) "Ha".
  iDestruct "Ha" as (o' base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
  inversion Ha; subst o'. unfold array.set_body. hm_pure. hm_take.
  iApply (wp_field_load with "Hptr"). iIntros "!> _ Hptr". hm_pure.
  iDestruct (big_sepL_insert_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
  iApply (wp_store with "Hi"). iIntros "!> _ Hi".
  iDestruct ("Hclose" $! x with "Hi") as "Hcells".
  iSplit; [done|]. iExists o, base. iSplit; [done|].
  rewrite length_insert. iFrame.
Qed.

Definition mf_call_swap (oa ob : loc) (i j : nat) : expr :=
  App (Val (RecV None (Some "args") mf_swap_body))
    (Val (StructV [LitV (LitObj oa); LitV (LitObj ob);
       LitV (LitInt (Z.of_nat i)); LitV (LitInt (Z.of_nat j))])).

Lemma mf_swap_arrays_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    xs indices oa ob i j x y xi yi :
  xs !! i = Some x -> xs !! j = Some y ->
  indices !! i = Some xi -> indices !! j = Some yi ->
  is_array xs (LitV (LitObj oa)) -∗ is_array indices (LitV (LitObj ob)) -∗
  WP mf_call_swap oa ob i j
    {{ v, ⌜v = LitV LitUnit⌝ ∗
       is_array (qsort.swap_list xs i j) (LitV (LitObj oa)) ∗
       is_array (qsort.swap_list indices i j) (LitV (LitObj ob)) }}.
Proof.
  iIntros (Hi Hj Hii Hij) "Ha Hb". unfold mf_call_swap.
  iApply wp_app.
  unfold mf_swap_body. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp with "Ha"). exact Hi. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Hb]").
  { iApply (mf_get_value_wp with "Hb"). exact Hii. }
  iIntros (v) "[%Hv Hb]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp with "Ha"). exact Hj. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Hb]").
  { iApply (mf_get_value_wp with "Hb"). exact Hij. }
  iIntros (v) "[%Hv Hb]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Ha]").
  { iApply (mf_set_value_wp with "Ha"). exact Hi. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Hb]").
  { iApply (mf_set_value_wp with "Hb"). exact Hii. }
  iIntros (v) "[%Hv Hb]". subst v. hm_admin.
  hm_take. hm_args. iApply (wp_wand with "[Ha]").
  { iApply (mf_set_value_wp with "Ha").
    destruct (decide (i=j)) as [->|Hne].
    - assert (x=y) as -> by congruence. rewrite list_lookup_insert; [done|].
      eapply lookup_lt_Some; exact Hj.
    - rewrite list_lookup_insert_ne; [exact Hj|congruence]. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin. hm_args.
  iApply (wp_wand with "[Hb]").
  { iApply (mf_set_value_wp with "Hb").
    destruct (decide (i=j)) as [->|Hne].
    - assert (xi=yi) as -> by congruence. rewrite list_lookup_insert; [done|].
      eapply lookup_lt_Some; exact Hij.
    - rewrite list_lookup_insert_ne; [exact Hij|congruence]. }
  iIntros (v) "[%Hv Hb]". subst v.
  rewrite (qsort.swap_list_code xs i j x y Hi Hj).
  rewrite (qsort.swap_list_code indices i j xi yi Hii Hij).
  iFrame. done.
Qed.

Definition mf_pair_arrays `{!cjrGS Σ} (pairs : list mf_pair) (oa ob : loc) : iProp Σ :=
  is_array (fst <$> pairs) (LitV (LitObj oa)) ∗
  is_array ((Z.of_nat ∘ snd) <$> pairs) (LitV (LitObj ob)).

Lemma mf_swap_pairs_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} pairs oa ob i j p q :
  pairs !! i = Some p -> pairs !! j = Some q ->
  mf_pair_arrays pairs oa ob -∗
  WP mf_call_swap oa ob i j
    {{ v, ⌜v = LitV LitUnit⌝ ∗ mf_pair_arrays (mf_pair_swap pairs i j) oa ob }}.
Proof.
  iIntros (Hi Hj) "[Ha Hb]".
  iApply (wp_wand with "[Ha Hb]").
  { iApply (mf_swap_arrays_wp with "Ha Hb"); by rewrite list_lookup_fmap Hi || rewrite list_lookup_fmap Hj. }
  iIntros (v) "(%Hv & Ha & Hb)".
  unfold mf_pair_arrays. rewrite !mf_swap_map. iFrame. done.
Qed.

Definition mf_lex_compare (x ix y iy : expr) : expr :=
  If (BinOp LeOp x y)
    (If (BinOp LeOp y x) (BinOp LeOp ix iy) (Val (LitV (LitBool true))))
    (Val (LitV (LitBool false))).

Lemma mf_le_bool x y : bool_decide (x <= y)%Z = Z.leb x y.
Proof. apply eq_true_iff_eq. rewrite bool_decide_eq_true Z.leb_le. done. Qed.
Lemma mf_nat_le_bool x y :
  bool_decide (Z.of_nat x <= Z.of_nat y)%Z = Nat.leb x y.
Proof. apply eq_true_iff_eq. rewrite bool_decide_eq_true Nat.leb_le. lia. Qed.

Lemma mf_lex_compare_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} p q :
  ⊢ WP mf_lex_compare (Val (LitV (LitInt (fst p))))
      (Val (LitV (LitInt (Z.of_nat (snd p))))) (Val (LitV (LitInt (fst q))))
      (Val (LitV (LitInt (Z.of_nat (snd q)))))
    {{ v, ⌜v = LitV (LitBool (mf_pair_leb p q))⌝ }}.
Proof.
  destruct p as [x i], q as [y j]. unfold mf_lex_compare, mf_pair_leb.
  cbn [fst snd]. destruct (Z.leb x y) eqn:Hxy; [|].
  - hm_pure. rewrite mf_le_bool Hxy. iApply wp_if_true.
    destruct (Z.leb y x) eqn:Hyx.
    + hm_pure. rewrite mf_le_bool Hyx. iApply wp_if_true.
      hm_pure. rewrite mf_nat_le_bool. done.
    + hm_pure. rewrite mf_le_bool Hyx. iApply wp_if_false. hm_pure. done.
  - hm_pure. rewrite mf_le_bool Hxy. iApply wp_if_false. hm_pure. done.
Qed.

Ltac mf_load_stack Hname :=
  match goal with
  | |- envs_entails _ (WP ?e {{ ?Φ }}) =>
    hm_focus e ltac:(fun _ => iApply (wp_stack_load with Hname);
      iIntros "!> _"; iIntros Hname)
  end.

Lemma mf_increment_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} l n Φ :
  StackId l ↦ₛ qsort.nval n -∗
  (StackId l ↦ₛ qsort.nval (S n) -∗ Φ (LitV LitUnit)) -∗
  WP qsort.sset l (qsort.plus1 (qsort.sload l)) {{ Φ }}.
Proof.
  iIntros "Hl HΦ".
  unfold qsort.sset, qsort.plus1, qsort.sload, qsort.slot,
    qsort.nval, qsort.zval, qsort.one.
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack l))]).
  iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
  iApply wp_binop; [reflexivity|]. iIntros "!> _".
  replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia.
  iApply (wp_stack_assign with "Hl"). iIntros "!> _ Hl".
  iApply ("HΦ" with "Hl").
Qed.

Definition mf_partition_step (oa ob : loc) (pivot : mf_pair) (li lj : loc) : expr :=
  Let (Some "v")
    (App (Rec None (Some "args") array.get_body)
      (Struct [] [Val (LitV (LitObj oa)); qsort.sload lj]))
    (Let (Some "ix")
      (App (Rec None (Some "args") array.get_body)
        (Struct [] [Val (LitV (LitObj ob)); qsort.sload lj]))
      (Let None
        (If (mf_lex_compare (Var "v") (Var "ix")
          (Val (LitV (LitInt (fst pivot))))
          (Val (LitV (LitInt (Z.of_nat (snd pivot))))))
          (Let None
            (App (Rec None (Some "args") mf_swap_body)
              (Struct [] [Val (LitV (LitObj oa)); Val (LitV (LitObj ob));
                qsort.sload li; qsort.sload lj]))
            (qsort.sset li (qsort.plus1 (qsort.sload li))))
          (Val (LitV LitUnit)))
        (qsort.sset lj (qsort.plus1 (qsort.sload lj))))).

Lemma mf_partition_step_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    pairs oa ob pivot i j li lj p q :
  pairs !! i = Some p -> pairs !! j = Some q ->
  StackId li ↦ₛ qsort.nval i -∗ StackId lj ↦ₛ qsort.nval j -∗
  mf_pair_arrays pairs oa ob -∗
  WP mf_partition_step oa ob pivot li lj
    {{ v, ⌜v = LitV LitUnit⌝ ∗
      StackId li ↦ₛ qsort.nval (if mf_pair_leb q pivot then S i else i) ∗
      StackId lj ↦ₛ qsort.nval (S j) ∗
      mf_pair_arrays (if mf_pair_leb q pivot then mf_pair_swap pairs i j else pairs) oa ob }}.
Proof.
  iIntros (Hi Hj) "Hi Hj [Ha Hb]". unfold mf_partition_step.
  hm_take. hm_args. mf_load_stack "Hj". hm_args.
  iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp with "Ha"). by rewrite list_lookup_fmap Hj. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin.
  hm_take. hm_args. mf_load_stack "Hj". hm_args.
  iApply (wp_wand with "[Hb]").
  { iApply (mf_get_value_wp with "Hb"). by rewrite list_lookup_fmap Hj. }
  iIntros (v) "[%Hv Hb]". subst v. iApply wp_let. simpl.
  hm_take.
  match goal with |- context [If ?c ?t ?f] => iApply (wp_bind [IfCtx t f]) end.
  iApply (wp_wand with "[]"). { iApply (mf_lex_compare_wp q pivot). }
  iIntros (v) "%Hv". subst v. destruct (mf_pair_leb q pivot) eqn:Hcmp.
  - iApply wp_if_true. hm_take. hm_args.
    mf_load_stack "Hi". hm_args. mf_load_stack "Hj". hm_args.
    iApply (wp_wand with "[Ha Hb]").
    { iApply (mf_swap_pairs_wp with "[Ha Hb]"); [exact Hi|exact Hj|]. iFrame. }
    iIntros (v) "[%Hv Hpairs]". subst v. hm_admin.
    iApply (mf_increment_wp with "Hi"). iIntros "Hi". hm_admin.
    iApply (mf_increment_wp with "Hj"). iIntros "Hj". iFrame. done.
  - iApply wp_if_false. hm_admin.
    iApply (mf_increment_wp with "Hj"). iIntros "Hj".
    iFrame. unfold mf_pair_arrays. iFrame. done.
Qed.

(** Extract the loop directly from the emitted partition term, so the step
    theorem is linked to the implementation rather than a separate program. *)
Definition mf_partition_loop_body : expr :=
  match mf_partition_body with
  | Let _ _ (Let _ _ (Let _ _ (Let _ _ (Let _ _ (Let _ _
      (VarBind _ _ (VarBind _ _ (Let _ (While _ body) _)))))))) => body
  | _ => Val (LitV LitUnit)
  end.

Lemma mf_partition_step_is_code oa ob pivot li lj :
  subst_var "j" lj (subst_var "i" li
    (subst "pi" (LitV (LitInt (Z.of_nat (snd pivot))))
      (subst "pv" (LitV (LitInt (fst pivot)))
        (subst "indices" (LitV (LitObj ob))
          (subst "values" (LitV (LitObj oa)) mf_partition_loop_body))))) =
  mf_partition_step oa ob pivot li lj.
Proof.
  unfold mf_partition_loop_body, mf_partition_body, mf_partition_step,
    mf_lex_compare, qsort.sload, qsort.sset, qsort.slot, qsort.plus1, qsort.one.
  reflexivity.
Qed.

Definition mf_partition_scan oa ob (hi : nat) pivot li lj : expr :=
  While (BinOp LeOp (qsort.plus1 (qsort.sload lj))
      (qsort.minus1 (Val (qsort.nval hi))))
    (mf_partition_step oa ob pivot li lj).

Lemma mf_partition_scan_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    n oa ob hi pivot li lj pairs i j :
  (0 < hi)%nat -> ((hi - 1) - j = n)%nat ->
  (i <= j)%nat -> (j <= hi - 1)%nat -> (hi - 1 < length pairs)%nat ->
  StackId li ↦ₛ qsort.nval i -∗ StackId lj ↦ₛ qsort.nval j -∗
  mf_pair_arrays pairs oa ob -∗
  WP mf_partition_scan oa ob hi pivot li lj
    {{ _, ∃ ys p, ⌜mf_lomuto n pairs pivot i j (hi - 1)%nat = (ys,p)⌝ ∗
      StackId li ↦ₛ qsort.nval p ∗ StackId lj ↦ₛ qsort.nval (hi - 1) ∗
      mf_pair_arrays ys oa ob }}.
Proof.
  intros Hhi. revert pairs i j.
  induction n as [|n IH]; intros pairs i j Hfuel Hij Hj Hlen.
  - assert (j = hi - 1)%nat as -> by lia.
    iIntros "Hi Hj Hpairs".
    unfold mf_partition_scan, qsort.plus1, qsort.minus1, qsort.sload,
      qsort.slot, qsort.one, qsort.nval, qsort.zval. iApply wp_while.
    mf_load_stack "Hj". hm_pure.
    rewrite bool_decide_eq_false_2; [|lia].
    iApply wp_if_false. iApply wp_value'.
    iExists pairs, i. simpl. iFrame. done.
  - assert (j < hi - 1)%nat as Hjb by lia.
    destruct (lookup_lt_is_Some_2 pairs i) as [p Hp]; [lia|].
    destruct (lookup_lt_is_Some_2 pairs j) as [q Hq]; [lia|].
    iIntros "Hi Hj Hpairs".
    remember (mf_lomuto (S n) pairs pivot i j (hi - 1)%nat) as spec eqn:Hspec.
    unfold mf_partition_scan, qsort.plus1, qsort.minus1, qsort.sload,
      qsort.slot, qsort.one, qsort.nval, qsort.zval. iApply wp_while.
    mf_load_stack "Hj". hm_pure.
    rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
    match goal with |- context [Seq ?e ?k] => iApply (wp_bind [SeqCtx k]) end.
    iApply (wp_wand with "[Hi Hj Hpairs]").
    { iApply (mf_partition_step_wp with "Hi Hj Hpairs"); [exact Hp|exact Hq]. }
    iIntros (v) "(%Hv & Hi & Hj & Hpairs)". subst v. iApply wp_seq.
    destruct (mf_pair_leb q pivot) eqn:Hcmp.
    + assert (spec =
        mf_lomuto n (mf_pair_swap pairs i j) pivot (S i) (S j) (hi - 1)%nat) as Heq.
      { rewrite Hspec. simpl. assert (Nat.ltb j (hi - 1)%nat = true) as -> by (apply Nat.ltb_lt; lia).
        rewrite Hq Hcmp. done. }
      rewrite Heq.
      iApply (IH (mf_pair_swap pairs i j) (S i) (S j) with "Hi Hj Hpairs"); try lia.
      rewrite (Permutation_length (mf_pair_swap_perm pairs i j)). exact Hlen.
    + assert (spec =
        mf_lomuto n pairs pivot i (S j) (hi - 1)%nat) as Heq.
      { rewrite Hspec. simpl. assert (Nat.ltb j (hi - 1)%nat = true) as -> by (apply Nat.ltb_lt; lia).
        rewrite Hq Hcmp. done. }
      rewrite Heq. iApply (IH pairs i (S j) with "Hi Hj Hpairs"); lia.
Qed.

Definition mf_partition_loop : expr :=
  match mf_partition_body with
  | Let _ _ (Let _ _ (Let _ _ (Let _ _ (Let _ _ (Let _ _
      (VarBind _ _ (VarBind _ _ (Let _ loop _)))))))) => loop
  | _ => Val (LitV LitUnit)
  end.

Lemma mf_partition_scan_is_code oa ob hi pivot li lj :
  subst_var "j" lj (subst_var "i" li
    (subst "hi" (qsort.nval hi)
      (subst "pi" (LitV (LitInt (Z.of_nat (snd pivot))))
        (subst "pv" (LitV (LitInt (fst pivot)))
          (subst "indices" (LitV (LitObj ob))
            (subst "values" (LitV (LitObj oa)) mf_partition_loop)))))) =
  mf_partition_scan oa ob hi pivot li lj.
Proof.
  unfold mf_partition_loop, mf_partition_body, mf_partition_scan, mf_partition_step,
    mf_lex_compare, qsort.sload, qsort.sset, qsort.slot, qsort.plus1,
    qsort.minus1, qsort.one, qsort.nval, qsort.zval. reflexivity.
Qed.

Lemma mf_lomuto_bounds fuel pairs pivot i j bound :
  (i <= j)%nat -> (j <= bound)%nat ->
  (i <= snd (mf_lomuto fuel pairs pivot i j bound) <= bound)%nat.
Proof.
  revert pairs i j. induction fuel as [|fuel IH]; intros pairs i j Hij Hj; simpl; [lia|].
  destruct (Nat.ltb j bound) eqn:Hlt; [apply Nat.ltb_lt in Hlt|simpl; lia].
  destruct (pairs !! j) as [q|]; [|simpl; lia].
  destruct (mf_pair_leb q pivot).
  - pose proof (IH (mf_pair_swap pairs i j) (S i) (S j) ltac:(lia) ltac:(lia)). lia.
  - apply IH; lia.
Qed.

Lemma mf_partition_bounds pairs lo hi :
  (lo < hi)%nat -> (hi <= length pairs)%nat ->
  (lo <= snd (mf_partition pairs lo hi) < hi)%nat.
Proof.
  intros Hlo Hhi. unfold mf_partition.
  destruct (lookup_lt_is_Some_2 pairs (hi - 1)%nat) as [pivot Hp]; [lia|]. rewrite Hp.
  pose proof (mf_lomuto_bounds ((hi - 1) - lo)%nat pairs pivot lo lo (hi - 1)%nat
    ltac:(lia) ltac:(lia)) as H.
  destruct (mf_lomuto ((hi - 1) - lo)%nat pairs pivot lo lo (hi - 1)%nat) as [ys p]. simpl in *. lia.
Qed.

Definition mf_call_partition oa ob (lo hi : nat) : expr :=
  App (Val (RecV None (Some "args") mf_partition_body))
    (Val (StructV [LitV (LitObj oa); LitV (LitObj ob); qsort.nval lo; qsort.nval hi])).

Lemma mf_partition_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} pairs oa ob lo hi :
  (lo < hi)%nat -> (hi <= length pairs)%nat ->
  mf_pair_arrays pairs oa ob -∗
  WP mf_call_partition oa ob lo hi
    {{ v, ∃ ys p, ⌜mf_partition pairs lo hi = (ys,p)⌝ ∗
       ⌜v = qsort.nval p⌝ ∗ mf_pair_arrays ys oa ob }}.
Proof.
  iIntros (Hlo Hlen) "[Ha Hb]".
  destruct (lookup_lt_is_Some_2 pairs (hi - 1)%nat) as [pivot Hpivot]; [lia|].
  unfold mf_call_partition. iApply wp_app. unfold mf_partition_body. hm_admin.
  hm_take. hm_args. replace (Z.of_nat hi - 1)%Z with (Z.of_nat (hi - 1)) by lia.
  iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp with "Ha"). by rewrite list_lookup_fmap Hpivot. }
  iIntros (v) "[%Hv Ha]". subst v. hm_admin.
  hm_take. hm_args. replace (Z.of_nat hi - 1)%Z with (Z.of_nat (hi - 1)) by lia.
  iApply (wp_wand with "[Hb]").
  { iApply (mf_get_value_wp with "Hb"). by rewrite list_lookup_fmap Hpivot. }
  iIntros (v) "[%Hv Hb]". subst v. hm_admin.
  iApply wp_var_bind. iIntros (li) "Hi". simpl.
  iApply wp_var_bind. iIntros (lj) "Hj". simpl.
  match goal with |- envs_entails ?Δ (WP ?e {{ ?Φ }}) =>
    change (envs_entails Δ (WP (Let None (mf_partition_scan oa ob hi pivot li lj)
      (Let None (App (Rec None (Some "args") mf_swap_body)
        (Struct [] [Val (LitV (LitObj oa)); Val (LitV (LitObj ob)); qsort.sload li;
          qsort.minus1 (Val (qsort.nval hi))])) (qsort.sload li))) {{ Φ }}))
  end.
  hm_take. iApply (wp_wand with "[Hi Hj Ha Hb]").
  { iApply (mf_partition_scan_wp ((hi - 1) - lo)%nat oa ob hi pivot li lj pairs lo lo
      with "Hi Hj [Ha Hb]"); try lia. unfold mf_pair_arrays. iFrame. }
  iIntros (v) "Hscan". iDestruct "Hscan" as (ys p) "(%Hlom & Hi & Hj & Hpairs)".
  pose proof (mf_lomuto_bounds ((hi - 1) - lo)%nat pairs pivot lo lo (hi - 1)%nat
    ltac:(lia) ltac:(lia)) as Hbound.
  rewrite Hlom in Hbound. simpl in Hbound.
  pose proof (mf_lomuto_perm ((hi - 1) - lo)%nat pairs pivot lo lo (hi - 1)%nat) as Hperm.
  rewrite Hlom in Hperm. simpl in Hperm.
  assert (length ys = length pairs) as Hlength by (apply Permutation_length; exact Hperm).
  destruct (lookup_lt_is_Some_2 ys p) as [pval Hpval]; [lia|].
  destruct (lookup_lt_is_Some_2 ys (hi - 1)%nat) as [qval Hqval]; [lia|].
  iApply wp_let. simpl. hm_take. hm_args.
  unfold qsort.sload, qsort.slot, qsort.minus1, qsort.one, qsort.nval, qsort.zval.
  mf_load_stack "Hi". hm_args.
  replace (Z.of_nat hi - 1)%Z with (Z.of_nat (hi - 1)) by lia.
  iApply (wp_wand with "[Hpairs]").
  { iApply (mf_swap_pairs_wp with "Hpairs"); [exact Hpval|exact Hqval]. }
  iIntros (u) "[%Hu Hpairs]". subst u. hm_admin.
  iApply (wp_stack_load with "Hi"). iIntros "!> _ Hi".
  iExists (qsort.nval (hi - 1)). iFrame "Hj".
  iExists (qsort.nval p). iFrame "Hi".
  iExists (mf_pair_swap ys p (hi - 1)), p.
  iSplit. { iPureIntro. unfold mf_partition. rewrite Hpivot Hlom. done. }
  iFrame. done.
Qed.

Definition mf_call_qsort oa ob (lo hi : nat) : expr :=
  App (Val (RecV (Some "pairQsort") (Some "args") mf_qsort_body))
    (Val (StructV [LitV (LitObj oa); LitV (LitObj ob); qsort.nval lo; qsort.nval hi])).

Lemma mf_qsort_slice_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} fuel oa ob pairs lo hi :
  (lo <= hi)%nat -> (hi <= length pairs)%nat -> (hi - lo <= fuel)%nat ->
  mf_pair_arrays pairs oa ob -∗
  WP mf_call_qsort oa ob lo hi
    {{ v, ⌜v = LitV LitUnit⌝ ∗ mf_pair_arrays (mf_qsort_slice fuel pairs lo hi) oa ob }}.
Proof.
  revert pairs lo hi. induction fuel as [|fuel IH]; intros pairs lo hi Hlo Hhi Hfuel.
  - assert (lo = hi) as -> by lia.
    iIntros "Hpairs". unfold mf_call_qsort. iApply wp_app. unfold mf_qsort_body. hm_admin.
    rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_admin. iFrame. done.
  - iIntros "Hpairs".
    remember (mf_qsort_slice (S fuel) pairs lo hi) as result eqn:Hresult.
    unfold mf_call_qsort. iApply wp_app. unfold mf_qsort_body. hm_admin.
    destruct (Nat.leb hi (lo + 1)%nat) eqn:Hstop.
    + pose proof (proj1 (Nat.leb_le hi (lo + 1)%nat) Hstop) as Hshort.
      rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. hm_admin.
      assert (result = pairs) as ->.
      { rewrite Hresult. simpl. rewrite Hstop. done. }
      iFrame. done.
    + assert (lo + 1 < hi)%nat as Hlong by (apply Nat.leb_gt; exact Hstop).
      rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
      hm_take. hm_args. iApply (wp_wand with "[Hpairs]").
      { iApply (mf_partition_wp with "Hpairs"); lia. }
      iIntros (v) "Hpart". iDestruct "Hpart" as (ys p) "(%Hpart & %Hv & Hpairs)".
      subst v.
      pose proof (mf_partition_bounds pairs lo hi ltac:(lia) Hhi) as Hbounds.
      rewrite Hpart in Hbounds. simpl in Hbounds.
      pose proof (mf_partition_perm pairs lo hi) as Hperm.
      rewrite Hpart in Hperm. simpl in Hperm.
      assert (length ys = length pairs) as Hlength by (apply Permutation_length; exact Hperm).
      assert (result = mf_qsort_slice fuel (mf_qsort_slice fuel ys lo p) (S p) hi) as Hnew.
      { rewrite Hresult. simpl. rewrite Hstop Hpart. done. }
      iApply wp_let. simpl. hm_take. hm_args.
      iApply (wp_wand with "[Hpairs]").
      { iApply (IH ys lo p with "Hpairs"); lia. }
      iIntros (v) "[%Hv Hpairs]". subst v. iApply wp_let. simpl. hm_args.
      replace (Z.of_nat p + 1)%Z with (Z.of_nat (S p)) by lia.
      assert (length (mf_qsort_slice fuel ys lo p) = length pairs) as Hlength1.
      { rewrite (Permutation_length (mf_qsort_slice_perm fuel ys lo p)). exact Hlength. }
      rewrite Hnew. iApply (IH (mf_qsort_slice fuel ys lo p) (S p) hi with "Hpairs"); lia.
Qed.

Theorem mf_qsort_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} pairs oa ob :
  mf_pair_arrays pairs oa ob -∗
  WP mf_call_qsort oa ob 0%nat (length pairs)
    {{ v, ⌜v = LitV LitUnit⌝ ∗ mf_pair_arrays (mf_qsort pairs) oa ob }}.
Proof.
  iIntros "Hpairs". unfold mf_qsort.
  iApply (mf_qsort_slice_wp (length pairs) with "Hpairs"); lia.
Qed.

(** * Copying the input and recording its original indices *)
Definition mf_copy_values (xs : list Z) j := take j xs ++ replicate (length xs - j) 0%Z.
Definition mf_copy_indices n j := (Z.of_nat <$> seq 0 j) ++ replicate (n-j) 0%Z.

Lemma mf_copy_values_length xs j : (j <= length xs)%nat -> length (mf_copy_values xs j) = length xs.
Proof. intros Hj. unfold mf_copy_values. rewrite length_app length_take_le; [|done]. rewrite length_replicate. lia. Qed.
Lemma mf_copy_indices_length n j : (j <= n)%nat -> length (mf_copy_indices n j) = n.
Proof. intros Hj. unfold mf_copy_indices. rewrite length_app length_fmap length_seq length_replicate. lia. Qed.
Lemma mf_copy_values_lookup xs j : (j < length xs)%nat -> mf_copy_values xs j !! j = Some 0%Z.
Proof. intros Hj. unfold mf_copy_values. rewrite lookup_app_r length_take_le; try lia. replace (j-j)%nat with 0%nat by lia. apply lookup_replicate_2. lia. Qed.
Lemma mf_copy_indices_lookup n j : (j<n)%nat -> mf_copy_indices n j !! j = Some 0%Z.
Proof. intros Hj. unfold mf_copy_indices. rewrite lookup_app_r length_fmap length_seq; try lia. replace (j-j)%nat with 0%nat by lia. apply lookup_replicate_2. lia. Qed.
Lemma mf_copy_values_insert xs j x : xs !! j = Some x ->
  <[j:=x]> (mf_copy_values xs j) = mf_copy_values xs (S j).
Proof.
  intros Hx. pose proof (lookup_lt_Some xs j x Hx) as Hj.
  unfold mf_copy_values. rewrite insert_app_r_alt length_take_le; try lia.
  replace (j-j)%nat with 0%nat by lia.
  replace (length xs-j)%nat with (S (length xs-S j)) by lia. simpl.
  rewrite (take_S_r xs j x Hx). rewrite <- app_assoc. done.
Qed.
Lemma mf_copy_indices_insert n j : (j<n)%nat ->
  <[j:=Z.of_nat j]> (mf_copy_indices n j) = mf_copy_indices n (S j).
Proof.
  intros Hj. unfold mf_copy_indices. rewrite insert_app_r_alt length_fmap length_seq; try lia.
  replace (j-j)%nat with 0%nat by lia. replace (n-j)%nat with (S (n-S j)) by lia.
  rewrite seq_S fmap_app. simpl. rewrite <- app_assoc. done.
Qed.
Lemma mf_pairs_indices xs offset : snd <$> mf_pairs xs offset = seq offset (length xs).
Proof. revert offset. induction xs as [|x xs IH]; intros offset; [done|].
  change (offset :: (snd <$> mf_pairs xs (S offset)) = offset :: seq (S offset) (length xs)). rewrite IH. done. Qed.
Lemma mf_copy_complete xs :
  mf_copy_values xs (length xs) = fst <$> mf_pairs xs 0%nat /\
  mf_copy_indices (length xs) (length xs) = (Z.of_nat ∘ snd) <$> mf_pairs xs 0%nat.
Proof.
  unfold mf_copy_values, mf_copy_indices. rewrite Nat.sub_diag /= !app_nil_r take_ge; [|lia].
  rewrite mf_pairs_values. split; [done|]. rewrite list_fmap_compose. rewrite mf_pairs_indices. done.
Qed.

Definition mf_copy_step oi oa ob lc : expr :=
  Let None (App (Rec None (Some "args") array.set_body)
    (Struct [] [Val (LitV (LitObj oa)); qsort.sload lc;
      App (Rec None (Some "args") array.get_body)
        (Struct [] [Val (LitV (LitObj oi)); qsort.sload lc])]))
  (Let None (App (Rec None (Some "args") array.set_body)
    (Struct [] [Val (LitV (LitObj ob)); qsort.sload lc; qsort.sload lc]))
    (qsort.sset lc (qsort.plus1 (qsort.sload lc)))).

Lemma mf_copy_step_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs oi oa ob lc j :
  (j < length xs)%nat ->
  StackId lc ↦ₛ qsort.nval j -∗ is_array xs (LitV (LitObj oi)) -∗
  is_array (mf_copy_values xs j) (LitV (LitObj oa)) -∗
  is_array (mf_copy_indices (length xs) j) (LitV (LitObj ob)) -∗
  WP mf_copy_step oi oa ob lc
    {{ v, ⌜v = LitV LitUnit⌝ ∗ StackId lc ↦ₛ qsort.nval (S j) ∗
       is_array xs (LitV (LitObj oi)) ∗
       is_array (mf_copy_values xs (S j)) (LitV (LitObj oa)) ∗
       is_array (mf_copy_indices (length xs) (S j)) (LitV (LitObj ob)) }}.
Proof.
  intros Hj. destruct (lookup_lt_is_Some_2 xs j Hj) as [x Hx].
  iIntros "Hc Hi Ha Hb". unfold mf_copy_step.
  hm_take. hm_args. unfold qsort.sload, qsort.slot.
  mf_load_stack "Hc". hm_args. mf_load_stack "Hc". hm_args.
  iApply (wp_wand with "[Hi]").
  { iApply (mf_get_value_wp with "Hi"). exact Hx. }
  iIntros (v) "[%Hv Hi]". subst v. hm_args.
  iApply (wp_wand with "[Ha]").
  { iApply (mf_set_value_wp with "Ha"). apply mf_copy_values_lookup. exact Hj. }
  iIntros (v) "[%Hv Ha]". subst v.
  rewrite (mf_copy_values_insert xs j x Hx). iApply wp_let. simpl.
  hm_take. hm_args. mf_load_stack "Hc". hm_args. mf_load_stack "Hc". hm_args.
  iApply (wp_wand with "[Hb]").
  { iApply (mf_set_value_wp with "Hb"). apply mf_copy_indices_lookup. exact Hj. }
  iIntros (v) "[%Hv Hb]". subst v.
  rewrite (mf_copy_indices_insert (length xs) j Hj). iApply wp_let. simpl.
  iApply (mf_increment_wp with "Hc"). iIntros "Hc". iFrame. done.
Qed.

Definition mf_copy_loop oi oa ob n lc : expr :=
  While (BinOp LeOp (qsort.plus1 (qsort.sload lc)) (Val (qsort.nval n)))
    (mf_copy_step oi oa ob lc).

Lemma mf_copy_loop_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    fuel xs oi oa ob lc j :
  (j <= length xs)%nat -> (length xs-j = fuel)%nat ->
  StackId lc ↦ₛ qsort.nval j -∗ is_array xs (LitV (LitObj oi)) -∗
  is_array (mf_copy_values xs j) (LitV (LitObj oa)) -∗
  is_array (mf_copy_indices (length xs) j) (LitV (LitObj ob)) -∗
  WP mf_copy_loop oi oa ob (length xs) lc
    {{ _, StackId lc ↦ₛ qsort.nval (length xs) ∗ is_array xs (LitV (LitObj oi)) ∗
       mf_pair_arrays (mf_pairs xs 0%nat) oa ob }}.
Proof.
  revert j. induction fuel as [|fuel IH]; intros j Hj Hfuel.
  - assert (j = length xs) as -> by lia.
    iIntros "Hc Hi Ha Hb". unfold mf_copy_loop, qsort.plus1, qsort.sload,
      qsort.slot, qsort.one, qsort.nval, qsort.zval. iApply wp_while.
    mf_load_stack "Hc". hm_pure. rewrite bool_decide_eq_false_2; [|lia].
    iApply wp_if_false. iApply wp_value'.
    destruct (mf_copy_complete xs) as [Hv Hidx]. rewrite Hv Hidx.
    unfold mf_pair_arrays. iFrame.
  - assert (j < length xs) as Hlt by lia.
    iIntros "Hc Hi Ha Hb". unfold mf_copy_loop, qsort.plus1, qsort.sload,
      qsort.slot, qsort.one, qsort.nval, qsort.zval. iApply wp_while.
    mf_load_stack "Hc". hm_pure. rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
    match goal with |- context [Seq ?e ?k] => iApply (wp_bind [SeqCtx k]) end.
    iApply (wp_wand with "[Hc Hi Ha Hb]").
    { iApply (mf_copy_step_wp with "Hc Hi Ha Hb"). exact Hlt. }
    iIntros (v) "(%Hv & Hc & Hi & Ha & Hb)". subst v. iApply wp_seq.
    iApply (IH (S j) with "Hc Hi Ha Hb"); lia.
Qed.

Definition mf_copy_code : expr :=
  match mf_body with
  | Let _ _ (If _ _ (Let _ _ (Let _ _ (Let _ (VarBind _ _ loop) _)))) => loop
  | _ => Val (LitV LitUnit)
  end.

Lemma mf_copy_loop_is_code oi oa ob n lc :
  subst_var "copyAt" lc (subst "n" (qsort.nval n)
    (subst "indices" (LitV (LitObj ob)) (subst "values" (LitV (LitObj oa))
      (subst "input" (LitV (LitObj oi)) mf_copy_code)))) = mf_copy_loop oi oa ob n lc.
Proof. unfold mf_copy_code, mf_body, mf_copy_loop, mf_copy_step, qsort.sload,
  qsort.sset, qsort.slot, qsort.plus1, qsort.one, qsort.nval, qsort.zval. reflexivity. Qed.

(** * Concrete run scan and full operation refinement *)
Fixpoint mf_scan_run (value : Z) (first : nat) (pairs : list mf_pair) : nat * nat :=
  match pairs with
  | [] => (0%nat, first)
  | p :: ps => if Z.eq_dec (fst p) value then
      let '(count, minimum) := mf_scan_run value (Nat.min first (snd p)) ps in
      (S count, minimum)
    else (0%nat, first)
  end.

Lemma mf_scan_run_bound value first pairs :
  (fst (mf_scan_run value first pairs) <= length pairs)%nat.
Proof.
  revert first. induction pairs as [|p ps IH]; intros first; simpl; [lia|].
  destruct (Z.eq_dec (fst p) value); [|simpl; lia].
  specialize (IH (Nat.min first (snd p))). destruct (mf_scan_run value (Nat.min first (snd p)) ps). simpl in *. lia.
Qed.

Definition mf_group_inner oa ob n value le lf : expr :=
  While (If (BinOp LeOp (qsort.plus1 (qsort.sload le)) (Val (qsort.nval n)))
    (BinOp EqOp (App (Rec None (Some "args") array.get_body)
      (Struct [] [Val (LitV (LitObj oa)); qsort.sload le])) (Val (LitV (LitInt value))))
    (Val (LitV (LitBool false))))
    (Let (Some "ix") (App (Rec None (Some "args") array.get_body)
      (Struct [] [Val (LitV (LitObj ob)); qsort.sload le]))
      (Let None (If (BinOp LeOp (qsort.plus1 (Var "ix")) (qsort.sload lf))
        (qsort.sset lf (Var "ix")) (Val (LitV LitUnit)))
        (qsort.sset le (qsort.plus1 (qsort.sload le))))).

Lemma mf_group_inner_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    suffix pairs oa ob le lf value j first :
  drop j pairs = suffix -> (j <= length pairs)%nat ->
  StackId le ↦ₛ qsort.nval j -∗ StackId lf ↦ₛ qsort.nval first -∗
  mf_pair_arrays pairs oa ob -∗
  WP mf_group_inner oa ob (length pairs) value le lf
    {{ _, StackId le ↦ₛ qsort.nval (j + fst (mf_scan_run value first suffix))%nat ∗
      StackId lf ↦ₛ qsort.nval (snd (mf_scan_run value first suffix)) ∗
      mf_pair_arrays pairs oa ob }}.
Proof.
  revert j first. induction suffix as [|p ps IH]; intros j first Hsuffix Hj.
  - assert (j = length pairs) as ->.
    { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
    iIntros "He Hf Hpairs". simpl.
    unfold mf_group_inner, qsort.plus1, qsort.sload, qsort.slot, qsort.one, qsort.nval, qsort.zval.
    iApply wp_while. mf_load_stack "He". hm_pure.
    rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. iApply wp_value'.
    iApply wp_if_false. iApply wp_value'. replace (length pairs + 0)%nat with (length pairs) by lia. iFrame.
  - assert (j < length pairs) as Hlt.
    { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
    assert (pairs !! j = Some p) as Hp.
    { pose proof (f_equal (fun xs => xs !! 0%nat) Hsuffix) as Hlookup.
      rewrite lookup_drop in Hlookup. simpl in Hlookup. rewrite Nat.add_0_r in Hlookup. exact Hlookup. }
    assert (drop (S j) pairs = ps) as Hps.
    { pose proof (f_equal (drop 1%nat) Hsuffix) as Hdrop.
      rewrite drop_drop in Hdrop. simpl in Hdrop. replace (j+1)%nat with (S j) in Hdrop by lia. rewrite drop_0 in Hdrop. exact Hdrop. }
    iIntros "He Hf Hpairs".
    remember (mf_scan_run value first (p::ps)) as result eqn:Hresult.
    unfold mf_group_inner, qsort.plus1, qsort.sload, qsort.slot, qsort.one, qsort.nval, qsort.zval.
    iApply wp_while. mf_load_stack "He". hm_pure.
    rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
    hm_args. mf_load_stack "He". hm_args.
    iDestruct "Hpairs" as "[Ha Hb]".
    iApply (wp_wand with "[Ha]").
    { iApply (mf_get_value_wp with "Ha"). rewrite list_lookup_fmap Hp. done. }
    iIntros (v) "[%Hv Ha]". subst v. hm_admin.
    destruct (Z.eq_dec (fst p) value) as [Heq|Hneq].
    + rewrite bool_decide_eq_true_2; [|f_equal; exact Heq]. iApply wp_if_true.
      match goal with |- context [Seq ?e ?k] => iApply (wp_bind [SeqCtx k]) end.
      hm_take. hm_args. mf_load_stack "He". hm_args.
      iApply (wp_wand with "[Hb]").
      { iApply (mf_get_value_wp with "Hb"). rewrite list_lookup_fmap Hp. done. }
      iIntros (v) "[%Hv Hb]". subst v. iApply wp_let. simpl.
      hm_take. hm_admin. unfold qsort.sload, qsort.slot. mf_load_stack "Hf". hm_admin.
      destruct (Nat.lt_ge_cases (snd p) first) as [Hmin|Hmin].
      * rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
        iApply (wp_stack_assign with "Hf"). iIntros "!> _ Hf".
        iApply wp_let. simpl. iApply (mf_increment_wp with "He"). iIntros "He".
        iApply wp_seq.
        rewrite Hresult /=. destruct (Z.eq_dec (fst p) value); [|contradiction].
        rewrite Nat.min_r; [|lia].
        destruct (mf_scan_run value (snd p) ps) as [count minimum] eqn:Hscan. simpl.
        replace (j + S count)%nat with (S j + count)%nat by lia.
        specialize (IH (S j) (snd p) Hps ltac:(lia)). rewrite Hscan /= in IH.
        iApply (IH with "He Hf [Ha Hb]"). unfold mf_pair_arrays. iFrame.
      * rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false.
        hm_admin. iApply (mf_increment_wp with "He"). iIntros "He".
        iApply wp_seq. rewrite Hresult /=. destruct (Z.eq_dec (fst p) value); [|contradiction].
        rewrite Nat.min_l; [|lia].
        destruct (mf_scan_run value first ps) as [count minimum] eqn:Hscan. simpl.
        replace (j + S count)%nat with (S j + count)%nat by lia.
        specialize (IH (S j) first Hps ltac:(lia)). rewrite Hscan /= in IH.
        iApply (IH with "He Hf [Ha Hb]"). unfold mf_pair_arrays. iFrame.
    + rewrite bool_decide_eq_false_2; [|intros Heq; inversion Heq; contradiction]. iApply wp_if_false.
      iApply wp_value'. rewrite Hresult /=. destruct (Z.eq_dec (fst p) value); [contradiction|]. simpl.
      replace (j+0)%nat with j by lia. unfold mf_pair_arrays. iFrame.
Qed.

Fixpoint mf_find_group_loop (e : expr) : expr :=
  match e with
  | Let None (While guard body) _ => While guard body
  | Let _ _ rest | VarBind _ _ rest => mf_find_group_loop rest
  | If _ _ nonempty => mf_find_group_loop nonempty
  | _ => Val (LitV LitUnit)
  end.
Definition mf_group_inner_code : expr :=
  match mf_find_group_loop mf_body with
  | While _ (Let _ _ (VarBind _ _ (VarBind _ _ (Let _ loop _)))) => loop
  | _ => Val (LitV LitUnit)
  end.
Lemma mf_group_inner_is_code oa ob n value le lf :
  subst_var "first" lf (subst_var "end" le
    (subst "value" (LitV (LitInt value)) (subst "n" (qsort.nval n)
      (subst "indices" (LitV (LitObj ob)) (subst "values" (LitV (LitObj oa))
        mf_group_inner_code))))) = mf_group_inner oa ob n value le lf.
Proof.
  unfold mf_group_inner_code, mf_body, mf_group_inner, qsort.sload,
    qsort.sset, qsort.slot, qsort.plus1, qsort.one, qsort.nval, qsort.zval. reflexivity.
Qed.

Definition mf_merge_summary (a b : mf_summary) : mf_summary :=
  (fst a, ((mf_summary_count a + mf_summary_count b)%nat,
    Nat.min (mf_summary_first a) (mf_summary_first b))).
Definition mf_join_summary (a : mf_summary) (runs : list mf_summary) : list mf_summary :=
  match runs with
  | [] => [a]
  | b :: bs => if Z.eq_dec (fst a) (fst b)
      then mf_merge_summary a b :: bs else a :: runs
  end.
Lemma mf_run_summaries_cons p ps :
  mf_run_summaries (p::ps) = mf_join_summary (mf_single_summary p) (mf_run_summaries ps).
Proof.
  simpl. destruct (mf_run_summaries ps); [done|].
  unfold mf_join_summary, mf_merge_summary, mf_extend_summary, mf_single_summary,
    mf_summary_count, mf_summary_first. simpl. destruct (Z.eq_dec (fst p) (fst m)); done.
Qed.
Lemma mf_join_summary_same a b runs : fst a = fst b ->
  mf_join_summary a (mf_join_summary b runs) = mf_join_summary (mf_merge_summary a b) runs.
Proof.
  intros Heq. destruct runs as [|c cs]; unfold mf_join_summary, mf_merge_summary;
    unfold mf_summary_count, mf_summary_first; simpl.
  - destruct (Z.eq_dec (fst a) (fst b)); [done|contradiction].
  - destruct (Z.eq_dec (fst b) (fst c)) as [Hbc|Hbc];
      destruct (Z.eq_dec (fst a) (fst b)) as [Hab|Hab]; try contradiction;
      destruct (Z.eq_dec (fst a) (fst c)) as [Hac|Hac]; try congruence; simpl.
    + rewrite Nat.add_assoc Nat.min_assoc. destruct (Z.eq_dec (fst a) (fst b)); [done|contradiction].
Qed.

Lemma mf_scan_run_summaries value first count ps :
  let '(extra, minimum) := mf_scan_run value first ps in
  mf_join_summary (value,(count,first)) (mf_run_summaries ps) =
    (value,((count+extra)%nat, minimum)) :: mf_run_summaries (drop extra ps).
Proof.
  revert first count. induction ps as [|p ps IH]; intros first count.
  - simpl. rewrite Nat.add_0_r. done.
  - rewrite mf_run_summaries_cons. cbn [mf_scan_run].
    destruct (Z.eq_dec (fst p) value) as [Heq|Hneq].
    + rewrite mf_join_summary_same; [|unfold mf_single_summary; simpl; congruence].
      unfold mf_merge_summary, mf_single_summary, mf_summary_count, mf_summary_first.
      cbn [fst snd].
      specialize (IH (Nat.min first (snd p)) (S count)).
      destruct (mf_scan_run value (Nat.min first (snd p)) ps) as [extra minimum].
      simpl. replace (count+1)%nat with (S count) by lia.
      replace (count+S extra)%nat with (S count+extra)%nat by lia. exact IH.
    + destruct (mf_run_summaries_head p ps) as [s [rest [Hruns Hhead]]].
      rewrite <- mf_run_summaries_cons. rewrite Hruns.
      unfold mf_join_summary. simpl. destruct (Z.eq_dec value (fst s)); [congruence|].
      rewrite Nat.add_0_r. done.
Qed.

Lemma mf_group_summary_decomposition p ps :
  let '(extra, minimum) := mf_scan_run (fst p) (snd p) ps in
  mf_run_summaries (p::ps) =
    (fst p,(S extra,minimum)) :: mf_run_summaries (drop extra ps).
Proof.
  rewrite mf_run_summaries_cons. unfold mf_single_summary.
  pose proof (mf_scan_run_summaries (fst p) (snd p) 1%nat ps) as H.
  destruct (mf_scan_run (fst p) (snd p) ps). simpl in *. exact H.
Qed.

Definition mf_strict_better (p b : mf_summary) : bool :=
  Nat.ltb (mf_summary_count b) (mf_summary_count p) ||
  (Nat.eqb (mf_summary_count b) (mf_summary_count p) &&
    Nat.ltb (mf_summary_first p) (mf_summary_first b)).
Definition mf_update_best b p := if mf_strict_better p b then p else b.
Fixpoint mf_fold_best (runs : list mf_summary) (best : mf_summary) : mf_summary :=
  match runs with [] => best | p::ps => mf_fold_best ps (mf_update_best best p) end.
Lemma mf_strict_better_yes p b : mf_strict_better p b = true -> mf_score p b.
Proof.
  unfold mf_strict_better, mf_score.
  rewrite Bool.orb_true_iff Bool.andb_true_iff Nat.ltb_lt Nat.eqb_eq Nat.ltb_lt. intuition lia.
Qed.
Lemma mf_strict_better_no p b : mf_strict_better p b = false -> mf_score b p.
Proof.
  unfold mf_strict_better, mf_score.
  rewrite Bool.orb_false_iff Bool.andb_false_iff Nat.ltb_ge Nat.eqb_neq Nat.ltb_ge. intuition lia.
Qed.
Lemma mf_update_best_scores b p : mf_score (mf_update_best b p) b /\ mf_score (mf_update_best b p) p.
Proof.
  unfold mf_update_best. destruct (mf_strict_better p b) eqn:H.
  - split; [apply mf_strict_better_yes; done|apply mf_score_refl].
  - split; [apply mf_score_refl|apply mf_strict_better_no; done].
Qed.
Lemma mf_fold_best_sound runs best :
  In (mf_fold_best runs best) (best::runs) /\
  forall p, In p (best::runs) -> mf_score (mf_fold_best runs best) p.
Proof.
  revert best. induction runs as [|p ps IH]; intros best; simpl.
  - split; [by left|]. intros q [->|[]]. apply mf_score_refl.
  - specialize (IH (mf_update_best best p)). destruct IH as [Hmem Hmax]. split.
    + destruct Hmem as [Hmem|Hmem]; [|by right; right].
      rewrite <- Hmem. unfold mf_update_best. destruct (mf_strict_better p best); [by right; left|by left].
    + intros q [->|[->|Hq]].
      * eapply mf_score_trans; [apply Hmax; by left|apply mf_update_best_scores].
      * eapply mf_score_trans; [apply Hmax; by left|apply mf_update_best_scores].
      * apply Hmax. by right.
Qed.

Fixpoint mf_forward_scan fuel (pairs : list mf_pair) best : mf_summary :=
  match fuel with
  | O => best
  | S fuel' => match pairs with
    | [] => best
    | p::ps => let '(extra,minimum) := mf_scan_run (fst p) (snd p) ps in
      mf_forward_scan fuel' (drop extra ps)
        (mf_update_best best (fst p,(S extra,minimum)))
    end
  end.
Lemma mf_forward_scan_groups fuel pairs best :
  (length pairs <= fuel)%nat ->
  mf_forward_scan fuel pairs best = mf_fold_best (mf_run_summaries pairs) best.
Proof.
  revert pairs best. induction fuel as [|fuel IH]; intros pairs best Hlen.
  - destruct pairs; [done|simpl in Hlen; lia].
  - destruct pairs as [|p ps]; [done|]. simpl in Hlen.
    cbn [mf_forward_scan]. pose proof (mf_group_summary_decomposition p ps) as Hgroups.
    destruct (mf_scan_run (fst p) (snd p) ps) as [extra minimum].
    rewrite Hgroups. simpl. apply IH. rewrite length_drop. lia.
Qed.

Theorem mf_forward_scan_correct xs seed : xs <> [] -> mf_summary_count seed = 0%nat ->
  most_frequent_spec xs (Some (fst (mf_forward_scan (length xs) (mf_sorted_pairs xs) seed))).
Proof.
  intros Hnonempty Hseed.
  rewrite mf_forward_scan_groups; [|rewrite mf_sorted_pairs_length; lia].
  pose proof (mf_run_summaries_complete xs) as [Hvalid Hcomplete].
  pose proof (mf_fold_best_sound (mf_run_summaries (mf_sorted_pairs xs)) seed) as [Hmem Hmax].
  remember (mf_fold_best (mf_run_summaries (mf_sorted_pairs xs)) seed) as best.
  assert (In best (mf_run_summaries (mf_sorted_pairs xs))) as Hbest.
  { destruct Hmem as [Heq|Hmem]; [|done]. subst best.
    destruct xs as [|x xs]; [contradiction|].
    destruct (Hcomplete x (or_introl eq_refl)) as [s [Hs _]].
    pose proof (Hvalid s Hs) as [_ [_ Hpos]].
    pose proof (proj1 (Hmax s (or_intror Hs))) as Hle. rewrite <- Heq in Hle. rewrite Hseed in Hle. lia. }
  destruct (Hvalid best Hbest) as [Hcount [Hfirst Hpos]].
  assert (In (fst best) xs) as Hcontains.
  { apply mf_frequency_pos_mem. rewrite <- Hcount. exact Hpos. }
  destruct xs as [|a xs]; [done|].
  change ((mf_frequency (fst best) (a::xs) > 0)%nat /\
    (forall y, (mf_frequency y (a::xs) <= mf_frequency (fst best) (a::xs))%nat) /\
    (forall y, mf_frequency y (a::xs) = mf_frequency (fst best) (a::xs) ->
      mf_first_index_or_len (fst best) (a::xs) <= mf_first_index_or_len y (a::xs))%nat).
  split; [rewrite <- Hcount; done|]. split.
  - intros y. destruct (in_dec Z.eq_dec y (a::xs)) as [Hy|Hnot].
    + destruct (Hcomplete y Hy) as [s [Hs Hsy]].
      destruct (Hvalid s Hs) as [Hsc _].
      pose proof (proj1 (Hmax s (or_intror Hs))) as Hle. rewrite Hcount Hsc Hsy in Hle. done.
    + rewrite (mf_frequency_not_mem y (a::xs) Hnot). lia.
  - intros y Heq. assert (In y (a::xs)) as Hy.
    { apply mf_frequency_pos_mem. rewrite Heq. rewrite <- Hcount. done. }
    destruct (Hcomplete y Hy) as [s [Hs Hsy]].
    destruct (Hvalid s Hs) as [Hsc [Hsf _]].
    destruct (Hmax s (or_intror Hs)) as [_ Htie].
    rewrite <- Hfirst. rewrite <- Hsy, <- Hsf.
    apply Htie. rewrite Hsc Hcount Hsy. done.
Qed.

Definition mf_best_cells `{!cjrGS Σ} (best : mf_summary) lv lc lf : iProp Σ :=
  StackId lv ↦ₛ LitV (LitInt (fst best)) ∗
  StackId lc ↦ₛ qsort.nval (mf_summary_count best) ∗
  StackId lf ↦ₛ qsort.nval (mf_summary_first best).

Lemma mf_strict_better_case p b : mf_strict_better p b =
  if bool_decide (mf_summary_count b < mf_summary_count p)%nat then true
  else if bool_decide (mf_summary_count b = mf_summary_count p)
    then bool_decide (mf_summary_first p < mf_summary_first b)%nat else false.
Proof.
  unfold mf_strict_better.
  assert (forall a b : nat, Nat.ltb a b = bool_decide (a<b)) as Hlt.
  { intros u v. destruct (Nat.lt_ge_cases u v) as [H|H].
    - assert (Nat.ltb u v = true) as -> by (apply Nat.ltb_lt; done). rewrite bool_decide_eq_true_2; done.
    - assert (Nat.ltb u v = false) as -> by (apply Nat.ltb_ge; done). rewrite bool_decide_eq_false_2; [done|lia]. }
  assert (forall a b : nat, Nat.eqb a b = bool_decide (a=b)) as Heq.
  { intros u v. destruct (Nat.eq_dec u v) as [H|H].
    - assert (Nat.eqb u v = true) as -> by (apply Nat.eqb_eq; done). rewrite bool_decide_eq_true_2; done.
    - assert (Nat.eqb u v = false) as -> by (apply Nat.eqb_neq; done). rewrite bool_decide_eq_false_2; done. }
  rewrite !Hlt Heq. destruct (bool_decide (mf_summary_count b < mf_summary_count p)%nat);
    destruct (bool_decide (mf_summary_count b = mf_summary_count p)); done.
Qed.

Definition mf_best_decision p lc lf : expr :=
  If (BinOp LeOp (qsort.plus1 (qsort.sload lc)) (Val (qsort.nval (mf_summary_count p))))
    (Val (LitV (LitBool true)))
    (If (BinOp EqOp (qsort.sload lc) (Val (qsort.nval (mf_summary_count p))))
      (BinOp LeOp (qsort.plus1 (Val (qsort.nval (mf_summary_first p)))) (qsort.sload lf))
      (Val (LitV (LitBool false)))).
Lemma mf_best_decision_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} p best lc lf :
  StackId lc ↦ₛ qsort.nval (mf_summary_count best) -∗
  StackId lf ↦ₛ qsort.nval (mf_summary_first best) -∗
  WP mf_best_decision p lc lf
    {{ v, ⌜v = LitV (LitBool (mf_strict_better p best))⌝ ∗
      StackId lc ↦ₛ qsort.nval (mf_summary_count best) ∗
      StackId lf ↦ₛ qsort.nval (mf_summary_first best) }}.
Proof.
  iIntros "Hc Hf". unfold mf_best_decision, qsort.plus1, qsort.sload, qsort.slot,
    qsort.one, qsort.nval, qsort.zval.
  mf_load_stack "Hc". hm_admin.
  rewrite mf_strict_better_case.
  destruct (Nat.lt_ge_cases (mf_summary_count best) (mf_summary_count p)) as [Hlt|Hge].
  - rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true. iApply wp_value'.
    rewrite bool_decide_eq_true_2; [|done]. iFrame. done.
  - rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false.
    mf_load_stack "Hc". hm_admin.
    destruct (Nat.eq_dec (mf_summary_count best) (mf_summary_count p)) as [Heq|Hneq].
    + rewrite bool_decide_eq_true_2; [|f_equal; lia]. iApply wp_if_true.
      hm_admin. mf_load_stack "Hf". hm_admin.
      assert (bool_decide (mf_summary_count best < mf_summary_count p)%nat = false) as ->
        by (apply bool_decide_eq_false_2; lia).
      assert (bool_decide (mf_summary_count best = mf_summary_count p) = true) as ->
        by (apply bool_decide_eq_true_2; done).
      destruct (Nat.lt_ge_cases (mf_summary_first p) (mf_summary_first best)) as [Hfirstlt|Hfirstge].
      * rewrite !bool_decide_eq_true_2; try lia. iFrame. done.
      * rewrite !bool_decide_eq_false_2; try lia. iFrame. done.
    + rewrite bool_decide_eq_false_2; [|intros Heq; inversion Heq; lia]. iApply wp_if_false. iApply wp_value'.
      rewrite !bool_decide_eq_false_2; try lia. iFrame. done.
Qed.

Definition mf_best_update p lv lc lf : expr :=
  If (mf_best_decision p lc lf)
    (Let None (qsort.sset lv (Val (LitV (LitInt (fst p)))))
      (Let None (qsort.sset lc (Val (qsort.nval (mf_summary_count p))))
        (qsort.sset lf (Val (qsort.nval (mf_summary_first p))))))
    (Val (LitV LitUnit)).
Lemma mf_best_update_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} p best lv lc lf :
  mf_best_cells best lv lc lf -∗
  WP mf_best_update p lv lc lf
    {{ v, ⌜v = LitV LitUnit⌝ ∗ mf_best_cells (mf_update_best best p) lv lc lf }}.
Proof.
  iIntros "(Hv & Hc & Hf)". unfold mf_best_update.
  iApply (wp_bind [IfCtx _ _]). iApply (wp_wand with "[Hc Hf]").
  { iApply (mf_best_decision_wp with "Hc Hf"). }
  iIntros (v) "(%Heq & Hc & Hf)". subst v. unfold mf_update_best.
  destruct (mf_strict_better p best).
  - iApply wp_if_true. hm_take. iApply (wp_stack_assign with "Hv"). iIntros "!> _ Hv".
    iApply wp_let. simpl. hm_take. iApply (wp_stack_assign with "Hc"). iIntros "!> _ Hc".
    iApply wp_let. simpl. iApply (wp_stack_assign with "Hf"). iIntros "!> _ Hf".
    unfold mf_best_cells. iFrame. done.
  - iApply wp_if_false. iApply wp_value'. unfold mf_best_cells. iFrame. done.
Qed.

Definition mf_best_decision_slot p lc lf ls : expr :=
  If (BinOp LeOp (qsort.plus1 (qsort.sload lc)) (Val (qsort.nval (mf_summary_count p))))
    (Val (LitV (LitBool true)))
    (If (BinOp EqOp (qsort.sload lc) (Val (qsort.nval (mf_summary_count p))))
      (BinOp LeOp (qsort.plus1 (qsort.sload ls)) (qsort.sload lf))
      (Val (LitV (LitBool false)))).
Lemma mf_best_decision_slot_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} p best lc lf ls :
  StackId ls ↦ₛ qsort.nval (mf_summary_first p) -∗
  StackId lc ↦ₛ qsort.nval (mf_summary_count best) -∗
  StackId lf ↦ₛ qsort.nval (mf_summary_first best) -∗
  WP mf_best_decision_slot p lc lf ls
    {{ v, ⌜v = LitV (LitBool (mf_strict_better p best))⌝ ∗
      StackId lc ↦ₛ qsort.nval (mf_summary_count best) ∗
      StackId lf ↦ₛ qsort.nval (mf_summary_first best) ∗
      StackId ls ↦ₛ qsort.nval (mf_summary_first p) }}.
Proof.
  iIntros "Hs Hc Hf". unfold mf_best_decision_slot, qsort.plus1, qsort.sload, qsort.slot,
    qsort.one, qsort.nval, qsort.zval.
  mf_load_stack "Hc". hm_admin.
  rewrite mf_strict_better_case.
  destruct (Nat.lt_ge_cases (mf_summary_count best) (mf_summary_count p)) as [Hlt|Hge].
  - rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true. iApply wp_value'.
    rewrite bool_decide_eq_true_2; [|done]. iFrame. done.
  - rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false.
    mf_load_stack "Hc". hm_admin.
    destruct (Nat.eq_dec (mf_summary_count best) (mf_summary_count p)) as [Heq|Hneq].
    + rewrite bool_decide_eq_true_2; [|f_equal; lia]. iApply wp_if_true.
      mf_load_stack "Hs". hm_admin. mf_load_stack "Hf". hm_admin.
      assert (bool_decide (mf_summary_count best < mf_summary_count p)%nat = false) as ->
        by (apply bool_decide_eq_false_2; lia).
      assert (bool_decide (mf_summary_count best = mf_summary_count p) = true) as ->
        by (apply bool_decide_eq_true_2; done).
      destruct (Nat.lt_ge_cases (mf_summary_first p) (mf_summary_first best)) as [Hfirstlt|Hfirstge].
      * rewrite !bool_decide_eq_true_2; try lia. iFrame. done.
      * rewrite !bool_decide_eq_false_2; try lia. iFrame. done.
    + rewrite bool_decide_eq_false_2; [|intros Heq; inversion Heq; lia]. iApply wp_if_false. iApply wp_value'.
      rewrite !bool_decide_eq_false_2; try lia. iFrame. done.
Qed.

Definition mf_best_update_slot p lv lc lf ls : expr :=
  If (mf_best_decision_slot p lc lf ls)
    (Let None (qsort.sset lv (Val (LitV (LitInt (fst p)))))
      (Let None (qsort.sset lc (Val (qsort.nval (mf_summary_count p))))
        (qsort.sset lf (qsort.sload ls))))
    (Val (LitV LitUnit)).
Lemma mf_best_update_slot_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} p best lv lc lf ls :
  StackId ls ↦ₛ qsort.nval (mf_summary_first p) -∗ mf_best_cells best lv lc lf -∗
  WP mf_best_update_slot p lv lc lf ls
    {{ v, ⌜v = LitV LitUnit⌝ ∗ StackId ls ↦ₛ qsort.nval (mf_summary_first p) ∗
       mf_best_cells (mf_update_best best p) lv lc lf }}.
Proof.
  iIntros "Hs (Hv & Hc & Hf)". unfold mf_best_update_slot.
  iApply (wp_bind [IfCtx _ _]). iApply (wp_wand with "[Hs Hc Hf]").
  { iApply (mf_best_decision_slot_wp with "Hs Hc Hf"). }
  iIntros (v) "(%Heq & Hc & Hf & Hs)". subst v. unfold mf_update_best.
  destruct (mf_strict_better p best).
  - iApply wp_if_true. hm_take. iApply (wp_stack_assign with "Hv"). iIntros "!> _ Hv".
    iApply wp_let. simpl. hm_take. iApply (wp_stack_assign with "Hc"). iIntros "!> _ Hc".
    iApply wp_let. simpl. unfold qsort.sset, qsort.slot, qsort.sload.
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack lf))]).
    iApply (wp_stack_load with "Hs"). iIntros "!> _ Hs".
    iApply (wp_stack_assign with "Hf"). iIntros "!> _ Hf".
    unfold mf_best_cells. iFrame. done.
  - iApply wp_if_false. iApply wp_value'. unfold mf_best_cells. iFrame. done.
Qed.

Definition mf_group_step oa ob n lv lc lf lj : expr :=
  Let (Some "value") (App (Rec None (Some "args") array.get_body)
    (Struct [] [Val (LitV (LitObj oa)); qsort.sload lj]))
  (VarBind "end" (qsort.plus1 (qsort.sload lj))
  (VarBind "first" (App (Rec None (Some "args") array.get_body)
    (Struct [] [Val (LitV (LitObj ob)); qsort.sload lj]))
  (Let None
    (While (If (BinOp LeOp (qsort.plus1 (Var "end")) (Val (qsort.nval n)))
      (BinOp EqOp (App (Rec None (Some "args") array.get_body)
        (Struct [] [Val (LitV (LitObj oa)); Var "end"])) (Var "value"))
      (Val (LitV (LitBool false))))
      (Let (Some "ix") (App (Rec None (Some "args") array.get_body)
        (Struct [] [Val (LitV (LitObj ob)); Var "end"]))
        (Let None (If (BinOp LeOp (qsort.plus1 (Var "ix")) (Var "first"))
          (Assign "first" (Var "ix")) (Val (LitV LitUnit)))
          (Assign "end" (qsort.plus1 (Var "end"))))))
    (Let (Some "count") (BinOp MinusOp (Var "end") (qsort.sload lj))
    (Let None (If
      (If (BinOp LeOp (qsort.plus1 (qsort.sload lc)) (Var "count"))
        (Val (LitV (LitBool true)))
        (If (BinOp EqOp (qsort.sload lc) (Var "count"))
          (BinOp LeOp (qsort.plus1 (Var "first")) (qsort.sload lf))
          (Val (LitV (LitBool false)))))
      (Let None (qsort.sset lv (Var "value"))
        (Let None (qsort.sset lc (Var "count")) (qsort.sset lf (Var "first"))))
      (Val (LitV LitUnit)))
      (qsort.sset lj (Var "end"))))))).

Lemma mf_group_step_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    pairs p ps oa ob lv lc lf lj j best :
  drop j pairs = p::ps -> (j < length pairs)%nat ->
  StackId lj ↦ₛ qsort.nval j -∗ mf_best_cells best lv lc lf -∗
  mf_pair_arrays pairs oa ob -∗
  WP mf_group_step oa ob (length pairs) lv lc lf lj
    {{ v, ⌜v = LitV LitUnit⌝ ∗
      StackId lj ↦ₛ qsort.nval (j + S (fst (mf_scan_run (fst p) (snd p) ps)))%nat ∗
      mf_best_cells (mf_update_best best
        (fst p,(S (fst (mf_scan_run (fst p) (snd p) ps)),
          snd (mf_scan_run (fst p) (snd p) ps)))) lv lc lf ∗
      mf_pair_arrays pairs oa ob }}.
Proof.
  intros Hsuffix Hj.
  assert (pairs !! j = Some p) as Hp.
  { pose proof (f_equal (fun xs => xs !! 0%nat) Hsuffix) as Hlookup.
    rewrite lookup_drop in Hlookup. simpl in Hlookup. rewrite Nat.add_0_r in Hlookup. exact Hlookup. }
  assert (drop (S j) pairs = ps) as Hps.
  { pose proof (f_equal (drop 1%nat) Hsuffix) as Hdrop.
    rewrite drop_drop in Hdrop. simpl in Hdrop. replace (j+1)%nat with (S j) in Hdrop by lia.
    rewrite drop_0 in Hdrop. exact Hdrop. }
  destruct (mf_scan_run (fst p) (snd p) ps) as [extra minimum] eqn:Hscan.
  iIntros "Hj Hbest Hpairs". unfold mf_group_step.
  hm_take. hm_args. unfold qsort.sload, qsort.slot. mf_load_stack "Hj". hm_args.
  iDestruct "Hpairs" as "[Ha Hb]". iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp with "Ha"). rewrite list_lookup_fmap Hp. done. }
  iIntros (v) "[%Hv Ha]". subst v. iApply wp_let. simpl.
  unfold qsort.plus1, qsort.sload, qsort.slot, qsort.one.
  match goal with |- context [VarBind ?x ?e ?b] => iApply (wp_bind [VarBindCtx x b]) end.
  mf_load_stack "Hj". hm_admin.
  replace (Z.of_nat j+1)%Z with (Z.of_nat (S j)) by lia.
  iApply wp_var_bind. iIntros (le) "He". simpl.
  match goal with |- context [VarBind ?x ?e ?b] => iApply (wp_bind [VarBindCtx x b]) end.
  hm_args. mf_load_stack "Hj". hm_args. iApply (wp_wand with "[Hb]").
  { iApply (mf_get_value_wp with "Hb"). rewrite list_lookup_fmap Hp. done. }
  iIntros (v) "[%Hv Hb]". subst v. iApply wp_var_bind. iIntros (ls) "Hs". simpl.
  hm_take. iApply (wp_wand with "[He Hs Ha Hb]").
  { iApply (mf_group_inner_wp ps pairs oa ob le ls (fst p) (S j) (snd p)
      Hps ltac:(lia) with "He Hs [Ha Hb]"). unfold mf_pair_arrays. iFrame. }
  iIntros (v) "(He & Hs & Hpairs)". rewrite Hscan /=.
  iApply wp_let. simpl. unfold qsort.sload, qsort.slot.
  mf_load_stack "He". hm_admin. mf_load_stack "Hj". hm_admin.
  replace (Z.of_nat (S (j+extra)) - Z.of_nat j)%Z with (Z.of_nat (S extra)) by lia.
  hm_take. iApply (wp_wand with "[Hs Hbest]").
  { iApply (mf_best_update_slot_wp (fst p,(S extra,minimum)) best lv lc lf ls with "Hs Hbest"). }
  iIntros (u) "(%Hu & Hs & Hbest)". subst u. iApply wp_let. simpl.
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack lj))]).
  iApply (wp_stack_load with "He"). iIntros "!> _ He".
  iApply (wp_stack_assign with "Hj"). iIntros "!> _ Hj".
  iExists (qsort.nval minimum). iFrame "Hs".
  iExists (qsort.nval (S j+extra)). iFrame "He".
  replace (j+S extra)%nat with (S j+extra)%nat by lia. iFrame. done.
Qed.

Definition mf_group_outer oa ob n lv lc lf lj : expr :=
  While (BinOp LeOp (qsort.plus1 (qsort.sload lj)) (Val (qsort.nval n)))
    (mf_group_step oa ob n lv lc lf lj).
Lemma mf_group_outer_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ}
    fuel pairs suffix oa ob lv lc lf lj j best :
  drop j pairs = suffix -> (j <= length pairs)%nat -> (length suffix <= fuel)%nat ->
  StackId lj ↦ₛ qsort.nval j -∗ mf_best_cells best lv lc lf -∗
  mf_pair_arrays pairs oa ob -∗
  WP mf_group_outer oa ob (length pairs) lv lc lf lj
    {{ _, StackId lj ↦ₛ qsort.nval (length pairs) ∗
      mf_best_cells (mf_forward_scan fuel suffix best) lv lc lf ∗
      mf_pair_arrays pairs oa ob }}.
Proof.
  revert suffix j best. induction fuel as [|fuel IH]; intros suffix j best Hsuffix Hj Hfuel.
  - assert (suffix = []) as -> by (destruct suffix; [done|simpl in Hfuel; lia]).
    assert (j = length pairs) as ->.
    { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
    iIntros "Hj Hbest Hpairs". simpl.
    unfold mf_group_outer, qsort.plus1, qsort.sload, qsort.slot, qsort.one, qsort.nval, qsort.zval.
    iApply wp_while. mf_load_stack "Hj". hm_pure.
    rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. iApply wp_value'. iFrame.
  - destruct suffix as [|p ps].
    + assert (j = length pairs) as ->.
      { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
      iIntros "Hj Hbest Hpairs". simpl.
      unfold mf_group_outer, qsort.plus1, qsort.sload, qsort.slot, qsort.one, qsort.nval, qsort.zval.
      iApply wp_while. mf_load_stack "Hj". hm_pure.
      rewrite bool_decide_eq_false_2; [|lia]. iApply wp_if_false. iApply wp_value'. iFrame.
    + assert (j < length pairs) as Hlt.
      { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
      iIntros "Hj Hbest Hpairs".
      remember (mf_forward_scan (S fuel) (p::ps) best) as result eqn:Hresult.
      unfold mf_group_outer, qsort.plus1, qsort.sload, qsort.slot, qsort.one, qsort.nval, qsort.zval.
      iApply wp_while. mf_load_stack "Hj". hm_pure.
      rewrite bool_decide_eq_true_2; [|lia]. iApply wp_if_true.
      match goal with |- context [Seq ?e ?k] => iApply (wp_bind [SeqCtx k]) end.
      iApply (wp_wand with "[Hj Hbest Hpairs]").
      { iApply (mf_group_step_wp pairs p ps with "Hj Hbest Hpairs"); done. }
      iIntros (v) "(%Hv & Hj & Hbest & Hpairs)". subst v. iApply wp_seq.
      pose proof (mf_scan_run_bound (fst p) (snd p) ps) as Hbound.
      destruct (mf_scan_run (fst p) (snd p) ps) as [extra minimum] eqn:Hscan. simpl in *.
      assert (drop (j+S extra)%nat pairs = drop extra ps) as Hrest.
      { pose proof (f_equal (drop (S extra)) Hsuffix) as Hdrop.
        rewrite drop_drop in Hdrop. simpl in Hdrop. exact Hdrop. }
      assert (j+S extra <= length pairs)%nat as Hnext.
      { pose proof (f_equal (@length mf_pair) Hsuffix) as Hlen. rewrite length_drop in Hlen. simpl in Hlen. lia. }
      assert (result = mf_forward_scan fuel (drop extra ps)
        (mf_update_best best (fst p,(S extra,minimum)))) as Hnew.
      { rewrite Hresult. cbn [mf_forward_scan]. rewrite Hscan. done. }
      rewrite Hnew.
      iApply (IH (drop extra ps) (j+S extra)%nat (mf_update_best best (fst p,(S extra,minimum)))
        Hrest Hnext with "Hj Hbest Hpairs"). rewrite length_drop. simpl in Hfuel. lia.
Qed.

Lemma mf_group_outer_is_code oa ob n lv lc lf lj :
  subst_var "start" lj (subst_var "bestFirst" lf
    (subst_var "bestCount" lc (subst_var "bestValue" lv
      (subst "n" (qsort.nval n) (subst "indices" (LitV (LitObj ob))
        (subst "values" (LitV (LitObj oa)) (mf_find_group_loop mf_body))))))) =
  mf_group_outer oa ob n lv lc lf lj.
Proof.
  unfold mf_body, mf_group_outer, mf_group_step, qsort.sload, qsort.sset,
    qsort.slot, qsort.plus1, qsort.one, qsort.nval, qsort.zval. reflexivity.
Qed.

Lemma mf_array_object `{!cjrGS Σ} xs a :
  is_array xs a -∗ ∃ o, ⌜a = LitV (LitObj o)⌝ ∗ is_array xs (LitV (LitObj o)).
Proof.
  iIntros "Ha". iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
  iExists o. iSplit; [done|]. iExists o, base. iFrame. done.
Qed.

Theorem mf_nonempty_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs oi :
  xs <> [] ->
  is_array xs (LitV (LitObj oi)) -∗
  WP App (Rec None (Some "input") mf_body) (Val (LitV (LitObj oi)))
    {{ v, ∃ answer, ⌜mf_sort_scan xs = Some answer /\
         v = StructV [LitV (LitBool true); LitV (LitInt answer)]⌝ ∗
         is_array xs (LitV (LitObj oi)) }}.
Proof.
  intros Hnonempty. assert (0 < length xs)%nat as Hlen by (destruct xs; simpl in *; [contradiction|lia]).
  assert (length (mf_pairs xs 0%nat) = length xs) as Htaglen.
  { rewrite <- (mf_pairs_values xs 0%nat) at 2. rewrite length_fmap. done. }
  pose proof (mf_sorted_pairs_length xs) as Hsortedlen.
  destruct (lookup_lt_is_Some_2 (mf_sorted_pairs xs) 0%nat ltac:(lia)) as [p Hp].
  set (seed := (fst p,(0%nat,length xs)) : mf_summary).
  set (winner := mf_forward_scan (length xs) (mf_sorted_pairs xs) seed).
  pose proof (mf_forward_scan_correct xs seed Hnonempty eq_refl) as Hcorrect.
  change (most_frequent_spec xs (Some (fst winner))) in Hcorrect.
  pose proof (most_frequent_spec_unique xs (mf_sort_scan xs) (Some (fst winner))
    (mf_sort_scan_correct xs) Hcorrect) as Hanswer.
  iIntros "Hi".
  iApply (wp_bind [AppLCtx (Val (LitV (LitObj oi)))]).
  iApply wp_rec. iIntros "!> _". iApply wp_app. unfold mf_body. simpl.
  hm_take. iApply (wp_wand with "[Hi]").
  { iApply (length_spec with "Hi"). }
  iIntros (v) "[%Hv Hi]". subst v. iApply wp_let. simpl. hm_admin.
  rewrite bool_decide_eq_false_2; [|intros Heq; inversion Heq; lia]. iApply wp_if_false.
  hm_take. iApply (wp_wand with "[]"). { iApply (make_spec (length xs)). exact Hlen. }
  iIntros (a) "Ha". iDestruct (mf_array_object with "Ha") as (oa) "[%Ha Ha]". subst a.
  iApply wp_let. simpl.
  hm_take. iApply (wp_wand with "[]"). { iApply (make_spec (length xs)). exact Hlen. }
  iIntros (b) "Hb". iDestruct (mf_array_object with "Hb") as (ob) "[%Hb Hb]". subst b.
  iApply wp_let. simpl. hm_take.
  iApply wp_var_bind. iIntros (lcopy) "Hcopy". simpl.
  iApply (wp_wand with "[Hcopy Hi Ha Hb]").
  { iApply (mf_copy_loop_wp (length xs) xs oi oa ob lcopy 0%nat with "Hcopy Hi [Ha] [Hb]");
      try lia; unfold mf_copy_values, mf_copy_indices; simpl; rewrite Nat.sub_0_r; iFrame. }
  iIntros (v) "(Hcopy & Hi & Hpairs)".
  iExists (qsort.nval (length xs)). iFrame "Hcopy". iApply wp_let. simpl.
  hm_take. hm_args. iApply (wp_wand with "[Hpairs]").
  { pose proof (mf_qsort_wp (mf_pairs xs 0%nat) oa ob) as Hsort.
    rewrite Htaglen in Hsort. iApply (Hsort with "Hpairs"). }
  iIntros (u) "[%Hu Hpairs]". subst u. iApply wp_let. simpl.
  match goal with |- context [VarBind ?x ?e ?b] => iApply (wp_bind [VarBindCtx x b]) end.
  hm_args. iDestruct "Hpairs" as "[Ha Hb]". iApply (wp_wand with "[Ha]").
  { iApply (mf_get_value_wp (fst <$> mf_sorted_pairs xs) oa 0%nat (fst p) with "Ha").
    rewrite list_lookup_fmap Hp. done. }
  iIntros (u) "[%Hu Ha]". subst u. iApply wp_var_bind. iIntros (lv) "Hv". simpl.
  iApply wp_var_bind. iIntros (lc) "Hc". simpl.
  iApply wp_var_bind. iIntros (lf) "Hf". simpl.
  iApply wp_var_bind. iIntros (lj) "Hj". simpl.
  hm_take. iApply (wp_wand with "[Hj Hv Hc Hf Ha Hb]").
  { pose proof (mf_group_outer_wp (length xs) (mf_sorted_pairs xs) (mf_sorted_pairs xs)
      oa ob lv lc lf lj 0%nat seed eq_refl ltac:(lia) ltac:(lia)) as Hscan.
    rewrite Hsortedlen in Hscan. iApply (Hscan with "Hj [Hv Hc Hf] [Ha Hb]").
    - unfold mf_best_cells, seed, mf_summary_count, mf_summary_first. simpl. iFrame.
    - unfold mf_pair_arrays, mf_sorted_pairs. iFrame. }
  iIntros (u) "(Hj & Hbest & Hpairs)". fold winner.
  iDestruct "Hbest" as "(Hv & Hc & Hf)". iDestruct "Hpairs" as "[Ha Hb]".
  iApply wp_let. simpl. hm_take. iApply (wp_wand with "[Ha]").
  { iApply (mf_release_array_wp with "Ha"). }
  iIntros (w) "%Hw". subst w. iApply wp_let. simpl. hm_take.
  iApply (wp_wand with "[Hb]"). { iApply (mf_release_array_wp with "Hb"). }
  iIntros (w) "%Hw". subst w. iApply wp_let. simpl. hm_admin.
  unfold qsort.sload, qsort.slot. mf_load_stack "Hv". hm_admin.
  iExists (qsort.nval (length xs)). iFrame "Hj".
  iExists (qsort.nval (mf_summary_first winner)). iFrame "Hf".
  iExists (qsort.nval (mf_summary_count winner)). iFrame "Hc".
  iExists (LitV (LitInt (fst winner))). iFrame "Hv".
  iExists (fst winner). iFrame. done.
Qed.

Definition mf_option_value (answer : option Z) : val :=
  match answer with
  | None => StructV [LitV (LitBool false); LitV (LitInt 0)]
  | Some x => StructV [LitV (LitBool true); LitV (LitInt x)]
  end.
Definition mf_input `{!cjrGS Σ} (xs : list Z) oi : iProp Σ :=
  match xs with
  | [] => ObjId oi ↦ₒ[0] LitV (LitInt 0)
  | _::_ => is_array xs (LitV (LitObj oi))
  end.

Theorem mf_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs oi :
  mf_input xs oi -∗
  WP App (Rec None (Some "input") mf_body) (Val (LitV (LitObj oi)))
    {{ v, ⌜v = mf_option_value (mf_sort_scan xs)⌝ ∗ mf_input xs oi }}.
Proof.
  destruct xs as [|x xs].
  - iIntros "Hi". iApply (wp_wand with "[Hi]"). { iApply (mf_empty_wp with "Hi"). }
    iIntros (v) "[%Hv Hi]". iFrame. done.
  - iIntros "Hi". iApply (wp_wand with "[Hi]").
    { iApply (mf_nonempty_wp with "Hi"). discriminate. }
    iIntros (v) "Hresult". iDestruct "Hresult" as (answer) "[[%Ha %Hv] Hi]".
    iFrame. rewrite Ha. done.
Qed.

Corollary mf_spec_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} xs oi :
  mf_input xs oi -∗
  WP App (Rec None (Some "input") mf_body) (Val (LitV (LitObj oi)))
    {{ v, ⌜v = mf_option_value (mf_sort_scan xs) /\
      most_frequent_spec xs (mf_sort_scan xs)⌝ ∗ mf_input xs oi }}.
Proof.
  iIntros "Hi". iApply (wp_wand with "[Hi]"). { iApply (mf_wp with "Hi"). }
  iIntros (v) "[%Hv Hi]". iFrame. iPureIntro. split; [done|apply mf_sort_scan_correct].
Qed.
