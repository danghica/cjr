(** Refinement of the printed CJR operations to finite-set semantics. *)
From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.quadtree.spec Require Import model.
From cjr.quadtree.algorithm Require Import program.
From cjr.quadtree.proof Require Import ownership routing.
From iris.prelude Require Import options.
Import ListNotations.
Local Open Scope Z_scope.
Ltac qt_head := first [hm_head | iApply wp_if_true | iApply wp_if_false].
Ltac qt_pure :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with |- envs_entails _ (WP ?e {{ ?P }}) => hm_focus e ltac:(fun _ => qt_head) end);
  simpl; cbn [fill fill_item].
Section correctness.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma wp_fields_load o vs i v Φ : vs !! i = Some v ->
  fields o vs -∗ (fields o vs -∗ Φ v) -∗ WP FieldLoad (Val (ov o)) i {{ Φ }}.
Proof.
  iIntros (H) "Hf HΦ". iDestruct (fields_lookup o vs i v H with "Hf") as "[Hl Hclose]".
  iApply (wp_field_load with "Hl"). iIntros "!> _ Hl". iApply "HΦ". by iApply "Hclose".
Qed.
Lemma wp_fields_store o vs i v w Φ : vs !! i = Some v ->
  fields o vs -∗ (fields o (<[i:=w]>vs) -∗ Φ uv) -∗
  WP FieldStore (Val (ov o)) i (Val w) {{ Φ }}.
Proof.
  iIntros (H) "Hf HΦ". iDestruct (fields_update o vs i v H with "Hf") as "[Hl Hclose]".
  iApply (wp_field_store with "Hl"). iIntros "!> _ Hl". iApply "HΦ". by iApply "Hclose".
Qed.
Ltac qt_read_head := match goal with
  |- envs_entails _ (WP FieldLoad (Val (LitV (LitObj ?o))) ?i {{ ?P }}) =>
    iApply (wp_fields_load o with "Hf"); [reflexivity|iIntros "Hf"]
  end.
Ltac qt_read := match goal with
  |- envs_entails _ (WP ?e {{ ?P }}) => hm_focus e ltac:(fun _ => qt_read_head)
  end.
Ltac qt_write_head := match goal with
  |- envs_entails _ (WP FieldStore (Val (LitV (LitObj ?o))) ?i (Val ?v) {{ ?P }}) =>
    iApply (wp_fields_store o with "Hf"); [reflexivity|iIntros "Hf"]
  end.
Ltac qt_write := match goal with
  |- envs_entails _ (WP ?e {{ ?P }}) => hm_focus e ltac:(fun _ => qt_write_head)
  end.
Lemma wp_qlt a b : ⊢ WP qlt (qi a) (qi b) {{ v, ⌜v = bv (bool_decide (a < b))⌝ }}.
Proof.
  unfold qlt, qle, qeq, qi, qb, bv. qt_pure. repeat (case_bool_decide; qt_pure).
  all: iPureIntro; try reflexivity; exfalso; lia.
Qed.
Lemma wp_qpoint_eq p q : ⊢ WP qpoint_eq (qi (fst p)) (qi (snd p)) (qi (fst q)) (qi (snd q))
  {{ v, ⌜v = bv (bool_decide (p = q))⌝ }}.
Proof.
  destruct p as [x y], q as [a b]. unfold qpoint_eq, qand, qeq, qi, bv. qt_pure. repeat (case_bool_decide; qt_pure).
  all: iPureIntro; try reflexivity; exfalso; congruence.
Qed.
Lemma wp_qinside r p : ⊢ WP qinside (qi (fst p)) (qi (snd p))
  (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r))
  {{ v, ⌜v = bv (bool_decide (in_rect r p))⌝ }}.
Proof.
  destruct r as [a b c d], p as [x y]. unfold in_rect; simpl. unfold qinside, qlt, qle, qeq, qand, qi, qb, bv. qt_pure.
  repeat (case_bool_decide; qt_pure).
  all: iPureIntro; try reflexivity; exfalso; intuition lia.
Qed.


Lemma wp_qt_empty_val d b : ⊢ WP App (Val (RecV (Some "qt_empty") (Some "args") qt_empty_body))
 (Val (StructV [iv (xmin b);iv (ymin b);iv (xmax b);iv (ymax b)]))
  {{ v, node_rep d b Empty v }}.
Proof.
  unfold qt_empty_body, qargs, qi, qu, iv. qt_pure.
  iApply wp_new. iIntros (o) "Hf".
  iExists o. iSplit; first done. iExact "Hf".
Qed.
Lemma wp_qt_nil : ⊢ WP qt_nil {{ v, point_list [] v }}.
Proof.
  unfold qt_nil, qt_nil_body, qb, qi, qu. qt_pure.
  iApply wp_new. iIntros (o) "Hf".
  iExists o. iSplit; first done. iExact "Hf".
Qed.
Lemma wp_qt_cons p xs tail : point_list xs tail -∗
  WP qt_cons (qi (fst p)) (qi (snd p)) (Val tail) {{ v, point_list (p::xs) v }}.
Proof.
  destruct p as [x y]. iIntros "Ht".
  iDestruct (point_list_object with "Ht") as %[oTail ->].
  unfold qt_cons, qinvoke, qt_cons_body, qargs, qi, qb. qt_pure.
  iApply wp_new. iIntros (o) "Hf".
  iExists o, (ov oTail). iSplit; first done. iSplitL "Hf"; first iExact "Hf". iExact "Ht".
Qed.
Lemma wp_qt_seed d b p n : node_rep d b Empty n -∗
  WP qt_seed (Val n) (qi (fst p)) (qi (snd p)) {{ v, ⌜v = uv⌝ ∗ node_rep d b (Leaf p) n }}.
Proof.
  iIntros "Hn". iDestruct "Hn" as (o ->) "Hf".
  unfold qt_seed, qinvoke, qt_seed_body, qargs, qi, qu. qt_pure.
  qt_write; qt_pure. qt_write; qt_pure. qt_write; qt_pure.
  iSplit; first done. iExists o. iSplit; first done. iExact "Hf".
Qed.
Lemma wp_qt_power_val d : ⊢ WP App (Val (RecV (Some "qt_power") (Some "args") qt_power_body))
  (Val (StructV [iv (Z.of_nat d)])) {{ v, ⌜v = iv (width d)⌝ }}.
Proof.
  induction d as [|d IH].
  - unfold qt_power_body, qargs, qi, qle, iv. qt_pure. done.
  - rewrite Nat2Z.inj_succ. unfold qt_power_body, qargs, qi, qle, iv.
    qt_pure. rewrite bool_decide_false; last lia. iApply wp_if_false. hm_args.
    replace (Z.succ (Z.of_nat d) - 1) with (Z.of_nat d) by lia.

    iApply (wp_wand with "[]").
    + iApply IH.
    + iIntros (v ->). qt_pure. iPureIntro. unfold iv. f_equal. f_equal. rewrite width_succ. lia.
Qed.
Lemma wp_qt_power d : ⊢ WP qt_power (qi (Z.of_nat d)) {{ v, ⌜v = iv (width d)⌝ }}.
Proof. unfold qt_power, qinvoke, qi. hm_args. iApply wp_qt_power_val. Qed.
Lemma wp_qt_make d : (d <= 30)%nat ->
  ⊢ WP qt_make (qi (Z.of_nat d)) {{ v, tree_rep d Empty v }}.
Proof.
  intros Hd. unfold qt_make, qinvoke, qi. hm_args. iApply wp_app. simpl. hm_args.
  iApply (wp_wand with "[]").
  - iApply wp_qt_power_val.
  - iIntros (v ->). hm_args.
    iApply (wp_wand with "[]").
    + iApply (wp_qt_empty_val d (domain d)).
    + iIntros (root) "Hn". iDestruct "Hn" as (no ->) "Hnf".
      qt_pure. iApply wp_new. iIntros (o) "Hf".
      iSplit; first (iPureIntro; split; done).
      iExists o, (ov no). iSplit; first done. iSplitL "Hf"; first iExact "Hf".
      iExists no. iSplit; first done. iExact "Hnf".
Qed.
Lemma wp_qoverlap b r : ⊢ WP qoverlap (qi (xmin b)) (qi (ymin b)) (qi (xmax b)) (qi (ymax b))
  (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r))
  {{ v, ⌜v = bv (bool_decide (overlap b r))⌝ }}.
Proof.
  destruct b as [a b c d], r as [x y z w]. unfold overlap; simpl.
  unfold qoverlap, qlt, qle, qeq, qand, qi, qb, bv. qt_pure.
  repeat (case_bool_decide; qt_pure).
  all: iPureIntro; try reflexivity; exfalso; intuition lia.
Qed.
Lemma wp_qchoose d b p a c e f : ⊢ WP qchoose (qi (fst p)) (qi (snd p))
  (qi (midx d b)) (qi (midy d b)) (Val (ov a)) (Val (ov c)) (Val (ov e)) (Val (ov f))
  {{ v, ⌜v = child_tree (route d b p) (ov a) (ov c) (ov e) (ov f)⌝ }}.
Proof.
  unfold qchoose, qlt, qle, qeq, qi, qb, route.
  destruct (Z.ltb_spec (fst p) (midx d b)); destruct (Z.ltb_spec (snd p) (midy d b)); simpl;
  qt_pure; repeat (case_bool_decide; qt_pure); try (exfalso; lia); done.
Qed.

End correctness.
