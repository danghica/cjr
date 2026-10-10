(** Refinement of the printed CJR operations to finite-set semantics. *)
From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.quadtree.spec Require Import model.
From cjr.quadtree.algorithm Require Import program.
From cjr.quadtree.proof Require Import ownership routing helpers.
From iris.prelude Require Import options.
Import ListNotations.
Local Open Scope Z_scope.
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

Section operations.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Ltac qt_call :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with |- envs_entails _ (WP ?e {{ ?P }}) =>
      hm_focus e ltac:(fun _ => first [hm_args_head | iApply wp_if_true | iApply wp_if_false]) end);
  simpl; cbn [fill fill_item].
Lemma wp_qt_contains_node_val d b t n p : square d b -> valid d b t ->
  node_rep d b t n -∗
  WP App (Val (RecV (Some "qt_contains_node") (Some "args") qt_contains_node_body))
    (Val (StructV [n;iv (fst p);iv (snd p)]))
    {{ v, ⌜v = bv (bool_decide (p ∈ contents t))⌝ ∗ node_rep d b t n }}.
Proof.
  revert d b n p. induction t as [|q|ll IHll lr IHlr ul IHul ur IHur]; intros d b n p Hb Ht; iIntros "Hn".
  - iDestruct "Hn" as (o ->) "Hf".
    unfold qt_contains_node_body, qargs, qeq, qi. qt_pure. qt_read; qt_pure.
    rewrite bool_decide_false; last set_solver. iSplit; first done.
    iExists o. iSplit; first done. iExact "Hf".
  - iDestruct "Hn" as (o ->) "Hf".
    unfold qt_contains_node_body, qargs, qeq, qi. qt_pure. qt_read; qt_pure.
    qt_read; qt_pure. qt_read; qt_pure.
    iSplit.
    + iPureIntro. unfold bv. f_equal. f_equal.
      destruct p as [x y], q as [a c]; simpl.
      repeat case_bool_decide; simpl; try reflexivity; exfalso; set_solver.
    + iExists o. iSplit; first done. iExact "Hf".
  - destruct d as [|d]; first contradiction.
    destruct Ht as [Hll [Hlr [Hul Hur]]].
    pose proof (routed_member d b ll lr ul ur p Hb (conj Hll (conj Hlr (conj Hul Hur)))) as Hr.
    iDestruct "Hn" as (o a c e f ->) "(Hf & Hll & Hlr & Hul & Hur)".
    iDestruct (node_rep_object with "Hll") as %[oa ->].
    iDestruct (node_rep_object with "Hlr") as %[oc ->].
    iDestruct (node_rep_object with "Hul") as %[oe ->].
    iDestruct (node_rep_object with "Hur") as %[of_ ->].
    unfold qt_contains_node_body, qargs, qeq, qi. qt_pure. qt_read; qt_pure.
    do 5 (qt_read; qt_pure). qt_read; iApply wp_let; simpl. hm_take.
    iApply (wp_wand with "[]").
    + iApply wp_qchoose.
    + iIntros (v ->). qt_call.
      destruct (route d b p) eqn:Hroute; simpl in Hr |- *.
      * iApply (wp_wand with "[Hll]").
        { iApply (IHll d _ _ p (child_square d b LL Hb) Hll with "Hll"). }
        iIntros (v) "[%Hv Hll]". iSplit.
        { iPureIntro. rewrite Hv. f_equal. by apply bool_decide_ext. }
        iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
      * iApply (wp_wand with "[Hlr]").
        { iApply (IHlr d _ _ p (child_square d b LR Hb) Hlr with "Hlr"). }
        iIntros (v) "[%Hv Hlr]". iSplit.
        { iPureIntro. rewrite Hv. f_equal. by apply bool_decide_ext. }
        iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
      * iApply (wp_wand with "[Hul]").
        { iApply (IHul d _ _ p (child_square d b UL Hb) Hul with "Hul"). }
        iIntros (v) "[%Hv Hul]". iSplit.
        { iPureIntro. rewrite Hv. f_equal. by apply bool_decide_ext. }
        iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
      * iApply (wp_wand with "[Hur]").
        { iApply (IHur d _ _ p (child_square d b UR Hb) Hur with "Hur"). }
        iIntros (v) "[%Hv Hur]". iSplit.
        { iPureIntro. rewrite Hv. f_equal. by apply bool_decide_ext. }
        iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
Qed.

Lemma wp_qt_contains d t v p : tree_rep d t v -∗
  WP qt_contains (Val v) (qi (fst p)) (qi (snd p))
  {{ r, ⌜r = bv (contains_set p (contents t))⌝ ∗ tree_rep d t v }}.
Proof.
  iIntros "Ht". iDestruct "Ht" as "[%Hd Ht]". destruct Hd as [Hd Hv].
  iDestruct "Ht" as (o root ->) "[Hf Hn]".
  iDestruct (node_rep_object with "Hn") as %[nr ->].
  unfold qt_contains, qinvoke, qi. hm_args. iApply wp_app. simpl. qt_pure.
  qt_read; iApply wp_let; simpl. match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qinside (domain d) p).
  iIntros (b ->). case_bool_decide as Hin.
  - iApply wp_if_true. qt_pure. qt_read; iApply wp_let; simpl. hm_args.
    iApply (wp_wand with "[Hn]").
    { iApply (wp_qt_contains_node_val d (domain d) t (ov nr) p (root_square d) Hv with "Hn"). }
    iIntros (b) "[%Hb Hn]". iSplit; first done. iSplit; first (iPureIntro; done).
    iExists o, (ov nr). iFrame. done.
  - iApply wp_if_false. qt_pure. iSplit.
    { iPureIntro. unfold contains_set. rewrite bool_decide_false; first done.
      intros Hp. apply Hin. exact (valid_contents d (domain d) t (root_square d) Hv p Hp). }
    iSplit; first (iPureIntro; done). iExists o, (ov nr). iFrame. done.
Qed.

Lemma wp_qt_cons_val p xs tail : point_list xs tail -∗
  WP App (Val (RecV (Some "qt_cons") (Some "args") qt_cons_body))
    (Val (StructV [iv (fst p);iv (snd p);tail])) {{ v, point_list (p::xs) v }}.
Proof.
  destruct p as [x y]. iIntros "Ht".
  iDestruct (point_list_object with "Ht") as %[oTail ->].
  unfold qt_cons_body, qargs, qi, qb, iv. qt_pure.
  iApply wp_new. iIntros (o) "Hf".
  iExists o, (ov oTail). iSplit; first done.
  iSplitL "Hf"; first iExact "Hf". iExact "Ht".
Qed.
Lemma wp_qt_range_node_val d b t n r xs acc : square d b -> valid d b t ->
  node_rep d b t n -∗ point_list xs acc -∗
  WP App (Val (RecV (Some "qt_range_node") (Some "args") qt_range_node_body))
    (Val (StructV [n;iv (xmin r);iv (ymin r);iv (xmax r);iv (ymax r);acc]))
    {{ v, point_list (query_model r t ++ xs) v ∗ node_rep d b t n }}.
Proof.
  revert d b n r xs acc. induction t as [|p|ll IHll lr IHlr ul IHul ur IHur];
    intros d b n r xs acc Hb Ht; iIntros "Hn Ha";
    iDestruct (point_list_object with "Ha") as %[ac ->].
  - iDestruct "Hn" as (o ->) "Hf".
    unfold qt_range_node_body, qargs, qeq, qi, iv. qt_pure. qt_read; qt_pure.
    iSplitL "Ha"; first iExact "Ha". iExists o. iSplit; first done. iExact "Hf".
  - iDestruct "Hn" as (o ->) "Hf".
    unfold qt_range_node_body, qargs, qeq, qi, iv. qt_pure. qt_read; qt_pure.
    do 3 (qt_read; qt_pure). qt_read; iApply wp_let; simpl.
    match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
    iApply (wp_wand with "[]"); first iApply (wp_qoverlap b r).
    iIntros (v ->). case_bool_decide as Ho.
    + iApply wp_if_true. qt_pure. qt_read; qt_pure. qt_read; iApply wp_let; simpl.
      match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
      iApply (wp_wand with "[]"); first iApply (wp_qinside r p).
      iIntros (v ->). case_bool_decide as Hp.
      * iApply wp_if_true. hm_args. iApply (wp_wand with "[Ha]").
        { iApply (wp_qt_cons_val p xs (ov ac) with "Ha"). }
        iIntros (v) "Ha". unfold query_model, select_points; simpl. rewrite filter_cons_True; last exact Hp. simpl.
        iSplitL "Ha"; first iExact "Ha". iExists o. iSplit; first done. iExact "Hf".
      * iApply wp_if_false. qt_pure. unfold query_model, select_points; simpl. rewrite filter_cons_False; last exact Hp. simpl.
        iSplitL "Ha"; first iExact "Ha". iExists o. iSplit; first done. iExact "Hf".
    + iApply wp_if_false. qt_pure. rewrite (query_pruned d b (Leaf p) r Hb Ht Ho); simpl.
      iSplitL "Ha"; first iExact "Ha". iExists o. iSplit; first done. iExact "Hf".
  - destruct d as [|d]; first contradiction. destruct Ht as [Hll [Hlr [Hul Hur]]].
    iDestruct "Hn" as (o a c e f ->) "(Hf & Hll & Hlr & Hul & Hur)".
    iDestruct (node_rep_object with "Hll") as %[oa ->].
    iDestruct (node_rep_object with "Hlr") as %[oc ->].
    iDestruct (node_rep_object with "Hul") as %[oe ->].
    iDestruct (node_rep_object with "Hur") as %[of_ ->].
    unfold qt_range_node_body, qargs, qeq, qi, iv. qt_pure. qt_read; qt_pure.
    do 3 (qt_read; qt_pure). qt_read; iApply wp_let; simpl.
    match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
    iApply (wp_wand with "[]"); first iApply (wp_qoverlap b r).
    iIntros (v ->). case_bool_decide as Ho.
    + iApply wp_if_true. qt_pure. do 3 (qt_read; qt_pure). qt_read; iApply wp_let; simpl. qt_call.
      iApply (wp_wand with "[Hur Ha]").
      { iApply (IHur d _ _ r xs (ov ac) (child_square d b UR Hb) Hur with "Hur Ha"). }
      iIntros (v) "[Ha Hur]". iDestruct (point_list_object with "Ha") as %[a3 ->]. qt_call.
      iApply (wp_wand with "[Hul Ha]").
      { iApply (IHul d _ _ r _ (ov a3) (child_square d b UL Hb) Hul with "Hul Ha"). }
      iIntros (v) "[Ha Hul]". iDestruct (point_list_object with "Ha") as %[a2 ->]. qt_call.
      iApply (wp_wand with "[Hlr Ha]").
      { iApply (IHlr d _ _ r _ (ov a2) (child_square d b LR Hb) Hlr with "Hlr Ha"). }
      iIntros (v) "[Ha Hlr]". iDestruct (point_list_object with "Ha") as %[a1 ->]. qt_call.
      iApply (wp_wand with "[Hll Ha]").
      { iApply (IHll d _ _ r _ (ov a1) (child_square d b LL Hb) Hll with "Hll Ha"). }
      iIntros (v) "[Ha Hll]". iSplitL "Ha".
      { unfold query_model, select_points; simpl. rewrite !filter_app !app_assoc. iExact "Ha". }
      iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
    + iApply wp_if_false. qt_pure.
      rewrite (query_pruned (S d) b (Branch ll lr ul ur) r Hb (conj Hll (conj Hlr (conj Hul Hur))) Ho); simpl.
      iSplitL "Ha"; first iExact "Ha". iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
Qed.

Lemma wp_qt_range d t v r : tree_rep d t v -∗
  WP qt_range (Val v) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r))
  {{ result, tree_rep d t v ∗ point_list (query_model r t) result ∗
    ⌜NoDup (query_model r t) /\ list_to_set (query_model r t) = range_set r (contents t)⌝ }}.
Proof.
  iIntros "Ht". iDestruct "Ht" as "[%Hd Ht]". destruct Hd as [Hd Hv].
  iDestruct "Ht" as (o root ->) "[Hf Hn]".
  iDestruct (node_rep_object with "Hn") as %[nr ->].
  unfold qt_range, qinvoke, qi. hm_args. iApply wp_app. simpl. qt_pure.
  qt_read; qt_pure. iApply wp_new. iIntros (a) "Ha".
  iAssert (point_list [] (ov a)) with "[Ha]" as "Ha".
  { iExists a. iSplit; first done. iExact "Ha". }
  qt_call. iApply (wp_wand with "[Hn Ha]").
  { iApply (wp_qt_range_node_val d (domain d) t (ov nr) r [] (ov a) (root_square d) Hv with "Hn Ha"). }
  iIntros (result) "[Ha Hn]". rewrite app_nil_r. iSplitL "Hf Hn".
  { iSplit; first (iPureIntro; done). iExists o, (ov nr). iFrame. done. }
  iFrame. iPureIntro. split; [by eapply query_model_unique; eauto using root_square|apply query_model_contents].
Qed.

End operations.
