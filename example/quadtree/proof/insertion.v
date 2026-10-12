From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.quadtree.spec Require Import model.
From cjr.quadtree.algorithm Require Import program.
From cjr.quadtree.proof Require Import ownership routing helpers insertion_model insertion_helpers.
From iris.prelude Require Import options.
Import ListNotations.
Local Open Scope Z_scope.
Section insertion_contracts.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Ltac qt_read_head := match goal with
  |- envs_entails _ (WP FieldLoad (Val (LitV (LitObj ?o))) ?i {{ ?P }}) =>
    iApply (wp_fields_load o with "Hf"); [reflexivity|iIntros "Hf"] end.
Ltac qt_read := match goal with |- envs_entails _ (WP ?e {{ ?P }}) => hm_focus e ltac:(fun _ => qt_read_head) end.
Ltac qt_write_head := match goal with
  |- envs_entails _ (WP FieldStore (Val (LitV (LitObj ?o))) ?i (Val ?v) {{ ?P }}) =>
    iApply (wp_fields_store o with "Hf"); [reflexivity|iIntros "Hf"] end.
Ltac qt_write := match goal with |- envs_entails _ (WP ?e {{ ?P }}) => hm_focus e ltac:(fun _ => qt_write_head) end.
Ltac qt_call :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with |- envs_entails _ (WP ?e {{ ?P }}) =>
      hm_focus e ltac:(fun _ => first [hm_args_head | iApply wp_if_true | iApply wp_if_false]) end);
  simpl; cbn [fill fill_item].

Lemma wp_insert_empty d b p o : in_rect b p ->
  node_rep d b Empty (ov o) -∗
  WP App (Val insert_self) (Val (StructV [ov o;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
  {{ v, insert_post d b Empty (ov o) p v }}.
Proof.
  intros Hp. iIntros "Hn". iDestruct "Hn" as (o' Hptr) "Hf".
  inversion Hptr; subst o'.
  unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure.
  qt_read; iApply wp_let; simpl. qt_call.
  iApply (wp_wand with "[Hf]").
  { iApply (wp_seed_val d b p (ov o) with "[Hf]"). iExists o. iSplit; first done. iExact "Hf". }
  iIntros (v) "[%Hv Hn]". subst v. qt_pure. iExists (Leaf p). iFrame.
  iPureIntro. split; first exact Hp. split; first (simpl; set_solver).
  rewrite bool_decide_true; first done. set_solver.
Qed.
Lemma wp_insert_leaf_zero b p q o : square 0 b -> in_rect b p -> in_rect b q ->
  node_rep 0 b (Leaf q) (ov o) -∗
  WP App (Val insert_self) (Val (StructV [ov o;iv 0;iv (fst p);iv (snd p)]))
  {{ v, insert_post 0 b (Leaf q) (ov o) p v }}.
Proof.
  intros Hb Hp Hq. assert (p=q) by (eapply unit_unique; eauto). subst p.
  iIntros "Hn". iDestruct "Hn" as (o' Hptr) "Hf". inversion Hptr; subst o'.
  unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure. qt_read; qt_pure.
  qt_read; qt_pure. qt_read; iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qpoint_eq q q).
  iIntros (v ->). rewrite bool_decide_true; last done. qt_pure.
  iExists (Leaf q). iSplit.
  { iPureIntro. split; first exact Hq. split; first (simpl; set_solver).
    rewrite bool_decide_false; first done. simpl; set_solver. }
  iExists o. iSplit; first done. iExact "Hf".
Qed.
Lemma wp_insert_leaf_succ d b p q o : square (S d) b -> in_rect b p -> in_rect b q ->
  (forall k t v, valid d (child_box d b k) t -> in_rect (child_box d b k) p ->
    node_rep d (child_box d b k) t v -∗
    WP App (Val insert_self) (Val (StructV [v;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
    {{ r, insert_post d (child_box d b k) t v p r }}) ->
  node_rep (S d) b (Leaf q) (ov o) -∗
  WP App (Val insert_self) (Val (StructV [ov o;iv (Z.of_nat (S d));iv (fst p);iv (snd p)]))
  {{ v, insert_post (S d) b (Leaf q) (ov o) p v }}.
Proof.
  intros Hb Hp Hq IH. iIntros "Hn". iDestruct "Hn" as (o' Hptr) "Hf". inversion Hptr; subst o'.
  unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure. qt_read; qt_pure.
  qt_read; qt_pure. qt_read; iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qpoint_eq p q).
  iIntros (v ->). case_bool_decide as Heq.
  - subst p. iApply wp_if_true. qt_pure. iExists (Leaf q). iSplit.
    { iPureIntro. split; first exact Hq. split; first (simpl; set_solver).
      rewrite bool_decide_false; first done. simpl; set_solver. }
    iExists o. iSplit; first done. iExact "Hf".
  - iApply wp_if_false. iApply (wp_split_call d b p q o Hb Hq Hp IH with "Hf").
Qed.
Theorem wp_qt_insert_node_val d b t n p : square d b -> valid d b t -> in_rect b p ->
  node_rep d b t n -∗
  WP App (Val insert_self) (Val (StructV [n;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
  {{ v, insert_post d b t n p v }}.
Proof.
  revert b t n p. induction d as [|d IH]; intros b t n p Hb Ht Hp; iIntros "Hn";
    iDestruct (node_rep_object with "Hn") as %[o ->]; destruct t as [|q|ll lr ul ur].
  - iApply (wp_insert_empty 0 b p o Hp with "Hn").
  - iApply (wp_insert_leaf_zero b p q o Hb Hp Ht with "Hn").
  - contradiction.
  - iApply (wp_insert_empty (S d) b p o Hp with "Hn").
  - iApply (wp_insert_leaf_succ d b p q o Hb Hp Ht with "Hn").
    intros k t v Hvalid Hin. exact (IH _ _ _ _ (child_square d b k Hb) Hvalid Hin).
  - iDestruct "Hn" as (o' a c e f Hptr) "Hn". inversion Hptr; subst o'.
    iDestruct "Hn" as "(Hf & Hll & Hlr & Hul & Hur)".
    unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure. qt_read; qt_pure.
    iApply (wp_branch_call d b ll lr ul ur (ov o) p Hb Ht Hp with "[Hf Hll Hlr Hul Hur]").
    + intros k t v Hvalid Hin. exact (IH _ _ _ _ (child_square d b k Hb) Hvalid Hin).
    + iExists o, a, c, e, f. iFrame. done.
Qed.
Theorem wp_qt_insert_set_refinement d t v p : tree_rep d t v -∗
  WP qt_insert (Val v) (qi (fst p)) (qi (snd p))
  {{ result, ∃ t', tree_rep d t' v ∗
    ⌜contents t' = insert_set d p (contents t) /\
      result = bv (bool_decide (in_rect (domain d) p /\ p ∉ contents t))⌝ }}.
Proof.
  iIntros "Ht". iDestruct "Ht" as "[%Hd Ht]". destruct Hd as [Hd Hv].
  iDestruct "Ht" as (o root ->) "[Hf Hn]".
  iDestruct (node_rep_object with "Hn") as %[nr ->].
  unfold qt_insert, qinvoke, qi. hm_args. iApply wp_app. simpl. qt_pure.
  qt_read; iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qinside (domain d) p).
  iIntros (b ->). case_bool_decide as Hin.
  - iApply wp_if_true. qt_pure. qt_read; qt_pure. qt_read; iApply wp_let; simpl. hm_args.
    iApply (wp_wand with "[Hn]").
    { iApply (wp_qt_insert_node_val d (domain d) t (ov nr) p (root_square d) Hv Hin with "Hn"). }
    iIntros (b) "Hn". iDestruct "Hn" as (t' [Ht [Hs Hb]]) "Hn".
    iExists t'. iSplitL "Hf Hn".
    { iSplit; first (iPureIntro; done). iExists o, (ov nr). iFrame. done. }
    iPureIntro. split.
    + unfold insert_set. rewrite decide_True; done.
    + rewrite Hb. f_equal. apply bool_decide_ext. tauto.
  - iApply wp_if_false. qt_pure. iExists t. iSplitL "Hf Hn".
    { iSplit; first (iPureIntro; done). iExists o, (ov nr). iFrame. done. }
    iPureIntro. split.
    + unfold insert_set. rewrite decide_False; done.
    + rewrite bool_decide_false; first done. tauto.
Qed.
Lemma wp_insert_existing_node d b t n p : square d b -> valid d b t -> p ∈ contents t ->
  node_rep d b t n -∗
  WP App (Val insert_self) (Val (StructV [n;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
  {{ v, ⌜v = bv false⌝ ∗ node_rep d b t n }}.
Proof.
  revert d b n p. induction t as [|q|ll IHll lr IHlr ul IHul ur IHur];
    intros d b n p Hb Ht Hp; iIntros "Hn".
  - simpl in Hp. set_solver.
  - assert (p=q) by (simpl in Hp; set_solver). subst p.
    iDestruct "Hn" as (o ->) "Hf".
    unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure. qt_read; qt_pure.
    qt_read; qt_pure. qt_read; iApply wp_let; simpl.
    match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
    iApply (wp_wand with "[]"); first iApply (wp_qpoint_eq q q).
    iIntros (v ->). rewrite bool_decide_true; last done. qt_pure.
    iSplit; first done. iExists o. iSplit; first done. iExact "Hf".
  - destruct d as [|d]; first contradiction. destruct Ht as [Hll [Hlr [Hul Hur]]].
    pose proof (proj1 (routed_member d b ll lr ul ur p Hb (conj Hll (conj Hlr (conj Hul Hur)))) Hp) as Hr.
    iDestruct "Hn" as (o a c e f ->) "(Hf & Hll & Hlr & Hul & Hur)".
    iDestruct (node_rep_object with "Hll") as %[oa ->].
    iDestruct (node_rep_object with "Hlr") as %[oc ->].
    iDestruct (node_rep_object with "Hul") as %[oe ->].
    iDestruct (node_rep_object with "Hur") as %[of_ ->].
    unfold insert_self, qt_insert_node_body, qargs, iv, qi, qeq. qt_pure. qt_read; qt_pure.
    do 5 (qt_read; qt_pure). qt_read; iApply wp_let; simpl. hm_take.
    iApply (wp_wand with "[]"); first iApply wp_qchoose.
    iIntros (v ->). qt_call.
    replace (Z.of_nat (S d) - 1) with (Z.of_nat d) by lia.
    destruct (route d b p) eqn:Hroute; simpl in Hr |- *.
    + iApply (wp_wand with "[Hll]").
      { iApply (IHll d _ _ p (child_square d b LL Hb) Hll Hr with "Hll"). }
      iIntros (v) "[%Hv Hll]". iSplit; first done.
      iExists o,(ov oa),(ov oc),(ov oe),(ov of_). iFrame. done.
    + iApply (wp_wand with "[Hlr]").
      { iApply (IHlr d _ _ p (child_square d b LR Hb) Hlr Hr with "Hlr"). }
      iIntros (v) "[%Hv Hlr]". iSplit; first done.
      iExists o,(ov oa),(ov oc),(ov oe),(ov of_). iFrame. done.
    + iApply (wp_wand with "[Hul]").
      { iApply (IHul d _ _ p (child_square d b UL Hb) Hul Hr with "Hul"). }
      iIntros (v) "[%Hv Hul]". iSplit; first done.
      iExists o,(ov oa),(ov oc),(ov oe),(ov of_). iFrame. done.
    + iApply (wp_wand with "[Hur]").
      { iApply (IHur d _ _ p (child_square d b UR Hb) Hur Hr with "Hur"). }
      iIntros (v) "[%Hv Hur]". iSplit; first done.
      iExists o,(ov oa),(ov oc),(ov oe),(ov of_). iFrame. done.
Qed.
Lemma wp_insert_duplicate d t v p : p ∈ contents t -> tree_rep d t v -∗
  WP qt_insert (Val v) (qi (fst p)) (qi (snd p)) {{ r, ⌜r = bv false⌝ ∗ tree_rep d t v }}.
Proof.
  intros Hp. iIntros "Ht". iDestruct "Ht" as "[%Hd Ht]". destruct Hd as [Hd Hv].
  pose proof (valid_contents d (domain d) t (root_square d) Hv p Hp) as Hin.
  iDestruct "Ht" as (o root ->) "[Hf Hn]".
  iDestruct (node_rep_object with "Hn") as %[nr ->].
  unfold qt_insert, qinvoke, qi. hm_args. iApply wp_app. simpl. qt_pure.
  qt_read; iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qinside (domain d) p).
  iIntros (b ->). rewrite bool_decide_true; last exact Hin. iApply wp_if_true.
  qt_pure. qt_read; qt_pure. qt_read; iApply wp_let; simpl. hm_args.
  iApply (wp_wand with "[Hn]").
  { iApply (wp_insert_existing_node d (domain d) t (ov nr) p (root_square d) Hv Hp with "Hn"). }
  iIntros (v) "[%Hres Hn]". iSplit; first done.
  iSplit; first done. iExists o,(ov nr). iFrame. done.
Qed.
Lemma wp_insert_rejected d t v p : ~in_rect (domain d) p -> tree_rep d t v -∗
  WP qt_insert (Val v) (qi (fst p)) (qi (snd p)) {{ r, ⌜r = bv false⌝ ∗ tree_rep d t v }}.
Proof.
  intros Hp. iIntros "Ht". iDestruct "Ht" as "[%Hd Ht]".
  iDestruct "Ht" as (o root ->) "[Hf Hn]".
  iDestruct (node_rep_object with "Hn") as %[nr ->].
  unfold qt_insert, qinvoke, qi. hm_args. iApply wp_app. simpl. qt_pure.
  qt_read; iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP If ?cond ?a ?b {{ ?P }}) => iApply (wp_bind [IfCtx a b]) end.
  iApply (wp_wand with "[]"); first iApply (wp_qinside (domain d) p).
  iIntros (b ->). rewrite bool_decide_false; last exact Hp. iApply wp_if_false. qt_pure.
  iSplit; first done. iSplit; first done. iExists o,(ov nr). iFrame. done.
Qed.
Theorem wp_qt_insert d t v p : tree_rep d t v -∗
  WP qt_insert (Val v) (qi (fst p)) (qi (snd p))
  {{ result, ∃ t', tree_rep d t' v ∗
    ⌜contents t' = insert_set d p (contents t) /\
      result = bv (bool_decide (in_rect (domain d) p /\ p ∉ contents t)) /\
      (result = bv false -> t'=t)⌝ }}.
Proof.
  iIntros "H". destruct (decide (in_rect (domain d) p)) as [Hin|Hout].
  - destruct (decide (p ∈ contents t)) as [Hp|Hnew].
    + iApply (wp_wand with "[H]"); first iApply (wp_insert_duplicate d t v p Hp with "H").
      iIntros (r) "[%Hr H]". iExists t. iFrame. iPureIntro. split.
      * unfold insert_set. rewrite decide_True; last exact Hin. set_solver.
      * split; last done. rewrite Hr bool_decide_false; first done. tauto.
    + iApply (wp_wand with "[H]"); first iApply (wp_qt_insert_set_refinement with "H").
      iIntros (r) "H". iDestruct "H" as (t') "[H %Hr]". destruct Hr as [HS HR].
      iExists t'. iFrame. iPureIntro. split; first done. split; first done.
      rewrite HR bool_decide_true; last tauto. discriminate.
  - iApply (wp_wand with "[H]"); first iApply (wp_insert_rejected d t v p Hout with "H").
    iIntros (r) "[%Hr H]". iExists t. iFrame. iPureIntro. split.
    + unfold insert_set. rewrite decide_False; done.
    + split; last done. rewrite Hr bool_decide_false; first done. tauto.
Qed.
End insertion_contracts.


