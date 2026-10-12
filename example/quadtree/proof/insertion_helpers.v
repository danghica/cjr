From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.quadtree.spec Require Import model.
From cjr.quadtree.algorithm Require Import program.
From cjr.quadtree.proof Require Import ownership routing helpers insertion_model.
From iris.prelude Require Import options.
Import ListNotations.
Local Open Scope Z_scope.
Definition insert_self := RecV (Some "qt_insert_node") (Some "args") qt_insert_node_body.
Definition branch_call n d p :=
  subst "node" n (subst "d" (iv (Z.of_nat (S d)))
    (subst "x" (iv (fst p)) (subst "y" (iv (snd p))
      (subst "qt_insert_node" insert_self qt_insert_branch)))).
Definition install_call n d b p a c e f :=
  Seq (FieldStore (Val n) 0 (qi 2))
  (Seq (FieldStore (Val n) 1 (qi 0))
  (Seq (FieldStore (Val n) 2 (qi 0))
  (Seq (FieldStore (Val n) 7 (qi (midx d b)))
  (Seq (FieldStore (Val n) 8 (qi (midy d b)))
  (Seq (FieldStore (Val n) 9 (Val a))
  (Seq (FieldStore (Val n) 10 (Val c))
  (Seq (FieldStore (Val n) 11 (Val e))
  (Seq (FieldStore (Val n) 12 (Val f)) (branch_call n d p))))))))).
Section insertion.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition insert_post d b t n p v : iProp Σ :=
  ∃ t', ⌜valid d b t' /\ contents t' = {[p]} ∪ contents t /\
      v = bv (bool_decide (p ∉ contents t))⌝ ∗ node_rep d b t' n.
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
Lemma wp_branch_call d b ll lr ul ur n p : square (S d) b ->
  valid (S d) b (Branch ll lr ul ur) -> in_rect b p ->
  (forall k t v, valid d (child_box d b k) t -> in_rect (child_box d b k) p ->
    node_rep d (child_box d b k) t v -∗
    WP App (Val insert_self) (Val (StructV [v;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
    {{ r, insert_post d (child_box d b k) t v p r }}) ->
  node_rep (S d) b (Branch ll lr ul ur) n -∗ WP branch_call n d p
  {{ v, insert_post (S d) b (Branch ll lr ul ur) n p v }}.
Proof.
  intros Hb Ht Hp IH. destruct Ht as [Hll [Hlr [Hul Hur]]].
  pose proof (routed_member d b ll lr ul ur p Hb (conj Hll (conj Hlr (conj Hul Hur)))) as Hr.
  pose proof (child_route d b p Hb Hp) as Hin.
  iIntros "Hn". iDestruct "Hn" as (o a c e f ->) "(Hf & Hll & Hlr & Hul & Hur)".
  iDestruct (node_rep_object with "Hll") as %[oa ->].
  iDestruct (node_rep_object with "Hlr") as %[oc ->].
  iDestruct (node_rep_object with "Hul") as %[oe ->].
  iDestruct (node_rep_object with "Hur") as %[of_ ->].
  unfold branch_call, ov. simpl. qt_pure.
  do 5 (qt_read; qt_pure). qt_read; iApply wp_let; simpl. hm_take.
  iApply (wp_wand with "[]"); first iApply wp_qchoose.
  iIntros (v ->). qt_call.
  replace (Z.of_nat (S d) - 1) with (Z.of_nat d) by lia.
  destruct (route d b p) eqn:Hroute; simpl in Hr, Hin |- *.
  - iApply (wp_wand with "[Hll]"). { iApply (IH LL ll (ov oa) Hll Hin with "Hll"). }
    iIntros (v) "H". iDestruct "H" as (t' [Hvalid [Hset Hbool]]) "Hll".
    iExists (Branch t' lr ul ur). iSplit.
    { iPureIntro. split; first (simpl; tauto). split.
      - simpl. rewrite Hset. set_solver.
      - rewrite Hbool. f_equal. apply bool_decide_ext. tauto. }
    iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
  - iApply (wp_wand with "[Hlr]"). { iApply (IH LR lr (ov oc) Hlr Hin with "Hlr"). }
    iIntros (v) "H". iDestruct "H" as (t' [Hvalid [Hset Hbool]]) "Hlr".
    iExists (Branch ll t' ul ur). iSplit.
    { iPureIntro. split; first (simpl; tauto). split.
      - simpl. rewrite Hset. set_solver.
      - rewrite Hbool. f_equal. apply bool_decide_ext. tauto. }
    iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
  - iApply (wp_wand with "[Hul]"). { iApply (IH UL ul (ov oe) Hul Hin with "Hul"). }
    iIntros (v) "H". iDestruct "H" as (t' [Hvalid [Hset Hbool]]) "Hul".
    iExists (Branch ll lr t' ur). iSplit.
    { iPureIntro. split; first (simpl; tauto). split.
      - simpl. rewrite Hset. set_solver.
      - rewrite Hbool. f_equal. apply bool_decide_ext. tauto. }
    iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
  - iApply (wp_wand with "[Hur]"). { iApply (IH UR ur (ov of_) Hur Hin with "Hur"). }
    iIntros (v) "H". iDestruct "H" as (t' [Hvalid [Hset Hbool]]) "Hur".
    iExists (Branch ll lr ul t'). iSplit.
    { iPureIntro. split; first (simpl; tauto). split.
      - simpl. rewrite Hset. set_solver.
      - rewrite Hbool. f_equal. apply bool_decide_ext. tauto. }
    iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
Qed.
Lemma wp_install_call d b ll lr ul ur o p q a c e f : square (S d) b ->
  valid (S d) b (Branch ll lr ul ur) -> in_rect b p ->
  (forall k t v, valid d (child_box d b k) t -> in_rect (child_box d b k) p ->
    node_rep d (child_box d b k) t v -∗
    WP App (Val insert_self) (Val (StructV [v;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
    {{ r, insert_post d (child_box d b k) t v p r }}) ->
  fields o (node_values b 1 q 0 0 uv uv uv uv) -∗
  node_rep d (child_box d b LL) ll a -∗ node_rep d (child_box d b LR) lr c -∗
  node_rep d (child_box d b UL) ul e -∗ node_rep d (child_box d b UR) ur f -∗
  WP install_call (ov o) d b p a c e f {{ v, insert_post (S d) b (Branch ll lr ul ur) (ov o) p v }}.
Proof.
  intros Hb Ht Hp IH. iIntros "Hf Hll Hlr Hul Hur".
  iDestruct (node_rep_object with "Hll") as %[oa ->].
  iDestruct (node_rep_object with "Hlr") as %[oc ->].
  iDestruct (node_rep_object with "Hul") as %[oe ->].
  iDestruct (node_rep_object with "Hur") as %[of_ ->].
  unfold install_call, qi, ov. qt_pure. do 9 (qt_write; qt_pure).
  iApply (wp_branch_call d b ll lr ul ur (ov o) p Hb Ht Hp IH with "[Hf Hll Hlr Hul Hur]").
  iExists o, (ov oa), (ov oc), (ov oe), (ov of_). iFrame. done.
Qed.
Lemma wp_seed_val d b p n : node_rep d b Empty n -∗
  WP App (Val (RecV (Some "qt_seed") (Some "args") qt_seed_body))
    (Val (StructV [n;iv (fst p);iv (snd p)])) {{ v, ⌜v = uv⌝ ∗ node_rep d b (Leaf p) n }}.
Proof.
  iIntros "Hn". iDestruct "Hn" as (o ->) "Hf".
  unfold qt_seed_body, qargs, qi, qu, iv. qt_pure.
  qt_write; qt_pure. qt_write; qt_pure. qt_write; qt_pure.
  iSplit; first done. iExists o. iSplit; first done. iExact "Hf".
Qed.
Lemma wp_split_call d b p q o : square (S d) b -> in_rect b q -> in_rect b p ->
  (forall k t v, valid d (child_box d b k) t -> in_rect (child_box d b k) p ->
    node_rep d (child_box d b k) t v -∗
    WP App (Val insert_self) (Val (StructV [v;iv (Z.of_nat d);iv (fst p);iv (snd p)]))
    {{ r, insert_post d (child_box d b k) t v p r }}) ->
  fields o (node_values b 1 q 0 0 uv uv uv uv) -∗
  WP subst "node" (ov o) (subst "d" (iv (Z.of_nat (S d)))
    (subst "x" (iv (fst p)) (subst "y" (iv (snd p))
      (subst "px" (iv (fst q)) (subst "py" (iv (snd q))
        (subst "qt_insert_node" insert_self qt_split))))))
  {{ v, insert_post (S d) b (Leaf q) (ov o) p v }}.
Proof.
  intros Hb Hq Hp IH. iIntros "Hf". unfold ov. simpl. qt_pure.
  do 3 (qt_read; qt_pure). qt_read; iApply wp_let; simpl. hm_args.
  replace (Z.of_nat (S d) - 1) with (Z.of_nat d) by lia.
  iApply (wp_wand with "[]"); first iApply wp_qt_power_val.
  iIntros (v ->). qt_call.
  iApply (wp_wand with "[]"); first iApply (wp_qt_empty_val d (child_box d b LL)).
  iIntros (a) "Hll". iDestruct (node_rep_object with "Hll") as %[oa ->]. qt_call.
  iApply (wp_wand with "[]"); first iApply (wp_qt_empty_val d (child_box d b LR)).
  iIntros (c) "Hlr". iDestruct (node_rep_object with "Hlr") as %[oc ->]. qt_call.
  iApply (wp_wand with "[]"); first iApply (wp_qt_empty_val d (child_box d b UL)).
  iIntros (e) "Hul". iDestruct (node_rep_object with "Hul") as %[oe ->]. qt_call.
  iApply (wp_wand with "[]"); first iApply (wp_qt_empty_val d (child_box d b UR)).
  iIntros (f) "Hur". iDestruct (node_rep_object with "Hur") as %[of_ ->].
  iApply wp_let; simpl. hm_take.
  iApply (wp_wand with "[]"); first iApply (wp_qchoose d b q oa oc oe of_).
  iIntros (v ->).
  pose proof (child_route d b q Hb Hq) as Hchild.
  destruct (route d b q) eqn:Hroute; simpl in Hchild |- *; qt_call.
  - iApply (wp_wand with "[Hll]"); first iApply (wp_seed_val d _ q (ov oa) with "Hll").
    iIntros (v) "[%Hv Hll]". subst v. iApply wp_seq.
    iApply (wp_wand with "[Hf Hll Hlr Hul Hur]").
    { iApply (wp_install_call d b (Leaf q) Empty Empty Empty o p q (ov oa) (ov oc) (ov oe) (ov of_) Hb (seeded_valid d b LL q Hchild) Hp IH with "Hf Hll Hlr Hul Hur"). }
    iIntros (v) "H". iDestruct "H" as (t' [Ht [HS HB]]) "Hn".
    iExists t'. iFrame. iPureIntro. rewrite (seeded_contents LL q) in HS, HB. done.
  - iApply (wp_wand with "[Hlr]"); first iApply (wp_seed_val d _ q (ov oc) with "Hlr").
    iIntros (v) "[%Hv Hlr]". subst v. iApply wp_seq.
    iApply (wp_wand with "[Hf Hll Hlr Hul Hur]").
    { iApply (wp_install_call d b Empty (Leaf q) Empty Empty o p q (ov oa) (ov oc) (ov oe) (ov of_) Hb (seeded_valid d b LR q Hchild) Hp IH with "Hf Hll Hlr Hul Hur"). }
    iIntros (v) "H". iDestruct "H" as (t' [Ht [HS HB]]) "Hn".
    iExists t'. iFrame. iPureIntro. rewrite (seeded_contents LR q) in HS, HB. done.
  - iApply (wp_wand with "[Hul]"); first iApply (wp_seed_val d _ q (ov oe) with "Hul").
    iIntros (v) "[%Hv Hul]". subst v. iApply wp_seq.
    iApply (wp_wand with "[Hf Hll Hlr Hul Hur]").
    { iApply (wp_install_call d b Empty Empty (Leaf q) Empty o p q (ov oa) (ov oc) (ov oe) (ov of_) Hb (seeded_valid d b UL q Hchild) Hp IH with "Hf Hll Hlr Hul Hur"). }
    iIntros (v) "H". iDestruct "H" as (t' [Ht [HS HB]]) "Hn".
    iExists t'. iFrame. iPureIntro. rewrite (seeded_contents UL q) in HS, HB. done.
  - iApply (wp_wand with "[Hur]"); first iApply (wp_seed_val d _ q (ov of_) with "Hur").
    iIntros (v) "[%Hv Hur]". subst v. iApply wp_seq.
    iApply (wp_wand with "[Hf Hll Hlr Hul Hur]").
    { iApply (wp_install_call d b Empty Empty Empty (Leaf q) o p q (ov oa) (ov oc) (ov oe) (ov of_) Hb (seeded_valid d b UR q Hchild) Hp IH with "Hf Hll Hlr Hul Hur"). }
    iIntros (v) "H". iDestruct "H" as (t' [Ht [HS HB]]) "Hn".
    iExists t'. iFrame. iPureIntro. rewrite (seeded_contents UR q) in HS, HB. done.
Qed.

End insertion.
