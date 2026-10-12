(** Concrete operation sequences inherit the finite-set algebra. *)
From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.quadtree.spec Require Import model.
From cjr.quadtree.algorithm Require Import program.
From cjr.quadtree.proof Require Import ownership correctness insertion.
From iris.prelude Require Import options.
Import ListNotations.
Section algebra.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma wp_insert_set d S v p : is_quadtree d S v -∗
  WP qt_insert (Val v) (qi (fst p)) (qi (snd p))
  {{ result, is_quadtree d (insert_set d p S) v ∗
    ⌜result = bv (bool_decide (in_rect (domain d) p /\ p ∉ S))⌝ }}.
Proof.
  iIntros "H". iDestruct "H" as (t <-) "H".
  iApply (wp_wand with "[H]"); first iApply (wp_qt_insert with "H").
  iIntros (r) "H". iDestruct "H" as (t' ) "[Ht %H]". destruct H as [HS [HR Hpres]].
  iSplitL "Ht"; last done. iExists t'. iFrame. done.
Qed.
Theorem wp_insertion_commutative d S a b p q :
  is_quadtree d S a -∗ is_quadtree d S b -∗
  WP Seq (qt_insert (Val a) (qi (fst p)) (qi (snd p)))
    (Seq (qt_insert (Val a) (qi (fst q)) (qi (snd q)))
      (Seq (qt_insert (Val b) (qi (fst q)) (qi (snd q)))
        (qt_insert (Val b) (qi (fst p)) (qi (snd p)))))
  {{ _, is_quadtree d (insert_set d q (insert_set d p S)) a ∗
         is_quadtree d (insert_set d q (insert_set d p S)) b }}.
Proof.
  iIntros "Ha Hb".
  match goal with |- envs_entails _ (WP Seq ?e ?rest {{ ?P }}) => iApply (wp_bind [SeqCtx rest]) end.
  iApply (wp_wand with "[Ha]"); first iApply (wp_insert_set with "Ha").
  iIntros (res1) "[Ha _]". iApply wp_seq.
  match goal with |- envs_entails _ (WP Seq ?e ?rest {{ ?P }}) => iApply (wp_bind [SeqCtx rest]) end.
  iApply (wp_wand with "[Ha]"); first iApply (wp_insert_set with "Ha").
  iIntros (res2) "[Ha _]". iApply wp_seq.
  match goal with |- envs_entails _ (WP Seq ?e ?rest {{ ?P }}) => iApply (wp_bind [SeqCtx rest]) end.
  iApply (wp_wand with "[Hb]"); first iApply (wp_insert_set with "Hb").
  iIntros (res3) "[Hb _]". iApply wp_seq.
  iApply (wp_wand with "[Hb]"); first iApply (wp_insert_set with "Hb").
  iIntros (res4) "[Hb _]". iEval (rewrite (insertion_commutative d p q S)) in "Hb". iFrame.
Qed.
Theorem wp_insertion_idempotent d S v p : is_quadtree d S v -∗
  WP Seq (qt_insert (Val v) (qi (fst p)) (qi (snd p)))
    (qt_insert (Val v) (qi (fst p)) (qi (snd p)))
  {{ result, ⌜result = bv false⌝ ∗ is_quadtree d (insert_set d p S) v }}.
Proof.
  iIntros "H".
  match goal with |- envs_entails _ (WP Seq ?e ?rest {{ ?P }}) => iApply (wp_bind [SeqCtx rest]) end.
  iApply (wp_wand with "[H]"); first iApply (wp_insert_set with "H").
  iIntros (first_r) "[H _]". iApply wp_seq.
  iApply (wp_wand with "[H]"); first iApply (wp_insert_set with "H").
  iIntros (r) "[H %Hr]". iEval (rewrite insertion_idempotent) in "H". iFrame.
  iPureIntro. rewrite Hr. rewrite bool_decide_false; first done.
  intros [Hin Hnot]. unfold insert_set in Hnot. rewrite decide_True in Hnot; [set_solver|exact Hin].
Qed.
Theorem wp_membership_repeated d t v p : tree_rep d t v -∗
  WP Let (Some "first") (qt_contains (Val v) (qi (fst p)) (qi (snd p)))
    (Let (Some "second") (qt_contains (Val v) (qi (fst p)) (qi (snd p)))
      (Struct [] [Var "first";Var "second"]))
  {{ result, ⌜result = StructV [bv (contains_set p (contents t));bv (contains_set p (contents t))]⌝ ∗ tree_rep d t v }}.
Proof.
  iIntros "H". iDestruct "H" as "[%Hd H]".
  iDestruct "H" as (o n ->) "H".
  iAssert (tree_rep d t (ov o)) with "[H]" as "H".
  { iSplit; first done. iExists o,n. iFrame. done. }
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[H]"); first iApply (wp_qt_contains with "H").
  iIntros (r) "[%Hr H]". subst r. iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[H]"); first iApply (wp_qt_contains with "H").
  iIntros (r) "[%Hr H]". subst r. hm_pure. iFrame. done.
Qed.
Theorem wp_range_repeated d t v r : tree_rep d t v -∗
  WP Let (Some "first") (qt_range (Val v) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r)))
    (Let (Some "second") (qt_range (Val v) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r)))
      (Struct [] [Var "first";Var "second"]))
  {{ result, ∃ a b, ⌜result = StructV [a;b]⌝ ∗ tree_rep d t v ∗
    point_list (query_model r t) a ∗ point_list (query_model r t) b ∗ ⌜NoDup (query_model r t)⌝ }}.
Proof.
  iIntros "H". iDestruct "H" as "[%Hd H]".
  iDestruct "H" as (o n ->) "H".
  iAssert (tree_rep d t (ov o)) with "[H]" as "H".
  { iSplit; first done. iExists o,n. iFrame. done. }
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[H]"); first iApply (wp_qt_range with "H").
  iIntros (a) "(H & Ha & %Hqa)". iDestruct (point_list_object with "Ha") as %[oa ->].
  iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[H]"); first iApply (wp_qt_range with "H").
  iIntros (b) "(H & Hb & %Hqb)". iDestruct (point_list_object with "Hb") as %[ob ->]. hm_pure.
  iExists (ov oa),(ov ob). iFrame. iSplit; first done. iPureIntro. tauto.
Qed.
Theorem wp_range_distributes_union d s t u a b c r :
  contents u = union_set (contents s) (contents t) ->
  tree_rep d s a -∗ tree_rep d t b -∗ tree_rep d u c -∗
  WP Let (Some "left") (qt_range (Val a) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r)))
    (Let (Some "right") (qt_range (Val b) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r)))
      (Let (Some "union") (qt_range (Val c) (qi (xmin r)) (qi (ymin r)) (qi (xmax r)) (qi (ymax r)))
        (Struct [] [Var "left";Var "right";Var "union"])))
  {{ result, ∃ x y z, ⌜result=StructV [x;y;z]⌝ ∗ tree_rep d s a ∗ tree_rep d t b ∗ tree_rep d u c ∗
    point_list (query_model r s) x ∗ point_list (query_model r t) y ∗ point_list (query_model r u) z ∗
    ⌜list_to_set (query_model r u) = union_set (list_to_set (query_model r s)) (list_to_set (query_model r t))⌝ }}.
Proof.
  intros Hun. iIntros "Hs Ht Hu".
  iDestruct "Hs" as "[%Hds Hs]". iDestruct "Hs" as (oa na ->) "Hs".
  iDestruct "Ht" as "[%Hdt Ht]". iDestruct "Ht" as (ob nb ->) "Ht".
  iDestruct "Hu" as "[%Hdu Hu]". iDestruct "Hu" as (oc nc ->) "Hu".
  iAssert (tree_rep d s (ov oa)) with "[Hs]" as "Hs".
  { iSplit; first done. iExists oa,na. iFrame. done. }
  iAssert (tree_rep d t (ov ob)) with "[Ht]" as "Ht".
  { iSplit; first done. iExists ob,nb. iFrame. done. }
  iAssert (tree_rep d u (ov oc)) with "[Hu]" as "Hu".
  { iSplit; first done. iExists oc,nc. iFrame. done. }
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[Hs]"); first iApply (wp_qt_range with "Hs").
  iIntros (x) "(Hs & Hx & _)". iDestruct (point_list_object with "Hx") as %[ox ->]. iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[Ht]"); first iApply (wp_qt_range with "Ht").
  iIntros (y) "(Ht & Hy & _)". iDestruct (point_list_object with "Hy") as %[oy ->]. iApply wp_let; simpl.
  match goal with |- envs_entails _ (WP Let ?name ?e ?rest {{ ?P }}) => iApply (wp_bind [LetCtx name rest]) end.
  iApply (wp_wand with "[Hu]"); first iApply (wp_qt_range with "Hu").
  iIntros (z) "(Hu & Hz & _)". iDestruct (point_list_object with "Hz") as %[oz ->]. hm_pure.
  iExists (ov ox),(ov oy),(ov oz). iFrame. iSplit; first done.
  iPureIntro. rewrite !query_model_contents Hun. apply range_distributes_union.
Qed.
End algebra.
