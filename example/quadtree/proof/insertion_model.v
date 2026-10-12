From cjr.quadtree.proof Require Import routing.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From cjr.quadtree.spec Require Import model.
Definition seeded (k : quadrant) (p : point) := match k with
  LL => Branch (Leaf p) Empty Empty Empty | LR => Branch Empty (Leaf p) Empty Empty |
  UL => Branch Empty Empty (Leaf p) Empty | UR => Branch Empty Empty Empty (Leaf p) end.
Lemma seeded_valid d b k p : in_rect (child_box d b k) p -> valid (S d) b (seeded k p).
Proof. destruct k; simpl; tauto. Qed.
Lemma seeded_contents k p : contents (seeded k p) = {[p]}.
Proof. destruct k; simpl; set_solver. Qed.
