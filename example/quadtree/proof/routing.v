From iris.proofmode Require Import proofmode.
From cjr.quadtree.spec Require Import model.
From iris.prelude Require Import options.
Definition child_tree {A : Type} (k : quadrant) (ll lr ul ur : A) : A := match k with LL=>ll | LR=>lr | UL=>ul | UR=>ur end.
Lemma routed_member d b ll lr ul ur p : square (S d) b ->
  valid (S d) b (Branch ll lr ul ur) ->
  (p ∈ contents (Branch ll lr ul ur) <-> p ∈ contents (child_tree (route d b p) ll lr ul ur)).
Proof.
  intros Hb [Hll [Hlr [Hul Hur]]].
  assert (Hr : forall k t, valid d (child_box d b k) t -> p ∈ contents t -> route d b p = k).
  { intros k t Ht Hp. apply (child_route_unique d b k p).
    exact (valid_contents d (child_box d b k) t (child_square d b k Hb) Ht p Hp). }
  assert (Hllr : p ∈ contents ll -> route d b p = LL) by (intros; eauto).
  assert (Hlrr : p ∈ contents lr -> route d b p = LR) by (intros; eauto).
  assert (Hulr : p ∈ contents ul -> route d b p = UL) by (intros; eauto).
  assert (Hurr : p ∈ contents ur -> route d b p = UR) by (intros; eauto).
  destruct (route d b p) eqn:Hroute; simpl; set_solver.
Qed.
Definition overlap (b r : rectangle) := xmin b < xmax r /\ xmin r < xmax b /\ ymin b < ymax r /\ ymin r < ymax b.
Global Instance overlap_dec b r : Decision (overlap b r).
Proof. unfold overlap; solve_decision. Defined.
Lemma query_pruned d b t r : square d b -> valid d b t -> ~overlap b r -> query_model r t = [].
Proof.
  intros Hb Ht Hno.
  assert (Hnone : forall p, p ∉ query_model r t).
  { intros p Hp. unfold query_model, select_points in Hp. apply elem_of_list_filter in Hp as [Hrp Hp].
    pose proof (valid_contents d b t Hb Ht p (proj1 (enumerate_member t p) Hp)).
    unfold in_rect, overlap in *. intuition lia. }
  destruct (query_model r t) as [|p xs] eqn:E; first done.
  exfalso. apply (Hnone p). by apply elem_of_list_here.
Qed.
