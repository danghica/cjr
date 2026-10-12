(** Finite-set specification and an independent executable quadtree model.
    Coordinates denote lattice points; rectangle endpoints are half-open. *)
From Coq Require Import ZArith Lia List.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap list fin_sets.
Import ListNotations.
Open Scope Z_scope.

Definition point := (Z * Z)%type.
Record rectangle := Rect { xmin : Z; ymin : Z; xmax : Z; ymax : Z }.
Definition in_rect (r : rectangle) (p : point) : Prop :=
  xmin r <= fst p < xmax r /\ ymin r <= snd p < ymax r.
Global Instance in_rect_dec r p : Decision (in_rect r p) := ltac:(unfold in_rect; solve_decision).
Definition width (d : nat) : Z := 2 ^ Z.of_nat d.
Definition domain (d : nat) := Rect 0 0 (width d) (width d).
Definition square (d : nat) (b : rectangle) : Prop :=
  xmax b = xmin b + width d /\ ymax b = ymin b + width d.
Definition points := gset point.
Definition admissible (d : nat) (S : points) : Prop := forall p, p ∈ S -> in_rect (domain d) p.
Definition insert_set (d : nat) (p : point) (S : points) : points :=
  if decide (in_rect (domain d) p) then {[p]} ∪ S else S.
Definition contains_set (p : point) (S : points) := bool_decide (p ∈ S).
Definition range_set (r : rectangle) (S : points) : points := filter (in_rect r) S.
Definition union_set (S T : points) := S ∪ T.

Lemma insertion_commutative d p q S :
  insert_set d p (insert_set d q S) = insert_set d q (insert_set d p S).
Proof. unfold insert_set; repeat case_decide; set_solver. Qed.
Lemma insertion_idempotent d p S : insert_set d p (insert_set d p S) = insert_set d p S.
Proof. unfold insert_set; repeat case_decide; set_solver. Qed.
Lemma insertion_rejected d p S : ~in_rect (domain d) p -> insert_set d p S = S.
Proof. intros H; unfold insert_set; case_decide; [contradiction|done]. Qed.
Lemma insertion_preserves_domain d p S : admissible d S -> admissible d (insert_set d p S).
Proof. unfold admissible, insert_set; case_decide; set_solver. Qed.
Lemma membership_repeated p S : (contains_set p S, S) = (contains_set p S, S).
Proof. reflexivity. Qed.
Lemma range_repeated r S : (range_set r S, S) = (range_set r S, S).
Proof. reflexivity. Qed.
Lemma range_distributes_union r S T : range_set r (union_set S T) = union_set (range_set r S) (range_set r T).
Proof. unfold range_set, union_set; set_solver. Qed.
Lemma range_empty_rectangle r S : xmax r <= xmin r \/ ymax r <= ymin r -> range_set r S = ∅.
Proof. intros H; unfold range_set. apply set_eq; intros [x y]. rewrite elem_of_filter. unfold in_rect; simpl. set_solver by lia. Qed.

Lemma width_zero : width 0 = 1. Proof. reflexivity. Qed.
Lemma width_succ d : width (S d) = 2 * width d.
Proof. unfold width. rewrite Nat2Z.inj_succ Z.pow_succ_r; [ring|lia]. Qed.
Lemma width_positive d : 0 < width d.
Proof. unfold width; apply Z.pow_pos_nonneg; lia. Qed.
Lemma width_bound d : (d <= 30)%nat -> width d <= 1073741824.
Proof. intros H. change (width d <= width 30). unfold width. apply Z.pow_le_mono_r; lia. Qed.
Lemma root_square d : square d (domain d). Proof. unfold square, domain; simpl; lia. Qed.
Lemma coordinate_int64 d p : (d <= 30)%nat -> in_rect (domain d) p ->
  -9223372036854775808 <= fst p <= 9223372036854775807 /\
  -9223372036854775808 <= snd p <= 9223372036854775807.
Proof. intros Hd Hp. pose proof (width_bound d Hd). unfold in_rect, domain in Hp; simpl in Hp; lia. Qed.

Inductive quadrant := LL | LR | UL | UR.
Global Instance quadrant_eq_dec : EqDecision quadrant := ltac:(solve_decision).
Definition midx (d : nat) (b : rectangle) := xmin b + width d.
Definition midy (d : nat) (b : rectangle) := ymin b + width d.
Definition child_box (d : nat) (b : rectangle) (k : quadrant) :=
  match k with
  | LL => Rect (xmin b) (ymin b) (midx d b) (midy d b)
  | LR => Rect (midx d b) (ymin b) (xmax b) (midy d b)
  | UL => Rect (xmin b) (midy d b) (midx d b) (ymax b)
  | UR => Rect (midx d b) (midy d b) (xmax b) (ymax b)
  end.
Definition route (d : nat) (b : rectangle) (p : point) :=
  if Z.ltb (fst p) (midx d b) then
    if Z.ltb (snd p) (midy d b) then LL else UL
  else if Z.ltb (snd p) (midy d b) then LR else UR.
Lemma child_square d b k : square (S d) b -> square d (child_box d b k).
Proof. unfold square, child_box, midx, midy. rewrite width_succ. destruct k; simpl; intros []; split; lia. Qed.
Lemma child_subset d b k p : square (S d) b -> in_rect (child_box d b k) p -> in_rect b p.
Proof. unfold square, child_box, in_rect, midx, midy. rewrite width_succ. pose proof (width_positive d). destruct k; simpl; intros [] []; lia. Qed.
Lemma child_route d b p : square (S d) b -> in_rect b p -> in_rect (child_box d b (route d b p)) p.
Proof.
  unfold square, in_rect, route, child_box, midx, midy. rewrite width_succ.
  pose proof (width_positive d). intros [] [].
  destruct (Z.ltb_spec (fst p) (xmin b + width d));
    destruct (Z.ltb_spec (snd p) (ymin b + width d)); simpl; split; lia.
Qed.
Lemma child_route_unique d b k p : in_rect (child_box d b k) p -> route d b p = k.
Proof.
  destruct k; unfold child_box, in_rect, route, midx, midy; simpl; intros [];
  destruct (Z.ltb_spec (fst p) (xmin b + width d));
    destruct (Z.ltb_spec (snd p) (ymin b + width d)); try reflexivity; lia.
Qed.
Lemma subdivision_disjoint d b k j p : k <> j ->
  in_rect (child_box d b k) p -> ~in_rect (child_box d b j) p.
Proof. intros H A B. apply H. rewrite <- (child_route_unique d b k p A), <- (child_route_unique d b j p B). reflexivity. Qed.
Lemma subdivision_coverage d b p : square (S d) b ->
  in_rect b p <-> exists k, in_rect (child_box d b k) p.
Proof. intros H. split; [intros Hp; exists (route d b p); by apply child_route|intros [k Hp]; by eapply child_subset]. Qed.
Lemma unit_unique b p q : square 0 b -> in_rect b p -> in_rect b q -> p = q.
Proof. destruct p as [x y], q as [z w]. unfold square, in_rect; rewrite width_zero; simpl. intros [] [] []; assert (Heq : x=z /\ y=w) by lia. destruct Heq as [-> ->]; reflexivity. Qed.

Inductive qtree := Empty | Leaf (p : point) | Branch (ll lr ul ur : qtree).
Fixpoint contents (t : qtree) : points :=
  match t with Empty => ∅ | Leaf p => {[p]} | Branch a b c d => contents a ∪ contents b ∪ contents c ∪ contents d end.
Fixpoint valid (depth : nat) (b : rectangle) (t : qtree) {struct t} : Prop :=
  match t with
  | Empty => True
  | Leaf p => in_rect b p
  | Branch a c e f => match depth with
      | 0%nat => False
      | S d => valid d (child_box d b LL) a /\ valid d (child_box d b LR) c /\
               valid d (child_box d b UL) e /\ valid d (child_box d b UR) f
      end
  end.
Fixpoint height (t : qtree) : nat :=
  match t with Branch a b c d => S (Nat.max (Nat.max (height a) (height b)) (Nat.max (height c) (height d))) | _ => 0 end.
Lemma valid_height d b t : valid d b t -> (height t <= d)%nat.
Proof. revert d b. induction t; intros d b H; simpl; try lia. destruct d; [contradiction|]. destruct H as (Ha&Hb&Hc&Hd). specialize (IHt1 _ _ Ha); specialize (IHt2 _ _ Hb); specialize (IHt3 _ _ Hc); specialize (IHt4 _ _ Hd). lia. Qed.
Lemma valid_contents d b t : square d b -> valid d b t -> forall p, p ∈ contents t -> in_rect b p.
Proof.
  revert d b. induction t; intros d b Hb Ht z Hz; simpl in *.
  - by apply elem_of_empty in Hz.
  - apply elem_of_singleton in Hz. subst z; exact Ht.
  - destruct d; [contradiction|]. destruct Ht as (H1&H2&H3&H4).
    repeat rewrite elem_of_union in Hz. destruct Hz as [[[Hz|Hz]|Hz]|Hz].
    + eapply (child_subset d b LL); [exact Hb|]. eapply IHt1; [by apply child_square|exact H1|exact Hz].
    + eapply (child_subset d b LR); [exact Hb|]. eapply IHt2; [by apply child_square|exact H2|exact Hz].
    + eapply (child_subset d b UL); [exact Hb|]. eapply IHt3; [by apply child_square|exact H3|exact Hz].
    + eapply (child_subset d b UR); [exact Hb|]. eapply IHt4; [by apply child_square|exact H4|exact Hz].

Qed.

Definition select_points (r : rectangle) (xs : list point) := filter (in_rect r) xs.
Lemma select_points_member r xs p : p ∈ select_points r xs <-> p ∈ xs /\ in_rect r p.
Proof. unfold select_points. rewrite elem_of_list_filter; tauto. Qed.
Lemma select_points_set r xs : list_to_set (select_points r xs) = range_set r (list_to_set xs : points).
Proof. apply set_eq; intros p. rewrite elem_of_list_to_set select_points_member /range_set elem_of_filter elem_of_list_to_set. tauto. Qed.

(** Independent reference construction: recursively partition an input list.
    Repeated coordinates collapse at unit cells. *)
Fixpoint build_tree (d : nat) (b : rectangle) (xs : list point) : qtree :=
  match xs with
  | [] => Empty
  | p :: rest => match rest with
      | [] => Leaf p
      | _ :: _ => match d with
          | 0%nat => Leaf p
          | S n => Branch
              (build_tree n (child_box n b LL) (select_points (child_box n b LL) xs))
              (build_tree n (child_box n b LR) (select_points (child_box n b LR) xs))
              (build_tree n (child_box n b UL) (select_points (child_box n b UL) xs))
              (build_tree n (child_box n b UR) (select_points (child_box n b UR) xs))
          end
      end
  end.

Lemma partition_points d b xs : square (S d) b ->
  (forall p, p ∈ xs -> in_rect b p) ->
  (list_to_set (select_points (child_box d b LL) xs) : points) ∪
  list_to_set (select_points (child_box d b LR) xs) ∪
  list_to_set (select_points (child_box d b UL) xs) ∪
  list_to_set (select_points (child_box d b UR) xs) = list_to_set xs.
Proof.
  intros Hb Hxs; apply set_eq; intros p.
  repeat rewrite elem_of_union. repeat rewrite elem_of_list_to_set.
  repeat rewrite select_points_member. split; [tauto|].
  intros Hp. pose proof (child_route d b p Hb (Hxs p Hp)) as Hroute.
  destruct (route d b p); tauto.
Qed.
Lemma build_tree_correct d b xs : square d b ->
  (forall p, p ∈ xs -> in_rect b p) ->
  valid d b (build_tree d b xs) /\ contents (build_tree d b xs) = (list_to_set xs : points).
Proof.
  revert b xs. induction d as [|d IH]; intros b xs Hb Hxs.
  - destruct xs as [|p rest]; [simpl; split; done|].
    destruct rest as [|q rest]; cbn [build_tree valid contents].
    + split; [apply Hxs; set_solver|set_solver].
    + split; [apply Hxs; set_solver|]. apply set_eq; intros z.
      rewrite elem_of_singleton elem_of_list_to_set. split; [intros ->; set_solver|].
      intros Hz. eapply unit_unique; [exact Hb|apply Hxs; exact Hz|apply Hxs; set_solver].
  - destruct xs as [|p rest]; [simpl; split; done|].
    destruct rest as [|q rest]; [simpl; split; [apply Hxs; set_solver|set_solver]|].
    pose proof (IH (child_box d b LL) (select_points (child_box d b LL) (p::q::rest))) as A.
    pose proof (IH (child_box d b LR) (select_points (child_box d b LR) (p::q::rest))) as B.
    pose proof (IH (child_box d b UL) (select_points (child_box d b UL) (p::q::rest))) as C.
    pose proof (IH (child_box d b UR) (select_points (child_box d b UR) (p::q::rest))) as E.
    assert (Hsel : forall k z, z ∈ select_points (child_box d b k) (p::q::rest) -> in_rect (child_box d b k) z).
    { intros k z Hz; by apply select_points_member in Hz as []. }
    destruct (A (child_square d b LL Hb) (Hsel LL)) as [VA EA].
    destruct (B (child_square d b LR Hb) (Hsel LR)) as [VB EB].
    destruct (C (child_square d b UL Hb) (Hsel UL)) as [VC EC].
    destruct (E (child_square d b UR Hb) (Hsel UR)) as [VE EE].
    split; [simpl; tauto|]. simpl. rewrite EA EB EC EE. by apply partition_points.
Qed.

Fixpoint enumerate (t : qtree) : list point :=
  match t with Empty => [] | Leaf p => [p] | Branch a b c d => enumerate a ++ enumerate b ++ enumerate c ++ enumerate d end.
Lemma enumerate_contents t : (list_to_set (enumerate t) : points) = contents t.
Proof. induction t; simpl; set_solver. Qed.
Lemma enumerate_member t p : p ∈ enumerate t <-> p ∈ contents t.
Proof. rewrite -enumerate_contents elem_of_list_to_set; reflexivity. Qed.
Lemma children_enumerate_disjoint d b k j t u p : square (S d) b -> k <> j ->
  valid d (child_box d b k) t -> valid d (child_box d b j) u ->
  p ∈ enumerate t -> p ∈ enumerate u -> False.
Proof.
  intros Hb Hkj Ht Hu Hpt Hpu. apply (subdivision_disjoint d b k j p Hkj).
  - eapply valid_contents; [by apply child_square|exact Ht|by apply enumerate_member].
  - eapply valid_contents; [by apply child_square|exact Hu|by apply enumerate_member].
Qed.
Lemma enumerate_unique d b t : square d b -> valid d b t -> NoDup (enumerate t).
Proof.
  revert d b. induction t; intros d b Hb Ht; simpl in *; [constructor|repeat constructor; set_solver|].
  destruct d; [contradiction|]. destruct Ht as (H1&H2&H3&H4).
  specialize (IHt1 d _ (child_square d b LL Hb) H1).
  specialize (IHt2 d _ (child_square d b LR Hb) H2).
  specialize (IHt3 d _ (child_square d b UL Hb) H3).
  specialize (IHt4 d _ (child_square d b UR Hb) H4).
  assert (D12 : forall p, p ∈ enumerate t1 -> p ∈ enumerate t2 -> False).
  { intros p; exact (children_enumerate_disjoint d b LL LR t1 t2 p Hb ltac:(discriminate) H1 H2). }
  assert (D13 : forall p, p ∈ enumerate t1 -> p ∈ enumerate t3 -> False).
  { intros p; exact (children_enumerate_disjoint d b LL UL t1 t3 p Hb ltac:(discriminate) H1 H3). }
  assert (D14 : forall p, p ∈ enumerate t1 -> p ∈ enumerate t4 -> False).
  { intros p; exact (children_enumerate_disjoint d b LL UR t1 t4 p Hb ltac:(discriminate) H1 H4). }
  assert (D23 : forall p, p ∈ enumerate t2 -> p ∈ enumerate t3 -> False).
  { intros p; exact (children_enumerate_disjoint d b LR UL t2 t3 p Hb ltac:(discriminate) H2 H3). }
  assert (D24 : forall p, p ∈ enumerate t2 -> p ∈ enumerate t4 -> False).
  { intros p; exact (children_enumerate_disjoint d b LR UR t2 t4 p Hb ltac:(discriminate) H2 H4). }
  assert (D34 : forall p, p ∈ enumerate t3 -> p ∈ enumerate t4 -> False).
  { intros p; exact (children_enumerate_disjoint d b UL UR t3 t4 p Hb ltac:(discriminate) H3 H4). }
  repeat rewrite NoDup_app. repeat split; try assumption; set_solver.
Qed.
Definition query_model r t := select_points r (enumerate t).
Lemma query_model_contents r t : (list_to_set (query_model r t) : points) = range_set r (contents t).
Proof. unfold query_model; rewrite select_points_set enumerate_contents; reflexivity. Qed.
Lemma query_model_unique d b t r : square d b -> valid d b t -> NoDup (query_model r t).
Proof. intros Hb Ht. apply NoDup_filter. by eapply enumerate_unique. Qed.
Definition query_state r t := (t, query_model r t).
Lemma query_state_repeated r t :
  let '(t1, a) := query_state r t in let '(t2, b) := query_state r t1 in t2 = t /\ a = b.
Proof. split; reflexivity. Qed.
Definition contains_state p t := (t, contains_set p (contents t)).
Lemma contains_state_repeated p t :
  let '(t1, a) := contains_state p t in let '(t2, b) := contains_state p t1 in t2 = t /\ a = b.
Proof. split; reflexivity. Qed.
Definition union_reference d t u := build_tree d (domain d) (elements (union_set (contents t) (contents u))).
Lemma union_reference_correct d t u : valid d (domain d) t -> valid d (domain d) u ->
  valid d (domain d) (union_reference d t u) /\
  contents (union_reference d t u) = union_set (contents t) (contents u).
Proof.
  intros Ht Hu. unfold union_reference. pose proof (build_tree_correct d (domain d)
    (elements (union_set (contents t) (contents u))) (root_square d)) as H.
  assert (Hin : forall p, p ∈ elements (union_set (contents t) (contents u)) -> in_rect (domain d) p).
  { intros p Hp. apply elem_of_elements in Hp. unfold union_set in Hp. apply elem_of_union in Hp as [Hp|Hp]; [exact (valid_contents d (domain d) t (root_square d) Ht p Hp)|exact (valid_contents d (domain d) u (root_square d) Hu p Hp)]. }
  destruct (H Hin) as [HV HC]. split; [exact HV|rewrite HC; set_solver].
Qed.
Lemma range_tree_union d t u r : valid d (domain d) t -> valid d (domain d) u ->
  (list_to_set (query_model r (union_reference d t u)) : points) =
  (list_to_set (query_model r t) : points) ∪ list_to_set (query_model r u).
Proof. intros Ht Hu. repeat rewrite query_model_contents. rewrite (proj2 (union_reference_correct d t u Ht Hu)). apply range_distributes_union. Qed.
Definition insert_reference d p t :=
  if decide (in_rect (domain d) p) then build_tree d (domain d) (elements ({[p]} ∪ contents t)) else t.
Lemma insert_reference_correct d p t : valid d (domain d) t ->
  valid d (domain d) (insert_reference d p t) /\ contents (insert_reference d p t) = insert_set d p (contents t).
Proof.
  intros Ht. unfold insert_reference, insert_set. case_decide as Hp; [|split; done].
  pose proof (build_tree_correct d (domain d) (elements ({[p]} ∪ contents t)) (root_square d)) as H.
  assert (Hin : forall q, q ∈ elements ({[p]} ∪ contents t) -> in_rect (domain d) q).
  { intros q Hq. apply elem_of_elements in Hq. apply elem_of_union in Hq as [Hq|Hq].
    - apply elem_of_singleton in Hq; subst; done.
    - exact (valid_contents d (domain d) t (root_square d) Ht q Hq). }
  destruct (H Hin) as [HV HC]. split; [exact HV|rewrite HC; set_solver].
Qed.
Lemma reference_insert_commutative d p q t : valid d (domain d) t ->
  contents (insert_reference d p (insert_reference d q t)) = contents (insert_reference d q (insert_reference d p t)).
Proof.
  intros Ht. destruct (insert_reference_correct d q t Ht) as [Vq Eq].
  destruct (insert_reference_correct d p t Ht) as [Vp Ep].
  rewrite (proj2 (insert_reference_correct d p _ Vq)) (proj2 (insert_reference_correct d q _ Vp)) Eq Ep.
  apply insertion_commutative.
Qed.
Lemma reference_insert_idempotent d p t : valid d (domain d) t ->
  contents (insert_reference d p (insert_reference d p t)) = contents (insert_reference d p t).
Proof.
  intros Ht. destruct (insert_reference_correct d p t Ht) as [V E].
  rewrite (proj2 (insert_reference_correct d p _ V)) E. apply insertion_idempotent.
Qed.
