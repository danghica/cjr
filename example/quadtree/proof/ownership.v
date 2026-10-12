(** Exclusive ownership records every node field, including unused fields.
    Queries preserve the same tree witness and hence the concrete topology. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From cjr.quadtree.spec Require Import model.
From iris.prelude Require Import options.
Import ListNotations.
Definition iv (z : Z) := LitV (LitInt z).
Definition bv (b : bool) := LitV (LitBool b).
Definition ov (o : Z) := LitV (LitObj o).
Definition uv := LitV LitUnit.
Definition node_values (b : rectangle) (tag : Z) (p : point) (mx my : Z) (ll lr ul ur : val_cjr) :=
  [iv tag;iv (fst p);iv (snd p);iv (xmin b);iv (ymin b);iv (xmax b);iv (ymax b);
   iv mx;iv my;ll;lr;ul;ur].
Section ownership.
Context `{!cjrGS Σ}.
Definition fields (o : Z) (vs : list val_cjr) : iProp Σ :=
  [∗ list] i↦v ∈ vs, ObjId o ↦ₒ[i] v.
Fixpoint node_rep (d : nat) (b : rectangle) (t : qtree) (n : val_cjr) {struct t} : iProp Σ :=
  match t with
  | Empty => ∃ o, ⌜n = ov o⌝ ∗ fields o (node_values b 0 (0,0) 0 0 uv uv uv uv)
  | Leaf p => ∃ o, ⌜n = ov o⌝ ∗ fields o (node_values b 1 p 0 0 uv uv uv uv)
  | Branch ll lr ul ur => match d with
      | 0%nat => False
      | S h => ∃ o a c e f, ⌜n = ov o⌝ ∗
          fields o (node_values b 2 (0,0) (midx h b) (midy h b) a c e f) ∗
          node_rep h (child_box h b LL) ll a ∗ node_rep h (child_box h b LR) lr c ∗
          node_rep h (child_box h b UL) ul e ∗ node_rep h (child_box h b UR) ur f
      end
  end.
Fixpoint point_list (xs : list point) (v : val_cjr) : iProp Σ :=
  match xs with
  | [] => ∃ o, ⌜v = ov o⌝ ∗ fields o [bv false;iv 0;iv 0;uv]
  | (x,y)::rest => ∃ o tail, ⌜v = ov o⌝ ∗ fields o [bv true;iv x;iv y;tail] ∗ point_list rest tail
  end.
Definition tree_rep (d : nat) (t : qtree) (v : val_cjr) : iProp Σ :=
  ⌜(d <= 30)%nat /\ valid d (domain d) t⌝ ∗
  ∃ o root, ⌜v = ov o⌝ ∗ fields o [iv (Z.of_nat d);iv (width d);root] ∗ node_rep d (domain d) t root.
Definition is_quadtree (d : nat) (S : points) (v : val_cjr) : iProp Σ :=
  ∃ t, ⌜contents t = S⌝ ∗ tree_rep d t v.
Lemma fields_lookup o vs i v : vs !! i = Some v ->
  fields o vs -∗ ObjId o ↦ₒ[i] v ∗ (ObjId o ↦ₒ[i] v -∗ fields o vs).
Proof. intros H. iIntros "Hf". iApply (big_sepL_lookup_acc with "Hf"); exact H. Qed.
Lemma fields_update o vs i v : vs !! i = Some v ->
  fields o vs -∗ ObjId o ↦ₒ[i] v ∗ (∀ w, ObjId o ↦ₒ[i] w -∗ fields o (<[i:=w]> vs)).
Proof. intros H. iIntros "Hf". iApply (big_sepL_insert_acc with "Hf"); exact H. Qed.
Lemma tree_domain d S v : is_quadtree d S v -∗ ⌜admissible d S⌝.
Proof.
  iIntros "H". iDestruct "H" as (t <-) "H". iDestruct "H" as "[%H _]".
  iPureIntro. destruct H as [Hd Ht]. intros p Hp. exact (valid_contents d (domain d) t (root_square d) Ht p Hp).
Qed.
Lemma point_list_object xs v : point_list xs v -∗ ⌜∃ o, v = ov o⌝.
Proof.
  destruct xs as [|[x y] xs]; simpl; iIntros "H".
  - iDestruct "H" as (o ->) "_". eauto.
  - iDestruct "H" as (o tail ->) "_". eauto.
Qed.
Lemma node_rep_object d b t v : node_rep d b t v -∗ ⌜∃ o, v = ov o⌝.
Proof.
  destruct t; simpl; iIntros "H".
  - iDestruct "H" as (o ->) "_". eauto.
  - iDestruct "H" as (o ->) "_". eauto.
  - destruct d; first by iDestruct "H" as %[].
    iDestruct "H" as (o a c e f ->) "_". eauto.
Qed.
End ownership.
