(** Classic in-place list reversal with a separation-logic proof.
Uses the [is_list] predicate and node layout from [list.v]. *)

From Coq Require Import Lia List.
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import list.
From iris.prelude Require Import options.
Open Scope expr_scope.

(** * Pure list algebra for the invariant *)

Lemma app_nil_r' (xs : list Z) : xs ++ [] = xs.
Proof. induction xs as [|z xs IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma app_assoc' (xs ys zs : list Z) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof. induction xs as [|x xs IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma rev_app (xs ys : list Z) : rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - rewrite app_nil_r'. reflexivity.
  - rewrite IH. rewrite app_assoc'. reflexivity.
Qed.

Lemma rev_cons (x : Z) (u : list Z) : rev (x :: u) = rev u ++ [x].
Proof. simpl. done. Qed.

Lemma rev_prefix_step (u v : list Z) (x : Z) (v' : list Z) :
  v = x :: v' → rev (x :: u) ++ v' = rev u ++ v.
Proof.
  intros ->. rewrite rev_cons. rewrite app_assoc'. simpl. reflexivity.
Qed.

Lemma rev_prefix_nil (u : list Z) :
  rev u ++ [] = rev u.
Proof. apply app_nil_r'. Qed.

Lemma rev_rev (xs : list Z) : rev (rev xs) = xs.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite rev_app. simpl. rewrite IH. reflexivity.
Qed.

Lemma rev_eq_rev (u xs : list Z) : rev u = xs → u = rev xs.
Proof.
  intros Heq. transitivity (rev (rev u)).
  - symmetry. apply rev_rev.
  - f_equal. exact Heq.
Qed.

Section list_rev.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Import list.

  Definition sld (z : Z) : expr := StackLoad (Val (LitV (LitStack z))).
  Definition sas (z : Z) (e : expr) : expr :=
    StackAssign (Val (LitV (LitStack z))) e.

  Definition rev_step : expr :=
    Let (Some "nxt") (FieldLoad (Var "cur") 2)
      (Seq (FieldStore (Var "cur") 2 (Var "acc"))
        (Seq (Assign "acc" (Var "cur"))
          (Assign "cur" (Var "nxt")))).

  Definition rev_loop : expr :=
    While (FieldLoad (Var "cur") 0) rev_step.

  Definition rev_body : expr :=
    Let (Some "acc0") call_nil
      (VarBind "acc" (Var "acc0")
        (VarBind "cur" (Var "n")
          (Seq rev_loop (Var "acc")))).

  Definition call_reverse (p : val_cjr) : expr :=
    App (Rec None (Some "n") rev_body) (Val p).

  Definition rev_step_at (la lc : Z) : expr :=
    Let (Some "nxt") (FieldLoad (sld lc) 2)
      (Seq (FieldStore (sld lc) 2 (sld la))
        (Seq (sas la (sld lc)) (sas lc (Var "nxt")))).

  Definition rev_loop_at (la lc : Z) : expr :=
    While (FieldLoad (sld lc) 0) (rev_step_at la lc).

  Lemma rev_step_at_subst (la lc : Z) :
    subst_var "acc" la (subst_var "cur" lc rev_step) = rev_step_at la lc.
  Proof.
    cbn [rev_step subst_var sas sld]. f_equal; repeat f_equal; reflexivity.
  Qed.

  Lemma rev_loop_at_subst (la lc : Z) :
    subst_var "acc" la (subst_var "cur" lc rev_loop) = rev_loop_at la lc.
  Proof.
    unfold rev_loop_at. cbn [rev_loop subst_var sld].
    rewrite rev_step_at_subst. reflexivity.
  Qed.

  Definition rev_inv (xs : list Z) (la lc : Z) : iProp Σ :=
    ∃ u v acc cur,
      ⌜ rev u ++ v = xs ⌝ ∗
      StackId la ↦ₛ acc ∗
      StackId lc ↦ₛ cur ∗
      is_list v cur ∗
      is_list u acc.

  Lemma is_list_cons_destruct (x : Z) (v : list Z) (p : val_cjr) :
    is_list (x :: v) p -∗
    ∃ o nxt, ⌜ p = LitV (LitObj o) ⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitBool true) ∗
      ObjId o ↦ₒ[1] LitV (LitInt x) ∗
      ObjId o ↦ₒ[2] nxt ∗
      is_list v nxt.
  Proof.
    iIntros "H". iDestruct "H" as (o nxt) "(%Hp & H0 & H1 & H2 & Hv)".
    iExists o, nxt. iSplit; [done|]. iFrame.
  Qed.

  Lemma is_list_snoc_acc (x : Z) (u : list Z) (acc : val_cjr) (o : loc) :
    is_list u acc -∗
    ObjId o ↦ₒ[0] LitV (LitBool true) -∗
    ObjId o ↦ₒ[1] LitV (LitInt x) -∗
    ObjId o ↦ₒ[2] acc -∗
    is_list (x :: u) (LitV (LitObj o)).
  Proof.
    iIntros "Hu H0 H1 H2". iExists o, acc. iSplit; [done|]. iFrame.
  Qed.

  (** One iteration preserves all ownership and moves one node to [acc]. *)
  Lemma wp_rev_step_at (xs u : list Z) (x : Z) (v : list Z)
      (la lc : Z) (acc cur : val_cjr) :
    rev u ++ x :: v = xs →
    StackId la ↦ₛ acc -∗ StackId lc ↦ₛ cur -∗
    is_list (x :: v) cur -∗ is_list u acc -∗
    WP (rev_step_at la lc)
      {{ _, ∃ nxt,
         ⌜ rev (x :: u) ++ v = xs ⌝ ∗
         StackId la ↦ₛ cur ∗ StackId lc ↦ₛ nxt ∗
         is_list v nxt ∗ is_list (x :: u) cur }}.
  Proof.
    intros Hpure. iIntros "Ha Hc Hv Hu".
    iDestruct (is_list_cons_destruct with "Hv") as (o nxt)
      "(%Hp & Htag & Hhead & Hnext & Hv)".
    subst cur. unfold rev_step_at, sld, sas.
    iApply (wp_bind [LetCtx (Some "nxt")
      (Seq (FieldStore (StackLoad (Val (LitV (LitStack lc)))) 2
              (StackLoad (Val (LitV (LitStack la)))))
        (Seq (StackAssign (Val (LitV (LitStack la)))
                (StackLoad (Val (LitV (LitStack lc)))))
          (StackAssign (Val (LitV (LitStack lc))) (Var "nxt"))))]).
    iApply (wp_bind [FieldLoadCtx 2]).
    iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
    iApply (wp_field_load with "Hnext"). iIntros "!> _ Hnext".
    iApply wp_let. simpl.
    iApply (wp_bind [SeqCtx
      (Seq (StackAssign (Val (LitV (LitStack la)))
              (StackLoad (Val (LitV (LitStack lc)))))
        (StackAssign (Val (LitV (LitStack lc))) (Val nxt)))]).
    iApply (wp_bind [FieldStoreLCtx 2 (StackLoad (Val (LitV (LitStack la))))]).
    iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
    iApply (wp_bind [FieldStoreRCtx (LitV (LitObj o)) 2]).
    iApply (wp_stack_load with "Ha"). iIntros "!> _ Ha".
    iApply (wp_field_store with "Hnext"). iIntros "!> _ Hnext".
    iApply wp_seq.
    iApply (wp_bind [SeqCtx (StackAssign (Val (LitV (LitStack lc))) (Val nxt))]).
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack la))]).
    iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
    iApply (wp_stack_assign with "Ha"). iIntros "!> _ Ha".
    iApply wp_seq.
    iApply (wp_stack_assign with "Hc"). iIntros "!> _ Hc".
    iExists nxt. iSplit.
    { iPureIntro. rewrite (rev_prefix_step u (x :: v) x v); done. }
    iFrame "Ha Hc Hv".
    iApply (is_list_snoc_acc with "Hu Htag Hhead Hnext").
  Qed.

  (** The exit condition is part of the postcondition, not just the invariant. *)
  Definition rev_done (xs : list Z) (la lc : Z) : iProp Σ :=
    ∃ acc cur, StackId la ↦ₛ acc ∗ StackId lc ↦ₛ cur ∗
      is_list (rev xs) acc ∗ is_list [] cur.

  Lemma wp_rev_loop_run (xs v : list Z) (la lc : Z) :
    ∀ u acc cur, rev u ++ v = xs →
    StackId la ↦ₛ acc -∗ StackId lc ↦ₛ cur -∗
    is_list v cur -∗ is_list u acc -∗
    WP (rev_loop_at la lc) {{ _, rev_done xs la lc }}.
  Proof.
    induction v as [|x v IH]; intros u acc cur Hpure;
      iIntros "Ha Hc Hv Hu".
    - iDestruct "Hv" as (o) "(%Hp & Htag & Hhead & Hnext)".
      subst cur. unfold rev_loop_at at 1.
      iApply wp_while.
      iApply (wp_bind [IfCtx
        (Seq (rev_step_at la lc) (While (FieldLoad (sld lc) 0) (rev_step_at la lc)))
        (Val (LitV LitUnit))]).
      iApply (wp_bind [FieldLoadCtx 0]).
      iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
      iApply (wp_field_load with "Htag"). iIntros "!> _ Htag".
      iApply wp_if_false. iApply wp_value'.
      rewrite app_nil_r' in Hpure.
      apply rev_eq_rev in Hpure. subst u.
      iExists acc, (LitV (LitObj o)). iFrame "Ha Hc Hu".
      iExists o. iSplit; [done|]. iFrame.
    - iDestruct (is_list_cons_destruct with "Hv") as (o nxt)
        "(%Hp & Htag & Hhead & Hnext & Hv)".
      subst cur. unfold rev_loop_at at 1.
      iApply wp_while.
      iApply (wp_bind [IfCtx
        (Seq (rev_step_at la lc) (While (FieldLoad (sld lc) 0) (rev_step_at la lc)))
        (Val (LitV LitUnit))]).
      iApply (wp_bind [FieldLoadCtx 0]).
      iApply (wp_stack_load with "Hc"). iIntros "!> _ Hc".
      iApply (wp_field_load with "Htag"). iIntros "!> _ Htag".
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx (rev_loop_at la lc)]).
      iApply (wp_wand with "[Ha Hc Htag Hhead Hnext Hv Hu]").
      { iApply (wp_rev_step_at xs u x v with "Ha Hc [Htag Hhead Hnext Hv] Hu").
        - exact Hpure.
        - iExists o, nxt. iSplit; [done|]. iFrame. }
      iIntros (w) "Hstep".
      iDestruct "Hstep" as (nxt') "(%Hpure' & Ha & Hc & Hv & Hu)".
      iApply wp_seq.
      iApply (IH (x :: u) (LitV (LitObj o)) nxt' Hpure' with "Ha Hc Hv Hu").
  Qed.

  Lemma wp_rev_loop (xs : list Z) (la lc : Z) :
    rev_inv xs la lc -∗
    WP (rev_loop_at la lc) {{ _, rev_done xs la lc }}.
  Proof.
    iIntros "Hinv".
    iDestruct "Hinv" as (u v acc cur) "(%Hpure & Ha & Hc & Hv & Hu)".
    iApply (wp_rev_loop_run xs v la lc u acc cur Hpure with "Ha Hc Hv Hu").
  Qed.

  Lemma reverse_spec (xs : list Z) (l : val_cjr) :
    is_list xs l -∗
    WP call_reverse l {{ v, is_list (rev xs) v }}.
  Proof.
    iIntros "Hl".
    iDestruct (is_list_obj with "Hl") as (ol) "(%Hl & Hl)".
    subst l. unfold call_reverse.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj ol)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. cbn [rev_body subst].
    iApply (wp_bind [LetCtx (Some "acc0")
      (VarBind "acc" (Var "acc0")
        (VarBind "cur" (Val (LitV (LitObj ol))) (Seq rev_loop (Var "acc"))))]).
    iApply (wp_wand with "[]").
    { iApply nil_spec. }
    iIntros (acc0) "Hnil". iApply wp_let. simpl.
    iApply wp_var_bind. iIntros (la) "Ha". simpl.
    iApply wp_var_bind. iIntros (lc) "Hc". simpl.
    change (subst_var "cur" lc (subst_var "acc" la rev_loop))
      with (rev_loop_at la lc).
    iApply (wp_bind [SeqCtx (sld la)]).
    iApply (wp_wand with "[Ha Hc Hl Hnil]").
    { iApply wp_rev_loop. iExists [], xs, acc0, (LitV (LitObj ol)).
      iSplit; [done|]. iFrame. }
    iIntros (w) "Hdone".
    iDestruct "Hdone" as (acc cur) "(Ha & Hc & Hrev & Hnil)".
    iApply wp_seq.
    iApply (wp_stack_load with "Ha"). iIntros "!> _ Ha".
    iExists cur. iFrame "Hc".
    iExists acc. iFrame "Ha Hrev".
  Qed.

  Definition reverse_twice (p : val_cjr) : expr :=
    Let (Some "r") (call_reverse p)
      (App (Rec None (Some "n") rev_body) (Var "r")).

  (** Double reversal restores contents; it need not restore the sentinel. *)
  Lemma reverse_twice_spec (xs : list Z) (p : val_cjr) :
    is_list xs p -∗ WP reverse_twice p {{ v, is_list xs v }}.
  Proof.
    iIntros "Hl". unfold reverse_twice.
    iApply (wp_bind [LetCtx (Some "r")
      (App (Rec None (Some "n") rev_body) (Var "r"))]).
    iApply (wp_wand with "[Hl]").
    { iApply (reverse_spec with "Hl"). }
    iIntros (r) "Hr". iApply wp_let. simpl.
    iApply (wp_wand with "[Hr]").
    { iApply (reverse_spec with "Hr"). }
    iIntros (v) "Hv". rewrite rev_rev. iFrame.
  Qed.

End list_rev.
