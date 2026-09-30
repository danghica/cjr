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

  Lemma wp_field_load_sld (z : loc) (o : loc) (i : nat) (w : val_cjr) :
    StackId z ↦ₛ LitV (LitObj o) -∗
    ObjId o ↦ₒ[i] w -∗
    WP (FieldLoad (sld z) i) {{ v, ⌜ v = w ⌝ }}.
  Proof.
    iIntros "Hlc Hfld".
    unfold sld.
    iApply (wp_bind [FieldLoadCtx i]).
    iApply (wp_stack_load (StackId z) with "Hlc").
    iIntros "!> _ Hlc".
    iApply (wp_field_load with "Hfld").
    iIntros "!> _ Hfld".
    iPureIntro. done.
  Qed.

  Definition rev_step_rest (lacc lcur : Z) (o : loc) (acc nxt : val_cjr) : expr :=
    Seq (FieldStore (Val (LitV (LitObj o))) 2 (Val acc))
      (Seq (sas lacc (Val (LitV (LitObj o)))) (sas lcur (Val nxt))).

  Lemma wp_field_store_sld2 (z1 z2 : loc) (o : loc) (i : nat) (old new : val_cjr) :
    StackId z1 ↦ₛ LitV (LitObj o) -∗
    StackId z2 ↦ₛ new -∗
    ObjId o ↦ₒ[i] old -∗
    WP (FieldStore (sld z1) i (sld z2)) {{ v, ⌜ v = LitV LitUnit ⌝ }}.
  Proof.
    iIntros "H1 H2 Hfld".
    unfold sld, sas.
    iApply (wp_bind [FieldStoreLCtx i (StackLoad (Val (LitV (LitStack z2))))]).
    iApply (wp_stack_load (StackId z1) with "H1").
    iIntros "!> _ H1".
    iApply (wp_bind [FieldStoreRCtx (LitV (LitObj o)) i]).
    iApply (wp_stack_load (StackId z2) with "H2").
    iIntros "!> _ H2".
    iApply (wp_field_store with "Hfld").
    iIntros "!> _ Hfld'".
    iPureIntro. done.
  Qed.

  Lemma wp_stack_copy (la lc : Z) (acc cur : val_cjr) Φ :
    StackId la ↦ₛ acc -∗
    StackId lc ↦ₛ cur -∗
    (StackId la ↦ₛ cur -∗ Φ) -∗
    WP (sas la (sld lc)) {{ _, Φ }}.
  Proof.
    iIntros "Hla Hlc HΦ".
    unfold sas, sld.
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack la))]).
    iApply (wp_stack_load (StackId lc) with "Hlc").
    iIntros "!> _ Hlc".
    iApply (wp_stack_assign with "Hla").
    iIntros "!> _ Hla". iApply ("HΦ" with "Hla").
  Qed.

  Lemma wp_rev_step_rest (xs : list Z) (u_prefix v : list Z) (x : Z) (v' : list Z)
      (lacc lcur : Z) (o : loc) (nxt vacc : val_cjr) :
    rev u_prefix ++ v = xs →
    StackId lacc ↦ₛ vacc -∗
    StackId lcur ↦ₛ LitV (LitObj o) -∗
    is_list v' nxt -∗
    is_list u_prefix vacc -∗
    ObjId o ↦ₒ[2] nxt -∗
    ObjId o ↦ₒ[0] LitV (LitBool true) -∗
    ObjId o ↦ₒ[1] LitV (LitInt x) -∗
    WP (rev_step_rest lacc lcur o vacc nxt)
      {{ _,
         ⌜ rev (x :: u_prefix) ++ v' = xs ⌝ ∗
         StackId lacc ↦ₛ LitV (LitObj o) ∗
         StackId lcur ↦ₛ nxt ∗
         is_list v' nxt ∗
         is_list (x :: u_prefix) (LitV (LitObj o)) }}.
  Proof.
    intros Hpure.
    iIntros "Hacc Hcur Hv' Hlist_u Hnext Ht Hh".
    unfold rev_step_rest, sld, sas.
    iApply (wp_bind [SeqCtx (Seq (sas lacc (Val (LitV (LitObj o)))) (sas lcur (Val nxt)))]).
    iApply (wp_field_store with "Hnext").
    iIntros "!> _ Hnext'".
    iApply (wp_bind [SeqCtx (sas lcur (Val nxt))]).
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack lacc))]).
    iApply wp_value'.
    iApply (wp_stack_assign (StackId lacc) (LitV (LitObj o)) with "Hacc").
    iIntros "!> _ Hacc'".
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack lcur))]).
    iApply wp_value'.
    iApply (wp_stack_assign (StackId lcur) nxt with "Hcur").
    iIntros "!> _ Hcur'".
    iFrame "Hv' Hlist_u". iSplitL "Hacc'"; [iFrame|].
    iSplitL "Hcur'"; [iFrame|].
    iApply (is_list_snoc_acc with "Hlist_u"); iFrame.
    iPureIntro. apply rev_prefix_step; done.
  Qed.

  Lemma wp_rev_step_at (xs : list Z) (u v : list Z) (x : Z) (v' : list Z)
      (lacc lcur : Z) (vacc vcur : val_cjr) :
    v = x :: v' →
    rev u ++ v = xs →
    StackId lacc ↦ₛ vacc -∗
    StackId lcur ↦ₛ vcur -∗
    is_list v vcur -∗
    is_list u vacc -∗
    WP (rev_step_at lacc lcur)
      {{ v,
         ⌜ rev (x :: u) ++ v' = xs ⌝ ∗
         StackId lacc ↦ₛ vcur ∗
         ∃ nxt,
           StackId lcur ↦ₛ nxt ∗
           is_list v' nxt ∗
           is_list (x :: u) vcur }}.
  Proof.
    intros -> Hpure.
    iIntros "Hacc Hcur Hlist_v Hlist_u".
    iDestruct (is_list_cons_destruct x v' vcur with "Hlist_v") as (o nxt) "(Hpo & Ht & Hh & Hnext & Hv')".
    iDestruct "Hpo" as %->.
    unfold rev_step_at, sld, sas.
    iApply (wp_bind [LetCtx (Some "nxt") (rev_step_rest lacc lcur o (Val vacc) (Var "nxt"))]).
    iApply (wp_wand with "[Hcur Hnext]").
    { iApply (wp_field_load_sld lcur o 2 nxt with "Hcur Hnext"). }
    iIntros (w) "%".
    iApply wp_let. simpl.
    iApply (wp_rev_step_rest xs u (x :: v') x v' lacc lcur o nxt vacc with
      "Hacc Hcur Hv' Hlist_u Hnext Ht Hh"); [exact Hpure|].
  Qed.

  Lemma wp_rev_loop (xs : list Z) (la lc : Z) :
    rev_inv xs la lc -∗
    WP (rev_loop_at la lc) {{ _, rev_inv xs la lc }}.
  Proof.
    iIntros "Hinv".
    iDestruct "Hinv" as (u & v & acc & cur & Hpure & Hla & Hlc & Hcur & Hu).
    revert u Hpure Hla Hlc Hcur Hu.
    induction v as [|x v IH]; intros u Hpure Hla Hlc Hcur Hu.
    - iDestruct "Hcur" as (o) "(%Hp & Hfalse & _ & _)".
      rewrite Hp. unfold rev_loop_at, rev_step_at, sld, sas.
      iApply wp_while.
      iApply (wp_bind [IfCtx (Seq (rev_step_at la lc) (rev_loop_at la lc)) (Val (LitV LitUnit))]).
      iApply (wp_bind [FieldLoadCtx 0]).
      iApply (wp_bind [StackLoadCtx]).
      iApply (wp_stack_load (StackId lc) with "Hlc").
      iIntros "!> _ Hlc".
      iApply (wp_field_load with "Hfalse").
      iIntros "!> _ Hfalse".
      iApply wp_if_false. iApply wp_value'.
      iExists u, [], acc, cur. iFrame. iPureIntro. rewrite app_nil_r. done.
    - iApply wp_while.
      iDestruct (is_list_cons_destruct x v cur with "Hcur") as (o & nxt & %Hp & Ht & Hh & Hn & Hv).
      rewrite Hp.
      unfold rev_loop_at, rev_step_at, sld, sas.
      iApply (wp_bind [IfCtx (Seq (rev_step_at la lc) (rev_loop_at la lc)) (Val (LitV LitUnit))]).
      iApply (wp_bind [FieldLoadCtx 0]).
      iApply (wp_bind [StackLoadCtx]).
      iApply (wp_stack_load (StackId lc) with "Hlc").
      iIntros "!> _ Hlc".
      iApply (wp_field_load with "Ht").
      iIntros "!> _ Ht".
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx (rev_loop_at la lc)]).
      iApply (wp_rev_step_at xs u (x :: v) x v la lc acc cur with "Hla Hlc Hcur Hu");
        [reflexivity|done|].
      iIntros "(%Hpure' & Hla' & Hlc' & Hv' & Hu')".
      iApply (wp_wand with "Hv'").
      { iApply IH; [done| | | |]; iFrame. }
      iIntros "!> _". iExists (x :: u), v, cur, nxt. iFrame. iPureIntro. exact Hpure'.
  Qed.

  Lemma reverse_spec (xs : list Z) (l : val_cjr) :
    is_list xs l -∗
    WP call_reverse l {{ v, is_list (rev xs) v }}.
  Proof.
    iIntros "Hl".
    iApply (wp_bind [AppLCtx (Val l)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "acc0")
      (VarBind "acc" (Var "acc0")
        (VarBind "cur" (Var "n") (Seq rev_loop (Var "acc"))))]).
    iApply (wp_wand with "[Hl]").
    { iApply nil_spec. }
    iIntros (acc0) "Hacc0".
    iApply wp_let. simpl.
    iApply (wp_bind [VarBindCtx "acc"
      (VarBind "cur" (Var "n") (Seq rev_loop (Var "acc")))]).
    iApply wp_var_bind. iIntros (la) "Hla".
    iApply (wp_bind [VarBindCtx "cur" (Seq rev_loop (Var "acc"))]).
    iApply wp_var_bind. iIntros (lc) "Hlc".
    iApply (wp_bind [SeqCtx (Var "acc")]).
    rewrite rev_loop_at_subst.
    iApply (wp_wand with "[Hla Hlc Hl]").
    { iExists [], xs, _, _. iFrame "Hla Hlc". iPureIntro. simpl. rewrite app_nil_r. done. }
    iIntros "Hinv".
    iApply (wp_wand with "Hinv").
    { iApply wp_rev_loop. }
    iIntros "Hpost".
    iDestruct "Hpost" as (u & v & acc & cur & Hpure & Hla' & Hlc' & Hcur & Hu).
    assert (v = []) as ->.
    { destruct v as [|? v]; simpl in Hpure; [done|].
      destruct (rev u) as [|? _]; simpl in Hpure; discriminate. }
    rewrite app_nil_r' in Hpure.
    iApply (wp_bind [StackLoadCtx]).
    cbn [subst_var sld]. iApply (wp_stack_load (StackId la) with "Hla'").
    iIntros "!> _ Hla''".
    iPureIntro. rewrite <- (rev_eq_rev u xs) //.
  Qed.

End list_rev.
