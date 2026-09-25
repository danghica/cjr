(** Singly linked lists as final class nodes, and the list equations
cons/head, cons/tail, and emptiness. A node is an object with three fields:
a boolean tag ([true] means cons), the head integer, and the tail.
The empty list is a node whose tag is [false]. Pointer equality is not
in the language, so emptiness is a boolean the program can branch on. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From iris.prelude Require Import options.
Open Scope expr_scope.

Section list.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Fixpoint is_list (xs : list Z) (p : val_cjr) : iProp Σ :=
    match xs with
    | [] =>
        ∃ o, ⌜ p = LitV (LitObj o) ⌝ ∗
          ObjId o ↦ₒ[0] LitV (LitBool false) ∗
          ObjId o ↦ₒ[1] LitV (LitInt 0) ∗
          ObjId o ↦ₒ[2] LitV LitUnit
    | x :: xs' =>
        ∃ o nxt, ⌜ p = LitV (LitObj o) ⌝ ∗
          ObjId o ↦ₒ[0] LitV (LitBool true) ∗
          ObjId o ↦ₒ[1] LitV (LitInt x) ∗
          ObjId o ↦ₒ[2] nxt ∗
          is_list xs' nxt
    end.

  Definition nil_body : expr :=
    New [LitV (LitBool false); LitV (LitInt 0); LitV LitUnit] [].

  Definition cons_body : expr :=
    Let (Some "x") (StructLoad (Var "a") 0)
      (Let (Some "xs") (StructLoad (Var "a") 1)
        (New [] [Val (LitV (LitBool true)); Var "x"; Var "xs"])).

  Definition head_body : expr := FieldLoad (Var "n") 1.
  Definition tail_body : expr := FieldLoad (Var "n") 2.
  Definition empty_body : expr :=
    If (FieldLoad (Var "n") 0)
      (Val (LitV (LitBool false)))
      (Val (LitV (LitBool true))).

  Definition call_nil : expr :=
    App (Rec None None nil_body) (Val (LitV LitUnit)).

  Definition call_cons (x : Z) (p : val_cjr) : expr :=
    App (Rec None (Some "a") cons_body)
      (Val (StructV [LitV (LitInt x); p])).

  Definition call_head (p : val_cjr) : expr :=
    App (Rec None (Some "n") head_body) (Val p).

  Definition call_tail (p : val_cjr) : expr :=
    App (Rec None (Some "n") tail_body) (Val p).

  Definition call_empty (p : val_cjr) : expr :=
    App (Rec None (Some "n") empty_body) (Val p).

  (** [tail (cons x xs)], as a single program. *)
  Definition cons_then_tail (x : Z) (p : val_cjr) : expr :=
    Let (Some "node") (call_cons x p)
      (App (Rec None (Some "n") tail_body) (Var "node")).

  Lemma is_list_obj xs p :
    is_list xs p -∗ ∃ o, ⌜ p = LitV (LitObj o) ⌝ ∗ is_list xs p.
  Proof.
    destruct xs as [|x xs].
    - iIntros "H". iDestruct "H" as (o) "(%Hp & H0 & H1 & H2)".
      iExists o. iSplit; [done|]. iExists o. iSplit; [done|]. iFrame.
    - iIntros "H". iDestruct "H" as (o nxt) "(%Hp & H0 & H1 & H2 & Hxs)".
      iExists o. iSplit; [done|]. iExists o, nxt. iSplit; [done|]. iFrame.
  Qed.

  Lemma wp_new_step vs v es Φ :
    WP New (vs ++ [v]) es {{ Φ }} ⊢ WP New vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (New (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma nil_spec : ⊢ WP call_nil {{ v, is_list [] v }}.
  Proof.
    iApply (wp_bind [AppLCtx (Val (LitV LitUnit))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply wp_new. iIntros (o) "H".
    iDestruct "H" as "[H0 [H1 [H2 _]]]".
    iExists o. iSplit; [done|]. iFrame.
  Qed.

  Lemma cons_spec (x : Z) xs (p : val_cjr) :
    is_list xs p -∗
    WP call_cons x p {{ v, ∃ o, ⌜ v = LitV (LitObj o) ⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitBool true) ∗
      ObjId o ↦ₒ[1] LitV (LitInt x) ∗
      ObjId o ↦ₒ[2] p ∗
      is_list xs p }}.
  Proof.
    iIntros "Hxs".
    iDestruct (is_list_obj with "Hxs") as (op) "[%Hp Hxs]".
    rewrite Hp.
    iApply (wp_bind [AppLCtx (Val (StructV [LitV (LitInt x); LitV (LitObj op)]))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "x")
      (Let (Some "xs") (StructLoad (Val (StructV [LitV (LitInt x); LitV (LitObj op)])) 1)
        (New [] [Val (LitV (LitBool true)); Var "x"; Var "xs"]))]).
    iApply (wp_struct_load [LitV (LitInt x); LitV (LitObj op)] 0 (LitV (LitInt x))).
    { done. }
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "xs")
      (New [] [Val (LitV (LitBool true)); Val (LitV (LitInt x)); Var "xs"])]).
    iApply (wp_struct_load [LitV (LitInt x); LitV (LitObj op)] 1 (LitV (LitObj op))).
    { done. }
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (o) "H".
    iDestruct "H" as "[H0 [H1 [H2 _]]]".
    iExists o. iSplit; [done|]. iFrame.
  Qed.

  Lemma head_spec (x : Z) xs (p : val_cjr) :
    is_list (x :: xs) p -∗
    WP call_head p {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ is_list (x :: xs) p }}.
  Proof.
    iIntros "H". iDestruct "H" as (o nxt) "(%Hp & H0 & H1 & H2 & Hxs)".
    rewrite Hp.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "H1").
    iIntros "!> _ H1".
    iSplit; [done|]. iExists o, nxt. iSplit; [done|]. iFrame.
  Qed.

  Lemma tail_spec (x : Z) xs (p : val_cjr) :
    is_list (x :: xs) p -∗
    WP call_tail p {{ v, is_list xs v ∗
      ∃ o, ⌜ p = LitV (LitObj o) ⌝ ∗
        ObjId o ↦ₒ[0] LitV (LitBool true) ∗
        ObjId o ↦ₒ[1] LitV (LitInt x) ∗
        ObjId o ↦ₒ[2] v }}.
  Proof.
    iIntros "H". iDestruct "H" as (o nxt) "(%Hp & H0 & H1 & H2 & Hxs)".
    rewrite Hp.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "H2").
    iIntros "!> _ H2".
    iSplitL "Hxs"; [iFrame|]. iExists o. iSplit; [done|]. iFrame.
  Qed.

  Lemma empty_nil (p : val_cjr) :
    is_list [] p -∗ WP call_empty p {{ v, ⌜ v = LitV (LitBool true) ⌝ ∗ is_list [] p }}.
  Proof.
    iIntros "H". iDestruct "H" as (o) "(%Hp & H0 & H1 & H2)".
    rewrite Hp.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [IfCtx (Val (LitV (LitBool false))) (Val (LitV (LitBool true)))]).
    iApply (wp_field_load with "H0").
    iIntros "!> _ H0".
    iApply wp_if_false.
    iApply wp_value'.
    iSplit; [done|]. iExists o. iSplit; [done|]. iFrame.
  Qed.

  Lemma empty_cons (x : Z) xs (p : val_cjr) :
    is_list (x :: xs) p -∗
    WP call_empty p {{ v, ⌜ v = LitV (LitBool false) ⌝ ∗ is_list (x :: xs) p }}.
  Proof.
    iIntros "H". iDestruct "H" as (o nxt) "(%Hp & H0 & H1 & H2 & Hxs)".
    rewrite Hp.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [IfCtx (Val (LitV (LitBool false))) (Val (LitV (LitBool true)))]).
    iApply (wp_field_load with "H0").
    iIntros "!> _ H0".
    iApply wp_if_true.
    iApply wp_value'.
    iSplit; [done|]. iExists o, nxt. iSplit; [done|]. iFrame.
  Qed.

  Lemma cons_then_tail_spec (x : Z) xs (p : val_cjr) :
    is_list xs p -∗
    WP cons_then_tail x p {{ v, ⌜ v = p ⌝ ∗ is_list xs v }}.
  Proof.
    iIntros "Hxs".
    iApply (wp_bind [LetCtx (Some "node")
      (App (Rec None (Some "n") tail_body) (Var "node"))]).
    iApply (wp_wand with "[Hxs]").
    { iApply (cons_spec with "Hxs"). }
    iIntros (node) "Hnode".
    iDestruct "Hnode" as (o) "(%Hn & H0 & H1 & H2 & Hxs)".
    iApply wp_let. simpl. rewrite Hn.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "H2").
    iIntros "!> _ H2".
    iClear "H0 H1 H2".
    iSplit; [done|]. iFrame.
  Qed.
End list.
