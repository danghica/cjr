(** Arrays as a library: a final class holding a length and a pointer to a
contiguous raw block. [make] allocates [n] zero words. [get] and [set] use
word offsets. The equations are the usual ones: reading a cell just written
returns that value, reading a different cell is unchanged, and [set] preserves
the length. Allocation of zero words is stuck, so [n] is positive. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From iris.prelude Require Import options.
From Coq Require Import Lia.
Open Scope expr_scope.

Section array.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition array_cells (base : Z) (xs : list Z) : iProp Σ :=
    [∗ list] i ↦ x ∈ xs, RawId (base + Z.of_nat i)%Z ↦ᵣ LitV (LitInt x).

  Definition is_array (xs : list Z) (a : val_cjr) : iProp Σ :=
    ∃ o base, ⌜ a = LitV (LitObj o) ⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitInt (Z.of_nat (length xs))) ∗
      ObjId o ↦ₒ[1] LitV (LitPtr base) ∗
      RawId base ↦ᵦ length xs ∗
      array_cells base xs.

  Lemma seq_zero_cells base n :
    ([∗ list] i ∈ seq 0 n, RawId (base + Z.of_nat i)%Z ↦ᵣ LitV (LitInt 0)) ⊢
    array_cells base (replicate n 0%Z).
  Proof.
    revert base. induction n as [|n IH]; intros base.
    - by rewrite big_sepL_nil.
    - rewrite seq_S big_sepL_snoc replicate_S_end.
      rewrite /array_cells big_sepL_app big_sepL_singleton.
      rewrite length_replicate Nat.add_0_r.
      apply bi.sep_mono; [apply IH|done].
  Qed.

  Definition make_body : expr :=
    Let (Some "p") (Alloc (Var "n"))
      (New [] [Var "n"; Var "p"]).

  Definition length_body : expr := FieldLoad (Var "a") 0.

  Definition get_body : expr :=
    Let (Some "arr") (StructLoad (Var "args") 0)
      (Let (Some "i") (StructLoad (Var "args") 1)
        (Let (Some "p") (FieldLoad (Var "arr") 1)
          (Load (Offset (Var "p") (Var "i"))))).

  Definition set_body : expr :=
    Let (Some "arr") (StructLoad (Var "args") 0)
      (Let (Some "i") (StructLoad (Var "args") 1)
        (Let (Some "x") (StructLoad (Var "args") 2)
          (Let (Some "p") (FieldLoad (Var "arr") 1)
            (Store (Offset (Var "p") (Var "i")) (Var "x"))))).

  Definition call_make (n : Z) : expr :=
    App (Rec None (Some "n") make_body) (Val (LitV (LitInt n))).

  Definition call_length (a : val_cjr) : expr :=
    App (Rec None (Some "a") length_body) (Val a).

  Definition call_get (a : val_cjr) (i : Z) : expr :=
    App (Rec None (Some "args") get_body)
      (Val (StructV [a; LitV (LitInt i)])).

  Definition call_set (a : val_cjr) (i x : Z) : expr :=
    App (Rec None (Some "args") set_body)
      (Val (StructV [a; LitV (LitInt i); LitV (LitInt x)])).

  Definition set_then_get (a : val_cjr) (i j x : Z) : expr :=
    Let None (call_set a i x) (call_get a j).

  Definition set_then_length (a : val_cjr) (i x : Z) : expr :=
    Let None (call_set a i x) (call_length a).

  Definition length_at (arr : expr) : expr :=
    App (Rec None (Some "a") length_body) arr.

  Definition make_then_get (n i : nat) : expr :=
    Let (Some "a") (call_make (Z.of_nat n))
      (Let (Some "s")
        (Struct [] [Var "a"; Val (LitV (LitInt (Z.of_nat i)))])
        (App (Rec None (Some "args") get_body) (Var "s"))).

  Definition make_then_length (n : nat) : expr :=
    Let (Some "a") (call_make (Z.of_nat n)) (length_at (Var "a")).

  Lemma wp_new_step vs v es Φ :
    WP New (vs ++ [v]) es {{ Φ }} ⊢ WP New vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (New (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_struct_step vs v es Φ :
    WP Struct (vs ++ [v]) es {{ Φ }} ⊢ WP Struct vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (Struct (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma make_spec (n : nat) :
    (0 < n)%nat →
    ⊢ WP call_make (Z.of_nat n) {{ a, is_array (replicate n 0%Z) a }}.
  Proof.
    iIntros (Hn).
    iApply (wp_bind [AppLCtx (Val (LitV (LitInt (Z.of_nat n))))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (New [] [Val (LitV (LitInt (Z.of_nat n))); Var "p"])]).
    iApply wp_alloc; [lia|].
    iIntros (base) "Hcells".
    iIntros "Hblk".
    iEval (rewrite Nat2Z.id) in "Hblk".
    iEval (rewrite Nat2Z.id) in "Hcells".
    iApply wp_let. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (o) "H".
    iDestruct "H" as "[Hlen [Hptr _]]".
    iExists o, base. iSplit; [done|].
    rewrite length_replicate.
    iFrame "Hlen Hptr Hblk".
    iApply (seq_zero_cells with "Hcells").
  Qed.

  Lemma length_spec xs (a : val_cjr) :
    is_array xs a -∗
    WP call_length a
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs))) ⌝ ∗ is_array xs a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "Hlen").
    iIntros "!> _ Hlen".
    iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma get_spec xs (a : val_cjr) (i : nat) x :
    xs !! i = Some x →
    is_array xs a -∗
    WP call_get a (Z.of_nat i)
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ is_array xs a }}.
  Proof.
    iIntros (Hi) "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i))]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "arr")
      (Let (Some "i") (StructLoad (Val arg) 1)
        (Let (Some "p") (FieldLoad (Var "arr") 1)
          (Load (Offset (Var "p") (Var "i")))))]).
    iApply (wp_struct_load [LitV (LitObj o); LitV (LitInt (Z.of_nat i))] 0
              (LitV (LitObj o))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "i")
      (Let (Some "p") (FieldLoad (Val (LitV (LitObj o))) 1)
        (Load (Offset (Var "p") (Var "i"))))]).
    iApply (wp_struct_load [LitV (LitObj o); LitV (LitInt (Z.of_nat i))] 1
              (LitV (LitInt (Z.of_nat i)))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Load (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i))))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr".
    iApply wp_let. simpl.
    iApply (wp_bind [LoadCtx]).
    iApply wp_offset.
    iIntros "!> _".
    iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_load with "Hi").
    iIntros "!> _ Hi".
    iDestruct ("Hclose" with "Hi") as "Hcells".
    iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma set_spec xs (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_array xs a -∗
    WP call_set a (Z.of_nat i) x
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗ is_array (<[i := x]> xs) a }}.
  Proof.
    iIntros (Hi) "Ha".
    assert (length (<[i := x]> xs) = length xs) as Heqlen
      by (apply length_insert; eapply lookup_lt_Some; exact Hi).
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i)); LitV (LitInt x)]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "arr")
      (Let (Some "i") (StructLoad (Val arg) 1)
        (Let (Some "x") (StructLoad (Val arg) 2)
          (Let (Some "p") (FieldLoad (Var "arr") 1)
            (Store (Offset (Var "p") (Var "i")) (Var "x")))))]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "i")
      (Let (Some "x") (StructLoad (Val arg) 2)
        (Let (Some "p") (FieldLoad (Val (LitV (LitObj o))) 1)
          (Store (Offset (Var "p") (Var "i")) (Var "x"))))]).
    iApply (wp_struct_load _ 1 (LitV (LitInt (Z.of_nat i)))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "x")
      (Let (Some "p") (FieldLoad (Val (LitV (LitObj o))) 1)
        (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i))))) (Var "x")))]).
    iApply (wp_struct_load _ 2 (LitV (LitInt x))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i)))))
        (Val (LitV (LitInt x))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr".
    iApply wp_let. simpl.
    iApply (wp_bind [StoreLCtx (Val (LitV (LitInt x)))]).
    iApply wp_offset.
    iIntros "!> _".
    iDestruct (big_sepL_insert_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_store with "Hi").
    iIntros "!> _ Hi".
    iDestruct ("Hclose" $! x with "Hi") as "Hcells".
    iSplit; [done|].
    iEval (rewrite <- Heqlen) in "Hlen".
    iEval (rewrite <- Heqlen) in "Hblk".
    iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma set_then_get_same xs (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_array xs a -∗
    WP set_then_get a (Z.of_nat i) (Z.of_nat i) x
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ is_array (<[i := x]> xs) a }}.
  Proof.
    iIntros (Hi) "Ha".
    iApply (wp_bind [LetCtx None (call_get a (Z.of_nat i))]).
    iApply (wp_wand with "[Ha]").
    { iApply (set_spec xs a i y x Hi with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (get_spec with "Ha").
    apply list_lookup_insert. by eapply lookup_lt_Some.
  Qed.

  Lemma set_then_get_other xs (a : val_cjr) (i j : nat) y z x :
    i ≠ j → xs !! i = Some y → xs !! j = Some z →
    is_array xs a -∗
    WP set_then_get a (Z.of_nat i) (Z.of_nat j) x
      {{ v, ⌜ v = LitV (LitInt z) ⌝ ∗ is_array (<[i := x]> xs) a }}.
  Proof.
    iIntros (Hij Hi Hj) "Ha".
    iApply (wp_bind [LetCtx None (call_get a (Z.of_nat j))]).
    iApply (wp_wand with "[Ha]").
    { iApply (set_spec xs a i y x Hi with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (get_spec with "Ha").
    by rewrite list_lookup_insert_ne.
  Qed.

  Lemma set_then_length_spec xs (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_array xs a -∗
    WP set_then_length a (Z.of_nat i) x
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs))) ⌝ ∗
             is_array (<[i := x]> xs) a }}.
  Proof.
    iIntros (Hi) "Ha".
    iApply (wp_bind [LetCtx None (call_length a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (set_spec xs a i y x Hi with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (length_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    assert (length (<[i := x]> xs) = length xs) as Heqlen
      by (apply length_insert; eapply lookup_lt_Some; exact Hi).
    rewrite Heqlen in Hv.
    iSplit; [|done]. by rewrite Hv.
  Qed.

  Lemma make_then_get_spec (n i : nat) :
    (0 < n)%nat → (i < n)%nat →
    ⊢ WP make_then_get n i
      {{ v, ∃ a, ⌜ v = LitV (LitInt 0) ⌝ ∗ is_array (replicate n 0%Z) a }}.
  Proof.
    iIntros (Hn Hi).
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "s")
        (Struct [] [Var "a"; Val (LitV (LitInt (Z.of_nat i)))])
        (App (Rec None (Some "args") get_body) (Var "s")))]).
    iApply wp_wand.
    { iApply make_spec. exact Hn. }
    iIntros (a) "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "s")
      (App (Rec None (Some "args") get_body) (Var "s"))]).
    iApply wp_struct_step. simpl.
    iApply wp_struct_step. simpl.
    iApply wp_struct_done.
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Hlen Hptr Hblk Hcells]").
    { iApply (get_spec (replicate n 0%Z) (LitV (LitObj o)) i 0%Z with "[Hlen Hptr Hblk Hcells]").
      - apply lookup_replicate. split; [done|exact Hi].
      - iExists o, base. iSplit; [done|]. iFrame. }
    iIntros (v) "[%Hv Ha]".
    iExists (LitV (LitObj o)). iSplit; [done|]. iFrame.
  Qed.

  Lemma make_then_length_spec (n : nat) :
    (0 < n)%nat →
    ⊢ WP make_then_length n
      {{ v, ∃ a, ⌜ v = LitV (LitInt (Z.of_nat n)) ⌝ ∗
                  is_array (replicate n 0%Z) a }}.
  Proof.
    iIntros (Hn).
    iApply (wp_bind [LetCtx (Some "a") (length_at (Var "a"))]).
    iApply wp_wand.
    { iApply make_spec. exact Hn. }
    iIntros (a) "Ha".
    iDestruct "Ha" as (o base) "(%Ha & Hlen & Hptr & Hblk & Hcells)".
    rewrite Ha.
    iApply wp_let. simpl.
    iApply (wp_wand with "[Hlen Hptr Hblk Hcells]").
    { iApply (length_spec with "[Hlen Hptr Hblk Hcells]").
      iExists o, base. iSplit; [done|]. iFrame. }
    iIntros (v) "[%Hv Ha]".
    iExists (LitV (LitObj o)).
    rewrite length_replicate in Hv. iSplit; [done|]. iFrame.
  Qed.
End array.
