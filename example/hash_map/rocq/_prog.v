
Open Scope expr_scope.

Section hash_map.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition sld (z : Z) : expr :=
    StackLoad (Val (LitV (LitStack z))).
  Definition sas (z : Z) (e : expr) : expr :=
    StackAssign (Val (LitV (LitStack z))) e.

  Definition nonneg_while (lh cap : Z) : expr :=
    While (sld lh ≤ Val (LitV (LitInt (-1))))
      (sas lh (sld lh + Val (LitV (LitInt cap)))).

  Definition below_while (lh cap : Z) : expr :=
    While (Val (LitV (LitInt cap)) ≤ sld lh)
      (sas lh (sld lh - Val (LitV (LitInt cap)))).

  Lemma wp_nonneg (lh : Z) (h cap : Z) :
    (0 < cap)%Z →
    StackId lh ↦ₛ LitV (LitInt h) -∗
    WP nonneg_while lh cap
      {{ _, ∃ h', ⌜ h' = bring_nonneg (Z.to_nat (Z.max 0 (- h))) h cap ⌝ ∗
                   StackId lh ↦ₛ LitV (LitInt h') }}.
  Proof.
    intros Hcap.
    remember (Z.to_nat (Z.max 0 (- h))) as fuel eqn:Hfuel.
    revert h Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros h Hfuel.
    iIntros "Hh".
    unfold nonneg_while.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq (sas lh (sld lh + Val (LitV (LitInt cap)))) (nonneg_while lh cap))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt (-1))))]).
    iApply (wp_stack_load (StackId lh) with "Hh").
    iIntros "!> _ Hh".
    iApply wp_binop.
    { reflexivity. }
    iIntros "!> _".
    destruct fuel as [|fuel].
    - assert (Z.to_nat (Z.max 0 (- h)) = 0)%nat as Hz by (symmetry; exact Hfuel).
      apply z_to_nat_0 in Hz.
      assert (bool_decide (h ≤ -1)%Z = false) as ->.
      { apply bool_decide_eq_false. lia. }
      iApply wp_if_false.
      iApply wp_value'.
      iExists h. iFrame "Hh". iPureIntro.
      assert (Z.max 0 (- h) = 0)%Z as -> by (rewrite Z.max_l; lia).
      reflexivity.
    - assert (h < 0)%Z as Hn.
      { assert (0 < Z.to_nat (Z.max 0 (- h)))%nat as Hpos by (rewrite <- Hfuel; lia).
        destruct (Z_lt_le_dec h 0) as [Hlt|Hge]; [exact Hlt|].
        assert (Z.max 0 (- h) = 0)%Z as Heq by (rewrite Z.max_l; lia).
        rewrite Heq in Hpos. simpl in Hpos. lia. }
      assert (bool_decide (h ≤ -1)%Z = true) as ->.
      { apply bool_decide_eq_true. lia. }
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx (nonneg_while lh cap)]).
      iApply (wp_bind [StackAssignRCtx (LitV (LitStack lh))]).
      iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt cap)))]).
      iApply (wp_stack_load (StackId lh) with "Hh").
      iIntros "!> _ Hh".
      iApply wp_binop.
      { reflexivity. }
      iIntros "!> _".
      iApply (wp_stack_assign with "Hh").
      iIntros "!> _ Hh".
      iApply wp_seq.
      fold nonneg_while.
      set (y := Z.to_nat (Z.max 0 (- (h + cap)))).
      assert (y < S fuel)%nat as Hlt.
      { unfold y. rewrite <- Hfuel.
        assert (Z.max 0 (- h) = - h)%Z as -> by (rewrite Z.max_r; lia).
        destruct (Z_lt_le_dec (h + cap) 0) as [Hstill|Hdone].
        - assert (Z.max 0 (- (h + cap)) = (- h - cap))%Z as -> by (rewrite Z.max_r; lia).
          assert (Z.to_nat (- h) = (Z.to_nat (- h - cap) + Z.to_nat cap)%nat) as Hsum.
          { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
          assert (1 ≤ Z.to_nat cap)%nat as Hone.
          { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
            apply Z2Nat.inj_le; lia. }
          lia.
        - assert (Z.max 0 (- (h + cap)) = 0)%Z as -> by (rewrite Z.max_l; lia).
          lia. }
      iApply (wp_wand with "[Hh]").
      { iApply (IH y Hlt (h + cap)%Z eq_refl with "Hh"). }
      iIntros (_) "(%h' & %Heq & Hh)".
      iExists h'. iFrame "Hh". iPureIntro.
      rewrite Heq. apply bring_nonneg_step; done.
  Qed.

  Lemma wp_below (lh : Z) (h cap : Z) :
    (0 < cap)%Z → (0 ≤ h)%Z →
    StackId lh ↦ₛ LitV (LitInt h) -∗
    WP below_while lh cap
      {{ _, ∃ h', ⌜ h' = bring_below (Z.to_nat h) h cap ⌝ ∗
                   StackId lh ↦ₛ LitV (LitInt h') }}.
  Proof.
    intros Hcap Hnn0.
    remember (Z.to_nat h) as fuel eqn:Hfuel.
    revert h Hnn0 Hfuel.
    induction fuel as [fuel IH] using lt_wf_ind.
    intros h Hnn Hfuel.
    iIntros "Hh".
    unfold below_while.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq (sas lh (sld lh - Val (LitV (LitInt cap)))) (below_while lh cap))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt cap))]).
    iApply (wp_stack_load (StackId lh) with "Hh").
    iIntros "!> _ Hh".
    iApply wp_binop.
    { reflexivity. }
    iIntros "!> _".
    destruct fuel as [|fuel].
    - assert (Z.to_nat h = 0)%nat as Hz by (symmetry; exact Hfuel).
      apply z_to_nat_0 in Hz.
      assert (bool_decide (cap ≤ h)%Z = false) as ->.
      { apply bool_decide_eq_false. lia. }
      iApply wp_if_false.
      iApply wp_value'.
      iExists h. iFrame "Hh". iPureIntro. reflexivity.
    - assert (cap ≤ h)%Z as Hge.
      { assert (0 < Z.to_nat h)%nat as Hpos by (rewrite <- Hfuel; lia).
        destruct (Z_lt_le_dec h cap) as [Hlt|Hge]; [|exact Hge].
        assert (Z.to_nat h = 0)%nat as Hz.
        { destruct h; simpl in Hlt; lia. }
        lia. }
      assert (bool_decide (cap ≤ h)%Z = true) as ->.
      { apply bool_decide_eq_true. exact Hge. }
      iApply wp_if_true.
      iApply (wp_bind [SeqCtx (below_while lh cap)]).
      iApply (wp_bind [StackAssignRCtx (LitV (LitStack lh))]).
      iApply (wp_bind [BinOpLCtx MinusOp (Val (LitV (LitInt cap)))]).
      iApply (wp_stack_load (StackId lh) with "Hh").
      iIntros "!> _ Hh".
      iApply wp_binop.
      { reflexivity. }
      iIntros "!> _".
      iApply (wp_stack_assign with "Hh").
      iIntros "!> _ Hh".
      iApply wp_seq.
      fold below_while.
      set (y := Z.to_nat (h - cap)).
      assert (0 ≤ h - cap)%Z as Hnn' by lia.
      assert (y < S fuel)%nat as Hlt.
      { unfold y. rewrite <- Hfuel.
        assert (Z.to_nat h = (Z.to_nat (h - cap) + Z.to_nat cap)%nat) as Hsum.
        { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
        assert (1 ≤ Z.to_nat cap)%nat as Hone.
        { replace 1%nat with (Z.to_nat 1%Z) by reflexivity.
          apply Z2Nat.inj_le; lia. }
        lia. }
      iApply (wp_wand with "[Hh]").
      { iApply (IH y Hlt (h - cap)%Z Hnn' eq_refl with "Hh"). }
      iIntros (_) "(%h' & %Heq & Hh)".
      iExists h'. iFrame "Hh". iPureIntro.
      rewrite Heq. apply bring_below_step; done.
  Qed.

  Definition residue_body : expr :=
    Let (Some "k") (StructLoad (Var "args") 0)
      (Let (Some "cap") (StructLoad (Var "args") 1)
        (VarBind "h" (Var "k")
          (Seq (While (Var "h" ≤ Val (LitV (LitInt (-1))))
                 (Assign "h" (Var "h" + Var "cap")))
            (Seq (While (Var "cap" ≤ Var "h")
                   (Assign "h" (Var "h" - Var "cap")))
              (Var "h"))))).

  Definition call_residue (k cap : Z) : expr :=
    App (Rec None (Some "args") residue_body)
      (Val (StructV [LitV (LitInt k); LitV (LitInt cap)])).

  Lemma residue_wp (k cap : Z) :
    (0 < cap)%Z →
    ⊢ WP call_residue k cap {{ v, ⌜ v = LitV (LitInt (residue k cap)) ⌝ }}.
  Proof.
    intros Hcap.
    set (arg := StructV [LitV (LitInt k); LitV (LitInt cap)]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "k")
      (Let (Some "cap") (StructLoad (Val arg) 1)
        (VarBind "h" (Var "k")
          (Seq (While (Var "h" ≤ Val (LitV (LitInt (-1))))
                 (Assign "h" (Var "h" + Var "cap")))
            (Seq (While (Var "cap" ≤ Var "h")
                   (Assign "h" (Var "h" - Var "cap")))
              (Var "h")))))]).
    iApply (wp_struct_load _ 0 (LitV (LitInt k))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "cap")
      (VarBind "h" (Val (LitV (LitInt k)))
        (Seq (While (Var "h" ≤ Val (LitV (LitInt (-1))))
               (Assign "h" (Var "h" + Val (LitV (LitInt cap)))))
          (Seq (While (Val (LitV (LitInt cap)) ≤ Var "h")
                 (Assign "h" (Var "h" - Val (LitV (LitInt cap)))))
            (Var "h"))))]).
    iApply (wp_struct_load _ 1 (LitV (LitInt cap))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply wp_var_bind. iIntros (lh) "Hh".
    simpl.
    iApply (wp_bind [SeqCtx
      (Seq (below_while lh cap) (sld lh))]).
    iApply (wp_wand with "[Hh]").
    { iApply (wp_nonneg with "Hh"). exact Hcap. }
    iIntros (_) "(%h1 & %Hh1 & Hh)".
    iApply wp_seq.
    iApply (wp_bind [SeqCtx (sld lh)]).
    iApply (wp_wand with "[Hh]").
    { iApply (wp_below with "Hh").
      - exact Hcap.
      - rewrite Hh1. apply bring_nonneg_spec; [exact Hcap|lia]. }
    iIntros (_) "(%h2 & %Hh2 & Hh)".
    iApply wp_seq.
    iApply (wp_stack_load (StackId lh) with "Hh").
    iIntros "!> _ Hh".
    iExists (LitV (LitInt h2)). iFrame "Hh".
    iPureIntro. f_equal. f_equal.
    unfold residue. rewrite Hh1 in Hh2. rewrite Hh2. reflexivity.
  Qed.

End hash_map.
