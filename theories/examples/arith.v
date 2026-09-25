(** Sum [1] with a [while] over two [var] locals. No heap. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws adequacy.
From iris.prelude Require Import options.
Open Scope expr_scope.

Definition sum_one : expr :=
  VarBind "n" (Val (LitV (LitInt 1)))
    (VarBind "s" (Val (LitV (LitInt 0)))
      (Seq
        (While
          (BinOp LeOp (Val (LitV (LitInt 1))) (Var "n"))
          (Seq
            (Assign "s" (BinOp PlusOp (Var "s") (Val (LitV (LitInt 1)))))
            (Assign "n" (BinOp MinusOp (Var "n") (Val (LitV (LitInt 1)))))))
        (Var "s"))).

Lemma sum_one_wp `{!cjrGS Σ} `{!invGS_gen HasLc Σ} :
  ⊢ WP sum_one {{ v, ⌜ v = LitV (LitInt 1) ⌝ }}.
Proof.
  iApply wp_var_bind. iIntros (ln) "Hn".
  iApply wp_var_bind. iIntros (ls) "Hs".
  simpl.
  set (loadn := StackLoad (Val (LitV (LitStack ln)))).
  set (loads := StackLoad (Val (LitV (LitStack ls)))).
  set (cond := Val (LitV (LitInt 1)) ≤ loadn).
  set (steps := StackAssign (Val (LitV (LitStack ls))) (loads + Val (LitV (LitInt 1)))).
  set (stepn := StackAssign (Val (LitV (LitStack ln))) (loadn - Val (LitV (LitInt 1)))).
  set (body := Seq steps stepn).
  iApply (wp_bind [SeqCtx loads]).
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt 1))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_true.
  iApply (wp_bind [SeqCtx (While cond body)]).
  iApply (wp_bind [SeqCtx stepn]).
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack ls))]).
  iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hs").
  iIntros "!> _ Hs".
  iApply wp_seq.
  iApply (wp_bind [StackAssignRCtx (LitV (LitStack ln))]).
  iApply (wp_bind [BinOpLCtx MinusOp (Val (LitV (LitInt 1)))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply (wp_stack_assign with "Hn").
  iIntros "!> _ Hn".
  iApply wp_seq.
  iApply wp_while.
  iApply (wp_bind [IfCtx (Seq body (While cond body)) (Val (LitV LitUnit))]).
  iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt 1))]).
  iApply (wp_stack_load (StackId ln) with "Hn").
  iIntros "!> _ Hn".
  iApply wp_binop; [by vm_compute|].
  iIntros "!> _".
  iApply wp_if_false.
  iApply wp_value'.
  iApply wp_seq.
  iApply (wp_stack_load (StackId ls) with "Hs").
  iIntros "!> _ Hs".
  iExists (LitV (LitInt 1)). iFrame "Hs".
  iExists (LitV (LitInt 0)). iFrame "Hn".
  done.
Qed.

Lemma sum_one_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck sum_one state_init (λ v _, v = LitV (LitInt 1)).
Proof. eapply (cjr_adequacy Σ). intros ??. eapply sum_one_wp. Qed.
