(** Block-fold bridge and the actual SHA-1 loop's 64-word stride. *)
From Coq Require Import ZArith List Lia String.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Lemma hash_blocks_zero msg st : model.hash_blocks 0 msg st = st.
Proof. reflexivity. Qed.
Lemma hash_blocks_left fuel msg st :
 model.hash_blocks (S fuel) msg st =
 model.hash_blocks fuel (drop 64 msg) (model.compress st (take 64 msg)).
Proof. reflexivity. Qed.
Lemma hash_blocks_right fuel msg st :
 model.hash_blocks (S fuel) msg st =
 model.compress (model.hash_blocks fuel msg st) (take 64 (drop (64*fuel) msg)).
Proof.
 revert msg st. induction fuel as [|fuel IH]; intros msg st.
 - rewrite hash_blocks_left hash_blocks_zero. reflexivity.
 - rewrite hash_blocks_left IH hash_blocks_left.
   rewrite drop_drop. replace (64 + 64 * fuel)%nat with (64 * S fuel)%nat by lia.
   reflexivity.
Qed.
Definition stride_test l stop :=
 BinOp LeOp (StackLoad (Val (LitV (LitStack l))))
   (BinOp MinusOp (int stop) (int 1)).
Definition stride_increment l step := StackAssign (Val (LitV (LitStack l)))
 (BinOp PlusOp (StackLoad (Val (LitV (LitStack l)))) (int step)).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem stride_while_wp l step total body (I : Z -> iProp Σ) start :
 0 < step -> 0 <= start <= total -> (total-start) mod step = 0 ->
 (forall i, 0 <= i < total ->
   StackId l ↦ₛ LitV (LitInt i) -∗ I i -∗
   WP body {{u, StackId l ↦ₛ LitV (LitInt i) ∗ I (i+step)}}) ->
 StackId l ↦ₛ LitV (LitInt start) -∗ I start -∗
 WP While (stride_test l total) (Seq body (stride_increment l step))
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt total) ∗ I total}}.
Proof.
 intros Hstep Hrange Halign Hbody. iIntros "Hl HI".
 iLöb as "IH" forall (start Hrange Halign).
 iApply wp_while.
 iApply (wp_bind [IfCtx
   (Seq (Seq body (stride_increment l step))
     (While (stride_test l total) (Seq body (stride_increment l step)))) unit_e]).
 unfold stride_test. iApply (wp_bind [BinOpLCtx LeOp
   (BinOp MinusOp (int total) (int 1))]).
 iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
 iApply (wp_bind [BinOpRCtx LeOp (LitV (LitInt start))]).
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 destruct (decide (start <= total-1)) as [Hlt|Hend].
 - rewrite bool_decide_true; last done. iApply wp_if_true.
   iApply (wp_bind [SeqCtx (While
     (BinOp LeOp (StackLoad (Val (LitV (LitStack l))))
       (BinOp MinusOp (int total) (int 1)))
     (Seq body (stride_increment l step)))]).
   iApply (wp_bind [SeqCtx (stride_increment l step)]).
   iApply (wp_wand with "[Hl HI]").
   { iApply (Hbody start with "Hl HI"); lia. }
   iIntros (u) "[Hl HI]". iApply wp_seq.
   unfold stride_increment. iApply (wp_bind [StackAssignRCtx (LitV (LitStack l))]).
   iApply (wp_bind [BinOpLCtx PlusOp (int step)]).
   iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
   iApply wp_binop; [reflexivity|]. iIntros "!> _".
   iApply (wp_stack_assign with "Hl"). iIntros "!> _ Hl".
   iApply wp_seq.
   assert (Hgap : step <= total-start).
   { pose proof (Z.div_mod (total-start) step ltac:(lia)) as Heq.
     rewrite Halign in Heq.
     assert (0 < (total-start)/step) by nia. nia. }
   iApply ("IH" $! (start+step) with "[] [] Hl HI").
   + iPureIntro. lia.
   + iPureIntro. apply Z.mod_divide; first lia.
     apply Z.mod_divide in Halign; last lia. destruct Halign as [k Hk].
     exists (k-1). nia.
 - rewrite bool_decide_false; last done. iApply wp_if_false.
   assert (start=total) by lia. subst start. iApply wp_value'. iFrame. done.
Qed.
End proofs.
