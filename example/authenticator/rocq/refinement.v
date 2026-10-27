(** Iris contracts for scalar operations. Heap-loop refinements are tracked
    separately in README: a proved arithmetic kernel is not a whole-core proof. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program base32.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Ltac auth_head := first [
 match goal with
 | |- envs_entails _ (WP BinOp DivOp (Val (LitV (LitInt _))) (Val (LitV (LitInt ?d))) {{_}}) =>
   iApply wp_div; [try (apply Z.pow_nonzero); lia|iIntros "!> _"]
 | |- envs_entails _ (WP BinOp RemOp (Val (LitV (LitInt _))) (Val (LitV (LitInt ?d))) {{_}}) =>
   iApply wp_rem; [lia|iIntros "!> _"]
 | |- envs_entails _ (WP If (Val (LitV (LitBool true))) _ _ {{_}}) => iApply wp_if_true
 | |- envs_entails _ (WP If (Val (LitV (LitBool false))) _ _ {{_}}) => iApply wp_if_false
 end | hm_head ].
Ltac auth_pure := iStartProof; repeat (
 simpl; cbn [fill fill_item];
 try (rewrite bool_decide_true; [|lia]);
 try (rewrite bool_decide_false; [|lia]);
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => auth_head) end);
 simpl; cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem rol_wp x n : 0 <= n <= 30 ->
 ⊢ WP rol (int x) n {{v, ⌜v = LitV (LitInt (rol32 x n))⌝}}.
Proof.
 intros Hn. unfold rol, mask, add, mul, div, band, int, op, rol32, mask32.
 auth_pure. done.
Qed.
Theorem remaining_wp timestamp period : 0 <= timestamp -> 1 <= period <= 2147483647 ->
 ⊢ WP call remaining_body [int timestamp;int period]
 {{v, ⌜v = LitV (LitInt (remaining timestamp period))⌝}}.
Proof.
 intros Ht Hp. unfold call, remaining_body, args, vars, lets, range,
  both, le, sub, rem, v, int, op, remaining.
 auth_pure. done.
Qed.
Theorem round_wp t w a b c d e :
 ⊢ WP call round_body (map int [Z.of_nat t;w;a;b;c;d;e])
 {{v, ⌜v = StructV (map (fun z => LitV (LitInt z)) (sha_round [a;b;c;d;e] (t,w)))⌝}}.
Proof.
 unfold call, round_body, args, lets, sha_choose, sha_constant,
   rol, mask, add, mul, div, band, xor, le, v, int, op,
   sha_round, sha_f, sha_k, sha_ch, sha_parity, sha_maj, rol32, mask32.
 destruct (Nat.ltb t 20) eqn:H20.
 - apply Nat.ltb_lt in H20. auth_pure. done.
 - apply Nat.ltb_ge in H20. destruct (Nat.ltb t 40) eqn:H40.
   + apply Nat.ltb_lt in H40. auth_pure. done.
   + apply Nat.ltb_ge in H40. destruct (Nat.ltb t 60) eqn:H60.
     * apply Nat.ltb_lt in H60. auth_pure. done.
     * apply Nat.ltb_ge in H60. auth_pure. done.
Qed.
Definition counter_test l n := BinOp LeOp (StackLoad (Val (LitV (LitStack l)))) (int (n-1)).
Definition counter_increment l := StackAssign (Val (LitV (LitStack l)))
 (BinOp PlusOp (StackLoad (Val (LitV (LitStack l)))) (int 1)).
Theorem counted_while_wp l n body (I : Z -> iProp Σ) start :
 (forall i, 0 <= i < n ->
   ⊢ StackId l ↦ₛ LitV (LitInt i) -∗ I i -∗
     WP body {{u, StackId l ↦ₛ LitV (LitInt i) ∗ I (i+1)}}) ->
 0 <= start <= n ->
 StackId l ↦ₛ LitV (LitInt start) -∗ I start -∗
 WP While (counter_test l n) (Seq body (counter_increment l))
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt n) ∗ I n}}.
Proof.
 intros Hstep Hstart. iIntros "Hl HI".
 iLöb as "IH" forall (start Hstart).
 iApply wp_while.
 iApply (wp_bind [IfCtx
  (Seq (Seq body (counter_increment l)) (While (counter_test l n) (Seq body (counter_increment l)))) unit_e]).
 unfold counter_test. iApply (wp_bind [BinOpLCtx LeOp (int (n-1))]).
 iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
 iApply wp_binop; [reflexivity|]. iIntros "!> _".
 destruct (decide (start <= n-1)) as [Hlt|Hend].
 - rewrite bool_decide_true; last done. iApply wp_if_true.
   iApply (wp_bind [SeqCtx (While (counter_test l n) (Seq body (counter_increment l)))]).
   iApply (wp_bind [SeqCtx (counter_increment l)]).
   iApply (wp_wand with "[Hl HI]").
   { iApply (Hstep start with "Hl HI"). lia. }
   iIntros (u) "[Hl HI]". iApply wp_seq.
   unfold counter_increment. iApply (wp_bind [StackAssignRCtx (LitV (LitStack l))]).
   iApply (wp_bind [BinOpLCtx PlusOp (int 1)]).
   iApply (wp_stack_load with "Hl"). iIntros "!> _ Hl".
   iApply wp_binop; [reflexivity|]. iIntros "!> _".
   iApply (wp_stack_assign with "Hl"). iIntros "!> _ Hl".
   iApply wp_seq. iApply ("IH" $! (start+1) with "[] Hl HI"). iPureIntro. lia.
 - rewrite bool_decide_false; last done. iApply wp_if_false.
   assert (start=n) by lia. subst start. iApply wp_value'. iFrame. done.
Qed.
Theorem base32_value_wp ch :
 ⊢ WP call base32_value_body [int ch]
 {{v, ⌜v = LitV (LitInt (match digit_value ch with Some d => d | None => -1 end))⌝}}.
Proof.
 unfold call, base32_value_body, args, range, both, le, sub, int, v, op, digit_value.
 destruct (Z.leb 65 ch) eqn:H1; [apply Z.leb_le in H1|apply Z.leb_gt in H1].
 all: (destruct (Z.leb ch 90) eqn:H2; [apply Z.leb_le in H2|apply Z.leb_gt in H2]).
 all: (destruct (Z.leb 97 ch) eqn:H3; [apply Z.leb_le in H3|apply Z.leb_gt in H3]).
 all: (destruct (Z.leb ch 122) eqn:H4; [apply Z.leb_le in H4|apply Z.leb_gt in H4]).
 all: (destruct (Z.leb 50 ch) eqn:H5; [apply Z.leb_le in H5|apply Z.leb_gt in H5]).
 all: (destruct (Z.leb ch 55) eqn:H6; [apply Z.leb_le in H6|apply Z.leb_gt in H6]).
 all: try lia; auth_pure; done.
Qed.
Theorem base32_reject_size p n q : n < 2 \/ 208 < n ->
 ⊢ WP call base32_body [Val (LitV (LitPtr p));int n;Val (LitV (LitPtr q))]
 {{v, ⌜v = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hn. unfold call, base32_body, args, range, both, le, int, v, op.
 destruct (decide (2 <= n)) as [Hlo|Hlo]; auth_pure; done.
Qed.
Theorem sha1_reject_size p n q : n < 0 \/ 2048 < n ->
 ⊢ WP call sha_body [Val (LitV (LitPtr p));int n;Val (LitV (LitPtr q))]
 {{v, ⌜v = LitV (LitBool false)⌝}}.
Proof.
 intros Hn. unfold call, sha_body, args, range, both, le, int, v, op.
 destruct (decide (0 <= n)) as [Hlo|Hlo]; auth_pure; done.
Qed.
Theorem remaining_reject timestamp period : timestamp < 0 \/ period < 1 \/ 2147483647 < period ->
 ⊢ WP call remaining_body [int timestamp;int period]
 {{v, ⌜v = LitV (LitInt (-1))⌝}}.
Proof.
 intros Hn. unfold call, remaining_body, args, range, both, le, int, v, op.
 destruct (decide (1 <= period)) as [Hlo|Hlo];
 destruct (decide (period <= 2147483647)) as [Hhi|Hhi]; try lia; auth_pure; done.
Qed.
Theorem buffer_get_wp p xs i x : xs !! i = Some x ->
 array.array_cells p xs -∗
 WP get (Val (LitV (LitPtr p))) (int (Z.of_nat i))
 {{v, ⌜v = LitV (LitInt x)⌝ ∗ array.array_cells p xs}}.
Proof.
 intros Hi. iIntros "Hcells". unfold get, ptr, int.
 iApply (wp_bind [LoadCtx]). iApply wp_offset. iIntros "!> _".
 iEval (unfold array.array_cells) in "Hcells".
 iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hx Hclose]"; [exact Hi|].
 iApply (wp_load with "Hx"). iIntros "!> _ Hx".
 iDestruct ("Hclose" with "Hx") as "Hcells".
 iSplit; [done|]. iExact "Hcells".
Qed.
Theorem buffer_put_wp p xs i old x : xs !! i = Some old ->
 array.array_cells p xs -∗
 WP put (Val (LitV (LitPtr p))) (int (Z.of_nat i)) (int x)
 {{v, ⌜v = LitV LitUnit⌝ ∗ array.array_cells p (<[i := x]> xs)}}.
Proof.
 intros Hi. iIntros "Hcells". unfold put, ptr, int.
 iApply (wp_bind [StoreLCtx (Val (LitV (LitInt x)))]).
 iApply wp_offset. iIntros "!> _".
 iEval (unfold array.array_cells) in "Hcells".
 iDestruct (big_sepL_insert_acc with "Hcells") as "[Hx Hclose]"; [exact Hi|].
 iApply (wp_store with "Hx"). iIntros "!> _ Hx".
 iDestruct ("Hclose" $! x with "Hx") as "Hcells".
 iSplit; [done|]. iExact "Hcells".
Qed.
End proofs.
