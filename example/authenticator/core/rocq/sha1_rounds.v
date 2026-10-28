(** Concrete SHA-1 round iteration and its five owned local state words. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory sha1_memory round_kernel round_model.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition round_loop w a b c d e :=
 let read l := StackLoad (Val (LitV (LitStack l))) in
 loop "t" (int 0) (int 80)
   (lets [("next", call round_body
     [v "t"; get (pv w) (v "t"); read a; read b; read c; read d; read e])]
    (seqs [StackAssign (Val (LitV (LitStack a))) (StructLoad (v "next") 0);
           StackAssign (Val (LitV (LitStack b))) (StructLoad (v "next") 1);
           StackAssign (Val (LitV (LitStack c))) (StructLoad (v "next") 2);
           StackAssign (Val (LitV (LitStack d))) (StructLoad (v "next") 3)]
          (StackAssign (Val (LitV (LitStack e))) (StructLoad (v "next") 4)))).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition state_at a b c d e st : iProp Σ :=
 ∃ av bv cv dv ev, ⌜st = [av;bv;cv;dv;ev]⌝ ∗
 StackId a ↦ₛ LitV (LitInt av) ∗ StackId b ↦ₛ LitV (LitInt bv) ∗
 StackId c ↦ₛ LitV (LitInt cv) ∗ StackId d ↦ₛ LitV (LitInt dv) ∗ StackId e ↦ₛ LitV (LitInt ev).
Opaque round_body rounds_state.
#[local] Hint Rewrite round_body_t_closed : round_subst.
Ltac rounds_args :=
 iStartProof; repeat (simpl; autorewrite with round_subst; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackLoad _ {{_}}) => first [
    iApply (wp_stack_load with "Hl"); iIntros "!> _ Hl"
   |iApply (wp_stack_load with "Ha"); iIntros "!> _ Ha"
   |iApply (wp_stack_load with "Hb"); iIntros "!> _ Hb"
   |iApply (wp_stack_load with "Hc"); iIntros "!> _ Hc"
   |iApply (wp_stack_load with "Hd"); iIntros "!> _ Hd"
   |iApply (wp_stack_load with "He"); iIntros "!> _ He"] end
   |hm_args_head]) end); simpl; cbn [fill fill_item].
Ltac rounds_update :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackAssign (Val _) (Val _) {{_}}) => first [
    iApply (wp_stack_assign with "Ha"); iIntros "!> _ Ha"
   |iApply (wp_stack_assign with "Hb"); iIntros "!> _ Hb"
   |iApply (wp_stack_assign with "Hc"); iIntros "!> _ Hc"
   |iApply (wp_stack_assign with "Hd"); iIntros "!> _ Hd"
   |iApply (wp_stack_assign with "He"); iIntros "!> _ He"] end
   |match goal with |- envs_entails _ (WP StackAssign (Val ?l) _ {{_}}) =>
      iApply (wp_bind [StackAssignRCtx l]) end
   |hm_head]) end); simpl; cbn [fill fill_item].
Theorem round_loop_wp w words a b c d e initial : (80 <= length words)%nat ->
 state_at a b c d e initial -∗ array.array_cells w words -∗
 WP round_loop w a b c d e
 {{u, ⌜u = LitV LitUnit⌝ ∗ state_at a b c d e (rounds_state words 80 initial) ∗
   array.array_cells w words}}.
Proof.
 intros Hlen. iIntros "Hstate Hw". unfold round_loop.
 set (I := fun i : Z => (state_at a b c d e (rounds_state words (Z.to_nat i) initial) ∗
   array.array_cells w words)%I).
 iApply (wp_wand with "[Hstate Hw]").
 { iApply (loop_wp "t" 0 80 _ I with "[Hstate Hw]").
   - intros l i Hi. iIntros "Hl [Hstate Hw]".
     iDestruct "Hstate" as (av bv cv dv ev) "[%Hstate [Ha [Hb [Hc [Hd He]]]]]".
     unfold lets, seqs, call, get, ptr, pv, v, int.
     cbn [subst_var subst_var_val]. autorewrite with round_subst.
     rounds_args.
     iApply wp_offset. iIntros "!> _".
     assert (Hlookup : words !! Z.to_nat i = Some (words !!! Z.to_nat i)) by
       (apply list_lookup_lookup_total_lt; lia).
     iDestruct (big_sepL_lookup_acc with "Hw") as "[Hcell Hclose]"; [exact Hlookup|].
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     rewrite Hki. iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hw". rounds_args.
     iApply (wp_wand with "[]").
     { iApply (round_app_z_wp i (words !!! Z.to_nat i) av bv cv dv ev). lia. }
     iIntros (next) "%Hnext". subst next. rounds_update.
     iFrame "Hl". unfold I. iFrame "Hw".
     replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.
     rewrite rounds_state_step; last lia. rewrite Hstate.
     iExists _,_,_,_,_. iFrame. done.
   - lia.
   - unfold I. rewrite rounds_state_zero. iFrame. }
 iIntros (u) "[%Hu HI]". iFrame. done.
Qed.
End proofs.
