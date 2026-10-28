(** Composition of the concrete SHA-1 round loop and feed-forward state update. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import model program refinement memory sha1_memory round_model sha1_rounds.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition compression_tail := match program.sha_compress with Seq _ (Seq _ rest) => rest | _ => unit_e end.
Fixpoint strip_vars n e := match n,e with
 | S n, VarBind _ _ rest => strip_vars n rest | _,_ => e end.
Definition read_local l := StackLoad (Val (LitV (LitStack l))).
Definition bind_hash h0 h1 h2 h3 h4 e :=
 subst_var "h0" h0 (subst_var "h1" h1 (subst_var "h2" h2
   (subst_var "h3" h3 (subst_var "h4" h4 e)))).
Definition feed_forward h0 h1 h2 h3 h4 a b c d e := seqs
 [StackAssign (Val (LitV (LitStack h0))) (mask (add (read_local h0) (read_local a)));
  StackAssign (Val (LitV (LitStack h1))) (mask (add (read_local h1) (read_local b)));
  StackAssign (Val (LitV (LitStack h2))) (mask (add (read_local h2) (read_local c)));
  StackAssign (Val (LitV (LitStack h3))) (mask (add (read_local h3) (read_local d)))]
  (StackAssign (Val (LitV (LitStack h4))) (mask (add (read_local h4) (read_local e)))).
Lemma compression_round_source w a b c d e :
 subst "w" (LitV (LitPtr w))
 (subst_var "a" a (subst_var "b" b (subst_var "c" c (subst_var "d" d (subst_var "e" e
   (match strip_vars 5 compression_tail with Seq rounds _ => rounds | _ => unit_e end)))))) =
 round_loop w a b c d e.
Proof. reflexivity. Qed.
Lemma compression_feed_source h0 h1 h2 h3 h4 a b c d e :
 bind_hash h0 h1 h2 h3 h4
 (subst_var "a" a (subst_var "b" b (subst_var "c" c (subst_var "d" d (subst_var "e" e
   (match strip_vars 5 compression_tail with Seq _ rest => rest | _ => unit_e end)))))) =
 feed_forward h0 h1 h2 h3 h4 a b c d e.
Proof. reflexivity. Qed.
Definition bind_work a b c d e ex :=
 subst_var "a" a (subst_var "b" b (subst_var "c" c (subst_var "d" d (subst_var "e" e ex)))) .
Definition compression_tail_bound w h0 h1 h2 h3 h4 :=
 subst "w" (LitV (LitPtr w)) (bind_hash h0 h1 h2 h3 h4 compression_tail).
Lemma compression_work_source w h0 h1 h2 h3 h4 a b c d e :
 bind_work a b c d e
 (subst "w" (LitV (LitPtr w)) (bind_hash h0 h1 h2 h3 h4 (strip_vars 5 compression_tail))) =
 Seq (round_loop w a b c d e) (feed_forward h0 h1 h2 h3 h4 a b c d e).
Proof. reflexivity. Qed.
Definition fed_state st work := map (fun xy => model.mask32 (fst xy+snd xy)) (combine st work).
Lemma round_closed_h0 l : subst_var "h0" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_h1 l : subst_var "h1" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_h2 l : subst_var "h2" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_h3 l : subst_var "h3" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_h4 l : subst_var "h4" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_a l : subst_var "a" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_b l : subst_var "b" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_c l : subst_var "c" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_d l : subst_var "d" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_e l : subst_var "e" l round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_w p : subst "w" (LitV (LitPtr p)) round_body = round_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite round_closed_h0 round_closed_h1 round_closed_h2 round_closed_h3 round_closed_h4 round_closed_a round_closed_b round_closed_c round_closed_d round_closed_e round_closed_w : compress_subst.
Lemma round_closed_pad p : subst "pad" (LitV (LitPtr p)) round_body = round_body.
Proof. reflexivity. Qed.
Lemma round_closed_block l : subst_var "block" l round_body = round_body.
Proof. reflexivity. Qed.
#[local] Hint Rewrite round_closed_pad round_closed_block : compress_subst.
Opaque round_body model.schedule_more.
Definition compression_bound p w block h0 h1 h2 h3 h4 :=
 subst "pad" (LitV (LitPtr p)) (subst "w" (LitV (LitPtr w))
   (subst_var "block" block (bind_hash h0 h1 h2 h3 h4 program.sha_compress))).
Lemma compression_source p w block h0 h1 h2 h3 h4 :
 compression_bound p w block h0 h1 h2 h3 h4 =
 seqs [load_schedule_operand p w (read_local block); expand_schedule w]
   (compression_tail_bound w h0 h1 h2 h3 h4).
Proof.
 unfold compression_bound, compression_tail_bound, compression_tail, bind_hash.
 simpl. autorewrite with compress_subst. reflexivity.
Qed.
Lemma compression_rounds_result st block tail :
 fed_state st (rounds_state (model.schedule_more 64 (model.message_words block) ++ tail) 80 st) =
 model.compress st block.
Proof.
 rewrite compress_rounds. unfold fed_state, rounds_state.
 rewrite take_app_le; last (rewrite schedule_length;lia). done.
Qed.
Opaque round_body.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Ltac compression_admin :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?ex {{_}}) =>
 hm_focus ex ltac:(fun _ => first [
   match goal with |- envs_entails _ (WP StackLoad _ {{_}}) => first [
    iApply (wp_stack_load with "H0"); iIntros "!> _ H0"
   |iApply (wp_stack_load with "H1"); iIntros "!> _ H1"
   |iApply (wp_stack_load with "H2"); iIntros "!> _ H2"
   |iApply (wp_stack_load with "H3"); iIntros "!> _ H3"
   |iApply (wp_stack_load with "H4"); iIntros "!> _ H4"
   |iApply (wp_stack_load with "Ha"); iIntros "!> _ Ha"
   |iApply (wp_stack_load with "Hb"); iIntros "!> _ Hb"
   |iApply (wp_stack_load with "Hc"); iIntros "!> _ Hc"
   |iApply (wp_stack_load with "Hd"); iIntros "!> _ Hd"
   |iApply (wp_stack_load with "He"); iIntros "!> _ He"] end
   |match goal with |- envs_entails _ (WP StackAssign (Val _) (Val _) {{_}}) => first [
    iApply (wp_stack_assign with "H0"); iIntros "!> _ H0"
   |iApply (wp_stack_assign with "H1"); iIntros "!> _ H1"
   |iApply (wp_stack_assign with "H2"); iIntros "!> _ H2"
   |iApply (wp_stack_assign with "H3"); iIntros "!> _ H3"
   |iApply (wp_stack_assign with "H4"); iIntros "!> _ H4"] end
   |match goal with |- envs_entails _ (WP StackAssign (Val ?lv) _ {{_}}) =>
      iApply (wp_bind [StackAssignRCtx lv]) end
   |hm_head]) end); simpl; cbn [fill fill_item].
Theorem feed_forward_wp h0 h1 h2 h3 h4 a b c d e st work :
 state_at h0 h1 h2 h3 h4 st -∗ state_at a b c d e work -∗
 WP feed_forward h0 h1 h2 h3 h4 a b c d e
 {{u, ⌜u = LitV LitUnit⌝ ∗ state_at h0 h1 h2 h3 h4 (fed_state st work) ∗
   state_at a b c d e work}}.
Proof.
 iIntros "Hhash Hwork".
 iDestruct "Hhash" as (h0v h1v h2v h3v h4v) "[%Hst [H0 [H1 [H2 [H3 H4]]]]]".
 iDestruct "Hwork" as (av bv cv dv ev) "[%Hwork [Ha [Hb [Hc [Hd He]]]]]".
 subst st work. unfold feed_forward, read_local, mask, add, band, int, op, seqs.
 compression_admin. iSplit; first done. iSplitL "H0 H1 H2 H3 H4".
 - iExists _,_,_,_,_. iFrame. done.
 - iExists _,_,_,_,_. iFrame. done.
Qed.
Theorem compression_tail_wp w words h0 h1 h2 h3 h4 st :
 (80 <= length words)%nat ->
 state_at h0 h1 h2 h3 h4 st -∗ array.array_cells w words -∗
 WP compression_tail_bound w h0 h1 h2 h3 h4
 {{u, ⌜u = LitV LitUnit⌝ ∗
   state_at h0 h1 h2 h3 h4 (fed_state st (rounds_state words 80 st)) ∗ array.array_cells w words}}.
Proof.
 intros Hlen. iIntros "Hhash Hw".
 iDestruct "Hhash" as (h0v h1v h2v h3v h4v) "[%Hst [H0 [H1 [H2 [H3 H4]]]]]".
 subst st. unfold compression_tail_bound, bind_hash, compression_tail.
 simpl. autorewrite with compress_subst.
 iApply (wp_bind [VarBindCtx "a" _]).
 iApply (wp_stack_load with "H0"). iIntros "!> _ H0".
 iApply wp_var_bind. iIntros (a) "Ha". simpl; autorewrite with compress_subst.
 iApply (wp_bind [VarBindCtx "b" _]).
 iApply (wp_stack_load with "H1"). iIntros "!> _ H1".
 iApply wp_var_bind. iIntros (b) "Hb". simpl; autorewrite with compress_subst.
 iApply (wp_bind [VarBindCtx "c" _]).
 iApply (wp_stack_load with "H2"). iIntros "!> _ H2".
 iApply wp_var_bind. iIntros (c) "Hc". simpl; autorewrite with compress_subst.
 iApply (wp_bind [VarBindCtx "d" _]).
 iApply (wp_stack_load with "H3"). iIntros "!> _ H3".
 iApply wp_var_bind. iIntros (d) "Hd". simpl; autorewrite with compress_subst.
 iApply (wp_bind [VarBindCtx "e" _]).
 iApply (wp_stack_load with "H4"). iIntros "!> _ H4".
 iApply wp_var_bind. iIntros (e) "He". simpl; autorewrite with compress_subst.
 match goal with |- envs_entails ?Delta (WP _ {{?Phi}}) =>
   change (envs_entails Delta (WP Seq (round_loop w a b c d e)
     (feed_forward h0 h1 h2 h3 h4 a b c d e) {{Phi}})) end.
 iApply (wp_bind [SeqCtx (feed_forward h0 h1 h2 h3 h4 a b c d e)]).
 iApply (wp_wand with "[Ha Hb Hc Hd He Hw]").
 { iApply (round_loop_wp with "[Ha Hb Hc Hd He] Hw"); first exact Hlen.
   iExists _,_,_,_,_. iFrame. done. }
 iIntros (u) "[%Hu [Hwork Hw]]". subst u. iApply wp_seq.
 iApply (wp_wand with "[H0 H1 H2 H3 H4 Hwork]").
 { iApply (feed_forward_wp with "[H0 H1 H2 H3 H4] Hwork").
   iExists _,_,_,_,_. iFrame. done. }
 iIntros (u) "[%Hu [Hhash Hwork]]".
 iDestruct "Hwork" as (av bv cv dv ev) "[%Hwork [Ha [Hb [Hc [Hd He]]]]]".
 iExists (LitV (LitInt ev)). iFrame "He".
 iExists (LitV (LitInt dv)). iFrame "Hd".
 iExists (LitV (LitInt cv)). iFrame "Hc".
 iExists (LitV (LitInt bv)). iFrame "Hb".
 iExists (LitV (LitInt av)). iFrame. done.
Qed.
Theorem compression_wp p pad w old base block h0 h1 h2 h3 h4 st :
 (base+64 <= length pad)%nat -> (80 <= length old)%nat ->
 StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) -∗
 state_at h0 h1 h2 h3 h4 st -∗ array.array_cells p pad -∗ array.array_cells w old -∗
 WP compression_bound p w block h0 h1 h2 h3 h4
 {{u, ⌜u = LitV LitUnit⌝ ∗ StackId block ↦ₛ LitV (LitInt (Z.of_nat base)) ∗
   state_at h0 h1 h2 h3 h4 (model.compress st (take 64 (drop base pad))) ∗
   array.array_cells p pad ∗ array.array_cells w
     (model.schedule_more 64 (model.message_words (take 64 (drop base pad))) ++ drop 80 old)}}.
Proof.
 intros Hpad Hlen. iIntros "Hblock Hhash Hpad Hw". rewrite compression_source.
 iApply (schedule_prefix_wp with "Hblock Hpad Hw [Hhash]"); [exact Hpad|exact Hlen|].
 iIntros "Hblock Hpad Hw".
 iApply (wp_wand with "[Hhash Hw]").
 { iApply (compression_tail_wp with "Hhash Hw"). rewrite length_app schedule_length. lia. }
 iIntros (u) "[%Hu [Hhash Hw]]".
 rewrite compression_rounds_result. iFrame. done.
Qed.
End proofs.
