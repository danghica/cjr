(** Stateful IGE refinement over disjoint caller-owned buffers. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics array.
From cjr.aes_ige Require Import bytes block aes ige program memory kernels routines calls cipher syntax ige_syntax mode.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Fixpoint blocks_at `{!cjrGS Σ} p xs : iProp Σ :=
 match xs with [] => emp | b::bs => block_at p b ∗ blocks_at (p+16) bs end.
Definition iv_at `{!cjrGS Σ} p (v : iv) : iProp Σ := block_at p (fst v) ∗ block_at (p+16) (snd v).
Definition workspace_at `{!cjrGS Σ} p : iProp Σ :=
 ∃ a b c d, block_at p a ∗ block_at (p+16) b ∗ block_at (p+32) c ∗ block_at (p+48) d.
Opaque encrypt_body decrypt_body copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body sbox_body inv_sbox_body xtime_body.
Lemma work_pack `{!cjrGS Σ} w a d : block_at w a -∗ block_at (w+16) d -∗ work_at w.
Proof. iIntros "Ha Hd". iExists a,d. iFrame. Qed.
Local Opaque block_at schedule_at xor encrypt decrypt encrypt_schedule decrypt_schedule
 sub_bytes inv_sub_bytes shift_rows inv_shift_rows mix_columns inv_mix_columns.
Ltac abstract_destination ::= fun q =>
 iMatchHyp ltac:(fun H P => lazymatch P with block_at ?loc ?payload =>
   let Eloc := fresh in assert (Eloc : loc = q) by (cbn [Z.of_nat Z.mul]; lia);
   tryif is_var payload then idtac else
   (let state := fresh "state" in let Estate := fresh "Estate" in
    remember payload as state eqn:Estate in *;
    let Hbyte := fresh in assert (Hbyte : block_bytes state) by
     (rewrite Estate; first [assumption | apply decrypt_bytes; assumption | apply encrypt_bytes; assumption | apply xor_bytes; assumption | block_byte_goal]))
 end).
Ltac cipher_substitution := repeat first [progress routine_rewrite | match goal with
| |- context[subst "src" ?value encrypt_body] => rewrite (encrypt_body_subst_src value)
| |- context[subst "dst" ?value encrypt_body] => rewrite (encrypt_body_subst_dst value)
| |- context[subst "len" ?value encrypt_body] => rewrite (encrypt_body_subst_len value)
| |- context[subst "iv" ?value encrypt_body] => rewrite (encrypt_body_subst_iv value)
| |- context[subst "schedule" ?value encrypt_body] => rewrite (encrypt_body_subst_schedule value)
| |- context[subst "nr" ?value encrypt_body] => rewrite (encrypt_body_subst_nr value)
| |- context[subst "work" ?value encrypt_body] => rewrite (encrypt_body_subst_work value)
| |- context[subst "i" ?value encrypt_body] => rewrite (encrypt_body_subst_i value)
| |- context[subst "src" ?value decrypt_body] => rewrite (decrypt_body_subst_src value)
| |- context[subst "dst" ?value decrypt_body] => rewrite (decrypt_body_subst_dst value)
| |- context[subst "len" ?value decrypt_body] => rewrite (decrypt_body_subst_len value)
| |- context[subst "iv" ?value decrypt_body] => rewrite (decrypt_body_subst_iv value)
| |- context[subst "schedule" ?value decrypt_body] => rewrite (decrypt_body_subst_schedule value)
| |- context[subst "nr" ?value decrypt_body] => rewrite (decrypt_body_subst_nr value)
| |- context[subst "work" ?value decrypt_body] => rewrite (decrypt_body_subst_work value)
| |- context[subst "i" ?value decrypt_body] => rewrite (decrypt_body_subst_i value)
| |- context[subst_var "i" ?l copy_body] => rewrite (copy_body_stack_i l)
| |- context[subst_var "i" ?l xor_body] => rewrite (xor_body_stack_i l)
| |- context[subst_var "i" ?l sub_body] => rewrite (sub_body_stack_i l)
| |- context[subst_var "i" ?l inv_sub_body] => rewrite (inv_sub_body_stack_i l)
| |- context[subst_var "i" ?l shift_body] => rewrite (shift_body_stack_i l)
| |- context[subst_var "i" ?l inv_shift_body] => rewrite (inv_shift_body_stack_i l)
| |- context[subst_var "i" ?l mix_body] => rewrite (mix_body_stack_i l)
| |- context[subst_var "i" ?l encrypt_body] => rewrite (encrypt_body_stack_i l)
| |- context[subst_var "i" ?l decrypt_body] => rewrite (decrypt_body_stack_i l)
end].
Ltac ige_focus e k :=
 lazymatch e with
 | StackAssign (Val ?v) (Val ?w) => k ()
 | StackAssign (Val ?v) ?rhs => iApply (wp_bind [StackAssignRCtx v]); ige_focus rhs k
 | _ => hm_focus e k
 end.
Ltac ige_cipher spec key p q s w :=
 iMatchHyp ltac:(fun H P => lazymatch P with @block_at ?sig ?gs ?hp ?b =>
 let Ep := fresh in assert (Ep : p = hp) by (cbn [Z.of_nat Z.mul]; lia);
 iMatchHyp ltac:(fun D Q => lazymatch Q with block_at ?hq ?old =>
 let Eq := fresh in assert (Eq : q = hq) by (cbn [Z.of_nat Z.mul]; lia);
 let Hbyte := fresh in assert (Hbyte : block_bytes b) by block_byte_goal;
 iMatchHyp ltac:(fun W PW => lazymatch PW with block_at ?hw ?a =>
 let Ew := fresh in assert (Ew : w = hw) by (cbn [Z.of_nat Z.mul]; lia);
 iMatchHyp ltac:(fun T PT => lazymatch PT with block_at ?ht ?d =>
 let Et := fresh in assert (Et : w+16 = ht) by (cbn [Z.of_nat Z.mul]; lia);
 try iEval (rewrite <- Ew) in W;
 try iEval (rewrite <- Et) in T;
 iPoseProof (work_pack w a d with W) as "Hcipherwork";
 iSpecialize ("Hcipherwork" with T);
 try rewrite Ep; try rewrite Eq;
 iPoseProof (@spec sig gs _ hp hq s w key b old ltac:(assumption) Hbyte
   with "[$] [$] Hschedule Hcipherwork") as "Hcall";
 iApply (wp_wand with "Hcall"); let result := fresh "result" in
 iIntros (result) "(%E & ? & ? & Hschedule & Hcipherwork)"; subst result;
 iEval (unfold work_at) in "Hcipherwork"; iDestruct "Hcipherwork" as (? ?) "[? ?]"; abstract_destination hq
 end) end) end) end).
Ltac ige_head key := first [
 match goal with
 | |- envs_entails _ (WP StackLoad (Val (LitV (LitStack ?l))) {{_}}) =>
    iApply (wp_stack_load (StackId l) with "[$]"); iIntros "!> _ ?"
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") encrypt_body))
    (Val (StructV [LitV (LitPtr ?p);LitV (LitPtr ?q);LitV (LitPtr ?s);LitV (LitInt ?nr);LitV (LitPtr ?w)])) {{_}}) =>
    ige_cipher encrypt_block_app_wp key p q s w
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") decrypt_body))
    (Val (StructV [LitV (LitPtr ?p);LitV (LitPtr ?q);LitV (LitPtr ?s);LitV (LitInt ?nr);LitV (LitPtr ?w)])) {{_}}) =>
    ige_cipher decrypt_block_app_wp key p q s w
 end | complete_head ].
Ltac ige_run key := iStartProof; repeat (cbn [fill fill_item]; simpl;
 cipher_substitution;
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => ige_focus e ltac:(fun _ => ige_head key) end);
 cbn [fill fill_item]; simpl.
Section ownership.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma blocks_at_app p xs ys : blocks_at p (xs++ys)%list ⊣⊢
 blocks_at p xs ∗ blocks_at (p+16*Z.of_nat (length xs)) ys.
Proof.
 revert p. induction xs as [|b xs IH]; intros p; simpl.
 - rewrite Z.add_0_r left_id. reflexivity.
 - rewrite IH assoc. replace (p+16+16*Z.of_nat (length xs)) with
    (p+16*Z.of_nat (S (length xs))) by lia. reflexivity.
Qed.
Theorem ige_iteration_wp enc p q n vptr s w l i key b old v :
 valid_key key -> block_bytes b -> iv_bytes v ->
 StackId l ↦ₛ LitV (LitInt i) -∗ block_at (p+i) b -∗ block_at (q+i) old -∗
 iv_at vptr v -∗ schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP iteration_at enc p q n vptr s (Z.of_nat (rounds_of_length (length key))) w l
 {{result, ⌜result = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt i) ∗
 block_at (p+i) b ∗ block_at (q+i) (ige_step enc key b v) ∗
 iv_at vptr (next_iv enc b (ige_step enc key b v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey Hb Hv. destruct v as [prevC prevP]. destruct Hv as [HC HP].
 iIntros "Hi Hsrc Hdst Hiv Hschedule Hwork".
 iEval (unfold iv_at; simpl) in "Hiv". iDestruct "Hiv" as "[? ?]". iEval (unfold workspace_at) in "Hwork". iDestruct "Hwork" as (a d t u) "(? & ? & ? & ?)".
 destruct enc; unfold iteration_at, ige_environment, ige_iteration, cipher_call,
  ige_work, ige_tmp, in_at, out_at, ivp, ivq, cp, xx, invoke, ptr, work, int, unit_e, seqs;
  ige_run key.
 all: iSplit; [done|].
 all: unfold iv_at, next_iv, ige_step, enc_step, dec_step, workspace_at; simpl.
 all: repeat match goal with H : @Logic.eq block ?state ?rhs |- _ =>
   is_var state; progress rewrite <- H end.
 all: iFrame; try (iExists _, _, _, _; iFrame).
Qed.
Local Opaque iteration_at loop_at ige_spec.
Ltac counter_admin := iStartProof; repeat (cbn [fill fill_item]; simpl;
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) =>
  ige_focus e ltac:(fun _ => first [
   match goal with
   | |- envs_entails _ (WP StackLoad (Val (LitV (LitStack ?l))) {{_}}) =>
      iApply (wp_stack_load (StackId l) with "Hi"); iIntros "!> _ Hi"
   | |- envs_entails _ (WP StackAssign (Val (LitV (LitStack ?l))) (Val ?v) {{_}}) =>
      iApply (wp_stack_assign (StackId l) with "Hi"); iIntros "!> _ Hi"
   end | hm_head]) end);
 cbn [fill fill_item]; simpl.
Theorem ige_loop_wp enc p q n vptr s w l i key xs old v :
 valid_key key -> Forall block_bytes xs -> iv_bytes v ->
 length old = length xs -> n = i + 16*Z.of_nat (length xs) ->
 StackId l ↦ₛ LitV (LitInt i) -∗ blocks_at (p+i) xs -∗ blocks_at (q+i) old -∗
 iv_at vptr v -∗ schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP loop_at enc p q n vptr s (Z.of_nat (rounds_of_length (length key))) w l
 {{result, ⌜result = LitV LitUnit⌝ ∗ StackId l ↦ₛ LitV (LitInt n) ∗
 blocks_at (p+i) xs ∗ blocks_at (q+i) (fst (ige_spec enc key xs v)) ∗
 iv_at vptr (snd (ige_spec enc key xs v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey. revert i old v. induction xs as [|b bs IH]; intros i old v Hbytes Hv Hlen Hn.
 - destruct old; [|simpl in Hlen; lia].
   iIntros "Hi Hsrc Hdst Hiv Hschedule Hwork".
   unfold loop_at at 1. iApply wp_while. unfold le, counter, int.
   counter_admin. rewrite bool_decide_false; [|simpl in Hn; lia].
   iApply wp_if_false. iApply wp_value'.
   Local Transparent ige_spec. destruct enc; simpl in Hn |- *; rewrite ?Z.add_0_r in Hn; subst n; simpl.
   all: iFrame; done.
   Local Opaque ige_spec.
 - destruct old as [|o os]; [simpl in Hlen; lia|]. apply Forall_cons in Hbytes. destruct Hbytes as [Hb Hbs].
   iIntros "Hi Hsrc Hdst Hiv Hschedule Hwork".
   iDestruct "Hsrc" as "[Hsrc Hsrcs]". iDestruct "Hdst" as "[Hdst Hdsts]".
   unfold loop_at at 1. iApply wp_while. unfold le, counter, int.
   counter_admin. rewrite bool_decide_true; [|simpl in Hn; lia]. iApply wp_if_true.
   iApply (wp_bind [SeqCtx (loop_at enc p q n vptr s (Z.of_nat (rounds_of_length (length key))) w l)]).
   iApply (wp_bind [SeqCtx (StackAssign (Val (LitV (LitStack l))) (plus (StackLoad (Val (LitV (LitStack l)))) (program.int 16)))]).
   iApply (wp_wand with "[Hi Hsrc Hdst Hiv Hschedule Hwork]").
   { iApply (ige_iteration_wp with "Hi Hsrc Hdst Hiv Hschedule Hwork"); assumption. }
   iIntros (result) "(%E & Hi & Hsrc & Hdst & Hiv & Hschedule & Hwork)". subst result.
   iApply wp_seq. unfold plus, program.int. counter_admin.
   assert (Ep : p+i+16 = p+(i+16)) by lia.
   assert (Eq : q+i+16 = q+(i+16)) by lia.
   iEval (rewrite Ep) in "Hsrcs". iEval (rewrite Eq) in "Hdsts".
   iApply (wp_wand with "[Hi Hsrcs Hdsts Hiv Hschedule Hwork]").
   { iApply (IH (i+16) os (next_iv enc b (ige_step enc key b v)) with "Hi Hsrcs Hdsts Hiv Hschedule Hwork").
     - assumption.
     - apply next_iv_range; assumption.
     - simpl in Hlen; lia.
     - simpl in Hn; lia. }
   iIntros (result) "(%E & Hi & Hsrcs & Hdsts & Hiv & Hschedule & Hwork)". subst result.
   rewrite ige_spec_step.
   destruct (ige_spec enc key bs (next_iv enc b (ige_step enc key b v))) as [outs final] eqn:E.
   simpl. rewrite E. simpl. iEval (try rewrite E; simpl) in "Hdsts Hiv".
   simpl blocks_at. rewrite ?Ep ?Eq. iFrame. done.
Qed.
Opaque ige_iteration ige_loop_source.
Ltac entry_admin := iStartProof; repeat (cbn [fill fill_item]; simpl;
 repeat match goal with
 | |- context[subst "args" ?v (ige_loop_source ?enc)] => rewrite (ige_loop_source_args enc v)
 end;
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) =>
  hm_focus e ltac:(fun _ => first [iApply wp_if_true|iApply wp_if_false|hm_head]) end);
 cbn [fill fill_item]; simpl.
Theorem ige_public_wp enc p q vptr s w key xs old v :
 valid_key key -> Forall block_bytes xs -> iv_bytes v -> length old = length xs ->
 blocks_at p xs -∗ blocks_at q old -∗ iv_at vptr v -∗
 schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP invoke (ige_body enc) [pv p;pv q;int (16*Z.of_nat (length xs));pv vptr;pv s;
  int (Z.of_nat (rounds_of_length (length key)));pv w]
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ blocks_at p xs ∗
 blocks_at q (fst (ige_spec enc key xs v)) ∗ iv_at vptr (snd (ige_spec enc key xs v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey Hbytes Hv Hlen. iIntros "Hsrc Hdst Hiv Hschedule Hwork".
 assert (Hrem : Z.rem (16*Z.of_nat (length xs)) 16 = 0).
 { rewrite Z.mul_comm. apply Z.rem_mul. lia. }
 pose proof (key_supported_rounds key Hkey) as Hnr.
 Local Transparent ige_loop_source.
 lazymatch goal with |- envs_entails ?Δ (WP ?e {{?Φ}}) =>
 change (envs_entails Δ (WP invoke (args ["src";"dst";"len";"iv";"schedule";"nr";"work"]
  (If (le (int 0) (Var "len"))
    (If (eq (BinOp RemOp (Var "len") (int 16)) (int 0))
      (If valid_rounds (VarBind "i" (int 0) (ige_loop_source enc)) (bool_e false))
      (bool_e false)) (bool_e false)))
  [pv p;pv q;int (16*Z.of_nat (length xs));pv vptr;pv s;
   int (Z.of_nat (rounds_of_length (length key)));pv w] {{Φ}})%I) end.
 Local Opaque ige_loop_source.
 unfold invoke, args, valid_rounds, pv, int, eq, le, bool_e.
 entry_admin.
 rewrite bool_decide_true; [|lia]. iApply wp_if_true. entry_admin.
 rewrite Hrem. entry_admin.
 destruct Hnr as [Hnr|[Hnr|Hnr]]; rewrite Hnr; entry_admin.
 all: rewrite <- (f_equal Z.of_nat Hnr).
 all: iApply wp_var_bind; iIntros (l) "Hi".
 all: lazymatch goal with |- envs_entails ?Δ (WP ?e {{?Φ}}) =>
 change (envs_entails Δ (WP subst_var "i" l
  (ige_environment p q (16*Z.of_nat (length xs)) vptr s
    (Z.of_nat (rounds_of_length (length key))) w (ige_loop_source enc)) {{Φ}})%I) end.
 all: rewrite ige_bound_loop.
 all: iApply (wp_bind [SeqCtx (bool_e true)]).
 all: iApply (wp_wand with "[Hi Hsrc Hdst Hiv Hschedule Hwork]").
 all: try (
  iPoseProof (ige_loop_wp enc p q (16*Z.of_nat (length xs)) vptr s w l 0 key xs old v
    Hkey Hbytes Hv Hlen ltac:(lia)) as "Hloop";
  iEval (rewrite !Z.add_0_r) in "Hloop";
  iApply ("Hloop" with "Hi Hsrc Hdst Hiv Hschedule Hwork")).
 all: iIntros (result) "(%E & Hi & Hsrc & Hdst & Hiv & Hschedule & Hwork)"; subst result.
 all: iApply wp_seq; iApply wp_value'; iExists (LitV (LitInt (16*Z.of_nat (length xs)))); iFrame; done.
Qed.
End ownership.
