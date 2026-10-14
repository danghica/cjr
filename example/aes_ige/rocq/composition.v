(** Client contracts derived from concrete refinement and pure algebra. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.aes_ige Require Import block aes ige program memory routines mode ige_refinement index_bounds.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition ige_call enc (key : list Z) p q count vptr s w := invoke (ige_body enc)
 [pv p;pv q;int (16*Z.of_nat count);pv vptr;pv s;
  int (Z.of_nat (rounds_of_length (length key)));pv w].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem ige_call_wp enc p q count vptr s w key xs old v :
 count = length xs -> valid_key key -> Forall block_bytes xs -> iv_bytes v -> length old = length xs ->
 blocks_at p xs -∗ blocks_at q old -∗ iv_at vptr v -∗
 schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP ige_call enc key p q count vptr s w
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ blocks_at p xs ∗
 blocks_at q (fst (ige_spec enc key xs v)) ∗ iv_at vptr (snd (ige_spec enc key xs v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof. intros ->. apply ige_public_wp. Qed.
(** Both IV buffers initially contain the original IV.  The inverse call uses
    that original value; it never starts from the mutated first-call IV. *)
Theorem ige_implementation_roundtrip enc p q r iv1 iv2 s w key xs oldq oldr v :
 valid_key key -> Forall block_bytes xs -> iv_bytes v ->
 length oldq = length xs -> length oldr = length xs ->
 blocks_at p xs -∗ blocks_at q oldq -∗ blocks_at r oldr -∗
 iv_at iv1 v -∗ iv_at iv2 v -∗ schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP Seq (ige_call enc key p q (length xs) iv1 s w)
        (ige_call (negb enc) key q r (length xs) iv2 s w)
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ blocks_at p xs ∗
 blocks_at q (fst (ige_spec enc key xs v)) ∗ blocks_at r xs ∗
 iv_at iv1 (snd (ige_spec enc key xs v)) ∗ iv_at iv2 (snd (ige_spec enc key xs v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey Hxs Hv Hq Hr. iIntros "Hp Hq Hr Hiv1 Hiv2 Hschedule Hwork".
 iApply (wp_bind [SeqCtx (ige_call (negb enc) key q r (length xs) iv2 s w)]).
 iApply (wp_wand with "[Hp Hq Hiv1 Hschedule Hwork]").
 { iApply (ige_call_wp with "Hp Hq Hiv1 Hschedule Hwork"); try assumption; reflexivity. }
 iIntros (result) "(%E & Hp & Hq & Hiv1 & Hschedule & Hwork)". subst result. iApply wp_seq.
 iApply (wp_wand with "[Hq Hr Hiv2 Hschedule Hwork]").
 { iApply (ige_call_wp with "Hq Hr Hiv2 Hschedule Hwork").
   - symmetry. apply ige_spec_length.
   - assumption.
   - exact (proj1 (ige_spec_range enc key xs v Hxs Hv)).
   - assumption.
   - rewrite ige_spec_length. assumption. }
 iIntros (result) "(%E & Hq & Hr & Hiv2 & Hschedule & Hwork)".
 iEval (rewrite ige_spec_inverse; [simpl|assumption|assumption]) in "Hr Hiv2".
 iFrame. done.
Qed.
Theorem ige_implementation_chunks enc p q ivptr s w key xs ys oldx oldy v :
 valid_key key -> Forall block_bytes xs -> Forall block_bytes ys -> iv_bytes v ->
 length oldx = length xs -> length oldy = length ys ->
 blocks_at p (xs++ys)%list -∗ blocks_at q (oldx++oldy)%list -∗
 iv_at ivptr v -∗ schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP Seq (ige_call enc key p q (length xs) ivptr s w)
 (ige_call enc key (p+16*Z.of_nat (length xs)) (q+16*Z.of_nat (length xs)) (length ys) ivptr s w)
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ blocks_at p (xs++ys)%list ∗
 blocks_at q (fst (ige_spec enc key (xs++ys)%list v)) ∗
 iv_at ivptr (snd (ige_spec enc key (xs++ys)%list v)) ∗
 schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey Hxs Hys Hv Hx Hy. iIntros "Hsrc Hdst Hiv Hschedule Hwork".
 iEval (rewrite blocks_at_app) in "Hsrc Hdst".
 iDestruct "Hsrc" as "[Hsrc Hsrcs]". iDestruct "Hdst" as "[Hdst Hdsts]".
 iEval (rewrite Hx) in "Hdsts".
 iApply (wp_bind [SeqCtx (ige_call enc key (p+16*Z.of_nat (length xs)) (q+16*Z.of_nat (length xs)) (length ys) ivptr s w)]).
 iApply (wp_wand with "[Hsrc Hdst Hiv Hschedule Hwork]").
 { iApply (ige_call_wp with "Hsrc Hdst Hiv Hschedule Hwork"); try assumption; reflexivity. }
 iIntros (result) "(%E & Hsrc & Hdst & Hiv & Hschedule & Hwork)". subst result. iApply wp_seq.
 iApply (wp_wand with "[Hsrcs Hdsts Hiv Hschedule Hwork]").
 { iApply (ige_call_wp with "Hsrcs Hdsts Hiv Hschedule Hwork"); try assumption; try reflexivity.
   exact (proj2 (ige_spec_range enc key xs v Hxs Hv)). }
 iIntros (result) "(%E & Hsrcs & Hdsts & Hiv & Hschedule & Hwork)".
 rewrite ige_spec_chunks.
 destruct (ige_spec enc key xs v) as [first middle] eqn:Efirst.
 destruct (ige_spec enc key ys middle) as [second final] eqn:Esecond.
 simpl. rewrite ?Efirst ?Esecond. simpl. iEval (try rewrite Efirst; simpl) in "Hdst".
 iEval (try rewrite Efirst; simpl; try rewrite Esecond; simpl) in "Hdsts Hiv".
 rewrite !blocks_at_app.
 assert (Hfirst : length first = length xs).
 { pose proof (ige_spec_length enc key xs v) as H. rewrite Efirst in H. exact H. }
 rewrite Hfirst. iFrame. done.
Qed.
Theorem ige_implementation_empty enc p q vptr s w key v : valid_key key -> iv_bytes v ->
 iv_at vptr v -∗ schedule_at s (key_schedule key) -∗ workspace_at w -∗
 WP ige_call enc key p q 0 vptr s w
 {{result, ⌜result = LitV (LitBool true)⌝ ∗ iv_at vptr v ∗ schedule_at s (key_schedule key) ∗ workspace_at w}}.
Proof.
 intros Hkey Hv. iIntros "Hiv Hschedule Hwork".
 iApply (wp_wand with "[Hiv Hschedule Hwork]").
 { iApply (ige_call_wp enc p q 0 vptr s w key [] [] v with "[] [] Hiv Hschedule Hwork"); auto. }
 iIntros (result) "(%E & _ & _ & Hiv & Hschedule & Hwork)".
 rewrite ige_spec_empty. simpl. iFrame. done.
Qed.
End proofs.
