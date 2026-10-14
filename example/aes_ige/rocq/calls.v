(** Administrative call rules; these never access a caller's raw buffers. *)
From Coq Require Import List String.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From cjr.examples Require Import array.
From cjr.aes_ige Require Import program.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma struct_values_wp ready vs :
 ⊢ WP Struct ready (map Val vs) {{v, ⌜v = StructV (ready++vs)%list⌝}}.
Proof.
 revert ready. induction vs as [|v vs IH]; intros ready; cbn [List.map].
 - iApply wp_struct_done. iIntros "!> _". rewrite app_nil_r. done.
 - iApply wp_struct_step. iApply (wp_wand with "[]"); [iApply IH|].
   iIntros (w) "%E". subst w. rewrite <- app_assoc. simpl. done.
Qed.
Lemma invoke_from_app body vs Φ :
 WP App (Val (RecV None (Some "args") body)) (Val (StructV vs)) {{Φ}} -∗
 WP invoke body (map Val vs) {{Φ}}.
Proof.
 iIntros "H". unfold invoke.
 iApply (wp_bind [AppLCtx (Struct [] (map Val vs))]).
 iApply wp_rec. iIntros "!> _".
 iApply (wp_bind [AppRCtx (RecV None (Some "args") body)]).
 iApply (wp_wand with "[]"); [iApply struct_values_wp|].
 iIntros (v) "%E". subst v. simpl. iExact "H".
Qed.
End proofs.
