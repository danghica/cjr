(** Mutable SHA-1 state initialization, block fold, and digest emission. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement memory sha1_memory round_model sha1_rounds sha1_compress sha1_blocks sha1_iteration sha1_loop sha1_digest.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition sha_state p w q total :=
 vars [("h0",int 1732584193);("h1",int 4023233417);("h2",int 2562383102);
       ("h3",int 271733878);("h4",int 3285377520);("block",int 0)]
 (Seq (While (le (v "block") (sub (int (Z.of_nat total)) (int 1)))
   (Seq (subst "pad" (LitV (LitPtr p)) (subst "w" (LitV (LitPtr w)) sha_compress))
     (Assign "block" (add (v "block") (int 64)))))
   (seqs (map (fun ni => emit_be (pv q) (int (4 * Z.of_nat (fst ni))) (v (snd ni)) 4)
          [(0%nat,"h0");(1%nat,"h1");(2%nat,"h2");(3%nat,"h3");(4%nat,"h4")]) unit_e)).
#[local] Hint Rewrite round_closed_h0 round_closed_h1 round_closed_h2 round_closed_h3 round_closed_h4
 round_closed_a round_closed_b round_closed_c round_closed_d round_closed_e round_closed_pad
 round_closed_w round_closed_block : state_subst.
Opaque round_body model.hash_blocks model.compress model.schedule_more.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem sha_state_wp p pad w old q dst total :
 (total <= length pad)%nat -> (total mod 64 = 0)%nat -> length old = 80%nat ->
 (20 <= length dst)%nat ->
 array.array_cells p pad -∗ array.array_cells w old -∗ array.array_cells q dst -∗
 WP sha_state p w q total
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p pad ∗
   (∃ ws, ⌜length ws = 80%nat⌝ ∗ array.array_cells w ws) ∗
   array.array_cells q (flat_map (model.be_bytes 4) (model.hash_blocks (total/64) pad model.initial) ++ drop 20 dst)}}.
Proof.
 intros Hpad Htotal Hold Hdst. iIntros "Hpad Hw Hd". unfold sha_state, vars.
 cbn [fold_right]. iApply wp_var_bind. iIntros (h0) "H0".
 simpl. autorewrite with state_subst.
 iApply wp_var_bind. iIntros (h1) "H1". simpl. autorewrite with state_subst.
 iApply wp_var_bind. iIntros (h2) "H2". simpl. autorewrite with state_subst.
 iApply wp_var_bind. iIntros (h3) "H3". simpl. autorewrite with state_subst.
 iApply wp_var_bind. iIntros (h4) "H4". simpl. autorewrite with state_subst.
 iApply wp_var_bind. iIntros (block) "Hl". simpl. autorewrite with state_subst.
 match goal with |- envs_entails ?Delta (WP _ {{?Phi}}) =>
   change (envs_entails Delta (WP Seq (hash_loop p w block h0 h1 h2 h3 h4 total)
     (digest_emission q h0 h1 h2 h3 h4) {{Phi}})) end.
 iApply (wp_bind [SeqCtx (digest_emission q h0 h1 h2 h3 h4)]).
 iApply (wp_wand with "[Hl H0 H1 H2 H3 H4 Hpad Hw]").
 { iApply (hash_loop_wp with "Hl [H0 H1 H2 H3 H4] Hpad Hw"); try done.
   iExists _,_,_,_,_. iFrame. done. }
 iIntros (u) "[%Hu [Hl [Hhash [Hpad Hws]]]]". subst u. iApply wp_seq.
 iApply (wp_wand with "[Hhash Hd]").
 { iApply (digest_emission_wp with "Hhash Hd"). exact Hdst. }
 iIntros (u) "[%Hu [Hhash Hd]]".
 iDestruct "Hhash" as (av bv cv dv ev) "[%Hhash [H0 [H1 [H2 [H3 H4]]]]]".
 iExists (LitV (LitInt (Z.of_nat total))). iFrame "Hl".
 iExists (LitV (LitInt ev)). iFrame "H4".
 iExists (LitV (LitInt dv)). iFrame "H3".
 iExists (LitV (LitInt cv)). iFrame "H2".
 iExists (LitV (LitInt bv)). iFrame "H1".
 iExists (LitV (LitInt av)). iFrame. done.
Qed.
End proofs.
