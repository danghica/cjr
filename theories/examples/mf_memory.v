From Coq Require Import Lia.
From iris.base_logic.lib Require Import ghost_map.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import proofmode.
From cjr Require Import primitive_laws.
From iris.prelude Require Import options.

Lemma mf_free_lookup_outside base n m z :
  (z < base \/ base + Z.of_nat n <= z)%Z ->
  free_cells base n m !! RawId z = m !! RawId z.
Proof.
  induction n as [|n IH]; intros H; [done|].
  simpl. rewrite lookup_delete_ne.
  - apply IH. lia.
  - intros E. injection E as E. lia.
Qed.

Lemma mf_free_dom_subset base n m :
  dom (free_cells base n m) ⊆ dom m.
Proof.
  induction n as [|n IH]; [done|]. simpl. rewrite dom_delete. set_solver.
Qed.

Lemma mf_wf_free_block σ base n :
  cjr_blocks σ !! RawId base = Some n -> state_wf σ ->
  state_wf (set_blocks (delete (RawId base) (cjr_blocks σ))
    (set_raw (free_cells base n (cjr_raw σ)) σ)).
Proof.
  intros Hlen [Hs Hr Hb Ho Hc Hd]. split; simpl; try done.
  - intros z Hz. apply Hr. apply (mf_free_dom_subset base n). exact Hz.
  - intros z Hz. rewrite dom_delete in Hz. apply Hb. set_solver.
  - intros z len Hn.
    destruct (decide (z = base)) as [->|Hne].
    + rewrite lookup_delete in Hn. discriminate.
    + rewrite lookup_delete_ne in Hn; last (intros E; injection E; done).
      destruct (Hc z len Hn) as [Hle Hcells]. split; [done|].
      intros i Hi. destruct (Hcells i Hi) as [v Hv]. exists v.
      rewrite mf_free_lookup_outside; [exact Hv|].
      destruct (Hd base n z len Hlen Hn) as [Hdis|Hdis]; lia.
  - intros l1 n1 l2 n2 H1 H2 Hneq.
    destruct (decide (l1 = base)) as [->|Hn1]; [rewrite lookup_delete in H1; discriminate|].
    destruct (decide (l2 = base)) as [->|Hn2]; [rewrite lookup_delete in H2; discriminate|].
    rewrite lookup_delete_ne in H1; last (intros E; injection E; done).
    rewrite lookup_delete_ne in H2; last (intros E; injection E; done).
    eapply Hd; eauto.
Qed.

Section memory.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

Lemma mf_ghost_free_cells base vs m :
  ghost_map_auth cjr_raw_name 1 m -∗
  ([∗ list] i ↦ v ∈ vs, RawId (base + Z.of_nat i)%Z ↦ᵣ v) ==∗
  ghost_map_auth cjr_raw_name 1 (free_cells base (length vs) m).
Proof.
  revert m. induction vs using rev_ind; intros m.
  - simpl. iIntros "Hm _". done.
  - iIntros "Hm Hcells".
    rewrite big_sepL_app big_sepL_singleton Nat.add_0_r.
    iDestruct "Hcells" as "[Hpre Hlast]".
    iMod (IHvs with "Hm Hpre") as "Hm".
    iMod (ghost_map_delete with "Hm Hlast") as "Hm".
    replace (length (vs ++ [x])) with (S (length vs)) by (rewrite length_app; simpl; lia).
    simpl. done.
Qed.

Lemma mf_wp_free_block base vs E Φ :
  RawId base ↦ᵦ length vs -∗
  ([∗ list] i ↦ v ∈ vs, RawId (base + Z.of_nat i)%Z ↦ᵣ v) -∗
  ▷ (£ 1 -∗ Φ (LitV LitUnit)) -∗
  WP Free (Val (LitV (LitPtr base))) @ E {{ Φ }}.
Proof.
  iIntros "Hblk Hcells HΦ".
  iApply wp_lift_atomic_base_step_no_fork; [done|].
  iIntros (σ ns κ κs nt) "(Hs & Hr & Hb & Ho & %Hwf)".
  iDestruct (ghost_map_lookup with "Hb Hblk") as %Hlen.
  iModIntro. iSplit.
  { iPureIntro. eexists [], (Val (LitV LitUnit)), _, [].
    eapply (FreeS base (length vs)); exact Hlen. }
  iIntros "!>" (e2 σ2 efs Hstep) "Hcred".
  assert (base_step (Free (Val (LitV (LitPtr base)))) σ [] (Val (LitV LitUnit))
    (set_blocks (delete (RawId base) (cjr_blocks σ))
      (set_raw (free_cells base (length vs) (cjr_raw σ)) σ)) []) as Hgood.
  { eapply (FreeS base (length vs)); exact Hlen. }
  destruct (base_step_det _ _ _ _ _ _ _ _ _ _ Hstep Hgood) as (-> & -> & -> & ->).
  iMod (mf_ghost_free_cells with "Hr Hcells") as "Hr".
  iMod (ghost_map_delete with "Hb Hblk") as "Hb".
  iModIntro. iSplit; [done|]. iSplitL "Hs Hr Hb Ho".
  { iFrame. iPureIntro. eapply mf_wf_free_block; eauto. }
  iApply ("HΦ" with "Hcred").
Qed.
End memory.
