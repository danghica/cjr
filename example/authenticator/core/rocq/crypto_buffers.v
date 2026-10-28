(** The 64-byte HMAC inner/outer key pad loop. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition xor_pad_loop key inner outer :=
 loop "i" (int 0) (int 64)
 (Seq (put (pv inner) (v "i") (xor (get (pv key) (v "i")) (int 54)))
      (put (pv outer) (v "i") (xor (get (pv key) (v "i")) (int 92)))).
Fixpoint skip_let_bindings n e := match n with
 | O => e | S n => match e with Let _ _ rest => skip_let_bindings n rest | _ => unit_e end end.
Definition hmac_xor_pad_source :=
 match skip_let_bindings 5 hmac_body with
 | If _ (If _ success _) _ =>
   match skip_let_bindings 4 success with Seq _ (Seq pad _) => pad | _ => unit_e end
 | _ => unit_e
 end.
Lemma xor_pad_loop_is_source p q r :
 subst "kb" (LitV (LitPtr p)) (subst "inner" (LitV (LitPtr q))
  (subst "outer" (LitV (LitPtr r)) hmac_xor_pad_source)) = xor_pad_loop p q r.
Proof. reflexivity. Qed.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem xor_pad_loop_wp p q r key inner outer :
 (64 <= length key)%nat -> (64 <= length inner)%nat -> (64 <= length outer)%nat ->
 array.array_cells p key -∗ array.array_cells q inner -∗ array.array_cells r outer -∗
 WP xor_pad_loop p q r
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p key ∗
   array.array_cells q (map (fun b => Z.lxor b 54) (take 64 key) ++ drop 64 inner) ∗
   array.array_cells r (map (fun b => Z.lxor b 92) (take 64 key) ++ drop 64 outer)}}.
Proof.
 intros Hkey Hinner Houter. iIntros "Hkey Hinner Houter". unfold xor_pad_loop.
 set (I := fun i : Z => (array.array_cells p key ∗
   array.array_cells q (take (Z.to_nat i) (map (fun b => Z.lxor b 54) key) ++ drop (Z.to_nat i) inner) ∗
   array.array_cells r (take (Z.to_nat i) (map (fun b => Z.lxor b 92) key) ++ drop (Z.to_nat i) outer))%I).
 iApply (wp_wand with "[Hkey Hinner Houter]").
 { iApply (loop_wp "i" 0 64 _ I with "[Hkey Hinner Houter]").
   - intros l i Hi. iIntros "Hl [Hkey [Hinner Houter]]".
     unfold put, get, ptr, pv, xor, op, v, int. cbn [subst_var subst_var_val].
     rewrite bool_decide_true; last done. memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hk : (Z.to_nat i < length key)%nat) by lia.
     destruct (lookup_lt_is_Some_2 key (Z.to_nat i) Hk) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hkey") as "[Hx Hclose]"; [exact Hx|].
     rewrite Hki. iApply (wp_load with "Hx"). iIntros "!> _ Hx".
     iDestruct ("Hclose" with "Hx") as "Hkey". memory_admin.
     assert (Hqi : (Z.to_nat i < length (take (Z.to_nat i) (map (fun b => Z.lxor b 54) key) ++ drop (Z.to_nat i) inner))%nat).
     { rewrite length_app length_take length_map length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hqi) as [old Hold].
     iDestruct (big_sepL_insert_acc with "Hinner") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (Z.lxor x 54) with "Hcell") as "Hinner". memory_admin.
     iDestruct (big_sepL_lookup_acc with "Hkey") as "[Hx Hclose]"; [exact Hx|].
     rewrite Hki. iApply (wp_load with "Hx"). iIntros "!> _ Hx".
     iDestruct ("Hclose" with "Hx") as "Hkey". memory_admin.
     assert (Hri : (Z.to_nat i < length (take (Z.to_nat i) (map (fun b => Z.lxor b 92) key) ++ drop (Z.to_nat i) outer))%nat).
     { rewrite length_app length_take length_map length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hri) as [oldr Holdr].
     iDestruct (big_sepL_insert_acc with "Houter") as "[Hcell Hclose]"; [exact Holdr|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! (Z.lxor x 92) with "Hcell") as "Houter".
     unfold I. rewrite Z2Nat.inj_add; [|lia|lia]. simpl. rewrite Nat.add_1_r.
     iFrame "Hl Hkey". iSplitL "Hinner".
     + rewrite <- (prefix_write_step (map (fun b => Z.lxor b 54) key) inner (Z.to_nat i) (Z.lxor x 54));
       [iExact "Hinner"|rewrite list_lookup_fmap Hx; done|lia].
     + rewrite <- (prefix_write_step (map (fun b => Z.lxor b 92) key) outer (Z.to_nat i) (Z.lxor x 92));
       [iExact "Houter"|rewrite list_lookup_fmap Hx; done|lia].
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hkey [Hinner Houter]]]". unfold I.
 rewrite <- !fmap_take. iFrame. done.
Qed.
End proofs.
