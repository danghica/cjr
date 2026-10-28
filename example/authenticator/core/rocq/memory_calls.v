(** Buffer copy contract at a reduced application, for computed arguments. *)
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
Definition copy_application src dst n :=
 App (Val (RecV None (Some "args") copy_body))
 (Val (StructV [LitV (LitPtr src);LitV (LitPtr dst);LitV (LitInt n)])).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem copy_application_wp p q src dst n :
 (n <= length src)%nat -> (n <= length dst)%nat ->
 array.array_cells p src -∗ array.array_cells q dst -∗
 WP copy_application p q (Z.of_nat n)
 {{u, ⌜u = LitV LitUnit⌝ ∗ array.array_cells p src ∗
       array.array_cells q (take n src ++ drop n dst)}}.
Proof.
 intros Hsrc Hdst. iIntros "Hs Hd".
 unfold copy_application. iApply wp_app. unfold copy_body, args. hm_pure.
 set (I := fun i : Z => (array.array_cells p src ∗
   array.array_cells q (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst))%I).
 iApply (wp_wand with "[Hs Hd]").
 { iApply (loop_wp "copyI" 0 (Z.of_nat n)
     (put (pv q) (v "copyI") (get (pv p) (v "copyI"))) I with "[Hs Hd]").
   - intros l i Hi. iIntros "Hl [Hs Hd]".
     unfold put, get, ptr, pv, v. cbn [subst_var subst_var_val].
     rewrite bool_decide_true; last done. memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hks : (Z.to_nat i < length src)%nat) by lia.
     destruct (lookup_lt_is_Some_2 src (Z.to_nat i) Hks) as [x Hx].
     iDestruct (big_sepL_lookup_acc with "Hs") as "[Hx Hclose]"; [exact Hx|].
     rewrite Hki. iApply (wp_load with "Hx"). iIntros "!> _ Hx".
     iDestruct ("Hclose" with "Hx") as "Hs". memory_admin.
     assert (Hkd : (Z.to_nat i < length (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst))%nat).
     { rewrite length_app length_take length_drop. lia. }
     destruct (lookup_lt_is_Some_2 _ _ Hkd) as [old Hold].
     iDestruct (big_sepL_insert_acc with "Hd") as "[Hcell Hclose]"; [exact Hold|].
     rewrite Hki. iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" $! x with "Hcell") as "Hd".
     assert (Hfill : <[Z.to_nat i := x]>
       (take (Z.to_nat i) src ++ drop (Z.to_nat i) dst) =
       take (S (Z.to_nat i)) src ++ drop (S (Z.to_nat i)) dst).
     { apply prefix_write_step; [exact Hx|lia]. }
     iAssert (array.array_cells q
       (take (S (Z.to_nat i)) src ++ drop (S (Z.to_nat i)) dst)) with "[Hd]" as "Hd".
     { rewrite <- Hfill. iExact "Hd". }
     iFrame "Hl Hs". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r. iExact "Hd".
   - lia.
   - unfold I. simpl. iFrame.
 }
 iIntros (u) "[%Hu [Hs Hd]]". unfold I. rewrite Nat2Z.id. iFrame. done.
Qed.
End proofs.
