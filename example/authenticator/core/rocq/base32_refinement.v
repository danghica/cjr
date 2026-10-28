(** Heap refinement of the canonical Base32 streaming decoder. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics.
From cjr.authenticator Require Import program refinement memory base32_stream.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.
Definition stack_e l := Val (LitV (LitStack l)).
Definition stack_get l := StackLoad (stack_e l).
Definition factor_e bits := If (eq bits (int 8)) (int 1)
 (If (eq bits (int 9)) (int 2) (If (eq bits (int 10)) (int 4)
 (If (eq bits (int 11)) (int 8) (int 16)))).
Definition consume_digit_expr valid padding symbols acc bits out scratch digit :=
 If (both (range digit 0 31) (eq (stack_get padding) (int 0)))
 (seqs [StackAssign (stack_e symbols) (add (stack_get symbols) (int 1));
  StackAssign (stack_e acc) (add (mul (stack_get acc) (int 32)) digit);
  StackAssign (stack_e bits) (add (stack_get bits) (int 5))]
  (If (le (int 8) (stack_get bits))
   (lets [("factor",factor_e (stack_get bits))]
    (seqs [put (pv scratch) (stack_get out) (div (stack_get acc) (v "factor"));
     StackAssign (stack_e out) (add (stack_get out) (int 1));
     StackAssign (stack_e acc) (rem (stack_get acc) (v "factor"))]
     (StackAssign (stack_e bits) (sub (stack_get bits) (int 8))))) unit_e))
 (StackAssign (stack_e valid) no).
Definition consume_digit valid padding symbols acc bits out scratch digit :=
 consume_digit_expr valid padding symbols acc bits out scratch (int digit).
Definition process_char_expr valid padding symbols acc bits out scratch ch :=
 If (eq ch (int 61))
 (StackAssign (stack_e padding) (add (stack_get padding) (int 1)))
 (lets [("digit",call base32_value_body [ch])]
  (consume_digit_expr valid padding symbols acc bits out scratch (v "digit"))).
Definition process_char valid padding symbols acc bits out scratch ch :=
 process_char_expr valid padding symbols acc bits out scratch (int ch).
Definition scan_loop valid padding symbols acc bits out src scratch n :=
 loop "i" (int 0) (int (Z.of_nat n))
 (lets [("ch",get (pv src) (v "i"))]
  (process_char_expr valid padding symbols acc bits out scratch (v "ch"))).
Fixpoint strip_lets n e :=
 match n,e with S n',Let _ _ body => strip_lets n' body | _,_ => e end.
Fixpoint strip_vars n e :=
 match n,e with S n',VarBind _ _ body => strip_vars n' body | _,_ => e end.
Definition source_scan_loop :=
 match strip_lets 3 base32_body with
 | If _ (Let _ _ scope) _ =>
   match strip_vars 6 scope with Seq scan _ => scan | _ => unit_e end
 | _ => unit_e end.
Definition bind_scan valid padding symbols acc bits out e :=
 subst_var "out" out (subst_var "bits" bits (subst_var "acc" acc
   (subst_var "symbols" symbols (subst_var "padding" padding (subst_var "valid" valid e))))).
Lemma scan_loop_source valid padding symbols acc bits out src scratch n :
 bind_scan valid padding symbols acc bits out
 (subst "src" (LitV (LitPtr src))
 (subst "scratch" (LitV (LitPtr scratch))
 (subst "n" (LitV (LitInt (Z.of_nat n))) source_scan_loop))) =
 scan_loop valid padding symbols acc bits out src scratch n.
Proof. reflexivity. Qed.
Definition validation_e valid padding symbols acc out n :=
 both (stack_get valid) (both (range (stack_get out) 1 128)
 (both (eq (stack_get acc) (int 0))
 (both (If (eq (rem (stack_get symbols) (int 8)) (int 1)) no
   (If (eq (rem (stack_get symbols) (int 8)) (int 3)) no
    (If (eq (rem (stack_get symbols) (int 8)) (int 6)) no yes)))
 (If (eq (stack_get padding) (int 0)) yes
  (both (eq (rem (int (Z.of_nat n)) (int 8)) (int 0)) (range (stack_get padding) 1 6)))))).
Definition validation_result st n :=
 (scan_valid st &&
 (bool_decide (1 <= Z.of_nat (length (emitted (scan_bits st)))) &&
  bool_decide (Z.of_nat (length (emitted (scan_bits st))) <= 128)) &&
 bool_decide (accumulator (scan_bits st) = 0) &&
 (if bool_decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 1) then false else
  if bool_decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 3) then false else
  if bool_decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 6) then false else true) &&
 (if bool_decide (Z.of_nat (scan_padding st) = 0) then true else
  bool_decide (Z.rem (Z.of_nat n) 8 = 0) &&
  bool_decide (1 <= Z.of_nat (scan_padding st)) && bool_decide (Z.of_nat (scan_padding st) <= 6)))%bool.
Lemma nat_eqb_native n m : bool_decide (Z.of_nat n = Z.of_nat m) = (n =? m)%nat.
Proof. apply Bool.eq_true_iff_eq. rewrite bool_decide_eq_true Nat.eqb_eq. lia. Qed.
Lemma nat_leb_native n m : bool_decide (Z.of_nat n <= Z.of_nat m) = (n <=? m)%nat.
Proof. apply Bool.eq_true_iff_eq. rewrite bool_decide_eq_true Nat.leb_le. lia. Qed.
Lemma z_eqb_native n m : bool_decide (n = m)%Z = (n =? m)%Z.
Proof. apply Bool.eq_true_iff_eq. rewrite bool_decide_eq_true Z.eqb_eq. tauto. Qed.
Lemma nat_rem_native n : Z.rem (Z.of_nat n) 8 = Z.of_nat (n mod 8).
Proof. rewrite Z.rem_mod_nonneg; [rewrite Nat2Z.inj_mod; reflexivity|lia|lia]. Qed.
Lemma validation_finish chars st :
 (if validation_result st (length chars) then Some (emitted (scan_bits st)) else None) =
 finish_scan chars st.
Proof.
 unfold validation_result,finish_scan.
 rewrite !nat_rem_native.
 rewrite (nat_leb_native 1 (length (emitted (scan_bits st))))
   (nat_leb_native (length (emitted (scan_bits st))) 128)
   (nat_leb_native 1 (scan_padding st)) (nat_leb_native (scan_padding st) 6).
 rewrite (nat_eqb_native (scan_symbols st mod 8) 1)
   (nat_eqb_native (scan_symbols st mod 8) 3) (nat_eqb_native (scan_symbols st mod 8) 6)
   (nat_eqb_native (scan_padding st) 0) (nat_eqb_native (length chars mod 8) 0) z_eqb_native.
 destruct (scan_valid st); cbn [andb]; [|reflexivity].
 destruct (scan_symbols st mod 8 =? 1)%nat;
 destruct (scan_symbols st mod 8 =? 3)%nat;
 destruct (scan_symbols st mod 8 =? 6)%nat;
 destruct (scan_padding st =? 0)%nat;
 destruct ((length chars mod 8 =? 0) && (1 <=? scan_padding st) && (scan_padding st <=? 6))%nat;
 destruct (((1 <=? length (emitted (scan_bits st))) &&
   (length (emitted (scan_bits st)) <=? 128))%nat);
 destruct (accumulator (scan_bits st) =? 0)%Z; reflexivity.
Qed.
Ltac b32_load := first [
 iApply (wp_stack_load with "Hv"); iIntros "!> _ Hv" |
 iApply (wp_stack_load with "Hp"); iIntros "!> _ Hp" |
 iApply (wp_stack_load with "Hs"); iIntros "!> _ Hs" |
 iApply (wp_stack_load with "Ha"); iIntros "!> _ Ha" |
 iApply (wp_stack_load with "Hb"); iIntros "!> _ Hb" |
 iApply (wp_stack_load with "Ho"); iIntros "!> _ Ho" ].
Ltac b32_assign := first [
 iApply (wp_stack_assign with "Hv"); iIntros "!> _ Hv" |
 iApply (wp_stack_assign with "Hp"); iIntros "!> _ Hp" |
 iApply (wp_stack_assign with "Hs"); iIntros "!> _ Hs" |
 iApply (wp_stack_assign with "Ha"); iIntros "!> _ Ha" |
 iApply (wp_stack_assign with "Hb"); iIntros "!> _ Hb" |
 iApply (wp_stack_assign with "Ho"); iIntros "!> _ Ho" ].
Ltac b32_admin :=
 iStartProof; repeat (simpl; cbn [fill fill_item];
 try (rewrite bool_decide_true; [|lia]);
 try (rewrite bool_decide_false; [|lia]);
 match goal with |- envs_entails _ (WP ?e {{_}}) =>
 hm_focus e ltac:(fun _ => first [b32_load | b32_assign |
 match goal with |- envs_entails _ (WP StackAssign (Val ?lv) ?rhs {{_}}) =>
   iApply (wp_bind [StackAssignRCtx lv]) end |
 match goal with
 | |- envs_entails _ (WP If (Val (LitV (LitBool true))) _ _ {{_}}) => iApply wp_if_true
 | |- envs_entails _ (WP If (Val (LitV (LitBool false))) _ _ {{_}}) => iApply wp_if_false
 end |
 match goal with
 | |- envs_entails _ (WP BinOp DivOp (Val (LitV (LitInt _))) (Val (LitV (LitInt ?d))) {{_}}) =>
   iApply wp_div; [lia|iIntros "!> _"]
 | |- envs_entails _ (WP BinOp RemOp (Val (LitV (LitInt _))) (Val (LitV (LitInt ?d))) {{_}}) =>
   iApply wp_rem; [lia|iIntros "!> _"]
 end | hm_head]) end);
 cbn [fill fill_item].
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition scan_cells valid padding symbols acc bits out st : iProp Σ :=
 StackId valid ↦ₛ LitV (LitBool (scan_valid st)) ∗
 StackId padding ↦ₛ LitV (LitInt (Z.of_nat (scan_padding st))) ∗
 StackId symbols ↦ₛ LitV (LitInt (Z.of_nat (scan_symbols st))) ∗
 StackId acc ↦ₛ LitV (LitInt (accumulator (scan_bits st))) ∗
 StackId bits ↦ₛ LitV (LitInt (bit_count (scan_bits st))) ∗
 StackId out ↦ₛ LitV (LitInt (Z.of_nat (length (emitted (scan_bits st))))).
Lemma factor_wp bits : 8 <= bits <= 12 ->
 ⊢ WP factor_e (int bits) {{u, ⌜u = LitV (LitInt (2^(bits-8)))⌝}}.
Proof.
 intros Hb. assert (Hcases : bits=8 \/ bits=9 \/ bits=10 \/ bits=11 \/ bits=12) by lia.
 destruct Hcases as [-> | [-> | [-> | [-> | ->]]]];
 unfold factor_e,eq,int,op; auth_pure; done.
Qed.
Lemma factor_stack_wp l width : 8 <= width <= 12 ->
 StackId l ↦ₛ LitV (LitInt width) -∗
 WP factor_e (stack_get l) {{u, ⌜u = LitV (LitInt (2^(width-8)))⌝ ∗ StackId l ↦ₛ LitV (LitInt width)}}.
Proof.
 intros Hbnd. iIntros "Hb".
 assert (Hcases : width=8 \/ width=9 \/ width=10 \/ width=11 \/ width=12) by lia.
 destruct Hcases as [-> | [-> | [-> | [-> | ->]]]];
 unfold factor_e,eq,int,op,stack_get,stack_e; b32_admin; iFrame; done.
Qed.
Theorem consume_digit_wp valid padding symbols acc bits out scratch st ch tail :
 (length (emitted (scan_bits st)) < 130)%nat ->
 (length (emitted (scan_bits st)) + length tail = 130)%nat ->
 0 <= bit_count (scan_bits st) < 8 ->
 0 <= accumulator (scan_bits st) < 2^(bit_count (scan_bits st)) ->
 (ch =? 61)%Z = false ->
 scan_cells valid padding symbols acc bits out st -∗
 array.array_cells scratch (emitted (scan_bits st) ++ tail) -∗
 WP consume_digit valid padding symbols acc bits out scratch
 (match base32.digit_value ch with Some d => d | None => -1 end)
 {{u, ⌜u = LitV LitUnit⌝ ∗ scan_cells valid padding symbols acc bits out (scan_step st ch) ∗
   ∃ tail', ⌜(length (emitted (scan_bits (scan_step st ch))) + length tail' = 130)%nat⌝ ∗
   array.array_cells scratch (emitted (scan_bits (scan_step st ch)) ++ tail')}}.
Proof.
 intros Hcap Hlength Hbits Hacc Hch. iIntros "Hstate Hscratch".
 iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
 unfold consume_digit,consume_digit_expr,range,both,le,eq,add,mul,sub,div,rem,op,int,
   stack_get,stack_e,seqs,lets,put,ptr,pv,v,unit_e,no. cbn [fold_right].
 destruct (base32.digit_value ch) as [digit|] eqn:Hdigit.
 - pose proof (base32.digit_value_range ch digit Hdigit) as Hrange.
   destruct (decide (scan_padding st = 0%nat)) as [Hz|Hz].
   + b32_admin.
     destruct (decide (8 <= bit_count (scan_bits st)+5)) as [Hwidth|Hwidth].
     * b32_admin.
       hm_take. iApply (wp_wand with "[Hb]").
       { iApply (factor_stack_wp with "Hb"). lia. }
       iIntros (u) "[%Hu Hb]". subst u. iApply wp_let. simpl.
       assert (Hfactor : 0 < 2^(bit_count (scan_bits st)+5-8)).
       { apply Z.pow_pos_nonneg; lia. }
       b32_admin.
       destruct tail as [|old tail]; [simpl in Hlength; lia|].
       assert (Hlookup : (emitted (scan_bits st) ++ old :: tail) !!
         length (emitted (scan_bits st)) = Some old).
       { rewrite lookup_app_r; [rewrite Nat.sub_diag; reflexivity|lia]. }
       iDestruct (big_sepL_insert_acc with "Hscratch") as "[Hcell Hclose]"; [exact Hlookup|].
       iApply (wp_store with "Hcell"). iIntros "!> _ Hcell".
       iDestruct ("Hclose" with "Hcell") as "Hscratch".
       b32_admin.
       unfold scan_cells,scan_step. rewrite Hch Hdigit Hz. simpl.
       unfold bit_step. cbn [emitted accumulator bit_count].
       assert (Hw : (bit_count (scan_bits st)+5 <? 8)%Z = false) by (apply Z.ltb_ge; lia).
       rewrite Hw. cbn [emitted accumulator bit_count].
       rewrite length_app Nat2Z.inj_add Nat2Z.inj_succ. simpl.
       iSplit; [done|]. iSplitL "Hv Hp Hs Ha Hb Ho"; [iFrame|].
       iExists tail. iSplit; [iPureIntro; simpl in Hlength; lia|].
       iEval (rewrite insert_app_r_alt; last lia; rewrite Nat.sub_diag; simpl) in "Hscratch".
       rewrite <- app_assoc. iExact "Hscratch".
     * b32_admin. unfold scan_cells,scan_step. rewrite Hch Hdigit Hz. simpl.
       unfold bit_step. cbn [emitted accumulator bit_count].
       assert (Hw : (bit_count (scan_bits st)+5 <? 8)%Z = true) by (apply Z.ltb_lt; lia).
       rewrite Hw. cbn [emitted accumulator bit_count]. rewrite Nat2Z.inj_succ.
       iSplit; [done|]. iSplitL "Hv Hp Hs Ha Hb Ho"; [iFrame|].
       iExists tail. iFrame. done.
   + b32_admin. unfold scan_cells,scan_step. rewrite Hch Hdigit.
     rewrite (proj2 (Nat.eqb_neq _ _) Hz). simpl.
     iSplit; [done|]. iSplitL "Hv Hp Hs Ha Hb Ho"; [iFrame|].
     iExists tail. iFrame. done.
 - b32_admin. unfold scan_cells,scan_step. rewrite Hch Hdigit. simpl.
   iSplit; [done|]. iSplitL "Hv Hp Hs Ha Hb Ho"; [iFrame|].
   iExists tail. iFrame. done.
Qed.
Theorem process_char_wp valid padding symbols acc bits out scratch st ch tail :
 (length (emitted (scan_bits st)) < 130)%nat ->
 (length (emitted (scan_bits st)) + length tail = 130)%nat ->
 0 <= bit_count (scan_bits st) < 8 ->
 0 <= accumulator (scan_bits st) < 2^(bit_count (scan_bits st)) ->
 scan_cells valid padding symbols acc bits out st -∗
 array.array_cells scratch (emitted (scan_bits st) ++ tail) -∗
 WP process_char valid padding symbols acc bits out scratch ch
 {{u, ⌜u = LitV LitUnit⌝ ∗ scan_cells valid padding symbols acc bits out (scan_step st ch) ∗
   ∃ tail', ⌜(length (emitted (scan_bits (scan_step st ch))) + length tail' = 130)%nat⌝ ∗
   array.array_cells scratch (emitted (scan_bits (scan_step st ch)) ++ tail')}}.
Proof.
 intros Hcap Hlength Hbits Hacc. iIntros "Hstate Hscratch".
 unfold process_char,process_char_expr. destruct (ch =? 61)%Z eqn:Hch.
 - apply Z.eqb_eq in Hch. subst ch.
   iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
   unfold eq,add,stack_get,stack_e,int,op. b32_admin.
   unfold scan_cells,scan_step. simpl. rewrite Nat2Z.inj_succ.
   iSplit; [done|]. iSplitL "Hv Hp Hs Ha Hb Ho"; [iFrame|].
   iExists tail. iFrame. done.
 - unfold eq,int,op. b32_admin.
   unfold lets. simpl. hm_take.
   iApply (wp_wand with "[]"). { iApply base32_value_wp. }
   iIntros (u) "%Hu". subst u. iApply wp_let.
   cbn [subst subst_val consume_digit_expr factor_e stack_e stack_get seqs fold_right
     put ptr pv range both le eq int op add mul sub div rem v unit_e no].
   fold (consume_digit valid padding symbols acc bits out scratch
     (match base32.digit_value ch with Some d => d | None => -1 end)).
   iApply (consume_digit_wp with "Hstate Hscratch"); auto.
Qed.
Theorem scan_loop_wp valid padding symbols acc bits out src scratch chars tail :
 (length chars <= 208)%nat -> length tail = 130%nat ->
 scan_cells valid padding symbols acc bits out initial_scan -∗
 array.array_cells src chars -∗ array.array_cells scratch tail -∗
 WP scan_loop valid padding symbols acc bits out src scratch (length chars)
 {{u, ⌜u = LitV LitUnit⌝ ∗ scan_cells valid padding symbols acc bits out (scan chars) ∗
   array.array_cells src chars ∗
   ∃ tail', ⌜(length (emitted (scan_bits (scan chars))) + length tail' = 130)%nat⌝ ∗
   array.array_cells scratch (emitted (scan_bits (scan chars)) ++ tail')}}.
Proof.
 intros Hlength Htail. iIntros "Hstate Hsrc Hscratch".
 unfold scan_loop.
 set (I := fun i : Z => (scan_cells valid padding symbols acc bits out (scan (take (Z.to_nat i) chars)) ∗
   array.array_cells src chars ∗
   ∃ tail', ⌜(length (emitted (scan_bits (scan (take (Z.to_nat i) chars)))) + length tail' = 130)%nat⌝ ∗
   array.array_cells scratch (emitted (scan_bits (scan (take (Z.to_nat i) chars))) ++ tail'))%I).
 iApply (wp_wand with "[Hstate Hsrc Hscratch]").
 { iApply (loop_wp "i" 0 (Z.of_nat (length chars))
   (lets [("ch",get (pv src) (v "i"))]
     (process_char_expr valid padding symbols acc bits out scratch (v "ch"))) I with "[Hstate Hsrc Hscratch]").
   - intros l i Hi. iIntros "Hl [Hstate [Hsrc Hscratch]]".
     iDestruct "Hscratch" as (rest) "[%Hrest Hscratch]".
     unfold lets,get,ptr,pv,v. cbn [subst_var subst_var_val].
     memory_admin.
     assert (Hki : Z.of_nat (Z.to_nat i) = i) by lia.
     assert (Hk : (Z.to_nat i < length chars)%nat) by lia.
     destruct (lookup_lt_is_Some_2 chars _ Hk) as [ch Hch].
     iDestruct (big_sepL_lookup_acc with "Hsrc") as "[Hcell Hclose]"; [exact Hch|].
     rewrite Hki. iApply (wp_load with "Hcell"). iIntros "!> _ Hcell".
     iDestruct ("Hclose" with "Hcell") as "Hsrc".
     iApply wp_let. cbn [subst subst_val].
     iApply (wp_wand with "[Hstate Hscratch]").
     { iApply (process_char_wp with "Hstate Hscratch").
       - apply scan_scratch_next. rewrite length_take. lia.
       - exact Hrest.
       - exact (proj1 (proj2 (scan_bounds (take (Z.to_nat i) chars)))).
       - exact (proj1 (proj2 (proj2 (scan_bounds (take (Z.to_nat i) chars))))).
     }
     iIntros (u) "[%Hu [Hstate Hscratch]]". subst u.
     iFrame "Hl Hsrc". unfold I. rewrite Z2Nat.inj_add; [|lia|lia].
     simpl. rewrite Nat.add_1_r (take_S_r chars _ ch Hch) scan_snoc.
     iFrame "Hstate Hscratch".
   - lia.
   - unfold I. simpl. iFrame "Hstate Hsrc". iExists tail. iFrame. done.
 }
 iIntros (u) "[%Hu H]". unfold I. rewrite Nat2Z.id take_ge; last lia.
 iDestruct "H" as "(Hstate & Hsrc & Hscratch)". iFrame. done.
Qed.
Theorem validation_wp valid padding symbols acc bits out st n :
 scan_cells valid padding symbols acc bits out st -∗
 WP validation_e valid padding symbols acc out n
 {{u, ⌜u = LitV (LitBool (validation_result st n))⌝ ∗
   scan_cells valid padding symbols acc bits out st}}.
Proof.
 iIntros "Hstate". iDestruct "Hstate" as "(Hv & Hp & Hs & Ha & Hb & Ho)".
 unfold validation_e,range,both,le,eq,rem,stack_get,stack_e,int,op,no,yes.
 destruct (decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 1));
 destruct (decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 3));
 destruct (decide (Z.rem (Z.of_nat (scan_symbols st)) 8 = 6));
 destruct (decide (Z.of_nat (scan_padding st) = 0));
 try lia; b32_admin; unfold validation_result,scan_cells;
 repeat (rewrite bool_decide_true; [|lia]);
 repeat (rewrite bool_decide_false; [|lia]);
 iFrame; iPureIntro; f_equal; f_equal; apply Bool.eq_true_iff_eq;
 repeat match goal with
 | Hknown : ?P |- context[bool_decide ?P] => rewrite (bool_decide_true P Hknown)
 | Hknown : ~ ?P |- context[bool_decide ?P] => rewrite (bool_decide_false P Hknown)
 end;
 repeat rewrite Bool.andb_true_iff;
 repeat rewrite bool_decide_eq_true; simpl; intuition lia.
Qed.
End proofs.
