(** Indexed buffer access and word-oriented key-expansion refinement. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import array hm_tactics.
From cjr.aes_ige Require Import bytes block aes program refinement.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Definition eptr p := Val (LitV (LitPtr p)).
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma cells_load_wp p xs i x : xs !! i = Some x ->
 array_cells p xs -∗
 WP Load (eptr (p+Z.of_nat i))
 {{v, ⌜v = LitV (LitInt x)⌝ ∗ array_cells p xs}}.
Proof.
 intros Hi. iIntros "H". unfold array_cells.
 iDestruct (big_sepL_lookup_acc _ _ i x Hi with "H") as "[Hx Hrestore]".
 iApply (wp_load with "Hx"). iIntros "!> _ Hx".
 iSplit; [done|]. iApply ("Hrestore" with "Hx").
Qed.
Lemma cells_store_wp p xs i old x : xs !! i = Some old ->
 array_cells p xs -∗
 WP Store (eptr (p+Z.of_nat i)) (int x)
 {{v, ⌜v = LitV LitUnit⌝ ∗ array_cells p (<[i:=x]>xs)}}.
Proof.
 intros Hi. iIntros "H". unfold array_cells.
 iDestruct (big_sepL_insert_acc _ _ i old Hi with "H") as "[Hx Hrestore]".
 iApply (wp_store with "Hx"). iIntros "!> _ Hx".
 iSplit; [done|]. iApply ("Hrestore" with "Hx").
Qed.
End proofs.
Close Scope string_scope.

Lemma mask_id x : byte x -> mask x = x.
Proof. intros H. unfold mask. change 255 with (Z.ones 8).
 rewrite Z.land_ones; [apply Z.mod_small; exact H|lia]. Qed.

Definition flatten_cols := flat_map col_list.
Lemma flatten_cols_app xs ys : flatten_cols (xs++ys) = flatten_cols xs ++ flatten_cols ys.
Proof. apply flat_map_app. Qed.
Lemma col_list_bytes c : column_bytes c -> Forall byte (col_list c).
Proof. destruct c; unfold column_bytes, col_list; simpl; intros H.
 repeat (constructor; [tauto|]); constructor. Qed.
Lemma read_col_flatten cs i : Forall column_bytes cs -> (i < length cs)%nat ->
 read_col (flatten_cols cs) (4*i) = nth i cs (Col 0 0 0 0).
Proof.
 revert i. induction cs as [|c cs IH]; intros i Hb Hi; [simpl in Hi; lia|].
 inversion Hb; subst. destruct i as [|i].
 - destruct c; unfold read_col, flatten_cols, col_list, column_bytes in *; simpl in *.
   f_equal; apply mask_id; tauto.
 - replace (4*S i)%nat with (4+4*i)%nat by lia.
   change (read_col (col_list c ++ flatten_cols cs) (4+4*i) = nth i cs (Col 0 0 0 0)).
   destruct c; unfold col_list, read_col at 1; simpl.
   change (read_col (flatten_cols cs) (4*i) = nth i cs (Col 0 0 0 0)).
   apply IH; [assumption|simpl in Hi; lia].
Qed.
Lemma map_nth_seq {A} (xs : list A) default :
 map (fun i => nth i xs default) (seq 0 (length xs)) = xs.
Proof.
 induction xs as [|x xs IH]; [reflexivity|].
 change (x :: map (fun i => nth i (x::xs) default) (seq 1 (length xs)) = x::xs).
 rewrite <- seq_shift. rewrite map_map. cbn [nth].
 rewrite IH. reflexivity.
Qed.
Lemma initial_words_flatten cs : Forall column_bytes cs ->
 map (fun i => read_col (flatten_cols cs) (4*i)) (seq 0 (length cs)) = cs.
Proof.
 intros Hb. rewrite <- (map_nth_seq cs (Col 0 0 0 0)) at 2.
 apply map_ext_in. intros i Hi. apply read_col_flatten; [exact Hb|].
 apply in_seq in Hi. lia.
Qed.
Lemma expanded_key_columns cs nk nr : Forall column_bytes cs ->
 length cs = nk ->
 (nk = 4 /\ nr = 10 \/ nk = 6 /\ nr = 12 \/ nk = 8 /\ nr = 14)%nat ->
 expanded_key (flatten_cols cs) = flatten_cols (expand_words (4*(nr+1)-nk) nk nk cs).
Proof.
 intros Hb Hlen Hsizes.
 assert (Hnk : nk_of_length (4*nk) = nk) by
   (destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; reflexivity).
 assert (Hnr : rounds_of_length (4*nk) = nr) by
   (destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; reflexivity).
 assert (Hnz : nk <> 0%nat) by (destruct Hsizes as [[-> _]|[[-> _]|[-> _]]]; lia).
 assert (Hinit : map (fun i => read_col (flatten_cols cs) (4*i)) (seq 0 nk) = cs).
 { rewrite <- Hlen. apply initial_words_flatten; exact Hb. }
 unfold expanded_key. change (length (flatten_cols cs)) with (length (flat_map col_list cs)).
 rewrite flatten_words_length Hlen Hnk Hnr (proj2 (Nat.eqb_neq nk 0) Hnz).
 change (flatten_cols (expand_words (4*(nr+1)-nk) nk nk
   (map (fun i => read_col (flatten_cols cs) (4*i)) (seq 0 nk))) =
   flatten_cols (expand_words (4*(nr+1)-nk) nk nk cs)).
 rewrite Hinit. reflexivity.
Qed.
Lemma word_div i r : (r < 4)%nat -> ((4*i+r)/4 = i)%nat.
Proof.
 intros H. replace (4*i+r)%nat with (r+i*4)%nat by lia.
 rewrite Nat.div_add; [|lia]. rewrite Nat.div_small; lia.
Qed.
Lemma word_mod i r : (r < 4)%nat -> ((4*i+r) mod 4 = r)%nat.
Proof.
 intros H. replace (4*i+r)%nat with (r+i*4)%nat by lia.
 rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia.
Qed.
Definition expansion_column nk i ws :=
 let previous := nth (i-1) ws (Col 0 0 0 0) in
 let t := if Nat.eqb (i mod nk) 0 then
   cxor (cmap sbox (rotate_word previous)) (Col (rcon (i/nk)) 0 0 0)
   else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool
   then cmap sbox previous else previous in
 cxor (nth (i-nk) ws (Col 0 0 0 0)) t.
Lemma expand_words_step fuel nk i ws :
 expand_words (S fuel) nk i ws =
 expand_words fuel nk (S i) (ws ++ [expansion_column nk i ws]).
Proof. reflexivity. Qed.
Lemma expansion_column_bytes nk i ws : Forall column_bytes ws ->
 column_bytes (expansion_column nk i ws).
Proof.
 intros H. unfold expansion_column. apply cxor_bytes; [apply nth_col_bytes; exact H|].
 destruct (Nat.eqb (i mod nk) 0).
 - apply cxor_bytes; [apply cmap_sbox_bytes, rotate_word_bytes, nth_col_bytes; exact H|].
   unfold column_bytes. simpl. split; [apply rcon_byte|]. unfold byte; lia.
 - destruct (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool;
   [apply cmap_sbox_bytes|]; apply nth_col_bytes; exact H.
Qed.

Definition col_at `{!cjrGS Σ} p (c : column) : iProp Σ :=
 RawId (p+0) ↦ᵣ LitV (LitInt (a0 c)) ∗
 RawId (p+1) ↦ᵣ LitV (LitInt (a1 c)) ∗
 RawId (p+2) ↦ᵣ LitV (LitInt (a2 c)) ∗
 RawId (p+3) ↦ᵣ LitV (LitInt (a3 c)).
Definition words_at `{!cjrGS Σ} p cs : iProp Σ :=
 [∗ list] i ↦ c ∈ cs, col_at (p+4*Z.of_nat i) c.
Definition expansion_word_term base previous target nk i :=
 let transform r :=
   let x := get (eptr previous) (Z.of_nat r) in
   if Nat.eqb (i mod nk) 0 then
     xb (sb (get (eptr previous) (Z.of_nat ((r+1) mod 4))))
       (int (if Nat.eqb r 0 then rcon (i/nk) else 0))
   else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool then sb x else x in
 seqs (map (fun r => put (eptr target) (Z.of_nat r)
   (xb (get (eptr base) (Z.of_nat r)) (transform r))) (seq 0 4)) unit_e.
Open Scope string_scope.
Section word_proof.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Opaque sbox_body inv_sbox_body xtime_body.
Lemma exp_sbox_app_wp x : byte x ->
 ⊢ WP App (Val (RecV None (Some "x") sbox_body)) (int x)
 {{v, ⌜v = LitV (LitInt (sbox x))⌝}}.
Proof. intros H. iApply wp_app. rewrite <- (sbox_table_value x H). iApply groups_wp. Qed.
End word_proof.
Ltac exp_head := first [
 match goal with
 | |- envs_entails _ (WP App (Val (RecV None (Some "x") sbox_body)) (Val (LitV (LitInt ?x))) {{_}}) =>
   iApply (wp_wand with "[]"); [iApply exp_sbox_app_wp; tauto|iIntros (?) "%E"; subst]
 | |- envs_entails _ (WP Load (Val (LitV (LitPtr ?p))) {{_}}) =>
   iApply (wp_load p with "[$]"); iIntros "!> _ ?"
 | |- envs_entails _ (WP Store (Val (LitV (LitPtr ?p))) (Val ?v) {{_}}) =>
   iApply (wp_store p with "[$]"); iIntros "!> _ ?"
 end | hm_head ].
Ltac exp_run := iStartProof; repeat (simpl; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => exp_head) end);
 cbn [fill fill_item]; simpl.
Section word_proof.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma expansion_word_wp base previous target nk i left prev old :
 column_bytes left -> column_bytes prev ->
 col_at base left -∗ col_at previous prev -∗ col_at target old -∗
 WP expansion_word_term base previous target nk i
 {{v, ⌜v = LitV LitUnit⌝ ∗ col_at base left ∗ col_at previous prev ∗
 col_at target (cxor left
   (if Nat.eqb (i mod nk) 0 then cxor (cmap sbox (rotate_word prev)) (Col (rcon (i/nk)) 0 0 0)
    else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool then cmap sbox prev else prev))}}.
Proof.
 intros Hl Hp. destruct left, prev, old. unfold column_bytes in *; simpl in *.
 iIntros "Hl Hp Ho".
 iEval (unfold col_at; simpl) in "Hl".
 iEval (unfold col_at; simpl) in "Hp".
 iEval (unfold col_at; simpl) in "Ho".
 iDestruct "Hl" as "(? & ? & ? & ?)".
 iDestruct "Hp" as "(? & ? & ? & ?)".
 iDestruct "Ho" as "(? & ? & ? & ?)".
 unfold expansion_word_term.
 destruct (Nat.eqb (i mod nk) 0) eqn:Hfirst;
 [|destruct (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool eqn:Hsecond];
 unfold seqs, put, get, ptr, int, unit_e, xb, sb, call1, eptr.
 all: (exp_run; iSplit; [done|]; unfold col_at, cxor, cmap, rotate_word; simpl;
 rewrite ?Z.lxor_0_r ?bx_zero; iFrame).
Qed.
End word_proof.

Section indexed_words.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma words_three_wp p cs a b t ca cb ct new e (Ψ : val_cjr -> iProp Σ) :
 cs !! a = Some ca -> cs !! b = Some cb -> cs !! t = Some ct ->
 a <> b -> a <> t -> b <> t ->
 (col_at (p+4*Z.of_nat a) ca -∗ col_at (p+4*Z.of_nat b) cb -∗
  col_at (p+4*Z.of_nat t) ct -∗ WP e
  {{v, col_at (p+4*Z.of_nat a) ca ∗ col_at (p+4*Z.of_nat b) cb ∗
       col_at (p+4*Z.of_nat t) new ∗ Ψ v}}) -∗
 words_at p cs -∗ WP e {{v, words_at p (<[t:=new]>cs) ∗ Ψ v}}.
Proof.
 intros Ha Hb Ht Hab Hat Hbt. iIntros "Hcall Hmem".
 unfold words_at.
 set (F := fun j c => col_at (p+4*Z.of_nat j) c).
 set (FA := fun j c => if decide (j=a) then emp%I else F j c).
 set (FAB := fun j c => if decide (j=b) then emp%I else FA j c).
 iDestruct (big_sepL_delete F cs a ca Ha with "Hmem") as "[HA Hmem]".
 iDestruct (big_sepL_delete FA cs b cb Hb with "Hmem") as "[HB Hmem]".
 iEval (unfold FA; rewrite decide_False; [|congruence]) in "HB".
 iDestruct (big_sepL_insert_acc FAB cs t ct Ht with "Hmem") as "[HT Hrestore]".
 iEval (unfold FAB, FA; rewrite !decide_False; try congruence) in "HT".
 iApply (wp_wand with "[HA HB HT Hcall]").
 { iApply ("Hcall" with "HA HB HT"). }
 iIntros (v) "(HA & HB & HT & HΨ)". iFrame "HΨ".
 assert (Ha' : (<[t:=new]>cs) !! a = Some ca) by (rewrite list_lookup_insert_ne; congruence).
 assert (Hb' : (<[t:=new]>cs) !! b = Some cb) by (rewrite list_lookup_insert_ne; congruence).
 rewrite (big_sepL_delete F (<[t:=new]>cs) a ca Ha'). iFrame "HA".
 rewrite (big_sepL_delete FA (<[t:=new]>cs) b cb Hb').
 iSplitL "HB".
 { unfold FA. rewrite decide_False; [iExact "HB"|congruence]. }
 iApply ("Hrestore" $! new).
 unfold FAB, FA. rewrite !decide_False; try congruence. iExact "HT".
Qed.
End indexed_words.
Close Scope string_scope.
Definition expansion_byte_normal (nk i r : nat) :=
 let previous r := get (Var "schedule") (Z.of_nat (4*(i-1)+r)) in
 let t := if Nat.eqb (i mod nk) 0 then
   xb (sb (previous ((r+1) mod 4)%nat))
      (int (if Nat.eqb r 0 then rcon (i/nk) else 0))
   else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool then sb (previous r)
   else previous r in
 put (Var "schedule") (Z.of_nat (4*i+r))
   (xb (get (Var "schedule") (Z.of_nat (4*(i-nk)+r))) t).
Lemma expansion_byte_index nk i r : (0 < nk <= i)%nat -> (r < 4)%nat ->
 expansion_byte nk (4*i+r) = expansion_byte_normal nk i r.
Proof.
 intros Hnk Hr. unfold expansion_byte, expansion_byte_normal.
 rewrite (word_div i r Hr) (word_mod i r Hr).
 replace (4*i+r-r-4+(r+1) mod 4)%nat with (4*(i-1)+(r+1) mod 4)%nat by lia.
 replace (4*i+r-4)%nat with (4*(i-1)+r)%nat by lia.
 replace (4*i+r-4*nk)%nat with (4*(i-nk)+r)%nat by lia.
 reflexivity.
Qed.
Lemma seq_word i : seq (4*i) 4 = [(4*i+0)%nat; (4*i+1)%nat; (4*i+2)%nat; (4*i+3)%nat].
Proof. cbn [seq]. repeat f_equal; lia. Qed.
Lemma expansion_word_indices nk i : (0 < nk <= i)%nat ->
 map (expansion_byte nk) (seq (4*i) 4) =
 map (expansion_byte_normal nk i) (seq 0 4).
Proof.
 intros H. rewrite seq_word. cbn [map seq].
 rewrite (expansion_byte_index nk i 0 H ltac:(lia))
         (expansion_byte_index nk i 1 H ltac:(lia))
         (expansion_byte_index nk i 2 H ltac:(lia))
         (expansion_byte_index nk i 3 H ltac:(lia)). reflexivity.
Qed.

Local Transparent sbox_body.
Lemma sbox_schedule_closed v : subst "schedule" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
Opaque sbox_body.
#[local] Hint Rewrite sbox_schedule_closed : exp_subst.
Open Scope string_scope.
Ltac exp_address_head := first [
 match goal with
 | |- envs_entails _ (WP Load (Val (LitV (LitPtr ?p))) {{_}}) =>
   iMatchHyp ltac:(fun H P => lazymatch P with raw_mapsto (RawId ?q) ?v =>
     let E := fresh "Eaddr" in assert (E : p=q) by lia; rewrite E;
     iApply (wp_load q with "[$]"); iIntros "!> _ ?" end)
 | |- envs_entails _ (WP Store (Val (LitV (LitPtr ?p))) (Val ?v) {{_}}) =>
   iMatchHyp ltac:(fun H P => lazymatch P with raw_mapsto (RawId ?q) ?old =>
     let E := fresh "Eaddr" in assert (E : p=q) by lia; rewrite E;
     iApply (wp_store q with "[$]"); iIntros "!> _ ?" end)
 end | exp_head ].
Ltac exp_cont_run := iStartProof; repeat (simpl; repeat match goal with |- context[subst "schedule" ?v sbox_body] => rewrite (sbox_schedule_closed v) end;
 rewrite ?Nat2Z.inj_add ?Nat2Z.inj_mul; cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => exp_address_head) end);
 cbn [fill fill_item]; simpl.
Section continuation_word.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma expansion_word_cont_wp p nk i left prev old tail (Φ : val_cjr -> iProp Σ) :
 (0 < nk <= i)%nat -> column_bytes left -> column_bytes prev ->
 (col_at (p+4*Z.of_nat (i-nk)) left ∗ col_at (p+4*Z.of_nat (i-1)) prev ∗
  col_at (p+4*Z.of_nat i)
   (cxor left (if Nat.eqb (i mod nk) 0 then
      cxor (cmap sbox (rotate_word prev)) (Col (rcon (i/nk)) 0 0 0)
    else if (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool then cmap sbox prev else prev))
  -∗ WP subst "schedule" (LitV (LitPtr p)) tail {{Φ}}) -∗
 col_at (p+4*Z.of_nat (i-nk)) left -∗ col_at (p+4*Z.of_nat (i-1)) prev -∗
 col_at (p+4*Z.of_nat i) old -∗
 WP subst "schedule" (LitV (LitPtr p))
    (seqs (map (expansion_byte nk) (seq (4*i) 4)) tail) {{Φ}}.
Proof.
 intros Hni Hl Hp. rewrite (expansion_word_indices nk i Hni).
 destruct left, prev, old. unfold column_bytes in *; simpl in *.
 iIntros "Htail Hl Hp Ho".
 iEval (unfold col_at; simpl) in "Hl".
 iEval (unfold col_at; simpl) in "Hp".
 iEval (unfold col_at; simpl) in "Ho".
 iDestruct "Hl" as "(? & ? & ? & ?)".
 iDestruct "Hp" as "(? & ? & ? & ?)".
 iDestruct "Ho" as "(? & ? & ? & ?)".
 unfold seqs, expansion_byte_normal.
 destruct (Nat.eqb (i mod nk) 0) eqn:Hfirst;
 [|destruct (Nat.eqb nk 8 && Nat.eqb (i mod nk) 4)%bool eqn:Hsecond];
 unfold put, get, ptr, int, unit_e, xb, sb, call1.
 all: (exp_cont_run; iApply "Htail"; unfold col_at, cxor, cmap, rotate_word;
 simpl; rewrite ?Z.lxor_0_r ?bx_zero; iFrame).
Qed.
End continuation_word.
Section word_accessors.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma words_three_acc p cs a b t ca cb ct :
 cs !! a = Some ca -> cs !! b = Some cb -> cs !! t = Some ct ->
 a <> b -> a <> t -> b <> t ->
 words_at p cs -∗
 col_at (p+4*Z.of_nat a) ca ∗ col_at (p+4*Z.of_nat b) cb ∗ col_at (p+4*Z.of_nat t) ct ∗
 (∀ new, col_at (p+4*Z.of_nat a) ca -∗ col_at (p+4*Z.of_nat b) cb -∗
          col_at (p+4*Z.of_nat t) new -∗ words_at p (<[t:=new]>cs)).
Proof.
 intros Ha Hb Ht Hab Hat Hbt. iIntros "Hmem". unfold words_at.
 set (F := fun j c => col_at (p+4*Z.of_nat j) c).
 set (FA := fun j c => if decide (j=a) then emp%I else F j c).
 set (FAB := fun j c => if decide (j=b) then emp%I else FA j c).
 iDestruct (big_sepL_delete F cs a ca Ha with "Hmem") as "[HA Hmem]".
 iDestruct (big_sepL_delete FA cs b cb Hb with "Hmem") as "[HB Hmem]".
 iEval (unfold FA; rewrite decide_False; [|congruence]) in "HB".
 iDestruct (big_sepL_insert_acc FAB cs t ct Ht with "Hmem") as "[HT Hrestore]".
 iEval (unfold FAB, FA; rewrite !decide_False; try congruence) in "HT".
 iFrame "HA HB HT". iIntros (new) "HA HB HT".
 assert (Ha' : (<[t:=new]>cs) !! a = Some ca) by (rewrite list_lookup_insert_ne; congruence).
 assert (Hb' : (<[t:=new]>cs) !! b = Some cb) by (rewrite list_lookup_insert_ne; congruence).
 rewrite (big_sepL_delete F (<[t:=new]>cs) a ca Ha'). iFrame "HA".
 rewrite (big_sepL_delete FA (<[t:=new]>cs) b cb Hb').
 iSplitL "HB".
 { unfold FA. rewrite decide_False; [iExact "HB"|congruence]. }
 iApply ("Hrestore" $! new).
 unfold FAB, FA. rewrite !decide_False; try congruence. iExact "HT".
Qed.
End word_accessors.
Close Scope string_scope.
Lemma seqs_app xs ys last : seqs (xs++ys) last = seqs xs (seqs ys last).
Proof. unfold seqs. rewrite fold_right_app. reflexivity. Qed.
Lemma prefix_insert {A} (xs : list A) y ys :
 <[length xs:=y]>(xs++ys) = (xs ++ <[0%nat:=y]>ys)%list.
Proof. rewrite insert_app_r_alt; [|lia]. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma nth_lookup_default {A} (xs : list A) i default :
 (i < length xs)%nat -> xs !! i = Some (nth i xs default).
Proof.
 revert i. induction xs as [|x xs IH]; intros i H; [simpl in H; lia|].
 destruct i; [reflexivity|]. apply IH. simpl in H; lia.
Qed.
Open Scope string_scope.
Section expansion_loop.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma expansion_loop_wp p nk fuel i ws old tail (Φ : val_cjr -> iProp Σ) :
 (2 <= nk <= i)%nat -> length ws = i -> Forall column_bytes ws ->
 (fuel <= length old)%nat ->
 (words_at p (expand_words fuel nk i ws ++ skipn fuel old) -∗
  WP subst "schedule" (LitV (LitPtr p)) tail {{Φ}}) -∗
 words_at p (ws ++ old) -∗
 WP subst "schedule" (LitV (LitPtr p))
    (seqs (map (expansion_byte nk) (seq (4*i) (4*fuel))) tail) {{Φ}}.
Proof.
 revert nk i ws old tail Φ. induction fuel as [|fuel IH]; intros nk i ws old tail Φ Hni Hlen Hb Hcap.
 - simpl. iIntros "Htail Hmem". iApply ("Htail" with "Hmem").
 - destruct old as [|ct rest]; [simpl in Hcap; lia|].
   set (ca := nth (i-nk) ws (Col 0 0 0 0)).
   set (cb := nth (i-1) ws (Col 0 0 0 0)).
   set (new := expansion_column nk i ws).
   assert (Ha : (ws ++ ct::rest)%list !! (i-nk)%nat = Some ca).
   { rewrite lookup_app_l; [apply nth_lookup_default; lia|lia]. }
   assert (Hb' : (ws ++ ct::rest)%list !! (i-1)%nat = Some cb).
   { rewrite lookup_app_l; [apply nth_lookup_default; lia|lia]. }
   assert (Ht : (ws ++ ct::rest)%list !! i = Some ct).
   { rewrite lookup_app_r; [rewrite Hlen Nat.sub_diag; reflexivity|lia]. }
   assert (Hca : column_bytes ca) by (apply nth_col_bytes; exact Hb).
   assert (Hcb : column_bytes cb) by (apply nth_col_bytes; exact Hb).
   assert (Hnew : column_bytes new) by (apply expansion_column_bytes; exact Hb).
   iIntros "Htail Hmem".
   iDestruct (words_three_acc p _ (i-nk) (i-1) i ca cb ct Ha Hb' Ht
     ltac:(lia) ltac:(lia) ltac:(lia) with "Hmem") as "(HA & HB & HT & Hrestore)".
   replace (4*S fuel)%nat with (4+4*fuel)%nat by lia.
   rewrite seq_app map_app seqs_app.
   replace (4*i+4)%nat with (4*S i)%nat by lia.
   iApply (expansion_word_cont_wp p nk i ca cb ct _ Φ ltac:(lia) Hca Hcb with "[Htail Hrestore] HA HB HT").
   iIntros "(HA & HB & HT)".
   iPoseProof ("Hrestore" $! new with "HA HB HT") as "Hnext".
   iEval (rewrite <- Hlen; rewrite prefix_insert; simpl) in "Hnext".
   iEval (rewrite (app_assoc ws [new] rest)) in "Hnext".
   iApply (IH nk (S i) (ws++[new])%list rest tail Φ with "[Htail] Hnext").
   + lia.
   + rewrite length_app. simpl. lia.
   + apply Forall_app. split; [exact Hb|constructor; [exact Hnew|constructor]].
   + simpl in Hcap. lia.
   + iEval (rewrite expand_words_step; cbn [skipn]) in "Htail". iExact "Htail".
Qed.
End expansion_loop.
Open Scope string_scope.
Section copy_words.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma copy_word_acc p q keys cs i key old :
 keys !! i = Some key -> cs !! i = Some old ->
 words_at p keys -∗ words_at q cs -∗
 col_at (p+4*Z.of_nat i) key ∗ col_at (q+4*Z.of_nat i) old ∗
 (∀ new, col_at (p+4*Z.of_nat i) key -∗ col_at (q+4*Z.of_nat i) new -∗
          words_at p keys ∗ words_at q (<[i:=new]>cs)).
Proof.
 intros Hkey Hold. iIntros "Hkey Hold". unfold words_at.
 iDestruct (big_sepL_lookup_acc _ _ i key Hkey with "Hkey") as "[HK HKrestore]".
 iDestruct (big_sepL_insert_acc _ _ i old Hold with "Hold") as "[HO HOrestore]".
 iFrame "HK HO". iIntros (new) "HK HO".
 iSplitL "HK HKrestore"; [iApply ("HKrestore" with "HK")|iApply ("HOrestore" $! new with "HO")].
Qed.
Definition key_copy_byte j := put (Var "schedule") (Z.of_nat j) (get (Var "key") (Z.of_nat j)).
Lemma copy_word_cont_wp p q i c old tail (Φ : val_cjr -> iProp Σ) :
 (col_at (p+4*Z.of_nat i) c ∗ col_at (q+4*Z.of_nat i) c -∗
  WP subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) tail) {{Φ}}) -∗
 col_at (p+4*Z.of_nat i) c -∗ col_at (q+4*Z.of_nat i) old -∗
 WP subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q))
    (seqs (map key_copy_byte (seq (4*i) 4)) tail)) {{Φ}}.
Proof.
 destruct c, old. iIntros "Htail Hkey Hold".
 iEval (unfold col_at; simpl) in "Hkey". iEval (unfold col_at; simpl) in "Hold".
 iDestruct "Hkey" as "(? & ? & ? & ?)". iDestruct "Hold" as "(? & ? & ? & ?)".
 rewrite seq_word. unfold seqs, key_copy_byte, put, get, ptr, int.
 exp_cont_run. iApply "Htail". unfold col_at; simpl. iFrame.
Qed.
Lemma copy_key_loop_wp p q keys fuel i old tail (Φ : val_cjr -> iProp Σ) :
 (i+fuel <= length keys)%nat -> (fuel <= length old)%nat ->
 (words_at p keys ∗ words_at q (firstn (i+fuel) keys ++ skipn fuel old) -∗
  WP subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) tail) {{Φ}}) -∗
 words_at p keys -∗ words_at q (firstn i keys ++ old) -∗
 WP subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q))
    (seqs (map key_copy_byte (seq (4*i) (4*fuel))) tail)) {{Φ}}.
Proof.
 revert i old tail Φ. induction fuel as [|fuel IH]; intros i old tail Φ Hkeycap Hcap.
 - replace (i+0)%nat with i by lia. simpl. iIntros "Htail Hkey Hold".
   iApply ("Htail" with "[$]").
 - destruct old as [|ct rest]; [simpl in Hcap; lia|].
   set (key := nth i keys (Col 0 0 0 0)).
   assert (Hkey : keys !! i = Some key) by (apply nth_lookup_default; lia).
   assert (Hprefix : length (firstn i keys) = i) by (rewrite length_firstn; lia).
   assert (Hold : (firstn i keys ++ ct::rest)%list !! i = Some ct).
   { rewrite lookup_app_r; [rewrite Hprefix Nat.sub_diag; reflexivity|lia]. }
   iIntros "Htail Hkey Hold".
   iDestruct (copy_word_acc p q keys _ i key ct Hkey Hold with "Hkey Hold") as "(HK & HO & Hrestore)".
   replace (4*S fuel)%nat with (4+4*fuel)%nat by lia.
   rewrite seq_app map_app seqs_app.
   replace (4*i+4)%nat with (4*S i)%nat by lia.
   iApply (copy_word_cont_wp p q i key ct _ Φ with "[Htail Hrestore] HK HO").
   iIntros "[HK HO]". iDestruct ("Hrestore" $! key with "HK HO") as "[Hkey Hnext]".
   iEval (rewrite insert_app_r_alt; [rewrite Hprefix Nat.sub_diag; simpl|rewrite Hprefix; lia]) in "Hnext".
   iEval (rewrite (app_assoc (firstn i keys) [key] rest)) in "Hnext".
   iEval (rewrite <- (take_S_r keys i key Hkey)) in "Hnext".
   iApply (IH (S i) rest tail Φ with "[Htail] Hkey Hnext").
   + lia.
   + simpl in Hcap; lia.
   + replace (S i+fuel)%nat with (i+S fuel)%nat by lia. simpl. iExact "Htail".
Qed.
End copy_words.
Local Transparent sbox_body.
Lemma sbox_key_closed v : subst "key" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
Opaque sbox_body.
Lemma expansion_byte_no_key v nk j : subst "key" v (expansion_byte nk j) = expansion_byte nk j.
Proof.
 unfold expansion_byte. destruct (Nat.eqb ((j/4) mod nk) 0);
 [|destruct (Nat.eqb nk 8 && Nat.eqb ((j/4) mod nk) 4)%bool];
 unfold put, get, ptr, xb, sb, call1, int; simpl; rewrite ?sbox_key_closed; reflexivity.
Qed.
Lemma expansion_byte_no_key_schedule p q nk j :
 subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) (expansion_byte nk j)) =
 subst "schedule" (LitV (LitPtr q)) (expansion_byte nk j).
Proof.
 unfold expansion_byte. destruct (Nat.eqb ((j/4) mod nk) 0);
 [|destruct (Nat.eqb nk 8 && Nat.eqb ((j/4) mod nk) 4)%bool];
 unfold put, get, ptr, xb, sb, call1, int; simpl;
 rewrite ?sbox_schedule_closed ?sbox_key_closed; reflexivity.
Qed.
Lemma expansion_tail_no_key_schedule p q nk indices nr :
 subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q))
   (seqs (map (expansion_byte nk) indices) (int nr))) =
 subst "schedule" (LitV (LitPtr q)) (seqs (map (expansion_byte nk) indices) (int nr)).
Proof.
 induction indices; [reflexivity|]. cbn [map seqs fold_right subst].
 rewrite expansion_byte_no_key_schedule IHindices. reflexivity.
Qed.
Lemma expansion_tail_no_key v nk indices nr :
 subst "key" v (seqs (map (expansion_byte nk) indices) (int nr)) =
 seqs (map (expansion_byte nk) indices) (int nr).
Proof.
 induction indices; [reflexivity|]. cbn [map seqs fold_right subst].
 rewrite expansion_byte_no_key IHindices. reflexivity.
Qed.
Close Scope string_scope.
Lemma valid_key_cols cs : Forall column_bytes cs ->
 (length cs = 4 \/ length cs = 6 \/ length cs = 8)%nat -> valid_key (flatten_cols cs).
Proof.
 intros Hbytes Hlen. split.
 - unfold flatten_cols. rewrite flatten_words_length. destruct Hlen as [Hlen|[Hlen|Hlen]]; rewrite Hlen; auto.
 - apply flatten_words_bytes; exact Hbytes.
Qed.
Open Scope string_scope.
Section complete_expansion.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Lemma expand_branch_wp p q keys old nk nr :
 (nk = 4 /\ nr = 10 \/ nk = 6 /\ nr = 12 \/ nk = 8 /\ nr = 14)%nat ->
 length keys = nk -> Forall column_bytes keys -> length old = 60%nat ->
 words_at p keys -∗ words_at q old -∗
 WP subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) (expand_branch nk nr))
 {{v, ⌜v = LitV (LitInt (Z.of_nat nr))⌝ ∗ words_at p keys ∗
 words_at q (expand_words (4*(nr+1)-nk) nk nk keys ++ skipn (4*(nr+1)) old)}}.
Proof.
 intros Hsizes Hlen Hbytes Hold.
 assert (Hnk : (2 <= nk)%nat) by (destruct Hsizes as [[-> _]|[[-> _]|[-> _]]]; lia).
 assert (Hcap : (4*(nr+1) <= 60)%nat) by (destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
 unfold expand_branch.
 rewrite seqs_app.
 iIntros "Hkey Hmem".
 iApply (copy_key_loop_wp p q keys nk 0 old _ _ with "[] Hkey Hmem"); [lia|lia|].
 iIntros "[Hkey Hmem]".
 rewrite Nat.add_0_l. iEval (rewrite <- Hlen; rewrite firstn_all; rewrite Hlen) in "Hmem".
 rewrite expansion_tail_no_key_schedule.
 replace (16*(nr+1)-4*nk)%nat with (4*(4*(nr+1)-nk))%nat by lia.
 iApply (expansion_loop_wp q nk (4*(nr+1)-nk) nk keys (skipn nk old) (int (Z.of_nat nr)) _ with "[Hkey] Hmem").
 - lia.
 - exact Hlen.
 - exact Hbytes.
 - rewrite length_skipn. lia.
 - iIntros "Hmem". simpl. iApply wp_value'. iSplit; [done|]. iFrame "Hkey".
   iEval (rewrite skipn_skipn) in "Hmem".
   assert (Hdrop : (4*(nr+1)-nk+nk = 4*(nr+1))%nat) by lia.
   iEval (rewrite Hdrop) in "Hmem". iExact "Hmem".
Qed.
End complete_expansion.
Local Transparent sbox_body.
Lemma sbox_keylen_closed v : subst "keyLen" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
Opaque sbox_body.
Lemma key_copy_byte_swap p q j :
 subst "schedule" (LitV (LitPtr q)) (subst "key" (LitV (LitPtr p)) (key_copy_byte j)) =
 subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) (key_copy_byte j)).
Proof. reflexivity. Qed.
Lemma key_copy_byte_keylen v j : subst "keyLen" v (key_copy_byte j) = key_copy_byte j.
Proof. reflexivity. Qed.
Lemma expansion_byte_keylen v nk j : subst "keyLen" v (expansion_byte nk j) = expansion_byte nk j.
Proof.
 unfold expansion_byte. destruct (Nat.eqb ((j/4) mod nk) 0);
 [|destruct (Nat.eqb nk 8 && Nat.eqb ((j/4) mod nk) 4)%bool];
 unfold put, get, ptr, xb, sb, call1, int; simpl; rewrite ?sbox_keylen_closed; reflexivity.
Qed.
Lemma expansion_byte_swap p q nk j :
 subst "schedule" (LitV (LitPtr q)) (subst "key" (LitV (LitPtr p)) (expansion_byte nk j)) =
 subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) (expansion_byte nk j)).
Proof. rewrite expansion_byte_no_key expansion_byte_no_key_schedule. reflexivity. Qed.
Close Scope string_scope.
Lemma seqs_closed x v es last :
 (forall e, In e es -> subst x v e = e) -> subst x v last = last ->
 subst x v (seqs es last) = seqs es last.
Proof.
 intros H Hl. induction es as [|e es IH]; [exact Hl|].
 cbn [seqs fold_right subst]. rewrite H; [|simpl; auto].
 rewrite IH; [reflexivity|intros; apply H; simpl; auto].
Qed.
Lemma seqs_swap x y v w es last :
 (forall e, In e es -> subst x v (subst y w e) = subst y w (subst x v e)) ->
 subst x v (subst y w last) = subst y w (subst x v last) ->
 subst x v (subst y w (seqs es last)) = subst y w (subst x v (seqs es last)).
Proof.
 intros H Hl. induction es as [|e es IH]; [exact Hl|].
 cbn [seqs fold_right subst]. rewrite H; [|simpl; auto].
 rewrite IH; [reflexivity|intros; apply H; simpl; auto].
Qed.
Open Scope string_scope.
Lemma expand_branch_keylen v nk nr : subst "keyLen" v (expand_branch nk nr) = expand_branch nk nr.
Proof.
 unfold expand_branch. apply seqs_closed; [|reflexivity].
 intros e He. apply in_app_iff in He. destruct He as [He|He]; apply in_map_iff in He;
 destruct He as [j [<- Hj]]; [apply key_copy_byte_keylen|apply expansion_byte_keylen].
Qed.
Lemma expand_branch_swap p q nk nr :
 subst "schedule" (LitV (LitPtr q)) (subst "key" (LitV (LitPtr p)) (expand_branch nk nr)) =
 subst "key" (LitV (LitPtr p)) (subst "schedule" (LitV (LitPtr q)) (expand_branch nk nr)).
Proof.
 unfold expand_branch. apply seqs_swap; [|reflexivity].
 intros e He. apply in_app_iff in He. destruct He as [He|He]; apply in_map_iff in He;
 destruct He as [j [<- Hj]]; [apply key_copy_byte_swap|apply expansion_byte_swap].
Qed.
Local Transparent sbox_body.
Lemma exp_sbox_args_closed v : subst "args" v sbox_body = sbox_body.
Proof. reflexivity. Qed.
Opaque sbox_body.
Lemma expansion_byte_args v nk j : subst "args" v (expansion_byte nk j) = expansion_byte nk j.
Proof.
 unfold expansion_byte. destruct (Nat.eqb ((j/4) mod nk) 0);
 [|destruct (Nat.eqb nk 8 && Nat.eqb ((j/4) mod nk) 4)%bool];
 unfold put, get, ptr, xb, sb, call1, int; simpl; rewrite ?exp_sbox_args_closed; reflexivity.
Qed.
Lemma expand_branch_args v nk nr : subst "args" v (expand_branch nk nr) = expand_branch nk nr.
Proof.
 unfold expand_branch. apply seqs_closed; [|reflexivity].
 intros e He. apply in_app_iff in He. destruct He as [He|He]; apply in_map_iff in He;
 destruct He as [j [<- Hj]]; [reflexivity|apply expansion_byte_args].
Qed.
Lemma seqs_closed_subst x y v w es last :
 (forall e, In e es -> subst x v (subst y w e) = subst y w e) ->
 subst x v (subst y w last) = subst y w last ->
 subst x v (subst y w (seqs es last)) = subst y w (seqs es last).
Proof.
 intros H Hl. induction es as [|e es IH]; [exact Hl|].
 cbn [seqs fold_right subst]. rewrite H; [|simpl; auto].
 rewrite IH; [reflexivity|intros; apply H; simpl; auto].
Qed.
Lemma expand_branch_keylen_key v p nk nr :
 subst "keyLen" v (subst "key" (LitV (LitPtr p)) (expand_branch nk nr)) =
 subst "key" (LitV (LitPtr p)) (expand_branch nk nr).
Proof.
 unfold expand_branch. apply seqs_closed_subst; [|reflexivity].
 intros e He. apply in_app_iff in He. destruct He as [He|He]; apply in_map_iff in He;
 destruct He as [j [<- Hj]].
 - reflexivity.
 - rewrite expansion_byte_no_key expansion_byte_keylen. reflexivity.
Qed.
Opaque expand_branch.
Local Opaque expand_words expansion_column words_at.
Ltac expand_admin := iStartProof; repeat (simpl;
 repeat match goal with |- context[subst "keyLen" ?v (expand_branch ?nk ?nr)] => rewrite (expand_branch_keylen v nk nr) end;
 cbn [fill fill_item];
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => first [iApply wp_if_true|iApply wp_if_false|hm_head]) end);
 cbn [fill fill_item]; simpl.
Section public_expansion.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem expand_key_wp p q keys old nk nr :
 (nk = 4 /\ nr = 10 \/ nk = 6 /\ nr = 12 \/ nk = 8 /\ nr = 14)%nat ->
 length keys = nk -> Forall column_bytes keys -> length old = 60%nat ->
 words_at p keys -∗ words_at q old -∗
 WP invoke expand_body [eptr p; int (Z.of_nat (4*nk)); eptr q]
 {{v, ⌜v = LitV (LitInt (Z.of_nat nr))⌝ ∗ words_at p keys ∗
 words_at q (expand_words (4*(nr+1)-nk) nk nk keys ++ skipn (4*(nr+1)) old)}}.
Proof.
 intros Hsizes Hlen Hb Hold. iIntros "Hkey Hmem".
 destruct Hsizes as [[-> ->]|[[-> ->]|[-> ->]]];
 unfold invoke, expand_body, args, eptr, int, eq; expand_admin.
 all: rewrite expand_branch_args expand_branch_keylen_key expand_branch_swap.
 all: iApply (expand_branch_wp with "Hkey Hmem"); try assumption; auto.
Qed.
End public_expansion.
Section public_model.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem key_expansion_refines p q keys old nk nr :
 (nk = 4 /\ nr = 10 \/ nk = 6 /\ nr = 12 \/ nk = 8 /\ nr = 14)%nat ->
 length keys = nk -> Forall column_bytes keys -> length old = 60%nat ->
 words_at p keys -∗ words_at q old -∗
 WP invoke expand_body [eptr p; int (Z.of_nat (4*nk)); eptr q]
 {{v, ⌜v = LitV (LitInt (Z.of_nat nr))⌝ ∗
 ⌜flatten_cols (expand_words (4*(nr+1)-nk) nk nk keys) = expanded_key (flatten_cols keys)⌝ ∗
 words_at p keys ∗ words_at q (expand_words (4*(nr+1)-nk) nk nk keys ++ skipn (4*(nr+1)) old)}}.
Proof.
 intros Hsizes Hlen Hb Hold. iIntros "Hkey Hmem".
 iApply (wp_wand with "[Hkey Hmem]").
 { iApply (expand_key_wp p q keys old nk nr with "Hkey Hmem"); assumption. }
 iIntros (v) "(%E & Hkey & Hmem)". iFrame. iSplit; [done|].
 iPureIntro. symmetry. apply expanded_key_columns; assumption.
Qed.
Theorem expand_invalid_wp p q keylen : keylen <> 16 -> keylen <> 24 -> keylen <> 32 ->
 ⊢ WP invoke expand_body [eptr p; int keylen; eptr q] {{v, ⌜v = LitV (LitInt 0)⌝}}.
Proof.
 intros H16 H24 H32. unfold invoke, expand_body, args, eptr, int, eq.
 expand_admin. rewrite bool_decide_false; [|exact H16]. iApply wp_if_false.
 expand_admin. rewrite bool_decide_false; [|exact H24]. iApply wp_if_false.
 expand_admin. rewrite bool_decide_false; [|exact H32]. iApply wp_if_false.
 expand_admin. done.
Qed.
End public_model.
