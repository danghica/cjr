(** Refinement of complete AES and IGE routines. *)
From Coq Require Import ZArith List String Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.examples Require Import hm_tactics array.
From cjr.aes_ige Require Import bytes block aes ige program refinement memory kernels.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Lemma mix_three_inv b : mix_columns (mix_columns (mix_columns b)) = inv_mix_columns b.
Proof. block_destruct b; reflexivity. Qed.
Local Opaque block_at xor sub_bytes inv_sub_bytes shift_rows inv_shift_rows mix_columns inv_mix_columns encrypt_schedule decrypt_schedule encrypt_tail decrypt_tail round unround final_round unfinal_round.
Opaque sbox_body inv_sbox_body xtime_body copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
#[local] Hint Rewrite copy_body_subst_src copy_body_subst_dst copy_body_subst_schedule copy_body_subst_nr copy_body_subst_work copy_body_subst_key copy_body_subst_keyLen copy_body_subst_len copy_body_subst_iv copy_body_subst_i xor_body_subst_src xor_body_subst_dst xor_body_subst_schedule xor_body_subst_nr xor_body_subst_work xor_body_subst_key xor_body_subst_keyLen xor_body_subst_len xor_body_subst_iv xor_body_subst_i sub_body_subst_src sub_body_subst_dst sub_body_subst_schedule sub_body_subst_nr sub_body_subst_work sub_body_subst_key sub_body_subst_keyLen sub_body_subst_len sub_body_subst_iv sub_body_subst_i inv_sub_body_subst_src inv_sub_body_subst_dst inv_sub_body_subst_schedule inv_sub_body_subst_nr inv_sub_body_subst_work inv_sub_body_subst_key inv_sub_body_subst_keyLen inv_sub_body_subst_len inv_sub_body_subst_iv inv_sub_body_subst_i shift_body_subst_src shift_body_subst_dst shift_body_subst_schedule shift_body_subst_nr shift_body_subst_work shift_body_subst_key shift_body_subst_keyLen shift_body_subst_len shift_body_subst_iv shift_body_subst_i inv_shift_body_subst_src inv_shift_body_subst_dst inv_shift_body_subst_schedule inv_shift_body_subst_nr inv_shift_body_subst_work inv_shift_body_subst_key inv_shift_body_subst_keyLen inv_shift_body_subst_len inv_shift_body_subst_iv inv_shift_body_subst_i mix_body_subst_src mix_body_subst_dst mix_body_subst_schedule mix_body_subst_nr mix_body_subst_work mix_body_subst_key mix_body_subst_keyLen mix_body_subst_len mix_body_subst_iv mix_body_subst_i : routine_subst.
Ltac routine_rewrite := repeat match goal with
| |- context[subst "src" ?value copy_body] => rewrite (copy_body_subst_src value)
| |- context[subst "dst" ?value copy_body] => rewrite (copy_body_subst_dst value)
| |- context[subst "schedule" ?value copy_body] => rewrite (copy_body_subst_schedule value)
| |- context[subst "nr" ?value copy_body] => rewrite (copy_body_subst_nr value)
| |- context[subst "work" ?value copy_body] => rewrite (copy_body_subst_work value)
| |- context[subst "key" ?value copy_body] => rewrite (copy_body_subst_key value)
| |- context[subst "keyLen" ?value copy_body] => rewrite (copy_body_subst_keyLen value)
| |- context[subst "len" ?value copy_body] => rewrite (copy_body_subst_len value)
| |- context[subst "iv" ?value copy_body] => rewrite (copy_body_subst_iv value)
| |- context[subst "i" ?value copy_body] => rewrite (copy_body_subst_i value)
| |- context[subst "src" ?value xor_body] => rewrite (xor_body_subst_src value)
| |- context[subst "dst" ?value xor_body] => rewrite (xor_body_subst_dst value)
| |- context[subst "schedule" ?value xor_body] => rewrite (xor_body_subst_schedule value)
| |- context[subst "nr" ?value xor_body] => rewrite (xor_body_subst_nr value)
| |- context[subst "work" ?value xor_body] => rewrite (xor_body_subst_work value)
| |- context[subst "key" ?value xor_body] => rewrite (xor_body_subst_key value)
| |- context[subst "keyLen" ?value xor_body] => rewrite (xor_body_subst_keyLen value)
| |- context[subst "len" ?value xor_body] => rewrite (xor_body_subst_len value)
| |- context[subst "iv" ?value xor_body] => rewrite (xor_body_subst_iv value)
| |- context[subst "i" ?value xor_body] => rewrite (xor_body_subst_i value)
| |- context[subst "src" ?value sub_body] => rewrite (sub_body_subst_src value)
| |- context[subst "dst" ?value sub_body] => rewrite (sub_body_subst_dst value)
| |- context[subst "schedule" ?value sub_body] => rewrite (sub_body_subst_schedule value)
| |- context[subst "nr" ?value sub_body] => rewrite (sub_body_subst_nr value)
| |- context[subst "work" ?value sub_body] => rewrite (sub_body_subst_work value)
| |- context[subst "key" ?value sub_body] => rewrite (sub_body_subst_key value)
| |- context[subst "keyLen" ?value sub_body] => rewrite (sub_body_subst_keyLen value)
| |- context[subst "len" ?value sub_body] => rewrite (sub_body_subst_len value)
| |- context[subst "iv" ?value sub_body] => rewrite (sub_body_subst_iv value)
| |- context[subst "i" ?value sub_body] => rewrite (sub_body_subst_i value)
| |- context[subst "src" ?value inv_sub_body] => rewrite (inv_sub_body_subst_src value)
| |- context[subst "dst" ?value inv_sub_body] => rewrite (inv_sub_body_subst_dst value)
| |- context[subst "schedule" ?value inv_sub_body] => rewrite (inv_sub_body_subst_schedule value)
| |- context[subst "nr" ?value inv_sub_body] => rewrite (inv_sub_body_subst_nr value)
| |- context[subst "work" ?value inv_sub_body] => rewrite (inv_sub_body_subst_work value)
| |- context[subst "key" ?value inv_sub_body] => rewrite (inv_sub_body_subst_key value)
| |- context[subst "keyLen" ?value inv_sub_body] => rewrite (inv_sub_body_subst_keyLen value)
| |- context[subst "len" ?value inv_sub_body] => rewrite (inv_sub_body_subst_len value)
| |- context[subst "iv" ?value inv_sub_body] => rewrite (inv_sub_body_subst_iv value)
| |- context[subst "i" ?value inv_sub_body] => rewrite (inv_sub_body_subst_i value)
| |- context[subst "src" ?value shift_body] => rewrite (shift_body_subst_src value)
| |- context[subst "dst" ?value shift_body] => rewrite (shift_body_subst_dst value)
| |- context[subst "schedule" ?value shift_body] => rewrite (shift_body_subst_schedule value)
| |- context[subst "nr" ?value shift_body] => rewrite (shift_body_subst_nr value)
| |- context[subst "work" ?value shift_body] => rewrite (shift_body_subst_work value)
| |- context[subst "key" ?value shift_body] => rewrite (shift_body_subst_key value)
| |- context[subst "keyLen" ?value shift_body] => rewrite (shift_body_subst_keyLen value)
| |- context[subst "len" ?value shift_body] => rewrite (shift_body_subst_len value)
| |- context[subst "iv" ?value shift_body] => rewrite (shift_body_subst_iv value)
| |- context[subst "i" ?value shift_body] => rewrite (shift_body_subst_i value)
| |- context[subst "src" ?value inv_shift_body] => rewrite (inv_shift_body_subst_src value)
| |- context[subst "dst" ?value inv_shift_body] => rewrite (inv_shift_body_subst_dst value)
| |- context[subst "schedule" ?value inv_shift_body] => rewrite (inv_shift_body_subst_schedule value)
| |- context[subst "nr" ?value inv_shift_body] => rewrite (inv_shift_body_subst_nr value)
| |- context[subst "work" ?value inv_shift_body] => rewrite (inv_shift_body_subst_work value)
| |- context[subst "key" ?value inv_shift_body] => rewrite (inv_shift_body_subst_key value)
| |- context[subst "keyLen" ?value inv_shift_body] => rewrite (inv_shift_body_subst_keyLen value)
| |- context[subst "len" ?value inv_shift_body] => rewrite (inv_shift_body_subst_len value)
| |- context[subst "iv" ?value inv_shift_body] => rewrite (inv_shift_body_subst_iv value)
| |- context[subst "i" ?value inv_shift_body] => rewrite (inv_shift_body_subst_i value)
| |- context[subst "src" ?value mix_body] => rewrite (mix_body_subst_src value)
| |- context[subst "dst" ?value mix_body] => rewrite (mix_body_subst_dst value)
| |- context[subst "schedule" ?value mix_body] => rewrite (mix_body_subst_schedule value)
| |- context[subst "nr" ?value mix_body] => rewrite (mix_body_subst_nr value)
| |- context[subst "work" ?value mix_body] => rewrite (mix_body_subst_work value)
| |- context[subst "key" ?value mix_body] => rewrite (mix_body_subst_key value)
| |- context[subst "keyLen" ?value mix_body] => rewrite (mix_body_subst_keyLen value)
| |- context[subst "len" ?value mix_body] => rewrite (mix_body_subst_len value)
| |- context[subst "iv" ?value mix_body] => rewrite (mix_body_subst_iv value)
| |- context[subst "i" ?value mix_body] => rewrite (mix_body_subst_i value)
end.
Ltac block_byte_goal := repeat first [assumption | apply xor_bytes | apply sub_bytes_range
 | apply inv_sub_bytes_range | apply shift_bytes | apply inv_shift_bytes
 | apply mix_columns_bytes | apply inv_mix_columns_bytes | apply round_bytes
 | apply final_bytes | apply encrypt_bytes | apply decrypt_bytes].
Ltac abstract_destination q :=
 iMatchHyp ltac:(fun H P => lazymatch P with block_at ?loc ?payload =>
   let Eloc := fresh "Eloc" in assert (Eloc : loc = q) by (cbn [Z.of_nat Z.mul]; lia);
   let state := fresh "state" in let Estate := fresh "Estate" in
   remember payload as state eqn:Estate in *;
   let Hbyte := fresh "Hstatebyte" in
   assert (Hbyte : block_bytes state) by (rewrite Estate; block_byte_goal)
 end).
Ltac complete_two spec p q needbytes :=
 iMatchHyp ltac:(fun H P => lazymatch P with @block_at ?sig ?gs ?hp ?b =>
 let Ep := fresh "Ep" in assert (Ep : p = hp) by (cbn [Z.of_nat Z.mul]; lia);
 iMatchHyp ltac:(fun D Q => lazymatch Q with block_at ?hq ?old =>
 let Eq := fresh "Eq" in assert (Eq : q = hq) by (cbn [Z.of_nat Z.mul]; lia);
 try rewrite Ep; try rewrite Eq;
 lazymatch needbytes with
 | true => let Hbyte := fresh "Hbyte" in assert (Hbyte : block_bytes b) by block_byte_goal; iPoseProof (@spec sig gs _ hp hq b old Hbyte with "[$] [$]") as "Hcall"
 | false => iPoseProof (@spec sig gs _ hp hq b old with "[$] [$]") as "Hcall"
 end;
 iApply (wp_wand with "Hcall"); let result := fresh "result" in iIntros (result) "(%E & ? & ?)"; subst result; abstract_destination hq
 end) end).
Ltac complete_three p k q :=
 iMatchHyp ltac:(fun H P => lazymatch P with block_at ?hp ?b =>
 let Ep := fresh "Ep" in assert (Ep : p = hp) by (cbn [Z.of_nat Z.mul]; lia);
 iMatchHyp ltac:(fun K Q => lazymatch Q with block_at ?hk ?key =>
 let Ek := fresh "Ek" in assert (Ek : k = hk) by (cbn [Z.of_nat Z.mul]; lia); iMatchHyp ltac:(fun D R => lazymatch R with block_at ?hq ?old =>
 let Eq := fresh "Eq" in assert (Eq : q = hq) by (cbn [Z.of_nat Z.mul]; lia); try rewrite Ep; try rewrite Ek; try rewrite Eq; iPoseProof (xor_app_wp hp hk hq b key old with "[$] [$] [$]") as "Hcall";
 iApply (wp_wand with "Hcall"); let result := fresh "result" in iIntros (result) "(%E & ? & ? & ?)"; subst result; abstract_destination hq
 end) end) end).
Ltac complete_head := first [
 match goal with
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") copy_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two copy_app_wp p q false
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") sub_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two sub_app_wp p q true
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") inv_sub_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two inv_sub_app_wp p q true
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") shift_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two shift_app_wp p q false
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") inv_shift_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two inv_shift_app_wp p q false
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") mix_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?q)])) {{_}}) => complete_two mix_app_wp p q true
 | |- envs_entails _ (WP App (Val (RecV None (Some "args") xor_body)) (Val (StructV [LitV (LitPtr ?p); LitV (LitPtr ?k); LitV (LitPtr ?q)])) {{_}}) => complete_three p k q
 end | iApply wp_if_true | iApply wp_if_false | hm_head ].
Ltac complete_run := iStartProof; repeat (cbn [fill fill_item]; simpl; routine_rewrite;
 match goal with |- envs_entails _ (WP ?e {{?Φ}}) => hm_focus e ltac:(fun _ => complete_head) end);
 cbn [fill fill_item]; simpl.
Section routines.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Definition schedule_at p ks : iProp Σ := [∗ list] i ↦ k ∈ ks, block_at (p + 16 * Z.of_nat i) k.
Definition work_at p : iProp Σ := ∃ a b, block_at p a ∗ block_at (p+16) b.
End routines.
