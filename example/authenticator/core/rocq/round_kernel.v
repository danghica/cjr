(** Scalar SHA-1 round application contract, compiled separately for loop proofs. *)
From Coq Require Import ZArith String List Lia.
From iris.proofmode Require Import proofmode environments.
From cjr Require Import primitive_laws.
From cjr.authenticator Require Import model program refinement.
From iris.prelude Require Import options.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Section proofs.
Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.
Theorem round_app_wp t w a b c d e :
 ⊢ WP App (Val (RecV None (Some "args") round_body))
     (Val (StructV (map (fun z => LitV (LitInt z)) [Z.of_nat t;w;a;b;c;d;e])))
 {{v, ⌜v = StructV (map (fun z => LitV (LitInt z)) (model.sha_round [a;b;c;d;e] (t,w)))⌝}}.
Proof.
 unfold round_body, args, lets, sha_choose, sha_constant,
   rol, mask, add, mul, div, band, xor, le, v, int, op,
   model.sha_round, model.sha_f, model.sha_k, model.sha_ch, model.sha_parity, model.sha_maj,
   model.rol32, model.mask32.
 destruct (Nat.ltb t 20) eqn:H20.
 - apply Nat.ltb_lt in H20. auth_pure. done.
 - apply Nat.ltb_ge in H20. destruct (Nat.ltb t 40) eqn:H40.
   + apply Nat.ltb_lt in H40. auth_pure. done.
   + apply Nat.ltb_ge in H40. destruct (Nat.ltb t 60) eqn:H60.
     * apply Nat.ltb_lt in H60. auth_pure. done.
     * apply Nat.ltb_ge in H60. auth_pure. done.
Qed.
Theorem round_app_z_wp i w a b c d e : 0 <= i ->
 ⊢ WP App (Val (RecV None (Some "args") round_body))
     (Val (StructV (map (fun z => LitV (LitInt z)) [i;w;a;b;c;d;e])))
 {{v, ⌜v = StructV (map (fun z => LitV (LitInt z))
   (model.sha_round [a;b;c;d;e] (Z.to_nat i,w)))⌝}}.
Proof.
 intros Hi.
 exact (eq_rect (Z.of_nat (Z.to_nat i))
   (fun j => ⊢ WP App (Val (RecV None (Some "args") round_body))
     (Val (StructV (map (fun z => LitV (LitInt z)) [j;w;a;b;c;d;e])))
     {{v, ⌜v = StructV (map (fun z => LitV (LitInt z))
       (model.sha_round [a;b;c;d;e] (Z.to_nat i,w)))⌝}})
   (round_app_wp (Z.to_nat i) w a b c d e) i (Z2Nat.id i Hi)).
Qed.
End proofs.
