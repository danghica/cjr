(** Fixed-size AES states: four columns, each with four byte coordinates. *)
From Coq Require Import ZArith List Lia Bool Btauto.
From cjr.aes_ige Require Import bytes.
Import ListNotations.
Open Scope Z_scope.
Record column := Col { a0 : Z; a1 : Z; a2 : Z; a3 : Z }.
Record block := Block { c0 : column; c1 : column; c2 : column; c3 : column }.
Definition column_bytes c := byte (a0 c) /\ byte (a1 c) /\ byte (a2 c) /\ byte (a3 c).
Definition block_bytes b := column_bytes (c0 b) /\ column_bytes (c1 b) /\
  column_bytes (c2 b) /\ column_bytes (c3 b).
Definition cmap f c := Col (f (a0 c)) (f (a1 c)) (f (a2 c)) (f (a3 c)).
Definition bmap f b := Block (f (c0 b)) (f (c1 b)) (f (c2 b)) (f (c3 b)).
Definition cxor x y := Col (bx (a0 x) (a0 y)) (bx (a1 x) (a1 y))
  (bx (a2 x) (a2 y)) (bx (a3 x) (a3 y)).
Definition xor x y := Block (cxor (c0 x) (c0 y)) (cxor (c1 x) (c1 y))
  (cxor (c2 x) (c2 y)) (cxor (c3 x) (c3 y)).
Definition zero := Block (Col 0 0 0 0) (Col 0 0 0 0) (Col 0 0 0 0) (Col 0 0 0 0).
Definition sub_bytes := bmap (cmap sbox).
Definition inv_sub_bytes := bmap (cmap inv_sbox).
Definition shift_rows b := Block
  (Col (a0 (c0 b)) (a1 (c1 b)) (a2 (c2 b)) (a3 (c3 b)))
  (Col (a0 (c1 b)) (a1 (c2 b)) (a2 (c3 b)) (a3 (c0 b)))
  (Col (a0 (c2 b)) (a1 (c3 b)) (a2 (c0 b)) (a3 (c1 b)))
  (Col (a0 (c3 b)) (a1 (c0 b)) (a2 (c1 b)) (a3 (c2 b))).
Definition inv_shift_rows b := Block
  (Col (a0 (c0 b)) (a1 (c3 b)) (a2 (c2 b)) (a3 (c1 b)))
  (Col (a0 (c1 b)) (a1 (c0 b)) (a2 (c3 b)) (a3 (c2 b)))
  (Col (a0 (c2 b)) (a1 (c1 b)) (a2 (c0 b)) (a3 (c3 b)))
  (Col (a0 (c3 b)) (a1 (c2 b)) (a2 (c1 b)) (a3 (c0 b))).
Definition mix c :=
  let x := a0 c in let y := a1 c in let z := a2 c in let w := a3 c in
  Col (bx (xtime (bx x y)) (bx y (bx z w)))
      (bx (xtime (bx y z)) (bx z (bx w x)))
      (bx (xtime (bx z w)) (bx w (bx x y)))
      (bx (xtime (bx w x)) (bx x (bx y z))).
Definition inv_mix c := mix (mix (mix c)).
Definition mix_columns := bmap mix.
Definition inv_mix_columns := bmap inv_mix.
Ltac block_destruct b := destruct b as [[? ? ? ?] [? ? ? ?] [? ? ? ?] [? ? ? ?]].
Ltac xor_bits :=
  repeat match goal with |- context[xtime ?x] =>
    let t := fresh "t" in let E := fresh "Et" in remember (xtime x) as t eqn:E end;
  unfold bx; apply Z.bits_inj; intros n;
  repeat rewrite Z.lxor_spec; rewrite ?Z.bits_0; btauto.
Lemma xor_assoc x y z : xor x (xor y z) = xor (xor x y) z.
Proof. block_destruct x; block_destruct y; block_destruct z;
  unfold xor, cxor; simpl; repeat rewrite bx_assoc; reflexivity. Qed.
Lemma xor_comm x y : xor x y = xor y x.
Proof. block_destruct x; block_destruct y; unfold xor, cxor; simpl;
  repeat first [apply bx_comm | f_equal]. Qed.
Lemma xor_zero x : xor x zero = x.
Proof. block_destruct x; unfold xor, cxor, zero; simpl;
  repeat rewrite bx_zero; reflexivity. Qed.
Lemma xor_self x : xor x x = zero.
Proof. block_destruct x; unfold xor, cxor, zero; simpl;
  repeat rewrite bx_self; reflexivity. Qed.
Lemma xor_cancel x y : xor (xor x y) y = x.
Proof. rewrite <- xor_assoc, xor_self, xor_zero. reflexivity. Qed.
Lemma xor_bytes x y : block_bytes x -> block_bytes y -> block_bytes (xor x y).
Proof. block_destruct x; block_destruct y;
  unfold block_bytes, column_bytes, xor, cxor; simpl;
  intros; repeat split; apply bx_byte; tauto. Qed.
Lemma shift_inverse b : inv_shift_rows (shift_rows b) = b.
Proof. block_destruct b; reflexivity. Qed.
Lemma inverse_shift b : shift_rows (inv_shift_rows b) = b.
Proof. block_destruct b; reflexivity. Qed.
Lemma shift_bytes b : block_bytes b -> block_bytes (shift_rows b).
Proof. block_destruct b; unfold block_bytes, column_bytes, shift_rows; simpl; tauto. Qed.
Lemma inv_shift_bytes b : block_bytes b -> block_bytes (inv_shift_rows b).
Proof. block_destruct b; unfold block_bytes, column_bytes, inv_shift_rows; simpl; tauto. Qed.
Lemma sub_inverse b : block_bytes b -> inv_sub_bytes (sub_bytes b) = b.
Proof. block_destruct b; unfold block_bytes, column_bytes; simpl; intros H;
  unfold inv_sub_bytes, sub_bytes, bmap, cmap; simpl;
  repeat rewrite inv_sbox_sbox by tauto; reflexivity. Qed.
Lemma inverse_sub b : block_bytes b -> sub_bytes (inv_sub_bytes b) = b.
Proof. block_destruct b; unfold block_bytes, column_bytes; simpl; intros H;
  unfold inv_sub_bytes, sub_bytes, bmap, cmap; simpl;
  repeat rewrite sbox_inv_sbox by tauto; reflexivity. Qed.
Lemma sub_bytes_range b : block_bytes b -> block_bytes (sub_bytes b).
Proof. block_destruct b; unfold block_bytes, column_bytes, sub_bytes, bmap, cmap;
  simpl; intros; repeat split; apply sbox_byte; tauto. Qed.
Lemma inv_sub_bytes_range b : block_bytes b -> block_bytes (inv_sub_bytes b).
Proof. block_destruct b; unfold block_bytes, column_bytes, inv_sub_bytes, bmap, cmap;
  simpl; intros; repeat split; apply inv_sbox_byte; tauto. Qed.
Arguments xtime _ : simpl never.
Arguments bx _ _ : simpl never.
Definition twice c :=
 let t := xtime (xtime (bx (a0 c) (a2 c))) in
 let u := xtime (xtime (bx (a1 c) (a3 c))) in
 Col (bx (a0 c) t) (bx (a1 c) u) (bx (a2 c) t) (bx (a3 c) u).
Lemma mix_two c : mix (mix c) = twice c.
Proof. destruct c; unfold mix, twice; simpl.
 repeat rewrite xtime_linear. f_equal; xor_bits. Qed.
Lemma mix_four c : mix (mix (mix (mix c))) = c.
Proof. rewrite mix_two, mix_two. destruct c; unfold twice; simpl.
 repeat rewrite xtime_linear. f_equal; xor_bits. Qed.
Lemma mix_inverse c : inv_mix (mix c) = c.
Proof. apply mix_four. Qed.
Lemma inverse_mix c : mix (inv_mix c) = c.
Proof. apply mix_four. Qed.
Lemma mix_columns_inverse b : inv_mix_columns (mix_columns b) = b.
Proof. destruct b; unfold inv_mix_columns, mix_columns, bmap; simpl;
  repeat rewrite mix_inverse; reflexivity. Qed.
Lemma inverse_mix_columns b : mix_columns (inv_mix_columns b) = b.
Proof. destruct b; unfold inv_mix_columns, mix_columns, bmap; simpl;
  repeat rewrite inverse_mix; reflexivity. Qed.
Lemma xtime_byte x : byte x -> byte (xtime x).
Proof. intros. apply bx_byte; [apply mask_byte|].
  destruct (Z.testbit x 7); unfold byte; lia. Qed.
Lemma mix_bytes c : column_bytes c -> column_bytes (mix c).
Proof. destruct c; unfold column_bytes, mix; simpl; intros;
  repeat first [tauto | apply xtime_byte | apply bx_byte | split]. Qed.
Lemma mix_columns_bytes b : block_bytes b -> block_bytes (mix_columns b).
Proof. destruct b; unfold block_bytes, mix_columns, bmap; simpl; intros;
  repeat first [tauto | apply mix_bytes | split]. Qed.
Lemma inv_mix_columns_bytes b : block_bytes b -> block_bytes (inv_mix_columns b).
Proof. destruct b; unfold block_bytes, inv_mix_columns, bmap, inv_mix; simpl; intros;
  repeat first [tauto | apply mix_bytes | split]. Qed.

(** Agreement with the inverse matrix in FIPS 197, not just an abstract inverse. *)
Definition inverse_matrix c := Col
 (bx (gf_mul (a0 c) 14) (bx (gf_mul (a1 c) 11) (bx (gf_mul (a2 c) 13) (gf_mul (a3 c) 9))))
 (bx (gf_mul (a0 c) 9) (bx (gf_mul (a1 c) 14) (bx (gf_mul (a2 c) 11) (gf_mul (a3 c) 13))))
 (bx (gf_mul (a0 c) 13) (bx (gf_mul (a1 c) 9) (bx (gf_mul (a2 c) 14) (gf_mul (a3 c) 11))))
 (bx (gf_mul (a0 c) 11) (bx (gf_mul (a1 c) 13) (bx (gf_mul (a2 c) 9) (gf_mul (a3 c) 14)))).
Definition x2 x := xtime (xtime x).
Definition x3 x := xtime (x2 x).
Lemma matrix_certificate : forallb (fun x =>
 Z.eqb (gf_mul x 9) (bx (x3 x) x) &&
 Z.eqb (gf_mul x 11) (bx (x3 x) (bx (xtime x) x)) &&
 Z.eqb (gf_mul x 13) (bx (x3 x) (bx (x2 x) x)) &&
 Z.eqb (gf_mul x 14) (bx (x3 x) (bx (x2 x) (xtime x)))) byte_values = true.
Proof. vm_compute. reflexivity. Qed.
Lemma matrix_coefficients x : byte x ->
 gf_mul x 9 = bx (x3 x) x /\
 gf_mul x 11 = bx (x3 x) (bx (xtime x) x) /\
 gf_mul x 13 = bx (x3 x) (bx (x2 x) x) /\
 gf_mul x 14 = bx (x3 x) (bx (x2 x) (xtime x)).
Proof. intros H. pose proof (byte_check _ matrix_certificate x H) as E.
 repeat rewrite andb_true_iff in E. repeat rewrite Z.eqb_eq in E. tauto. Qed.
Theorem inv_mix_fips c : column_bytes c -> inv_mix c = inverse_matrix c.
Proof.
 destruct c as [a b c d]. unfold column_bytes; simpl; intros H.
 destruct (matrix_coefficients a ltac:(tauto)) as [A9 [A11 [A13 A14]]].
 destruct (matrix_coefficients b ltac:(tauto)) as [B9 [B11 [B13 B14]]].
 destruct (matrix_coefficients c ltac:(tauto)) as [C9 [C11 [C13 C14]]].
 destruct (matrix_coefficients d ltac:(tauto)) as [D9 [D11 [D13 D14]]].
 unfold inverse_matrix; simpl. rewrite A9,A11,A13,A14,B9,B11,B13,B14,C9,C11,C13,C14,D9,D11,D13,D14.
 unfold inv_mix. rewrite mix_two. unfold mix, twice; simpl. unfold x3,x2. repeat rewrite xtime_linear.
 f_equal; xor_bits.
Qed.
