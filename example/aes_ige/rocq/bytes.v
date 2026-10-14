(** Concrete FIPS 197 byte operations. No cipher correctness is assumed. *)
From Coq Require Import ZArith List Lia Bool Btauto.
Import ListNotations.
Open Scope Z_scope.
Definition byte (x : Z) := 0 <= x < 256.
Definition mask (x : Z) := Z.land x 255.
Definition bx := Z.lxor.
Definition xtime (x : Z) := bx (mask (Z.shiftl x 1))
  (if Z.testbit x 7 then 27 else 0).
Fixpoint gf_mul_bits (n : nat) (a b : Z) : Z :=
  match n with O => 0 | S n =>
    bx (if Z.testbit b 0 then a else 0)
       (gf_mul_bits n (xtime a) (Z.shiftr b 1)) end.
Definition gf_mul := gf_mul_bits 8.
Fixpoint gf_pow (n : nat) (a : Z) : Z :=
  match n with O => 1 | S n => gf_mul a (gf_pow n a) end.
Definition rot8 (x n : Z) := mask (Z.lor (Z.shiftl x n) (Z.shiftr x (8-n))).
Definition sbox_field (x : Z) :=
  let y := gf_pow 254 x in bx y (bx (rot8 y 1)
    (bx (rot8 y 2) (bx (rot8 y 3) (bx (rot8 y 4) 99)))).
Definition sbox_table : list Z := [99; 124; 119; 123; 242; 107; 111; 197; 48; 1; 103; 43; 254; 215; 171; 118; 202; 130; 201; 125; 250; 89; 71; 240; 173; 212; 162; 175; 156; 164; 114; 192; 183; 253; 147; 38; 54; 63; 247; 204; 52; 165; 229; 241; 113; 216; 49; 21; 4; 199; 35; 195; 24; 150; 5; 154; 7; 18; 128; 226; 235; 39; 178; 117; 9; 131; 44; 26; 27; 110; 90; 160; 82; 59; 214; 179; 41; 227; 47; 132; 83; 209; 0; 237; 32; 252; 177; 91; 106; 203; 190; 57; 74; 76; 88; 207; 208; 239; 170; 251; 67; 77; 51; 133; 69; 249; 2; 127; 80; 60; 159; 168; 81; 163; 64; 143; 146; 157; 56; 245; 188; 182; 218; 33; 16; 255; 243; 210; 205; 12; 19; 236; 95; 151; 68; 23; 196; 167; 126; 61; 100; 93; 25; 115; 96; 129; 79; 220; 34; 42; 144; 136; 70; 238; 184; 20; 222; 94; 11; 219; 224; 50; 58; 10; 73; 6; 36; 92; 194; 211; 172; 98; 145; 149; 228; 121; 231; 200; 55; 109; 141; 213; 78; 169; 108; 86; 244; 234; 101; 122; 174; 8; 186; 120; 37; 46; 28; 166; 180; 198; 232; 221; 116; 31; 75; 189; 139; 138; 112; 62; 181; 102; 72; 3; 246; 14; 97; 53; 87; 185; 134; 193; 29; 158; 225; 248; 152; 17; 105; 217; 142; 148; 155; 30; 135; 233; 206; 85; 40; 223; 140; 161; 137; 13; 191; 230; 66; 104; 65; 153; 45; 15; 176; 84; 187; 22].
Definition inv_sbox_table : list Z := [82; 9; 106; 213; 48; 54; 165; 56; 191; 64; 163; 158; 129; 243; 215; 251; 124; 227; 57; 130; 155; 47; 255; 135; 52; 142; 67; 68; 196; 222; 233; 203; 84; 123; 148; 50; 166; 194; 35; 61; 238; 76; 149; 11; 66; 250; 195; 78; 8; 46; 161; 102; 40; 217; 36; 178; 118; 91; 162; 73; 109; 139; 209; 37; 114; 248; 246; 100; 134; 104; 152; 22; 212; 164; 92; 204; 93; 101; 182; 146; 108; 112; 72; 80; 253; 237; 185; 218; 94; 21; 70; 87; 167; 141; 157; 132; 144; 216; 171; 0; 140; 188; 211; 10; 247; 228; 88; 5; 184; 179; 69; 6; 208; 44; 30; 143; 202; 63; 15; 2; 193; 175; 189; 3; 1; 19; 138; 107; 58; 145; 17; 65; 79; 103; 220; 234; 151; 242; 207; 206; 240; 180; 230; 115; 150; 172; 116; 34; 231; 173; 53; 133; 226; 249; 55; 232; 28; 117; 223; 110; 71; 241; 26; 113; 29; 41; 197; 137; 111; 183; 98; 14; 170; 24; 190; 27; 252; 86; 62; 75; 198; 210; 121; 32; 154; 219; 192; 254; 120; 205; 90; 244; 31; 221; 168; 51; 136; 7; 199; 49; 177; 18; 16; 89; 39; 128; 236; 95; 96; 81; 127; 169; 25; 181; 74; 13; 45; 229; 122; 159; 147; 201; 156; 239; 160; 224; 59; 77; 174; 42; 245; 176; 200; 235; 187; 60; 131; 83; 153; 97; 23; 43; 4; 126; 186; 119; 214; 38; 225; 105; 20; 99; 85; 33; 12; 125].
Definition sbox (x : Z) := nth (Z.to_nat x) sbox_table 0.
Definition inv_sbox (x : Z) := nth (Z.to_nat x) inv_sbox_table 0.
Definition byte_values := map Z.of_nat (seq 0 256).
Lemma byte_check f : forallb f byte_values = true ->
  forall x, byte x -> f x = true.
Proof.
  intros H x Hx. apply (proj1 (forallb_forall _ _) H).
  unfold byte_values. apply in_map_iff. exists (Z.to_nat x). split.
  - rewrite Z2Nat.id; unfold byte in Hx; lia.
  - apply in_seq. unfold byte in Hx. lia.
Qed.
Lemma mask_byte x : byte (mask x).
Proof.
  unfold mask, byte. change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^8)). simpl in *. lia.
Qed.
Lemma bx_assoc a b c : bx a (bx b c) = bx (bx a b) c.
Proof. symmetry. apply Z.lxor_assoc. Qed.
Lemma bx_comm a b : bx a b = bx b a.
Proof. apply Z.lxor_comm. Qed.
Lemma bx_zero a : bx a 0 = a.
Proof. apply Z.lxor_0_r. Qed.
Lemma bx_self a : bx a a = 0.
Proof. apply Z.lxor_nilpotent. Qed.
Lemma bx_cancel a b : bx (bx a b) b = a.
Proof. rewrite <- bx_assoc, bx_self, bx_zero. reflexivity. Qed.
Lemma land_xor a b c : Z.land (Z.lxor a b) c =
  Z.lxor (Z.land a c) (Z.land b c).
Proof.
  apply Z.bits_inj; intros n; repeat rewrite Z.land_spec;
    repeat rewrite Z.lxor_spec; repeat rewrite Z.land_spec; btauto.
Qed.
Lemma bx_byte a b : byte a -> byte b -> byte (bx a b).
Proof.
  intros Ha Hb. assert (mask a = a) as Ea.
  { unfold mask. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    apply Z.mod_small. exact Ha. }
  assert (mask b = b) as Eb.
  { unfold mask. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
    apply Z.mod_small. exact Hb. }
  rewrite <- Ea, <- Eb. unfold mask, bx.
  rewrite <- land_xor. apply mask_byte.
Qed.
Lemma xtime_linear a b : xtime (bx a b) = bx (xtime a) (xtime b).
Proof.
  unfold xtime, mask, bx. rewrite Z.shiftl_lxor, land_xor, Z.lxor_spec.
  destruct (Z.testbit a 7), (Z.testbit b 7); simpl;
    apply Z.bits_inj; intros n; repeat rewrite Z.lxor_spec;
    rewrite ?Z.bits_0; btauto.
Qed.
Lemma sbox_certificate : forallb (fun x =>
  Z.eqb (sbox x) (sbox_field x) &&
  Z.eqb (inv_sbox (sbox x)) x && Z.eqb (sbox (inv_sbox x)) x &&
  ((0 <=? sbox x) && (sbox x <? 256)) &&
  ((0 <=? inv_sbox x) && (inv_sbox x <? 256))) byte_values = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sbox_properties x : byte x ->
  sbox x = sbox_field x /\ inv_sbox (sbox x) = x /\
  sbox (inv_sbox x) = x /\ byte (sbox x) /\ byte (inv_sbox x).
Proof.
  intros Hx. pose proof (byte_check _ sbox_certificate x Hx) as H.
  repeat rewrite andb_true_iff in H. repeat rewrite Z.eqb_eq in H.
  repeat rewrite Z.leb_le in H. repeat rewrite Z.ltb_lt in H.
  unfold byte. tauto.
Qed.
Lemma inv_sbox_sbox x : byte x -> inv_sbox (sbox x) = x.
Proof. intros H; apply sbox_properties in H; tauto. Qed.
Lemma sbox_inv_sbox x : byte x -> sbox (inv_sbox x) = x.
Proof. intros H; apply sbox_properties in H; tauto. Qed.
Lemma sbox_byte x : byte x -> byte (sbox x).
Proof. intros H; apply sbox_properties in H; tauto. Qed.
Lemma inv_sbox_byte x : byte x -> byte (inv_sbox x).
Proof. intros H; apply sbox_properties in H; tauto. Qed.

(** Every arithmetic intermediate of the byte-doubling kernel fits Int64. *)
Theorem byte_machine_bounds x : byte x ->
  0 <= x+x <= 510 /\ -9223372036854775808 <= x+x <= 9223372036854775807.
Proof. unfold byte; lia. Qed.
Theorem block_loop_machine_bounds i n :
  0 <= i -> 0 <= n <= 9223372036854775807 -> i <= n-16 ->
  -16 <= n-16 <= 9223372036854775807 /\ 0 <= i+16 <= n.
Proof. lia. Qed.
