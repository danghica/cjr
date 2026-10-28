(** Streaming invariants for the actual Base32 decoder. *)
From Coq Require Import ZArith List Lia Bool.
From cjr.authenticator Require Import model base32.
Import ListNotations.
Open Scope Z_scope.

Definition padding_only chars := forallb (fun ch => ch =? 61) chars.
Lemma padding_only_length chars :
 padding_only chars = true -> read_symbols chars = Some ([],length chars).
Proof.
 destruct chars as [|ch rest]; [reflexivity|].
 unfold padding_only; simpl. rewrite andb_true_iff.
 intros [Hch Hr]. rewrite Hch, Hr. reflexivity.
Qed.
Lemma read_symbols_empty chars pad :
 read_symbols chars = Some ([],pad) ->
 padding_only chars = true /\ pad = length chars.
Proof.
 destruct chars as [|ch rest]; simpl.
 - intros H; inversion H; subst; auto.
 - unfold padding_only; simpl.
   destruct (ch =? 61) eqn:Hch.
   + destruct (forallb (fun x => x =? 61) rest) eqn:Hr;
       intros H; inversion H; subst; auto.
   + destruct (digit_value ch); [|discriminate].
     destruct (read_symbols rest) as [[ds p]|]; discriminate.
Qed.
Lemma read_symbols_snoc chars ch ds pad :
 read_symbols chars = Some (ds,pad) ->
 read_symbols (chars ++ [ch]) =
 if ch =? 61 then Some (ds,S pad) else
 if (pad =? 0)%nat then
   match digit_value ch with Some d => Some (ds ++ [d],0%nat) | None => None end
 else None.
Proof.
 revert ds pad. induction chars as [|a rest IH]; intros ds pad Hread.
 - simpl in Hread; inversion Hread; subst. simpl.
   destruct (ch =? 61); [reflexivity|].
   destruct (digit_value ch); reflexivity.
 - simpl in Hread |- *.
   destruct (a =? 61) eqn:Ha.
   + destruct (forallb (fun x => x =? 61) rest) eqn:Hr; [|discriminate].
     inversion Hread; subst. rewrite forallb_app, Hr. simpl.
     destruct (ch =? 61); simpl; [rewrite length_app; simpl; f_equal; f_equal; lia|reflexivity].
   + destruct (digit_value a) as [d|] eqn:Hd; [|discriminate].
     destruct (read_symbols rest) as [[values padding]|] eqn:Hp; [|discriminate].
     inversion Hread; subst. rewrite (IH _ _ eq_refl).
     destruct (ch =? 61); [reflexivity|].
     destruct (pad =? 0)%nat; [|reflexivity].
     destruct (digit_value ch); reflexivity.
Qed.
Lemma read_symbols_invalid_snoc chars ch :
 read_symbols chars = None -> read_symbols (chars ++ [ch]) = None.
Proof.
 induction chars as [|a rest IH]; simpl; [discriminate|].
 destruct (a =? 61) eqn:Ha.
 - destruct (forallb (fun x => x =? 61) rest) eqn:Hr; [discriminate|].
   intros _. rewrite forallb_app, Hr. reflexivity.
 - destruct (digit_value a) eqn:Hd; [|reflexivity].
   destruct (read_symbols rest) as [[ds pad]|] eqn:Hr; [discriminate|].
   intros _. rewrite (IH eq_refl). reflexivity.
Qed.
Lemma read_symbols_length chars ds pad :
 read_symbols chars = Some (ds,pad) -> (length ds + pad = length chars)%nat.
Proof.
 revert ds pad. induction chars as [|ch rest IH]; simpl; intros ds pad H.
 - inversion H; reflexivity.
 - destruct (ch =? 61).
   + destruct (forallb (fun x => x =? 61) rest); inversion H; subst; reflexivity.
   + destruct (digit_value ch); [|discriminate].
     destruct (read_symbols rest) as [[values padding]|] eqn:Hr; [|discriminate].
     inversion H; subst. simpl. specialize (IH _ _ eq_refl). lia.
Qed.
Record bit_state := Bits { emitted : list Z; accumulator : Z; bit_count : Z }.
Definition bit_step st d :=
 let next := accumulator st * 32 + d in
 let width := bit_count st + 5 in
 if width <? 8 then Bits (emitted st) next width else
 let factor := 2^(width-8) in
 Bits (emitted st ++ [Z.quot next factor]) (Z.rem next factor) (width-8).
Definition bit_run ds acc bits := fold_left bit_step ds (Bits [] acc bits).
Lemma bit_step_prefix prefix st d :
 bit_step (Bits (prefix ++ emitted st) (accumulator st) (bit_count st)) d =
 let next := bit_step st d in Bits (prefix ++ emitted next) (accumulator next) (bit_count next).
Proof.
 destruct st as [out acc bits]. unfold bit_step; simpl.
 destruct (bits+5 <? 8); simpl; [reflexivity|]. rewrite app_assoc. reflexivity.
Qed.
Lemma bit_fold_prefix ds prefix st :
 fold_left bit_step ds (Bits (prefix ++ emitted st) (accumulator st) (bit_count st)) =
 let next := fold_left bit_step ds st in
 Bits (prefix ++ emitted next) (accumulator next) (bit_count next).
Proof.
 revert st. induction ds as [|d ds IH]; intros st; simpl.
 - destruct st; reflexivity.
 - rewrite bit_step_prefix. apply IH.
Qed.
Lemma bit_fold_output ds prefix acc bits :
 fold_left bit_step ds (Bits prefix acc bits) =
 let next := bit_run ds acc bits in
 Bits (prefix ++ emitted next) (accumulator next) (bit_count next).
Proof.
 pose proof (bit_fold_prefix ds prefix (Bits [] acc bits)) as H.
 simpl in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma bit_step_empty acc bits d :
 bit_step (Bits [] acc bits) d =
 if bits+5 <? 8 then Bits [] (acc*32+d) (bits+5) else
 Bits [Z.quot (acc*32+d) (2^(bits+5-8))]
   (Z.rem (acc*32+d) (2^(bits+5-8))) (bits+5-8).
Proof. reflexivity. Qed.
Lemma bit_run_values ds acc bits :
 (emitted (bit_run ds acc bits), accumulator (bit_run ds acc bits)) = decode_values ds acc bits.
Proof.
 revert acc bits. induction ds as [|d ds IH]; intros acc bits; [reflexivity|].
 change ((emitted (fold_left bit_step ds (bit_step (Bits [] acc bits) d)),
   accumulator (fold_left bit_step ds (bit_step (Bits [] acc bits) d))) = decode_values (d :: ds) acc bits).
 rewrite bit_step_empty. cbn [decode_values].
 destruct (bits+5 <? 8) eqn:Hw.
 - exact (IH (acc*32+d) (bits+5)).
 - rewrite bit_fold_output.
   specialize (IH (Z.rem (acc*32+d) (2^(bits+5-8))) (bits+5-8)).
   destruct (bit_run ds (Z.rem (acc*32+d) (2^(bits+5-8))) (bits+5-8)) as [out tail width].
   simpl in IH |- *. rewrite <- IH. reflexivity.
Qed.
Lemma bit_run_snoc ds acc bits d :
 bit_run (ds ++ [d]) acc bits = bit_step (bit_run ds acc bits) d.
Proof. unfold bit_run. rewrite fold_left_app. reflexivity. Qed.
Record scan_state := Scan { scan_valid : bool; scan_padding : nat;
 scan_symbols : nat; scan_bits : bit_state }.
Definition initial_scan := Scan true 0 0 (Bits [] 0 0).
Definition scan_step st ch :=
 if ch =? 61 then Scan (scan_valid st) (S (scan_padding st)) (scan_symbols st) (scan_bits st)
 else match digit_value ch with
 | Some d => if (scan_padding st =? 0)%nat then
     Scan (scan_valid st) (scan_padding st) (S (scan_symbols st)) (bit_step (scan_bits st) d)
   else Scan false (scan_padding st) (scan_symbols st) (scan_bits st)
 | None => Scan false (scan_padding st) (scan_symbols st) (scan_bits st)
 end.
Definition scan chars := fold_left scan_step chars initial_scan.
Lemma scan_snoc chars ch : scan (chars ++ [ch]) = scan_step (scan chars) ch.
Proof. unfold scan. rewrite fold_left_app. reflexivity. Qed.
Lemma invalid_scan_step st ch : scan_valid st = false -> scan_valid (scan_step st ch) = false.
Proof.
 unfold scan_step; intros H; destruct (ch =? 61); simpl; [exact H|].
 destruct (digit_value ch); [destruct (scan_padding st =? 0)%nat|]; simpl; auto.
Qed.
Lemma scan_parser chars :
 match read_symbols chars with
 | None => scan_valid (scan chars) = false
 | Some (ds,pad) => scan_valid (scan chars) = true /\
   scan_padding (scan chars) = pad /\ scan_symbols (scan chars) = length ds /\
   scan_bits (scan chars) = bit_run ds 0 0
 end.
Proof.
 induction chars as [|ch chars IH] using rev_ind; [repeat split; reflexivity|].
 rewrite scan_snoc.
 destruct (read_symbols chars) as [[ds pad]|] eqn:Hr.
 - rewrite (read_symbols_snoc _ ch _ _ Hr).
   destruct IH as [Hv [Hp [Hs Hb]]]. unfold scan_step.
   rewrite Hp. destruct (ch =? 61) eqn:Hch; simpl; [auto|].
   destruct (pad =? 0)%nat eqn:Hpad; destruct (digit_value ch) eqn:Hd; simpl; auto.
   rewrite bit_run_snoc. rewrite length_app. simpl. apply Nat.eqb_eq in Hpad.
   repeat split; auto; [lia|rewrite Hb; reflexivity].
 - rewrite (read_symbols_invalid_snoc _ ch Hr). apply invalid_scan_step. exact IH.
Qed.
Definition finish_scan (chars : list Z) st : option (list Z) :=
 if scan_valid st then
 let residue := (scan_symbols st mod 8)%nat in
 if ((residue =? 1) || (residue =? 3) || (residue =? 6))%nat then None else
 if (scan_padding st =? 0)%nat ||
   (((length chars mod 8 =? 0) && (1 <=? scan_padding st) && (scan_padding st <=? 6))%nat) then
 if ((1 <=? length (emitted (scan_bits st))) &&
   (length (emitted (scan_bits st)) <=? 128))%nat && (accumulator (scan_bits st) =? 0)
 then Some (emitted (scan_bits st)) else None
 else None else None.
Theorem scan_decode chars :
 decode chars =
 if ((2 <=? length chars) && (length chars <=? 208))%nat
 then finish_scan chars (scan chars) else None.
Proof.
 unfold decode. destruct ((2 <=? length chars) && (length chars <=? 208))%nat; [|reflexivity].
 pose proof (scan_parser chars) as H.
 unfold finish_scan. destruct (read_symbols chars) as [[ds pad]|] eqn:Hr.
 - destruct H as [Hv [Hp [Hs Hb]]]. rewrite Hv, Hp, Hs, Hb.
   pose proof (bit_run_values ds 0 0) as Hdecode.
   destruct (bit_run ds 0 0) as [out acc bits]. simpl in Hdecode |- *.
   rewrite <- Hdecode. reflexivity.
 - rewrite H. reflexivity.
Qed.
Lemma bit_step_bounds st d :
 0 <= bit_count st < 8 -> 0 <= accumulator st < 2^(bit_count st) -> 0 <= d < 32 ->
 0 <= bit_count (bit_step st d) < 8 /\
 0 <= accumulator (bit_step st d) < 2^(bit_count (bit_step st d)).
Proof.
 destruct st as [out acc bits]; simpl. intros Hbits Hacc Hd.
 assert (Hnext : 0 <= acc*32+d < 2^(bits+5)).
 { rewrite Z.pow_add_r by lia. change (2^5) with 32. nia. }
 unfold bit_step; simpl. destruct (bits+5 <? 8) eqn:Hw; simpl.
 - apply Z.ltb_lt in Hw. split; lia.
 - apply Z.ltb_ge in Hw. split; [lia|].
   apply Z.rem_bound_pos; [lia|apply Z.pow_pos_nonneg; lia].
Qed.
Lemma bit_step_emitted_length st d :
 (length (emitted (bit_step st d)) <= S (length (emitted st)))%nat.
Proof.
 unfold bit_step; destruct (bit_count st +5 <? 8); simpl; [lia|].
 rewrite length_app. simpl. lia.
Qed.
Lemma bit_run_bounds ds : Forall (fun d => 0 <= d < 32) ds ->
 0 <= bit_count (bit_run ds 0 0) < 8 /\
 0 <= accumulator (bit_run ds 0 0) < 2^(bit_count (bit_run ds 0 0)).
Proof.
 intros Hd. unfold bit_run.
 assert (H : forall st, 0 <= bit_count st < 8 -> 0 <= accumulator st < 2^(bit_count st) ->
  0 <= bit_count (fold_left bit_step ds st) < 8 /\
  0 <= accumulator (fold_left bit_step ds st) < 2^(bit_count (fold_left bit_step ds st))).
 { induction Hd as [|d ds Hd Hds IH]; intros st Hbits Hacc; simpl; [auto|].
   destruct (bit_step_bounds st d Hbits Hacc Hd) as [Hb Ha]. auto. }
 apply H; simpl; lia.
Qed.
Lemma bit_step_conservation st d :
 8 * Z.of_nat (length (emitted (bit_step st d))) + bit_count (bit_step st d) =
 8 * Z.of_nat (length (emitted st)) + bit_count st + 5.
Proof.
 unfold bit_step. destruct (bit_count st +5 <? 8); cbn [emitted bit_count]; [lia|].
 rewrite length_app, Nat2Z.inj_add. change (Z.of_nat (length [_])) with 1. lia.
Qed.
Lemma scan_step_bits st ch :
 0 <= bit_count (scan_bits st) < 8 ->
 0 <= accumulator (scan_bits st) < 2^(bit_count (scan_bits st)) ->
 0 <= bit_count (scan_bits (scan_step st ch)) < 8 /\
 0 <= accumulator (scan_bits (scan_step st ch)) < 2^(bit_count (scan_bits (scan_step st ch))).
Proof.
 intros Hb Ha. unfold scan_step. destruct (ch =? 61); simpl; [auto|].
 destruct (digit_value ch) eqn:Hd; [destruct (scan_padding st =? 0)%nat|]; simpl; auto.
 apply bit_step_bounds; auto. eapply digit_value_range; eauto.
Qed.
Lemma scan_bounds chars :
 (scan_symbols (scan chars) + scan_padding (scan chars) <= length chars)%nat /\
 0 <= bit_count (scan_bits (scan chars)) < 8 /\
 0 <= accumulator (scan_bits (scan chars)) < 2^(bit_count (scan_bits (scan chars))) /\
 8 * Z.of_nat (length (emitted (scan_bits (scan chars)))) + bit_count (scan_bits (scan chars)) =
 5 * Z.of_nat (scan_symbols (scan chars)).
Proof.
 induction chars as [|ch chars IH] using rev_ind; [repeat split; simpl; lia|].
 rewrite scan_snoc. destruct IH as [Hlength [Hb [Ha Hcount]]].
 destruct (scan_step_bits _ ch Hb Ha) as [Hb' Ha'].
 split.
 - unfold scan_step. rewrite length_app. simpl.
   destruct (ch =? 61); simpl; [lia|].
   destruct (digit_value ch); [destruct (scan_padding (scan chars) =? 0)%nat|]; simpl; lia.
 - split; [exact Hb'|]. split; [exact Ha'|].
   unfold scan_step. destruct (ch =? 61); cbn [scan_bits scan_symbols]; [exact Hcount|].
   destruct (digit_value ch); [destruct (scan_padding (scan chars) =? 0)%nat|]; cbn [scan_bits scan_symbols];
     try exact Hcount.
   rewrite bit_step_conservation, Nat2Z.inj_succ. lia.
Qed.
Corollary scan_scratch_capacity chars : (length chars <= 208)%nat ->
 (length (emitted (scan_bits (scan chars))) <= 130)%nat.
Proof. intros Hlen. destruct (scan_bounds chars) as [Hs [Hb [Ha Hcount]]]. lia. Qed.
Corollary scan_scratch_next chars : (length chars < 208)%nat ->
 (length (emitted (scan_bits (scan chars))) < 130)%nat.
Proof. intros Hlen. destruct (scan_bounds chars) as [Hs [Hb [Ha Hcount]]]. lia. Qed.
Lemma base32_factor bits : 8 <= bits <= 12 ->
 (if bits =? 8 then 1 else if bits =? 9 then 2 else if bits =? 10 then 4
  else if bits =? 11 then 8 else 16) = 2^(bits-8).
Proof.
 intros Hb. assert (bits=8 \/ bits=9 \/ bits=10 \/ bits=11 \/ bits=12) by lia.
 destruct H as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
Qed.
Lemma scan_native_bounds chars : (length chars <= 208)%nat ->
 0 <= accumulator (scan_bits (scan chars)) <= 127 /\
 0 <= bit_count (scan_bits (scan chars)) <= 7 /\
 (scan_symbols (scan chars) <= 208 /\ scan_padding (scan chars) <= 208)%nat.
Proof.
 intros Hlen. destruct (scan_bounds chars) as [Hlength [Hb [Ha Hcount]]].
 assert (Hpow : 2^(bit_count (scan_bits (scan chars))) <= 128).
 { change 128 with (2^7). apply Z.pow_le_mono_r; lia. }
 lia.
Qed.
