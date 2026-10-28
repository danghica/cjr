(** Canonical Base32 enrollment specification, independent of buffer layout. *)
From Coq Require Import ZArith List Lia Bool.
From cjr.authenticator Require Import model.
Import ListNotations.
Open Scope Z_scope.
Definition digit_value ch : option Z :=
 if (65 <=? ch) && (ch <=? 90) then Some (ch-65) else
 if (97 <=? ch) && (ch <=? 122) then Some (ch-97) else
 if (50 <=? ch) && (ch <=? 55) then Some (ch-24) else None.
Fixpoint read_symbols chars : option (list Z * nat) :=
 match chars with
 | [] => Some ([],0%nat)
 | ch::rest => if ch =? 61 then
     if forallb (fun x => x =? 61) rest then Some ([], S (length rest)) else None
   else match digit_value ch, read_symbols rest with
   | Some d, Some (ds,pad) => Some (d::ds,pad)
   | _,_ => None end
 end.
Fixpoint decode_values ds acc bits : list Z * Z :=
 match ds with
 | [] => ([],acc)
 | d::rest => let next := acc*32+d in let width := bits+5 in
   if width <? 8 then decode_values rest next width else
   let factor := 2^(width-8) in
   let '(out,tail) := decode_values rest (Z.rem next factor) (width-8) in
   (Z.quot next factor :: out,tail)
 end.
Definition decode chars : option (list Z) :=
 if ((2 <=? length chars) && (length chars <=? 208))%nat then
 match read_symbols chars with
 | None => None
 | Some (ds,pad) =>
   let residue := (length ds mod 8)%nat in
   if ((residue =? 1) || (residue =? 3) || (residue =? 6))%nat then None else
   if (pad =? 0)%nat || (((length chars mod 8 =? 0) && (1 <=? pad) && (pad <=? 6))%nat) then
   let '(out,tail) := decode_values ds 0 0 in
   if ((1 <=? length out) && (length out <=? 128))%nat && (tail =? 0) then Some out else None
   else None
 end else None.
Lemma digit_value_range ch d : digit_value ch = Some d -> 0 <= d < 32.
Proof.
 unfold digit_value.
 destruct ((65 <=? ch) && (ch <=? 90)) eqn:H1.
 - apply andb_true_iff in H1 as [Hlo Hhi]. apply Z.leb_le in Hlo,Hhi. intros H; inversion H; lia.
 - destruct ((97 <=? ch) && (ch <=? 122)) eqn:H2.
   + apply andb_true_iff in H2 as [Hlo Hhi]. apply Z.leb_le in Hlo,Hhi. intros H; inversion H; lia.
   + destruct ((50 <=? ch) && (ch <=? 55)) eqn:H3; [|discriminate].
     apply andb_true_iff in H3 as [Hlo Hhi]. apply Z.leb_le in Hlo,Hhi. intros H; inversion H; lia.
Qed.
Lemma read_symbols_range chars ds pad : read_symbols chars = Some (ds,pad) -> Forall (fun d => 0 <= d < 32) ds.
Proof.
 revert ds pad. induction chars as [|ch rest IH]; intros ds pad; simpl.
 - intros H; inversion H; constructor.
 - destruct (ch =? 61).
   + destruct (forallb (fun x => x =? 61) rest); intros H; inversion H; constructor.
   + destruct (digit_value ch) as [d|] eqn:Hd; [|discriminate].
     destruct (read_symbols rest) as [[values padding]|] eqn:Hr; [|discriminate].
     intros H; inversion H; subst. constructor; [eapply digit_value_range; eauto|eapply IH; eauto].
Qed.
Lemma decode_values_bytes ds acc bits : Forall (fun d => 0 <= d < 32) ds ->
 0 <= bits < 8 -> 0 <= acc < 2^bits -> Forall byte (fst (decode_values ds acc bits)).
Proof.
 intros Hds. revert acc bits. induction Hds as [|d ds Hd Hds IH]; intros acc bits Hbits Hacc; simpl.
 - constructor.
 - assert (Hnext : 0 <= acc*32+d < 2^(bits+5)).
   { rewrite Z.pow_add_r by lia. change (2^5) with 32. nia. }
   destruct (bits+5 <? 8) eqn:Hw.
   + apply Z.ltb_lt in Hw. apply IH; lia.
   + apply Z.ltb_ge in Hw.
     assert (Hfactor : 0 < 2^(bits+5-8)) by (apply Z.pow_pos_nonneg; lia).
     assert (Hrem := Z.rem_bound_pos (acc*32+d) (2^(bits+5-8)) ltac:(lia) Hfactor).
     specialize (IH (Z.rem (acc*32+d) (2^(bits+5-8))) (bits+5-8) ltac:(lia) Hrem).
     destruct (decode_values ds (Z.rem (acc*32+d) (2^(bits+5-8))) (bits+5-8)) as [out tail] eqn:E.
     simpl in *. constructor; [|exact IH]. unfold byte.
     rewrite Z.quot_div_nonneg by lia. split; [apply Z.div_pos; lia|].
     apply Z.div_lt_upper_bound; [exact Hfactor|].
     assert (Heq : bits+5 = (bits+5-8)+8) by lia. rewrite Heq in Hnext.
     rewrite Z.pow_add_r in Hnext by lia. change (2^8) with 256 in Hnext. nia.
Qed.
Theorem decode_bytes chars out : decode chars = Some out -> Forall byte out.
Proof.
 unfold decode. destruct ((2 <=? length chars) && (length chars <=? 208))%nat; [|discriminate].
 destruct (read_symbols chars) as [[ds pad]|] eqn:Hread; [|discriminate].
 destruct (((length ds mod 8 =? 1) || (length ds mod 8 =? 3) || (length ds mod 8 =? 6))%nat); [discriminate|].
 destruct ((pad =? 0)%nat || ((length chars mod 8 =? 0) && (1 <=? pad) && (pad <=? 6))%nat); [|discriminate].
 pose proof (decode_values_bytes ds 0 0 (read_symbols_range _ _ _ Hread) ltac:(lia) ltac:(simpl; lia)) as Hb.
 destruct (decode_values ds 0 0) as [values tail]. simpl in Hb.
 destruct (((1 <=? length values) && (length values <=? 128))%nat && (tail =? 0)); [|discriminate].
 intros H; inversion H; subst. exact Hb.
Qed.
Example decode_f : decode [77;89;61;61;61;61;61;61] = Some [102].
Proof. vm_compute. reflexivity. Qed.
Example decode_foobar : decode [77;90;88;87;54;89;84;66;79;73] = Some [102;111;111;98;97;114].
Proof. vm_compute. reflexivity. Qed.
Example reject_noncanonical_tail : decode [77;90] = None.
Proof. vm_compute. reflexivity. Qed.
Example reject_padding_middle : decode [77;89;61;65;65;65;65;65] = None.
Proof. vm_compute. reflexivity. Qed.
