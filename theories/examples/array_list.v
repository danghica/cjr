(** Resizable arrays, lowered from Cangjie [ArrayList] to monomorphic [Int64].

The buffer is the array library: a final object holding a capacity and a pointer
to a raw block of that many words. The list object holds that buffer, the live
length, and a version. The live prefix is the mathematical list; the tail is
zero, which is what [Alloc] writes and what [remove] writes back.

[Alloc] of zero words is stuck, so the only constructor is the default one,
capacity 16. There is no shift, so [grow] doubles with addition. There are no
exceptions: an index outside [0, size) reduces to [Load] of a non-pointer,
which has no step, and every specification takes the in-range arm.
[set] does not bump the version; [add] and [remove] do. The old block is
dropped on [grow]: the source relies on collection, which this language does
not have. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import array.
From iris.prelude Require Import options.
From Coq Require Import Lia.
Close Scope expr_scope.

Definition default_capacity : nat := 16.

Definition al_set (xs : list Z) (i : nat) (x : Z) : list Z := <[i := x]> xs.
Definition al_add (xs : list Z) (x : Z) : list Z := xs ++ [x].
Definition al_remove (xs : list Z) (i : nat) : list Z := take i xs ++ drop (S i) xs.

Definition doubled (cap : nat) : nat := (cap + cap)%nat.
Definition grow_cap (cap minCap : nat) : nat :=
  if decide (minCap ≤ doubled cap)%nat then doubled cap else minCap.
Definition add_cap (cap n : nat) : nat :=
  if decide (n < cap)%nat then cap else grow_cap cap (S n).

Definition slots_of (xs : list Z) (cap : nat) : list Z :=
  xs ++ replicate (cap - length xs)%nat 0%Z.

Definition overwrite (dst : list Z) (at_ : nat) (chunk : list Z) : list Z :=
  take at_ dst ++ chunk ++ drop (at_ + length chunk)%nat dst.

Definition shift_from (xs : list Z) (doff i len : nat) : list Z :=
  take (doff + i) xs ++
  take (len - i) (drop (doff + i + 1) xs) ++
  drop (doff + len) xs.

Lemma al_add_lookup_new (xs : list Z) (x : Z) :
  (xs ++ [x]) !! length xs = Some x.
Proof. rewrite lookup_app_r; [|lia]. by rewrite Nat.sub_diag. Qed.

Lemma al_add_lookup_old (xs : list Z) (x : Z) (i : nat) :
  (i < length xs)%nat → (xs ++ [x]) !! i = xs !! i.
Proof. intros. by rewrite lookup_app_l. Qed.

Lemma al_add_length (xs : list Z) (x : Z) : length (xs ++ [x]) = S (length xs).
Proof. rewrite length_app /=. lia. Qed.

Lemma al_set_lookup (xs : list Z) (i : nat) (x y : Z) :
  xs !! i = Some y → <[i := x]> xs !! i = Some x.
Proof. intros. apply list_lookup_insert. by eapply lookup_lt_Some. Qed.

Lemma al_set_lookup_ne (xs : list Z) (i j : nat) (x y : Z) :
  i ≠ j → xs !! j = Some y → <[i := x]> xs !! j = Some y.
Proof. intros. by rewrite list_lookup_insert_ne. Qed.

Lemma al_set_length (xs : list Z) (i : nat) (x : Z) :
  length (<[i := x]> xs) = length xs.
Proof. apply length_insert. Qed.

Lemma al_remove_length (xs : list Z) (i : nat) :
  (i < length xs)%nat → length (al_remove xs i) = (length xs - 1)%nat.
Proof.
  intros. rewrite /al_remove length_app length_take length_drop. lia.
Qed.

Lemma al_remove_lookup_left (xs : list Z) (i j : nat) :
  (j < i)%nat → (i < length xs)%nat → al_remove xs i !! j = xs !! j.
Proof.
  intros. rewrite /al_remove lookup_app_l.
  - by rewrite lookup_take.
  - rewrite length_take. lia.
Qed.

Lemma al_remove_lookup_right (xs : list Z) (i j : nat) :
  (i ≤ j)%nat → (j < length xs - 1)%nat → (i < length xs)%nat →
  al_remove xs i !! j = xs !! S j.
Proof.
  intros Hij Hj Hi.
  rewrite /al_remove lookup_app_r.
  - rewrite length_take_le; last lia. rewrite lookup_drop.
    replace (S i + (j - i))%nat with (S j) by lia. done.
  - rewrite length_take_le; lia.
Qed.

Lemma al_remove_snoc (xs : list Z) (x : Z) :
  al_remove (xs ++ [x]) (length xs) = xs.
Proof.
  rewrite /al_remove take_app_length.
  rewrite drop_ge; last first.
  { rewrite length_app /=. lia. }
  by rewrite app_nil_r.
Qed.

Lemma grow_cap_pos cap minCap :
  (0 < cap)%nat → (0 < minCap)%nat → (0 < grow_cap cap minCap)%nat.
Proof. intros. rewrite /grow_cap /doubled. case_decide; lia. Qed.

Lemma grow_cap_ge cap minCap n :
  (n ≤ cap)%nat → (n ≤ minCap)%nat → (n ≤ grow_cap cap minCap)%nat.
Proof. intros. rewrite /grow_cap /doubled. case_decide; lia. Qed.

Lemma grow_cap_double cap :
  (0 < cap)%nat → grow_cap cap (S cap) = doubled cap.
Proof. intros. rewrite /grow_cap /doubled decide_True; lia. Qed.

Lemma add_cap_room cap n : (n < cap)%nat → add_cap cap n = cap.
Proof. intros. by rewrite /add_cap decide_True. Qed.

Lemma add_cap_full cap : (0 < cap)%nat → add_cap cap cap = doubled cap.
Proof.
  intros. rewrite /add_cap decide_False; last lia. by apply grow_cap_double.
Qed.

Lemma slots_length (xs : list Z) (cap : nat) :
  (length xs ≤ cap)%nat → length (slots_of xs cap) = cap.
Proof. intros. rewrite /slots_of length_app length_replicate. lia. Qed.

Lemma slots_lookup_prefix (xs : list Z) (cap i : nat) (x : Z) :
  (length xs ≤ cap)%nat → xs !! i = Some x → slots_of xs cap !! i = Some x.
Proof.
  intros. rewrite /slots_of lookup_app_l //. by eapply lookup_lt_Some.
Qed.

Lemma slots_lookup_zero (xs : list Z) (cap i : nat) :
  (length xs ≤ i)%nat → (i < cap)%nat → slots_of xs cap !! i = Some 0%Z.
Proof.
  intros. rewrite /slots_of lookup_app_r; last lia.
  apply lookup_replicate. split; [done|lia].
Qed.

Lemma slots_set (xs : list Z) (cap i : nat) (x : Z) :
  (i < length xs)%nat → (length xs ≤ cap)%nat →
  slots_of (<[i := x]> xs) cap = <[i := x]> (slots_of xs cap).
Proof.
  intros Hi Hle. rewrite /slots_of length_insert. by rewrite -insert_app_l.
Qed.

Lemma slots_snoc (xs : list Z) (cap : nat) (x : Z) :
  (length xs < cap)%nat →
  slots_of (xs ++ [x]) cap = <[length xs := x]> (slots_of xs cap).
Proof.
  intros Hlt. rewrite /slots_of length_app /=.
  rewrite insert_app_r_alt; [|lia]. rewrite Nat.sub_diag.
  destruct (cap - length xs)%nat as [|m] eqn:Hm; [lia|].
  simpl. replace (cap - (length xs + 1))%nat with m by lia.
  by rewrite -app_assoc.
Qed.

Lemma overwrite_nil (dst : list Z) (at_ : nat) :
  (at_ ≤ length dst)%nat → overwrite dst at_ [] = dst.
Proof.
  intros. rewrite /overwrite /= Nat.add_0_r. by rewrite take_drop.
Qed.

Lemma overwrite_cons (dst : list Z) (at_ : nat) (sv : Z) (rest : list Z) :
  (at_ < length dst)%nat →
  overwrite dst at_ (sv :: rest) =
    overwrite (<[at_ := sv]> dst) (S at_) rest.
Proof.
  intros Hlt. rewrite /overwrite /=.
  rewrite drop_insert_gt; last lia.
  rewrite take_insert_lt; last lia.
  destruct (lookup_lt_is_Some_2 dst at_ Hlt) as [d Hd].
  rewrite (take_S_r dst at_ d Hd).
  rewrite insert_app_r_alt; last by rewrite length_take_le; lia.
  rewrite length_take_le; last lia. rewrite Nat.sub_diag /=.
  change (sv :: rest ++ drop (at_ + S (length rest)) dst)
    with ([sv] ++ rest ++ drop (at_ + S (length rest)) dst).
  rewrite -app_assoc. f_equal.
  by replace (at_ + S (length rest))%nat with (S (at_ + length rest)) by lia.
Qed.

Lemma overwrite_replicate (n : nat) (xs : list Z) :
  (length xs ≤ n)%nat →
  overwrite (replicate n 0%Z) 0 xs = xs ++ replicate (n - length xs) 0%Z.
Proof.
  intros. rewrite /overwrite /= drop_replicate. done.
Qed.

Lemma shift_from_done (xs : list Z) (doff len : nat) :
  (doff + len ≤ length xs)%nat →
  shift_from xs doff len len = xs.
Proof.
  intros. rewrite /shift_from Nat.sub_diag /=. by rewrite take_drop.
Qed.

Lemma shift_from_length (xs : list Z) (doff i len : nat) :
  (i ≤ len)%nat → (doff + len < length xs)%nat →
  length (shift_from xs doff i len) = length xs.
Proof.
  intros Hi Hlt. rewrite /shift_from !length_app length_take length_drop length_take length_drop.
  lia.
Qed.

Lemma shift_from_step (xs : list Z) (doff i len : nat) (x : Z) :
  (i < len)%nat → (doff + len < length xs)%nat →
  xs !! (doff + i + 1) = Some x →
  shift_from xs doff i len = shift_from (<[doff + i := x]> xs) doff (S i) len.
Proof.
  intros Hi Hlt Hx.
  set (p := (doff + i)%nat).
  assert (xs !! (p + 1) = Some x) as Hx1.
  { by replace (p + 1)%nat with (doff + i + 1)%nat by lia. }
  rewrite /shift_from.
  replace (doff + S i)%nat with (S p) by lia.
  replace (doff + S i + 1)%nat with (p + 2)%nat by lia.
  replace (len - i)%nat with (S (len - S i)) by lia.
  replace (doff + i)%nat with p by lia.
  replace (doff + i + 1)%nat with (p + 1)%nat by lia.
  rewrite (drop_S xs x (p + 1) Hx1).
  replace (S (p + 1)) with (p + 2)%nat by lia.
  cbn [take].
  rewrite drop_insert_gt; last lia.
  rewrite drop_insert_gt; last lia.
  rewrite take_insert_lt; last lia.
  destruct (lookup_lt_is_Some_2 xs p) as [old Hp]; [lia|].
  rewrite (take_S_r xs p old Hp).
  rewrite insert_app_r_alt; last by rewrite length_take_le; lia.
  rewrite length_take_le; last lia. rewrite Nat.sub_diag /=.
  replace (S (p + 1)) with (p + 2)%nat by lia.
  by rewrite -app_assoc.
Qed.

Lemma remove_slots (xs : list Z) (cap at_ : nat) :
  (at_ < length xs)%nat → (length xs ≤ cap)%nat →
  let len := (length xs - at_ - 1)%nat in
  <[length xs - 1 := 0%Z]> (shift_from (slots_of xs cap) at_ 0 len)
    = slots_of (al_remove xs at_) cap.
Proof.
  intros Hat Hle. set (n := length xs). set (len := (n - at_ - 1)%nat).
  assert (at_ + len = n - 1)%nat as Hatlen by lia.
  rewrite /shift_from /slots_of /al_remove.
  rewrite !Nat.add_0_r Nat.sub_0_r.
  replace (at_ + 1)%nat with (S at_) by lia.
  rewrite Hatlen.
  rewrite take_app_le; last lia.
  rewrite (drop_app_le xs (replicate (cap - n) 0%Z) (S at_)); last lia.
  assert (length (drop (S at_) xs) = len) as Hdrop.
  { rewrite length_drop. lia. }
  rewrite (take_app_length' (drop (S at_) xs) (replicate (cap - n) 0%Z) len).
  2: { exact (eq_sym Hdrop). }
  rewrite (drop_app_le xs (replicate (cap - n) 0%Z) (n - 1)); last lia.
  destruct (lookup_lt_is_Some_2 xs (n - 1)) as [last Hlast]; [lia|].
  rewrite (drop_S xs last (n - 1) Hlast).
  replace (S (n - 1)) with n by lia. rewrite drop_all. simpl.
  rewrite insert_app_r_alt.
  2: { rewrite length_take_le; lia. }
  rewrite length_take_le; [|lia].
  replace (n - 1 - at_)%nat with (length (drop (S at_) xs)).
  2: { rewrite length_drop. lia. }
  rewrite insert_app_r_alt; [|lia].
  rewrite Nat.sub_diag. simpl.
  rewrite -app_assoc. f_equal.
  replace (cap - length (take at_ xs ++ drop (S at_) xs))%nat with (S (cap - n))%nat.
  2: { rewrite length_app length_take_le ?length_drop; lia. }
  rewrite replicate_S. done.
Qed.

Lemma nat_decide_eq_refl {A} (a b : A) :
  (if decide (0 = 0)%nat then a else b) = a.
Proof. case_decide; [done|lia]. Qed.

Lemma nat_decide_zero_succ {A} (a b : A) (n : nat) :
  (if decide (0 = S n)%nat then a else b) = b.
Proof. case_decide; [lia|done]. Qed.

Lemma nat_decide_succ_ne {A} (a b : A) (k : nat) :
  (if decide (S k = 0)%nat then a else b) = b.
Proof. case_decide; [lia|done]. Qed.

Lemma decide_succ_eq {A} (a b : A) (k wi : nat) :
  (if decide (S k = S wi)%nat then a else b) =
  (if decide (k = wi)%nat then a else b).
Proof. case_decide; case_decide; intuition lia. Qed.

Lemma grow_cap_Z cap minCap :
  (if decide (Z.of_nat minCap ≤ Z.of_nat (doubled cap))%Z
   then Z.of_nat (doubled cap) else Z.of_nat minCap)
  = Z.of_nat (grow_cap cap minCap).
Proof.
  rewrite /grow_cap /doubled.
  destruct (decide (minCap ≤ cap + cap)%nat);
    destruct (decide (Z.of_nat minCap ≤ Z.of_nat (cap + cap))%Z); lia.
Qed.

Open Scope expr_scope.

Section array_list.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Definition is_buf (slots : list Z) (buf : val_cjr) : iProp Σ :=
    ∃ o base, ⌜ buf = LitV (LitObj o) ⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitInt (Z.of_nat (length slots))) ∗
      ObjId o ↦ₒ[1] LitV (LitPtr base) ∗
      RawId base ↦ᵦ length slots ∗
      array_cells base slots.

  Definition is_arraylist (xs : list Z) (cap : nat) (ver : Z) (a : val_cjr) : iProp Σ :=
    ∃ o buf, ⌜ a = LitV (LitObj o) ⌝ ∗
      ⌜ (length xs ≤ cap)%nat ⌝ ∗
      ⌜ (0 < cap)%nat ⌝ ∗
      ObjId o ↦ₒ[0] buf ∗
      ObjId o ↦ₒ[1] LitV (LitInt (Z.of_nat (length xs))) ∗
      ObjId o ↦ₒ[2] LitV (LitInt ver) ∗
      is_buf (slots_of xs cap) buf.

  Definition oob : expr := Load (Val (LitV LitUnit)).

  Definition sload (li : Z) : expr := StackLoad (Val (LitV (LitStack li))).

  Definition copy_vars : expr :=
    While
      ((Var "i" + Val (LitV (LitInt 1))) ≤ Var "len")
      (Seq
        (Store
          (Offset (Var "dst") (Var "i" + Var "doff"))
          (Load (Offset (Var "src") (Var "i" + Var "soff"))))
        (Assign "i" (Var "i" + Val (LitV (LitInt 1))))).

  Definition copy_open (src dst soff doff len : Z) : expr :=
    subst "len" (LitV (LitInt len))
      (subst "doff" (LitV (LitInt doff))
        (subst "soff" (LitV (LitInt soff))
          (subst "dst" (LitV (LitPtr dst))
            (subst "src" (LitV (LitPtr src)) copy_vars)))).

  Definition copy_cond (li len : Z) : expr :=
    (sload li + Val (LitV (LitInt 1))) ≤ Val (LitV (LitInt len)).

  Definition copy_step (li src dst soff doff : Z) : expr :=
    Seq
      (Store
        (Offset (Val (LitV (LitPtr dst))) (sload li + Val (LitV (LitInt doff))))
        (Load (Offset (Val (LitV (LitPtr src))) (sload li + Val (LitV (LitInt soff))))))
      (StackAssign (Val (LitV (LitStack li))) (sload li + Val (LitV (LitInt 1)))).

  Definition copy_while (li src dst soff doff len : Z) : expr :=
    While (copy_cond li len) (copy_step li src dst soff doff).

  Lemma copy_while_eq li src dst soff doff len :
    subst_var "i" li (copy_open src dst soff doff len) =
    copy_while li src dst soff doff len.
  Proof. reflexivity. Qed.

  Lemma wp_new_step vs v es Φ :
    WP New (vs ++ [v]) es {{ Φ }} ⊢ WP New vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (New (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_struct_step vs v es Φ :
    WP Struct (vs ++ [v]) es {{ Φ }} ⊢ WP Struct vs (Val v :: es) {{ Φ }}.
  Proof.
    iIntros "H".
    iApply wp_pure_step; [done| | |].
    { intros σ. eexists [], (Struct (vs ++ [v]) es), σ, []. constructor. }
    { intros ????? Hstep. inversion Hstep; simplify_eq; auto. }
    iIntros "!> _". iApply "H".
  Qed.

  Lemma wp_range_ok (n i : Z) (eok : expr) Φ :
    (0 ≤ i)%Z → (i < n)%Z →
    WP eok {{ Φ }} ⊢
    WP If (Val (LitV (LitInt n)) ≤ Val (LitV (LitInt i))) oob
         (If (Val (LitV (LitInt i)) ≤ Val (LitV (LitInt (Z.opp 1)))) oob eok) {{ Φ }}.
  Proof.
    iIntros (H0 Hi) "H".
    iApply (wp_bind [IfCtx oob
      (If (Val (LitV (LitInt i)) ≤ Val (LitV (LitInt (Z.opp 1)))) oob eok)]).
    iApply wp_binop.
    { simpl. rewrite bool_decide_eq_false_2; [reflexivity|lia]. }
    iIntros "!> _".
    iApply wp_if_false.
    iApply (wp_bind [IfCtx oob eok]).
    iApply wp_binop.
    { simpl. rewrite bool_decide_eq_false_2; [reflexivity|lia]. }
    iIntros "!> _".
    iApply wp_if_false. iApply "H".
  Qed.

  Lemma array_cells_cons base x xs :
    array_cells base (x :: xs) ⊣⊢
    RawId base ↦ᵣ LitV (LitInt x) ∗ array_cells (base + 1)%Z xs.
  Proof.
    rewrite /array_cells big_sepL_cons Z.add_0_r. f_equiv.
    apply big_sepL_proper. intros k y _.
    assert ((base + Z.of_nat (S k))%Z = (base + 1 + Z.of_nat k)%Z) as -> by lia.
    done.
  Qed.

  Lemma big_sepL_succ0_emp {A} (Φ : nat → A → iProp Σ) (xs : list A) :
    ([∗ list] k↦y ∈ xs, if decide (S k = 0)%nat then emp else Φ k y) ⊣⊢
    ([∗ list] k↦y ∈ xs, Φ k y).
  Proof.
    induction xs as [|z xs IH].
    - by rewrite !big_sepL_nil.
    - by rewrite !big_sepL_cons.
  Qed.

  Lemma big_sepL_shift_cells base xs :
    ([∗ list] k↦y ∈ xs, RawId (base + Z.of_nat (S k))%Z ↦ᵣ LitV (LitInt y)) ⊣⊢
    array_cells (base + 1)%Z xs.
  Proof.
    revert base. induction xs as [|z xs IH]; intros base.
    - by rewrite big_sepL_nil /array_cells big_sepL_nil.
    - rewrite big_sepL_cons array_cells_cons. apply bi.sep_proper.
      + assert ((base + Z.of_nat 1)%Z = (base + 1)%Z) as -> by lia. done.
      + etrans; [|apply IH]. apply big_sepL_proper. intros k y _.
        assert ((base + Z.of_nat (S (S k)))%Z =
                ((base + 1) + Z.of_nat (S k))%Z) as -> by lia. done.
  Qed.

  Lemma big_sepL_succ_index base xs wi :
    ([∗ list] k↦y ∈ xs, if decide (S k = S wi)%nat then emp else
        RawId (base + Z.of_nat (S k))%Z ↦ᵣ LitV (LitInt y)) ⊣⊢
    ([∗ list] k↦y ∈ xs, if decide (k = wi)%nat then emp else
        RawId ((base + 1) + Z.of_nat k)%Z ↦ᵣ LitV (LitInt y)).
  Proof.
    apply big_sepL_proper. intros k y _. case_decide; case_decide; try done; try lia.
    assert ((base + Z.of_nat (S k))%Z = ((base + 1) + Z.of_nat k)%Z) as -> by lia.
    done.
  Qed.

  Lemma if_decide_ne_elim (ri wi : nat) (Q : iProp Σ) :
    ri ≠ wi → (if decide (ri = wi) then emp else Q) ⊢ Q.
  Proof. intros. case_decide; [lia|done]. Qed.

  Lemma if_decide_ne_intro (ri wi : nat) (Q : iProp Σ) :
    ri ≠ wi → Q ⊢ (if decide (ri = wi) then emp else Q).
  Proof. intros. case_decide; [lia|done]. Qed.

  Lemma array_cells_replace base xs wi (y' : Z) :
    (wi < length xs)%nat →
    ([∗ list] k↦z ∈ xs, if decide (k = wi) then emp else
        RawId (base + Z.of_nat k)%Z ↦ᵣ LitV (LitInt z)) -∗
    RawId (base + Z.of_nat wi)%Z ↦ᵣ LitV (LitInt y') -∗
    array_cells base (<[wi := y']> xs).
  Proof.
    revert base wi. induction xs as [|z xs IH]; intros base [|wi] Hlt; simpl in Hlt.
    - lia.
    - lia.
    - rewrite big_sepL_cons. case_decide; last lia. simpl.
      rewrite array_cells_cons Z.add_0_r.
      iIntros "[_ Htail] Hw". iSplitL "Hw"; [done|].
      rewrite big_sepL_succ0_emp big_sepL_shift_cells. done.
    - rewrite big_sepL_cons. case_decide; first lia. simpl.
      rewrite array_cells_cons Z.add_0_r.
      iIntros "[Hz Htail] Hw". iSplitL "Hz"; [done|].
      rewrite big_sepL_succ_index.
      iApply (IH with "Htail [Hw]"); [lia|].
      assert ((base + Z.of_nat (S wi))%Z = ((base + 1) + Z.of_nat wi)%Z) as -> by lia.
      done.
  Qed.

  Lemma array_cells_read_update base xs ri wi x y y' :
    ri ≠ wi → xs !! ri = Some x → xs !! wi = Some y →
    array_cells base xs -∗
    RawId (base + Z.of_nat ri)%Z ↦ᵣ LitV (LitInt x) ∗
    RawId (base + Z.of_nat wi)%Z ↦ᵣ LitV (LitInt y) ∗
    (RawId (base + Z.of_nat ri)%Z ↦ᵣ LitV (LitInt x) -∗
     RawId (base + Z.of_nat wi)%Z ↦ᵣ LitV (LitInt y') -∗
     array_cells base (<[wi := y']> xs)).
  Proof.
    iIntros (Hne Hri Hwi) "H".
    rewrite {1}/array_cells (big_sepL_delete _ xs wi y Hwi).
    iDestruct "H" as "[Hwi Hrest]".
    iDestruct (big_sepL_lookup_acc _ xs ri with "Hrest") as "[Hri Hclose]"; first done.
    iPoseProof (if_decide_ne_elim ri wi with "Hri") as "Hri"; [done|].
    iFrame "Hri Hwi".
    iIntros "Hri Hwi".
    iSpecialize ("Hclose" with "[Hri]").
    { iApply if_decide_ne_intro; [done|done]. }
    iApply (array_cells_replace with "Hclose Hwi").
    by eapply lookup_lt_Some.
  Qed.

  Lemma wp_copy_iter li src dst soff doff len (i : Z) sv dv Φ :
    (i + 1 ≤ len)%Z →
    StackId li ↦ₛ LitV (LitInt i) -∗
    RawId (src + (soff + i))%Z ↦ᵣ LitV (LitInt sv) -∗
    RawId (dst + (doff + i))%Z ↦ᵣ LitV (LitInt dv) -∗
    (StackId li ↦ₛ LitV (LitInt (i + 1)) -∗
     RawId (src + (soff + i))%Z ↦ᵣ LitV (LitInt sv) -∗
     RawId (dst + (doff + i))%Z ↦ᵣ LitV (LitInt sv) -∗
     WP copy_while li src dst soff doff len {{ Φ }}) -∗
    WP copy_while li src dst soff doff len {{ Φ }}.
  Proof.
    iIntros (Hle) "Hi Hs Hd Hcont".
    rewrite /copy_while /copy_cond /copy_step /sload.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq
        (Seq
          (Store
            (Offset (Val (LitV (LitPtr dst)))
              (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt doff))))
            (Load
              (Offset (Val (LitV (LitPtr src)))
                (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt soff))))))
          (StackAssign (Val (LitV (LitStack li)))
            (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1)))))
        (While
          ((StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1)))
            ≤ Val (LitV (LitInt len)))
          (Seq
            (Store
              (Offset (Val (LitV (LitPtr dst)))
                (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt doff))))
              (Load
                (Offset (Val (LitV (LitPtr src)))
                  (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt soff))))))
            (StackAssign (Val (LitV (LitStack li)))
              (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1)))))))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt len)))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply wp_binop.
    { simpl. rewrite bool_decide_eq_true_2; [reflexivity|lia]. }
    iIntros "!> _".
    iApply wp_if_true.
    iApply (wp_bind [SeqCtx
      (While
        ((StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1)))
          ≤ Val (LitV (LitInt len)))
        (Seq
          (Store
            (Offset (Val (LitV (LitPtr dst)))
              (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt doff))))
            (Load
              (Offset (Val (LitV (LitPtr src)))
                (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt soff))))))
          (StackAssign (Val (LitV (LitStack li)))
            (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1))))))]).
    iApply (wp_bind [SeqCtx
      (StackAssign (Val (LitV (LitStack li)))
        (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt 1))))]).
    iApply (wp_bind [StoreLCtx
      (Load
        (Offset (Val (LitV (LitPtr src)))
          (StackLoad (Val (LitV (LitStack li))) + Val (LitV (LitInt soff)))))]).
    iApply (wp_bind [OffsetRCtx (LitV (LitPtr dst))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt doff)))]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply wp_offset. iIntros "!> _".
    assert ((dst + (i + doff))%Z = (dst + (doff + i))%Z) as -> by lia.
    iApply (wp_bind [StoreRCtx (LitV (LitPtr (dst + (doff + i))%Z))]).
    iApply (wp_bind [LoadCtx]).
    iApply (wp_bind [OffsetRCtx (LitV (LitPtr src))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt soff)))]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply wp_offset. iIntros "!> _".
    assert ((src + (i + soff))%Z = (src + (soff + i))%Z) as -> by lia.
    iApply (wp_load with "Hs").
    iIntros "!> _ Hs".
    iApply (wp_store with "Hd").
    iIntros "!> _ Hd".
    iApply wp_seq.
    iApply (wp_bind [StackAssignRCtx (LitV (LitStack li))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply (wp_stack_assign with "Hi").
    iIntros "!> _ Hi".
    iApply wp_seq.
    iApply ("Hcont" with "Hi Hs Hd").
  Qed.

  Lemma wp_copy_stop li src dst soff doff len (i : Z) Φ :
    ¬ (i + 1 ≤ len)%Z →
    StackId li ↦ₛ LitV (LitInt i) -∗
    (StackId li ↦ₛ LitV (LitInt i) -∗ Φ (LitV LitUnit)) -∗
    WP copy_while li src dst soff doff len {{ Φ }}.
  Proof.
    iIntros (Hle) "Hi HΦ".
    rewrite /copy_while /copy_cond /copy_step /sload.
    iApply wp_while.
    iApply (wp_bind [IfCtx
      (Seq (copy_step li src dst soff doff) (copy_while li src dst soff doff len))
      (Val (LitV LitUnit))]).
    iApply (wp_bind [BinOpLCtx LeOp (Val (LitV (LitInt len)))]).
    iApply (wp_bind [BinOpLCtx PlusOp (Val (LitV (LitInt 1)))]).
    iApply (wp_stack_load (StackId li) with "Hi").
    iIntros "!> _ Hi".
    iApply wp_binop; [simpl; reflexivity|].
    iIntros "!> _".
    iApply wp_binop.
    { simpl. rewrite bool_decide_eq_false_2; [reflexivity|lia]. }
    iIntros "!> _".
    iApply wp_if_false.
    iApply wp_value'.
    iApply ("HΦ" with "Hi").
  Qed.

  Lemma copy_disjoint_go (n : nat) li src dst (soff doff len i : nat)
      (srcSlots dstSlots : list Z) :
    (len - i = n)%nat →
    (i ≤ len)%nat →
    (soff + len ≤ length srcSlots)%nat →
    (doff + len ≤ length dstSlots)%nat →
    StackId li ↦ₛ LitV (LitInt (Z.of_nat i)) -∗
    array_cells src srcSlots -∗
    array_cells dst dstSlots -∗
    WP copy_while li src dst (Z.of_nat soff) (Z.of_nat doff) (Z.of_nat len)
    {{ v, ⌜ v = LitV LitUnit ⌝ ∗
          StackId li ↦ₛ LitV (LitInt (Z.of_nat len)) ∗
          array_cells src srcSlots ∗
          array_cells dst (overwrite dstSlots (doff + i)
            (take (len - i) (drop (soff + i) srcSlots))) }}.
  Proof.
    revert i dstSlots. induction n as [|n IH]; intros i dstSlots Heq Hi Hs Hd.
    - assert (i = len) as -> by lia.
      iIntros "Hi Hsrc Hdst".
      iApply (wp_copy_stop with "Hi").
      { lia. }
      iIntros "Hi".
      rewrite Nat.sub_diag take_0 overwrite_nil; last lia.
      iSplit; [done|]. iFrame.
    - assert (i < len)%nat as Hlt by lia.
      iIntros "Hi Hsrc Hdst".
      destruct (lookup_lt_is_Some_2 srcSlots (soff + i)) as [sv Hsv]; [lia|].
      destruct (lookup_lt_is_Some_2 dstSlots (doff + i)) as [dv Hdv]; [lia|].
      iDestruct (big_sepL_lookup_acc with "Hsrc") as "[Hs HsrcC]"; first exact Hsv.
      iDestruct (big_sepL_insert_acc with "Hdst") as "[Hd HdstC]"; first exact Hdv.
      assert ((src + Z.of_nat (soff + i))%Z =
              (src + (Z.of_nat soff + Z.of_nat i))%Z) as -> by lia.
      assert ((dst + Z.of_nat (doff + i))%Z =
              (dst + (Z.of_nat doff + Z.of_nat i))%Z) as -> by lia.
      iApply (wp_copy_iter with "Hi Hs Hd").
      { lia. }
      iIntros "Hi Hs Hd".
      assert ((Z.of_nat i + 1)%Z = Z.of_nat (S i)) as -> by lia.
      iDestruct ("HsrcC" with "Hs") as "Hsrc".
      iDestruct ("HdstC" $! sv with "Hd") as "Hdst".
      iApply (wp_wand with "[Hi Hsrc Hdst]").
      { iApply (IH (S i) (<[(doff + i)%nat := sv]> dstSlots) with "Hi Hsrc Hdst"); try lia.
        by rewrite length_insert. }
      iIntros (v) "(%Hv & Hi & Hsrc & Hdst)".
      iSplit; [done|]. iFrame "Hi Hsrc".
      assert (take (len - i) (drop (soff + i) srcSlots) =
              sv :: take (len - S i) (drop (soff + S i) srcSlots)) as Hchunk.
      { rewrite (drop_S _ sv _ Hsv).
        assert ((len - i)%nat = S (len - S i)) as -> by lia.
        cbn [take].
        by replace (S (soff + i))%nat with (soff + S i)%nat by lia. }
      rewrite Hchunk.
      rewrite (overwrite_cons dstSlots (doff + i)%nat sv _); last lia.
      by replace (S (doff + i)%nat) with ((doff + S i)%nat) by lia.
  Qed.

  Lemma copy_disjoint src dst (soff doff len : nat) srcSlots dstSlots :
    (soff + len ≤ length srcSlots)%nat →
    (doff + len ≤ length dstSlots)%nat →
    array_cells src srcSlots -∗
    array_cells dst dstSlots -∗
    WP VarBind "i" (Val (LitV (LitInt 0)))
         (copy_open src dst (Z.of_nat soff) (Z.of_nat doff) (Z.of_nat len))
    {{ v, ⌜ v = LitV LitUnit ⌝ ∗
          array_cells src srcSlots ∗
          array_cells dst (overwrite dstSlots doff (take len (drop soff srcSlots))) }}.
  Proof.
    iIntros (Hs Hd) "Hsrc Hdst".
    iApply wp_var_bind. iIntros (li) "Hi".
    rewrite copy_while_eq.
    iApply (wp_wand with "[Hi Hsrc Hdst]").
    { iApply (copy_disjoint_go (len - 0)%nat li src dst soff doff len 0%nat
        with "Hi Hsrc Hdst").
      - rewrite Nat.sub_0_r. done.
      - lia.
      - done.
      - done. }
    iIntros (v) "(%Hv & Hi & Hsrc & Hdst)".
    iExists (LitV (LitInt (Z.of_nat len))). iFrame "Hi".
    iSplit; [done|]. iFrame "Hsrc".
    iStopProof. rewrite !Nat.add_0_r Nat.sub_0_r. done.
  Qed.

  Lemma copy_shift_go (n : nat) li base (doff len i : nat) (xs : list Z) :
    (len - i = n)%nat →
    (i ≤ len)%nat →
    (doff + len < length xs)%nat →
    StackId li ↦ₛ LitV (LitInt (Z.of_nat i)) -∗
    array_cells base xs -∗
    WP copy_while li base base (Z.of_nat (doff + 1)) (Z.of_nat doff) (Z.of_nat len)
    {{ v, ⌜ v = LitV LitUnit ⌝ ∗
          StackId li ↦ₛ LitV (LitInt (Z.of_nat len)) ∗
          array_cells base (shift_from xs doff i len) }}.
  Proof.
    revert i xs. induction n as [|n IH]; intros i xs Heq Hi Hlt.
    - assert (i = len) as -> by lia.
      iIntros "Hi Hxs".
      iApply (wp_copy_stop with "Hi").
      { lia. }
      iIntros "Hi".
      rewrite shift_from_done; last lia.
      iSplit; [done|]. iFrame.
    - assert (i < len)%nat as Hlt' by lia.
      iIntros "Hi Hxs".
      destruct (lookup_lt_is_Some_2 xs (doff + i + 1)) as [sv Hsv]; [lia|].
      destruct (lookup_lt_is_Some_2 xs (doff + i)) as [dv Hdv]; [lia|].
      iDestruct (array_cells_read_update _ _ (doff + i + 1) (doff + i)
                   sv dv sv with "Hxs") as "(Hs & Hd & Hclose)"; [lia|done|done|].
      assert ((base + Z.of_nat (doff + i + 1))%Z =
              (base + (Z.of_nat (doff + 1) + Z.of_nat i))%Z) as -> by lia.
      assert ((base + Z.of_nat (doff + i))%Z =
              (base + (Z.of_nat doff + Z.of_nat i))%Z) as -> by lia.
      iApply (wp_copy_iter with "Hi Hs Hd").
      { lia. }
      iIntros "Hi Hs Hd".
      assert ((Z.of_nat i + 1)%Z = Z.of_nat (S i)) as -> by lia.
      iDestruct ("Hclose" with "Hs Hd") as "Hxs".
      iApply (wp_wand with "[Hi Hxs]").
      { iApply (IH (S i) (<[(doff + i)%nat := sv]> xs) with "Hi Hxs"); try lia.
        by rewrite length_insert. }
      iIntros (v) "(%Hv & Hi & Hxs)".
      iSplit; [done|]. iFrame "Hi".
      rewrite -(shift_from_step _ _ _ _ sv); [done|lia|lia|done].
  Qed.

  Lemma copy_shift base (doff len : nat) (xs : list Z) :
    (doff + len < length xs)%nat →
    array_cells base xs -∗
    WP VarBind "i" (Val (LitV (LitInt 0)))
         (copy_open base base (Z.of_nat (doff + 1)) (Z.of_nat doff) (Z.of_nat len))
    {{ v, ⌜ v = LitV LitUnit ⌝ ∗
          array_cells base (shift_from xs doff 0 len) }}.
  Proof.
    iIntros (Hlt) "Hxs".
    iApply wp_var_bind. iIntros (li) "Hi".
    rewrite copy_while_eq.
    iApply (wp_wand with "[Hi Hxs]").
    { iApply (copy_shift_go (len - 0)%nat li base doff len 0%nat
        with "Hi Hxs").
      - rewrite Nat.sub_0_r. done.
      - lia.
      - done. }
    iIntros (v) "(%Hv & Hi & Hxs)".
    iExists (LitV (LitInt (Z.of_nat len))). iFrame "Hi".
    iSplit; [done|]. iFrame.
  Qed.

  Definition init_body : expr :=
    Let (Some "p") (Alloc (Val (LitV (LitInt (Z.of_nat default_capacity)))))
      (Let (Some "buf")
        (New [] [Val (LitV (LitInt (Z.of_nat default_capacity))); Var "p"])
        (New [] [Var "buf"; Val (LitV (LitInt 0)); Val (LitV (LitInt 0))])).

  Definition call_init : expr :=
    App (Rec None None init_body) (Val (LitV LitUnit)).

  Definition size_body : expr := FieldLoad (Var "a") 1.
  Definition call_size (a : val_cjr) : expr :=
    App (Rec None (Some "a") size_body) (Val a).

  Definition capacity_body : expr :=
    Let (Some "buf") (FieldLoad (Var "a") 0) (FieldLoad (Var "buf") 0).
  Definition call_capacity (a : val_cjr) : expr :=
    App (Rec None (Some "a") capacity_body) (Val a).

  Definition version_body : expr := FieldLoad (Var "a") 2.
  Definition call_version (a : val_cjr) : expr :=
    App (Rec None (Some "a") version_body) (Val a).

  Definition is_empty_body : expr :=
    Let (Some "n") (FieldLoad (Var "a") 1)
      (BinOp EqOp (Var "n") (Val (LitV (LitInt 0)))).
  Definition call_is_empty (a : val_cjr) : expr :=
    App (Rec None (Some "a") is_empty_body) (Val a).

  Definition al_get_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
      (Let (Some "i") (StructLoad (Var "args") 1)
        (Let (Some "n") (FieldLoad (Var "a") 1)
          (If (Var "n" ≤ Var "i") oob
            (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
              (Let (Some "buf") (FieldLoad (Var "a") 0)
                (Let (Some "p") (FieldLoad (Var "buf") 1)
                  (Load (Offset (Var "p") (Var "i"))))))))).

  Definition call_al_get (a : val_cjr) (i : Z) : expr :=
    App (Rec None (Some "args") al_get_body)
      (Val (StructV [a; LitV (LitInt i)])).

  Definition al_set_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
      (Let (Some "i") (StructLoad (Var "args") 1)
        (Let (Some "x") (StructLoad (Var "args") 2)
          (Let (Some "n") (FieldLoad (Var "a") 1)
            (If (Var "n" ≤ Var "i") oob
              (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
                (Let (Some "buf") (FieldLoad (Var "a") 0)
                  (Let (Some "p") (FieldLoad (Var "buf") 1)
                    (Store (Offset (Var "p") (Var "i")) (Var "x"))))))))).

  Definition call_al_set (a : val_cjr) (i x : Z) : expr :=
    App (Rec None (Some "args") al_set_body)
      (Val (StructV [a; LitV (LitInt i); LitV (LitInt x)])).

  Lemma init_spec :
    ⊢ WP call_init {{ a, is_arraylist [] default_capacity 0 a }}.
  Proof.
    iApply (wp_bind [AppLCtx (Val (LitV LitUnit))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Let (Some "buf")
        (New [] [Val (LitV (LitInt (Z.of_nat default_capacity))); Var "p"])
        (New [] [Var "buf"; Val (LitV (LitInt 0)); Val (LitV (LitInt 0))]))]).
    iApply (wp_alloc (Z.of_nat default_capacity)).
    { unfold default_capacity. done. }
    iIntros (base) "Hcells".
    iIntros "Hblk".
    iEval (rewrite Nat2Z.id) in "Hblk".
    iEval (rewrite Nat2Z.id) in "Hcells".
    iPoseProof (seq_zero_cells with "Hcells") as "Hcells".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "buf")
      (New [] [Var "buf"; Val (LitV (LitInt 0)); Val (LitV (LitInt 0))])]).
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (ob) "Hb".
    iDestruct "Hb" as "[Hcap [Hptr _]]".
    iApply wp_let. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (o) "Ha".
    iDestruct "Ha" as "[Hbuf [Hsz [Hver _]]]".
    iExists o, (LitV (LitObj ob)). iSplit; [done|].
    iSplit. { iPureIntro. unfold default_capacity. cbn. lia. }
    iSplit. { iPureIntro. unfold default_capacity. cbn. lia. }
    iFrame "Hbuf Hsz Hver".
    iExists ob, base. iSplit; [done|].
    rewrite /slots_of /=. iFrame.
  Qed.

  Lemma size_spec xs cap ver (a : val_cjr) :
    is_arraylist xs cap ver a -∗
    WP call_size a
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs))) ⌝ ∗ is_arraylist xs cap ver a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz".
    iSplit; [done|]. iExists o, buf. iSplit; [done|]. iFrame. done.
  Qed.

  Lemma capacity_spec xs cap ver (a : val_cjr) :
    is_arraylist xs cap ver a -∗
    WP call_capacity a
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat cap)) ⌝ ∗ is_arraylist xs cap ver a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "buf") (FieldLoad (Var "buf") 0)]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf".
    iApply wp_let. simpl.
    iApply (wp_field_load with "Hcapf").
    iIntros "!> _ Hcapf".
    iSplit.
    { iPureIntro. rewrite (slots_length xs cap Hlen). done. }
    iExists o, (LitV (LitObj ob)). iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Hbuf Hsz Hver". iExists ob, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma version_spec xs cap ver (a : val_cjr) :
    is_arraylist xs cap ver a -∗
    WP call_version a
      {{ v, ⌜ v = LitV (LitInt ver) ⌝ ∗ is_arraylist xs cap ver a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_field_load with "Hver").
    iIntros "!> _ Hver".
    iSplit; [done|]. iExists o, buf. iSplit; [done|]. iFrame. done.
  Qed.

  Lemma is_empty_spec xs cap ver (a : val_cjr) :
    is_arraylist xs cap ver a -∗
    WP call_is_empty a
      {{ v, ⌜ v = LitV (LitBool (bool_decide (length xs = 0)%nat)) ⌝ ∗
            is_arraylist xs cap ver a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    iApply (wp_bind [AppLCtx (Val (LitV (LitObj o)))]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "n")
      (BinOp EqOp (Var "n") (Val (LitV (LitInt 0))))]).
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz".
    iApply wp_let. simpl.
    iApply wp_binop.
    { simpl.
      assert (bool_decide (Z.of_nat (length xs) = 0)%Z =
              bool_decide (length xs = 0)%nat) as ->.
      { apply bool_decide_ext. lia. }
      reflexivity. }
    iIntros "!> _".
    iSplit; [done|]. iExists o, buf. iSplit; [done|]. iFrame. done.
  Qed.

  Lemma al_get_spec xs cap ver (a : val_cjr) (i : nat) x :
    xs !! i = Some x →
    is_arraylist xs cap ver a -∗
    WP call_al_get a (Z.of_nat i)
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ is_arraylist xs cap ver a }}.
  Proof.
    iIntros (Hi) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i))]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "i") (StructLoad (Val arg) 1)
        (Let (Some "n") (FieldLoad (Var "a") 1)
          (If (Var "n" ≤ Var "i") oob
            (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
              (Let (Some "buf") (FieldLoad (Var "a") 0)
                (Let (Some "p") (FieldLoad (Var "buf") 1)
                  (Load (Offset (Var "p") (Var "i")))))))))]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "i")
      (Let (Some "n") (FieldLoad (Val (LitV (LitObj o))) 1)
        (If (Var "n" ≤ Var "i") oob
          (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
            (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
              (Let (Some "p") (FieldLoad (Var "buf") 1)
                (Load (Offset (Var "p") (Var "i"))))))))]).
    iApply (wp_struct_load _ 1 (LitV (LitInt (Z.of_nat i)))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "n")
      (If (BinOp LeOp (Var "n") (Val (LitV (LitInt (Z.of_nat i))))) oob
        (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat i)))) (Val (LitV (LitInt (Z.opp 1))))) oob
          (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
            (Let (Some "p") (FieldLoad (Var "buf") 1)
              (Load (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i))))))))))]).
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz".
    iApply wp_let. simpl.
    iApply wp_range_ok.
    { apply Nat2Z.is_nonneg. }
    { apply Nat2Z.inj_lt. eapply lookup_lt_Some. exact Hi. }
    iApply (wp_bind [LetCtx (Some "buf")
      (Let (Some "p") (FieldLoad (Var "buf") 1)
        (Load (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i)))))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Load (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i))))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr".
    iApply wp_let. simpl.
    iApply (wp_bind [LoadCtx]).
    iApply wp_offset. iIntros "!> _".
    iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hc Hclose]".
    { apply slots_lookup_prefix; [done|done]. }
    assert ((base + Z.of_nat i)%Z = (base + Z.of_nat i)%Z) as Heq by done.
    iApply (wp_load with "Hc").
    iIntros "!> _ Hc".
    iDestruct ("Hclose" with "Hc") as "Hcells".
    iSplit; [done|].
    iExists o, (LitV (LitObj ob)). iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Hbuf Hsz Hver". iExists ob, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma al_set_spec xs cap ver (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_arraylist xs cap ver a -∗
    WP call_al_set a (Z.of_nat i) x
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗ is_arraylist (al_set xs i x) cap ver a }}.
  Proof.
    iIntros (Hi) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb.
    assert (i < length xs)%nat as Hlt by (eapply lookup_lt_Some; exact Hi).
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat i)); LitV (LitInt x)]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "i") (StructLoad (Val arg) 1)
        (Let (Some "x") (StructLoad (Val arg) 2)
          (Let (Some "n") (FieldLoad (Var "a") 1)
            (If (Var "n" ≤ Var "i") oob
              (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
                (Let (Some "buf") (FieldLoad (Var "a") 0)
                  (Let (Some "p") (FieldLoad (Var "buf") 1)
                    (Store (Offset (Var "p") (Var "i")) (Var "x")))))))))]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "i")
      (Let (Some "x") (StructLoad (Val arg) 2)
        (Let (Some "n") (FieldLoad (Val (LitV (LitObj o))) 1)
          (If (Var "n" ≤ Var "i") oob
            (If (Var "i" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
              (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
                (Let (Some "p") (FieldLoad (Var "buf") 1)
                  (Store (Offset (Var "p") (Var "i")) (Var "x"))))))))]).
    iApply (wp_struct_load _ 1 (LitV (LitInt (Z.of_nat i)))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "x")
      (Let (Some "n") (FieldLoad (Val (LitV (LitObj o))) 1)
        (If (BinOp LeOp (Var "n") (Val (LitV (LitInt (Z.of_nat i))))) oob
          (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat i)))) (Val (LitV (LitInt (Z.opp 1))))) oob
            (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
              (Let (Some "p") (FieldLoad (Var "buf") 1)
                (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i))))) (Var "x")))))))]).
    iApply (wp_struct_load _ 2 (LitV (LitInt x))); [done|].
    iIntros "!> _".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "n")
      (If (BinOp LeOp (Var "n") (Val (LitV (LitInt (Z.of_nat i))))) oob
        (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat i)))) (Val (LitV (LitInt (Z.opp 1))))) oob
          (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
            (Let (Some "p") (FieldLoad (Var "buf") 1)
              (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i)))))
                (Val (LitV (LitInt x))))))))]).
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz".
    iApply wp_let. simpl.
    iApply wp_range_ok.
    { apply Nat2Z.is_nonneg. }
    { apply Nat2Z.inj_lt. exact Hlt. }
    iApply (wp_bind [LetCtx (Some "buf")
      (Let (Some "p") (FieldLoad (Var "buf") 1)
        (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i)))))
          (Val (LitV (LitInt x)))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Store (Offset (Var "p") (Val (LitV (LitInt (Z.of_nat i)))))
        (Val (LitV (LitInt x))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr".
    iApply wp_let. simpl.
    iApply (wp_bind [StoreLCtx (Val (LitV (LitInt x)))]).
    iApply wp_offset. iIntros "!> _".
    iDestruct (big_sepL_insert_acc with "Hcells") as "[Hc Hclose]".
    { apply slots_lookup_prefix; [done|done]. }
    iApply (wp_store with "Hc").
    iIntros "!> _ Hc".
    iDestruct ("Hclose" $! x with "Hc") as "Hcells".
    iSplit; [done|].
    unfold is_arraylist, is_buf.
    rewrite /al_set (slots_set xs cap i x); [|done|done].
    rewrite !length_insert.
    iExists o, (LitV (LitObj ob)). iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Hbuf Hsz Hver".
    iExists ob, base. iSplit; [done|]. iFrame.
  Qed.

  Definition copy_pending_dst (src len : Z) : expr :=
    subst "len" (LitV (LitInt len))
      (subst "doff" (LitV (LitInt 0))
        (subst "soff" (LitV (LitInt 0))
          (subst "src" (LitV (LitPtr src)) copy_vars))).

  Lemma copy_pending_eq src dst len :
    subst "dst" (LitV (LitPtr dst)) (copy_pending_dst src len) =
    copy_open src dst 0 0 len.
  Proof. reflexivity. Qed.

  Definition grow_alloc_e (ao : loc) (newCap src len : Z) : expr :=
    Let (Some "dst") (Alloc (Val (LitV (LitInt newCap))))
      (Let (Some "nb") (New [] [Val (LitV (LitInt newCap)); Var "dst"])
        (Let None
          (VarBind "i" (Val (LitV (LitInt 0))) (copy_pending_dst src len))
          (FieldStore (Val (LitV (LitObj ao))) 0 (Var "nb")))).

  Lemma grow_alloc_spec xs (cap newCap : nat) ver (ao : loc) (base : Z) (old : val) :
    (length xs ≤ cap)%nat → (length xs ≤ newCap)%nat → (0 < newCap)%nat →
    ObjId ao ↦ₒ[0] old -∗
    ObjId ao ↦ₒ[1] LitV (LitInt (Z.of_nat (length xs))) -∗
    ObjId ao ↦ₒ[2] LitV (LitInt ver) -∗
    array_cells base (slots_of xs cap) -∗
    WP grow_alloc_e ao (Z.of_nat newCap) base (Z.of_nat (length xs))
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗ is_arraylist xs newCap ver (LitV (LitObj ao)) }}.
  Proof.
    iIntros (Hle Hnew Hpos) "Hold Hsz Hver Hsrc".
    iApply (wp_bind [LetCtx (Some "dst")
      (Let (Some "nb") (New [] [Val (LitV (LitInt (Z.of_nat newCap))); Var "dst"])
        (Let None
          (VarBind "i" (Val (LitV (LitInt 0)))
            (copy_pending_dst base (Z.of_nat (length xs))))
          (FieldStore (Val (LitV (LitObj ao))) 0 (Var "nb"))))]).
    iApply (wp_alloc (Z.of_nat newCap)).
    { rewrite <- Nat2Z.inj_0. apply Nat2Z.inj_lt. exact Hpos. }
    iIntros (dst) "Hcells".
    iIntros "Hblk".
    iEval (rewrite Nat2Z.id) in "Hblk".
    iEval (rewrite Nat2Z.id) in "Hcells".
    iPoseProof (seq_zero_cells with "Hcells") as "Hdst".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "nb")
      (Let None
        (VarBind "i" (Val (LitV (LitInt 0)))
          (subst "dst" (LitV (LitPtr dst))
            (copy_pending_dst base (Z.of_nat (length xs)))))
        (FieldStore (Val (LitV (LitObj ao))) 0 (Var "nb")))]).
    iApply wp_new_step. simpl.
    iApply wp_new_step. simpl.
    iApply wp_new. iIntros (nb) "Hnb".
    iDestruct "Hnb" as "[Hcap [Hptr _]]".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx None
      (FieldStore (Val (LitV (LitObj ao))) 0 (Val (LitV (LitObj nb))))]).
    iApply (wp_wand with "[Hsrc Hdst]").
    { iApply (copy_disjoint base dst 0%nat 0%nat (length xs)
                (slots_of xs cap) (replicate newCap 0%Z) with "Hsrc Hdst").
      - rewrite (slots_length xs cap Hle). done.
      - rewrite length_replicate Nat.add_0_l. done. }
    iIntros (v) "(%Hv & Hsrc & Hdst)".
    rewrite Hv. iApply wp_let.
    iApply (wp_field_store with "Hold").
    iIntros "!> _ Hold".
    assert (overwrite (replicate newCap 0%Z) 0
              (take (length xs) (drop 0 (slots_of xs cap))) =
            slots_of xs newCap) as Heqslots.
    { rewrite drop_0 /slots_of take_app_length.
      rewrite overwrite_replicate; last done. done. }
    iEval (rewrite Heqslots) in "Hdst".
    iSplit; [done|].
    unfold is_arraylist, is_buf.
    iExists ao, (LitV (LitObj nb)). iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame "Hold Hsz Hver".
    iExists nb, dst. iSplit; [done|].
    rewrite (slots_length xs newCap Hnew). iFrame.
  Qed.

  Definition grow_open : expr :=
    Let (Some "dst") (Alloc (Var "newCap"))
      (Let (Some "nb") (New [] [Var "newCap"; Var "dst"])
        (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
          (FieldStore (Var "a") 0 (Var "nb")))).

  Arguments grow_open : simpl never.

  Definition ga_of (ao : loc) : expr :=
    subst "a" (LitV (LitObj ao)) grow_open.
  Definition g_new (ao : loc) (c : Z) : expr :=
    subst "newCap" (LitV (LitInt c)) (ga_of ao).
  Definition g_src (ao : loc) (c src : Z) : expr :=
    subst "src" (LitV (LitPtr src)) (g_new ao c).
  Definition g_len (ao : loc) (c src len : Z) : expr :=
    subst "len" (LitV (LitInt len)) (g_src ao c src).
  Definition g_soff (ao : loc) (c src len : Z) : expr :=
    subst "soff" (LitV (LitInt 0)) (g_len ao c src len).
  Definition g_doff (ao : loc) (c src len : Z) : expr :=
    subst "doff" (LitV (LitInt 0)) (g_soff ao c src len).

  Lemma drop_min (ao : loc) (w : val) :
    subst "min" w (ga_of ao) = ga_of ao.
  Proof. reflexivity. Qed.
  Lemma drop_buf (ao : loc) (w : val) :
    subst "buf" w (ga_of ao) = ga_of ao.
  Proof. reflexivity. Qed.
  Lemma drop_pcap (ao : loc) (w : val) :
    subst "pcap" w (ga_of ao) = ga_of ao.
  Proof. reflexivity. Qed.
  Lemma drop_doubled (ao : loc) (w : val) :
    subst "doubled" w (ga_of ao) = ga_of ao.
  Proof. reflexivity. Qed.

Lemma grow_open_eq (ao : loc) (newCap src len : Z) :
    subst "doff" (LitV (LitInt 0))
      (subst "soff" (LitV (LitInt 0))
        (subst "len" (LitV (LitInt len))
          (subst "src" (LitV (LitPtr src))
            (subst "newCap" (LitV (LitInt newCap))
              (subst "a" (LitV (LitObj ao)) grow_open))))) =
    grow_alloc_e ao newCap src len.
  Proof. reflexivity. Qed.

  Definition grow_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
      (Let (Some "min") (StructLoad (Var "args") 1)
        (Let (Some "buf") (FieldLoad (Var "a") 0)
          (Let (Some "pcap") (FieldLoad (Var "buf") 0)
            (Let (Some "doubled") (BinOp PlusOp (Var "pcap") (Var "pcap"))
              (Let (Some "newCap")
                (If (BinOp LeOp (Var "min") (Var "doubled"))
                  (Var "doubled") (Var "min"))
                (Let (Some "src") (FieldLoad (Var "buf") 1)
                  (Let (Some "len") (FieldLoad (Var "a") 1)
                    (Let (Some "soff") (Val (LitV (LitInt 0)))
                      (Let (Some "doff") (Val (LitV (LitInt 0))) grow_open))))))))).

  Definition call_grow (a : val_cjr) (minCap : Z) : expr :=
    App (Rec None (Some "args") grow_body)
      (Val (StructV [a; LitV (LitInt minCap)])).

  Lemma grow_spec xs cap ver (a : val_cjr) (minCap : nat) :
    (length xs ≤ minCap)%nat → (0 < minCap)%nat →
    is_arraylist xs cap ver a -∗
    WP call_grow a (Z.of_nat minCap)
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗
            is_arraylist xs (grow_cap cap minCap) ver a }}.
  Proof.
    iIntros (Hmin Hminpos) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat minCap))]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "min") (StructLoad (Val arg) 1)
        (Let (Some "buf") (FieldLoad (Var "a") 0)
          (Let (Some "pcap") (FieldLoad (Var "buf") 0)
            (Let (Some "doubled") (BinOp PlusOp (Var "pcap") (Var "pcap"))
              (Let (Some "newCap")
                (If (BinOp LeOp (Var "min") (Var "doubled"))
                  (Var "doubled") (Var "min"))
                (Let (Some "src") (FieldLoad (Var "buf") 1)
                  (Let (Some "len") (FieldLoad (Var "a") 1)
                    (Let (Some "soff") (Val (LitV (LitInt 0)))
                      (Let (Some "doff") (Val (LitV (LitInt 0))) grow_open)))))))))]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _". Opaque grow_open. iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "min")
      (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
        (Let (Some "pcap") (FieldLoad (Var "buf") 0)
          (Let (Some "doubled") (BinOp PlusOp (Var "pcap") (Var "pcap"))
            (Let (Some "newCap")
              (If (BinOp LeOp (Var "min") (Var "doubled"))
                (Var "doubled") (Var "min"))
              (Let (Some "src") (FieldLoad (Var "buf") 1)
                (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
                  (Let (Some "soff") (Val (LitV (LitInt 0)))
                    (Let (Some "doff") (Val (LitV (LitInt 0))) (ga_of o)))))))))]).
    iApply (wp_struct_load _ 1 (LitV (LitInt (Z.of_nat minCap)))); [done|].
    iIntros "!> _". iApply wp_let. simpl. rewrite drop_min.
    iApply (wp_bind [LetCtx (Some "buf")
      (Let (Some "pcap") (FieldLoad (Var "buf") 0)
        (Let (Some "doubled") (BinOp PlusOp (Var "pcap") (Var "pcap"))
          (Let (Some "newCap")
            (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat minCap)))) (Var "doubled"))
              (Var "doubled") (Val (LitV (LitInt (Z.of_nat minCap)))))
            (Let (Some "src") (FieldLoad (Var "buf") 1)
              (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
                (Let (Some "soff") (Val (LitV (LitInt 0)))
                  (Let (Some "doff") (Val (LitV (LitInt 0))) (ga_of o))))))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf". iApply wp_let. simpl. rewrite drop_buf.
    iApply (wp_bind [LetCtx (Some "pcap")
      (Let (Some "doubled") (BinOp PlusOp (Var "pcap") (Var "pcap"))
        (Let (Some "newCap")
          (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat minCap)))) (Var "doubled"))
            (Var "doubled") (Val (LitV (LitInt (Z.of_nat minCap)))))
          (Let (Some "src") (FieldLoad (Val (LitV (LitObj ob))) 1)
            (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
              (Let (Some "soff") (Val (LitV (LitInt 0)))
                (Let (Some "doff") (Val (LitV (LitInt 0))) (ga_of o)))))))]).
    iEval (rewrite (slots_length xs cap Hlen)) in "Hcapf".
    iApply (wp_field_load with "Hcapf").
    iIntros "!> _ Hcapf". iApply wp_let. simpl. rewrite drop_pcap.
    assert ((Z.of_nat cap + Z.of_nat cap)%Z = Z.of_nat (doubled cap)) as Hsum.
    { rewrite /doubled Nat2Z.inj_add. done. }
    iApply (wp_bind [LetCtx (Some "doubled")
      (Let (Some "newCap")
        (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat minCap)))) (Var "doubled"))
          (Var "doubled") (Val (LitV (LitInt (Z.of_nat minCap)))))
        (Let (Some "src") (FieldLoad (Val (LitV (LitObj ob))) 1)
          (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
            (Let (Some "soff") (Val (LitV (LitInt 0)))
              (Let (Some "doff") (Val (LitV (LitInt 0))) (ga_of o))))))]).
    iApply wp_binop.
    { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl. rewrite drop_doubled.
    iApply (wp_bind [LetCtx (Some "newCap")
      (Let (Some "src") (FieldLoad (Val (LitV (LitObj ob))) 1)
        (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
          (Let (Some "soff") (Val (LitV (LitInt 0)))
            (Let (Some "doff") (Val (LitV (LitInt 0))) (ga_of o)))))]).
    iApply (wp_bind [IfCtx (Val (LitV (LitInt (Z.of_nat cap + Z.of_nat cap)%Z)))
                           (Val (LitV (LitInt (Z.of_nat minCap))))]).
    destruct (decide (Z.of_nat minCap ≤ Z.of_nat (doubled cap))%Z) as [HleZ|HgtZ].
    - iApply wp_binop.
      { simpl. rewrite bool_decide_eq_true_2; [reflexivity|].
        rewrite Hsum. exact HleZ. }
      iIntros "!> _". iApply wp_if_true. iApply wp_value'.
      iApply wp_let. simpl. rewrite Hsum.
      assert (grow_cap cap minCap = doubled cap) as ->.
      { rewrite /grow_cap /doubled. destruct (decide (minCap ≤ cap + cap)%nat); lia. }
      iApply (wp_bind [LetCtx (Some "src")
        (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
          (Let (Some "soff") (Val (LitV (LitInt 0)))
            (Let (Some "doff") (Val (LitV (LitInt 0)))
              (g_new o (Z.of_nat (doubled cap))))))]).
      iApply (wp_field_load with "Hptr").
      iIntros "!> _ Hptr". iApply wp_let. simpl.
      iApply (wp_bind [LetCtx (Some "len")
        (Let (Some "soff") (Val (LitV (LitInt 0)))
          (Let (Some "doff") (Val (LitV (LitInt 0)))
            (g_src o (Z.of_nat (doubled cap)) base)))]).
      iApply (wp_field_load with "Hsz").
      iIntros "!> _ Hsz". iApply wp_let. simpl.
      iApply wp_let. simpl.
      iApply wp_let. simpl.
      rewrite /g_doff /g_soff /g_len /g_src /g_new /ga_of grow_open_eq.
      iClear "Hcapf Hptr Hblk".
      iApply (grow_alloc_spec xs cap (doubled cap) ver o base
                (LitV (LitObj ob)) with "Hbuf Hsz Hver Hcells").
      { done. }
      { rewrite /doubled. lia. }
      { rewrite /doubled. lia. }
    - iApply wp_binop.
      { simpl. rewrite bool_decide_eq_false_2; [reflexivity|].
        rewrite Hsum. exact HgtZ. }
      iIntros "!> _". iApply wp_if_false. iApply wp_value'.
      iApply wp_let. simpl.
      assert (grow_cap cap minCap = minCap) as ->.
      { rewrite /grow_cap /doubled. destruct (decide (minCap ≤ cap + cap)%nat); lia. }
      iApply (wp_bind [LetCtx (Some "src")
        (Let (Some "len") (FieldLoad (Val (LitV (LitObj o))) 1)
          (Let (Some "soff") (Val (LitV (LitInt 0)))
            (Let (Some "doff") (Val (LitV (LitInt 0)))
              (g_new o (Z.of_nat minCap)))))]).
      iApply (wp_field_load with "Hptr").
      iIntros "!> _ Hptr". iApply wp_let. simpl.
      iApply (wp_bind [LetCtx (Some "len")
        (Let (Some "soff") (Val (LitV (LitInt 0)))
          (Let (Some "doff") (Val (LitV (LitInt 0)))
            (g_src o (Z.of_nat minCap) base)))]).
      iApply (wp_field_load with "Hsz").
      iIntros "!> _ Hsz". iApply wp_let. simpl.
      iApply wp_let. simpl.
      iApply wp_let. simpl.
      rewrite /g_doff /g_soff /g_len /g_src /g_new /ga_of grow_open_eq.
      iClear "Hcapf Hptr Hblk".
      iApply (grow_alloc_spec xs cap minCap ver o base
                (LitV (LitObj ob)) with "Hbuf Hsz Hver Hcells").
      { done. }
      { done. }
      { done. }
  Qed.

  Transparent grow_open.

  (* The suffix of [add]: the element is written at the live length, then
     the length and the version each increase by one. *)
  Definition add_suffix (ao : loc) (x : Z) : expr :=
    Let (Some "buf2") (FieldLoad (Val (LitV (LitObj ao))) 0)
      (Let (Some "p") (FieldLoad (Var "buf2") 1)
        (Let None
          (Store (Offset (Var "p") (Var "n")) (Val (LitV (LitInt x))))
          (Let (Some "n1") (BinOp PlusOp (Var "n") (Val (LitV (LitInt 1))))
            (Let None
              (FieldStore (Val (LitV (LitObj ao))) 1 (Var "n1"))
              (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
                (FieldStore (Val (LitV (LitObj ao))) 2
                  (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))))))).

  Definition add_write_e (ao : loc) (n x : Z) : expr :=
    subst "n" (LitV (LitInt n)) (add_suffix ao x).

  Arguments add_suffix : simpl never.
  Arguments grow_body : simpl never.

  Lemma add_write_spec (xs : list Z) (cap : nat) (ver : Z) (ao : loc) (x : Z) :
    (length xs < cap)%nat →
    is_arraylist xs cap ver (LitV (LitObj ao)) -∗
    WP add_write_e ao (Z.of_nat (length xs)) x
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗
            is_arraylist (xs ++ [x]) cap (ver + 1)%Z (LitV (LitObj ao)) }}.
  Proof.
    iIntros (Hlt) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite /add_write_e /add_suffix Ha Hb. simpl.
    set (nZ := Z.of_nat (length xs)).
    iApply (wp_bind [LetCtx (Some "buf2")
      (Let (Some "p") (FieldLoad (Var "buf2") 1)
        (Let None
          (Store (Offset (Var "p") (Val (LitV (LitInt nZ)))) (Val (LitV (LitInt x))))
          (Let (Some "n1") (BinOp PlusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt 1))))
            (Let None
              (FieldStore (Val (LitV (LitObj o))) 1 (Var "n1"))
              (Let (Some "ver") (FieldLoad (Val (LitV (LitObj o))) 2)
                (FieldStore (Val (LitV (LitObj o))) 2
                  (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1))))))))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "p")
      (Let None
        (Store (Offset (Var "p") (Val (LitV (LitInt nZ)))) (Val (LitV (LitInt x))))
        (Let (Some "n1") (BinOp PlusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt 1))))
          (Let None
            (FieldStore (Val (LitV (LitObj o))) 1 (Var "n1"))
            (Let (Some "ver") (FieldLoad (Val (LitV (LitObj o))) 2)
              (FieldStore (Val (LitV (LitObj o))) 2
                (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx None
      (Let (Some "n1") (BinOp PlusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt 1))))
        (Let None
          (FieldStore (Val (LitV (LitObj o))) 1 (Var "n1"))
          (Let (Some "ver") (FieldLoad (Val (LitV (LitObj o))) 2)
            (FieldStore (Val (LitV (LitObj o))) 2
              (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1))))))))]).
    iApply (wp_bind [StoreLCtx (Val (LitV (LitInt x)))]).
    iApply wp_offset. iIntros "!> _".
    iDestruct (big_sepL_insert_acc _ _ (length xs) with "Hcells") as "[Hc Hclose]".
    { apply slots_lookup_zero; [lia|exact Hlt]. }
    iApply (wp_store with "Hc").
    iIntros "!> _ Hc".
    iDestruct ("Hclose" $! x with "Hc") as "Hcells".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "n1")
      (Let None
        (FieldStore (Val (LitV (LitObj o))) 1 (Var "n1"))
        (Let (Some "ver") (FieldLoad (Val (LitV (LitObj o))) 2)
          (FieldStore (Val (LitV (LitObj o))) 2
            (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))))]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl.
    assert ((nZ + 1)%Z = Z.of_nat (length (xs ++ [x]))) as Hszv.
    { rewrite /nZ al_add_length Nat2Z.inj_succ. unfold Z.succ. done. }
    iApply (wp_bind [LetCtx None
      (Let (Some "ver") (FieldLoad (Val (LitV (LitObj o))) 2)
        (FieldStore (Val (LitV (LitObj o))) 2
          (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1))))))]).
    iApply (wp_field_store with "Hsz").
    iIntros "!> _ Hsz". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "ver")
      (FieldStore (Val (LitV (LitObj o))) 2
        (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))]).
    iApply (wp_field_load with "Hver").
    iIntros "!> _ Hver". iApply wp_let. simpl.
    iApply (wp_bind [FieldStoreRCtx (LitV (LitObj o)) 2]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _".
    iApply (wp_field_store with "Hver").
    iIntros "!> _ Hver".
    iEval (rewrite Hszv) in "Hsz".
    iEval (rewrite -(slots_snoc xs cap x Hlt)) in "Hcells".
    iEval (rewrite (slots_length xs cap Hlen)) in "Hcapf".
    iEval (rewrite (slots_length xs cap Hlen)) in "Hblk".
    unfold is_arraylist, is_buf.
    rewrite (slots_length (xs ++ [x]) cap); last first.
    { rewrite al_add_length. lia. }
    iSplit; [done|].
    iExists o, (LitV (LitObj ob)).
    iSplit; [done|].
    iSplit. { iPureIntro. rewrite al_add_length. lia. }
    iSplit; [done|].
    iFrame "Hbuf Hsz Hver".
    iExists ob, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma suf_buf (ao : loc) (x n : Z) (w : val) :
    subst "buf" w (add_write_e ao n x) = add_write_e ao n x.
  Proof. rewrite /add_write_e /add_suffix. simpl. reflexivity. Qed.
  Lemma suf_pcap (ao : loc) (x n : Z) (w : val) :
    subst "pcap" w (add_write_e ao n x) = add_write_e ao n x.
  Proof. rewrite /add_write_e /add_suffix. simpl. reflexivity. Qed.
  Lemma suf_min (ao : loc) (x n : Z) (w : val) :
    subst "min" w (add_write_e ao n x) = add_write_e ao n x.
  Proof. rewrite /add_write_e /add_suffix. simpl. reflexivity. Qed.
  Lemma suf_gargs (ao : loc) (x n : Z) (w : val) :
    subst "gargs" w (add_write_e ao n x) = add_write_e ao n x.
  Proof. rewrite /add_write_e /add_suffix. simpl. reflexivity. Qed.

  Definition add_suffix_var : expr :=
    Let (Some "buf2") (FieldLoad (Var "a") 0)
      (Let (Some "p") (FieldLoad (Var "buf2") 1)
        (Let None
          (Store (Offset (Var "p") (Var "n")) (Var "x"))
          (Let (Some "n1") (BinOp PlusOp (Var "n") (Val (LitV (LitInt 1))))
            (Let None
              (FieldStore (Var "a") 1 (Var "n1"))
              (Let (Some "ver") (FieldLoad (Var "a") 2)
                (FieldStore (Var "a") 2
                  (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))))))).

  Definition add_core : expr :=
    Let (Some "n") (FieldLoad (Var "a") 1)
      (Let (Some "buf") (FieldLoad (Var "a") 0)
        (Let (Some "pcap") (FieldLoad (Var "buf") 0)
          (Let (Some "min") (BinOp PlusOp (Var "n") (Val (LitV (LitInt 1))))
            (Let (Some "gargs") (Struct [] [Var "a"; Var "min"])
              (Let None
                (If (BinOp LeOp (Var "pcap") (Var "n"))
                  (App (Rec None (Some "args") grow_body) (Var "gargs"))
                  (Val (LitV LitUnit)))
                add_suffix_var))))).

  Definition add_open (ao : loc) (x : Z) : expr :=
    Let (Some "n") (FieldLoad (Val (LitV (LitObj ao))) 1)
      (Let (Some "buf") (FieldLoad (Val (LitV (LitObj ao))) 0)
        (Let (Some "pcap") (FieldLoad (Var "buf") 0)
          (Let (Some "min") (BinOp PlusOp (Var "n") (Val (LitV (LitInt 1))))
            (Let (Some "gargs") (Struct [] [Val (LitV (LitObj ao)); Var "min"])
              (Let None
                (If (BinOp LeOp (Var "pcap") (Var "n"))
                  (App (Rec None (Some "args") grow_body) (Var "gargs"))
                  (Val (LitV LitUnit)))
                (add_suffix ao x)))))).

  Definition add_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
      (Let (Some "x") (StructLoad (Var "args") 1) add_core).

  Definition call_add (a : val_cjr) (x : Z) : expr :=
    App (Rec None (Some "args") add_body)
      (Val (StructV [a; LitV (LitInt x)])).

  Lemma add_bridge (ao : loc) (x : Z) :
    subst "x" (LitV (LitInt x)) (subst "a" (LitV (LitObj ao)) add_core) = add_open ao x.
  Proof.
    rewrite /add_core /add_open /add_suffix /add_suffix_var. simpl. reflexivity.
  Qed.

  Lemma add_open_spec (xs : list Z) (cap : nat) (ver : Z) (ao : loc) (x : Z) :
    is_arraylist xs cap ver (LitV (LitObj ao)) -∗
    WP add_open ao x
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z
              (LitV (LitObj ao)) }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb. simplify_eq.
    rewrite /add_open. Opaque add_suffix.
    set (nZ := Z.of_nat (length xs)).
    assert (length (slots_of xs cap) = cap) as Hslots.
    { apply slots_length. done. }
    assert ((nZ + 1)%Z = Z.of_nat (S (length xs))) as Hsucc.
    { rewrite /nZ. change ((Z.of_nat (length xs) + 1)%Z) with (Z.succ (Z.of_nat (length xs))).
      rewrite -Nat2Z.inj_succ. done. }
    iApply (wp_bind [LetCtx (Some "n")
      (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
        (Let (Some "pcap") (FieldLoad (Var "buf") 0)
          (Let (Some "min") (BinOp PlusOp (Var "n") (Val (LitV (LitInt 1))))
            (Let (Some "gargs") (Struct [] [Val (LitV (LitObj o)); Var "min"])
              (Let None
                (If (BinOp LeOp (Var "pcap") (Var "n"))
                  (App (Rec None (Some "args") grow_body) (Var "gargs"))
                  (Val (LitV LitUnit)))
                (add_suffix o x))))))]).
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz". iApply wp_let. simpl.
    rewrite -/(add_write_e o nZ x).
    iApply (wp_bind [LetCtx (Some "buf")
      (Let (Some "pcap") (FieldLoad (Var "buf") 0)
        (Let (Some "min") (BinOp PlusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt 1))))
          (Let (Some "gargs")
            (Struct [] [Val (LitV (LitObj o)); Var "min"])
            (Let None
              (If (BinOp LeOp (Var "pcap") (Val (LitV (LitInt nZ))))
                (App (Rec None (Some "args") grow_body) (Var "gargs"))
                (Val (LitV LitUnit)))
              (add_write_e o nZ x)))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf". iApply wp_let. simpl. rewrite suf_buf.
    iApply (wp_bind [LetCtx (Some "pcap")
      (Let (Some "min") (BinOp PlusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt 1))))
        (Let (Some "gargs")
          (Struct [] [Val (LitV (LitObj o)); Var "min"])
          (Let None
            (If (BinOp LeOp (Var "pcap") (Val (LitV (LitInt nZ))))
              (App (Rec None (Some "args") grow_body) (Var "gargs"))
              (Val (LitV LitUnit)))
            (add_write_e o nZ x))))]).
    iApply (wp_field_load with "Hcapf").
    iIntros "!> _ Hcapf". iApply wp_let. simpl. rewrite suf_pcap.
    iApply (wp_bind [LetCtx (Some "min")
      (Let (Some "gargs")
        (Struct [] [Val (LitV (LitObj o)); Var "min"])
        (Let None
          (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat (length (slots_of xs cap))))))
                         (Val (LitV (LitInt nZ))))
            (App (Rec None (Some "args") grow_body) (Var "gargs"))
            (Val (LitV LitUnit)))
          (add_write_e o nZ x)))]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl. rewrite suf_min.
    iApply (wp_bind [LetCtx (Some "gargs")
      (Let None
        (If (BinOp LeOp (Val (LitV (LitInt (Z.of_nat (length (slots_of xs cap))))))
                       (Val (LitV (LitInt nZ))))
          (App (Rec None (Some "args") grow_body) (Var "gargs"))
          (Val (LitV LitUnit)))
        (add_write_e o nZ x))]).
    iApply wp_struct_step. iApply wp_struct_step. iApply wp_struct_done.
    iIntros "!> _". iApply wp_let. simpl. rewrite suf_gargs.
    rewrite Hslots Hsucc.
    iAssert (is_arraylist xs cap ver (LitV (LitObj o)))
      with "[Hbuf Hsz Hver Hcapf Hptr Hblk Hcells]" as "Ha".
    { rewrite /is_arraylist /is_buf Hslots.
      iExists o, (LitV (LitObj ob)).
      iSplit. { iPureIntro. done. }
      iSplit. { iPureIntro. exact Hlen. }
      iSplit. { iPureIntro. exact Hcap. }
      iFrame "Hbuf Hsz Hver".
      iExists ob, base.
      iSplit. { iPureIntro. done. }
      iFrame. }
    iApply (wp_bind [LetCtx None (add_write_e o nZ x)]).
    iApply (wp_bind [IfCtx
      (App (Rec None (Some "args") grow_body)
        (Val (StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat (S (length xs))))])))
      (Val (LitV LitUnit))]).
    destruct (decide (Z.of_nat cap ≤ nZ)%Z) as [Hfull|Hroom].
    - iApply wp_binop.
      { simpl. rewrite bool_decide_eq_true_2; [reflexivity|]. rewrite /nZ. exact Hfull. }
      iIntros "!> _". iApply wp_if_true.
      assert (length xs = cap) as Heq by (rewrite /nZ in Hfull; lia).
      iApply (wp_wand with "[Ha]").
      { rewrite Heq. iApply (grow_spec xs cap ver (LitV (LitObj o)) (S cap) with "Ha").
        - lia.
        - lia. }
      iIntros (v) "[%Hv Ha]". rewrite Hv. iApply wp_let. simpl.
      iApply (wp_wand with "[Ha]").
      { rewrite grow_cap_double; last done.
        iApply (add_write_spec xs (doubled cap) ver o x with "Ha").
        rewrite /doubled. lia. }
      iIntros (w) "[%Hw Ha]". iSplit; [done|].
      rewrite /al_add Heq -(add_cap_full cap Hcap). done.
    - iApply wp_binop.
      { simpl. rewrite bool_decide_eq_false_2; [reflexivity|]. rewrite /nZ. exact Hroom. }
      iIntros "!> _". iApply wp_if_false. iApply wp_value'. iApply wp_let. simpl.
      assert ((length xs < cap)%nat) as Hlt by (rewrite /nZ in Hroom; lia).
      iApply (wp_wand with "[Ha]").
      { iApply (add_write_spec xs cap ver o x Hlt with "Ha"). }
      iIntros (w) "[%Hw Ha]". iSplit; [done|].
      rewrite /al_add.
      assert (add_cap cap (length xs) = cap) as -> by (apply add_cap_room; exact Hlt).
      done.
  Qed.

  Lemma add_spec (xs : list Z) (cap : nat) (ver : Z) (a : val_cjr) (x : Z) :
    is_arraylist xs cap ver a -∗
    WP call_add a x
      {{ v, ⌜ v = LitV LitUnit ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z a }}.
  Proof.
    iIntros "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt x)]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    Opaque add_core.
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "x") (StructLoad (Val arg) 1) add_core)]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "x") (subst "a" (LitV (LitObj o)) add_core)]).
    iApply (wp_struct_load _ 1 (LitV (LitInt x))); [done|].
    iIntros "!> _". iApply wp_let. simpl.
    Transparent add_core.
    rewrite add_bridge.
    iApply add_open_spec.
    iExists o, buf. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    iFrame.
  Qed.

  Definition remove_finish_e (ao : loc) (n p y : Z) : expr :=
    Let (Some "last") (BinOp MinusOp (Val (LitV (LitInt n))) (Val (LitV (LitInt 1))))
      (Let None
        (Store (Offset (Val (LitV (LitPtr p))) (Var "last")) (Val (LitV (LitInt 0))))
        (Let None
          (FieldStore (Val (LitV (LitObj ao))) 1 (Var "last"))
          (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
            (Let None
              (FieldStore (Val (LitV (LitObj ao))) 2
                (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))
              (Val (LitV (LitInt y))))))).

  Lemma remove_finish_spec (xs : list Z) (cap j : nat) (ver y : Z)
      (ao ob : loc) (base : Z) :
    (j < length xs)%nat → (length xs ≤ cap)%nat → (0 < cap)%nat →
    xs !! j = Some y →
    ObjId ao ↦ₒ[0] LitV (LitObj ob) -∗
    ObjId ao ↦ₒ[1] LitV (LitInt (Z.of_nat (length xs))) -∗
    ObjId ao ↦ₒ[2] LitV (LitInt ver) -∗
    ObjId ob ↦ₒ[0] LitV (LitInt (Z.of_nat cap)) -∗
    ObjId ob ↦ₒ[1] LitV (LitPtr base) -∗
    RawId base ↦ᵦ cap -∗
    array_cells base (shift_from (slots_of xs cap) j 0 (length xs - j - 1)) -∗
    WP remove_finish_e ao (Z.of_nat (length xs)) base y
      {{ v, ⌜ v = LitV (LitInt y) ⌝ ∗
            is_arraylist (al_remove xs j) cap (ver + 1)%Z (LitV (LitObj ao)) }}.
  Proof.
    iIntros (Hj Hlen Hcap Hy) "Hbuf Hsz Hver Hcapf Hptr Hblk Hcells".
    set (len := (length xs - j - 1)%nat).
    set (nZ := Z.of_nat (length xs)).
    assert ((nZ - 1)%Z = Z.of_nat (length xs - 1)) as Hlast.
    { rewrite /nZ. lia. }
    assert (length (al_remove xs j) = (length xs - 1)%nat) as Hrmlen.
    { apply al_remove_length. done. }
    assert ((j + len)%nat = (length xs - 1)%nat) as Hjl by (rewrite /len; lia).
    assert (length (shift_from (slots_of xs cap) j 0 len) = cap) as Hslen.
    { rewrite shift_from_length; last first.
      - rewrite (slots_length xs cap Hlen). lia.
      - lia.
      - apply slots_length. done. }
    iApply (wp_bind [LetCtx (Some "last")
      (Let None
        (Store (Offset (Val (LitV (LitPtr base))) (Var "last")) (Val (LitV (LitInt 0))))
        (Let None
          (FieldStore (Val (LitV (LitObj ao))) 1 (Var "last"))
          (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
            (Let None
              (FieldStore (Val (LitV (LitObj ao))) 2
                (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))
              (Val (LitV (LitInt y)))))))]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl. rewrite Hlast.
    destruct (lookup_lt_is_Some_2 (shift_from (slots_of xs cap) j 0 len)
                (length xs - 1)) as [old Hold].
    { rewrite Hslen. lia. }
    iApply (wp_bind [LetCtx None
      (Let None
        (FieldStore (Val (LitV (LitObj ao))) 1
          (Val (LitV (LitInt (Z.of_nat (length xs - 1))))))
        (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
          (Let None
            (FieldStore (Val (LitV (LitObj ao))) 2
              (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))
            (Val (LitV (LitInt y))))))]).
    iApply (wp_bind [StoreLCtx (Val (LitV (LitInt 0)))]).
    iApply wp_offset. iIntros "!> _".
    iDestruct (big_sepL_insert_acc _ _ (length xs - 1) with "Hcells") as "[Hc Hclose]".
    { exact Hold. }
    iApply (wp_store with "Hc").
    iIntros "!> _ Hc".
    iDestruct ("Hclose" $! 0%Z with "Hc") as "Hcells".
    iApply wp_let. simpl.
    iApply (wp_bind [LetCtx None
      (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
        (Let None
          (FieldStore (Val (LitV (LitObj ao))) 2
            (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))
          (Val (LitV (LitInt y)))))]).
    iApply (wp_field_store with "Hsz").
    iIntros "!> _ Hsz". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "ver")
      (Let None
        (FieldStore (Val (LitV (LitObj ao))) 2
          (BinOp PlusOp (Var "ver") (Val (LitV (LitInt 1)))))
        (Val (LitV (LitInt y))))]).
    iApply (wp_field_load with "Hver").
    iIntros "!> _ Hver". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx None (Val (LitV (LitInt y)))]).
    iApply (wp_bind [FieldStoreRCtx (LitV (LitObj ao)) 2]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _".
    iApply (wp_field_store with "Hver").
    iIntros "!> _ Hver".
    iApply wp_let. simpl.
    iApply wp_value'.
    iEval (rewrite -Hrmlen) in "Hsz".
    iEval (rewrite (remove_slots xs cap j Hj Hlen)) in "Hcells".
    unfold is_arraylist, is_buf.
    rewrite (slots_length (al_remove xs j) cap); last first.
    { rewrite Hrmlen. lia. }
    iSplit; [done|].
    iExists ao, (LitV (LitObj ob)).
    iSplit; [done|].
    iSplit. { iPureIntro. rewrite Hrmlen. lia. }
    iSplit; [done|].
    iFrame "Hbuf Hsz Hver".
    iExists ob, base. iSplit; [done|]. iFrame.
  Qed.

  Definition remove_tail (ao : loc) : expr :=
    Let (Some "last") ((Var "n") - (Val (LitV (LitInt 1))))
      (Let None
        (Store (Offset (Var "p") (Var "last")) (Val (LitV (LitInt 0))))
        (Let None
          (FieldStore (Val (LitV (LitObj ao))) 1 (Var "last"))
          (Let (Some "ver") (FieldLoad (Val (LitV (LitObj ao))) 2)
            (Let None
              (FieldStore (Val (LitV (LitObj ao))) 2 ((Var "ver") + (Val (LitV (LitInt 1)))))
              (Var "removed"))))).

  Definition remove_ready (ao : loc) (n p y : Z) : expr :=
    subst "removed" (LitV (LitInt y))
      (subst "p" (LitV (LitPtr p))
        (subst "n" (LitV (LitInt n)) (remove_tail ao))).

  Lemma remove_ready_eq (ao : loc) (n p y : Z) :
    remove_ready ao n p y = remove_finish_e ao n p y.
  Proof. rewrite /remove_ready /remove_tail /remove_finish_e. simpl. reflexivity. Qed.

  Lemma rr_buf (ao : loc) (n : Z) (w : val) :
    subst "buf" w (subst "n" (LitV (LitInt n)) (remove_tail ao)) =
    subst "n" (LitV (LitInt n)) (remove_tail ao).
  Proof. rewrite /remove_tail. simpl. reflexivity. Qed.
  Lemma rr_soff (ao : loc) (n p y : Z) (w : val) :
    subst "soff" w (remove_ready ao n p y) = remove_ready ao n p y.
  Proof. rewrite /remove_ready /remove_tail. simpl. reflexivity. Qed.
  Lemma rr_doff (ao : loc) (n p y : Z) (w : val) :
    subst "doff" w (remove_ready ao n p y) = remove_ready ao n p y.
  Proof. rewrite /remove_ready /remove_tail. simpl. reflexivity. Qed.
  Lemma rr_len (ao : loc) (n p y : Z) (w : val) :
    subst "len" w (remove_ready ao n p y) = remove_ready ao n p y.
  Proof. rewrite /remove_ready /remove_tail. simpl. reflexivity. Qed.
  Lemma rr_src (ao : loc) (n p y : Z) (w : val) :
    subst "src" w (remove_ready ao n p y) = remove_ready ao n p y.
  Proof. rewrite /remove_ready /remove_tail. simpl. reflexivity. Qed.
  Lemma rr_dst (ao : loc) (n p y : Z) (w : val) :
    subst "dst" w (remove_ready ao n p y) = remove_ready ao n p y.
  Proof. rewrite /remove_ready /remove_tail. simpl. reflexivity. Qed.

  Arguments remove_tail : simpl never.

  Definition remove_tail_var : expr :=
    Let (Some "last") ((Var "n") - (Val (LitV (LitInt 1))))
      (Let None
        (Store (Offset (Var "p") (Var "last")) (Val (LitV (LitInt 0))))
        (Let None
          (FieldStore (Var "a") 1 (Var "last"))
          (Let (Some "ver") (FieldLoad (Var "a") 2)
            (Let None
              (FieldStore (Var "a") 2 ((Var "ver") + (Val (LitV (LitInt 1)))))
              (Var "removed"))))).

  Definition remove_core : expr :=
    Let (Some "n") (FieldLoad (Var "a") 1)
      (If (Var "n" ≤ Var "at") oob
        (If (Var "at" ≤ Val (LitV (LitInt (Z.opp 1)))) oob
          (Let (Some "buf") (FieldLoad (Var "a") 0)
            (Let (Some "p") (FieldLoad (Var "buf") 1)
              (Let (Some "removed") (Load (Offset (Var "p") (Var "at")))
                (Let (Some "src") (Var "p")
                  (Let (Some "dst") (Var "p")
                    (Let (Some "soff") ((Var "at") + (Val (LitV (LitInt 1))))
                      (Let (Some "doff") (Var "at")
                        (Let (Some "len") (((Var "n") - (Var "at")) - (Val (LitV (LitInt 1))))
                          (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                            (remove_tail_var)))))))))))).

  Definition remove_open (ao : loc) (j : Z) : expr :=
    Let (Some "n") (FieldLoad (Val (LitV (LitObj ao))) 1)
      (If ((Var "n") ≤ (Val (LitV (LitInt j)))) oob
        (If ((Val (LitV (LitInt j))) ≤ (Val (LitV (LitInt (Z.opp 1))))) oob
          (Let (Some "buf") (FieldLoad (Val (LitV (LitObj ao))) 0)
            (Let (Some "p") (FieldLoad (Var "buf") 1)
              (Let (Some "removed") (Load (Offset (Var "p") (Val (LitV (LitInt j)))))
                (Let (Some "src") (Var "p")
                  (Let (Some "dst") (Var "p")
                    (Let (Some "soff") ((Val (LitV (LitInt j))) + (Val (LitV (LitInt 1))))
                      (Let (Some "doff") (Val (LitV (LitInt j)))
                        (Let (Some "len")
                          (((Var "n") - (Val (LitV (LitInt j)))) - (Val (LitV (LitInt 1))))
                          (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                            (remove_tail ao)))))))))))).

  Lemma remove_bridge (ao : loc) (j : Z) :
    subst "at" (LitV (LitInt j)) (subst "a" (LitV (LitObj ao)) remove_core) =
    remove_open ao j.
  Proof.
    rewrite /remove_core /remove_open /remove_tail /remove_tail_var. simpl. reflexivity.
  Qed.

  Definition remove_body : expr :=
    Let (Some "a") (StructLoad (Var "args") 0)
      (Let (Some "at") (StructLoad (Var "args") 1) remove_core).

  Definition call_remove (a : val_cjr) (j : Z) : expr :=
    App (Rec None (Some "args") remove_body)
      (Val (StructV [a; LitV (LitInt j)])).

  Arguments remove_core : simpl never.

  Lemma remove_open_spec (xs : list Z) (cap j : nat) (ver y : Z) (ao : loc) :
    (j < length xs)%nat → xs !! j = Some y →
    is_arraylist xs cap ver (LitV (LitObj ao)) -∗
    WP remove_open ao (Z.of_nat j)
      {{ v, ⌜ v = LitV (LitInt y) ⌝ ∗
            is_arraylist (al_remove xs j) cap (ver + 1)%Z (LitV (LitObj ao)) }}.
  Proof.
    iIntros (Hj Hy) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    iDestruct "Hdata" as (ob base) "(%Hb & Hcapf & Hptr & Hblk & Hcells)".
    rewrite Ha Hb. simplify_eq.
    set (jZ := Z.of_nat j). set (nZ := Z.of_nat (length xs)).
    set (len := (length xs - j - 1)%nat).
    iEval (rewrite (slots_length xs cap Hlen)) in "Hcapf".
    iEval (rewrite (slots_length xs cap Hlen)) in "Hblk".
    rewrite /remove_open.
    iApply (wp_bind [LetCtx (Some "n")
      (If (BinOp LeOp (Var "n") (Val (LitV (LitInt jZ)))) oob
        (If (BinOp LeOp (Val (LitV (LitInt jZ))) (Val (LitV (LitInt (Z.opp 1))))) oob
          (Let (Some "buf") (FieldLoad (Val (LitV (LitObj o))) 0)
            (Let (Some "p") (FieldLoad (Var "buf") 1)
              (Let (Some "removed") (Load (Offset (Var "p") (Val (LitV (LitInt jZ)))))
                (Let (Some "src") (Var "p")
                  (Let (Some "dst") (Var "p")
                    (Let (Some "soff") (BinOp PlusOp (Val (LitV (LitInt jZ))) (Val (LitV (LitInt 1))))
                      (Let (Some "doff") (Val (LitV (LitInt jZ)))
                        (Let (Some "len")
                          (BinOp MinusOp
                            (BinOp MinusOp (Var "n") (Val (LitV (LitInt jZ))))
                            (Val (LitV (LitInt 1))))
                          (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                            (remove_tail o))))))))))))]).
    iApply (wp_field_load with "Hsz").
    iIntros "!> _ Hsz". Opaque remove_tail. iApply wp_let. simpl.
    iApply wp_range_ok.
    { apply Nat2Z.is_nonneg. }
    { apply Nat2Z.inj_lt. exact Hj. }
    iApply (wp_bind [LetCtx (Some "buf")
      (Let (Some "p") (FieldLoad (Var "buf") 1)
        (Let (Some "removed") (Load (Offset (Var "p") (Val (LitV (LitInt jZ)))))
          (Let (Some "src") (Var "p")
            (Let (Some "dst") (Var "p")
              (Let (Some "soff") (BinOp PlusOp (Val (LitV (LitInt jZ))) (Val (LitV (LitInt 1))))
                (Let (Some "doff") (Val (LitV (LitInt jZ)))
                  (Let (Some "len")
                    (BinOp MinusOp (BinOp MinusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt jZ))))
                     (Val (LitV (LitInt 1))))
                    (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                      (subst "n" (LitV (LitInt nZ)) (remove_tail o))))))))))]).
    iApply (wp_field_load with "Hbuf").
    iIntros "!> _ Hbuf". iApply wp_let. simpl. rewrite rr_buf.
    iApply (wp_bind [LetCtx (Some "p")
      (Let (Some "removed") (Load (Offset (Var "p") (Val (LitV (LitInt jZ)))))
        (Let (Some "src") (Var "p")
          (Let (Some "dst") (Var "p")
            (Let (Some "soff") (BinOp PlusOp (Val (LitV (LitInt jZ))) (Val (LitV (LitInt 1))))
              (Let (Some "doff") (Val (LitV (LitInt jZ)))
                (Let (Some "len")
                  (BinOp MinusOp (BinOp MinusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt jZ))))
                   (Val (LitV (LitInt 1))))
                  (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                    (subst "n" (LitV (LitInt nZ)) (remove_tail o)))))))))]).
    iApply (wp_field_load with "Hptr").
    iIntros "!> _ Hptr". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "removed")
      (Let (Some "src") (Val (LitV (LitPtr base)))
        (Let (Some "dst") (Val (LitV (LitPtr base)))
          (Let (Some "soff") (BinOp PlusOp (Val (LitV (LitInt jZ))) (Val (LitV (LitInt 1))))
            (Let (Some "doff") (Val (LitV (LitInt jZ)))
              (Let (Some "len")
                (BinOp MinusOp (BinOp MinusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt jZ))))
                 (Val (LitV (LitInt 1))))
                (Let None (VarBind "i" (Val (LitV (LitInt 0))) copy_vars)
                  (subst "p" (LitV (LitPtr base))
                    (subst "n" (LitV (LitInt nZ)) (remove_tail o)))))))))]).
    iApply (wp_bind [LoadCtx]).
    iApply wp_offset. iIntros "!> _".
    iDestruct (big_sepL_lookup_acc _ _ j with "Hcells") as "[Hc Hclose]".
    { apply slots_lookup_prefix; [done|done]. }
    iApply (wp_load with "Hc").
    iIntros "!> _ Hc".
    iDestruct ("Hclose" with "Hc") as "Hcells".
    iApply wp_let. simpl.
    rewrite -/(remove_ready o nZ base y).
    iApply wp_let. simpl. rewrite rr_src.
    iApply wp_let. simpl. rewrite rr_dst.
    iApply (wp_bind [LetCtx (Some "soff")
      (Let (Some "doff") (Val (LitV (LitInt jZ)))
        (Let (Some "len")
          (BinOp MinusOp (BinOp MinusOp (Val (LitV (LitInt nZ))) (Val (LitV (LitInt jZ))))
           (Val (LitV (LitInt 1))))
          (Let None (VarBind "i" (Val (LitV (LitInt 0)))
            (subst "dst" (LitV (LitPtr base))
              (subst "src" (LitV (LitPtr base)) copy_vars)))
            (remove_ready o nZ base y))))]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl. rewrite rr_soff.
    iApply wp_let. simpl. rewrite rr_doff.
    iApply (wp_bind [LetCtx (Some "len")
      (Let None (VarBind "i" (Val (LitV (LitInt 0)))
        (subst "doff" (LitV (LitInt jZ))
          (subst "soff" (LitV (LitInt (jZ + 1)%Z))
            (subst "dst" (LitV (LitPtr base))
              (subst "src" (LitV (LitPtr base)) copy_vars)))))
        (remove_ready o nZ base y))]).
    iApply (wp_bind [BinOpLCtx MinusOp (Val (LitV (LitInt 1)))]).
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _".
    iApply wp_binop. { simpl. reflexivity. }
    iIntros "!> _". iApply wp_let. simpl. rewrite rr_len.
    assert ((jZ + 1)%Z = Z.of_nat (j + 1)) as Hsoff.
    { rewrite /jZ Nat2Z.inj_add. done. }
    assert (((nZ - jZ) - 1)%Z = Z.of_nat len) as HlenZ.
    { rewrite /nZ /jZ /len. lia. }
    rewrite Hsoff HlenZ.
    iApply (wp_bind [LetCtx None (remove_ready o nZ base y)]).
    iApply (wp_wand with "[Hcells]").
    { iApply (copy_shift base j len (slots_of xs cap) with "Hcells").
      rewrite (slots_length xs cap Hlen). rewrite /len. lia. }
    iIntros (v) "[%Hv Hcells]". rewrite Hv. iApply wp_let. simpl.
    rewrite remove_ready_eq. Transparent remove_tail.
    iApply (remove_finish_spec xs cap j ver y o ob base
              with "Hbuf Hsz Hver Hcapf Hptr Hblk Hcells").
    { exact Hj. }
    { exact Hlen. }
    { exact Hcap. }
    { exact Hy. }
  Qed.

  Lemma remove_spec (xs : list Z) (cap j : nat) (ver y : Z) (a : val_cjr) :
    (j < length xs)%nat → xs !! j = Some y →
    is_arraylist xs cap ver a -∗
    WP call_remove a (Z.of_nat j)
      {{ v, ⌜ v = LitV (LitInt y) ⌝ ∗
            is_arraylist (al_remove xs j) cap (ver + 1)%Z a }}.
  Proof.
    iIntros (Hj Hy) "Ha".
    iDestruct "Ha" as (o buf) "(%Ha & %Hlen & %Hcap & Hbuf & Hsz & Hver & Hdata)".
    rewrite Ha.
    set (arg := StructV [LitV (LitObj o); LitV (LitInt (Z.of_nat j))]).
    iApply (wp_bind [AppLCtx (Val arg)]).
    iApply wp_rec. iIntros "!> _".
    Opaque remove_core.
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx (Some "a")
      (Let (Some "at") (StructLoad (Val arg) 1) remove_core)]).
    iApply (wp_struct_load _ 0 (LitV (LitObj o))); [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx (Some "at") (subst "a" (LitV (LitObj o)) remove_core)]).
    iApply (wp_struct_load _ 1 (LitV (LitInt (Z.of_nat j)))); [done|].
    iIntros "!> _". iApply wp_let. simpl.
    Transparent remove_core.
    rewrite remove_bridge.
    iApply remove_open_spec.
    { exact Hj. }
    { exact Hy. }
    iExists o, buf. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iFrame.
  Qed.

  Definition size_at (arr : expr) : expr :=
    App (Rec None (Some "a") size_body) arr.
  Definition capacity_at (arr : expr) : expr :=
    App (Rec None (Some "a") capacity_body) arr.
  Definition version_at (arr : expr) : expr :=
    App (Rec None (Some "a") version_body) arr.
  Definition is_empty_at (arr : expr) : expr :=
    App (Rec None (Some "a") is_empty_body) arr.

  Definition init_then_size : expr :=
    Let (Some "a") call_init (size_at (Var "a")).
  Definition init_then_empty : expr :=
    Let (Some "a") call_init (is_empty_at (Var "a")).
  Definition init_then_capacity : expr :=
    Let (Some "a") call_init (capacity_at (Var "a")).
  Definition init_then_version : expr :=
    Let (Some "a") call_init (version_at (Var "a")).

  Lemma init_then_size_spec :
    ⊢ WP init_then_size
      {{ v, ∃ a, ⌜ v = LitV (LitInt 0) ⌝ ∗
                  is_arraylist [] default_capacity 0 a }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "a") (size_at (Var "a"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (a) "Ha".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (size_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    iExists a. iSplit; [done|]. iFrame.
  Qed.

  Lemma init_then_empty_spec :
    ⊢ WP init_then_empty
      {{ v, ∃ a, ⌜ v = LitV (LitBool true) ⌝ ∗
                  is_arraylist [] default_capacity 0 a }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "a") (is_empty_at (Var "a"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (a) "Ha".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (is_empty_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    simpl in Hv.
    iExists a. iSplit; [done|]. iFrame.
  Qed.

  Lemma init_then_capacity_spec :
    ⊢ WP init_then_capacity
      {{ v, ∃ a, ⌜ v = LitV (LitInt 16) ⌝ ∗
                  is_arraylist [] default_capacity 0 a }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "a") (capacity_at (Var "a"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (a) "Ha".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (capacity_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite /default_capacity in Hv. simpl in Hv.
    iExists a. iSplit; [done|]. iFrame.
  Qed.

  Lemma init_then_version_spec :
    ⊢ WP init_then_version
      {{ v, ∃ a, ⌜ v = LitV (LitInt 0) ⌝ ∗
                  is_arraylist [] default_capacity 0 a }}.
  Proof.
    iApply (wp_bind [LetCtx (Some "a") (version_at (Var "a"))]).
    iApply wp_wand. { iApply init_spec. }
    iIntros (a) "Ha".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (version_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    iExists a. iSplit; [done|]. iFrame.
  Qed.

  Definition add_then_size (a : val_cjr) (x : Z) : expr :=
    Let None (call_add a x) (call_size a).
  Definition add_then_get (a : val_cjr) (x i : Z) : expr :=
    Let None (call_add a x) (call_al_get a i).
  Definition add_then_version (a : val_cjr) (x : Z) : expr :=
    Let None (call_add a x) (call_version a).
  Definition add_then_capacity (a : val_cjr) (x : Z) : expr :=
    Let None (call_add a x) (call_capacity a).
  Definition add_then_remove (a : val_cjr) (x i : Z) : expr :=
    Let None (call_add a x) (call_remove a i).

  Lemma add_then_size_spec xs cap ver (a : val_cjr) (x : Z) :
    is_arraylist xs cap ver a -∗
    WP add_then_size a x
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (S (length xs)))) ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z a }}.
  Proof.
    iIntros "Ha".
    iApply (wp_bind [LetCtx None (call_size a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (size_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite al_add_length in Hv.
    iSplit; [done|]. iFrame.
  Qed.

  Lemma add_then_get_new_spec xs cap ver (a : val_cjr) (x : Z) :
    is_arraylist xs cap ver a -∗
    WP add_then_get a x (Z.of_nat (length xs))
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z a }}.
  Proof.
    iIntros "Ha".
    iApply (wp_bind [LetCtx None (call_al_get a (Z.of_nat (length xs)))]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (al_get_spec with "Ha"). apply al_add_lookup_new. }
    iIntros (v) "[%Hv Ha]".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma add_then_get_old_spec xs cap ver (a : val_cjr) (x y : Z) (i : nat) :
    (i < length xs)%nat → xs !! i = Some y →
    is_arraylist xs cap ver a -∗
    WP add_then_get a x (Z.of_nat i)
      {{ v, ⌜ v = LitV (LitInt y) ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z a }}.
  Proof.
    iIntros (Hi Hy) "Ha".
    iApply (wp_bind [LetCtx None (call_al_get a (Z.of_nat i))]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (al_get_spec with "Ha").
      rewrite /al_add (al_add_lookup_old xs x i Hi). exact Hy. }
    iIntros (v) "[%Hv Ha]".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma add_then_version_spec xs cap ver (a : val_cjr) (x : Z) :
    is_arraylist xs cap ver a -∗
    WP add_then_version a x
      {{ v, ⌜ v = LitV (LitInt (ver + 1)%Z) ⌝ ∗
            is_arraylist (al_add xs x) (add_cap cap (length xs)) (ver + 1)%Z a }}.
  Proof.
    iIntros "Ha".
    iApply (wp_bind [LetCtx None (call_version a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (version_spec with "Ha").
  Qed.

  Lemma add_then_capacity_room_spec xs cap ver (a : val_cjr) (x : Z) :
    (length xs < cap)%nat →
    is_arraylist xs cap ver a -∗
    WP add_then_capacity a x
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat cap)) ⌝ ∗
            is_arraylist (al_add xs x) cap (ver + 1)%Z a }}.
  Proof.
    iIntros (Hlt) "Ha".
    iApply (wp_bind [LetCtx None (call_capacity a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (capacity_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite (add_cap_room cap (length xs) Hlt) in Hv.
    assert (add_cap cap (length xs) = cap) as Heq by (apply add_cap_room; exact Hlt).
    iEval (rewrite Heq) in "Ha".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma add_then_capacity_full_spec xs cap ver (a : val_cjr) (x : Z) :
    length xs = cap → (0 < cap)%nat →
    is_arraylist xs cap ver a -∗
    WP add_then_capacity a x
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (doubled cap))) ⌝ ∗
            is_arraylist (al_add xs x) (doubled cap) (ver + 1)%Z a }}.
  Proof.
    iIntros (Heq Hcap) "Ha".
    iApply (wp_bind [LetCtx None (call_capacity a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (capacity_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite Heq (add_cap_full cap Hcap) in Hv.
    assert (add_cap cap (length xs) = doubled cap) as Hcap' .
    { rewrite Heq. by apply add_cap_full. }
    iEval (rewrite Hcap') in "Ha".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma add_then_remove_last_spec xs cap ver (a : val_cjr) (x : Z) :
    is_arraylist xs cap ver a -∗
    WP add_then_remove a x (Z.of_nat (length xs))
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗
            is_arraylist xs (add_cap cap (length xs)) (ver + 2)%Z a }}.
  Proof.
    iIntros "Ha".
    iApply (wp_bind [LetCtx None (call_remove a (Z.of_nat (length xs)))]).
    iApply (wp_wand with "[Ha]").
    { iApply (add_spec with "Ha"). }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (remove_spec with "Ha").
      - rewrite al_add_length. lia.
      - apply al_add_lookup_new. }
    iIntros (v) "[%Hv Ha]".
    rewrite /al_add al_remove_snoc.
    assert (((ver + 1) + 1)%Z = (ver + 2)%Z) as Hver by lia.
    iEval (rewrite Hver) in "Ha".
    iSplit; [done|]. iFrame.
  Qed.

  Definition set_then_get (a : val_cjr) (i j x : Z) : expr :=
    Let None (call_al_set a i x) (call_al_get a j).
  Definition set_then_size (a : val_cjr) (i x : Z) : expr :=
    Let None (call_al_set a i x) (call_size a).
  Definition set_then_version (a : val_cjr) (i x : Z) : expr :=
    Let None (call_al_set a i x) (call_version a).

  Lemma set_then_get_same_spec xs cap ver (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_arraylist xs cap ver a -∗
    WP set_then_get a (Z.of_nat i) (Z.of_nat i) x
      {{ v, ⌜ v = LitV (LitInt x) ⌝ ∗ is_arraylist (al_set xs i x) cap ver a }}.
  Proof.
    iIntros (Hy) "Ha".
    iApply (wp_bind [LetCtx None (call_al_get a (Z.of_nat i))]).
    iApply (wp_wand with "[Ha]").
    { iApply (al_set_spec with "Ha"). exact Hy. }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (al_get_spec with "Ha").
      rewrite /al_set. by apply (al_set_lookup xs i x y). }
    iIntros (v) "[%Hv Ha]".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma set_then_get_other_spec xs cap ver (a : val_cjr) (i j : nat) y z x :
    i ≠ j → xs !! i = Some y → xs !! j = Some z →
    is_arraylist xs cap ver a -∗
    WP set_then_get a (Z.of_nat i) (Z.of_nat j) x
      {{ v, ⌜ v = LitV (LitInt z) ⌝ ∗ is_arraylist (al_set xs i x) cap ver a }}.
  Proof.
    iIntros (Hij Hy Hz) "Ha".
    iApply (wp_bind [LetCtx None (call_al_get a (Z.of_nat j))]).
    iApply (wp_wand with "[Ha]").
    { iApply (al_set_spec with "Ha"). exact Hy. }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (al_get_spec with "Ha"). rewrite /al_set. by apply al_set_lookup_ne. }
    iIntros (v) "[%Hv Ha]".
    iSplit; [done|]. iFrame.
  Qed.

  Lemma set_then_size_spec xs cap ver (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_arraylist xs cap ver a -∗
    WP set_then_size a (Z.of_nat i) x
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs))) ⌝ ∗
            is_arraylist (al_set xs i x) cap ver a }}.
  Proof.
    iIntros (Hy) "Ha".
    iApply (wp_bind [LetCtx None (call_size a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (al_set_spec with "Ha"). exact Hy. }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (size_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite al_set_length in Hv.
    iSplit; [done|]. iFrame.
  Qed.

  Lemma set_then_version_spec xs cap ver (a : val_cjr) (i : nat) y x :
    xs !! i = Some y →
    is_arraylist xs cap ver a -∗
    WP set_then_version a (Z.of_nat i) x
      {{ v, ⌜ v = LitV (LitInt ver) ⌝ ∗ is_arraylist (al_set xs i x) cap ver a }}.
  Proof.
    iIntros (Hy) "Ha".
    iApply (wp_bind [LetCtx None (call_version a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (al_set_spec with "Ha"). exact Hy. }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (version_spec with "Ha").
  Qed.

  Definition remove_then_size (a : val_cjr) (i : Z) : expr :=
    Let None (call_remove a i) (call_size a).

  Lemma remove_then_size_spec xs cap ver (a : val_cjr) (j : nat) y :
    (j < length xs)%nat → xs !! j = Some y →
    is_arraylist xs cap ver a -∗
    WP remove_then_size a (Z.of_nat j)
      {{ v, ⌜ v = LitV (LitInt (Z.of_nat (length xs - 1))) ⌝ ∗
            is_arraylist (al_remove xs j) cap (ver + 1)%Z a }}.
  Proof.
    iIntros (Hj Hy) "Ha".
    iApply (wp_bind [LetCtx None (call_size a)]).
    iApply (wp_wand with "[Ha]").
    { iApply (remove_spec with "Ha"); [exact Hj|exact Hy]. }
    iIntros (u) "[%Hu Ha]".
    iApply wp_let. simpl.
    iApply (wp_wand with "[Ha]").
    { iApply (size_spec with "Ha"). }
    iIntros (v) "[%Hv Ha]".
    rewrite (al_remove_length xs j Hj) in Hv.
    iSplit; [done|]. iFrame.
  Qed.
End array_list.
