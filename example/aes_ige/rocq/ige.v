(** OpenSSL-compatible IGE: the IV is (previous ciphertext, previous plaintext). *)
From Coq Require Import ZArith List Lia.
From cjr.aes_ige Require Import bytes block aes.
Import ListNotations.
Definition iv := (block * block)%type.
Definition iv_bytes (v : iv) := block_bytes (fst v) /\ block_bytes (snd v).
Fixpoint ige_encrypt key (xs : list block) (v : iv) : list block * iv :=
  match xs with [] => ([],v) | p::ps =>
    let c := xor (encrypt key (xor p (fst v))) (snd v) in
    let '(cs,w) := ige_encrypt key ps (c,p) in (c::cs,w) end.
Fixpoint ige_decrypt key (xs : list block) (v : iv) : list block * iv :=
  match xs with [] => ([],v) | c::cs =>
    let p := xor (decrypt key (xor c (snd v))) (fst v) in
    let '(ps,w) := ige_decrypt key cs (c,p) in (p::ps,w) end.
Definition enc_step key p v := xor (encrypt key (xor p (fst v))) (snd v).
Definition dec_step key c v := xor (decrypt key (xor c (snd v))) (fst v).
Lemma enc_step_bytes key p v : block_bytes p -> iv_bytes v -> block_bytes (enc_step key p v).
Proof. intros Hp [Hc Hq]. apply xor_bytes; [apply encrypt_bytes, xor_bytes|]; assumption. Qed.
Lemma dec_step_bytes key c v : block_bytes c -> iv_bytes v -> block_bytes (dec_step key c v).
Proof. intros Hc [Hp Hq]. apply xor_bytes; [apply decrypt_bytes, xor_bytes|]; assumption. Qed.
Lemma step_inverse key p v : block_bytes p -> iv_bytes v -> dec_step key (enc_step key p v) v = p.
Proof. intros Hp [Hc Hq]. unfold enc_step, dec_step. rewrite xor_cancel.
  rewrite decrypt_encrypt by (apply xor_bytes; assumption). apply xor_cancel. Qed.
Lemma inverse_step key c v : block_bytes c -> iv_bytes v -> enc_step key (dec_step key c v) v = c.
Proof. intros Hc [Hp Hq]. unfold enc_step, dec_step. rewrite xor_cancel.
  rewrite encrypt_decrypt by (apply xor_bytes; assumption). apply xor_cancel. Qed.
Theorem ige_decrypt_encrypt key xs v : Forall block_bytes xs -> iv_bytes v ->
  ige_decrypt key (fst (ige_encrypt key xs v)) v = (xs, snd (ige_encrypt key xs v)).
Proof.
  revert v. induction xs as [|p ps IH]; intros v Hxs Hv; [reflexivity|].
  inversion Hxs as [|? ? Hp Hps]; subst.
  cbn [ige_encrypt]. change (xor (encrypt key (xor p (fst v))) (snd v)) with (enc_step key p v).
  destruct (ige_encrypt key ps (enc_step key p v,p)) as [cs w] eqn:E.
  cbn [fst snd ige_decrypt].
  change (xor (decrypt key (xor (enc_step key p v) (snd v))) (fst v)) with (dec_step key (enc_step key p v) v).
  rewrite step_inverse by assumption.
  specialize (IH (enc_step key p v,p) Hps).
  assert (iv_bytes (enc_step key p v,p)) as Hnext by (split; [apply enc_step_bytes|]; assumption).
  specialize (IH Hnext). rewrite E in IH. simpl in IH. rewrite IH. reflexivity.
Qed.
Theorem ige_encrypt_decrypt key xs v : Forall block_bytes xs -> iv_bytes v ->
  ige_encrypt key (fst (ige_decrypt key xs v)) v = (xs, snd (ige_decrypt key xs v)).
Proof.
  revert v. induction xs as [|c cs IH]; intros v Hxs Hv; [reflexivity|].
  inversion Hxs as [|? ? Hc Hcs]; subst.
  cbn [ige_decrypt]. change (xor (decrypt key (xor c (snd v))) (fst v)) with (dec_step key c v).
  destruct (ige_decrypt key cs (c,dec_step key c v)) as [ps w] eqn:E.
  cbn [fst snd ige_encrypt].
  change (xor (encrypt key (xor (dec_step key c v) (fst v))) (snd v)) with (enc_step key (dec_step key c v) v).
  rewrite inverse_step by assumption.
  specialize (IH (c,dec_step key c v) Hcs).
  assert (iv_bytes (c,dec_step key c v)) as Hnext by (split; [assumption|apply dec_step_bytes; assumption]).
  specialize (IH Hnext). rewrite E in IH. simpl in IH. rewrite IH. reflexivity.
Qed.
Theorem ige_encrypt_length key xs v : length (fst (ige_encrypt key xs v)) = length xs.
Proof. revert v; induction xs; intros; [reflexivity|]. simpl.
  destruct (ige_encrypt key xs _) eqn:E. simpl. f_equal. specialize (IHxs (xor (encrypt key (xor a (fst v))) (snd v),a)).
  rewrite E in IHxs. exact IHxs. Qed.
Theorem ige_decrypt_length key xs v : length (fst (ige_decrypt key xs v)) = length xs.
Proof. revert v; induction xs; intros; [reflexivity|]. simpl.
  destruct (ige_decrypt key xs _) eqn:E. simpl. f_equal. specialize (IHxs (a,xor (decrypt key (xor a (snd v))) (fst v))).
  rewrite E in IHxs. exact IHxs. Qed.
Theorem ige_encrypt_range key xs v : Forall block_bytes xs -> iv_bytes v ->
  Forall block_bytes (fst (ige_encrypt key xs v)) /\ iv_bytes (snd (ige_encrypt key xs v)).
Proof.
  revert v. induction xs as [|p ps IH]; intros v H Hv; [simpl; auto|].
  inversion H; subst. cbn [ige_encrypt].
  change (xor (encrypt key (xor p (fst v))) (snd v)) with (enc_step key p v).
  assert (block_bytes (enc_step key p v)) by (apply enc_step_bytes; assumption).
  specialize (IH (enc_step key p v,p)).
  destruct (ige_encrypt key ps (enc_step key p v,p)) as [cs w] eqn:E. simpl in *.
  specialize (IH ltac:(assumption) ltac:(split; assumption)). destruct IH.
  split; [constructor|]; assumption.
Qed.
Theorem ige_decrypt_range key xs v : Forall block_bytes xs -> iv_bytes v ->
  Forall block_bytes (fst (ige_decrypt key xs v)) /\ iv_bytes (snd (ige_decrypt key xs v)).
Proof.
  revert v. induction xs as [|c cs IH]; intros v H Hv; [simpl; auto|].
  inversion H; subst. cbn [ige_decrypt].
  change (xor (decrypt key (xor c (snd v))) (fst v)) with (dec_step key c v).
  assert (block_bytes (dec_step key c v)) by (apply dec_step_bytes; assumption).
  specialize (IH (c,dec_step key c v)).
  destruct (ige_decrypt key cs (c,dec_step key c v)) as [ps w] eqn:E. simpl in *.
  specialize (IH ltac:(assumption) ltac:(split; assumption)). destruct IH.
  split; [constructor|]; assumption.
Qed.
Theorem ige_encrypt_chunks key xs ys v :
  ige_encrypt key (xs ++ ys) v =
  let '(cs,w) := ige_encrypt key xs v in
  let '(ds,u) := ige_encrypt key ys w in (cs ++ ds,u).
Proof.
  revert v. induction xs as [|p ps IH]; intros v; [simpl; destruct (ige_encrypt key ys v); reflexivity|].
  cbn [app ige_encrypt]. rewrite IH.
  destruct (ige_encrypt key ps _) as [cs w]; destruct (ige_encrypt key ys w); reflexivity.
Qed.
Theorem ige_decrypt_chunks key xs ys v :
  ige_decrypt key (xs ++ ys) v =
  let '(ps,w) := ige_decrypt key xs v in
  let '(qs,u) := ige_decrypt key ys w in (ps ++ qs,u).
Proof.
  revert v. induction xs as [|c cs IH]; intros v; [simpl; destruct (ige_decrypt key ys v); reflexivity|].
  cbn [app ige_decrypt]. rewrite IH.
  destruct (ige_decrypt key cs _) as [ps w]; destruct (ige_decrypt key ys w); reflexivity.
Qed.
Theorem ige_encrypt_empty key v : ige_encrypt key [] v = ([],v).
Proof. reflexivity. Qed.
Theorem ige_decrypt_empty key v : ige_decrypt key [] v = ([],v).
Proof. reflexivity. Qed.
Theorem ige_encrypt_injective key xs ys v : Forall block_bytes xs -> Forall block_bytes ys -> iv_bytes v ->
  fst (ige_encrypt key xs v) = fst (ige_encrypt key ys v) -> xs = ys.
Proof. intros Hx Hy Hv E.
  pose proof (f_equal fst (ige_decrypt_encrypt key xs v Hx Hv)) as H.
  rewrite E, ige_decrypt_encrypt in H by assumption. symmetry. exact H. Qed.
Theorem ige_decrypt_injective key xs ys v : Forall block_bytes xs -> Forall block_bytes ys -> iv_bytes v ->
  fst (ige_decrypt key xs v) = fst (ige_decrypt key ys v) -> xs = ys.
Proof. intros Hx Hy Hv E.
  pose proof (f_equal fst (ige_encrypt_decrypt key xs v Hx Hv)) as H.
  rewrite E, ige_encrypt_decrypt in H by assumption. symmetry. exact H. Qed.
Theorem ige_encrypt_surjective key ys v : Forall block_bytes ys -> iv_bytes v ->
  exists xs, Forall block_bytes xs /\ length xs = length ys /\ fst (ige_encrypt key xs v) = ys.
Proof. intros Hy Hv. exists (fst (ige_decrypt key ys v)). repeat split.
  - apply (ige_decrypt_range key ys v Hy Hv).
  - apply ige_decrypt_length.
  - rewrite ige_encrypt_decrypt by assumption. reflexivity.
Qed.
Theorem ige_decrypt_surjective key ys v : Forall block_bytes ys -> iv_bytes v ->
  exists xs, Forall block_bytes xs /\ length xs = length ys /\ fst (ige_decrypt key xs v) = ys.
Proof. intros Hy Hv. exists (fst (ige_encrypt key ys v)). repeat split.
  - apply (ige_encrypt_range key ys v Hy Hv).
  - apply ige_encrypt_length.
  - rewrite ige_decrypt_encrypt by assumption. reflexivity.
Qed.
