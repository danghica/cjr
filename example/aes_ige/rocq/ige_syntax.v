(** Parameter instantiation shared by the IGE loop and its entry point. *)
From Coq Require Import ZArith List String.
From cjr Require Import primitive_laws.
From cjr.aes_ige Require Import program memory kernels syntax.
Import ListNotations.
Open Scope string_scope.
Definition ige_environment p q n iv s nr w e :=
 subst "work" (LitV (LitPtr w))
 (subst "nr" (LitV (LitInt nr))
 (subst "schedule" (LitV (LitPtr s))
 (subst "iv" (LitV (LitPtr iv))
 (subst "len" (LitV (LitInt n))
 (subst "dst" (LitV (LitPtr q))
 (subst "src" (LitV (LitPtr p)) e)))))).
Definition iteration_at enc p q n iv s nr w l :=
 subst_var "i" l (ige_environment p q n iv s nr w (ige_iteration enc)).
Definition counter l := Val (LitV (LitStack l)).
Definition loop_at enc p q n iv s nr w l :=
 While (le (StackLoad (counter l)) (BinOp MinusOp (int n) (int 16)))
   (Seq (iteration_at enc p q n iv s nr w l)
        (StackAssign (counter l) (plus (StackLoad (counter l)) (int 16)))).

Local Transparent copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body.
Lemma copy_body_stack_i l : subst_var "i" l copy_body = copy_body.
Proof. reflexivity. Qed.
Lemma xor_body_stack_i l : subst_var "i" l xor_body = xor_body.
Proof. reflexivity. Qed.
Lemma sub_body_stack_i l : subst_var "i" l sub_body = sub_body.
Proof. reflexivity. Qed.
Lemma inv_sub_body_stack_i l : subst_var "i" l inv_sub_body = inv_sub_body.
Proof. reflexivity. Qed.
Lemma shift_body_stack_i l : subst_var "i" l shift_body = shift_body.
Proof. reflexivity. Qed.
Lemma inv_shift_body_stack_i l : subst_var "i" l inv_shift_body = inv_shift_body.
Proof. reflexivity. Qed.
Lemma mix_body_stack_i l : subst_var "i" l mix_body = mix_body.
Proof. reflexivity. Qed.
Opaque copy_body xor_body sub_body inv_sub_body shift_body inv_shift_body mix_body encrypt_body decrypt_body.
Definition ige_loop_source enc :=
 seqs [While (le (Var "i") (BinOp MinusOp (Var "len") (int 16)))
   (Seq (ige_iteration enc) (Assign "i" (plus (Var "i") (int 16))))] (bool_e true).
Lemma ige_bound_loop enc p q n iv s nr w l :
 subst_var "i" l (ige_environment p q n iv s nr w (ige_loop_source enc)) =
 Seq (loop_at enc p q n iv s nr w l) (bool_e true).
Proof. unfold ige_loop_source, seqs, ige_environment, loop_at, iteration_at,
 le, int, counter, plus, bool_e. reflexivity. Qed.
Lemma ige_iteration_args enc v : subst "args" v (ige_iteration enc) = ige_iteration enc.
Proof. destruct enc; reflexivity. Qed.
Lemma ige_loop_source_args enc v : subst "args" v (ige_loop_source enc) = ige_loop_source enc.
Proof. unfold ige_loop_source, seqs, le, plus, int, bool_e; simpl. rewrite ige_iteration_args. reflexivity. Qed.
