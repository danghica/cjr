(** Kernel-checked source and extraction regressions for managed buffers. *)
From Coq Require Import String List Lia.
From cjr Require Import generic_laws buffer_laws.
From cjr.examples Require Import generic_print poly_array.
From iris.proofmode Require Import proofmode.
Import ListNotations.
Local Open Scope string_scope.

Example poly_nested_type_substitution :
  gty_subst [("T", GTBool)] (GTBuffer (poly_ty (GTBuffer poly_t))) =
    GTBuffer (poly_ty (GTBuffer GTBool)).
Proof. reflexivity. Qed.
Example poly_nested_wf : gty_wf poly_layouts [] (poly_ty (poly_ty GTBool)) = true.
Proof. reflexivity. Qed.
Example poly_unbound_element_rejected :
  check_expr [] [] [] [] (GEBufferMake poly_t (GEVal (LitV (LitInt 2))) (GEVal (LitV LitUnit))) =
    ["unbound type variable, unknown type, or wrong type arity"].
Proof. reflexivity. Qed.
Example poly_wrong_arity_rejected :
  check_expr poly_layouts poly_functions [] []
    (GEStaticCall (poly_ty GTInt) "make" [GTBool] [GEVal (LitV (LitInt 2)); GEVal (LitV (LitInt 0))]) =
    ["wrong static method type arity: make"].
Proof. reflexivity. Qed.
Example poly_storage_name_reserved : identifier "CjrBuffer" = false.
Proof. reflexivity. Qed.
Example poly_nested_print :
  print_type (GTBuffer (poly_ty GTBool)) = "CjrBuffer<PolyArray<Bool>>".
Proof. reflexivity. Qed.
Example poly_all_operations_owned :
  map gf_owner poly_functions = replicate 4 (Some "PolyArray").
Proof. reflexivity. Qed.
Example poly_factory_print :
  print_expr poly_layouts (poly_make GTBool 2 (LitV (LitBool false))) =
    "PolyArray<Bool>.make(2, false)".
Proof. reflexivity. Qed.
Example poly_factory_owner_arity_rejected :
  check_expr poly_layouts poly_functions [] []
    (GEStaticCall (GTNamed "PolyArray" [GTInt; GTBool]) "make" []
      [GEVal (LitV (LitInt 2)); GEVal (LitV (LitInt 0))]) =
    ["unbound type variable, unknown type, or wrong type arity"].
Proof. reflexivity. Qed.
Example poly_static_instance_call_rejected :
  check_expr poly_layouts poly_functions [] ["arr"]
    (GEMethod (poly_ty GTBool) (GEVar "arr") "make" [] [GEVal (LitV (LitInt 2))]) =
    ["static method requires a type-qualified call: make"].
Proof. reflexivity. Qed.
Example poly_instance_static_call_rejected :
  check_expr poly_layouts poly_functions [] ["arr"]
    (GEStaticCall (poly_ty GTBool) "get" [] [GEVar "arr"; GEVal (LitV (LitInt 0))]) =
    ["instance method requires a receiver: get"].
Proof. reflexivity. Qed.
Example poly_method_type_arity_rejected :
  check_expr poly_layouts poly_functions [] ["arr"]
    (GEMethod (poly_ty GTBool) (GEVar "arr") "get" [GTBool] [GEVal (LitV (LitInt 0))]) =
    ["wrong method type arity: get"].
Proof. reflexivity. Qed.
Example poly_static_unknown_rejected :
  check_expr poly_layouts poly_functions [] []
    (GEStaticCall (poly_ty GTBool) "missing" [] []) =
    ["unresolved static method: PolyArray.missing"].
Proof. reflexivity. Qed.
Example poly_factory_argument_arity_rejected :
  check_expr poly_layouts poly_functions [] []
    (GEStaticCall (poly_ty GTBool) "make" [] []) =
    ["wrong static method argument arity: make"].
Proof. reflexivity. Qed.
Example poly_factory_call_erasure_uniform s :
  erase poly_layouts poly_runtime (ginstantiate s (poly_make poly_t 2 (LitV (LitBool false)))) =
    erase poly_layouts poly_runtime (poly_make poly_t 2 (LitV (LitBool false))).
Proof. apply erase_instantiate. reflexivity. Qed.
Example poly_factory_call_substitution fs x v :
  subst x v (resolve fs "PolyArray.make") = resolve fs "PolyArray.make" →
  erase poly_layouts fs
    (gsubst x v (GEStaticCall (poly_ty poly_t) "make" [] [GEVar "n"; GEVar "seed"])) =
  subst x v (erase poly_layouts fs
    (GEStaticCall (poly_ty poly_t) "make" [] [GEVar "n"; GEVar "seed"])).
Proof. intros H. apply erase_subst. simpl. intros n [<-|[]]. exact H. Qed.
Example poly_make_erasure_uniform s :
  erase poly_layouts [] (ginstantiate s (gf_body poly_make_fn)) =
    erase poly_layouts [] (gf_body poly_make_fn).
Proof. apply erase_instantiate. reflexivity. Qed.
Example poly_get_erasure_uniform s :
  erase poly_layouts [] (ginstantiate s (gf_body poly_get_fn)) =
    erase poly_layouts [] (gf_body poly_get_fn).
Proof. apply erase_instantiate. reflexivity. Qed.
Example poly_set_erasure_uniform s :
  erase poly_layouts [] (ginstantiate s (gf_body poly_set_fn)) =
    erase poly_layouts [] (gf_body poly_set_fn).
Proof. apply erase_instantiate. reflexivity. Qed.
Example poly_make_substitution x v :
  erase poly_layouts [] (gsubst x v (gf_body poly_make_fn)) =
    subst x v (erase poly_layouts [] (gf_body poly_make_fn)).
Proof. apply erase_subst. simpl. intros n H. contradiction. Qed.
Example poly_set_substitution x v :
  erase poly_layouts [] (gsubst x v (gf_body poly_set_fn)) =
    subst x v (erase poly_layouts [] (gf_body poly_set_fn)).
Proof. apply erase_subst. simpl. intros n H. contradiction. Qed.

Section instances.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  Example poly_bool_roundtrip a :
    is_poly_array [LitV (LitBool false); LitV (LitBool false)] a -∗
    generic_wp poly_layouts poly_runtime
      (GELet None (poly_set GTBool a 1 (LitV (LitBool true))) (poly_get GTBool a 1))
      (λ v, ⌜v = LitV (LitBool true)⌝ ∗
        is_poly_array [LitV (LitBool false); LitV (LitBool true)] a).
  Proof. iApply (poly_set_get_same GTBool); [done|apply closed_lit]. Qed.

  Example poly_int_roundtrip a :
    is_poly_array [LitV (LitInt 0)] a -∗
    generic_wp poly_layouts poly_runtime
      (GELet None (poly_set GTInt a 0 (LitV (LitInt 42))) (poly_get GTInt a 0))
      (λ v, ⌜v = LitV (LitInt 42)⌝ ∗ is_poly_array [LitV (LitInt 42)] a).
  Proof. iApply (poly_set_get_same GTInt); [done|apply closed_lit]. Qed.

  (** The outer array owns exactly one inner-array resource. *)
  Lemma poly_nested_singleton_spec t xs a :
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime (poly_make (poly_ty t) 1 a)
      (poly_array_rep (is_poly_array xs) [a]).
  Proof.
    iIntros "Ha". iDestruct "Ha" as (o base ->) "(Hlen & Hdata & Hblock & Hcells)".
    iApply (poly_make_owned_spec (is_poly_array xs) (poly_ty t) 1 (LitV (LitObj o))); [lia|apply closed_lit|].
    rewrite big_sepL_singleton. iExists o, base. iSplit; [done|]. iFrame.
  Qed.
End instances.
