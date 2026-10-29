(** A separate polymorphic adaptation of example/array: the same length,
    pointer and contiguous-cell model, generalized from integers to values.
    Native storage is managed Array<T>, not a size assumption about T. *)
From iris.proofmode Require Import proofmode.
From cjr Require Import generic_laws buffer_laws primitive_laws.
From cjr.examples Require Import generic_print array.
From iris.prelude Require Import options.
From Coq Require Import Lia.
Import ListNotations.
Local Open Scope string_scope.

Definition poly_t := GTVar "T".
Definition poly_ty t := GTNamed "PolyArray" [t].
Definition poly_layout := GLayout "PolyArray" GClass ["T"]
  [("len", GTInt); ("data", GTBuffer poly_t)].
Definition poly_layouts := [poly_layout].
Definition poly_make_fn := GStaticFunction "make" "PolyArray" []
  [("n", GTInt); ("seed", poly_t)] (poly_ty poly_t)
  (GELet (Some "p") (GEBufferMake poly_t (GEVar "n") (GEVar "seed"))
    (GEConstruct (poly_ty poly_t) [GEVar "n"; GEVar "p"])).
Definition poly_length_fn := GFunction "length" (Some "PolyArray") []
  [("arr", poly_ty poly_t)] GTInt (GEField (poly_ty poly_t) (GEVar "arr") 0).
Definition poly_get_fn := GFunction "get" (Some "PolyArray") []
  [("arr", poly_ty poly_t); ("i", GTInt)] poly_t
  (GEBufferGet poly_t (GEField (poly_ty poly_t) (GEVar "arr") 1) (GEVar "i")).
Definition poly_set_fn := GFunction "set" (Some "PolyArray") []
  [("arr", poly_ty poly_t); ("i", GTInt); ("x", poly_t)] GTUnit
  (GEBufferSet poly_t (GEField (poly_ty poly_t) (GEVar "arr") 1) (GEVar "i") (GEVar "x")).
Definition poly_functions := [poly_make_fn; poly_length_fn; poly_get_fn; poly_set_fn].
Definition poly_runtime := link_functions poly_layouts [] poly_functions.
Definition poly_make t n seed := GEStaticCall (poly_ty t) "make" [] [GEVal (LitV (LitInt (Z.of_nat n))); GEVal seed].
Definition poly_length t a := GEMethod (poly_ty t) (GEVal a) "length" [] [].
Definition poly_get t a i := GEMethod (poly_ty t) (GEVal a) "get" [] [ GEVal (LitV (LitInt (Z.of_nat i)))].
Definition poly_set t a i x := GEMethod (poly_ty t) (GEVal a) "set" [] [ GEVal (LitV (LitInt (Z.of_nat i))); GEVal x].
Definition poly_program := GProgram poly_layouts poly_functions
  (poly_make GTBool 3 (LitV (LitBool false))).

Example poly_program_checked : check_program poly_program = [].
Proof. vm_compute. reflexivity. Qed.

Section proofs.
  Context `{!cjrGS Σ} `{!invGS_gen HasLc Σ}.

  (** Adapted verbatim in shape from [array.is_array]. The only change in
      cells is [list val] instead of [list Z] and removal of [LitInt]. *)
  Definition is_poly_array (xs : list val) (a : val) : iProp Σ :=
    ∃ o base, ⌜a = LitV (LitObj o)⌝ ∗
      ObjId o ↦ₒ[0] LitV (LitInt (Z.of_nat (length xs))) ∗
      ObjId o ↦ₒ[1] LitV (LitPtr base) ∗
      RawId base ↦ᵦ length xs ∗ buffer_cells base xs.

  Definition poly_array_rep (R : val → iProp Σ) xs a : iProp Σ :=
    is_poly_array xs a ∗ [∗ list] v ∈ xs, R v.

  Lemma poly_int_adaptation xs a :
    is_poly_array (map (λ z, LitV (LitInt z)) xs) a ⊣⊢ array.is_array xs a.
  Proof.
    unfold is_poly_array, array.is_array, buffer_cells, array.array_cells.
    rewrite length_map. setoid_rewrite big_sepL_fmap. done.
  Qed.

  Lemma poly_make_spec t n seed : (0 < n)%nat → closed_val seed →
    ⊢ generic_wp poly_layouts poly_runtime (poly_make t n seed)
      (is_poly_array (replicate n seed)).
  Proof.
    intros Hn Hclosed. unfold generic_wp, poly_make. simpl.
    iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [LitV (LitInt (Z.of_nat n)); seed]). simpl.
    iApply wp_app. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [AppRCtx buffer_make_val; LetCtx _ _]).
    iApply (wp_generic_pack_acc [] [LitV (LitInt (Z.of_nat n)); seed]). simpl app.
    iApply (wp_bind [LetCtx _ _]). iApply wp_wand.
    { iApply wp_buffer_make; done. }
    iIntros (v) "H". iDestruct "H" as (base ->) "[Hblock Hcells]".
    iApply wp_let. simpl. iApply wp_generic_new_step. simpl.
    iApply wp_generic_new_step. simpl. iApply wp_new.
    iIntros (o) "[Hlen [Hdata _]]". iExists o, base.
    rewrite length_replicate. iSplit; [done|]. iFrame.
  Qed.

  Lemma poly_length_spec t xs a :
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime (poly_length t a)
      (λ v, ⌜v = LitV (LitInt (Z.of_nat (length xs)))⌝ ∗ is_poly_array xs a).
  Proof.
    iIntros "Ha". iDestruct "Ha" as (o base ->) "(Hlen & Hdata & Hblock & Hcells)".
    unfold generic_wp, poly_length. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [LitV (LitObj o)]). simpl. iApply wp_app. simpl.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl. iApply (wp_field_load with "Hlen").
    iIntros "!> _ Hlen". iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma poly_get_spec t xs a i x : xs !! i = Some x →
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime (poly_get t a i)
      (λ v, ⌜v = x⌝ ∗ is_poly_array xs a).
  Proof.
    iIntros (Hi) "Ha". iDestruct "Ha" as (o base ->) "(Hlen & Hdata & Hblock & Hcells)".
    unfold generic_wp, poly_get. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [LitV (LitObj o); LitV (LitInt (Z.of_nat i))]). simpl.
    iApply wp_app. simpl.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [OffsetLCtx _; LoadCtx]). iApply (wp_field_load with "Hdata").
    iIntros "!> _ Hdata". iApply (wp_bind [LoadCtx]). iApply wp_offset.
    iIntros "!> _". iDestruct (big_sepL_lookup_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_load with "Hi"). iIntros "!> _ Hi".
    iDestruct ("Hclose" with "Hi") as "Hcells".
    iSplit; [done|]. iExists o, base. iSplit; [done|]. iFrame.
  Qed.

  Lemma poly_set_spec t xs a i old x : xs !! i = Some old → closed_val x →
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime (poly_set t a i x)
      (λ v, ⌜v = LitV LitUnit⌝ ∗ is_poly_array (<[i := x]> xs) a).
  Proof.
    iIntros (Hi Hclosed) "Ha".
    iDestruct "Ha" as (o base ->) "(Hlen & Hdata & Hblock & Hcells)".
    unfold generic_wp, poly_set. simpl. iApply (wp_bind [AppRCtx _]).
    iApply (wp_generic_pack_acc [] [LitV (LitObj o); LitV (LitInt (Z.of_nat i)); x]). simpl.
    iApply wp_app. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl. rewrite ?Hclosed.
    iApply (wp_bind [LetCtx _ _]); iApply wp_struct_load; [done|].
    iIntros "!> _". iApply wp_let. simpl.
    iApply (wp_bind [OffsetLCtx _; StoreLCtx _]). iApply (wp_field_load with "Hdata").
    iIntros "!> _ Hdata". iApply (wp_bind [StoreLCtx _]). iApply wp_offset.
    iIntros "!> _". iDestruct (big_sepL_insert_acc with "Hcells") as "[Hi Hclose]"; [exact Hi|].
    iApply (wp_store with "Hi"). iIntros "!> _ Hi".
    iDestruct ("Hclose" $! x with "Hi") as "Hcells".
    iSplit; [done|]. iExists o, base. rewrite length_insert. iSplit; [done|]. iFrame.
  Qed.

  (** Reading exposes an element resource together with a way to restore
      the array. This is a borrow, not a duplicate of that resource. *)
  Lemma poly_get_owned_spec (R : val → iProp Σ) t xs a i x : xs !! i = Some x →
    poly_array_rep R xs a -∗ generic_wp poly_layouts poly_runtime (poly_get t a i)
      (λ v, ⌜v = x⌝ ∗ R v ∗ (R v -∗ poly_array_rep R xs a)).
  Proof.
    iIntros (Hi) "[Ha HR]". iApply (wp_wand with "[Ha]").
    { iApply (poly_get_spec t with "Ha"). exact Hi. }
    iIntros (v) "[%Hv Ha]". subst v.
    iDestruct (big_sepL_lookup_acc with "HR") as "[Hx Hclose]"; [exact Hi|].
    iSplit; [done|]. iFrame "Hx". iIntros "Hx".
    iFrame "Ha". iApply ("Hclose" with "Hx").
  Qed.

  (** The overwritten element's ownership is returned to the caller. *)
  Lemma poly_set_owned_spec (R : val → iProp Σ) t xs a i old x :
    xs !! i = Some old → closed_val x →
    poly_array_rep R xs a -∗ R x -∗
    generic_wp poly_layouts poly_runtime (poly_set t a i x)
      (λ v, ⌜v = LitV LitUnit⌝ ∗ poly_array_rep R (<[i := x]> xs) a ∗ R old).
  Proof.
    iIntros (Hi Hclosed) "[Ha HR] Hx". iApply (wp_wand with "[Ha]").
    { iApply (poly_set_spec t xs a i old x with "Ha"); done. }
    iIntros (v) "[Hv Ha]".
    iDestruct (big_sepL_insert_acc with "HR") as "[Hold Hclose]"; [exact Hi|].
    iDestruct ("Hclose" $! x with "Hx") as "HR". iFrame.
  Qed.

  Lemma poly_make_owned_spec (R : val → iProp Σ) t n seed :
    (0 < n)%nat → closed_val seed →
    ([∗ list] v ∈ replicate n seed, R v) -∗
    generic_wp poly_layouts poly_runtime (poly_make t n seed)
      (poly_array_rep R (replicate n seed)).
  Proof.
    iIntros (Hn Hclosed) "HR". iApply wp_wand.
    { iApply (poly_make_spec t); done. }
    iIntros (a) "Ha". iFrame.
  Qed.

  Lemma poly_make_persistent_spec (R : val → iProp Σ) t n seed
      `{!Persistent (R seed)} : (0 < n)%nat → closed_val seed →
    R seed -∗ generic_wp poly_layouts poly_runtime (poly_make t n seed)
      (poly_array_rep R (replicate n seed)).
  Proof.
    iIntros (Hn Hclosed) "#HR". iApply (poly_make_owned_spec R t); [done|done|].
    iApply big_sepL_intro. iIntros "!>" (i v Hi).
    apply lookup_replicate in Hi as [-> _]. done.
  Qed.

  Lemma poly_set_get_same t xs a i old x : xs !! i = Some old → closed_val x →
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime
      (GELet None (poly_set t a i x) (poly_get t a i))
      (λ v, ⌜v = x⌝ ∗ is_poly_array (<[i := x]> xs) a).
  Proof.
    iIntros (Hi Hclosed) "Ha". unfold generic_wp. simpl erase.
    iApply (wp_bind [LetCtx None _]). iApply (wp_wand with "[Ha]").
    { iApply (poly_set_spec t xs a i old x with "Ha"); done. }
    iIntros (v) "[_ Ha]". iApply wp_let. simpl subst_binder.
    iApply (poly_get_spec t with "Ha"). apply list_lookup_insert. by eapply lookup_lt_Some.
  Qed.

  Lemma poly_set_get_other t xs a i j old y x :
    i ≠ j → xs !! i = Some old → xs !! j = Some y → closed_val x →
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime
      (GELet None (poly_set t a i x) (poly_get t a j))
      (λ v, ⌜v = y⌝ ∗ is_poly_array (<[i := x]> xs) a).
  Proof.
    iIntros (Hij Hi Hj Hclosed) "Ha". unfold generic_wp. simpl erase.
    iApply (wp_bind [LetCtx None _]). iApply (wp_wand with "[Ha]").
    { iApply (poly_set_spec t xs a i old x with "Ha"); done. }
    iIntros (v) "[_ Ha]". iApply wp_let. simpl subst_binder.
    iApply (poly_get_spec t with "Ha"). by rewrite list_lookup_insert_ne.
  Qed.

  Lemma poly_set_length t xs a i old x : xs !! i = Some old → closed_val x →
    is_poly_array xs a -∗ generic_wp poly_layouts poly_runtime
      (GELet None (poly_set t a i x) (poly_length t a))
      (λ v, ⌜v = LitV (LitInt (Z.of_nat (length xs)))⌝ ∗ is_poly_array (<[i := x]> xs) a).
  Proof.
    iIntros (Hi Hclosed) "Ha". unfold generic_wp. simpl erase.
    iApply (wp_bind [LetCtx None _]). iApply (wp_wand with "[Ha]").
    { iApply (poly_set_spec t xs a i old x with "Ha"); done. }
    iIntros (v) "[_ Ha]". iApply wp_let. simpl subst_binder.
    iApply (wp_wand with "[Ha]").
    { iApply (poly_length_spec t with "Ha"). }
    iIntros (w) "[%Hw Ha]". rewrite length_insert in Hw. iFrame. done.
  Qed.

  Lemma poly_fresh_get t n seed i : (0 < n)%nat → (i < n)%nat → closed_val seed →
    ⊢ generic_wp poly_layouts poly_runtime (poly_make t n seed)
      (λ a, is_poly_array (replicate n seed) a ∗
        (is_poly_array (replicate n seed) a -∗
          generic_wp poly_layouts poly_runtime (poly_get t a i)
            (λ v, ⌜v = seed⌝ ∗ is_poly_array (replicate n seed) a))).
  Proof.
    intros Hn Hi Hclosed. iApply wp_wand.
    { iApply (poly_make_spec t); done. }
    iIntros (a) "Ha". iFrame "Ha". iIntros "Ha".
    iApply (poly_get_spec t with "Ha"). apply lookup_replicate. done.
  Qed.

  Lemma poly_main_wp :
    ⊢ generic_wp poly_layouts poly_runtime (gp_main poly_program)
      (λ a, ⌜∃ o, a = LitV (LitObj o)⌝).
  Proof.
    iApply wp_wand.
    { iApply (poly_make_spec GTBool 3 (LitV (LitBool false))); [lia|apply closed_lit]. }
    iIntros (a) "Ha". iDestruct "Ha" as (o base) "(%Ha & _)".
    iPureIntro. exists o. done.
  Qed.
End proofs.

Lemma poly_main_adequate Σ `{!cjrGpreS Σ} :
  adequate NotStuck (erase_program poly_program) state_init (λ a _, ∃ o, a = LitV (LitObj o)).
Proof. apply (generic_adequacy Σ). intros ??. apply poly_main_wp. Qed.
