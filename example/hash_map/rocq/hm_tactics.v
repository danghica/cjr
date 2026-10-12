(** Small evaluation-context automation shared by the HashMap proofs. *)
From iris.proofmode Require Import proofmode environments.
From cjr Require Import notation primitive_laws.
From cjr.examples Require Import array.
From iris.prelude Require Import options.

Ltac hm_focus e k :=
  lazymatch e with
  | Let ?x (Val ?v) ?b => k ()
  | Let ?x ?a ?b => iApply (wp_bind [LetCtx x b]); hm_focus a k
  | Seq (Val ?v) ?b => k ()
  | Seq ?a ?b => iApply (wp_bind [SeqCtx b]); hm_focus a k
  | App (Val ?v) (Val ?w) => k ()
  | App (Val ?v) ?a => iApply (wp_bind [AppRCtx v]); hm_focus a k
  | App ?a ?b => iApply (wp_bind [AppLCtx b]); hm_focus a k
  | Struct ?vs [] => k ()
  | Struct ?vs ((Val ?v) :: ?es) => k ()
  | Struct ?vs (?a :: ?es) => iApply (wp_bind [StructCtx vs es]); hm_focus a k
  | New ?vs [] => k ()
  | New ?vs ((Val ?v) :: ?es) => k ()
  | New ?vs (?a :: ?es) => iApply (wp_bind [NewCtx vs es]); hm_focus a k
  | StructLoad (Val ?v) ?i => k ()
  | StructLoad ?a ?i => iApply (wp_bind [StructLoadCtx i]); hm_focus a k
  | FieldLoad (Val ?v) ?i => k ()
  | FieldLoad ?a ?i => iApply (wp_bind [FieldLoadCtx i]); hm_focus a k
  | FieldStore (Val ?v) ?i (Val ?w) => k ()
  | FieldStore (Val ?v) ?i ?a => iApply (wp_bind [FieldStoreRCtx v i]); hm_focus a k
  | FieldStore ?a ?i ?b => iApply (wp_bind [FieldStoreLCtx i b]); hm_focus a k
  | BinOp ?op (Val ?v) (Val ?w) => k ()
  | BinOp ?op (Val ?v) ?a => iApply (wp_bind [BinOpRCtx op v]); hm_focus a k
  | BinOp ?op ?a ?b => iApply (wp_bind [BinOpLCtx op b]); hm_focus a k
  | Load (Val ?v) => k ()
  | Load ?a => iApply (wp_bind [LoadCtx]); hm_focus a k
  | Store (Val ?v) (Val ?w) => k ()
  | Store (Val ?v) ?a => iApply (wp_bind [StoreRCtx v]); hm_focus a k
  | Store ?a ?b => iApply (wp_bind [StoreLCtx b]); hm_focus a k
  | Offset (Val ?v) (Val ?w) => k ()
  | Offset (Val ?v) ?a => iApply (wp_bind [OffsetRCtx v]); hm_focus a k
  | Offset ?a ?b => iApply (wp_bind [OffsetLCtx b]); hm_focus a k
  | If (Val ?v) ?a ?b => k ()
  | If ?c ?a ?b => iApply (wp_bind [IfCtx a b]); hm_focus c k
  | _ => k ()
  end.

Ltac hm_head :=
  first [iApply wp_let; simpl
        | iApply wp_seq
        | iApply wp_rec; iIntros "!> _"
        | iApply wp_app; simpl
        | iApply wp_offset; iIntros "!> _"
        | iApply wp_struct_step
        | iApply wp_struct_done; iIntros "!> _"
        | iApply wp_new_step
        | iApply wp_struct_load; [reflexivity|iIntros "!> _"]
        | iApply wp_binop; [reflexivity|iIntros "!> _"]
        | iApply wp_value'].
Ltac hm_pure :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with
    | |- envs_entails _ (WP ?e {{ ?Φ }}) => hm_focus e ltac:(fun _ => hm_head)
    end); simpl; cbn [fill fill_item].

Ltac hm_take :=
  match goal with
  | |- envs_entails _ (WP Let ?x ?e ?b {{ ?Φ }}) => iApply (wp_bind [LetCtx x b])
  end.

Ltac hm_read_head :=
  match goal with
  | |- envs_entails _ (WP FieldLoad (Val (LitV (LitObj ?o))) ?i {{ ?P }}) =>
    iApply (wp_field_load o i with "[$]"); iIntros "!> _ ?"
  end.
Ltac hm_read :=
  match goal with
  | |- envs_entails _ (WP ?e {{ ?Φ }}) => hm_focus e ltac:(fun _ => hm_read_head)
  end.

Ltac hm_admin_head :=
  first [iApply wp_let; simpl
        | iApply wp_seq
        | iApply wp_struct_step
        | iApply wp_struct_done; iIntros "!> _"
        | iApply wp_struct_load; [reflexivity|iIntros "!> _"]
        | iApply wp_binop; [reflexivity|iIntros "!> _"]
        | iApply wp_value'].
Ltac hm_admin :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with
    | |- envs_entails _ (WP ?e {{ ?Φ }}) => hm_focus e ltac:(fun _ => hm_admin_head)
    end); simpl; cbn [fill fill_item].

(** Evaluate arguments and closures, leaving a function application for a
    separately proved specification. *)
Ltac hm_args_head :=
  first [iApply wp_rec; iIntros "!> _" | hm_admin_head].
Ltac hm_args :=
  iStartProof; repeat (simpl; cbn [fill fill_item];
    match goal with
    | |- envs_entails _ (WP ?e {{ ?Φ }}) => hm_focus e ltac:(fun _ => hm_args_head)
    end); simpl; cbn [fill fill_item].

Ltac hm_write_head :=
  match goal with
  | |- envs_entails _ (WP FieldStore (Val (LitV (LitObj ?o))) ?i (Val ?v) {{ ?P }}) =>
    iApply (wp_field_store o i with "[$]"); iIntros "!> _ ?"
  end.
Ltac hm_write :=
  match goal with
  | |- envs_entails _ (WP ?e {{ ?Φ }}) => hm_focus e ltac:(fun _ => hm_write_head)
  end.
