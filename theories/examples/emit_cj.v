(** The Cangjie text of every example, printed from its defined core terms.
Proof coverage is documented per example; the most-frequent example has
a full Iris refinement theorem for its empty and nonempty branches. [make cj] writes each string to
[generated/cj/NAME.cj]. *)

From Coq Require Import String ZArith List.
From cjr Require Import lang.
From cjr.examples Require Import cj_print.
From cjr.examples Require arith struct_upd cell swap sum_block class_upd
  frame_call vtable list list_rev array array_list hash_map qsort most_frequent.
Import ListNotations.

Local Open Scope string_scope.

Definition int (n : Z) : expr := Val (LitV (LitInt n)).
Definition unit_e : expr := Val (LitV LitUnit).

Definition t_int := "Int64".
Definition t_ptr := "CPointer<Int64>".

(** * Layouts *)

Definition cell_s := Decl "Cell" [("x", t_int)].
Definition box_c := Decl "Box" [("value", t_int)].
Definition counter_c := Decl "Counter" [("value", t_int)].
Definition vtable_s := Decl "VTable" [("inc", "(Counter) -> Unit")].
Definition node_c := Decl "Node" [("isCons", "Bool"); ("value", t_int); ("next", "Node")].
Definition array_c := Decl "Array" [("len", t_int); ("data", t_ptr)].
Definition array_list_c :=
  Decl "ArrayList" [("myData", "Array"); ("mySize", t_int); ("myVersion", t_int)].
Definition hash_map_c :=
  Decl "HashMap" [("mySize", t_int); ("tags", "Array"); ("keys", "Array"); ("vals", "Array")].
Definition probe_result_s :=
  Decl "ProbeResult" [("found", "Bool"); ("index", t_int); ("value", t_int)].
Definition int64_opt_c :=
  Decl "Int64Option" [("ok", "Bool"); ("value", t_int)].

(** * Straight-line examples *)

Definition sum_one_fn := Fn "sumOne" None None arith.sum_one [] t_int.
Definition p_arith := Prog [] [] [sum_one_fn] arith.sum_one.

Definition p_struct_upd :=
  Prog [] [cell_s]
    [Fn "bump" None None struct_upd.bump [] t_int;
     Fn "bumpKeep" None None struct_upd.bump_keep [] t_int]
    struct_upd.bump_keep.

Definition p_cell := Prog [] [] [Fn "cell" None None cell.cell [] "Unit"] cell.cell.

Definition p_class_upd :=
  Prog [box_c] [] [Fn "classBump" None None class_upd.class_bump [] t_int]
    class_upd.class_bump.

Definition p_vtable :=
  Prog [counter_c] [vtable_s]
    [Fn "inc" None (Some "this") vtable.inc_body ["Counter"] "Unit";
     Fn "run" None None vtable.vtable_prog [] t_int]
    vtable.vtable_prog.

(** * Examples over raw addresses

The placeholder pointers are renamed back to the parameters they stand for. *)

Definition swap_body : expr :=
  Let (Some "l1") (StructLoad (Var "args") 0)
    (Let (Some "l2") (StructLoad (Var "args") 1)
      (rename_ptr 0 "l1" (rename_ptr 1 "l2" (swap.swap_at 0 1)))).

Definition p_swap :=
  Prog [] [] [Fn "swap" None (Some "args") swap_body [t_ptr; t_ptr] "Unit"]
    (Let (Some "l1") (Alloc (int 1))
      (Let (Some "l2") (Alloc (int 1))
        (Seq (Store (Var "l1") (int 1))
          (Seq (Store (Var "l2") (int 2))
            (App (Rec None (Some "args") swap_body)
              (Struct [] [Var "l1"; Var "l2"])))))).

Definition sum_at_body : expr := rename_ptr 0 "p" (sum_block.sum_at 0).

Definition p_sum_block :=
  Prog [] [] [Fn "sumAt" None (Some "p") sum_at_body [t_ptr] t_int]
    (Let (Some "p") (Alloc (int 1))
      (Seq (Store (Var "p") (int 4))
        (App (Rec None (Some "p") sum_at_body) (Var "p")))).

Definition write_body : expr :=
  match frame_call.write_call 0 1 with
  | Let _ (Rec _ _ b) _ => b
  | _ => unit_e
  end.

Definition frame_body : expr :=
  Let (Some "p") (StructLoad (Var "args") 0)
    (Let (Some "q") (StructLoad (Var "args") 1)
      (rename_ptr 0 "p" (rename_ptr 1 "q" (frame_call.write_call 0 1)))).

Definition p_frame_call :=
  Prog [] []
    [Fn "write" None (Some "x") write_body [t_ptr] "Unit";
     Fn "frameCall" None (Some "args") frame_body [t_ptr; t_ptr] t_int]
    (Let (Some "p") (Alloc (int 1))
      (Let (Some "q") (Alloc (int 1))
        (Seq (Store (Var "q") (int 3))
          (App (Rec None (Some "args") frame_body)
            (Struct [] [Var "p"; Var "q"]))))).

(** * Libraries *)

Definition p_list :=
  Prog [node_c] []
    [Fn "nil" None None list.nil_body [] "Node";
     Fn "cons" None (Some "a") list.cons_body [t_int; "Node"] "Node";
     Fn "head" None (Some "n") list.head_body ["Node"] t_int;
     Fn "tail" None (Some "n") list.tail_body ["Node"] "Node";
     Fn "empty" None (Some "n") list.empty_body ["Node"] "Bool"]
    (Let (Some "e") (App (Rec None None list.nil_body) unit_e)
      (Let (Some "l") (App (Rec None (Some "a") list.cons_body) (Struct [] [int 1; Var "e"]))
        (Let (Some "h") (App (Rec None (Some "n") list.head_body) (Var "l"))
          (Let (Some "t") (App (Rec None (Some "n") list.tail_body) (Var "l"))
            (App (Rec None (Some "n") list.empty_body) (Var "t")))))).

(** Standalone reversal library, sharing the list representation and constructors. *)
Definition p_list_rev :=
  Prog [node_c] []
    [Fn "nil" None None list.nil_body [] "Node";
     Fn "cons" None (Some "a") list.cons_body [t_int; "Node"] "Node";
     Fn "head" None (Some "n") list.head_body ["Node"] t_int;
     Fn "tail" None (Some "n") list.tail_body ["Node"] "Node";
     Fn "empty" None (Some "n") list.empty_body ["Node"] "Bool";
     Fn "reverse" None (Some "n") list_rev.rev_body ["Node"] "Node"]
    (Let (Some "e") (App (Rec None None list.nil_body) unit_e)
      (Let (Some "l")
        (App (Rec None (Some "a") list.cons_body) (Struct [] [int 1; Var "e"]))
        (App (Rec None (Some "n") list_rev.rev_body) (Var "l")))).

Definition p_array :=
  Prog [array_c] []
    [Fn "make" None (Some "n") array.make_body [t_int] "Array";
     Fn "length" None (Some "a") array.length_body ["Array"] t_int;
     Fn "get" None (Some "args") array.get_body ["Array"; t_int] t_int;
     Fn "set" None (Some "args") array.set_body ["Array"; t_int; t_int] "Unit"]
    (Let (Some "a") (App (Rec None (Some "n") array.make_body) (int 4))
      (Let None
        (App (Rec None (Some "args") array.set_body) (Struct [] [Var "a"; int 0; int 7]))
        (Let (Some "x") (App (Rec None (Some "args") array.get_body) (Struct [] [Var "a"; int 0]))
          (App (Rec None (Some "a") array.length_body) (Var "a"))))).

Definition al := Some "ArrayList".
Definition hm := Some "HashMap".

Definition p_hash_map :=
  Prog [array_c; hash_map_c] [int64_opt_c; probe_result_s]
    [Fn "make" None (Some "n") array.make_body [t_int] "Array";
     Fn "length" None (Some "a") array.length_body ["Array"] t_int;
     Fn "arrayGet" None (Some "args") array.get_body ["Array"; t_int] t_int;
     Fn "arraySet" None (Some "args") array.set_body ["Array"; t_int; t_int] "Unit";
     Fn "residue" None (Some "args") hash_map.residue_body [t_int; t_int] t_int;
     Fn "scan" None (Some "args") hash_map.scan_body
       [t_int; t_int; t_int; t_int; "Array"; "Array"; "Array"; t_int; t_int] "ProbeResult";
     Fn "bufferProbe" None (Some "args") hash_map.buffer_probe_body
       ["Array"; "Array"; "Array"; t_int; t_int] "ProbeResult";
     Fn "put" None (Some "args") hash_map.put_body
       ["Array"; "Array"; "Array"; t_int; t_int; t_int] "Unit";
     Fn "rehash" None (Some "args") hash_map.rehash_body
       [t_int; t_int; "Array"; "Array"; "Array"; t_int; "Array"; "Array"; "Array"] "Unit";
     Fn "probe" hm (Some "args") hash_map.probe_for_body [t_int] "ProbeResult";
     Fn "addRoom" hm (Some "args") hash_map.add_room_body [t_int; t_int; "Bool"] "Unit";
     Fn "initHashMap" None None hash_map.init_body [] "HashMap";
     Fn "size" hm (Some "m") hash_map.size_body [] t_int;
     Fn "capacity" hm (Some "m") hash_map.capacity_body [] t_int;
     Fn "isEmpty" hm (Some "m") hash_map.is_empty_body [] "Bool";
     Fn "contains" hm (Some "args") hash_map.contains_body [t_int] "Bool";
     Fn "get" hm (Some "args") hash_map.get_body [t_int] "Int64Option";
     Fn "add" hm (Some "args") hash_map.add_body [t_int; t_int] "Unit";
     Fn "remove" hm (Some "args") hash_map.remove_body [t_int] t_int;
     Fn "grow" hm (Some "args") hash_map.grow_body [t_int] "Unit"]
    (Let (Some "m") (App (Rec None None hash_map.init_body) unit_e)
      (Let None
        (App (Rec None (Some "args") hash_map.add_body) (Struct [] [Var "m"; int 1; int 2]))
        (Let (Some "r")
          (App (Rec None (Some "args") hash_map.get_body) (Struct [] [Var "m"; int 1]))
          (App (Rec None (Some "m") hash_map.size_body) (Var "m"))))).

Definition p_array_list :=
  Prog [array_c; array_list_c] []
    [Fn "initArrayList" None None array_list.init_body [] "ArrayList";
     Fn "size" al (Some "a") array_list.size_body [] t_int;
     Fn "capacity" al (Some "a") array_list.capacity_body [] t_int;
     Fn "version" al (Some "a") array_list.version_body [] t_int;
     Fn "isEmpty" al (Some "a") array_list.is_empty_body [] "Bool";
     Fn "get" al (Some "args") array_list.al_get_body [t_int] t_int;
     Fn "set" al (Some "args") array_list.al_set_body [t_int; t_int] "Unit";
     Fn "grow" al (Some "args") array_list.grow_body [t_int] "Unit";
     Fn "add" al (Some "args") array_list.add_body [t_int] "Unit";
     Fn "remove" al (Some "args") array_list.remove_body [t_int] t_int]
    (Let (Some "a") (App (Rec None None array_list.init_body) unit_e)
      (Let None
        (App (Rec None (Some "args") array_list.add_body) (Struct [] [Var "a"; int 1]))
        (Let None
          (App (Rec None (Some "args") array_list.add_body) (Struct [] [Var "a"; int 2]))
          (Let (Some "r")
            (App (Rec None (Some "args") array_list.remove_body) (Struct [] [Var "a"; int 0]))
            (App (Rec None (Some "a") array_list.size_body) (Var "a")))))).

(** * Quicksort

One algorithm, printed twice. The array file calls the free functions
[length], [get], and [set]. The array-list file calls the methods
[size], [get], and [set]. [add] is included so a program can fill the
list, and [add] calls [grow]. *)

Definition array_swap := qsort.swap_body array.get_body array.set_body.
Definition array_partition :=
  qsort.partition_body array.get_body array.set_body.
Definition array_qsort := qsort.qsort_body array.get_body array.set_body.
Definition array_sort :=
  qsort.sort_body array.length_body array.get_body array.set_body.

Definition p_qsort_array :=
  Prog [array_c] []
    [Fn "make" None (Some "n") array.make_body [t_int] "Array";
     Fn "length" None (Some "a") array.length_body ["Array"] t_int;
     Fn "get" None (Some "args") array.get_body ["Array"; t_int] t_int;
     Fn "set" None (Some "args") array.set_body ["Array"; t_int; t_int] "Unit";
     Fn "swap" None (Some "args") array_swap ["Array"; t_int; t_int] "Unit";
     Fn "partition" None (Some "args") array_partition
       ["Array"; t_int; t_int] t_int;
     Fn "qsort" None (Some "args") array_qsort ["Array"; t_int; t_int] "Unit";
     Fn "sort" None (Some "a") array_sort ["Array"] "Unit"]
    (Let (Some "a") (App (Rec None (Some "n") array.make_body) (int 3))
      (Let None
        (App (Rec None (Some "args") array.set_body)
          (Struct [] [Var "a"; int 0; int 3]))
        (Let None
          (App (Rec None (Some "args") array.set_body)
            (Struct [] [Var "a"; int 1; int 1]))
          (Let None
            (App (Rec None (Some "args") array.set_body)
              (Struct [] [Var "a"; int 2; int 2]))
            (App (Rec None (Some "a") array_sort) (Var "a")))))).

Definition list_swap :=
  qsort.swap_body array_list.al_get_body array_list.al_set_body.
Definition list_partition :=
  qsort.partition_body array_list.al_get_body array_list.al_set_body.
Definition list_qsort :=
  qsort.qsort_body array_list.al_get_body array_list.al_set_body.
Definition list_sort :=
  qsort.sort_body array_list.size_body array_list.al_get_body
    array_list.al_set_body.

Definition p_qsort_array_list :=
  Prog [array_c; array_list_c] []
    [Fn "initArrayList" None None array_list.init_body [] "ArrayList";
     Fn "size" al (Some "a") array_list.size_body [] t_int;
     Fn "capacity" al (Some "a") array_list.capacity_body [] t_int;
     Fn "version" al (Some "a") array_list.version_body [] t_int;
     Fn "get" al (Some "args") array_list.al_get_body [t_int] t_int;
     Fn "set" al (Some "args") array_list.al_set_body [t_int; t_int] "Unit";
     Fn "grow" al (Some "args") array_list.grow_body [t_int] "Unit";
     Fn "add" al (Some "args") array_list.add_body [t_int] "Unit";
     Fn "swap" None (Some "args") list_swap ["ArrayList"; t_int; t_int] "Unit";
     Fn "partition" None (Some "args") list_partition
       ["ArrayList"; t_int; t_int] t_int;
     Fn "qsort" None (Some "args") list_qsort
       ["ArrayList"; t_int; t_int] "Unit";
     Fn "sort" None (Some "a") list_sort ["ArrayList"] "Unit"]
    (Let (Some "a") (App (Rec None None array_list.init_body) unit_e)
      (Let None
        (App (Rec None (Some "args") array_list.add_body)
          (Struct [] [Var "a"; int 3]))
        (Let None
          (App (Rec None (Some "args") array_list.add_body)
            (Struct [] [Var "a"; int 1]))
          (Let None
            (App (Rec None (Some "args") array_list.add_body)
              (Struct [] [Var "a"; int 2]))
            (App (Rec None (Some "a") list_sort) (Var "a")))))).

(** Most-frequent: printed from the parallel-array CJR terms. *)
Definition p_most_frequent :=
  Prog [array_c] [int64_opt_c]
    [Fn "make" None (Some "n") array.make_body [t_int] "Array";
     Fn "length" None (Some "a") array.length_body ["Array"] t_int;
     Fn "get" None (Some "args") array.get_body ["Array"; t_int] t_int;
     Fn "set" None (Some "args") array.set_body ["Array"; t_int; t_int] "Unit";
     Fn "pairSwap" None (Some "args") most_frequent.mf_swap_body
       ["Array"; "Array"; t_int; t_int] "Unit";
     Fn "pairPartition" None (Some "args") most_frequent.mf_partition_body
       ["Array"; "Array"; t_int; t_int] t_int;
     Fn "pairQsort" None (Some "args") most_frequent.mf_qsort_body
       ["Array"; "Array"; t_int; t_int] "Unit";
     Fn "mostFrequent" None (Some "input") most_frequent.mf_body ["Array"] "Int64Option"]
    (Let (Some "input") (App (Rec None (Some "n") array.make_body) (int 1))
      (Let None
        (App (Rec None (Some "args") array.set_body)
          (Struct [] [Var "input"; int 0; int 42]))
        (App (Rec None (Some "input") most_frequent.mf_body) (Var "input")))).

(** * The files, in [_CoqProject] order *)

Definition cj_files : list (string * prog) :=
  [("arith", p_arith);
   ("struct_upd", p_struct_upd);
   ("cell", p_cell);
   ("swap", p_swap);
   ("sum_block", p_sum_block);
   ("class_upd", p_class_upd);
   ("frame_call", p_frame_call);
   ("vtable", p_vtable);
   ("list", p_list);
   ("list_rev", p_list_rev);
   ("array", p_array);
   ("array_list", p_array_list);
   ("hash_map", p_hash_map);
   ("qsort_array", p_qsort_array);
   ("qsort_array_list", p_qsort_array_list);
   ("most_frequent", p_most_frequent)].

(** Every file, each preceded by a line [@@FILE NAME]. *)
Definition cj_bundle : string :=
  cat_all (map (fun '(n, p) => "@@FILE " ++ n ++ nl ++ print_prog p) cj_files).
