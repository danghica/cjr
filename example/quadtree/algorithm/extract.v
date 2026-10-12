(** The shared syntax-directed printer consumes precisely the implementation AST. *)
From Coq Require Import String List.
From cjr.examples Require Import cj_print.
From cjr.quadtree.algorithm Require Import program.
Import ListNotations.
Local Open Scope string_scope.
Definition node_class := Decl "QuadNode"
  [("tag","Int64");("px","Int64");("py","Int64");("x0","Int64");("y0","Int64");
   ("x1","Int64");("y1","Int64");("mx","Int64");("my","Int64");
   ("ll","QuadNode");("lr","QuadNode");("ul","QuadNode");("ur","QuadNode")].
Definition list_class := Decl "PointList"
  [("nonempty","Bool");("x","Int64");("y","Int64");("next","PointList")].
Definition tree_class := Decl "QuadTree" [("depth","Int64");("side","Int64");("root","QuadNode")].
Definition quadtree_program := Prog [node_class;list_class;tree_class] []
  [Fn "qt_power" None (Some "args") qt_power_body ["Int64"] "Int64";
   Fn "qt_empty" None (Some "args") qt_empty_body ["Int64";"Int64";"Int64";"Int64"] "QuadNode";
   Fn "qt_seed" None (Some "args") qt_seed_body ["QuadNode";"Int64";"Int64"] "Unit";
   Fn "qt_insert_node" None (Some "args") qt_insert_node_body ["QuadNode";"Int64";"Int64";"Int64"] "Bool";
   Fn "qt_contains_node" None (Some "args") qt_contains_node_body ["QuadNode";"Int64";"Int64"] "Bool";
   Fn "qt_nil" None None qt_nil_body [] "PointList";
   Fn "qt_cons" None (Some "args") qt_cons_body ["Int64";"Int64";"PointList"] "PointList";
   Fn "qt_range_node" None (Some "args") qt_range_node_body ["QuadNode";"Int64";"Int64";"Int64";"Int64";"PointList"] "PointList";
   Fn "make" None (Some "args") qt_make_body ["Int64"] "QuadTree";
   Fn "insert" None (Some "args") qt_insert_body ["QuadTree";"Int64";"Int64"] "Bool";
   Fn "contains" None (Some "args") qt_contains_body ["QuadTree";"Int64";"Int64"] "Bool";
   Fn "range" None (Some "args") qt_range_body ["QuadTree";"Int64";"Int64";"Int64";"Int64"] "PointList"] qu.
