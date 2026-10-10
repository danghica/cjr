(** The executable CJR program. Every Cangjie implementation operation is
    printed from these definitions, including subdivision and pruning. *)
From Coq Require Import String List ZArith.
From cjr Require Import lang.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition qi n := Val (LitV (LitInt n)).
Definition qb b := Val (LitV (LitBool b)).
Definition qu := Val (LitV LitUnit).
Definition qeq a b := BinOp EqOp a b.
Definition qle a b := BinOp LeOp a b.
Definition qand a b := BinOp AndOp a b.
(** Strict comparison avoids subtracting one from a possibly minimum Int64. *)
Definition qlt a b := If (qle a b) (If (qeq a b) (qb false) (qb true)) (qb false).
Fixpoint qargs_from (i : nat) (names : list string) (body : expr) : expr :=
  match names with [] => body | n::ns => Let (Some n) (StructLoad (Var "args") i) (qargs_from (S i) ns body) end.
Definition qargs := qargs_from 0.
Definition qinvoke (name : string) (body : expr) (args : list expr) :=
  App (Rec (Some name) (Some "args") body) (Struct [] args).
Definition qrecur (name : string) (args : list expr) := App (Var name) (Struct [] args).
Definition qpoint_eq x y a b := qand (qeq x a) (qeq y b).
Definition qinside x y x0 y0 x1 y1 :=
  qand (qand (qle x0 x) (qlt x x1)) (qand (qle y0 y) (qlt y y1)).
Definition qoverlap x0 y0 x1 y1 a0 b0 a1 b1 :=
  qand (qand (qlt x0 a1) (qlt a0 x1)) (qand (qlt y0 b1) (qlt b0 y1)).
Definition qchoose x y mx my ll lr ul ur :=
  If (qlt x mx) (If (qlt y my) ll ul) (If (qlt y my) lr ur).
Fixpoint qloads (object : string) (fields : list (string * nat)) (body : expr) :=
  match fields with [] => body | (name,index)::rest =>
    Let (Some name) (FieldLoad (Var object) index) (qloads object rest body) end.
Fixpoint qstores (object : string) (fields : list (nat * expr)) (body : expr) :=
  match fields with [] => body | (index,value)::rest =>
    Seq (FieldStore (Var object) index value) (qstores object rest body) end.

Definition qt_power_body := qargs ["d"]
  (If (qle (Var "d") (qi 0)) (qi 1)
    (Let (Some "n") (qrecur "qt_power" [BinOp MinusOp (Var "d") (qi 1)])
      (BinOp PlusOp (Var "n") (Var "n")))).
Definition qt_power e := qinvoke "qt_power" qt_power_body [e].

(** QuadNode fields: tag, px, py, x0, y0, x1, y1, mx, my, ll, lr, ul, ur.
    Unused leaf children carry Unit in CJR and None in the printed constructor.
    They are never read. *)
Definition qt_empty_body := qargs ["x0";"y0";"x1";"y1"]
  (New [] [qi 0;qi 0;qi 0;Var "x0";Var "y0";Var "x1";Var "y1";
           qi 0;qi 0;qu;qu;qu;qu]).
Definition qt_empty a b c d := qinvoke "qt_empty" qt_empty_body [a;b;c;d].
Definition qt_seed_body := qargs ["node";"x";"y"]
  (qstores "node" [(0%nat,qi 1);(1%nat,Var "x");(2%nat,Var "y")] qu).
Definition qt_seed n x y := qinvoke "qt_seed" qt_seed_body [n;x;y].

Definition qt_insert_branch :=
  qloads "node" [("mx",7%nat);("my",8%nat);("ll",9%nat);("lr",10%nat);("ul",11%nat);("ur",12%nat)]
    (Let (Some "child") (qchoose (Var "x") (Var "y") (Var "mx") (Var "my")
                           (Var "ll") (Var "lr") (Var "ul") (Var "ur"))
      (qrecur "qt_insert_node" [Var "child";BinOp MinusOp (Var "d") (qi 1);Var "x";Var "y"])).
Definition qt_split :=
  qloads "node" [("x0",3%nat);("y0",4%nat);("x1",5%nat);("y1",6%nat)]
  (Let (Some "half") (qt_power (BinOp MinusOp (Var "d") (qi 1)))
  (Let (Some "split_mx") (BinOp PlusOp (Var "x0") (Var "half"))
  (Let (Some "split_my") (BinOp PlusOp (Var "y0") (Var "half"))
  (Let (Some "split_ll") (qt_empty (Var "x0") (Var "y0") (Var "split_mx") (Var "split_my"))
  (Let (Some "split_lr") (qt_empty (Var "split_mx") (Var "y0") (Var "x1") (Var "split_my"))
  (Let (Some "split_ul") (qt_empty (Var "x0") (Var "split_my") (Var "split_mx") (Var "y1"))
  (Let (Some "split_ur") (qt_empty (Var "split_mx") (Var "split_my") (Var "x1") (Var "y1"))
  (Let (Some "seed") (qchoose (Var "px") (Var "py") (Var "split_mx") (Var "split_my")
                         (Var "split_ll") (Var "split_lr") (Var "split_ul") (Var "split_ur"))
  (Seq (qt_seed (Var "seed") (Var "px") (Var "py"))
  (qstores "node" [(0%nat,qi 2);(1%nat,qi 0);(2%nat,qi 0);(7%nat,Var "split_mx");(8%nat,Var "split_my");
                   (9%nat,Var "split_ll");(10%nat,Var "split_lr");(11%nat,Var "split_ul");(12%nat,Var "split_ur")]
    qt_insert_branch)))))))))).
Definition qt_insert_node_body := qargs ["node";"d";"x";"y"]
  (Let (Some "tag") (FieldLoad (Var "node") 0)
  (If (qeq (Var "tag") (qi 0))
    (Seq (qt_seed (Var "node") (Var "x") (Var "y")) (qb true))
    (If (qeq (Var "tag") (qi 1))
      (qloads "node" [("px",1%nat);("py",2%nat)]
        (If (qpoint_eq (Var "x") (Var "y") (Var "px") (Var "py")) (qb false) qt_split))
      qt_insert_branch))).
Definition qt_insert_node n d x y := qinvoke "qt_insert_node" qt_insert_node_body [n;d;x;y].

Definition qt_contains_node_body := qargs ["node";"x";"y"]
  (Let (Some "tag") (FieldLoad (Var "node") 0)
  (If (qeq (Var "tag") (qi 0)) (qb false)
    (If (qeq (Var "tag") (qi 1))
      (qloads "node" [("px",1%nat);("py",2%nat)]
        (qpoint_eq (Var "x") (Var "y") (Var "px") (Var "py")))
      (qloads "node" [("mx",7%nat);("my",8%nat);("ll",9%nat);("lr",10%nat);("ul",11%nat);("ur",12%nat)]
        (Let (Some "child") (qchoose (Var "x") (Var "y") (Var "mx") (Var "my")
                              (Var "ll") (Var "lr") (Var "ul") (Var "ur"))
          (qrecur "qt_contains_node" [Var "child";Var "x";Var "y"])))))).
Definition qt_contains_node n x y := qinvoke "qt_contains_node" qt_contains_node_body [n;x;y].

(** PointList fields: nonempty, x, y, next. The empty sentinel's next is unused. *)
Definition qt_nil_body := New [] [qb false;qi 0;qi 0;qu].
Definition qt_nil := App (Rec None None qt_nil_body) qu.
Definition qt_cons_body := qargs ["x";"y";"tail"] (New [] [qb true;Var "x";Var "y";Var "tail"]).
Definition qt_cons x y tail := qinvoke "qt_cons" qt_cons_body [x;y;tail].
Definition qt_range_branch :=
  qloads "node" [("ll",9%nat);("lr",10%nat);("ul",11%nat);("ur",12%nat)]
    (Let (Some "a3") (qrecur "qt_range_node" [Var "ur";Var "a0";Var "b0";Var "a1";Var "b1";Var "acc"])
    (Let (Some "a2") (qrecur "qt_range_node" [Var "ul";Var "a0";Var "b0";Var "a1";Var "b1";Var "a3"])
    (Let (Some "a1out") (qrecur "qt_range_node" [Var "lr";Var "a0";Var "b0";Var "a1";Var "b1";Var "a2"])
      (qrecur "qt_range_node" [Var "ll";Var "a0";Var "b0";Var "a1";Var "b1";Var "a1out"])))).
Definition qt_range_node_body := qargs ["node";"a0";"b0";"a1";"b1";"acc"]
  (Let (Some "tag") (FieldLoad (Var "node") 0)
  (If (qeq (Var "tag") (qi 0)) (Var "acc")
    (qloads "node" [("x0",3%nat);("y0",4%nat);("x1",5%nat);("y1",6%nat)]
    (If (qoverlap (Var "x0") (Var "y0") (Var "x1") (Var "y1")
                 (Var "a0") (Var "b0") (Var "a1") (Var "b1"))
      (If (qeq (Var "tag") (qi 1))
        (qloads "node" [("px",1%nat);("py",2%nat)]
          (If (qinside (Var "px") (Var "py") (Var "a0") (Var "b0") (Var "a1") (Var "b1"))
            (qt_cons (Var "px") (Var "py") (Var "acc")) (Var "acc")))
        qt_range_branch)
      (Var "acc"))))).
Definition qt_range_node n a b c d acc := qinvoke "qt_range_node" qt_range_node_body [n;a;b;c;d;acc].

(** QuadTree fields: depth, side, root. *)
Definition qt_make_body := qargs ["depth"]
  (Let (Some "side") (qt_power (Var "depth"))
  (Let (Some "root") (qt_empty (qi 0) (qi 0) (Var "side") (Var "side"))
    (New [] [Var "depth";Var "side";Var "root"]))).
Definition qt_make d := qinvoke "qt_make" qt_make_body [d].
Definition qt_insert_body := qargs ["tree";"x";"y"]
  (qloads "tree" [("side",1%nat)]
  (If (qinside (Var "x") (Var "y") (qi 0) (qi 0) (Var "side") (Var "side"))
    (qloads "tree" [("depth",0%nat);("root",2%nat)]
      (qt_insert_node (Var "root") (Var "depth") (Var "x") (Var "y"))) (qb false))).
Definition qt_insert t x y := qinvoke "qt_insert" qt_insert_body [t;x;y].
Definition qt_contains_body := qargs ["tree";"x";"y"]
  (qloads "tree" [("side",1%nat)]
  (If (qinside (Var "x") (Var "y") (qi 0) (qi 0) (Var "side") (Var "side"))
    (qloads "tree" [("root",2%nat)]
      (qt_contains_node (Var "root") (Var "x") (Var "y"))) (qb false))).
Definition qt_contains t x y := qinvoke "qt_contains" qt_contains_body [t;x;y].
Definition qt_range_body := qargs ["tree";"a0";"b0";"a1";"b1"]
  (qloads "tree" [("root",2%nat)]
  (Let (Some "acc") qt_nil
    (qt_range_node (Var "root") (Var "a0") (Var "b0") (Var "a1") (Var "b1") (Var "acc")))).
Definition qt_range t a b c d := qinvoke "qt_range" qt_range_body [t;a;b;c;d].
