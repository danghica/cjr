(** Print a CJR [expr] as the Cangjie surface of the tutorial's correspondence
table. Class and struct layouts, and the signatures of the functions an
example defines, are passed in with each example. *)

From Coq Require Import String Ascii ZArith List Bool.
From cjr Require Import lang.
Import ListNotations.

Local Open Scope string_scope.

Local Set Warnings "-inconsistent-scopes".

Local Infix "+++" := String.append (right associativity, at level 60).

Definition nl : string := String (ascii_of_nat 10) EmptyString.

Fixpoint nat_digits (fuel n : nat) : string :=
  match fuel with
  | O => ""
  | S fuel =>
      let d :=
        match Nat.modulo n 10 with
        | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
        | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
        end in
      if Nat.eqb n 0 then "" else nat_digits fuel (Nat.div n 10) +++ d
  end.

Definition nat_string (n : nat) : string :=
  if Nat.eqb n 0 then "0" else nat_digits (S n) n.

Definition z_string (z : Z) : string :=
  if Z.ltb z 0 then "-" +++ nat_string (Z.to_nat (Z.opp z))
  else nat_string (Z.to_nat z).

Fixpoint cat_all (xs : list string) : string :=
  match xs with
  | [] => ""
  | x :: xs => x +++ cat_all xs
  end.

Fixpoint comma (xs : list string) : string :=
  match xs with
  | [] => ""
  | [x] => x
  | x :: xs => x +++ ", " +++ comma xs
  end.

(** * Syntactic equality, used to recognise known function bodies *)

Definition binder_beq (a b : binder) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => String.eqb x y
  | _, _ => false
  end.

Definition binop_beq (a b : bin_op) : bool :=
  match a, b with
  | PlusOp, PlusOp | MinusOp, MinusOp | LeOp, LeOp
  | EqOp, EqOp | AndOp, AndOp => true
  | _, _ => false
  end.

Definition lit_beq (a b : base_lit) : bool :=
  match a, b with
  | LitInt x, LitInt y => Z.eqb x y
  | LitFloat x, LitFloat y => Z.eqb x y
  | LitBool x, LitBool y => Bool.eqb x y
  | LitUnit, LitUnit => true
  | LitPtr x, LitPtr y => Z.eqb x y
  | LitNull, LitNull => true
  | LitObj x, LitObj y => Z.eqb x y
  | LitStack x, LitStack y => Z.eqb x y
  | _, _ => false
  end.

Fixpoint expr_beq (a b : expr) {struct a} : bool :=
  match a, b with
  | Val v, Val w => val_beq v w
  | Var x, Var y => String.eqb x y
  | Rec f x e, Rec g y e' => binder_beq f g && binder_beq x y && expr_beq e e'
  | App e1 e2, App e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | Let x e1 e2, Let y e1' e2' =>
      binder_beq x y && expr_beq e1 e1' && expr_beq e2 e2'
  | VarBind x e1 e2, VarBind y e1' e2' =>
      String.eqb x y && expr_beq e1 e1' && expr_beq e2 e2'
  | Assign x e, Assign y e' => String.eqb x y && expr_beq e e'
  | Pop (StackId z) e, Pop (StackId z') e' => Z.eqb z z' && expr_beq e e'
  | StackLoad e, StackLoad e' => expr_beq e e'
  | StackAssign e1 e2, StackAssign e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | StackFieldStore e1 i e2, StackFieldStore e1' j e2' =>
      expr_beq e1 e1' && Nat.eqb i j && expr_beq e2 e2'
  | If e0 e1 e2, If e0' e1' e2' =>
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
  | While e1 e2, While e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | Seq e1 e2, Seq e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
  | BinOp op e1 e2, BinOp op' e1' e2' =>
      binop_beq op op' && expr_beq e1 e1' && expr_beq e2 e2'
  | Alloc e, Alloc e' | Free e, Free e' | Load e, Load e' => expr_beq e e'
  | Store e1 e2, Store e1' e2' | Offset e1 e2, Offset e1' e2' =>
      expr_beq e1 e1' && expr_beq e2 e2'
  | Struct vs es, Struct vs' es' | New vs es, New vs' es' =>
      (fix go (xs ys : list val) : bool :=
         match xs, ys with
         | [], [] => true
         | x :: xs, y :: ys => val_beq x y && go xs ys
         | _, _ => false
         end) vs vs' &&
      (fix go (xs ys : list expr) : bool :=
         match xs, ys with
         | [], [] => true
         | x :: xs, y :: ys => expr_beq x y && go xs ys
         | _, _ => false
         end) es es'
  | StructLoad e i, StructLoad e' j | FieldLoad e i, FieldLoad e' j =>
      expr_beq e e' && Nat.eqb i j
  | StructStore x i e, StructStore y j e' =>
      String.eqb x y && Nat.eqb i j && expr_beq e e'
  | FieldStore e1 i e2, FieldStore e1' j e2' =>
      expr_beq e1 e1' && Nat.eqb i j && expr_beq e2 e2'
  | _, _ => false
  end
with val_beq (a b : val) {struct a} : bool :=
  match a, b with
  | LitV l, LitV l' => lit_beq l l'
  | RecV f x e, RecV g y e' => binder_beq f g && binder_beq x y && expr_beq e e'
  | StructV vs, StructV vs' =>
      (fix go (xs ys : list val) : bool :=
         match xs, ys with
         | [], [] => true
         | x :: xs, y :: ys => val_beq x y && go xs ys
         | _, _ => false
         end) vs vs'
  | _, _ => false
  end.

(** * Renaming a placeholder pointer back to a parameter *)

Fixpoint rename_ptr (l : Z) (x : string) (e : expr) : expr :=
  match e with
  | Val (LitV (LitPtr l')) => if Z.eqb l l' then Var x else e
  | Val _ | Var _ => e
  | Rec f y e1 => Rec f y (rename_ptr l x e1)
  | App e1 e2 => App (rename_ptr l x e1) (rename_ptr l x e2)
  | Let b e1 e2 => Let b (rename_ptr l x e1) (rename_ptr l x e2)
  | VarBind y e1 e2 => VarBind y (rename_ptr l x e1) (rename_ptr l x e2)
  | Assign y e1 => Assign y (rename_ptr l x e1)
  | Pop s e1 => Pop s (rename_ptr l x e1)
  | StackLoad e1 => StackLoad (rename_ptr l x e1)
  | StackAssign e1 e2 => StackAssign (rename_ptr l x e1) (rename_ptr l x e2)
  | StackFieldStore e1 i e2 =>
      StackFieldStore (rename_ptr l x e1) i (rename_ptr l x e2)
  | If e0 e1 e2 => If (rename_ptr l x e0) (rename_ptr l x e1) (rename_ptr l x e2)
  | While e1 e2 => While (rename_ptr l x e1) (rename_ptr l x e2)
  | Seq e1 e2 => Seq (rename_ptr l x e1) (rename_ptr l x e2)
  | BinOp op e1 e2 => BinOp op (rename_ptr l x e1) (rename_ptr l x e2)
  | Alloc e1 => Alloc (rename_ptr l x e1)
  | Free e1 => Free (rename_ptr l x e1)
  | Load e1 => Load (rename_ptr l x e1)
  | Store e1 e2 => Store (rename_ptr l x e1) (rename_ptr l x e2)
  | Offset e1 e2 => Offset (rename_ptr l x e1) (rename_ptr l x e2)
  | Struct vs es => Struct vs (map (rename_ptr l x) es)
  | StructLoad e1 i => StructLoad (rename_ptr l x e1) i
  | StructStore y i e1 => StructStore y i (rename_ptr l x e1)
  | New vs es => New vs (map (rename_ptr l x) es)
  | FieldLoad e1 i => FieldLoad (rename_ptr l x e1) i
  | FieldStore e1 i e2 => FieldStore (rename_ptr l x e1) i (rename_ptr l x e2)
  end.

(** * Layouts, signatures, and the printing environment *)

(** A class or struct: its name and its fields, each a name and a type. *)
Record decl := Decl { d_name : string; d_fields : list (string * string) }.

(** A function an example defines. [fn_owner] is the class of a method.
A method's receiver is the first component of its argument struct, or the
argument itself; it is not a parameter. [fn_tys] are the parameter types. *)
Record fn := Fn {
  fn_name : string;
  fn_owner : option string;
  fn_arg : binder;
  fn_body : expr;
  fn_tys : list string;
  fn_ret : string
}.

(** One generated file: layouts, functions, and the body of [main]. *)
Record prog := Prog {
  p_classes : list decl;
  p_structs : list decl;
  p_fns : list fn;
  p_main : expr
}.

Record penv := Env {
  e_cls : list decl;
  e_sty : list decl;
  e_fns : list fn;
  e_this : option string;
  e_ty : list (string * string);
  e_pack : list (string * list string);
  e_alias : list (string * string)
}.

Fixpoint assoc {A} (k : string) (xs : list (string * A)) : option A :=
  match xs with
  | [] => None
  | (y, a) :: xs => if String.eqb k y then Some a else assoc k xs
  end.

Fixpoint decl_by_name (ds : list decl) (n : string) : option decl :=
  match ds with
  | [] => None
  | d :: ds => if String.eqb (d_name d) n then Some d else decl_by_name ds n
  end.

Fixpoint decl_by_arity (ds : list decl) (n : nat) : option decl :=
  match ds with
  | [] => None
  | d :: ds =>
      if Nat.eqb (List.length (d_fields d)) n then Some d else decl_by_arity ds n
  end.

Definition all_decls (env : penv) : list decl := app (e_cls env) (e_sty env).

Definition find_body (env : penv) (b : expr) : option fn :=
  find (fun k => expr_beq (fn_body k) b) (e_fns env).

Definition find_name (env : penv) (n : string) : option fn :=
  find (fun k => String.eqb (fn_name k) n) (e_fns env).

(** A closed function (no argument) whose body is literally [e]. *)
Definition find_closed (env : penv) (e : expr) : option fn :=
  find (fun k => match fn_arg k with
                 | None => expr_beq (fn_body k) e
                 | Some _ => false
                 end) (e_fns env).

Definition with_ty (env : penv) (x t : string) : penv :=
  Env (e_cls env) (e_sty env) (e_fns env) (e_this env)
      ((x, t) :: e_ty env) (e_pack env) (e_alias env).

Definition with_ty_opt (env : penv) (x : string) (t : option string) : penv :=
  with_ty env x (match t with Some t => t | None => "" end).

Definition with_pack (env : penv) (x : string) (ss : list string) : penv :=
  Env (e_cls env) (e_sty env) (e_fns env) (e_this env)
      (e_ty env) ((x, ss) :: e_pack env) (e_alias env).

Definition with_alias (env : penv) (x n : string) : penv :=
  Env (e_cls env) (e_sty env) (e_fns env) (e_this env)
      (e_ty env) (e_pack env) ((x, n) :: e_alias env).

Definition with_this (env : penv) (r : option string) (owner : option string) : penv :=
  let tys := match r, owner with
             | Some r, Some c => (r, c) :: e_ty env
             | _, _ => e_ty env
             end in
  Env (e_cls env) (e_sty env) (e_fns env) r tys (e_pack env) (e_alias env).

Definition without (env : penv) (n : string) : penv :=
  Env (e_cls env) (e_sty env)
      (filter (fun k => negb (String.eqb (fn_name k) n)) (e_fns env))
      (e_this env) (e_ty env) (e_pack env) (e_alias env).

Definition keywords : list string :=
  ["this"; "super"; "init"; "main"; "func"; "let"; "var"; "type"; "in"; "is";
   "as"; "where"; "match"; "case"; "class"; "struct"; "spawn"; "true"; "false";
   "if"; "else"; "while"; "for"; "do"; "return"; "break"; "continue"].

(** [this] is a parameter name in the core; it is a keyword in Cangjie. *)
Definition sanitize (x : string) : string :=
  if String.eqb x "this" then "self"
  else if existsb (String.eqb x) keywords then x +++ "_" else x.

Definition binder_name (b : binder) : string :=
  match b with Some x => sanitize x | None => "_" end.

Definition var_name (env : penv) (x : string) : string :=
  match e_this env with
  | Some r => if String.eqb x r then "this" else
      match assoc x (e_alias env) with Some n => n | None => sanitize x end
  | None => match assoc x (e_alias env) with Some n => n | None => sanitize x end
  end.

Definition field_of (env : penv) (c : option string) (i : nat) : string :=
  match c with
  | Some c =>
      match decl_by_name (all_decls env) c with
      | Some d =>
          match nth_error (d_fields d) i with
          | Some (f, _) => f
          | None => "f" +++ nat_string i
          end
      | None => "f" +++ nat_string i
      end
  | None => "f" +++ nat_string i
  end.

Definition field_ty (env : penv) (c : option string) (i : nat) : option string :=
  match c with
  | Some c =>
      match decl_by_name (all_decls env) c with
      | Some d =>
          match nth_error (d_fields d) i with
          | Some (_, t) =>
              match decl_by_name (all_decls env) t with
              | Some _ => Some t
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition var_class (env : penv) (x : string) : option string :=
  match assoc x (e_ty env) with
  | Some t => match decl_by_name (all_decls env) t with
              | Some _ => Some t
              | None => None
              end
  | None => None
  end.

(** The class or struct of an expression, where the layouts determine it. *)
Definition class_of (env : penv) (e : expr) : option string :=
  match e with
  | Var x => var_class env x
  | New vs es =>
      option_map d_name (decl_by_arity (e_cls env) (List.length vs + List.length es))
  | Struct vs es =>
      option_map d_name (decl_by_arity (e_sty env) (List.length vs + List.length es))
  | Val (StructV vs) => option_map d_name (decl_by_arity (e_sty env) (List.length vs))
  | FieldLoad (Var y) i | StructLoad (Var y) i => field_ty env (var_class env y) i
  | App (Rec _ _ b) _ =>
      match find_body env b with
      | Some k => match decl_by_name (all_decls env) (fn_ret k) with
                  | Some _ => Some (fn_ret k)
                  | None => None
                  end
      | None => None
      end
  | _ => None
  end.

Definition is_stmt (e : expr) : bool :=
  match e with
  | Let _ _ _ | VarBind _ _ _ | Seq _ _ | While _ _ => true
  | _ => false
  end.

Definition is_binop (e : expr) : bool :=
  match e with BinOp _ _ _ => true | _ => false end.

Definition is_unit (e : expr) : bool :=
  match e with Val (LitV LitUnit) => true | _ => false end.

Definition leaf (e : expr) : bool :=
  match e with
  | Val (LitV _) | Var _ | FieldLoad (Var _) _ | StructLoad (Var _) _ => true
  | _ => false
  end.

Definition simple (e : expr) : bool :=
  match e with
  | BinOp _ a b => leaf a && leaf b
  | _ => leaf e
  end.

(** Peel [let x = args.i] bindings off the front of a function body. *)
Fixpoint peel (b : string) (e : expr) : list string * expr :=
  match e with
  | Let (Some x) (StructLoad (Var y) _) e2 =>
      if String.eqb y b then
        let '(xs, r) := peel b e2 in (x :: xs, r)
      else ([], e)
  | _ => ([], e)
  end.

Definition unsupported (what : string) : string :=
  "/* unsupported: " +++ what +++ " */".

Definition oob_text : string := "unsafe { CPointer<Int64>().read() }".

Definition sym (op : bin_op) : string :=
  match op with
  | PlusOp => " + "
  | MinusOp => " - "
  | LeOp => " <= "
  | EqOp => " == "
  | AndOp => " && "
  end.

Definition lit (l : base_lit) : string :=
  match l with
  | LitInt n => z_string n
  | LitFloat n => z_string n +++ ".0"
  | LitBool true => "true"
  | LitBool false => "false"
  | LitUnit => "()"
  | LitNull => "CPointer<Int64>()"
  | LitPtr _ => unsupported "raw address literal"
  | LitObj _ => unsupported "object reference literal"
  | LitStack _ => unsupported "stack slot"
  end.

Definition lam (ind body : string) : string :=
  "{ =>" +++ nl +++ ind +++ "    " +++ body +++ nl +++ ind +++ "}()".

Definition paren (s : string) : string := "(" +++ s +++ ")".

(** A subexpression in operand position. A block-shaped term is wrapped in a
lambda that is applied at once. *)
Local Notation arg f ind s :=
  (if is_stmt s then lam ind (f (String.append ind "    "%string) s) else f ind s)
  (only parsing).

Local Notation opnd f ind s :=
  (if is_binop s then paren (f ind s) else arg f ind s) (only parsing).

(** * The printer

[ex env ind e] prints [e] starting at the current column. Further lines of a
block are indented by [ind]. *)
Fixpoint ex (env : penv) (ind : string) (e : expr) {struct e} : string :=
  let ind2 := ind +++ "    " in
  match find_closed env e with
  | Some k => fn_name k +++ "()"
  | None =>
  match e with
  | Val v => exv env ind v
  | Var x => var_name env x
  | Rec None x body =>
      match find_body env body with
      | Some k => fn_name k
      | None => "{ " +++ binder_name x +++ " => " +++ ex env ind body +++ " }"
      end
  | Rec (Some _) _ _ => unsupported "recursive closure"
  | App f a =>
      let k := match f with
               | Rec _ _ body => find_body env body
               | Val (RecV _ _ body) => find_body env body
               | Var x => match assoc x (e_alias env) with
                          | Some n => find_name env n
                          | None => None
                          end
               | _ => None
               end in
      let args :=
        match a with
        | Struct vs es =>
            app (map (exv env ind) vs) (map (fun s => arg (ex env) ind s) es)
        | Val (StructV vs) => map (exv env ind) vs
        | Val (LitV LitUnit) => []
        | Var x =>
            match assoc x (e_pack env) with
            | Some ss => ss
            | None => [var_name env x]
            end
        | _ => [arg (ex env) ind a]
        end in
      match k with
      | Some k =>
          match fn_owner k, args with
          | Some _, o :: rest => o +++ "." +++ fn_name k +++ "(" +++ comma rest +++ ")"
          | _, _ => fn_name k +++ "(" +++ comma args +++ ")"
          end
      | None =>
          let callee := match f with
                        | Var _ | StructLoad (Var _) _ | FieldLoad (Var _) _ => ex env ind f
                        | _ => "(" +++ ex env ind f +++ ")"
                        end in
          callee +++ "(" +++ comma args +++ ")"
      end
  | Let (Some x) e1 e2 =>
      match e1 with
      | Rec None _ body =>
          match find_body env body with
          | Some k => ex (with_alias env x (fn_name k)) ind e2
          | None =>
              "let " +++ sanitize x +++ " = " +++ ex env ind e1 +++ nl +++ ind
              +++ ex (with_ty env x "") ind e2
          end
      | Struct vs es =>
          match decl_by_arity (e_sty env) (List.length vs + List.length es) with
          | Some d =>
              "let " +++ sanitize x +++ " = " +++ ex env ind e1 +++ nl +++ ind
              +++ ex (with_ty env x (d_name d)) ind e2
          | None =>
              ex (with_pack env x
                    (app (map (exv env ind) vs) (map (fun s => arg (ex env) ind s) es)))
                 ind e2
          end
      | _ =>
          "let " +++ sanitize x +++ " = " +++ arg (ex env) ind e1 +++ nl +++ ind
          +++ ex (with_ty_opt env x (class_of env e1)) ind e2
      end
  | Let None e1 e2 | Seq e1 e2 =>
      ex env ind e1 +++ nl +++ ind +++ ex env ind e2
  | VarBind x e1 e2 =>
      "var " +++ sanitize x +++ " = " +++ arg (ex env) ind e1 +++ nl +++ ind
      +++ ex (with_ty_opt env x (class_of env e1)) ind e2
  | Assign x a => var_name env x +++ " = " +++ arg (ex env) ind a
  | If c e1 e2 =>
      if simple e1 && simple e2 then
        "if (" +++ ex env ind c +++ ") { " +++ ex env ind e1 +++ " } else { "
        +++ ex env ind e2 +++ " }"
      else if is_unit e2 then
        "if (" +++ ex env ind c +++ ") {" +++ nl +++ ind2 +++ ex env ind2 e1
        +++ nl +++ ind +++ "}"
      else
        "if (" +++ ex env ind c +++ ") {" +++ nl +++ ind2 +++ ex env ind2 e1
        +++ nl +++ ind +++ "} else {" +++ nl +++ ind2 +++ ex env ind2 e2
        +++ nl +++ ind +++ "}"
  | While c b =>
      "while (" +++ ex env ind c +++ ") {" +++ nl +++ ind2 +++ ex env ind2 b
      +++ nl +++ ind +++ "}"
  | BinOp op a b => opnd (ex env) ind a +++ sym op +++ opnd (ex env) ind b
  | Alloc n =>
      "unsafe { CPointer<Int64>(malloc(UIntNative(8 * " +++ opnd (ex env) ind n
      +++ "))) }"
  | Free p => "unsafe { free(CPointer<Unit>(" +++ ex env ind p +++ ")) }"
  | Load (Val (LitV LitUnit)) => oob_text
  | Load (Offset b i) =>
      "unsafe { (" +++ ex env ind b +++ " + " +++ opnd (ex env) ind i +++ ").read() }"
  | Load (Var x) => "unsafe { " +++ var_name env x +++ ".read() }"
  | Load p => "unsafe { (" +++ ex env ind p +++ ").read() }"
  | Store (Offset b i) v =>
      "unsafe { (" +++ ex env ind b +++ " + " +++ opnd (ex env) ind i +++ ").write("
      +++ arg (ex env) ind v +++ ") }"
  | Store (Var x) v =>
      "unsafe { " +++ var_name env x +++ ".write(" +++ arg (ex env) ind v +++ ") }"
  | Store p v =>
      "unsafe { (" +++ ex env ind p +++ ").write(" +++ arg (ex env) ind v +++ ") }"
  | Offset b i => "unsafe { " +++ ex env ind b +++ " + " +++ opnd (ex env) ind i +++ " }"
  | Struct vs es =>
      let args := app (map (exv env ind) vs) (map (fun s => arg (ex env) ind s) es) in
      match decl_by_arity (e_sty env) (List.length args) with
      | Some d => d_name d +++ "(" +++ comma args +++ ")"
      | None => "(" +++ comma args +++ ")"
      end
  | StructLoad (Var x) i =>
      match var_class env x with
      | Some c => var_name env x +++ "." +++ field_of env (Some c) i
      | None => var_name env x +++ "[" +++ nat_string i +++ "]"
      end
  | StructLoad s i => "(" +++ ex env ind s +++ ")[" +++ nat_string i +++ "]"
  | StructStore x i a =>
      var_name env x +++ "." +++ field_of env (var_class env x) i +++ " = "
      +++ arg (ex env) ind a
  | New vs es =>
      let args := app (map (exv env ind) vs) (map (fun s => arg (ex env) ind s) es) in
      match decl_by_arity (e_cls env) (List.length args) with
      | Some d => d_name d +++ "(" +++ comma args +++ ")"
      | None => unsupported "object of unknown layout"
      end
  | FieldLoad (Var x) i => var_name env x +++ "." +++ field_of env (var_class env x) i
  | FieldLoad s i => "(" +++ ex env ind s +++ ")." +++ field_of env (class_of env s) i
  | FieldStore (Var x) i a =>
      var_name env x +++ "." +++ field_of env (var_class env x) i +++ " = "
      +++ arg (ex env) ind a
  | FieldStore s i a =>
      "(" +++ ex env ind s +++ ")." +++ field_of env (class_of env s) i +++ " = "
      +++ arg (ex env) ind a
  | Pop _ _ | StackLoad _ | StackAssign _ _ | StackFieldStore _ _ _ =>
      unsupported "stack form"
  end
  end
with exv (env : penv) (ind : string) (v : val) {struct v} : string :=
  match v with
  | LitV l => lit l
  | RecV None x body =>
      match find_body env body with
      | Some k => fn_name k
      | None => "{ " +++ binder_name x +++ " => " +++ ex env ind body +++ " }"
      end
  | RecV (Some _) _ _ => unsupported "recursive closure"
  | StructV vs =>
      let args := map (exv env ind) vs in
      match decl_by_arity (e_sty env) (List.length args) with
      | Some d => d_name d +++ "(" +++ comma args +++ ")"
      | None => "(" +++ comma args +++ ")"
      end
  end.

(** * Functions, declarations, files *)

Definition fn_parts (k : fn) : option string * list string * expr :=
  match fn_arg k with
  | None => (None, [], fn_body k)
  | Some b =>
      match peel b (fn_body k), fn_owner k with
      | ([], _), Some _ => (Some b, [], fn_body k)
      | ([], _), None => (None, [b], fn_body k)
      | (x :: xs, r), Some _ => (Some x, xs, r)
      | (xs, r), None => (None, xs, r)
      end
  end.

Definition print_fn (env : penv) (ind : string) (k : fn) : string :=
  let '(recv, ps, body) := fn_parts k in
  let typed := combine ps (fn_tys k) in
  let env1 :=
    fold_left (fun env '(x, t) => with_ty env x t) typed
      (with_this (without env (fn_name k)) recv (fn_owner k)) in
  let ind2 := ind +++ "    " in
  let kw := match fn_owner k with Some _ => "public func " | None => "func " end in
  ind +++ kw +++ fn_name k +++ "("
  +++ comma (map (fun '(x, t) => sanitize x +++ ": " +++ t) typed)
  +++ "): " +++ fn_ret k +++ " {" +++ nl
  +++ ind2 +++ ex env1 ind2 body +++ nl
  +++ ind +++ "}" +++ nl.

Definition owned_by (c : string) (k : fn) : bool :=
  match fn_owner k with Some c' => String.eqb c c' | None => false end.

Definition is_free (k : fn) : bool :=
  match fn_owner k with Some _ => false | None => true end.

Definition print_decl (env : penv) (kw : string) (d : decl) : string :=
  let fs := d_fields d in
  kw +++ " " +++ d_name d +++ " {" +++ nl
  +++ cat_all (map (fun '(f, t) => "    public var " +++ f +++ ": " +++ t +++ nl) fs)
  +++ "    public init(" +++ comma (map (fun '(f, t) => f +++ ": " +++ t) fs)
  +++ ") {" +++ nl
  +++ cat_all (map (fun '(f, _) => "        this." +++ f +++ " = " +++ f +++ nl) fs)
  +++ "    }" +++ nl
  +++ cat_all (map (fun k => nl +++ print_fn env "    " k)
                  (filter (owned_by (d_name d)) (e_fns env)))
  +++ "}" +++ nl.

Definition prelude : string :=
  "// Generated by theories/examples/emit_cj.v from the CJR core terms." +++ nl
  +++ nl
  +++ "foreign func malloc(size: UIntNative): CPointer<Unit>" +++ nl
  +++ "foreign func free(ptr: CPointer<Unit>): Unit" +++ nl.

Definition print_prog (p : prog) : string :=
  let env := Env (p_classes p) (p_structs p) (p_fns p) None [] [] [] in
  prelude
  +++ cat_all (map (fun d => nl +++ print_decl env "struct" d) (p_structs p))
  +++ cat_all (map (fun d => nl +++ print_decl env "class" d) (p_classes p))
  +++ cat_all (map (fun k => nl +++ print_fn env "" k) (filter is_free (p_fns p)))
  +++ nl +++ "main(): Unit {" +++ nl
  +++ "    " +++ ex env "    " (p_main p) +++ nl
  +++ "}" +++ nl.
