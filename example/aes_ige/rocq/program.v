(** Executable CJR terms. Every extracted AES operation is defined here. *)
From Coq Require Import ZArith String List.
From cjr Require Import lang.
From cjr.aes_ige Require Import bytes.
Import ListNotations.
Open Scope string_scope.
Definition int (x : Z) := Val (LitV (LitInt x)).
Definition unit_e := Val (LitV LitUnit).
Definition bool_e (x : bool) := Val (LitV (LitBool x)).
Definition ptr (p : expr) (i : Z) := Offset p (int i).
Definition get (p : expr) (i : Z) := Load (ptr p i).
Definition put (p : expr) (i : Z) (v : expr) := Store (ptr p i) v.
Definition xb (a b : expr) := BinOp BitXorOp a b.
Definition ab (a b : expr) := BinOp BitAndOp a b.
Definition plus (a b : expr) := BinOp PlusOp a b.
Definition eq (a b : expr) := BinOp EqOp a b.
Definition le (a b : expr) := BinOp LeOp a b.
Definition seqs (xs : list expr) (last : expr) := fold_right Seq last xs.
Definition args (names : list string) (body : expr) :=
  fold_right (fun ni e => Let (Some (fst ni)) (StructLoad (Var "args") (snd ni)) e)
    body (combine names (seq 0 (length names))).
Definition invoke body (values : list expr) :=
  App (Rec None (Some "args") body) (Struct [] values).
Definition call1 body x := App (Rec None (Some "x") body) x.
Definition table_leaf (base : nat) (table : list Z) :=
  fold_right (fun ni rest => If (eq (Var "x") (int (Z.of_nat (fst ni))))
    (int (snd ni)) rest) (int 0) (combine (seq base (length table)) table).
Fixpoint table_groups (fuel base : nat) (table : list Z) :=
  match fuel with O => int 0 | S fuel =>
    If (le (Var "x") (int (Z.of_nat (base+15))))
      (table_leaf base (firstn 16 table))
      (table_groups fuel (base+16) (skipn 16 table)) end.
Definition table_body table := table_groups 16 0 table.
Definition sbox_body := table_body sbox_table.
Definition inv_sbox_body := table_body inv_sbox_table.
Definition xtime_body :=
  Let (Some "d") (ab (plus (Var "x") (Var "x")) (int 255))
    (If (eq (ab (Var "x") (int 128)) (int 0))
       (Var "d") (xb (Var "d") (int 27))).
Definition xt x := call1 xtime_body x.
Definition sb x := call1 sbox_body x.
Definition isb x := call1 inv_sbox_body x.
Definition copy_body := args ["src";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (get (Var "src") (Z.of_nat i))) (seq 0 16)) unit_e).
Definition xor_body := args ["src";"key";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (xb (get (Var "src") (Z.of_nat i)) (get (Var "key") (Z.of_nat i)))) (seq 0 16)) unit_e).
Definition sub_body := args ["src";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (sb (get (Var "src") (Z.of_nat i)))) (seq 0 16)) unit_e).
Definition inv_sub_body := args ["src";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (isb (get (Var "src") (Z.of_nat i)))) (seq 0 16)) unit_e).
Definition shift_body := args ["src";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (get (Var "src") (Z.of_nat (4 * (((i / 4) + (i mod 4)) mod 4) + (i mod 4))))) (seq 0 16)) unit_e).
Definition inv_shift_body := args ["src";"dst"]
  (seqs (map (fun i => put (Var "dst") (Z.of_nat i)
    (get (Var "src") (Z.of_nat (4 * (((i / 4) + 4 - (i mod 4)) mod 4) + (i mod 4))))) (seq 0 16)) unit_e).
Definition mix_body := args ["src";"dst"]
  (seqs (map (fun i =>
    let k := (4 * (i/4))%nat in let r := (i mod 4)%nat in
    let x := get (Var "src") (Z.of_nat (k+r)) in
    let y := get (Var "src") (Z.of_nat (k+(r+1) mod 4)) in
    let z := get (Var "src") (Z.of_nat (k+(r+2) mod 4)) in
    let w := get (Var "src") (Z.of_nat (k+(r+3) mod 4)) in
    put (Var "dst") (Z.of_nat i) (xb (xt (xb x y)) (xb y (xb z w)))) (seq 0 16)) unit_e).
Definition cp s d := invoke copy_body [s;d].
Definition xx s k d := invoke xor_body [s;k;d].
Definition sub s d := invoke sub_body [s;d].
Definition isub s d := invoke inv_sub_body [s;d].
Definition shift s d := invoke shift_body [s;d].
Definition ishift s d := invoke inv_shift_body [s;d].
Definition mx s d := invoke mix_body [s;d].
Definition imx s d := seqs [mx s d; mx d s; mx s d] unit_e.
Definition expansion_byte (nk j : nat) :=
  let iw := (j/4)%nat in let row := (j mod 4)%nat in
  let t := if Nat.eqb (iw mod nk) 0 then
    xb (sb (get (Var "schedule") (Z.of_nat (j-row-4+(row+1) mod 4))))
       (int (if Nat.eqb row 0 then nth ((iw/nk)-1) [1;2;4;8;16;32;64;128;27;54] 0 else 0))
    else if (Nat.eqb nk 8 && Nat.eqb (iw mod nk) 4)%bool
    then sb (get (Var "schedule") (Z.of_nat (j-4)))
    else get (Var "schedule") (Z.of_nat (j-4)) in
  put (Var "schedule") (Z.of_nat j)
    (xb (get (Var "schedule") (Z.of_nat (j-4*nk))) t).
Definition expand_branch nk nr := seqs
  (map (fun i => put (Var "schedule") (Z.of_nat i)
    (get (Var "key") (Z.of_nat i))) (seq 0 (4*nk)) ++
   map (expansion_byte nk) (seq (4*nk) (16*(nr+1)-4*nk))) (int (Z.of_nat nr)).
Definition expand_body := args ["key";"keyLen";"schedule"]
  (If (eq (Var "keyLen") (int 16)) (expand_branch 4 10)
    (If (eq (Var "keyLen") (int 24)) (expand_branch 6 12)
      (If (eq (Var "keyLen") (int 32)) (expand_branch 8 14) (int 0)))).
Definition work := Var "work".
Definition tmp := ptr work 16.
Definition rkey r := ptr (Var "schedule") (Z.of_nat (16*r)).
Definition enc_round r := seqs [sub work tmp; shift tmp work; mx work tmp; xx tmp (rkey r) work] unit_e.
Definition dec_round r := seqs [ishift work tmp; isub tmp work; xx work (rkey r) tmp; imx tmp work] unit_e.
Definition encrypt_branch nr := seqs
  ([xx (Var "src") (rkey 0) work] ++
   map enc_round (seq 1 (nr-1)) ++
   [sub work tmp; shift tmp work; xx work (rkey nr) (Var "dst")]) (bool_e true).
Definition decrypt_branch nr := seqs
  ([xx (Var "src") (rkey nr) work] ++
   map dec_round (rev (seq 1 (nr-1))) ++
   [ishift work tmp; isub tmp work; xx work (rkey 0) (Var "dst")]) (bool_e true).
Definition choose_rounds f :=
  If (eq (Var "nr") (int 10)) (f 10%nat)
    (If (eq (Var "nr") (int 12)) (f 12%nat)
      (If (eq (Var "nr") (int 14)) (f 14%nat) (bool_e false))).
Definition encrypt_body := args ["src";"dst";"schedule";"nr";"work"] (choose_rounds encrypt_branch).
Definition decrypt_body := args ["src";"dst";"schedule";"nr";"work"] (choose_rounds decrypt_branch).
Definition cipher_call body s d := invoke body [s;d;Var "schedule";Var "nr";work].
Definition ige_work := ptr work 32.
Definition ige_tmp := ptr work 48.
Definition ivp := Var "iv".
Definition ivq := ptr ivp 16.
Definition in_at := Offset (Var "src") (Var "i").
Definition out_at := Offset (Var "dst") (Var "i").
Definition ige_iteration (enc : bool) :=
  if enc then seqs [xx in_at ivp ige_work;
    cipher_call encrypt_body ige_work ige_tmp;
    xx ige_tmp ivq out_at; cp out_at ivp; cp in_at ivq] unit_e
  else seqs [xx in_at ivq ige_work;
    cipher_call decrypt_body ige_work ige_tmp;
    xx ige_tmp ivp out_at; cp in_at ivp; cp out_at ivq] unit_e.
Definition valid_rounds := If (eq (Var "nr") (int 10)) (bool_e true)
  (If (eq (Var "nr") (int 12)) (bool_e true) (eq (Var "nr") (int 14))).
Definition ige_body enc := args ["src";"dst";"len";"iv";"schedule";"nr";"work"]
  (If (le (int 0) (Var "len"))
    (If (eq (BinOp RemOp (Var "len") (int 16)) (int 0))
      (If valid_rounds
        (VarBind "i" (int 0) (seqs
          [While (le (Var "i") (BinOp MinusOp (Var "len") (int 16)))
            (Seq (ige_iteration enc) (Assign "i" (plus (Var "i") (int 16))))]
          (bool_e true))) (bool_e false)) (bool_e false)) (bool_e false)).
