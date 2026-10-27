(** CJR source of the authenticator core. No platform or UI operations. *)
From Coq Require Import ZArith String List.
From cjr Require Import lang.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Definition int (x : Z) := Val (LitV (LitInt x)).
Definition yes := Val (LitV (LitBool true)).
Definition no := Val (LitV (LitBool false)).
Definition unit_e := Val (LitV LitUnit).
Definition v := Var.
Definition op := BinOp.
Definition add := op PlusOp.
Definition sub := op MinusOp.
Definition mul := op MulOp.
Definition div := op DivOp.
Definition rem := op RemOp.
Definition band := op BitAndOp.
Definition xor := op BitXorOp.
Definition eq := op EqOp.
Definition le := op LeOp.
Definition both := op AndOp.
Definition range x lo hi := both (le (int lo) x) (le x (int hi)).
Definition ptr p i := Offset p i.
Definition get p i := Load (ptr p i).
Definition put p i x := Store (ptr p i) x.
Definition seqs xs last := fold_right Seq last xs.
Definition args names body := fold_right (fun ni e => Let (Some (fst ni))
 (StructLoad (v "args") (snd ni)) e) body (combine names (seq 0 (length names))).
Definition call body values := App (Rec None (Some "args") body) (Struct [] values).
Definition lets names body := fold_right (fun nx e => Let (Some (fst nx)) (snd nx) e) body names.
Definition vars names body := fold_right (fun nx e => VarBind (fst nx) (snd nx) e) body names.
Definition loop name start stop body := VarBind name start (While (le (v name) (sub stop (int 1)))
 (Seq body (Assign name (add (v name) (int 1))))).
Definition copy_body := args ["source";"dest";"count"]
 (loop "copyI" (int 0) (v "count") (put (v "dest") (v "copyI") (get (v "source") (v "copyI")))).
Definition copy src dst n := call copy_body [src;dst;n].
Definition zero_body := args ["dest";"count"] (loop "zeroI" (int 0) (v "count") (put (v "dest") (v "zeroI") (int 0))).
Definition zero dst n := call zero_body [dst;n].
Definition mask x := band x (int 4294967295).
Definition rol x n := mask (add (mul x (int (2^n))) (div x (int (2^(32-n))))).
Definition byte_body := args ["src";"n"] (vars [("valid",yes)]
 (Seq (loop "i" (int 0) (v "n")
   (If (range (get (v "src") (v "i")) 0 255) unit_e (Assign "valid" no))) (v "valid"))).
Definition sha_choose :=
 If (le (v "t") (int 19))
  (xor (band (v "b") (v "c")) (band (xor (v "b") (int 4294967295)) (v "d")))
 (If (le (v "t") (int 39)) (xor (v "b") (xor (v "c") (v "d")))
  (If (le (v "t") (int 59))
   (xor (xor (band (v "b") (v "c")) (band (v "b") (v "d"))) (band (v "c") (v "d")))
   (xor (v "b") (xor (v "c") (v "d"))))).
Definition sha_constant := If (le (v "t") (int 19)) (int 1518500249)
 (If (le (v "t") (int 39)) (int 1859775393)
  (If (le (v "t") (int 59)) (int 2400959708) (int 3395469782))).
Definition round_body := args ["t";"wt";"a";"b";"c";"d";"e"]
 (lets [("f",sha_choose);("k",sha_constant)]
  (Struct [] [mask (add (add (add (add (rol (v "a") 5) (v "f")) (v "e")) (v "k")) (v "wt"));
    v "a";rol (v "b") 30;v "c";v "d"])).
Definition sha_compress := seqs
 [loop "loadT" (int 0) (int 16)
  (put (v "w") (v "loadT")
    (fold_left (fun acc j => add (mul acc (int 256))
       (get (v "pad") (add (v "block") (add (mul (v "loadT") (int 4)) (int j))))) [0;1;2;3] (int 0)));
  loop "expandT" (int 16) (int 80)
   (put (v "w") (v "expandT") (rol (xor (get (v "w") (sub (v "expandT") (int 3)))
    (xor (get (v "w") (sub (v "expandT") (int 8)))
     (xor (get (v "w") (sub (v "expandT") (int 14))) (get (v "w") (sub (v "expandT") (int 16)))))) 1))]
 (vars [("a",v "h0");("b",v "h1");("c",v "h2");("d",v "h3");("e",v "h4")]
  (seqs [loop "t" (int 0) (int 80)
    (lets [("next",call round_body [v "t";get (v "w") (v "t");v "a";v "b";v "c";v "d";v "e"])]
     (seqs [Assign "a" (StructLoad (v "next") 0);Assign "b" (StructLoad (v "next") 1);
       Assign "c" (StructLoad (v "next") 2);Assign "d" (StructLoad (v "next") 3)]
       (Assign "e" (StructLoad (v "next") 4))));
    Assign "h0" (mask (add (v "h0") (v "a")));
    Assign "h1" (mask (add (v "h1") (v "b")));
    Assign "h2" (mask (add (v "h2") (v "c")));
    Assign "h3" (mask (add (v "h3") (v "d")))]
    (Assign "h4" (mask (add (v "h4") (v "e")))))).
Definition emit_be dst start x n := seqs (map (fun i => put dst (add start (int (Z.of_nat i)))
  (rem (div x (int (256 ^ Z.of_nat (n-1-i)))) (int 256))) (seq 0 n)) unit_e.
Definition sha_body := args ["src";"n";"dst"]
 (If (range (v "n") 0 2048)
  (If (call byte_body [v "src";v "n"])
   (lets [("pad",Alloc (int 2112));("w",Alloc (int 80));
     ("total",mul (div (add (v "n") (int 72)) (int 64)) (int 64))]
    (seqs [copy (v "src") (v "pad") (v "n");put (v "pad") (v "n") (int 128);
      emit_be (v "pad") (sub (v "total") (int 8)) (mul (v "n") (int 8)) 8;
      vars [("h0",int 1732584193);("h1",int 4023233417);("h2",int 2562383102);
       ("h3",int 271733878);("h4",int 3285377520);("block",int 0)]
       (Seq (While (le (v "block") (sub (v "total") (int 1)))
         (Seq sha_compress (Assign "block" (add (v "block") (int 64)))))
        (seqs (map (fun ni => emit_be (v "dst") (int (4 * Z.of_nat (fst ni))) (v (snd ni)) 4)
          [(0%nat,"h0");(1%nat,"h1");(2%nat,"h2");(3%nat,"h3");(4%nat,"h4")]) unit_e));
      Free (v "w");Free (v "pad")] yes)) no) no).
Definition hmac_body := args ["key";"keyLen";"msg";"msgLen";"dst"]
 (If (both (range (v "keyLen") 1 128) (range (v "msgLen") 0 1024))
 (If (both (call byte_body [v "key";v "keyLen"]) (call byte_body [v "msg";v "msgLen"]))
 (lets [("kb",Alloc (int 64));("inner",Alloc (int 1088));("outer",Alloc (int 84));("digest",Alloc (int 20))]
 (seqs [If (le (v "keyLen") (int 64)) (copy (v "key") (v "kb") (v "keyLen"))
    (Seq (call sha_body [v "key";v "keyLen";v "kb"]) unit_e);
   loop "i" (int 0) (int 64) (seqs
    [put (v "inner") (v "i") (xor (get (v "kb") (v "i")) (int 54))]
    (put (v "outer") (v "i") (xor (get (v "kb") (v "i")) (int 92))));
   copy (v "msg") (ptr (v "inner") (int 64)) (v "msgLen");
   call sha_body [v "inner";add (v "msgLen") (int 64);v "digest"];
   copy (v "digest") (ptr (v "outer") (int 64)) (int 20);
   call sha_body [v "outer";int 84;v "dst"];
   Free (v "digest");Free (v "outer");Free (v "inner");Free (v "kb")] yes)) no) no).
Definition parameters := both (If (eq (v "digits") (int 6)) yes (eq (v "digits") (int 8))) (range (v "period") 1 2147483647).
Definition hotp_body := args ["key";"keyLen";"counter";"digits"]
 (If (both (range (v "keyLen") 1 128) (both (le (int 0) (v "counter"))
   (If (eq (v "digits") (int 6)) yes (eq (v "digits") (int 8)))))
 (If (call byte_body [v "key";v "keyLen"])
 (lets [("msg",Alloc (int 8));("digest",Alloc (int 20))]
 (seqs [emit_be (v "msg") (int 0) (v "counter") 8;
   call hmac_body [v "key";v "keyLen";v "msg";int 8;v "digest"]]
 (lets [("off",band (get (v "digest") (int 19)) (int 15));
   ("binary",band (fold_left (fun acc j => add (mul acc (int 256))
     (get (v "digest") (add (v "off") (int j)))) [0;1;2;3] (int 0)) (int 2147483647));
   ("code",rem (v "binary") (If (eq (v "digits") (int 6)) (int 1000000) (int 100000000)))]
  (seqs [Free (v "digest");Free (v "msg")] (v "code"))))) (int (-1))) (int (-1))).
Definition totp_body := args ["key";"keyLen";"timestamp";"period";"digits"]
 (If (both parameters (le (int 0) (v "timestamp")))
  (call hotp_body [v "key";v "keyLen";div (v "timestamp") (v "period");v "digits"]) (int (-1))).
Definition remaining_body := args ["timestamp";"period"]
 (If (both (range (v "period") 1 2147483647) (le (int 0) (v "timestamp")))
  (sub (v "period") (rem (v "timestamp") (v "period"))) (int (-1))).

(** Canonical RFC 4648 Base32: upper/lower case, optional correct padding,
    zero trailing bits, 1..128 decoded bytes. Failure leaves destination alone. *)
Definition base32_value_body := args ["ch"]
 (If (range (v "ch") 65 90) (sub (v "ch") (int 65))
 (If (range (v "ch") 97 122) (sub (v "ch") (int 97))
 (If (range (v "ch") 50 55) (sub (v "ch") (int 24)) (int (-1))))).
Definition base32_body := args ["src";"n";"dst"]
 (If (range (v "n") 2 208)
 (lets [("scratch",Alloc (int 130))]
 (vars [("valid",yes);("padding",int 0);("symbols",int 0);("acc",int 0);("bits",int 0);("out",int 0)]
 (seqs [loop "i" (int 0) (v "n")
   (lets [("ch",get (v "src") (v "i"))]
    (If (eq (v "ch") (int 61)) (Assign "padding" (add (v "padding") (int 1)))
    (lets [("digit",call base32_value_body [v "ch"])]
     (If (both (range (v "digit") 0 31) (eq (v "padding") (int 0)))
      (seqs [Assign "symbols" (add (v "symbols") (int 1));
       Assign "acc" (add (mul (v "acc") (int 32)) (v "digit"));Assign "bits" (add (v "bits") (int 5))]
       (If (le (int 8) (v "bits"))
        (lets [("factor",If (eq (v "bits") (int 8)) (int 1)
          (If (eq (v "bits") (int 9)) (int 2)
           (If (eq (v "bits") (int 10)) (int 4)
            (If (eq (v "bits") (int 11)) (int 8) (int 16)))))]
         (seqs [put (v "scratch") (v "out") (div (v "acc") (v "factor"));
          Assign "out" (add (v "out") (int 1));Assign "acc" (rem (v "acc") (v "factor"))]
          (Assign "bits" (sub (v "bits") (int 8))))) unit_e)) (Assign "valid" no)))));
  If (both (v "valid") (both (range (v "out") 1 128) (both (eq (v "acc") (int 0))
   (both (If (eq (rem (v "symbols") (int 8)) (int 1)) no
      (If (eq (rem (v "symbols") (int 8)) (int 3)) no
       (If (eq (rem (v "symbols") (int 8)) (int 6)) no yes)))
    (If (eq (v "padding") (int 0)) yes
      (both (eq (rem (v "n") (int 8)) (int 0)) (range (v "padding") 1 6)))))))
    (copy (v "scratch") (v "dst") (v "out")) (Assign "valid" no)]
  (lets [("result",If (v "valid") (v "out") (int (-1)))]
   (Seq (Free (v "scratch")) (v "result")))))) (int (-1))).

(** Session: 2 header words, 16 slots of 390 words. Slot fields:
    id,digits,period,labelLen,issuerLen,secretLen,label[128],issuer[128],secret[128].
    Labels/issuers are opaque byte sequences; display encoding belongs to adapters. *)
Definition session_words : Z := 6242.
Definition slot session index := ptr session (add (int 2) (mul index (int 390))).
Definition new_body := lets [("session",Alloc (int session_words))]
 (Seq (put (v "session") (int 0) (int 1)) (v "session")).
Definition destroy_body := args ["session"] (Seq (zero (v "session") (int session_words)) (Free (v "session"))).
Definition find_body := args ["session";"id"]
 (vars [("found",int (-1))]
  (Seq (loop "i" (int 0) (int 16)
   (If (both (le (int 1) (v "id")) (eq (get (slot (v "session") (v "i")) (int 0)) (v "id")))
    (Assign "found" (v "i")) unit_e)) (v "found"))).
Definition add_body := args ["session";"label";"labelLen";"issuer";"issuerLen";"secret";"secretLen";"digits";"period"]
 (If (both parameters (both (range (v "labelLen") 1 128)
   (both (range (v "issuerLen") 0 128) (range (v "secretLen") 2 208))))
 (If (both (call byte_body [v "label";v "labelLen"]) (call byte_body [v "issuer";v "issuerLen"]))
 (lets [("decoded",Alloc (int 128));("n",call base32_body [v "secret";v "secretLen";v "decoded"])]
 (lets [("result",If (le (int 1) (v "n"))
   (If (le (get (v "session") (int 1)) (int 15))
    (If (le (get (v "session") (int 0)) (int 9223372036854775806))
     (vars [("freeSlot",int (-1))]
      (Seq (loop "i" (int 0) (int 16)
        (If (both (eq (v "freeSlot") (int (-1))) (eq (get (slot (v "session") (v "i")) (int 0)) (int 0)))
         (Assign "freeSlot" (v "i")) unit_e))
       (lets [("entry",slot (v "session") (v "freeSlot"));("id",get (v "session") (int 0))]
        (seqs [put (v "entry") (int 0) (v "id");put (v "entry") (int 1) (v "digits");
         put (v "entry") (int 2) (v "period");put (v "entry") (int 3) (v "labelLen");
         put (v "entry") (int 4) (v "issuerLen");put (v "entry") (int 5) (v "n");
         copy (v "label") (ptr (v "entry") (int 6)) (v "labelLen");
         copy (v "issuer") (ptr (v "entry") (int 134)) (v "issuerLen");
         copy (v "decoded") (ptr (v "entry") (int 262)) (v "n");
         put (v "session") (int 0) (add (v "id") (int 1));
         put (v "session") (int 1) (add (get (v "session") (int 1)) (int 1))] (v "id")))))
      (int (-3))) (int (-2))) (int (-1)))]
  (seqs [zero (v "decoded") (int 128);Free (v "decoded")] (v "result")))) (int (-1))) (int (-1))).
Definition list_body := args ["session";"dst"] (vars [("count",int 0)]
 (Seq (loop "i" (int 0) (int 16)
  (lets [("id",get (slot (v "session") (v "i")) (int 0))]
   (If (le (int 1) (v "id")) (seqs [put (v "dst") (v "count") (v "id")]
     (Assign "count" (add (v "count") (int 1)))) unit_e))) (v "count"))).
Definition read_body := args ["session";"id";"dst"]
 (lets [("index",call find_body [v "session";v "id"])]
  (If (le (int 0) (v "index")) (lets [("entry",slot (v "session") (v "index"))]
   (seqs [copy (ptr (v "entry") (int 1)) (v "dst") (int 4);
    copy (ptr (v "entry") (int 6)) (ptr (v "dst") (int 4)) (get (v "entry") (int 3));
    copy (ptr (v "entry") (int 134)) (ptr (v "dst") (int 132)) (get (v "entry") (int 4))] yes)) no)).
Definition remove_body := args ["session";"id"]
 (lets [("index",call find_body [v "session";v "id"])]
 (If (le (int 0) (v "index")) (seqs [zero (slot (v "session") (v "index")) (int 390);
   put (v "session") (int 1) (sub (get (v "session") (int 1)) (int 1))] yes) no)).
Definition rename_body := args ["session";"id";"label";"labelLen";"issuer";"issuerLen"]
 (If (both (range (v "labelLen") 1 128) (range (v "issuerLen") 0 128))
 (If (both (call byte_body [v "label";v "labelLen"]) (call byte_body [v "issuer";v "issuerLen"]))
 (lets [("index",call find_body [v "session";v "id"])]
 (If (le (int 0) (v "index")) (lets [("entry",slot (v "session") (v "index"))]
   (seqs [zero (ptr (v "entry") (int 6)) (int 256);
    copy (v "label") (ptr (v "entry") (int 6)) (v "labelLen");
    copy (v "issuer") (ptr (v "entry") (int 134)) (v "issuerLen");
    put (v "entry") (int 3) (v "labelLen");put (v "entry") (int 4) (v "issuerLen")] yes)) no)) no) no).
Definition code_body := args ["session";"id";"timestamp"]
 (lets [("index",call find_body [v "session";v "id"])]
 (If (le (int 0) (v "index")) (lets [("entry",slot (v "session") (v "index"))]
  (call totp_body [ptr (v "entry") (int 262);get (v "entry") (int 5);v "timestamp";
    get (v "entry") (int 2);get (v "entry") (int 1)])) (int (-1)))).
