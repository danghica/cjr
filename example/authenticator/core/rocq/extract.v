From Coq Require Import String List.
From cjr.examples Require Import cj_print.
From cjr.authenticator Require Import program.
Import ListNotations.
Open Scope string_scope.
Definition ti := "Int64".
Definition tp := "CPointer<Int64>".
Definition authenticator_program := Prog [] [Decl "ShaState" [("a",ti);("b",ti);("c",ti);("d",ti);("e",ti)]]
 [Fn "authCopy" None (Some "args") copy_body [tp;tp;ti] "Unit";
  Fn "authZero" None (Some "args") zero_body [tp;ti] "Unit";
  Fn "authBytes" None (Some "args") byte_body [tp;ti] "Bool";
  Fn "authRound" None (Some "args") round_body [ti;ti;ti;ti;ti;ti;ti] "ShaState";
  Fn "authSha1" None (Some "args") sha_body [tp;ti;tp] "Bool";
  Fn "authHmac" None (Some "args") hmac_body [tp;ti;tp;ti;tp] "Bool";
  Fn "authHotp" None (Some "args") hotp_body [tp;ti;ti;ti] ti;
  Fn "authTotp" None (Some "args") totp_body [tp;ti;ti;ti;ti] ti;
  Fn "authRemaining" None (Some "args") remaining_body [ti;ti] ti;
  Fn "authBase32Value" None (Some "args") base32_value_body [ti] ti;
  Fn "authBase32" None (Some "args") base32_body [tp;ti;tp] ti;
  Fn "authNew" None None new_body [] tp;
  Fn "authDestroy" None (Some "args") destroy_body [tp] "Unit";
  Fn "authFind" None (Some "args") program.find_body [tp;ti] ti;
  Fn "authAdd" None (Some "args") add_body [tp;tp;ti;tp;ti;tp;ti;ti;ti] ti;
  Fn "authList" None (Some "args") list_body [tp;tp] ti;
  Fn "authRead" None (Some "args") read_body [tp;ti;tp] "Bool";
  Fn "authRemove" None (Some "args") remove_body [tp;ti] "Bool";
  Fn "authRename" None (Some "args") rename_body [tp;ti;tp;ti;tp;ti] "Bool";
  Fn "authCode" None (Some "args") code_body [tp;ti;ti] ti] unit_e.
Definition authenticator_cj := print_prog authenticator_program.
