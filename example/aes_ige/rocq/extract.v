From Coq Require Import String List.
From cjr.examples Require Import cj_print.
From cjr.aes_ige Require Import program.
Import ListNotations.
Open Scope string_scope.
Definition tptr := "CPointer<Int64>".
Definition tint := "Int64".
Definition aes_program := Prog [] []
 [Fn "aesSbox" None (Some "x") sbox_body [tint] tint;
  Fn "aesInvSbox" None (Some "x") inv_sbox_body [tint] tint;
  Fn "aesXtime" None (Some "x") xtime_body [tint] tint;
  Fn "aesCopy" None (Some "args") copy_body [tptr;tptr] "Unit";
  Fn "aesXor" None (Some "args") xor_body [tptr;tptr;tptr] "Unit";
  Fn "aesSub" None (Some "args") sub_body [tptr;tptr] "Unit";
  Fn "aesInvSub" None (Some "args") inv_sub_body [tptr;tptr] "Unit";
  Fn "aesShift" None (Some "args") shift_body [tptr;tptr] "Unit";
  Fn "aesInvShift" None (Some "args") inv_shift_body [tptr;tptr] "Unit";
  Fn "aesMix" None (Some "args") mix_body [tptr;tptr] "Unit";
  Fn "aesExpandKey" None (Some "args") expand_body [tptr;tint;tptr] tint;
  Fn "aesEncryptBlock" None (Some "args") encrypt_body [tptr;tptr;tptr;tint;tptr] "Bool";
  Fn "aesDecryptBlock" None (Some "args") decrypt_body [tptr;tptr;tptr;tint;tptr] "Bool";
  Fn "aesIgeEncrypt" None (Some "args") (ige_body true) [tptr;tptr;tint;tptr;tptr;tint;tptr] "Bool";
  Fn "aesIgeDecrypt" None (Some "args") (ige_body false) [tptr;tptr;tint;tptr;tptr;tint;tptr] "Bool"] unit_e.
