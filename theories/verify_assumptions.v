(** Audit: [Print Assumptions] on representative closed theorems.
    Built by [make check-axioms]; each should report "Closed under the global context". *)

From cjr Require Import adequacy.
From cjr.examples Require Import arith struct_upd cell class_upd vtable list_rev.

Print Assumptions cjr_adequacy.
Print Assumptions sum_one_adequate.
Print Assumptions bump_adequate.
Print Assumptions cell_adequate.
Print Assumptions class_bump_adequate.
Print Assumptions vtable_adequate.

Print Assumptions reverse_spec.
Print Assumptions reverse_twice_spec.
