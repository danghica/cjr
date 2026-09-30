(** Audit: [Print Assumptions] on representative closed theorems.
    Built by [make check-axioms]; each should report "Closed under the global context". *)

From cjr Require Import adequacy.
From cjr.examples Require Import arith struct_upd cell class_upd vtable list_rev hash_map.

Print Assumptions cjr_adequacy.
Print Assumptions sum_one_adequate.
Print Assumptions bump_adequate.
Print Assumptions cell_adequate.
Print Assumptions class_bump_adequate.
Print Assumptions vtable_adequate.

Print Assumptions reverse_spec.
Print Assumptions reverse_twice_spec.

(** HashMap operations, kernels, and client compositions. *)
Print Assumptions hash_map.residue_wp.
Print Assumptions hash_map.scan_spec.
Print Assumptions hash_map.buffer_probe_spec.
Print Assumptions hash_map.put_spec.
Print Assumptions hash_map.rehash_spec.
Print Assumptions hash_map.init_spec.
Print Assumptions hash_map.size_spec.
Print Assumptions hash_map.capacity_spec.
Print Assumptions hash_map.is_empty_spec.
Print Assumptions hash_map.probe_spec.
Print Assumptions hash_map.contains_spec.
Print Assumptions hash_map.get_spec.
Print Assumptions hash_map.grow_spec.
Print Assumptions hash_map.add_room_spec.
Print Assumptions hash_map.add_spec.
Print Assumptions hash_map.remove_spec.
Print Assumptions hash_map.add_then_get_spec.
Print Assumptions hash_map.add_then_contains_spec.
Print Assumptions hash_map.init_then_size_spec.
Print Assumptions hash_map.init_then_capacity_spec.
Print Assumptions hash_map.init_then_empty_spec.
