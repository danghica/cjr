(** Audit: [Print Assumptions] on representative closed theorems.
    Built by [make check-axioms]; each should report "Closed under the global context". *)

From cjr Require Import adequacy.
From cjr.examples Require Import arith struct_upd cell class_upd vtable list_rev hash_map most_frequent mf_memory.

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

(** Most-frequent: pure correctness, concrete Iris kernels, and the
    complete empty/nonempty operation refinement are audited below. *)
Print Assumptions most_frequent.mf_choose_correct.
Print Assumptions most_frequent.mf_qsort_perm.
Print Assumptions most_frequent.mf_qsort_sorted.
Print Assumptions most_frequent.mf_sorted_pairs_ordered.
Print Assumptions most_frequent.mf_sorted_pairs_frequency.
Print Assumptions most_frequent.mf_sorted_pairs_origin.
Print Assumptions most_frequent.mf_summary_selection_correct.
Print Assumptions most_frequent.mf_empty_wp.
Print Assumptions most_frequent.mf_run_summaries_sound.
Print Assumptions most_frequent.mf_run_summaries_complete.
Print Assumptions most_frequent.mf_sort_scan_correct.

(** Concrete paired quicksort and whole-block cleanup kernels. *)
Print Assumptions mf_memory.mf_wf_free_block.
Print Assumptions mf_memory.mf_wp_free_block.
Print Assumptions most_frequent.most_frequent_spec_unique.
Print Assumptions most_frequent.mf_release_array_wp.
Print Assumptions most_frequent.mf_cleanup_wp.
Print Assumptions most_frequent.mf_swap_arrays_wp.
Print Assumptions most_frequent.mf_swap_pairs_wp.
Print Assumptions most_frequent.mf_lex_compare_wp.
Print Assumptions most_frequent.mf_partition_step_wp.
Print Assumptions most_frequent.mf_partition_step_is_code.
Print Assumptions most_frequent.mf_partition_scan_wp.
Print Assumptions most_frequent.mf_partition_scan_is_code.
Print Assumptions most_frequent.mf_partition_wp.
Print Assumptions most_frequent.mf_qsort_slice_wp.
Print Assumptions most_frequent.mf_qsort_wp.

Print Assumptions most_frequent.mf_copy_complete.
Print Assumptions most_frequent.mf_copy_step_wp.
Print Assumptions most_frequent.mf_copy_loop_wp.
Print Assumptions most_frequent.mf_copy_loop_is_code.
Print Assumptions most_frequent.mf_scan_run_bound.
Print Assumptions most_frequent.mf_group_inner_wp.
Print Assumptions most_frequent.mf_group_inner_is_code.
Print Assumptions most_frequent.mf_group_summary_decomposition.
Print Assumptions most_frequent.mf_fold_best_sound.
Print Assumptions most_frequent.mf_forward_scan_groups.
Print Assumptions most_frequent.mf_forward_scan_correct.
Print Assumptions most_frequent.mf_best_update_slot_wp.
Print Assumptions most_frequent.mf_group_step_wp.
Print Assumptions most_frequent.mf_group_outer_wp.
Print Assumptions most_frequent.mf_group_outer_is_code.
Print Assumptions most_frequent.mf_nonempty_wp.
Print Assumptions most_frequent.mf_wp.
Print Assumptions most_frequent.mf_spec_wp.
