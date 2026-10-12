# list: historical runtime results

These entries were relocated from the historical suite report; this is not a new test run. Dates and detailed run commentary are retained in [the original suite record](../../../paper/test-history.md).

| `list.cj` | 3 | passed |
The three existing `list.cj` cases were also compiled and rerun on the same compiler; all passed. The list regression total for this run is 9/9 (six reversal cases plus three existing list cases). `coqchk` succeeds for the reversal module and `make check-proofs` completes for the project. The project-wide `make check-no-cheats` gate now passes: the hash map obligations have been completed, and the source contains no admitted proofs or declared axioms.
The optimized benchmark suites compile the generated `list.cj`, `array.cj`, `array_list.cj`, and `hash_map.cj`
