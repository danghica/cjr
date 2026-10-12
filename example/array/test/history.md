# array: historical runtime results

These entries were relocated from the historical suite report; this is not a new test run. Dates and detailed run commentary are retained in [the original suite record](../../../paper/test-history.md).

Each extracted file was compiled on its own with its test file, because every file declares `malloc`, `free`, and `main`, and both `array.cj` and `array_list.cj` declare `class Array`. The quicksort files declare that class as well, and `qsort_array_list.cj` also declares `class ArrayList`. The command was:
| `array.cj` | 3 | passed |
The optimized benchmark suites compile the generated `list.cj`, `array.cj`, `array_list.cj`, and `hash_map.cj`
