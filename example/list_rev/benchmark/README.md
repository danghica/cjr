# In-place list reversal benchmark

Run `make -C example/list_rev benchmark` from the repository root. The existing
shared runner compiles with Cangjie 1.0.5 and `--test -O2`, launches three fresh
processes, saves raw CSV and metadata, and produces median/IQR summaries and an
offline report. `make -C example/list_rev assemble` adds the results to the
example report.

The extracted program is unchanged. Its comparator is an independent native
singly linked reversal with the same tagged-sentinel convention. Both allocate
one sentinel on each reversal. Their link-access bridges differ, so these
measurements compare concrete implementations rather than isolate a cost of
verification.

Lists of 256, 4096 and 16384 elements are built outside timing. Each batch
reverses twice, reading the resulting heads as a checked checksum and restoring
the original orientation. The reported operation is one full reversal, including
sentinel allocation, GC, and amortized checksum overhead. Each implementation
receives two warmup batches and independent calibration toward 20 ms, capped at
65536 batches. Seven trials run per process; trial-plus-process parity rotates
which implementation runs first. Summaries use all 21 observations per size and
implementation and inclusive quartiles.

Outside timing, both implementations validate full reverse and double-reverse
sequences for empty, singleton, duplicate/negative-valued and all measured-size
lists. Full original sequences are checked again after timing. A wrong length or
value fails the run. Existing runtime tests additionally exercise node rewiring
and preservation of a separate list.

`results/raw.csv`, `summary.json`, and `metadata.json` are the recorded results.
Dates and machine/compiler provenance are local observations. Rerunning replaces
these result files; changing repository paths is not itself a new measurement.
