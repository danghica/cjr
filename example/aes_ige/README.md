# AES-IGE

Concrete AES-128/192/256 and OpenSSL-compatible Infinite Garble Extension, with
Rocq specifications, algebraic proofs, CJR programs, extracted Cangjie, independent
known-answer tests, and throughput benchmarks.

Open `index.html` for the offline artifact index and `docs/report.html` for the
proof narrative and exact coverage. Build and audit with `make build` and
`make verify`; regenerate code with `make extract`; run `make test`,
`make benchmark`, and `make docs EXPLANATIONS=offline`; assemble with `make assemble`.

The specification algebra includes both AES inverse compositions, bijectivity,
transformation inverses, byte-XOR laws, both IGE inverse compositions with final-IV
agreement, range/length preservation, empty identity, and chunk composition.
No cipher correctness, additional axioms, or admissions are assumed.

The complete Iris refinement covers caller-owned key expansion, every AES block
variant, and both IGE loops. Client contracts prove both implementation round trips
with identical original IV values, final-IV agreement, empty identity, and chunk
composition. Invalid-argument contracts prove rejection before raw-buffer access.
All public contracts are included in the repository assumption and kernel audits.
The offline renderer selects the mathematical model and generic public contracts;
internal fixed-round specializations and closure-substitution machinery remain
in the complete build and kernel audit.
The guarantees cover functional correctness and memory safety under the buffer
ownership and bounds preconditions; constant-time behavior and cryptographic
security proofs remain outside scope.

## API

- `aesExpandKey(key, keyLen, schedule)` returns 10/12/14 for 16/24/32 key bytes,
  or zero for invalid length. Reserve 240 words for the schedule. Only the first
  176/208/240 words are written for the corresponding variant.
- `aesEncryptBlock(src, dst, schedule, nr, work)` and `aesDecryptBlock(...)`
  process 16 bytes, represented as sixteen Int64 words.
- `aesIgeEncrypt(src, dst, len, iv, schedule, nr, work)` and `aesIgeDecrypt(...)`
  process a nonnegative multiple of 16 bytes and update the 32-word IV.
- Reserve 64 words for workspace. All input, output, schedule, IV, and workspace
  regions must be disjoint and large enough. Inputs must be in 0..255. Use the
  expanded schedule matching the key and round count. Empty calls permit zero
  accessible message words; they still require a valid round count.

Invalid round counts and invalid message lengths return false without changing
output or IV. Invalid key lengths return zero without changing the schedule.
Pointer validity, capacities, byte-valued contents, and non-aliasing are caller
preconditions, not dynamic checks.

The IV is `previous ciphertext || previous plaintext`. To decrypt an encrypted
message, restore the original IV. To continue a message in chunks, retain the
mutated IV. No padding, authentication, in-place operation, or bidirectional IGE
is provided. The branch-based S-box is not constant-time; no side-channel or
cryptographic security theorem is claimed.

Reference fixtures use OpenSSL's low-level API; regenerate them with
`python3 scripts/reference_vectors.py --library /path/to/libcrypto`.
The fixture JSON records the OpenSSL version and library digest. The executable
implementation never calls OpenSSL.

## OpenSSL performance comparison

`make benchmark` measures both extracted Cangjie and the native OpenSSL C
`AES_ige_encrypt` API, rebuilding and checking complete outputs and final IVs
before collecting timings. It needs a C compiler and OpenSSL development files;
set `CC` and `OPENSSL_PREFIX` to override the defaults (`cc` and Homebrew
`openssl@3`). Native toolchain/library provenance is saved in
`benchmark/results/openssl-metadata.json`; full-byte agreement is recorded in
`benchmark/results/differential.json`.

Both harnesses reuse schedules, reset the IV, and sum outputs inside timing.
Three processes each produce seven samples after two warm-up calls and independent
calibration to 20 ms or 16,777,216 repetitions. Encryption/decryption units are ns per
logical byte; key setup units are ns per forward expansion including its checksum.
OpenSSL requires a separately prepared inverse schedule for decryption, excluded
from throughput timing and not separately measured. CJR stores bytes in Int64
words; OpenSSL uses packed bytes. This is a practical implementation comparison,
not a measurement that isolates language overhead or establishes hardware AES use.
