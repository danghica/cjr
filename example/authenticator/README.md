# Authenticator core

Memory-only, platform-independent CJR core for the authenticator described in
[the implementation plan](../../authenticator-plan.md). This directory contains
milestone 1–2 work only. There are no CLI, SwiftUI, FFI, URI parsing, or Cliver
adapters. The generated empty `main` is printer boilerplate, not a frontend.

Readable Rocq documentation, including the declaration dependency graph, is in
[the generated index](docs/rocq/index.html). Regenerate it with
`make -C example/authenticator readable` from the repository root. Set
`EXPLANATIONS=offline` to use only cached explanations; the default generates
missing explanations through the configured Codex CLI.

## Status and proof coverage

The core is implemented as CJR terms and extracted to compilable Cangjie.
Runtime tests exercise SHA-1, HMAC-SHA-1, HOTP, TOTP, Base32, and account sessions.
**Milestone 2 is not complete:** the full Iris refinement of the heap-based
routines has not been established. Passing the build, proof audit, and runtime
suite does not turn these routines into a fully verified application core.

Checked proofs currently cover:

- Signed division's operational rule and primitive Iris contract.
- SHA-1 round refinement (`round_wp`) for arbitrary round inputs, rotation
  refinement, and remaining-validity calculation.
- Base32 character conversion and early size rejection for Base32/SHA-1,
  plus invalid timing-argument rejection.
- Owned-buffer read/write contracts (`buffer_get_wp`, `buffer_put_wp`) and a
  reusable counted-loop Iris rule (`counted_while_wp`).
- Pure SHA-1/HMAC output lengths and byte ranges; HOTP/TOTP output ranges.
- SHA-1 padding capacity/alignment, word masking, five-word addition bounds,
  rotation-product bounds, time-counter bounds, and countdown bounds.
- Canonical Base32 model output byte validity.
- Abstract account-model validity, monotonic insertion, identifier uniqueness,
  failed enrollment preserving state, and removal validity/absence.
- Executable Rocq checks for SHA-1 empty/abc and RFC HOTP/TOTP examples.

Remaining milestone-2 proof obligations are buffer ownership and loop refinements
for SHA-1 padding/scheduling/compression, HMAC composition, HOTP/TOTP composition,
Base32 decoding/rejection, and the concrete session layout. These must connect
the extracted implementations to the pure models, including unchanged outputs
and session state on rejection. The abstract account model is not yet a proof
of `authAdd`, `authRename`, or `authRemove`. Likewise, generic arithmetic bounds
are not yet a proof that every extracted intermediate stays within `Int64`.

No theorem claims cryptographic security, constant-time execution, or guaranteed
secret erasure. Compilation/runtime, allocation success, and platform adapters
remain outside CJR's proof boundary. Inputs to extracted functions must respect
the buffer ownership and capacity requirements below.

## Build and check

With the repository's Rocq and Cangjie toolchains available:

```sh
make -C example/authenticator build
make -C example/authenticator extract
make -C example/authenticator test
make verify
```

The extraction script evaluates `print_prog authenticator_program` in Rocq;
it does not hand-write or patch the generated Cangjie. `make extract` and
`make test` at the repository root include this core. Runtime artifacts are
written to `build/authenticator/`: compiler log, execution log, and JSON report.

The test runner generates deterministic independent oracles using Python
`hashlib`, `hmac`, and `base64`, plus explicit RFC 4226/6238 fixtures. Coverage
includes padding boundaries, keys crossing the HMAC block size, six/eight digits,
period boundaries, post-2038 and maximum signed timestamps, malformed Base32,
capacity, session isolation, identifier exhaustion, and whole-session snapshots
on failure. Test inputs contain synthetic secrets only.

## Core interface and buffer contract

All buffers are `CPointer<Int64>` with **one logical byte per word**, not packed
bytes. Byte values must lie in 0..255. Callers own sufficiently large live
buffers. The session must be a live `authNew` result and must not be changed
outside these operations. Calls on the same session must be serialized. Never
use a destroyed pointer or supply an input/output buffer overlapping session
storage. Outputs must have their documented capacity and not overlap inputs.
Read-only input buffers may overlap each other.

Cryptographic operations:

- `authSha1(src, n, dst)`: 0..2048 input bytes, 20 output words; returns `Bool`.
- `authHmac(key, keyLen, msg, msgLen, dst)`: 1..128 key bytes,
  0..1024 message bytes, 20 output words; returns `Bool`.
- `authHotp(key, keyLen, counter, digits)`: nonnegative signed `Int64` counter,
  six or eight digits; returns a numeric code or -1 for invalid arguments.
- `authTotp(key, keyLen, timestamp, period, digits)`: nonnegative Unix seconds,
  period 1..2147483647; returns a numeric code or -1. The epoch is zero.
- `authRemaining(timestamp, period)`: returns 1..period, including a full period
  at the boundary, or -1 for invalid arguments.
- `authBase32(src, n, dst)`: 2..208 ASCII input words, 128 output words; returns
  the decoded length or -1. Accepts upper/lowercase and optional canonical `=`
  padding, rejects whitespace and nonzero unused bits, and requires 1..128
  decoded bytes. It validates in scratch storage before writing the result.

Numeric codes retain their configured digit count in account metadata; future
adapters must zero-pad when displaying them. No algorithm selector is exposed:
this version supports SHA-1 only. HMAC/HOTP/TOTP do not call external crypto.

Session operations:

- `authNew()` / `authDestroy(session)`: allocate/dispose an independent session.
  Destruction overwrites session words before freeing in the source program;
  no platform-level erasure guarantee is made.
- `authAdd(session, label, labelLen, issuer, issuerLen, secret, secretLen,
  digits, period)`: Base32 secret input; returns a positive identifier, -1 for
  invalid input, -2 for capacity, or -3 for exhausted identifiers.
- `authList(session, dst)`: capacity 16 words; writes live identifiers and
  returns their count. Ordering is unspecified.
- `authRead(session, id, dst)`: capacity 260 words; returns `Bool`. Writes
  `[digits, period, labelLen, issuerLen]`, label at offset 4, issuer at offset
  132. Only the indicated string lengths are meaningful; it does not expose
  secret length or secret material.
- `authRename(session, id, label, labelLen, issuer, issuerLen)`: updates display
  metadata, returning `Bool`.
- `authRemove(session, id)`: overwrites the slot, returning whether it existed.
- `authCode(session, id, timestamp)`: returns a code or -1. Use `authRead` for
  digits/period and `authRemaining` for the countdown.

Sessions hold at most 16 accounts. Labels are 1..128 opaque bytes and issuers
0..128 opaque bytes; encoding and URI syntax are adapter concerns. Duplicate
labels are allowed. Identifiers are monotonic and are never reused during a
session. Failed operations leave existing session state unchanged in runtime
tests; complete concrete Iris proofs of that property remain outstanding.

The 6242-word session layout is internal: next identifier and live count in two
header words, followed by 16 slots of 390 words. Each slot contains identifier,
digits, period, label length, issuer length, secret length, then three 128-word
regions for label, issuer, and decoded secret. External consumers must use the
operations rather than depending on these offsets.
