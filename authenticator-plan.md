# Verified authenticator: core first, three interfaces

## 1. First-version scope

Build a memory-only authenticator that manages accounts and generates offline time-based one-time passwords.

- Support adding, listing, renaming, and removing accounts.
- Accept manually entered Base32 secrets and `otpauth://totp` enrollment URIs.
- Initially support SHA-1, six- or eight-digit codes, and positive configurable periods; default to six digits and 30 seconds.
- Show each account’s current code and time remaining.
- Target a Cangjie CLI, macOS SwiftUI app, and local Cliver browser interface.

Defaults: no persistence, synchronization, push approval, passkeys, QR image scanning, or account export in this version. Each running interface owns its own independent session.

## 2. Hexagonal architecture

**CJR core**

Own account state, parameter validation, Base32 decoding, SHA-1, HMAC, HOTP construction, and TOTP calculation. Develop these as Rocq specifications and CJR implementations with Iris refinement proofs, then extract Cangjie.

Expose operations for session creation/destruction, account management, and code generation. Code generation takes an explicit Unix timestamp and returns the numeric code, digit count, and remaining validity. Account listings exclude secrets.

Keep operating-system access, clocks, text presentation, networking, and foreign-language types outside the core. Use explicit status results for invalid input, unknown accounts, and capacity limits.

**Ports and adapters**

- A clock adapter supplies timestamps; tests supply deterministic values.
- Enrollment adapters parse URI syntax into normalized fields; the core validates supported parameters and decodes secrets.
- CLI, SwiftUI, and Cliver invoke the same application operations.
- Session construction wires the adapters to the extracted core. No interface implements OTP algorithms.

## 3. Implementation sequence

### Milestone 1 — Specifications and CJR arithmetic support

- Add an isolated authenticator development following the repository’s specification, proof, extraction, and runtime-test conventions.
- Specify SHA-1, HMAC, HOTP, TOTP, account state, and failure behavior.
- Add integer division to CJR semantics, proof rules, and extraction. Use bounded nonnegative arithmetic to implement word shifts and rotations.
- Prove byte ranges, 32-bit word masking, and bounds sufficient to avoid extracted `Int64` overflow. Do not rely on CJR’s unbounded integers matching machine arithmetic automatically.

### Milestone 2 — Complete verified core

- Implement and prove SHA-1, including padding, message scheduling, compression, and digest encoding.
- Implement and prove HMAC-SHA-1, HOTP truncation, decimal reduction, and TOTP time-counter calculation against the specifications.
- Implement validated Base32 decoding and account operations.
- Define finite input and account-capacity limits in the public contract; reject invalid inputs without changing existing session state.
- Complete extraction and runtime validation before starting production front-end work.

### Milestone 3 — Cangjie CLI

- Provide an interactive session so accounts survive successive commands until exit.
- Support account management, URI enrollment, current-code display, and deterministic timestamp input for testing.
- Read enrollment secrets through input rather than command-line arguments; exclude secrets from diagnostic output.
- Expose a narrow public Cangjie command façade suitable for Cliver generation, keeping internal cryptographic functions out of its command surface.

### Milestone 4 — SwiftUI through FFI

- First validate a minimal Cangjie-to-C ABI bridge callable from Swift.
- Expose opaque session handles, fixed-width scalar parameters, explicit buffer lengths, status codes, and destruction functions.
- Document ownership and lifetimes; prevent Cangjie runtime objects or exceptions from crossing the ABI.
- Build account enrollment, account list, code countdown, copy action, and deletion flows.
- Serialize access to each core session. Timer ticks obtain a fresh timestamp and request a new result from the core.

### Milestone 5 — Cliver web interface

- Generate commands from the public application façade.
- Adapt Cliver’s backend to maintain one Cangjie worker per WebSocket connection using its existing `--serve-stdin` mode.
- Serialize requests and responses within each connection; destroy session state when its worker exits or the connection closes.
- Keep the integration in this application rather than changing the separate Cliver repository.
- Bind locally, validate browser origins, and keep enrollment secrets and generated codes out of backend logs and retained command history.

## 4. Verification and acceptance

- Check SHA-1 and HMAC against published known-answer vectors; check HOTP and TOTP against [RFC 4226](https://www.rfc-editor.org/rfc/rfc4226) and [RFC 6238](https://www.rfc-editor.org/rfc/rfc6238).
- Test hash block boundaries, long HMAC keys, leading-zero codes, time-step transitions, timestamps beyond 2038, and supported digit/period combinations.
- Test malformed enrollment data, unsupported algorithms, duplicate account labels, missing account IDs, capacity limits, and unchanged state after rejection.
- Verify that identical secrets, parameters, and timestamps produce identical results through all three adapters.
- Test FFI buffer handling and session destruction; test Cliver state across messages, connection isolation, and cleanup.
- Run the repository’s proof audit with `make verify` and the relevant extracted Cangjie runtime suites.

The core milestone is complete only when its proofs and extracted tests pass. Final prototype acceptance requires all three interfaces to enroll an account, display matching codes, and discard accounts when their sessions end.

## 5. Proof boundary and later work

Prove functional correctness and modeled memory safety without admissions or new axioms. Treat the compiler/runtime, FFI bridge, clock, URI parser, and operating system as trusted boundaries covered by integration tests.

Cryptographic security, constant-time execution, and guaranteed secret erasure are separate claims. Persistence and secure storage will be designed after the memory-only prototype is validated.
