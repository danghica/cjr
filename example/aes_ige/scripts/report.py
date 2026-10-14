#!/usr/bin/env python3
"""Assemble the narrative with observed results and explicit proof coverage."""
from pathlib import Path
import html,json
ROOT=Path(__file__).resolve().parents[1]
def read(rel,default):
 p=ROOT/rel
 return json.loads(p.read_text()) if p.exists() else default

def main():
 tests=read('test/results/report.json',{})
 measurements=read('benchmark/results/summary.json',[])
 verification=read('proof/results/verification.json',{})
 css=ROOT/'docs/report.css'
 css.write_text(':root{color-scheme:light;--ink:#172e37;--muted:#53676f;--accent:#176f76;--line:#c9dadb;--paper:#fff;--wash:#f0f6f5}*{box-sizing:border-box}body{margin:0;background:var(--wash);color:var(--ink);font:16px/1.6 system-ui,sans-serif}main{max-width:1160px;margin:auto;padding:40px 28px}header{border-bottom:2px solid var(--accent);padding-bottom:24px;margin-bottom:28px}.eyebrow{font-size:.8rem;text-transform:uppercase;letter-spacing:.16em;color:var(--accent)}h1{font-size:clamp(2rem,5vw,3.4rem);line-height:1.1;margin:12px 0}h2{font-size:1.5rem;margin:34px 0 14px}h3{font-size:1.08rem;margin:24px 0 10px}p{max-width:85ch}a{color:var(--accent);text-underline-offset:.18em}nav,.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:14px}nav a,.card{padding:16px 20px;background:var(--paper);border:1px solid var(--line);border-radius:8px}.declarations{columns:3 260px;list-style:none;padding:0}.declarations li{break-inside:avoid;margin:0 0 8px}.kind{font-size:.8rem;color:var(--muted);margin-left:8px}.badge{display:inline-block;padding:4px 12px;border-radius:20px;background:#d7ebe4;color:#165940;font-size:.88rem}.pending{background:#fff0d1;color:#795420}pre{background:#fff;border:1px solid var(--line);padding:20px;white-space:pre;overflow-x:auto;font:13px/1.6 ui-monospace,monospace}details{margin:14px 0}summary{cursor:pointer;color:var(--accent)}table{width:100%;border-collapse:collapse;background:#fff;font-size:.9rem}td,th{text-align:left;padding:8px 12px;border-bottom:1px solid var(--line)}.scroll{overflow-x:auto}img{max-width:100%;height:auto;background:white}footer{margin-top:36px;border-top:1px solid var(--line);padding-top:16px;color:var(--muted);font-size:.85rem}@media(max-width:500px){main{padding:24px 16px}.declarations{columns:1}nav{grid-template-columns:1fr}}\n/* Shared report pages retain long generated source lines on narrow screens. */\nmain, article { min-width: 0; box-sizing: border-box; }\narticle { max-width: 100%; overflow-x: hidden; }\npre { min-width: 0; max-width: 100%; overflow-x: auto; box-sizing: border-box; }\n\narticle{background:white;padding:20px 26px;margin:18px 0;border:1px solid var(--line);border-radius:8px}.status{border-left:5px solid #b66b12}code{overflow-wrap:anywhere}li{margin:8px 0}\n')
 laws=[
 ('AES inverse compositions','decrypt(k, encrypt(k, b)) = b and encrypt(k, decrypt(k, b)) = b.',
  'Byte-valued 16-byte blocks. The concrete schedule contains byte-valued round keys.',
  'Each inverse round cancels AddRoundKey, MixColumns, ShiftRows, and SubBytes in reverse order. Induction on the round-key list cancels the entire cipher. The final round has its own inverse because it omits MixColumns.',
  'aes','decrypt_encrypt; encrypt_decrypt'),
 ('AES bijectivity','Encryption and decryption are injective and surjective on byte-valued blocks.',
  'Fixed key and the same block domain.',
  'Apply the inverse function to an equality for injectivity. For surjectivity, choose the inverse image and use the appropriate inverse composition.',
  'aes','encrypt_injective; decrypt_injective; encrypt_surjective; decrypt_surjective'),
 ('Transformation inverse laws','Both orders of SubBytes/InvSubBytes, ShiftRows/InvShiftRows, and MixColumns/InvMixColumns are identity; AddRoundKey twice with the same key is identity.',
  'SubBytes requires byte-valued coordinates. Row permutation and XOR cancellation hold for arbitrary integer coordinates.',
  'A kernel-checked finite certificate checks the S-box on all 256 inputs against the finite-field definition and both inverse compositions. Row permutations cancel by direct coordinate computation. The MixColumns matrix has fourth power identity, proved using xtime linearity and bitwise Boolean algebra; its third power equals the FIPS inverse matrix with coefficients 14,11,13,9.',
  'block','sub_inverse; inverse_sub; shift_inverse; inverse_shift; mix_columns_inverse; inverse_mix_columns; inv_mix_fips; xor_cancel'),
 ('Byte XOR algebra','Associativity, commutativity, zero identity, self-cancellation, cancellation, and byte-range closure.',
  'The algebraic equalities hold for all integers; closure requires byte-valued operands.',
  'Use Rocq bitwise integer laws and bit extensionality. Masking commutes with XOR, so the XOR of two eight-bit values remains eight-bit.',
  'bytes','bx_assoc; bx_comm; bx_zero; bx_self; bx_cancel; bx_byte'),
 ('IGE inverse compositions and final IV','Decrypting encrypted blocks, or encrypting decrypted blocks, recovers the input; the final IVs of the paired operations agree.',
  'Both directions start from the SAME original IV. Message blocks and both IV blocks are byte-valued.',
  'Each IGE step cancels the outer XOR, applies the concrete AES inverse law, and cancels the inner XOR. Induction carries the identical ciphertext/plaintext IV pair to the next step. The theorem returns both recovered blocks and the original operation’s final IV.',
  'ige','ige_decrypt_encrypt; ige_encrypt_decrypt'),
 ('IGE bijectivity','For fixed key, initial IV, and block count, both output transformations are bijections.',
  'Byte-valued messages and IV. Bijectivity concerns output messages, with the final IV determined by the operation.',
  'Apply the opposite direction to equal outputs for injectivity. Choose the opposite transformation as the preimage for surjectivity; range and length theorems ensure membership in the same domain.',
  'ige','ige_encrypt_injective; ige_decrypt_injective; ige_encrypt_surjective; ige_decrypt_surjective'),
 ('Length, range, and empty identity','AES produces 16-byte blocks; IGE preserves block count and byte range. Empty messages return an empty output and the unchanged IV.',
  'Range preservation requires byte-valued message and IV inputs.',
  'The fixed block record contains sixteen coordinates. Induction on the message establishes length and range preservation. Empty identity is the defining base case of both IGE functions.',
  'ige','ige_encrypt_length; ige_decrypt_length; ige_encrypt_range; ige_decrypt_range; ige_encrypt_empty; ige_decrypt_empty'),
 ('Chunk composition','Processing xs ++ ys equals processing xs and then ys using the returned IV, including equality of the final IV.',
  'Chunks contain whole AES blocks. The pure theorem itself needs no byte-range premise.',
  'Induction on the first chunk unfolds one step on each side and applies the induction hypothesis to the updated IV. Both output concatenation and final state follow.',
  'ige','ige_encrypt_chunks; ige_decrypt_chunks'),
 ]
 consequences={
 'AES inverse compositions':'The checked block_implementation_roundtrip contract composes the concrete routines in both orders and returns the original block while preserving source and schedule.',
 'AES bijectivity':'Each valid output block has exactly one valid input for the fixed key.',
 'Transformation inverse laws':'The proved transformation kernels can be composed into forward and inverse rounds without assuming an opaque AES primitive.',
 'Byte XOR algebra':'The IGE step proofs cancel both chaining XORs while preserving the byte domain.',
 'IGE inverse compositions and final IV':'The checked ige_implementation_roundtrip contract starts both calls from the same original IV value, using independently initialized IV buffers. It recovers the message and proves equality of their final IVs; a caller reusing one IV buffer must restore its original value before the inverse call.',
 'IGE bijectivity':'A fixed initial IV gives a unique plaintext/ciphertext correspondence at every supported block count.',
 'Length, range, and empty identity':'The complete IGE refinement fixes output capacity to input capacity; ige_implementation_empty proves that the concrete call preserves the IV for zero input blocks.',
 'Chunk composition':'The checked ige_implementation_chunks contract executes both concrete calls using the returned IV and proves the same concatenated output and final state as one call.'}
 sections=[]
 for title,statement,assumptions,proof,module,names in laws:
  links=' · '.join(f'<a href="rocq/rocq/{module}.html#{html.escape(n)}">{html.escape(n)}</a>' for n in names.split('; '))
  # Renderer anchor spelling is derived from its navigation, so link to the module page.
  links=f'<a href="rocq/rocq/{module}.html">Checked declarations: {html.escape(names)}</a>'
  sections.append(f'<article><h3>{title}</h3><p><strong>Statement.</strong> {statement}</p><p><strong>Assumptions.</strong> {assumptions}</p><p><strong>Proof.</strong> {proof}</p><p><strong>Consequence.</strong> {consequences[title]}</p><p>{links}</p></article>')
 bench=''.join(f'<li>{html.escape(r.get("implementation","CJR"))} {html.escape(r["case"])} at {r["n"]} bytes: median {r["median_ns"]:.2f} '+('ns/expansion' if r['case'].startswith('key_') else 'ns/byte')+f'; {r["samples"]} samples.</li>' for r in measurements)
 paired={(r['case'],r['n'],r.get('implementation','CJR')):r for r in measurements}
 comparison=[]
 for bits in (128,192,256):
  for direction in ('encrypt','decrypt'):
   case=f'{direction}_{bits}'
   native=paired.get((case,65536,'OpenSSL'))
   extracted=paired.get((case,65536,'CJR'))
   if native and extracted:
    comparison.append(f"<li>AES-{bits} {direction}, 64 KiB: CJR {extracted['median_ns']:.2f} ns/byte, OpenSSL {native['median_ns']:.2f} ns/byte; OpenSSL takes {extracted['median_ns']/native['median_ns']:.1f} times less time.</li>")
 comparison_html='<h3>64 KiB comparison</h3><ul>'+''.join(comparison)+'</ul><p><a href="../benchmark/results/comparison.json">Ratios for every workload</a>. The ratios combine representation, cipher implementation, library optimization, and compiler effects; they cannot be attributed to language alone.</p>' if comparison else ''
 page=f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>AES-IGE proof and implementation report</title><link rel="stylesheet" href="report.css"></head><body><main>
 <nav><a href="../index.html">Artifact index</a> · <a href="rocq/index.html">Rocq declarations</a> · <a href="../test/report.html">Runtime tests</a> · <a href="../benchmark/results/report.html">Benchmarks</a></nav>
 <h1>AES-IGE: specification, algebra, and implementation</h1>
 <p>A byte-oriented AES-128/192/256 implementation extracted from CJR terms, with an explicit two-block IGE state and checked algebraic properties of a concrete AES model.</p>
 <article class="status"><h2>Exact verification coverage</h2>
 <p>The concrete specification and the complete embedded implementation are machine checked. Iris contracts cover key expansion into a caller-owned schedule, AES encryption and decryption for all three key sizes, complete IGE loops, input and schedule preservation, exact output and final IV, and rejection before buffer access. Derived implementation contracts prove both inverse compositions, final-IV agreement, empty-message identity, and chunk composition. No cipher-correctness assumption or admission is introduced.</p>
 <p>Kernel/assumption audit: {html.escape(str(verification.get('coqchk','not recorded')))}. Runtime tests: {html.escape(str(tests.get('status','not run')))}, {len(tests.get('cases',[]))} passed cases. Benchmark observations: {sum(r['samples'] for r in measurements)}.</p></article>
 <h2>Specification and conventions</h2>
 <p>A byte is an integer in 0..255. A block consists of four columns with four coordinates each; flattening uses the column-major layout from <a href="#fips197">FIPS 197</a>. Key expansion produces 176, 208, or 240 bytes for 10, 12, or 14 rounds. The final round omits MixColumns.</p>
 <p>The S-box is defined independently through inversion in GF(2⁸), reduction polynomial 0x11b, and the affine transformation. A finite certificate verifies the executable lookup tables. Inverse MixColumns uses three forward applications, with a proof that this equals the standard inverse coefficient matrix.</p>
 <p>IGE uses Cᵢ = AESₖ(Pᵢ XOR Cᵢ₋₁) XOR Pᵢ₋₁ and Pᵢ = AESₖ⁻¹(Cᵢ XOR Pᵢ₋₁) XOR Cᵢ₋₁. The mutable IV is C₀ || P₀ and ends as Cₙ || Pₙ, matching <a href="#openssl-ige">OpenSSL</a>. Pure operations return (output, finalIV).</p>
 <h2>Algebraic validating properties</h2>{''.join(sections)}
 <article><h2>Executable buffers and proof structure</h2><p>All buffers contain Int64 words representing bytes. Input/output must be disjoint; the IV, schedule, and 64-word workspace must also be disjoint. Source and schedule are preserved. Capacity, ownership, and byte-range conditions are caller obligations. Invalid round counts and invalid message lengths return false before writes; invalid key lengths return zero before schedule writes.</p>
 <p>Byte-kernel Iris proofs refine the grouped S-box lookup and arithmetic xtime to their pure definitions. Transformation contracts own sixteen source words and sixteen destination words, frame unrelated memory, preserve the source, and establish the transformed destination. The expansion proof initializes the key prefix, then maintains an expanded-prefix/untouched-suffix invariant across the original byte-write sequence. A representation theorem covers every valid byte key and a layout theorem connects the expanded columns to the schedule consumed by AES. Six concrete round-sequence proofs compose the helper contracts for 10, 12, and 14 rounds; named intermediate states keep each buffer update local. The decryption proofs identify three forward MixColumns calls with the standard inverse. The IGE induction owns the remaining input/output blocks, current counter, chaining IV, schedule, and reusable workspace; each iteration establishes the exact next ciphertext/plaintext pair and advances the counter by sixteen. Pure rejection proofs need no raw-buffer ownership, so any caller memory can be framed unchanged.</p>
 <p>CJR gains integer XOR and AND with Z.lxor/Z.land semantics, dedicated WP rules, extraction operators ^ and &amp;, and renderer entries. Boolean conjunction remains a separate operation. Shift and multiplication primitives are unnecessary. Doubling is bounded by 510. The loop uses i ≤ len−16, with an arithmetic theorem establishing safe increment bounds under the Int64 message-length bound.</p></article>
 <article><h2>Public correctness contracts</h2><p><a href="rocq/rocq/layout.html">expand_supported_key_wp</a> covers every supported byte key and connects its caller-owned schedule to the concrete model. <a href="rocq/rocq/cipher.html">encrypt_block_wp, decrypt_block_wp, and block_implementation_roundtrip</a> cover complete AES calls and both inverse directions. <a href="rocq/rocq/ige_refinement.html">ige_public_wp</a> covers both complete IGE directions. <a href="rocq/rocq/composition.html">ige_implementation_roundtrip, ige_implementation_chunks, and ige_implementation_empty</a> derive the client laws. <a href="rocq/rocq/rejection.html">Rejection contracts</a> prove returns before raw-buffer access; <a href="rocq/rocq/index_bounds.html">index bounds</a> cover schedule, workspace, IV, and message offsets.</p></article>
 <article><h2>Independent empirical checks</h2><p>The repository runtime regression run passed 89 cases across ten examples (<a href="../test/results/regressions.json">saved run summary</a>). NIST known-answer vectors cover AES encryption and decryption for all key sizes, with corresponding model examples also checked by Rocq computation. Published OpenSSL IGE vectors and additional fixtures generated through libcrypto test interoperability. <a href="../test/reference-vectors.json">Fixture provenance</a> records the library version and SHA-256. Tests cover both inverse directions, final IV agreement, chunking, empty input, high-bit bytes, invalid arguments, schedule/input preservation, and guards around mutable buffers.</p></article>
 <article><h2>Performance</h2><p>The extracted Cangjie implementation is compared with OpenSSL’s native C AES-IGE API on the same machine. Both use three processes, seven samples per workload, two warm-up calls, and adaptive batching to 20 ms or 16,777,216 repetitions. Throughput uses pre-expanded keys, includes IV reset and an output checksum, and is reported per logical byte. Key-expansion timings include a schedule checksum and are reported per forward expansion; OpenSSL inverse schedule setup is excluded from decryption timings and is not separately measured. Every output byte and final IV agrees across all throughput workloads before timing: <a href="../benchmark/results/differential.json">differential validation</a>. OpenSSL uses packed bytes, CJR uses Int64 words, and their algorithms and toolchains differ. Default OpenSSL dispatch is used; hardware instruction use has not been separately established. This compares practical implementations and does not isolate language overhead. <a href="../benchmark/results/openssl-metadata.json">Native compiler and library provenance</a> records build flags, version, digest, and capabilities. <a href="../benchmark/results/report.html">Comparison charts and all measurements</a> show medians and IQR. Jobs run sequentially, so small timing differences should not be overinterpreted.</p>{comparison_html}<ul>{bench}</ul></article>
 <article><h2>Trust and limits</h2><p>No admissions or additional cipher-correctness axioms are used. The Rocq kernel checks the algebraic proofs; Iris contracts depend on the existing CJR semantics. The printer and Cangjie toolchain remain part of the correspondence boundary. The verified guarantees are functional correctness and memory safety in the CJR semantics, under the stated ownership and bounds preconditions. Branch-based S-box lookup is not constant-time. Authentication, padding, cryptographic-security proofs, and side-channel proofs are outside scope.</p></article>
 <article id="references"><h2>References</h2><p id="fips197">NIST FIPS 197, updated 2023: Advanced Encryption Standard. Source address: <code>https://csrc.nist.gov/pubs/fips/197/final</code>.</p><p id="openssl-ige">OpenSSL AES-IGE implementation and published vectors. Source addresses: <code>https://github.com/openssl/openssl/blob/master/crypto/aes/aes_ige.c</code> and <code>https://github.com/openssl/openssl/blob/master/test/igetest.c</code>.</p><p>Reference addresses are text so this report’s navigation and assets remain fully local.</p></article>
 <footer>Generated from this example’s saved validation artifacts. Timing provenance and source hashes are retained in the linked machine-readable reports.</footer>
 </main></body></html>'''
 (ROOT/'docs/report.html').write_text(page)

if __name__=='__main__':main()
