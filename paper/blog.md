# A checked fragment of Cangjie

This repository, [cjr](https://github.com/danghica/cjr), defines a small fragment of the Cangjie programming language and proves specifications of programs written in that fragment. The fragment is called CJR, for Cangjie Radical. The definitions and proofs are checked by Coq 8.20.1 with the Iris library 4.4.0 and std++ 1.12.0. The same proof assistant is now released under the name the Rocq Prover. This text says what the fragment contains, what the proofs establish, and how the proved programs are printed back as Cangjie source.

The reader assumed here can read an operational semantics and a data-structure invariant, and has not used a proof assistant or separation logic. Those tools are described by the operations they perform in this repository.

The longer account, with each Coq definition followed by the same statement in mathematical notation, is `paper/cjr-tutorial.tex`. The command `make cj` rebuilds `paper/cjr-tutorial.pdf` from that file and from the generated Cangjie listings.

## The fragment

Cangjie has functions, immutable and mutable locals, structs, classes, and a raw pointer type `CPointer`. The version 1.0 language documentation is the surface syntax this work starts from. CJR keeps a subset of that syntax and gives the subset a small-step semantics and a program logic.

The subset is sequential and monomorphic. It has `func`, `let`, `var`, `if`, `while`, unboxed structs, classes that cannot be extended, and word-addressed blocks allocated with `malloc` and released with `free`. It has code pointers, so a method table can be an ordinary struct that holds functions. It has no generics, no inheritance, no `enum` or `match`, no concurrency, and no garbage collector. A larger Cangjie program would have to be translated into this subset before these proofs would apply. That translation is not defined. The requirement recorded for any future translation is that it preserve the time and space cost of the constructs this fragment represents directly: unboxed structs, raw blocks, and final classes.

`let x = v` followed by `e` substitutes `v` for `x` in `e`. The binding cannot be updated. `var x = v` followed by `e` allocates a stack slot, stores `v`, and runs `e` with `x` rewritten to that slot. Assignment updates the slot. When the body has reduced to a value, the slot is deleted.

Application in the core takes one argument. A Cangjie function of several parameters is a function of one struct, and the components of the struct are the parameters. Field names are positions. The first field of a struct or a class is index 0.

The syntax in `theories/lang.v` is an inductive definition, one constructor per form. Four constructors, `Pop`, `StackLoad`, `StackAssign`, and `StackFieldStore`, have no Cangjie spelling. They appear only after a `var` has been assigned a stack slot. The tutorial tabulates the rest of the correspondence. Integer arithmetic is addition, subtraction, comparison, and equality. There is no shift and no division. Boolean conjunction is present. Floating-point literals are in the grammar, and no floating-point operator is.

## The machine

A state has five components. A stack map holds `var` slots and the structs stored in them. A raw map holds the words of `CPointer` blocks. A block map records the length of each live block. An object map sends a pair of an object identifier and a field index to a value. An integer counter supplies the next fresh address for all three regions. The initial state has four empty maps and counter 0.

Allocation reads the counter, writes the new cells, and advances it. A one-word block and a class object each advance it by one. Object fields are stored under the pair (object, index), so they do not occupy consecutive raw addresses. Adding an index `i` to a pointer at `ℓ` yields the pointer at `ℓ + i`. There is no byte offset and no padding. A block of length `n` at base `ℓ` occupies `ℓ` through `ℓ + n - 1`.

A state is well formed when every live address is below the counter, every recorded block is fully present, and distinct blocks are disjoint. The initial state is well formed, and the memory steps used by the logic preserve that property. The address equal to the counter is absent from all four maps.

Head reduction is deterministic, with an empty observation type and no new threads. The only fresh address is the counter. Steps at the root are placed in an evaluation context with one hole. Arguments run left to right. `if` evaluates the condition only. `while e1 do e2` becomes `if e1 then (e2; while e1 do e2) else ()`, and the two copies of the loop are syntax.

A configuration that is not a value, and to which no rule applies, is stuck. Null, an out-of-bounds address, a freed address, and a non-pointer all fail the lookup a load or store requires. There is no error value and no exception. A type grammar is defined, covering integers, floats, booleans, unit, structs, pointers, objects, and functions. The semantics does not consult it. Safety here means a proved specification, from which adequacy concludes that execution from the empty machine does not get stuck.

## Coq, and the name Rocq

Coq is a proof assistant. The user writes definitions, statements, and proofs in a text file. Coq accepts the file when every proof follows from the definitions by the rules of its logic, and it rejects the file when a step does not. The check is mechanical. A reader who trusts the checker can read the definitions and the theorem statements without replaying each proof.

The specification language has dependent types. A type may contain a value. The statement of a theorem is written as a type, and a proof is a term of that type. Checking the proof is type-checking the term. Commands called tactics construct the term: they apply lemmas, rewrite equalities, and split cases, under the user's direction. When the proof is closed, Coq submits the constructed term to a kernel that type-checks it. The kernel does not run the tactic script. If the kernel implements the type system correctly, an error in a tactic cannot make an invalid proof accepted. A proof assistant with a small trusted checker and a larger untrusted procedure that proposes proofs meets the de Bruijn criterion. That is the arrangement Coq uses.

Data are inductive definitions. An inductive definition lists its constructors. An algebraic data type lists the same kind of constructors. The grammars of expressions and of values are inductive. A recursive function on expressions is accepted when every recursive call is on a subexpression. A proof proceeds by cases on the constructors, and by induction when the statement is recursive. The determinism proof inverts both step derivations. Where a rule reads a map, both derivations perform the same lookup and obtain the same result.

A `.v` file is source. Coq writes a `.vo` file after checking it. `coq_makefile` builds a `Makefile` from `_CoqProject`, and `make` checks every listed file. std++ provides finite maps, list lemmas, and a tactic for boolean goals. Iris provides the program logic.

The system is now released as the Rocq Prover. Rocq 9 continues Coq and is the first series under that name. These sources were checked with Coq 8.20.1, which the tutorial cites. Coq can also translate some of its functions to OCaml, Haskell, or Scheme, a process called extraction. The Cangjie files here are not extracted. A separate Coq function maps each expression to a string, and the build rejects output that contains the marker used for forms the examples do not use.

## Separation logic

A Hoare triple `{P} c {Q}` says that if assertion `P` is true before command `c`, and `c` terminates, then `Q` is true afterwards. When the language has a heap, `P` and `Q` describe the heap. A specification of a small command that mentions the whole heap also mentions cells the command does not use. Combining two such specifications requires a separate argument that the commands touch disjoint cells.

Separation logic, introduced for this purpose by John C. Reynolds and developed with Peter W. O'Hearn and Hongseok Yang, reads an assertion as ownership of part of the heap. The separating conjunction `P ∗ Q` holds when the heap splits into two disjoint parts, one satisfying `P` and one satisfying `Q`. The points-to assertion `ℓ ↦ v` holds of the heap that consists of the single cell `ℓ` containing `v`. The two parts of a separating conjunction are disjoint, so `ℓ ↦ v ∗ ℓ ↦ w` holds of no heap. Full ownership of one cell cannot be stated twice.

The frame rule is the reason for this reading. From a proof of `{P} c {Q}` and a separate assertion `R`, the rule concludes `{P ∗ R} c {Q ∗ R}`. The specification of `c` names the cells `c` uses. Cells named only in `R` are not given to that proof, and they are still owned afterwards. O'Hearn, Reynolds, and Yang call this local reasoning. In this repository the frame rule is the one supplied by Iris. It is not proved again by induction over CJR expressions.

CJR has one points-to assertion per map: a stack slot, a raw word, a block length, and an object field. The identifier types differ, so a stack lemma cannot be applied to a raw pointer. The word and the length are separate, so a proof may load a word and still own the right to free the block. The indexed-block example does the load and does not free.

Ownership here is the full fraction 1. From `ℓ1 ↦ v1 ∗ ℓ2 ↦ v2`, swap ends in `ℓ1 ↦ v2 ∗ ℓ2 ↦ v1`. The assertion `ℓ ↦ v1 ∗ ℓ ↦ v2` is a contradiction, so that specification cannot be used twice at one address.

Iris assertions are affine: `P ∗ Q` implies `P`. Ownership may be discarded, and it cannot be invented. When a theorem stops mentioning an allocated object or block, the machine still holds that storage and the proof no longer names it. The list equation that conses and then takes the tail discards the new cell. Array-list growth likewise leaves the old buffer allocated. The source library would collect it. This language has a one-word `free` and no collector, so the proof discards the old facts.

## Iris

Iris is a separation logic implemented in Coq for higher-order programs and for concurrency. Jung, Swasey, Sieczkowski, Svendsen, Turon, Birkedal, and Dreyer, in 2015, introduce the algebra ghost state is built from. Krebbers, Jung, Bizjak, Jourdan, Dreyer, and Birkedal, in 2017, present weakest preconditions, evaluation contexts, and the lifting of one deterministic head step. *Iris from the ground up* includes adequacy. A further paper describes the Proof Mode tactics used in this repository. CJR is registered as an evaluation-context language through the same interface HeapLang uses. HeapLang is the example language shipped with Iris 4.4.0.

The concurrency layer is unused. There is no `fork` and no rule for an invariant shared by several threads. The parts in use are the weakest precondition, the frame rule, the bind rule, and ghost maps.

A ghost map has an authoritative copy and fragments. The state interpretation owns one authoritative map for each concrete map, plus the fact that the state is well formed. A points-to fact is a fragment. Iris holds the state interpretation at every step. A load is allowed when the fragment agrees with the authoritative map, and the step updates both. A load of an address with no fragment has no proof.

`wp e {Φ}` means that, for every well-formed extension of the current ownership, `e` does not get stuck and does not fork, and if it returns `v` then `Φ(v)` holds. This is partial correctness: a loop that does not terminate satisfies a postcondition that is never demanded. The rules also carry a later modality and a step credit, which count steps so recursive reasoning stays well founded. The example proofs discard those hypotheses after the step. The memory content of a load is the points-to fact: ownership of the cell is enough, and the same ownership is returned with the stored value.

The bind rule handles contexts. A proof of `wp (K[e]) {Φ}`, for a context `K`, follows from a proof of `wp e {v. wp (K[v]) {Φ}}`. Choosing `K` chooses which subexpression is evaluated. The rule does not mention memory. The consequence rule weakens a postcondition: from `wp e {Φ}` and a proof that every `Φ(v)` implies `Ψ(v)`, one obtains `wp e {Ψ}`. The examples use it when a lemma returns both a numeric result and a framed cell, and the next command needs only one of them.

The proofs are interactive. `iIntros` introduces a hypothesis. `iApply` uses a lemma. `iDestruct` splits a separating conjunction or opens an existential quantifier. `iFrame` sends a hypothesis to the part of the goal that asks for the same assertion. What remains is ordinary reasoning about integers, lists, and equalities, using std++ or computation.

## From a proof back to execution

Adequacy, in `theories/adequacy.v`, connects a weakest-precondition proof to execution. If for every allocation of the ghost state one can prove `wp e {v. φ(v)}`, with `φ` free of ownership, then from the initial state every reachable configuration can step or is a value, and every final value satisfies `φ`. The proof allocates four empty ghost maps, notes that the initial state is well formed, and applies Iris's general adequacy theorem.

The hypothesis has to be proved. A free variable, a null load, or a load of an unallocated address has no such proof. Adequacy also returns only `φ`. A postcondition that says the result is unit yields a theorem that the program returns unit and does not get stuck. Memory facts used along the way are not part of `φ`.

Five closed programs are instantiated at this theorem: the arithmetic loop, the stack update beside an untouched raw cell, the allocate-write-read-free cell, the class-field update beside an untouched raw cell, and the hand-assembled method table. The other examples assume points-to facts for cells that already exist. They are stated as weakest preconditions, and a caller that owns those cells frames them in.

## Programs and the facts they establish

The files in `theories/examples/` add one feature at a time. Each Coq definition is the core term, and the tutorial's Cangjie is printed from that term.

`sum_one` binds `n` to 1 and `s` to 0, loops while `1 <= n`, and returns `s`. The body runs once and the result is 1. Nothing is allocated on the raw heap or the object heap. `struct_upd.v` updates a struct field in a stack slot. A second program allocates one raw word, runs that update, and reads the word back as 0, because the raw points-to fact is framed across a stack operation. `cell.v` allocates a word, stores 7, loads 7, and frees it. The postcondition has no points-to fact, so a further load is not provable.

`sum_block.v` sums a one-word block containing 4. The address is the base plus the index. The only iteration has index 0, so the load uses the fact at the base, and the result is 4. A load of the next word has no points-to fact. `class_upd.v` stores 5 in an object field and returns a raw word allocated earlier, still 0. `frame_call.v` applies a closure that stores 9 through one pointer, then loads a second pointer that held 3. The callee receives only the first fact. `vtable.v` stores a closure in a struct, applies the closure to a fresh object, and reads field 0, which is 1. The machine has no method table. A method here is a function of the object, and the table is a struct the program built.

## Lists, arrays, and array lists

`list.v` is a singly linked list of integers. Equality compares integers only, so a program cannot branch on null, and a load through null is stuck. The empty list is an object with a false boolean in field 0, the integer 0 in field 1, and a pointer to that same object in field 2. The allocation writes unit into the third field and then overwrites it with the new object before returning. A cons cell stores true, the head, and the object for the rest. `empty` does not read the tail when the tag is false. Objects are never deleted. The printed class stores the tail as an optional raw field, because a Cangjie constructor cannot receive the object it is building, and reads it back as a `Node`.

`isList(xs, p)` recurses on the mathematical list and owns the fields of `p` together with, in the cons case, a separate `isList` fact for the tail. `nil` and `cons` allocate. `head`, `tail`, and `empty` read and return the same predicate. The equation `tail` after `cons` returns the original pointer, which still represents the original list. The new cell's fields are discarded. `head` after `cons` returns the inserted integer. Append is not proved. `list_rev.v` now proves iterative in-place reversal: its invariant owns separate accumulator and remaining lists and states `rev u ++ v = xs`. Each iteration opens a cons cell, saves its tail, rewires field 2, and transfers that same cell to the accumulator. The loop theorem establishes an empty remainder and the reversed contents. `reverse_twice_spec` composes two calls and proves restoration of the original sequence. One fresh empty sentinel per call makes the two owned chains separate; the theorem does not restore sentinel identity. The tutorial explains every definition and proof in a separate subsection, with the complete checked scripts.

`array.v` is a final object plus a raw block: field 0 is the length, field 1 is the base pointer, and word `i` is element `i`. The index is a computed integer, so the elements cannot be object fields, whose indices are static. `Alloc` of zero words is stuck, so `make` requires a positive length and fills the block with zeros. The representation is a separating conjunction of one points-to fact per element. A write at `i` replaces that fact and leaves the others, so a read of a different index returns the old value. The proved equations are: a fresh array has the requested length and contains zeros; writing `x` at `i` and reading `i` returns `x`; that write leaves every other in-range index unchanged. An out-of-range index is the stuck load of a non-pointer. A loop over every cell is not proved. The indexed conjunction is the hypothesis that loop would use.

`array_list.v` is the resizable `Int64` buffer from Cangjie's `ArrayList`: construction at capacity 16, length, capacity, version, emptiness, get, set, append, removal, and growth. The iterator, collection interface, ranges, higher-order methods, and sort are omitted. The outer object stores the buffer, the live length, and the version. The buffer is the array above, holding the list followed by zeros out to the capacity. `set` leaves the version unchanged. `add` and `remove` add one. Growth replaces the buffer, leaves the version unchanged, and doubles by adding the capacity to itself, because there is no shift. The old block stays allocated and is absent from the postcondition.

One copy loop serves both growth and removal. Between two non-overlapping blocks it copies a prefix and leaves the source unchanged. Inside one block it shifts the suffix down by one, reading each word before the next store overwrites it. Removal of the last element is the loop test failing immediately. Append grows only when the length already equals the capacity, in which case the capacity doubles; otherwise it overwrites the first zero. It then writes the new element at the old length and increases the length and the version. Removal loads the element, shifts, writes zero at the old last index, decreases the length, increases the version, and returns the element.

Client theorems compose these calls with `let` and framing. A fresh list has size 0, capacity 16, and version 0, and it is empty. After append the size is one larger, the new index holds the new element, older indexes are unchanged, the capacity doubles only when the buffer was full, and the version increases by one. After `set` the written index holds the new value, other indexes and the version stay put, and the length is unchanged. Append then removal of the new last index returns that element and restores the list, with the capacity that append left behind and with the version increased by two. List equality and `filter` are not proved.

## The printed programs, and their size

Each `.v` file holds the expression, the specification, and the proof. The Cangjie a reader compares with a library is a rendering of the expression alone. `theories/examples/cj_print.v` defines that rendering. It imports the language and Coq's string library. Class and field names are arguments, so one file can print an array as `len` and `data`, an array list as `myData`, `mySize`, and `myVersion`, and a list node as `isCons`, `value`, and `next`.

The printer inverts the tutorial's table: `let`, `var`, `while`, `malloc` of eight bytes times the word count followed by a `CPointer<Int64>` cast, `unsafe` read, write, and `+`, and constructor calls for `New`. The receiver is omitted from the parameter list. A body structurally equal to a known method prints as a call, so `add` calls `grow`. The copy loop prints as its `while`. The out-of-range arm prints as `unsafe { CPointer<Int64>().read() }`, a stuck null read. An administrative stack form prints a marker containing `unsupported`, and the build rejects any file that contains it. None of the fifteen generated files does.

`theories/examples/emit_cj.v` builds one string per example. The `cj` target in `Makefile.local-late` compiles that file, evaluates the strings, writes `generated/cj/`, writes `generated/cj/further.tex` for any generated file the tutorial does not yet name, and runs `pdflatex` twice. The tutorial includes those files with `\lstinputlisting`. The Coq listings of the core terms remain. Each generated file declares `malloc` and `free`, the types and functions, and a `main` that runs a closed program or calls a library's operations. The array-list factory is named `initArrayList`, leaving `init` for constructors. The parameter called `this` in the method-table term is printed as `self`. No Cangjie compiler is run.

The counts below are `wc -l` of the whole file. A `.v` file includes the program, the specification, the proofs, and blank lines.

| Spec | Lines | Extracted | Lines | Spec / extracted |
|---|---:|---|---:|---:|
| `theories/examples/arith.v` | 78 | `generated/cj/arith.cj` | 18 | 4.3 |
| `theories/examples/struct_upd.v` | 57 | `generated/cj/struct_upd.cj` | 27 | 2.1 |
| `theories/examples/cell.v` | 35 | `generated/cj/cell.cj` | 15 | 2.3 |
| `theories/examples/swap.v` | 40 | `generated/cj/swap.cj` | 18 | 2.2 |
| `theories/examples/sum_block.v` | 90 | `generated/cj/sum_block.cj` | 20 | 4.5 |
| `theories/examples/class_upd.v` | 45 | `generated/cj/class_upd.cj` | 23 | 2.0 |
| `theories/examples/frame_call.v` | 37 | `generated/cj/frame_call.cj` | 20 | 1.9 |
| `theories/examples/vtable.v` | 70 | `generated/cj/vtable.cj` | 33 | 2.1 |
| `theories/examples/list.v` | 227 | `generated/cj/list.cj` | 54 | 4.2 |
| `theories/examples/list_rev.v` | 287 | `generated/cj/list_rev.cj` | 65 | 4.4 |
| `theories/examples/array.v` | 354 | `generated/cj/array.cj` | 39 | 9.1 |
| `theories/examples/array_list.v` | 2416 | `generated/cj/array_list.cj` | 153 | 15.8 |
| `theories/examples/qsort.v` | 1749 | `generated/cj/qsort_array.cj` (76), `generated/cj/qsort_array_list.cj` (153) | 229 | 7.6 |
| `theories/examples/hash_map.v` | 2398 | `generated/cj/hash_map.cj` | 375 | 6.4 |
| **Total** | **7883** | | **1089** | **7.2** |

Ratios near 2 are proofs of about one lemma per instruction: the cell, the swap, the field update, and the framed call. Loops are longer relative to the printed `while` because they need invariants. The data-structure examples add representation predicates and equations. `array_list.v` is 2416 of the 7883 specification lines; its generated program has 153 lines. `list_rev.v` has 287 lines for the program, algebra, representation helpers, iteration and loop proofs, and client theorems, compared with 65 generated lines. Quicksort is counted once in the specifications and printed twice. Across the fifteen generated files the specifications are 7.2 times as long as the printed Cangjie.

## What is omitted, and where to read

Concurrency is absent, so there is no shared invariant and no fork. Objects are not collected. The named free rule is the one-word rule, while the array library uses allocation of a positive word count. Pointer arithmetic is by words. Null, a freed address, and an address with no points-to fact are stuck. Types are not enforced. Adequacy applies to the programs whose specifications have been proved.

The tutorial's bibliography is the set of sources used here: the Cangjie 1.0 documentation; Reynolds's 2002 paper and the 2001 paper of O'Hearn, Reynolds, and Yang; the Iris papers named above, the Iris lecture notes, and the Iris 4.4.0 development; and the manuals for Coq 8.20.1 and std++ 1.12.0. In the repository, `theories/lang.v` is the syntax and the machine, `theories/primitive_laws.v` is the points-to facts and the rules, `theories/adequacy.v` is the link to execution, and `theories/examples/` holds the programs. The generated Cangjie is in `generated/cj/`.
