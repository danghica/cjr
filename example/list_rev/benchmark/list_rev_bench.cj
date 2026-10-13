import std.env.*

// Independent native implementation, with the same tagged sentinel convention.
// Both implementations allocate one new sentinel inside every reversal.
class NativeNode {
    var present: Bool
    var value: Int64
    var link: ?NativeNode
    init(present: Bool, value: Int64, link: ?NativeNode) {
        this.present = present
        this.value = value
        this.link = link
    }
}

func nativeNil(): NativeNode { NativeNode(false, 0, None) }

func nativeReverse(root: NativeNode): NativeNode {
    var previous = nativeNil()
    var current = root
    while (current.present) {
        let following = current.link.getOrThrow()
        current.link = previous
        previous = current
        current = following
    }
    previous
}

func checkCjrSequence(root: Node, values: Array<Int64>, backward: Bool): Unit {
    var p = root
    var i: Int64 = 0
    while (i < values.size) {
        if (empty(p)) { throw Exception("CJR list truncated") }
        let j = if (backward) { values.size - 1 - i } else { i }
        checked(head(p), values[j])
        p = tail(p)
        i += 1
    }
    if (!empty(p)) { throw Exception("CJR list too long") }
}

func checkNativeSequence(root: NativeNode, values: Array<Int64>, backward: Bool): Unit {
    var p = root
    var i: Int64 = 0
    while (i < values.size) {
        if (!p.present) { throw Exception("native list truncated") }
        let j = if (backward) { values.size - 1 - i } else { i }
        checked(p.value, values[j])
        p = p.link.getOrThrow()
        i += 1
    }
    if (p.present) { throw Exception("native list too long") }
}

func validate(values: Array<Int64>): Unit {
    var cj = nil()
    var nt = nativeNil()
    var i = values.size
    while (i > 0) {
        i -= 1
        cj = cons(values[i], cj)
        nt = NativeNode(true, values[i], nt)
    }
    cj = reverse(cj); nt = nativeReverse(nt)
    checkCjrSequence(cj, values, true)
    checkNativeSequence(nt, values, true)
    cj = reverse(cj); nt = nativeReverse(nt)
    checkCjrSequence(cj, values, false)
    checkNativeSequence(nt, values, false)
}

@Test
class ReversalBenchmark {
    @TestCase
    func compare(): Unit {
        // Validation is outside every timed region, for both implementations.
        validate([])
        validate([7])
        validate([-2, 0, -2, 9])
        let process: Int64 = if (getVariable("CJR_BENCH_PROCESS").getOrThrow() == "1") { 1 } else { 0 }
        for (n in [256, 4096, 16384]) {
            let values = Array<Int64>(n, { i => i })
            validate(values)
            var cj = nil()
            var nt = nativeNil()
            var i = n
            while (i > 0) {
                i -= 1
                cj = cons(i, cj)
                nt = NativeNode(true, i, nt)
            }
            // Two reversals restore the input orientation. Read endpoints after
            // each reversal so that timed work produces an observable checksum.
            let croot = cj
            let nroot = nt
            let cwork = { =>
                let reversed = reverse(croot)
                let first = head(reversed)
                let restored = reverse(reversed)
                first + head(restored)
            }
            let nwork = { =>
                let reversed = nativeReverse(nroot)
                let first = reversed.value
                let restored = nativeReverse(reversed)
                first + restored.value
            }
            checked(cwork(), n - 1); checked(nwork(), n - 1)
            checked(cwork(), n - 1); checked(nwork(), n - 1)
            let cr = calibrate(cwork, 65536)
            let nr = calibrate(nwork, 65536)
            var t: Int64 = 0
            while (t < 7) {
                // One reported operation is one reversal, including its sentinel.
                if ((t + process) % 2 == 0) {
                    sample("list_reverse", "CJR", n, 2, t, cr, n - 1, cwork)
                    sample("list_reverse", "Native", n, 2, t, nr, n - 1, nwork)
                } else {
                    sample("list_reverse", "Native", n, 2, t, nr, n - 1, nwork)
                    sample("list_reverse", "CJR", n, 2, t, cr, n - 1, cwork)
                }
                t += 1
            }
            checkCjrSequence(cj, values, false)
            checkNativeSequence(nt, values, false)
        }
    }
}
