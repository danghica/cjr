import std.core.Array as StdArray
import std.collection.HashMap as StdHashMap
import std.sort.sort as stdSort
import std.time.*

func stdInput(n: Int64, pattern: Int64): StdArray<Int64> {
    StdArray<Int64>(n, { i =>
        if (pattern == 0) { ((i * 37) % 101) - 50 }
        else if (pattern == 1) { ((i * 48271) % n) - (n / 2) }
        else if (pattern == 2) { i - (n / 2) }
        else if (pattern == 3) { (n - i) - (n / 2) }
        else { (i * 17) % 7 - 3 }
    })
}

func cjrInput(a: StdArray<Int64>): Array {
    let out = make(a.size)
    var i: Int64 = 0
    while (i < a.size) { set(out, i, a[i]); i = i + 1 }
    out
}

func stdSortedMode(a: StdArray<Int64>): Int64Option {
    let n = a.size
    if (n == 0) { return Int64Option(false, 0) }
    let order = StdArray<Int64>(n, { i => i })
    stdSort(order, lessThan: { i: Int64, j: Int64 =>
        if (a[i] < a[j]) { true }
        else if (a[j] < a[i]) { false }
        else { i < j }
    })
    var bestValue = a[order[0]]
    var bestCount: Int64 = 0
    var bestFirst: Int64 = n
    var start: Int64 = 0
    while (start < n) {
        let value = a[order[start]]
        var end = start + 1
        var first = order[start]
        while (end < n && a[order[end]] == value) {
            if (order[end] < first) { first = order[end] }
            end = end + 1
        }
        let count = end - start
        if (bestCount < count || (bestCount == count && first < bestFirst)) {
            bestValue = value
            bestCount = count
            bestFirst = first
        }
        start = end
    }
    Int64Option(true, bestValue)
}

func stdHashMode(a: StdArray<Int64>): Int64Option {
    let n = a.size
    if (n == 0) { return Int64Option(false, 0) }
    let counts = StdHashMap<Int64, Int64>()
    var i: Int64 = 0
    var best: Int64 = 0
    while (i < n) {
        let x = a[i]
        let count = if (counts.contains(x)) { counts.get(x).getOrThrow() + 1 } else { 1 }
        counts.add(x, count)
        if (count > best) { best = count }
        i = i + 1
    }
    i = 0
    while (i < n) {
        let x = a[i]
        if (counts.get(x).getOrThrow() == best) { return Int64Option(true, x) }
        i = i + 1
    }
    Int64Option(false, 0)
}

func sampleMode(label: String, n: Int64, trial: Int64, implementation: String,
                reps: Int64, expected: Int64, work: () -> Int64): Unit {
    let t0 = MonoTime.now()
    var j: Int64 = 0
    var checksum: Int64 = 0
    while (j < reps) { checksum += work(); j += 1 }
    let elapsed = (MonoTime.now() - t0).toNanoseconds()
    if (checksum != expected * reps) { throw Exception("${implementation} checksum") }
    println("BENCH,${label},${n},${trial},${implementation},${elapsed},${reps},${expected}")
}

func runOne(label: String, n: Int64, pattern: Int64): Unit {
    let input = stdInput(n, pattern)
    let cjr = cjrInput(input)
    let cjrWork = { => mostFrequent(cjr).value }
    let sortWork = { => stdSortedMode(input).value }
    let hashWork = { => stdHashMode(input).value }
    let expected = sortWork()
    let emptyStd = StdArray<Int64>()
    let emptyCjr = make(1)
    emptyCjr.len = 0
    if (mostFrequent(emptyCjr).ok || stdSortedMode(emptyStd).ok || stdHashMode(emptyStd).ok) {
        throw Exception("empty input must produce None")
    }
    if (cjrWork() != expected || hashWork() != expected) {
        throw Exception("implementation mismatch: ${label}, n=${n}")
    }
    _ = cjrWork(); _ = cjrWork()
    _ = sortWork(); _ = sortWork()
    _ = hashWork(); _ = hashWork()
    let reps = 262144 / n
    var trial: Int64 = 0
    while (trial < 7) {
        if (trial % 3 == 0) {
            sampleMode(label, n, trial, "CJR", reps, expected, cjrWork)
            sampleMode(label, n, trial, "StdSort", reps, expected, sortWork)
            sampleMode(label, n, trial, "StdHash", reps, expected, hashWork)
        } else if (trial % 3 == 1) {
            sampleMode(label, n, trial, "StdSort", reps, expected, sortWork)
            sampleMode(label, n, trial, "StdHash", reps, expected, hashWork)
            sampleMode(label, n, trial, "CJR", reps, expected, cjrWork)
        } else {
            sampleMode(label, n, trial, "StdHash", reps, expected, hashWork)
            sampleMode(label, n, trial, "CJR", reps, expected, cjrWork)
            sampleMode(label, n, trial, "StdSort", reps, expected, sortWork)
        }
        trial += 1
    }
}

@Test
class MostFrequentBenchmark {
    @TestCase
    func benchmark(): Unit {
        for (n in [256, 4096, 16384]) {
            runOne("dense", n, 0)
            runOne("wide", n, 1)
            runOne("small_domain", n, 4)
            if (n <= 256) {
            runOne("sorted", n, 2)
            runOne("reverse_sorted", n, 3)
            }
        }
    }
}
