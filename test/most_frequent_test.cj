import std.core.Array as StdArray

@Test
class MostFrequentTests {
    func from(values: StdArray<Int64>): Array {
        // A zero-length view over a positive allocation avoids malloc(0).
        let a = make(if (values.size == 0) { 1 } else { values.size })
        a.len = values.size
        var i: Int64 = 0
        while (i < values.size) {
            set(a, i, values[i])
            i = i + 1
        }
        a
    }

    func expect(values: StdArray<Int64>, want: Option<Int64>): Unit {
        let input = from(values)
        let got = mostFrequent(input)
        for (i in 0..values.size) { @Expect(get(input, i), values[i]) }
        match (want) {
            case Some(x) =>
                @Expect(got.ok, true)
                @Expect(got.value, x)
            case None => @Expect(got.ok, false)
        }
    }

    @TestCase
    func empty(): Unit { expect([], None) }

    @TestCase
    func singleton(): Unit { expect([42], Some(42)) }

    @TestCase
    func allEqual(): Unit { expect([-7, -7, -7, -7], Some(-7)) }

    @TestCase
    func allDistinct(): Unit { expect([9, -2, 4, 0], Some(9)) }

    @TestCase
    func interleavedTieUsesFirstOccurrence(): Unit {
        expect([8, 3, 3, 8], Some(8))
    }

    @TestCase
    func threeWayTieUsesFirstOccurrence(): Unit {
        expect([5, 9, -1, 9, -1, 5], Some(5))
    }

    @TestCase
    func negativeAndBoundaryIntegers(): Unit {
        let minValue: Int64 = -9223372036854775807 - 1
        let maxValue: Int64 = 9223372036854775807
        expect([minValue, maxValue, minValue, 0, maxValue, minValue], Some(minValue))
    }

    @TestCase
    func sortedInput(): Unit {
        expect([-3, -3, -1, 0, 0, 0, 6, 6], Some(0))
    }

    @TestCase
    func reverseSortedInput(): Unit {
        expect([6, 6, 0, 0, 0, -1, -3, -3], Some(0))
    }
    // Deliberately independent O(n^2) reference, visiting candidates in
    // input order. Strict improvement keeps the earliest tied value.
    func reference(values: StdArray<Int64>): Option<Int64> {
        if (values.size == 0) { return None }
        var best = values[0]
        var bestCount: Int64 = 0
        for (x in values) {
            var count: Int64 = 0
            for (y in values) { if (x == y) { count++ } }
            if (count > bestCount) { best = x; bestCount = count }
        }
        Some(best)
    }

    @TestCase
    func exhaustiveSmallArrays(): Unit {
        var configurations: Int64 = 1
        var checked: Int64 = 0
        for (n in 0..8) {
            for (code in 0..configurations) {
                let values = StdArray<Int64>(n, repeat: 0)
                var digits = code
                for (i in 0..n) { values[i] = digits % 3 - 1; digits = digits / 3 }
                expect(values, reference(values))
                checked++
            }
            configurations *= 3
        }
        @Expect(checked, 3280)
    }

    @TestCase
    func pairSortPreservesOriginalRecords(): Unit {
        let original: StdArray<Int64> = [9, -4, 9, 0, -4, 9, 0]
        let values = from(original)
        let indices = make(original.size)
        for (i in 0..original.size) { set(indices, i, i) }
        pairQsort(values, indices, 0, original.size)
        let seen = StdArray<Bool>(original.size, repeat: false)
        for (i in 0..original.size) {
            let index = get(indices, i)
            @Assert(index >= 0 && index < original.size)
            @Expect(seen[index], false)
            seen[index] = true
            @Expect(get(values, i), original[index])
            if (i > 0) {
                let previous = get(values, i - 1)
                let current = get(values, i)
                @Assert(previous < current ||
                    (previous == current && get(indices, i - 1) < index))
            }
        }
        for (present in seen) { @Expect(present, true) }
    }
}
