import std.core.Array as StdArray

@Test
class ArrayBenchmark {
    @TestCase
    func compare(): Unit {
        for (n in [256, 4096, 65536]) {
            let ca = make(n)
            let sa = StdArray<Int64>(n, repeat: 0)
            var j: Int64 = 0
            while (j < n) { set(ca, j, j); sa[j] = j; j += 1 }
            benchPair("array_read", n, n, 65536, n * (n - 1) / 2,
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += get(ca, (i * 17) % n); i += 1 }; sum },
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += sa[(i * 17) % n]; i += 1 }; sum })
            benchPair("array_write_read", n, 2 * n, 65536, 3 * n * (n - 1) / 2,
                { => var i: Int64 = 0
                    while (i < n) { set(ca, (i * 17) % n, i * 3); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += get(ca, i); i += 1 }; sum },
                { => var i: Int64 = 0
                    while (i < n) { sa[(i * 17) % n] = i * 3; i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += sa[i]; i += 1 }; sum })
        }
    }
}
