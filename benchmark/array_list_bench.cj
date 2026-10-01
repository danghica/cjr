import std.collection.ArrayList as StdArrayList

@Test
class ArrayListBenchmark {
    @TestCase
    func compare(): Unit {
        for (n in [256, 4096, 16384]) {
            let expected = n * (n - 1) / 2
            let ca = initArrayList()
            let sa = StdArrayList<Int64>()
            var j: Int64 = 0
            while (j < n) { ca.add(j); sa.add(j); j += 1 }
            benchPair("arraylist_read", n, n, 65536, expected,
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += ca.get((i * 17) % n); i += 1 }; sum },
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += sa[(i * 17) % n]; i += 1 }; sum })
            benchPair("arraylist_build_scan", n, n, 262144 / n, expected,
                { => let a = initArrayList(); var i: Int64 = 0
                    while (i < n) { a.add(i); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += a.get(i); i += 1 }; sum },
                { => let a = StdArrayList<Int64>(); var i: Int64 = 0
                    while (i < n) { a.add(i); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += a[i]; i += 1 }; sum })
        }
        for (n in [256, 1024, 4096]) {
            let ca = initArrayList()
            let sa = StdArrayList<Int64>()
            var j: Int64 = 0
            while (j < n) { ca.add(j); sa.add(j); j += 1 }
            // n remove-first / append pairs restore the entire original sequence.
            benchPair("arraylist_rotate", n, n, 65536, n * (n - 1) / 2,
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { let v = ca.remove(0); ca.add(v); sum += v; i += 1 }; sum },
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { let v = sa.remove(at: 0); sa.add(v); sum += v; i += 1 }; sum })
            checked(ca.size(), n); checked(sa.size, n)
            j = 0
            while (j < n) { checked(ca.get(j), j); checked(sa[j], j); j += 1 }
        }
    }
}
