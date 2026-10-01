import std.collection.HashMap as StdHashMap

func buildCjr(n: Int64, base: Int64, stride: Int64): HashMap {
    let m = initHashMap()
    var i: Int64 = 0
    while (i < n) { m.add(base + i * stride, i * 3 + 1); i += 1 }
    checked(m.size(), n)
    i = 0
    while (i < n) {
        let r = m.get(base + i * stride)
        if (!r.ok) { throw Exception("missing CJR map key") }
        checked(r.value, i * 3 + 1); i += 1
    }
    return m
}

func buildStd(n: Int64, base: Int64, stride: Int64): StdHashMap<Int64, Int64> {
    let m = StdHashMap<Int64, Int64>()
    var i: Int64 = 0
    while (i < n) { m.add(base + i * stride, i * 3 + 1); i += 1 }
    checked(m.size, n)
    i = 0
    while (i < n) { checked(m.get(base + i * stride).getOrThrow(), i * 3 + 1); i += 1 }
    return m
}

func lookupPair(name: String, n: Int64, base: Int64, stride: Int64): Unit {
    let cm = buildCjr(n, base, stride)
    let sm = buildStd(n, base, stride)
    benchPair(name, n, n, 65536, 3 * n * (n - 1) / 2 + n,
        { => var i: Int64 = 0; var sum: Int64 = 0
            while (i < n) {
                let r = cm.get(base + i * stride)
                if (!r.ok) { throw Exception("missing CJR map key") }
                sum += r.value; i += 1
            }; sum },
        { => var i: Int64 = 0; var sum: Int64 = 0
            while (i < n) { sum += sm.get(base + i * stride).getOrThrow(); i += 1 }; sum })
}

@Test
class HashMapBenchmark {
    @TestCase
    func compare(): Unit {
        for (n in [256, 4096, 16384]) {
            lookupPair("hashmap_hit", n, 0, 1)
            lookupPair("hashmap_wide_key", n, 1000000, 1)
            let cm = buildCjr(n, 0, 1)
            let sm = buildStd(n, 0, 1)
            benchPair("hashmap_miss", n, n, 65536, n,
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { if (!cm.contains(n + i)) { sum += 1 }; i += 1 }; sum },
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { if (!sm.contains(n + i)) { sum += 1 }; i += 1 }; sum })
            benchPair("hashmap_build_scan", n, n, 262144 / n, 3 * n * (n - 1) / 2 + n,
                { => let m = initHashMap(); var i: Int64 = 0
                    while (i < n) { m.add(i, i * 3 + 1); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) {
                        let r = m.get(i)
                        if (!r.ok) { throw Exception("missing CJR map key") }
                        sum += r.value; i += 1
                    }; sum },
                { => let m = StdHashMap<Int64, Int64>(); var i: Int64 = 0
                    while (i < n) { m.add(i, i * 3 + 1); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += m.get(i).getOrThrow(); i += 1 }; sum })
        }
        for (n in [256, 1024, 4096]) {
            // With final CJR capacity 2*n, these keys all start in bucket zero.
            lookupPair("hashmap_collision", n, 0, 2 * n)
        }
    }
}
