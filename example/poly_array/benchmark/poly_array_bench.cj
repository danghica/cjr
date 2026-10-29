// Same workloads and sizes as example/array/benchmark/array_bench.cj.
// Both arrays are populated before timing. Native managed bounds checks stay on.
func benchArrays(name: String, n: Int64, ops: Int64, expected: Int64,
                 mono: () -> Int64, poly: () -> Int64): Unit {
    checked(mono(), expected); checked(poly(), expected)
    checked(mono(), expected); checked(poly(), expected)
    let mr = calibrate(mono, 65536)
    let pr = calibrate(poly, 65536)
    var t: Int64 = 0
    while (t < 7) {
        if (t % 2 == 0) {
            sample(name, "Mono", n, ops, t, mr, expected, mono)
            sample(name, "Poly", n, ops, t, pr, expected, poly)
        } else {
            sample(name, "Poly", n, ops, t, pr, expected, poly)
            sample(name, "Mono", n, ops, t, mr, expected, mono)
        }
        t += 1
    }
}

@Test
class PolymorphicArrayBenchmark {
    @TestCase
    func compare(): Unit {
        for (n in [256, 4096, 65536]) {
            let ma = make(n)
            let pa = PolyArray<Int64>.make(n, 0)
            var j: Int64 = 0
            while (j < n) { set(ma, j, j); pa.set(j, j); j += 1 }
            benchArrays("array_read", n, n, n * (n - 1) / 2,
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += get(ma, (i * 17) % n); i += 1 }; sum },
                { => var i: Int64 = 0; var sum: Int64 = 0
                    while (i < n) { sum += pa.get((i * 17) % n); i += 1 }; sum })
            benchArrays("array_write_read", n, 2 * n, 3 * n * (n - 1) / 2,
                { => var i: Int64 = 0
                    while (i < n) { set(ma, (i * 17) % n, i * 3); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += get(ma, i); i += 1 }; sum },
                { => var i: Int64 = 0
                    while (i < n) { pa.set((i * 17) % n, i * 3); i += 1 }
                    var sum: Int64 = 0; i = 0
                    while (i < n) { sum += pa.get(i); i += 1 }; sum })
            unsafe { free(CPointer<Unit>(ma.data)) }
        }
    }
}
