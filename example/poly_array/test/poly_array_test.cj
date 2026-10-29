// Runtime checks complement the uniform Rocq specifications.
public struct ArrayItem<A, B> {
    public let first: A
    public let second: B
    public init(a: A, b: B) { first = a; second = b }
}

@Test
class PolyArrayTests {
    @TestCase
    func integerSeedAndLength(): Unit {
        for (n in [1, 2, 17, 4096]) {
            let a = PolyArray<Int64>.make(n, -7)
            @Expect(a.length(), n)
            var i: Int64 = 0
            while (i < n) { @Expect(a.get(i), -7); i += 1 }
        }
    }

    @TestCase
    func booleanSeedAndUpdate(): Unit {
        let a = PolyArray<Bool>.make(3, false)
        a.set(1, true)
        @Expect(a.get(0), false)
        @Expect(a.get(1), true)
        @Expect(a.get(2), false)
        @Expect(a.length(), 3)
    }

    @TestCase
    func writesPreserveOtherCells(): Unit {
        let a = PolyArray<Int64>.make(17, 0)
        var i: Int64 = 0
        while (i < 17) { a.set(i, i * 3 - 11); i += 1 }
        i = 0
        while (i < 17) { @Expect(a.get(i), i * 3 - 11); i += 1 }
        a.set(0, 99)
        a.set(16, -99)
        @Expect(a.get(0), 99)
        @Expect(a.get(16), -99)
        @Expect(a.get(8), 13)
        @Expect(a.length(), 17)
    }

    @TestCase
    func independentArrays(): Unit {
        let a = PolyArray<Int64>.make(2, 7)
        let b = PolyArray<Int64>.make(2, 7)
        a.set(0, 9)
        @Expect(a.get(0), 9)
        @Expect(b.get(0), 7)
    }

    @TestCase
    func nestedArraysAndReferenceAliasing(): Unit {
        let inner = PolyArray<Bool>.make(2, false)
        let outer = PolyArray<PolyArray<Bool>>.make(2, inner)
        outer.get(0).set(1, true)
        // Repeating a reference repeats the alias, not the referenced object.
        @Expect(outer.get(1).get(1), true)
        let replacement = PolyArray<Bool>.make(2, false)
        outer.set(0, replacement)
        @Expect(outer.get(0).get(1), false)
        @Expect(outer.get(1).get(1), true)
    }

    @TestCase
    func genericStructElements(): Unit {
        let a = PolyArray<ArrayItem<Int64, Bool>>.make(2, ArrayItem<Int64, Bool>(7, true))
        a.set(1, ArrayItem<Int64, Bool>(9, false))
        @Expect(a.get(0).first, 7)
        @Expect(a.get(0).second, true)
        @Expect(a.get(1).first, 9)
        @Expect(a.get(1).second, false)
    }

    @TestCase
    func functionElements(): Unit {
        let a = PolyArray<(Int64) -> Bool>.make(2, { n: Int64 => n > 0 })
        @Expect(a.get(0)(3), true)
        a.set(1, { n: Int64 => n == 0 })
        @Expect(a.get(0)(0), false)
        @Expect(a.get(1)(0), true)
    }

    @TestCase
    func unitElements(): Unit {
        let a = PolyArray<Unit>.make(2, ())
        a.set(1, ())
        a.get(1)
        @Expect(a.length(), 2)
    }
}
