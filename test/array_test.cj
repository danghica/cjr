@Test
class ArrayTests {
    @TestCase
    func makeSetsTheLength(): Unit {
        let a = make(4)
        @Expect(length(a), 4)
    }

    @TestCase
    func freshArrayIsZero(): Unit {
        let a = make(4)
        @Expect(get(a, 0), 0)
        @Expect(get(a, 3), 0)
    }

    @TestCase
    func setThenGetSameAndOther(): Unit {
        let a = make(4)
        set(a, 0, 1)
        set(a, 2, 9)
        set(a, 0, 7)
        @Expect(get(a, 0), 7)
        @Expect(get(a, 2), 9)
        @Expect(length(a), 4)
    }
}
