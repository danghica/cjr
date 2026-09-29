@Test
class QsortArrayTests {
    @TestCase
    func oneElement(): Unit {
        let a = make(1)
        set(a, 0, 7)
        sort(a)
        @Expect(length(a), 1)
        @Expect(get(a, 0), 7)
    }

    @TestCase
    func alreadySorted(): Unit {
        let a = make(4)
        set(a, 0, 1)
        set(a, 1, 2)
        set(a, 2, 3)
        set(a, 3, 4)
        sort(a)
        @Expect(length(a), 4)
        @Expect(get(a, 0), 1)
        @Expect(get(a, 1), 2)
        @Expect(get(a, 2), 3)
        @Expect(get(a, 3), 4)
    }

    @TestCase
    func reversed(): Unit {
        let a = make(4)
        set(a, 0, 4)
        set(a, 1, 3)
        set(a, 2, 2)
        set(a, 3, 1)
        sort(a)
        @Expect(get(a, 0), 1)
        @Expect(get(a, 1), 2)
        @Expect(get(a, 2), 3)
        @Expect(get(a, 3), 4)
    }

    @TestCase
    func duplicates(): Unit {
        let a = make(4)
        set(a, 0, 2)
        set(a, 1, 2)
        set(a, 2, 1)
        set(a, 3, 2)
        sort(a)
        @Expect(get(a, 0), 1)
        @Expect(get(a, 1), 2)
        @Expect(get(a, 2), 2)
        @Expect(get(a, 3), 2)
    }

    @TestCase
    func mixed(): Unit {
        let a = make(5)
        set(a, 0, 3)
        set(a, 1, 1)
        set(a, 2, 4)
        set(a, 3, 1)
        set(a, 4, 5)
        sort(a)
        @Expect(get(a, 0), 1)
        @Expect(get(a, 1), 1)
        @Expect(get(a, 2), 3)
        @Expect(get(a, 3), 4)
        @Expect(get(a, 4), 5)
    }
}
