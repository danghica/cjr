@Test
class QsortArrayListTests {
    @TestCase
    func emptyIsUntouched(): Unit {
        let a = initArrayList()
        sort(a)
        @Expect(a.size(), 0)
        @Expect(a.capacity(), 16)
        @Expect(a.version(), 0)
    }

    @TestCase
    func oneElement(): Unit {
        let a = initArrayList()
        a.add(7)
        let ver = a.version()
        let cap = a.capacity()
        sort(a)
        @Expect(a.size(), 1)
        @Expect(a.get(0), 7)
        @Expect(a.capacity(), cap)
        @Expect(a.version(), ver)
    }

    @TestCase
    func alreadySorted(): Unit {
        let a = initArrayList()
        a.add(1)
        a.add(2)
        a.add(3)
        a.add(4)
        let ver = a.version()
        let cap = a.capacity()
        sort(a)
        @Expect(a.size(), 4)
        @Expect(a.get(0), 1)
        @Expect(a.get(1), 2)
        @Expect(a.get(2), 3)
        @Expect(a.get(3), 4)
        @Expect(a.capacity(), cap)
        @Expect(a.version(), ver)
    }

    @TestCase
    func reversed(): Unit {
        let a = initArrayList()
        a.add(4)
        a.add(3)
        a.add(2)
        a.add(1)
        let ver = a.version()
        let cap = a.capacity()
        sort(a)
        @Expect(a.get(0), 1)
        @Expect(a.get(1), 2)
        @Expect(a.get(2), 3)
        @Expect(a.get(3), 4)
        @Expect(a.size(), 4)
        @Expect(a.capacity(), cap)
        @Expect(a.version(), ver)
    }

    @TestCase
    func duplicates(): Unit {
        let a = initArrayList()
        a.add(2)
        a.add(2)
        a.add(1)
        a.add(2)
        let ver = a.version()
        let cap = a.capacity()
        sort(a)
        @Expect(a.get(0), 1)
        @Expect(a.get(1), 2)
        @Expect(a.get(2), 2)
        @Expect(a.get(3), 2)
        @Expect(a.size(), 4)
        @Expect(a.capacity(), cap)
        @Expect(a.version(), ver)
    }

    @TestCase
    func mixed(): Unit {
        let a = initArrayList()
        a.add(3)
        a.add(1)
        a.add(4)
        a.add(1)
        a.add(5)
        let ver = a.version()
        let cap = a.capacity()
        sort(a)
        @Expect(a.get(0), 1)
        @Expect(a.get(1), 1)
        @Expect(a.get(2), 3)
        @Expect(a.get(3), 4)
        @Expect(a.get(4), 5)
        @Expect(a.size(), 5)
        @Expect(a.capacity(), cap)
        @Expect(a.version(), ver)
    }
}
