@Test
class ArrayListTests {
    @TestCase
    func freshList(): Unit {
        let a = initArrayList()
        @Expect(a.size(), 0)
        @Expect(a.capacity(), 16)
        @Expect(a.version(), 0)
        @Expect(a.isEmpty(), true)
    }

    @TestCase
    func addThenRead(): Unit {
        let a = initArrayList()
        a.add(1)
        @Expect(a.size(), 1)
        @Expect(a.get(0), 1)
        @Expect(a.isEmpty(), false)
        @Expect(a.capacity(), 16)
        @Expect(a.version(), 1)
        a.add(2)
        @Expect(a.size(), 2)
        @Expect(a.get(0), 1)
        @Expect(a.get(1), 2)
        @Expect(a.version(), 2)
    }

    @TestCase
    func setDoesNotChangeVersion(): Unit {
        let a = initArrayList()
        a.add(1)
        a.add(2)
        a.set(0, 9)
        @Expect(a.get(0), 9)
        @Expect(a.get(1), 2)
        @Expect(a.size(), 2)
        @Expect(a.version(), 2)
        @Expect(a.capacity(), 16)
    }

    @TestCase
    func addThenRemoveLast(): Unit {
        let a = initArrayList()
        a.add(4)
        a.add(5)
        let r = a.remove(1)
        @Expect(r, 5)
        @Expect(a.size(), 1)
        @Expect(a.get(0), 4)
        @Expect(a.capacity(), 16)
        @Expect(a.version(), 3)
    }

    @TestCase
    func removeShiftsTheSuffix(): Unit {
        let a = initArrayList()
        a.add(1)
        a.add(2)
        a.add(3)
        let r = a.remove(0)
        @Expect(r, 1)
        @Expect(a.size(), 2)
        @Expect(a.get(0), 2)
        @Expect(a.get(1), 3)
        @Expect(a.version(), 4)
    }

    @TestCase
    func addGrowsWhenFull(): Unit {
        let a = initArrayList()
        var i: Int64 = 0
        while (i < 16) {
            a.add(i + 10)
            i = i + 1
        }
        @Expect(a.size(), 16)
        @Expect(a.capacity(), 16)
        @Expect(a.get(0), 10)
        @Expect(a.get(15), 25)
        a.add(99)
        @Expect(a.size(), 17)
        @Expect(a.capacity(), 32)
        @Expect(a.get(0), 10)
        @Expect(a.get(15), 25)
        @Expect(a.get(16), 99)
        @Expect(a.version(), 17)
    }
}
