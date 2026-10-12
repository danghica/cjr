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
    @TestCase
    func repeatedFrontRemovalAndAppend(): Unit {
        for (n in [1, 2, 17, 65, 256]) {
            let a = initArrayList()
            for (i in 0..n) { a.add(i) }
            let cap = a.capacity()
            for (round in 0..3) {
                for (i in 0..n) {
                    let removed = a.remove(0)
                    @Expect(removed, i)
                    a.add(removed)
                }
                @Expect(a.size(), n)
                @Expect(a.capacity(), cap)
                @Expect(a.version(), n + 2 * n * (round + 1))
                for (i in 0..n) { @Expect(a.get(i), i) }
            }
        }
    }

    @TestCase
    func middleRemovalAfterRepeatedGrowth(): Unit {
        let a = initArrayList()
        for (i in 0..128) { a.add(i) }
        @Expect(a.remove(32), 32)
        @Expect(a.size(), 127)
        @Expect(a.version(), 129)
        for (i in 0..127) {
            @Expect(a.get(i), if (i < 32) { i } else { i + 1 })
        }
        let last = unsafe { (a.myData.data + 127).read() }
        @Expect(last, 0)
        a.add(-9)
        @Expect(a.get(127), -9)
        @Expect(a.version(), 130)
        a.grow(256)
        @Expect(a.capacity(), 256)
        @Expect(a.get(127), -9)
        for (i in 0..127) {
            @Expect(a.get(i), if (i < 32) { i } else { i + 1 })
        }
        @Expect(a.version(), 130)
    }

    @TestCase
    func zeroLengthCopyDuringEmptyGrowth(): Unit {
        let a = initArrayList()
        a.grow(64)
        @Expect(a.capacity(), 64)
        @Expect(a.size(), 0)
        @Expect(a.version(), 0)
        for (i in 0..64) {
            let cell = unsafe { (a.myData.data + i).read() }
            @Expect(cell, 0)
        }
        a.add(7)
        @Expect(a.remove(0), 7)
        @Expect(a.size(), 0)
        @Expect(a.version(), 2)
        let cell = unsafe { a.myData.data.read() }
        @Expect(cell, 0)
    }

}
