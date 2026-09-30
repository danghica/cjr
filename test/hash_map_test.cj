@Test
class HashMapTests {
    @TestCase
    func freshMap(): Unit {
        let m = initHashMap()
        @Expect(m.size(), 0)
        @Expect(m.capacity(), 16)
        @Expect(m.isEmpty(), true)
    }

    @TestCase
    func addThenGet(): Unit {
        let m = initHashMap()
        m.add(1, 10)
        @Expect(m.size(), 1)
        @Expect(m.contains(1), true)
        let r = m.get(1)
        @Expect(r.ok, true)
        @Expect(r.value, 10)
        @Expect(m.isEmpty(), false)
    }

    @TestCase
    func addOverwrite(): Unit {
        let m = initHashMap()
        m.add(2, 20)
        m.add(2, 21)
        @Expect(m.size(), 1)
        @Expect(m.get(2).value, 21)
    }

    @TestCase
    func removeMissing(): Unit {
        let m = initHashMap()
        let r = m.remove(99)
        @Expect(r, 0)
        @Expect(m.size(), 0)
    }

    @TestCase
    func addThenRemove(): Unit {
        let m = initHashMap()
        m.add(3, 30)
        let r = m.remove(3)
        @Expect(r, 30)
        @Expect(m.size(), 0)
        @Expect(m.contains(3), false)
    }
}
