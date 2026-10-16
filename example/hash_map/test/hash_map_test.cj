@Test
class HashMapTests {
    @TestCase
    func signedRemainder(): Unit {
        // Match the core's truncation-toward-zero semantics in all sign cases.
        let a: Int64 = 7
        let b: Int64 = -7
        let c: Int64 = 3
        let d: Int64 = -3
        @Expect(a % c, 1)
        @Expect(b % c, -1)
        @Expect(a % d, 1)
        @Expect(b % d, -1)
        @Expect(residue(-7, 3), 2)
        @Expect(residue(-6, 3), 0)
        @Expect(residue(7, 3), 1)
    }

    @TestCase
    func extremeKeys(): Unit {
        let lo: Int64 = -9223372036854775807 - 1
        let hi: Int64 = 9223372036854775807
        @Expect(residue(lo, 16), 0)
        @Expect(residue(hi, 16), 15)
        @Expect(residue(lo, 3), 1)
        @Expect(residue(hi, 3), 1)
        let m = initHashMap()
        m.add(lo, 11)
        m.add(hi, 22)
        @Expect(m.get(lo).ok, true)
        @Expect(m.get(lo).value, 11)
        @Expect(m.get(hi).ok, true)
        @Expect(m.get(hi).value, 22)
        @Expect(m.remove(lo), 11)
        @Expect(m.contains(lo), false)
        @Expect(m.get(hi).value, 22)
    }

    @TestCase
    func mixedBucketsAndPrimeCollisions(): Unit {
        @Expect(hashBucket(-9223372036854775807 - 1, 16), 2)
        @Expect(hashBucket(9223372036854775807, 16), 7)
        // These reduced keys produce the largest-magnitude hash products.
        @Expect(hashBucket(2147483646, 16), 8)
        @Expect(hashBucket(-2147483646, 16), 8)
        @Expect(hashBucket(0, 8192) == hashBucket(8192, 8192), false)
        let m = initHashMap()
        // Mixing still permits collisions; original keys distinguish entries.
        for (i in -20..21) { m.add(i * 2147483647, i + 100) }
        for (i in -20..21) { @Expect(m.get(i * 2147483647).value, i + 100) }
        @Expect(m.remove(0), 100)
        @Expect(m.get(2147483647).value, 101)
        @Expect(m.get(-2147483647).value, 99)
    }

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
    @TestCase
    func collisionsAndWraparound(): Unit {
        @Expect(hashBucket(15, 16), 15)
        @Expect(hashBucket(30, 16), 15)
        @Expect(hashBucket(45, 16), 15)
        let m = initHashMap()
        m.add(15, 150)
        m.add(30, 300)
        m.add(45, 450)
        @Expect(m.get(15).value, 150)
        @Expect(m.get(30).value, 300)
        @Expect(m.get(45).value, 450)
        @Expect(m.contains(60), false)
        @Expect(m.size(), 3)
    }

    @TestCase
    func tombstoneDoesNotHideExistingKey(): Unit {
        let m = initHashMap()
        m.add(13, 10)
        m.add(28, 280)
        m.add(43, 430)
        @Expect(m.remove(13), 10)
        @Expect(m.get(43).value, 430)
        m.add(43, 431)
        @Expect(m.size(), 2)
        @Expect(m.get(43).value, 431)
        m.add(58, 580)
        @Expect(m.size(), 3)
        @Expect(m.get(28).value, 280)
        @Expect(m.get(58).value, 580)
    }

    @TestCase
    func negativeKeysAndZeroValues(): Unit {
        let m = initHashMap()
        m.add(-1, 0)
        m.add(-17, -170)
        @Expect(m.contains(-1), true)
        @Expect(m.get(-1).ok, true)
        @Expect(m.get(-1).value, 0)
        @Expect(m.get(-17).value, -170)
        @Expect(m.get(99).ok, false)
        @Expect(m.get(99).value, 0)
        @Expect(m.remove(-1), 0)
        @Expect(m.contains(-1), false)
        @Expect(m.size(), 1)
    }

    @TestCase
    func updateAtLoadLimitDoesNotGrow(): Unit {
        let m = initHashMap()
        for (i in 0..8) { m.add(i, i * 10) }
        @Expect(m.capacity(), 16)
        m.add(7, 777)
        @Expect(m.capacity(), 16)
        @Expect(m.size(), 8)
        @Expect(m.get(7).value, 777)
    }

    @TestCase
    func growthPreservesEveryEntry(): Unit {
        let m = initHashMap()
        for (i in 0..9) { m.add(i * 16 + 15, i * 10) }
        @Expect(m.capacity(), 32)
        @Expect(m.size(), 9)
        for (i in 0..9) {
            @Expect(m.get(i * 16 + 15).ok, true)
            @Expect(m.get(i * 16 + 15).value, i * 10)
        }
    }

    @TestCase
    func repeatedGrowthAndRemoval(): Unit {
        let m = initHashMap()
        for (i in 0..80) { m.add(i * 16, i + 100) }
        @Expect(m.capacity(), 256)
        @Expect(m.size(), 80)
        for (i in 0..80) { @Expect(m.get(i * 16).value, i + 100) }
        for (i in 0..40) { @Expect(m.remove(i * 16), i + 100) }
        @Expect(m.size(), 40)
        @Expect(m.remove(999), 0)
        @Expect(m.size(), 40)
        for (i in 40..80) { @Expect(m.get(i * 16).value, i + 100) }
        for (i in 0..40) { m.add(i * 16, i + 200) }
        @Expect(m.size(), 80)
        for (i in 0..40) { @Expect(m.get(i * 16).value, i + 200) }
    }

    @TestCase
    func explicitGrowthPreservesContents(): Unit {
        let m = initHashMap()
        m.add(15, 15)
        m.add(31, 31)
        m.grow(32)
        @Expect(m.capacity(), 32)
        @Expect(m.size(), 2)
        @Expect(m.get(15).value, 15)
        @Expect(m.get(31).value, 31)
    }

    @TestCase
    func tombstonesAcrossEntireProbeCycle(): Unit {
        let m = initHashMap()
        for (i in 0..16) {
            m.add(i, i + 1)
            @Expect(m.remove(i), i + 1)
        }
        @Expect(m.size(), 0)
        @Expect(m.capacity(), 16)
        @Expect(m.contains(0), false)
        m.add(31, 310)
        @Expect(m.get(31).value, 310)
        @Expect(m.size(), 1)
    }
    @TestCase
    func freshBuffersAreZero(): Unit {
        for (round in 0..32) {
            let a = make(32)
            for (i in 0..32) { @Expect(arrayGet(a, i), 0) }
            for (i in 0..32) { arraySet(a, i, round + i + 1) }
            unsafe { free(CPointer<Unit>(a.data)) }
            let m = initHashMap()
            for (i in 0..16) {
                @Expect(arrayGet(m.tags, i), 0)
                @Expect(arrayGet(m.keys, i), 0)
                @Expect(arrayGet(m.vals, i), 0)
                arraySet(m.tags, i, 1)
                arraySet(m.keys, i, round + i + 1)
                arraySet(m.vals, i, round + i + 1)
            }
            unsafe {
                free(CPointer<Unit>(m.tags.data))
                free(CPointer<Unit>(m.keys.data))
                free(CPointer<Unit>(m.vals.data))
            }
        }
    }

    @TestCase
    func lookupWrapsPastTombstones(): Unit {
        let m = initHashMap()
        for (i in 0..8) { m.add(i * 15 + 15, i - 3) }
        @Expect(m.remove(15), -3)
        @Expect(m.remove(45), -1)
        for (i in 0..8) {
            let present = i != 0 && i != 2
            @Expect(m.contains(i * 15 + 15), present)
            let r = m.get(i * 15 + 15)
            @Expect(r.ok, present)
            @Expect(r.value, if (present) { i - 3 } else { 0 })
        }
        @Expect(m.get(135).ok, false)
        @Expect(m.get(135).value, 0)
        @Expect(m.size(), 6)
        @Expect(m.capacity(), 16)
    }

}
