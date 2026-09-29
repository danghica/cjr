@Test
class SumBlockTests {
    @TestCase
    func sumAtReadsTheWrittenWord(): Unit {
        let p = unsafe { CPointer<Int64>(malloc(UIntNative(8 * 1))) }
        unsafe { p.write(4) }
        let s = sumAt(p)
        @Expect(s, 4)
        unsafe { free(CPointer<Unit>(p)) }
    }
}
