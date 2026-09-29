@Test
class FrameCallTests {
    @TestCase
    func writeTouchesOnlyThePassedPointer(): Unit {
        let p = unsafe { CPointer<Int64>(malloc(UIntNative(8 * 1))) }
        let q = unsafe { CPointer<Int64>(malloc(UIntNative(8 * 1))) }
        unsafe { p.write(0) }
        unsafe { q.write(3) }
        let r = frameCall(p, q)
        let pv = unsafe { p.read() }
        let qv = unsafe { q.read() }
        @Expect(r, 3)
        @Expect(pv, 9)
        @Expect(qv, 3)
        unsafe { free(CPointer<Unit>(p)) }
        unsafe { free(CPointer<Unit>(q)) }
    }
}
