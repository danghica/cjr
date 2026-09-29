@Test
class ArithTests {
    @TestCase
    func sumOneReturnsOne(): Unit {
        @Expect(sumOne(), 1)
    }
}
