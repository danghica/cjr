@Test
class ArithTests {
    @TestCase
    func signedMultiplication(): Unit {
        @Expect(multiply(-7, 6), -42)
        @Expect(multiply(-7, -6), 42)
        @Expect(multiply(0, 9223372036854775807), 0)
        @Expect(multiply(2147483646, 1000000007), 2147483661032385522)
        @Expect(multiply(-2147483646, 1000000007), -2147483661032385522)
    }

    @TestCase
    func sumOneReturnsOne(): Unit {
        @Expect(sumOne(), 1)
    }
}
