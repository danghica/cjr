@Test
class ListTests {
    @TestCase
    func nilIsEmpty(): Unit {
        let e = nil()
        @Expect(empty(e), true)
        @Expect(head(e), 0)
    }

    @TestCase
    func consThenHeadAndTail(): Unit {
        let e = nil()
        let l = cons(1, e)
        @Expect(empty(l), false)
        @Expect(head(l), 1)
        let t = tail(l)
        @Expect(empty(t), true)
        @Expect(head(t), 0)
    }

    @TestCase
    func consThenTailReturnsTheOriginalNode(): Unit {
        let e = nil()
        let l = cons(7, cons(1, e))
        let t = tail(l)
        @Expect(head(t), 1)
        @Expect(empty(tail(t)), true)
    }
}
