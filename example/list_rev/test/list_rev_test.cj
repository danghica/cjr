@Test
class ListRevTests {
    @TestCase
    func emptyList(): Unit {
        let e = nil()
        let r = reverse(e)
        @Expect(empty(r), true)
        @Expect(head(r), 0)
        @Expect(empty(tail(r)), true)
        @Expect(empty(e), true)
    }

    @TestCase
    func singleton(): Unit {
        let n = cons(7, nil())
        let r = reverse(n)
        @Expect(empty(r), false)
        @Expect(head(r), 7)
        @Expect(empty(tail(r)), true)
        // The original cons node now ends the result.
        @Expect(empty(tail(n)), true)
    }

    @TestCase
    func severalNodes(): Unit {
        let r = reverse(cons(1, cons(2, cons(3, cons(4, nil())))))
        @Expect(head(r), 4)
        @Expect(head(tail(r)), 3)
        @Expect(head(tail(tail(r))), 2)
        @Expect(head(tail(tail(tail(r)))), 1)
        @Expect(empty(tail(tail(tail(tail(r))))), true)
    }

    @TestCase
    func duplicatesAndNegativeValues(): Unit {
        let r = reverse(cons(-2, cons(0, cons(-2, cons(9, nil())))))
        @Expect(head(r), 9)
        @Expect(head(tail(r)), -2)
        @Expect(head(tail(tail(r))), 0)
        @Expect(head(tail(tail(tail(r)))), -2)
        @Expect(empty(tail(tail(tail(tail(r))))), true)
    }

    @TestCase
    func doubleReversal(): Unit {
        let r = reverse(reverse(cons(5, cons(-1, cons(5, nil())))))
        @Expect(head(r), 5)
        @Expect(head(tail(r)), -1)
        @Expect(head(tail(tail(r))), 5)
        @Expect(empty(tail(tail(tail(r)))), true)
    }

    @TestCase
    func rewiresOriginalNodesAndFramesOtherList(): Unit {
        let e = nil()
        let c = cons(3, e)
        let b = cons(2, c)
        let a = cons(1, b)
        let other = cons(42, nil())
        let r = reverse(a)
        @Expect(head(r), 3)
        // Observe the old references: copying would leave these links unchanged.
        @Expect(head(tail(c)), 2)
        @Expect(head(tail(b)), 1)
        @Expect(empty(tail(a)), true)
        @Expect(empty(e), true)
        @Expect(head(other), 42)
        @Expect(empty(tail(other)), true)
    }
}
