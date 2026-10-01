import std.collection.LinkedList as StdLinkedList

@Test
class ListBenchmark {
    @TestCase
    func compare(): Unit {
        for (n in [256, 4096, 16384]) {
            let expected = n * (n - 1) / 2
            var root = nil()
            let sl = StdLinkedList<Int64>()
            var i: Int64 = 0
            while (i < n) { root = cons(i, root); sl.addFirst(i); i += 1 }
            let traversalRoot = root
            benchPair("list_traverse", n, n, 65536, expected,
                { => var p = traversalRoot; var sum: Int64 = 0
                    while (!empty(p)) { sum += head(p); p = tail(p) }; sum },
                { => var p = sl.firstNode; var sum: Int64 = 0
                    while (p.isSome()) { let node = p.getOrThrow(); sum += node.value; p = node.next }; sum })
            benchPair("list_build_scan", n, n, 262144 / n, expected,
                { => var p = nil(); var j: Int64 = 0
                    while (j < n) { p = cons(j, p); j += 1 }
                    var sum: Int64 = 0
                    while (!empty(p)) { sum += head(p); p = tail(p) }; sum },
                { => let l = StdLinkedList<Int64>(); var j: Int64 = 0
                    while (j < n) { l.addFirst(j); j += 1 }
                    var p = l.firstNode; var sum: Int64 = 0
                    while (p.isSome()) { let node = p.getOrThrow(); sum += node.value; p = node.next }; sum })
        }
    }
}
