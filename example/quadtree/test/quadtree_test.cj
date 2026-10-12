import std.collection.*

func require(ok: Bool, message: String): Unit {
    if (!ok) { throw Exception(message) }
}
// The oracle uses a flat collection, independent of node routing and bounds.
func key(x: Int64, y: Int64): Int64 { x * 1073741824 + y }
func outputSet(list: PointList): HashSet<Int64> {
    let s = HashSet<Int64>()
    var p = list
    while (p.nonempty) {
        require(!s.contains(key(p.x,p.y)), "duplicate range result")
        s.add(key(p.x,p.y)); p = p.next
    }
    return s
}
func same(a: HashSet<Int64>, b: HashSet<Int64>): Bool {
    if (a.size != b.size) { return false }
    for (k in a) { if (!b.contains(k)) { return false } }
    return true
}
func shape(n: QuadNode): String {
    let prefix = "${n.tag}:${n.px}:${n.py}:${n.x0}:${n.y0}:${n.x1}:${n.y1}:${n.mx}:${n.my}"
    if (n.tag != 2) { return prefix }
    return prefix + "[" + shape(n.ll)+","+shape(n.lr)+","+shape(n.ul)+","+shape(n.ur)+"]"
}
func full(t: QuadTree): HashSet<Int64> { outputSet(range(t,0,0,t.side,t.side)) }
func oracleRange(s: HashSet<Int64>, a: Int64, b: Int64, c: Int64, d: Int64): HashSet<Int64> {
    let result=HashSet<Int64>()
    for (k in s) {
        let x=k/1073741824; let y=k%1073741824
        if (a<=x && x<c && b<=y && y<d) { result.add(k) }
    }
    return result
}
@Test
class QuadtreeTests {
    @TestCase
    func emptyAndUnit(): Unit {
        for (d in [0,1,8,30]) {
            let t=make(d)
            require(full(t).size==0, "empty")
            require(!contains(t,0,0), "empty membership")
            require(insert(t,0,0), "first insert")
            require(!insert(t,0,0), "duplicate")
            require(contains(t,0,0), "present")
            let before=shape(t.root)
            require(!insert(t,-1,0) && !insert(t,t.side,0), "rejected")
            require(!contains(t,-1,0) && !contains(t,t.side,0), "oob membership")
            require(shape(t.root)==before, "rejected structure")
        }
    }
    @TestCase
    func boundsQuadrantsAndRectangles(): Unit {
        let t=make(4); let oracle=HashSet<Int64>()
        for (x in [0,7,8,15]) { for (y in [0,7,8,15]) {
            require(insert(t,x,y), "quadrant insertion");oracle.add(key(x,y))
        } }
        require(same(full(t),oracle), "quadrants")
        let lo: Int64 = -9223372036854775807-1
        let hi: Int64 = 9223372036854775807
        require(!insert(t,lo,hi) && !contains(t,hi,lo), "Int64 extremes")
        for (r in [(0,0,0,0),(9,9,3,3),(-20,-20,-1,-1),(7,7,9,9),(0,0,8,8),(0,0,16,16),(lo,lo,hi,hi)]) {
            let before=shape(t.root)
            let a=outputSet(range(t,r[0],r[1],r[2],r[3]))
            let b=outputSet(range(t,r[0],r[1],r[2],r[3]))
            require(same(a,oracleRange(oracle,r[0],r[1],r[2],r[3])), "rectangle oracle")
            require(same(a,b) && before==shape(t.root), "query idempotence and structure")
        }
    }
    @TestCase
    func insertionAlgebra(): Unit {
        for (p in [(0,0),(7,8),(8,7),(15,15),(-1,0),(16,1)]) {
            for (q in [(0,0),(7,8),(8,7),(15,15),(-1,0),(16,1)]) {
                let a=make(4);let b=make(4)
                insert(a,p[0],p[1]);insert(a,q[0],q[1])
                insert(b,q[0],q[1]);insert(b,p[0],p[1])
                require(same(full(a),full(b)), "commutativity")
                let before=shape(a.root)
                require(!insert(a,p[0],p[1]) && before==shape(a.root), "idempotence")
                for (x in 0..16) { for (y in 0..16) {
                    require(contains(a,x,y)==contains(b,x,y), "complete membership")
                } }
            }
        }
    }
    @TestCase
    func unionDistribution(): Unit {
        let s=make(6);let t=make(6);let u=make(6)
        for (i in 0..64) {
            insert(s,i,i);insert(u,i,i)
            insert(t,i,63-i);insert(u,i,63-i)
        }
        for (r in [(0,0,64,64),(10,5,40,42),(0,0,32,32),(20,20,20,25),(70,70,80,80)]) {
            let a=outputSet(range(s,r[0],r[1],r[2],r[3]))
            let b=outputSet(range(t,r[0],r[1],r[2],r[3]))
            for (k in b) { a.add(k) }
            require(same(a,outputSet(range(u,r[0],r[1],r[2],r[3]))), "range union distribution")
        }
    }
    @TestCase
    func seededSequencesAndPermutations(): Unit {
        var seed: Int64=20261010
        let points=ArrayList<(Int64,Int64)>()
        let t=make(8);let oracle=HashSet<Int64>()
        for (i in 0..4000) {
            seed=(seed*48271)%2147483647;let x=seed%280-12
            seed=(seed*48271)%2147483647;let y=seed%280-12
            let good=0<=x && x<256 && 0<=y && y<256
            let fresh=good && !oracle.contains(key(x,y))
            require(insert(t,x,y)==fresh, "seeded insertion")
            if (good) {oracle.add(key(x,y));points.add((x,y))}
            let beforeMembership=shape(t.root)
            let first=contains(t,x,y);let second=contains(t,x,y)
            require(first==good && second==first, "seeded membership idempotence")
            require(beforeMembership==shape(t.root), "membership structure")
            if (i%97==0) {
                let before=shape(t.root)
                let a=x;let b=y;let c=x+31;let d=y+19
                require(same(outputSet(range(t,a,b,c,d)),oracleRange(oracle,a,b,c,d)), "seeded range")
                require(before==shape(t.root), "seeded query structure")
            }
        }
        let reversed=make(8)
        var i=points.size
        while (i>0) {i-=1;let p=points[i];insert(reversed,p[0],p[1])}
        require(same(full(t),oracle) && same(full(reversed),oracle), "insertion permutation")
        for (shift in [1,97,521]) {
            let permuted=make(8)
            for (j in 0..points.size) {let p=points[(j+shift)%points.size];insert(permuted,p[0],p[1])}
            require(same(full(permuted),oracle), "rotated insertion permutation")
        }
        let deep=make(30)
        for (j in 0..256) {require(insert(deep,j%16,j/16), "cluster insertion")}
        require(full(deep).size==256, "deep shared prefix")
        require(outputSet(range(deep,0,0,8,8)).size==64, "deep selective")
    }
}
