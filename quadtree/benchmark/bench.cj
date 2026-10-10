import std.collection.*
import std.time.*
import std.env.*
import std.convert.*

func checksum(list: PointList): Int64 {
    var sum: Int64=0;var p=list
    while (p.nonempty) {sum+=(p.x*65537+p.y+1)%1000003;p=p.next}
    return sum
}
func batch(work: ()->Int64,reps: Int64,expected: Int64): Int64 {
    let start=MonoTime.now();var sum: Int64=0
    for (i in 0..reps) {sum+=work()}
    let elapsed=(MonoTime.now()-start).toNanoseconds()
    require(sum==expected*reps,"timed checksum");return elapsed
}
func compare(name: String,dist: String,n: Int64,ops: Int64,limit: Int64,expected: Int64,
             works: Array<()->Int64>,offset: Int64): Unit {
    let reps=Array<Int64>(3,{_ => 1})
    // Two complete warmup batches, then independent calibration toward 20 ms.
    for (k in 0..3) {
        batch(works[k],1,expected);batch(works[k],1,expected)
        while (batch(works[k],reps[k],expected)<20000000 && reps[k]<limit) {reps[k]=min(reps[k]*2,limit)}
    }
    let names=["CJR","Native","Flat"]
    for (trial in 0..7) {
        for (j in 0..3) {
            let k=(j+trial+offset)%3
            let ns=batch(works[k],reps[k],expected)
            println("BENCH,${dist},${n},${name},${names[k]},${trial},${reps[k]},${ns},${ops*reps[k]},${expected*reps[k]}")
        }
    }
}
func dataset(dist: String,n: Int64): ArrayList<(Int64,Int64)> {
    let ps=ArrayList<(Int64,Int64)>();let seen=HashSet<Int64>()
    var state: Int64=20261010
    while (ps.size<n) {
        var x: Int64=0;var y: Int64=0
        if (dist=="prefix") {x=ps.size%128;y=ps.size/128}
        else {
            state=(state*48271)%2147483647;x=state%(if(dist=="cluster"){256}else{1073741824})
            state=(state*48271)%2147483647;y=state%(if(dist=="cluster"){256}else{1073741824})
        }
        if (!seen.contains(key(x,y))) {seen.add(key(x,y));ps.add((x,y))}
    }
    return ps
}
@Test
class QuadtreeBenchmark {
    @TestCase
    func measured(): Unit {
        let offset=Int64.parse(getVariable("QT_PROCESS").getOrThrow())
        for (dist in ["uniform","cluster","prefix"]) {for (n in [256,4096,16384]) {
            let ps=dataset(dist,n);let c=make(30);let nt=NativeTree(30);let f=FlatTree(1073741824)
            for (p in ps) {require(insert(c,p[0],p[1]),"CJR build");require(nt.add(p[0],p[1]),"native build");require(f.add(p[0],p[1]),"flat build")}
            require(same(full(c),f.keys),"complete CJR result")
            require(same(outputSet(nt.select(0,0,f.side,f.side)),f.keys),"complete native result")
            for (p in ps) {require(contains(c,p[0],p[1]) && nt.has(p[0],p[1]) && f.has(p[0],p[1]),"complete membership")}
            compare("build",dist,n,n,max(1,262144/n),n,[
                {=>let t=make(30);var count: Int64=0;for (p in ps) {if(insert(t,p[0],p[1])){count+=1}};count},
                {=>let t=NativeTree(30);var count: Int64=0;for(p in ps){if(t.add(p[0],p[1])){count+=1}};count},
                {=>let t=FlatTree(f.side);var count: Int64=0;for(p in ps){if(t.add(p[0],p[1])){count+=1}};count}],offset)
            compare("hits",dist,n,n,65536,n,[
                {=>var count: Int64=0;for(p in ps){if(contains(c,p[0],p[1])){count+=1}};count},
                {=>var count: Int64=0;for(p in ps){if(nt.has(p[0],p[1])){count+=1}};count},
                {=>var count: Int64=0;for(p in ps){if(f.has(p[0],p[1])){count+=1}};count}],offset)
            // Miss points are in-domain. Uniform misses use an oracle-checked shift.
            let misses=ArrayList<(Int64,Int64)>()
            for(p in ps){var x=(p[0]+536870912)%1073741824;while(f.has(x,p[1])){x=(x+1)%1073741824};misses.add((x,p[1]))}
            for(p in misses){require(!contains(c,p[0],p[1]) && !nt.has(p[0],p[1]),"complete misses")}
            compare("misses",dist,n,n,65536,n,[
                {=>var count: Int64=0;for(p in misses){if(!contains(c,p[0],p[1])){count+=1}};count},
                {=>var count: Int64=0;for(p in misses){if(!nt.has(p[0],p[1])){count+=1}};count},
                {=>var count: Int64=0;for(p in misses){if(!f.has(p[0],p[1])){count+=1}};count}],offset)
            let span=if(dist=="uniform"){1073741824}else{if(dist=="cluster"){256}else{128}}
            let rects=[(-1,-1,0,0),(0,0,span/8,span/8),(0,0,span*3/4,span*3/4),(0,0,f.side,f.side)]
            let labels=["empty","selective","broad","whole"]
            for (i in 0..4) {
                let r=rects[i];let expectedSet=oracleRange(f.keys,r[0],r[1],r[2],r[3])
                require(same(outputSet(range(c,r[0],r[1],r[2],r[3])),expectedSet),"complete CJR range")
                require(same(outputSet(nt.select(r[0],r[1],r[2],r[3])),expectedSet),"complete native range")
                require(same(outputSet(f.select(r[0],r[1],r[2],r[3])),expectedSet),"complete flat range")
                let expected=checksum(f.select(r[0],r[1],r[2],r[3]))
                compare(labels[i],dist,n,1,min(65536,max(1,262144/max(1,expectedSet.size))),expected,[
                    {=>checksum(range(c,r[0],r[1],r[2],r[3]))},
                    {=>checksum(nt.select(r[0],r[1],r[2],r[3]))},
                    {=>checksum(f.select(r[0],r[1],r[2],r[3]))}],offset)
            }
        }}
    }
}
