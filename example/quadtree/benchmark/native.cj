import std.collection.*

// Independent implementation: no calls to the extracted operations.
class NativeNode {
    let x0: Int64; let y0: Int64; let x1: Int64; let y1: Int64
    var tag: Int64=0; var x: Int64=0; var y: Int64=0
    var mx: Int64=0; var my: Int64=0
    let children=ArrayList<NativeNode>()
    init(a: Int64,b: Int64,c: Int64,d: Int64) {x0=a;y0=b;x1=c;y1=d}
    func child(px: Int64,py: Int64): NativeNode {children[(if (px<mx) {0} else {1})+(if (py<my) {0} else {2})]}
    func add(px: Int64,py: Int64): Bool {
        if (tag==0) {tag=1;x=px;y=py;return true}
        if (tag==1) {
            if (x==px && y==py) {return false}
            let half=(x1-x0)/2;mx=x0+half;my=y0+half
            children.add(NativeNode(x0,y0,mx,my));children.add(NativeNode(mx,y0,x1,my))
            children.add(NativeNode(x0,my,mx,y1));children.add(NativeNode(mx,my,x1,y1))
            child(x,y).add(x,y);tag=2;x=0;y=0
        }
        return child(px,py).add(px,py)
    }
    func has(px: Int64,py: Int64): Bool {
        if (tag==0) {return false}
        if (tag==1) {return px==x && py==y}
        return child(px,py).has(px,py)
    }
    func select(a: Int64,b: Int64,c: Int64,d: Int64,tail: PointList): PointList {
        if (tag==0 || x0>=c || a>=x1 || y0>=d || b>=y1) {return tail}
        if (tag==1) {
            if (a<=x && x<c && b<=y && y<d) {return PointList(true,x,y,tail)}
            return tail
        }
        var acc=tail;var i: Int64=4
        while (i>0) {i-=1;acc=children[i].select(a,b,c,d,acc)}
        return acc
    }
}
class NativeTree {
    let side: Int64;let root: NativeNode
    init(depth: Int64) {
        var s: Int64=1;for (i in 0..depth) {s+=s};side=s;root=NativeNode(0,0,s,s)
    }
    func add(x: Int64,y: Int64): Bool {if (x<0 || y<0 || x>=side || y>=side) {return false};return root.add(x,y)}
    func has(x: Int64,y: Int64): Bool {x>=0 && y>=0 && x<side && y<side && root.has(x,y)}
    func select(a: Int64,b: Int64,c: Int64,d: Int64): PointList {root.select(a,b,c,d,PointList(false,0,0,None))}
}
class FlatTree {
    let entries=ArrayList<(Int64,Int64)>()
    let keys=HashSet<Int64>()
    let side: Int64
    init(s: Int64) {side=s}
    func add(x: Int64,y: Int64): Bool {
        if (x<0 || y<0 || x>=side || y>=side || keys.contains(key(x,y))) {return false}
        keys.add(key(x,y));entries.add((x,y));return true
    }
    func has(x: Int64,y: Int64): Bool {x>=0 && y>=0 && x<side && y<side && keys.contains(key(x,y))}
    func select(a: Int64,b: Int64,c: Int64,d: Int64): PointList {
        var result=PointList(false,0,0,None)
        for (p in entries) {if (a<=p[0] && p[0]<c && b<=p[1] && p[1]<d) {result=PointList(true,p[0],p[1],result)}}
        return result
    }
}
