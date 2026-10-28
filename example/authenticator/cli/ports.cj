// Driving port. Only this adapter knows the extracted pointer layout.
interface AccountPort {
    func add(e: Enrollment): Int64
    func ids(): Array<Int64>
    func read(id: Int64): Metadata
    func rename(id: Int64, label: String, issuer: String): Bool
    func remove(id: Int64): Bool
    func code(id: Int64, timestamp: Int64): Int64
    func remaining(timestamp: Int64, period: Int64): Int64
    func close(): Unit
}
interface ClockPort { func now(): Int64 }
struct Enrollment {
    let label: String; let issuer: String; let secret: String
    let digits: Int64; let period: Int64
    init(l: String, i: String, s: String, d: Int64, p: Int64) {
        label=l; issuer=i; secret=s; digits=d; period=p
    }
}
struct Metadata {
    let label: String; let issuer: String; let digits: Int64; let period: Int64
    init(l: String, i: String, d: Int64, p: Int64) { label=l; issuer=i; digits=d; period=p }
}
class Words {
    let pointer: CPointer<Int64>; let count: Int64
    init(n: Int64) { count=n; pointer=unsafe { CPointer<Int64>(calloc(UIntNative(n),8)) }; if (pointer.isNull()) { throw Exception("Memory unavailable") } }
    init(s: String) {
        let bytes=s.toArray(); count=bytes.size+1
        pointer=unsafe { CPointer<Int64>(calloc(UIntNative(count),8)) }
        if (pointer.isNull()) { throw Exception("Memory unavailable") }
        for (i in 0..bytes.size) { unsafe { (pointer+i).write(Int64(bytes[i])) } }
    }
    func at(i: Int64): Int64 { unsafe { (pointer+i).read() } }
    func text(start: Int64, n: Int64): String { String.fromUtf8(Array<UInt8>(n,{i => UInt8(at(start+i))})) }
    func close(): Unit { for (i in 0..count) { unsafe { (pointer+i).write(0) } }; unsafe { free(CPointer<Unit>(pointer)) } }
}
class CoreAccounts <: AccountPort {
    private let session: CPointer<Int64> = authNew()
    private var closed=false
    private func live(): Unit { if (closed) { throw Exception("Session closed") } }
    public func add(e: Enrollment): Int64 {
        live(); validateText(e.label,false); validateText(e.issuer,true)
        if (e.secret.size<2 || e.secret.size>208) { return -1 }
        let l=Words(e.label)
        try { let i=Words(e.issuer)
            try { let s=Words(e.secret)
                try { return authAdd(session,l.pointer,e.label.size,i.pointer,e.issuer.size,s.pointer,e.secret.size,e.digits,e.period) }
                finally { s.close() }
            } finally { i.close() }
        } finally { l.close() }
    }
    public func ids(): Array<Int64> { live(); let out=Words(16); try { let n=authList(session,out.pointer); return Array<Int64>(n,{i=>out.at(i)}) } finally { out.close() } }
    public func read(id: Int64): Metadata { live(); let out=Words(260)
        try { if (!authRead(session,id,out.pointer)) { throw Exception("Unknown account") }
            return Metadata(out.text(4,out.at(2)),out.text(132,out.at(3)),out.at(0),out.at(1))
        } finally { out.close() }
    }
    public func rename(id: Int64, label: String, issuer: String): Bool {
        live(); validateText(label,false); validateText(issuer,true)
        let l=Words(label); try { let i=Words(issuer)
            try { return authRename(session,id,l.pointer,label.size,i.pointer,issuer.size) } finally { i.close() }
        } finally { l.close() }
    }
    public func remove(id: Int64): Bool { live(); authRemove(session,id) }
    public func code(id: Int64,timestamp: Int64): Int64 { live(); authCode(session,id,timestamp) }
    public func remaining(timestamp: Int64,period: Int64): Int64 { live(); authRemaining(timestamp,period) }
    public func close(): Unit { if (!closed) { authDestroy(session); closed=true } }
}
