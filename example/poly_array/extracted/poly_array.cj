// Generated from checked CJR generic source; do not edit.
import std.core.Array as CjrBuffer
public class PolyArray<T> {
public let len: Int64
public let data: CjrBuffer<T>
public init(len: Int64, data: CjrBuffer<T>) {
this.len = len
this.data = data
}
public static func make(n: Int64, seed: T): PolyArray<T> {
return ({ => 
let p = CjrBuffer<T>(n, repeat: seed)
PolyArray<T>(n, p)
})()
}
public func length(): Int64 {
let arr = this
return (({ cjrTypedValue: PolyArray<T> => cjrTypedValue })(arr)).len
}
public func get(i: Int64): T {
let arr = this
return (({ cjrTypedValue: CjrBuffer<T> => cjrTypedValue })((({ cjrTypedValue: PolyArray<T> => cjrTypedValue })(arr)).data))[i]
}
public func set(i: Int64, x: T): Unit {
let arr = this
return ({ cjrBuf: CjrBuffer<T>, cjrIndex: Int64, cjrValue: T => cjrBuf[cjrIndex] = cjrValue; () })((({ cjrTypedValue: PolyArray<T> => cjrTypedValue })(arr)).data, i, x)
}
}
main() {
PolyArray<Bool>.make(3, false)
0
}
