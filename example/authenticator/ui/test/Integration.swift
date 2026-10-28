import Foundation
@main struct Integration {
    static func check(_ condition: Bool) { precondition(condition) }
    static func reject(_ work: () throws -> Void) {
        do { try work(); fatalError("Expected rejection") } catch {}
    }
    static func main() throws {
        let data = try Data(contentsOf: URL(fileURLWithPath: CommandLine.arguments[1]))
        let fixtures = try JSONSerialization.jsonObject(with: data) as! [String: [String]]
        for uri in fixtures["valid"]! {
            let s = try CoreSession(); defer { s.close() }
            let e = try EnrollmentAdapter.parse(uri)
            _ = try s.enroll(e)
            check(try s.accounts(at: 59).count == 1)
        }
        for uri in fixtures["invalid"]! {
            let s = try CoreSession(); defer { s.close() }
            reject { _ = try s.enroll(EnrollmentAdapter.parse(uri)) }
            check(try s.accounts(at: 59).isEmpty)
        }
        let s = try CoreSession(), other = try CoreSession()
        defer { s.close(); other.close() }
        _ = try other.enroll(Enrollment(label: "Defaults", issuer: "", secret: "GEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ"))
        check(try other.accounts(at: 29)[0].code == "755224")
        check(try other.accounts(at: 30)[0].code == "287082")
        other.close()
        let isolated = try CoreSession(); defer { isolated.close() }
        let e = Enrollment(label: "alice", issuer: "Example", secret: "GEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ", digits: 8)
        let id = try s.enroll(e)
        var rows = try s.accounts(at: 59)
        precondition(rows[0].code == "94287082" && rows[0].remaining == 1)
        rows = try s.accounts(at: 1111111109)
        precondition(rows[0].code == "07081804")
        check(try isolated.accounts(at: 59).isEmpty)
        reject { _ = try s.enroll(Enrollment(label: "bad", issuer: "", secret: "MZ")) }
        check(try s.accounts(at: 59).count == 1)
        try s.rename(id, label: "Renamed", issuer: "Issuer")
        check(try s.accounts(at: 60)[0].label == "Renamed")
        check(try s.accounts(at: 60)[0].remaining == 30)
        for _ in 1..<16 { _ = try s.enroll(e) }
        reject { _ = try s.enroll(e) }
        check(try s.accounts(at: 59).count == 16)
        try s.remove(id)
        reject { try s.remove(id) }
        _ = try s.enroll(e)
        s.close(); s.close()
        reject { _ = try s.accounts(at: 59) }
        // Test ABI rejection before dispatch and preservation of output sentinels.
        let h = auth_session_create()!
        var params = [Int64](repeating: 0, count: 471)
        var output = [Int64](repeating: 777, count: 260)
        let result = params.withUnsafeMutableBufferPointer { p in
            output.withUnsafeMutableBufferPointer { o in
                auth_session_call(h, 2, p.baseAddress, 471, o.baseAddress, 15)
            }
        }
        precondition(result == -10 && output.allSatisfy { $0 == 777 })
        func rawCall(_ op: Int64, count: Int = 471, capacity: Int = 260) -> Int64 {
            params.withUnsafeMutableBufferPointer { p in
                output.withUnsafeMutableBufferPointer { o in
                    auth_session_call(h, op, p.baseAddress, count, o.baseAddress, capacity)
                }
            }
        }
        precondition(rawCall(2, count: 470) == -10)
        precondition(rawCall(99) == -10)
        params[6] = 209
        precondition(rawCall(1) == -10)
        params[6] = 0; params[4] = 129
        precondition(rawCall(4) == -10)
        params[4] = 0; params[0] = 999
        precondition(rawCall(3) == 0 && output.allSatisfy { $0 == 777 })
        precondition(rawCall(2) == 0)
        precondition(auth_session_destroy(h) == 0)
        print("Swift → C → Cangjie passed: URI parity, RFC vectors, padding, boundaries, isolation, atomic rejection, capacity, rename/remove, close and ABI capacity.")
    }
}
