import Foundation

// This adapter alone knows the ABI word layout. The UI holds only Account values.
final class CoreSession: AccountPort {
    private var handle: OpaquePointer?
    private let lock = NSRecursiveLock()
    init() throws {
        handle = auth_session_create()
        guard handle != nil else { throw AdapterError.runtime }
    }
    deinit { close() }
    func close() {
        lock.lock(); defer { lock.unlock() }
        if let live = handle {
            // Runtime failure leaves the handle owned here so a later close can retry.
            if auth_session_destroy(live) == 0 { handle = nil }
        }
    }
    private func call(_ op: Int64, _ params: [Int64], output: inout [Int64]) throws -> Int64 {
        lock.lock(); defer { lock.unlock() }
        guard let handle else { throw AdapterError.closed }
        let result = params.withUnsafeBufferPointer { p in
            output.withUnsafeMutableBufferPointer { out in
                auth_session_call(handle, op, p.baseAddress, p.count, out.baseAddress, out.count)
            }
        }
        if result == -10 { throw AdapterError.runtime }
        return result
    }
    private func input(_ e: Enrollment, id: Int64 = 0) throws -> [Int64] {
        try EnrollmentAdapter.validateText(e.label)
        try EnrollmentAdapter.validateText(e.issuer, empty: true)
        guard e.secret.utf8.count <= 208 else { throw AdapterError.invalid }
        var p = [Int64](repeating: 0, count: 471)
        p[0] = id; p[2] = e.digits; p[3] = e.period
        p[4] = Int64(e.label.utf8.count); p[5] = Int64(e.issuer.utf8.count); p[6] = Int64(e.secret.utf8.count)
        for (start, text) in [(7, e.label), (135, e.issuer), (263, e.secret)] {
            for (i, byte) in text.utf8.enumerated() { p[start+i] = Int64(byte) }
        }
        return p
    }
    func enroll(_ input: Enrollment) throws -> Int64 {
        var p = try self.input(input)
        defer { _ = p.withUnsafeMutableBytes { $0.initializeMemory(as: UInt8.self, repeating: 0) } }
        var out: [Int64] = []; let result = try call(1, p, output: &out)
        if result == -1 { throw AdapterError.invalid }
        if result < 0 { throw AdapterError.capacity }
        return result
    }
    func accounts(at timestamp: Int64) throws -> [Account] {
        lock.lock(); defer { lock.unlock() }
        guard timestamp >= 0 else { throw AdapterError.invalid }
        var p = [Int64](repeating: 0, count: 471)
        var ids = [Int64](repeating: 0, count: 16)
        let count = try call(2, p, output: &ids)
        guard (0...16).contains(count) else { throw AdapterError.runtime }
        return try ids.prefix(Int(count)).map { id in
            p[0] = id
            var metadata = [Int64](repeating: 0, count: 260)
            guard try call(3, p, output: &metadata) == 1 else { throw AdapterError.missing }
            let digits = metadata[0], period = metadata[1]
            guard [6,8].contains(digits), (1...2_147_483_647).contains(period),
                  (1...128).contains(metadata[2]), (0...128).contains(metadata[3]) else { throw AdapterError.runtime }
            func text(_ start: Int, _ length: Int64) throws -> String {
                let words = metadata[start..<(start+Int(length))]
                guard words.allSatisfy({ (0...255).contains($0) }),
                      let value = String(bytes: words.map { UInt8($0) }, encoding: .utf8) else { throw AdapterError.runtime }
                return value
            }
            p[1] = timestamp; p[3] = period
            var out: [Int64] = []
            let code = try call(6, p, output: &out)
            let remaining = try call(7, p, output: &out)
            guard code >= 0, (1...period).contains(remaining) else { throw AdapterError.invalid }
            return Account(id: id, label: try text(4, metadata[2]), issuer: try text(132, metadata[3]),
                           digits: digits, period: period,
                           code: String(repeating: "0", count: max(0, Int(digits)-String(code).count))+String(code),
                           remaining: remaining)
        }
    }
    func rename(_ id: Int64, label: String, issuer: String) throws {
        let p = try input(Enrollment(label: label, issuer: issuer, secret: ""), id: id)
        var out: [Int64] = []
        guard try call(4, p, output: &out) == 1 else { throw AdapterError.missing }
    }
    func remove(_ id: Int64) throws {
        var p = [Int64](repeating: 0, count: 471); p[0] = id
        var out: [Int64] = []
        guard try call(5, p, output: &out) == 1 else { throw AdapterError.missing }
    }
}
