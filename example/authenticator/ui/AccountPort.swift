import Foundation

struct Enrollment {
    var label: String
    var issuer: String
    var secret: String
    var digits: Int64 = 6
    var period: Int64 = 30
}
struct Account: Identifiable {
    let id: Int64
    let label: String
    let issuer: String
    let digits: Int64
    let period: Int64
    let code: String
    let remaining: Int64
}
protocol AccountPort: AnyObject {
    func enroll(_ input: Enrollment) throws -> Int64
    func accounts(at timestamp: Int64) throws -> [Account]
    func rename(_ id: Int64, label: String, issuer: String) throws
    func remove(_ id: Int64) throws
    func close()
}
protocol ClockPort { func now() -> Int64 }
struct SystemClock: ClockPort {
    func now() -> Int64 { max(0, Int64(Date().timeIntervalSince1970)) }
}
enum AdapterError: Error, LocalizedError {
    case invalid, capacity, missing, closed, runtime
    var errorDescription: String? {
        switch self {
        case .invalid: return "Check the account fields. Use SHA1, 6 or 8 digits, and a valid Base32 secret."
        case .capacity: return "This session has reached its account or identifier limit."
        case .missing: return "The account is no longer available."
        case .closed: return "This session has ended. Open a new session to continue."
        case .runtime: return "The core runtime could not complete the request."
        }
    }
}

// URI syntax and UTF-8 presentation validation belong in this driving adapter.
enum EnrollmentAdapter {
    static func decimal(_ text: String) throws -> Int64 {
        guard !text.isEmpty, text.utf8.allSatisfy({ $0 >= 48 && $0 <= 57 }),
              let number = Int64(text) else { throw AdapterError.invalid }
        return number
    }
    static func validateText(_ text: String, empty: Bool = false) throws {
        guard (empty || !text.isEmpty), text.utf8.count <= 128,
              text.utf8.allSatisfy({ $0 >= 32 && $0 != 127 }) else { throw AdapterError.invalid }
    }
    static func parse(_ uri: String) throws -> Enrollment {
        guard uri.utf8.count <= 4096, uri.hasPrefix("otpauth://totp/"), !uri.contains("#") else { throw AdapterError.invalid }
        let parts = uri.split(separator: "?", omittingEmptySubsequences: false)
        guard parts.count == 2,
              let label = String(parts[0].dropFirst(15)).removingPercentEncoding,
              !label.contains("/") else { throw AdapterError.invalid }
        var fields: [String: String] = [:]
        for field in parts[1].split(separator: "&", omittingEmptySubsequences: false) {
            let pair = field.split(separator: "=", maxSplits: 1, omittingEmptySubsequences: false)
            guard pair.count == 2, let name = String(pair[0]).removingPercentEncoding,
                  let value = String(pair[1]).removingPercentEncoding,
                  ["secret", "issuer", "algorithm", "digits", "period"].contains(name), fields[name] == nil
            else { throw AdapterError.invalid }
            fields[name] = value
        }
        guard let secret = fields["secret"], fields["algorithm", default: "SHA1"] == "SHA1" else { throw AdapterError.invalid }
        var issuer = fields["issuer", default: ""]
        let labels = label.split(separator: ":", omittingEmptySubsequences: false)
        guard labels.count <= 2 else { throw AdapterError.invalid }
        var account = label
        if labels.count == 2 {
            let prefix = String(labels[0])
            guard !prefix.isEmpty, issuer.isEmpty || issuer == prefix else { throw AdapterError.invalid }
            issuer = prefix; account = String(labels[1])
        }
        try validateText(account); try validateText(issuer, empty: true)
        return Enrollment(label: account, issuer: issuer, secret: secret,
                          digits: try decimal(fields["digits", default: "6"]),
                          period: try decimal(fields["period", default: "30"]))
    }
}
