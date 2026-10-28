import SwiftUI
import AppKit
import Combine

@MainActor final class SessionModel: ObservableObject {
    @Published var accounts: [Account] = []
    @Published var error: String?
    private var port: AccountPort?
    private let clock: ClockPort
    init(clock: ClockPort = SystemClock()) {
        self.clock = clock
        do { port = try CoreSession(); refresh() } catch { self.error = error.localizedDescription }
    }
    func perform(_ work: (AccountPort) throws -> Void) {
        do {
            guard let port else { throw AdapterError.closed }
            try work(port); error = nil; refresh()
        } catch { self.error = error.localizedDescription }
    }
    func refresh() {
        guard let port else { return }
        do { accounts = try port.accounts(at: clock.now()) }
        catch { self.error = error.localizedDescription; accounts = [] }
    }
    func close() { port?.close(); port = nil; accounts = [] }
}

@main struct AuthenticatorApp: App {
    @StateObject private var model = SessionModel()
    var body: some Scene {
        WindowGroup {
            AccountsView(model: model)
                .onReceive(NotificationCenter.default.publisher(for: NSApplication.willTerminateNotification)) { _ in model.close() }
        }.windowStyle(.titleBar)
        .commands { CommandGroup(replacing: .newItem) {} }
    }
}

struct AccountsView: View {
    @ObservedObject var model: SessionModel
    @State private var adding = false
    @State private var editing: Account?
    @State private var deleting: Account?
    @State private var copied: Int64?
    private let timer = Timer.publish(every: 1, on: .main, in: .common).autoconnect()
    var body: some View {
        VStack(alignment: .leading, spacing: 0) {
            HStack {
                Image(systemName: "checkmark.shield.fill").font(.largeTitle).foregroundStyle(.teal)
                VStack(alignment: .leading, spacing: 4) {
                    Text("Authenticator").font(.title.bold())
                    Text("Offline codes · This session only").foregroundStyle(.secondary)
                }
                Spacer()
                Button { adding = true } label: { Label("Add account", systemImage: "plus") }
                    .buttonStyle(.borderedProminent).tint(.teal).keyboardShortcut("n")
            }.padding(24)
            Divider()
            if let error = model.error {
                Label(error, systemImage: "exclamationmark.circle").foregroundStyle(.red).padding(.horizontal, 24).padding(.top, 14)
            }
            if model.accounts.isEmpty {
                VStack(spacing: 12) {
                    Image(systemName: "key.horizontal").font(.system(size: 48)).foregroundStyle(.teal)
                    Text("Your codes start here").font(.title2.bold())
                    Text("Add a Base32 secret or paste a TOTP enrollment URI.\nAccounts are cleared when you quit.")
                        .multilineTextAlignment(.center).foregroundStyle(.secondary)
                    Button("Add your first account") { adding = true }.buttonStyle(.bordered)
                }.frame(maxWidth: .infinity, maxHeight: .infinity).padding(30)
            } else {
                ScrollView {
                    LazyVStack(spacing: 14) {
                        ForEach(model.accounts) { account in
                            HStack(spacing: 20) {
                                VStack(alignment: .leading, spacing: 5) {
                                    Text(account.issuer.isEmpty ? "Personal" : account.issuer).font(.caption.weight(.semibold)).foregroundStyle(.secondary)
                                    Text(account.label).font(.headline).textSelection(.enabled)
                                    Text(account.code).font(.system(size: 32, weight: .medium, design: .monospaced)).foregroundStyle(.teal).textSelection(.enabled)
                                }
                                Spacer()
                                VStack(spacing: 6) {
                                    ZStack {
                                        Circle().stroke(.teal.opacity(0.12), lineWidth: 4)
                                        Circle().trim(from: 0, to: Double(account.remaining)/Double(account.period)).stroke(.teal, style: StrokeStyle(lineWidth: 4, lineCap: .round)).rotationEffect(.degrees(-90))
                                        Text("\(account.remaining)").font(.caption.monospacedDigit())
                                    }.frame(width: 40, height: 40)
                                    Text("seconds").font(.caption2).foregroundStyle(.secondary)
                                }.accessibilityLabel("\(account.remaining) seconds remaining")
                                Button {
                                    NSPasteboard.general.clearContents()
                                    NSPasteboard.general.setString(account.code, forType: .string)
                                    copied = account.id
                                    DispatchQueue.main.asyncAfter(deadline: .now()+2) { copied = nil }
                                } label: { Image(systemName: copied == account.id ? "checkmark" : "doc.on.doc") }
                                .help("Copy code").accessibilityLabel("Copy code for \(account.label)")
                                Menu {
                                    Button("Rename") { editing = account }
                                    Button("Remove", role: .destructive) { deleting = account }
                                } label: { Image(systemName: "ellipsis") }.menuStyle(.borderlessButton).frame(width: 20)
                            }.padding(20).background(.background, in: RoundedRectangle(cornerRadius: 14))
                                .overlay(RoundedRectangle(cornerRadius: 14).stroke(.primary.opacity(0.08)))
                        }
                    }.padding(24)
                }.background(.quaternary.opacity(0.2))
            }
            Divider()
            HStack {
                Label("Memory only", systemImage: "lock").font(.caption)
                Spacer()
                Text("\(model.accounts.count) of 16 accounts · SHA1 TOTP").font(.caption)
            }.foregroundStyle(.secondary).padding(.horizontal, 24).padding(.vertical, 12)
        }.frame(minWidth: 620, minHeight: 480)
            .sheet(isPresented: $adding) { EnrollmentView(model: model) }
            .sheet(item: $editing) { account in RenameView(model: model, account: account) }
            .alert("Remove account?", isPresented: Binding(get: { deleting != nil }, set: { if !$0 { deleting = nil } })) {
                Button("Cancel", role: .cancel) { deleting = nil }
                Button("Remove", role: .destructive) { if let id = deleting?.id { model.perform { try $0.remove(id) } }; deleting = nil }
            } message: { Text("This session’s secret will be cleared. You will need the enrollment secret to add it again.") }
            .onReceive(timer) { _ in model.refresh() }
    }
}

struct EnrollmentView: View {
    @ObservedObject var model: SessionModel
    @Environment(\.dismiss) private var dismiss
    @State private var mode = 0
    @State private var label = ""
    @State private var issuer = ""
    @State private var secret = ""
    @State private var uri = ""
    @State private var digits: Int64 = 6
    @State private var period = "30"
    @State private var error: String?
    var body: some View {
        VStack(alignment: .leading, spacing: 18) {
            Text("Add account").font(.title2.bold())
            Picker("Enrollment", selection: $mode) { Text("Manual secret").tag(0); Text("TOTP URI").tag(1) }.pickerStyle(.segmented)
            Form {
                if mode == 0 {
                    TextField("Account label", text: $label)
                    TextField("Issuer (optional)", text: $issuer)
                    SecureField("Base32 secret", text: $secret)
                    Picker("Digits", selection: $digits) { Text("6").tag(Int64(6)); Text("8").tag(Int64(8)) }
                    TextField("Period in seconds", text: $period)
                } else { SecureField("otpauth://totp/…", text: $uri) }
            }
            Text("Your secret stays in this process. Accounts are discarded when you quit.").font(.caption).foregroundStyle(.secondary)
            if let error { Text(error).foregroundStyle(.red).font(.callout) }
            HStack {
                Button("Cancel") { dismiss() }.keyboardShortcut(.cancelAction)
                Spacer()
                Button("Add account") {
                    do {
                        let e = mode == 0 ? Enrollment(label: label, issuer: issuer, secret: secret, digits: digits, period: try EnrollmentAdapter.decimal(period)) : try EnrollmentAdapter.parse(uri)
                        var success = false
                        model.perform { _ = try $0.enroll(e); success = true }
                        if success { secret = ""; uri = ""; dismiss() } else { error = model.error }
                    } catch { self.error = error.localizedDescription }
                }.buttonStyle(.borderedProminent).tint(.teal).keyboardShortcut(.defaultAction)
            }
        }.padding(26).frame(width: 420).onDisappear { secret = ""; uri = "" }
    }
}
struct RenameView: View {
    @ObservedObject var model: SessionModel
    let account: Account
    @Environment(\.dismiss) private var dismiss
    @State private var label = ""
    @State private var issuer = ""
    @State private var error: String?
    var body: some View {
        VStack(alignment: .leading, spacing: 18) {
            Text("Rename account").font(.title2.bold())
            TextField("Account label", text: $label)
            TextField("Issuer", text: $issuer)
            if let error { Text(error).foregroundStyle(.red) }
            HStack {
                Button("Cancel") { dismiss() }.keyboardShortcut(.cancelAction)
                Spacer()
                Button("Save") {
                    var success = false
                    model.perform { try $0.rename(account.id, label: label, issuer: issuer); success = true }
                    if success { dismiss() } else { error = model.error }
                }.keyboardShortcut(.defaultAction)
            }
        }.padding(26).frame(width: 380).onAppear { label = account.label; issuer = account.issuer }
    }
}
