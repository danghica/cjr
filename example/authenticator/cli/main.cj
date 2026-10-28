import std.env.*
import std.time.*
class SystemClock <: ClockPort { public func now(): Int64 { DateTime.nowUTC().toUnixTimeStamp().toSeconds() } }
func ask(prompt: String): String {
    print(prompt+": ")
    match (getStdIn().readln()) { case Some(s) => s case None => throw Exception("End of input") }
}
func help(topic: String): Unit {
    match (topic) {
        case "add" => println("add — prompts for label, issuer, Base32 secret, digits (6/8; default 6), period (1..2147483647; default 30). Example: add")
        case "uri" => println("uri — prompts for an otpauth://totp URI (SHA1 only). Example: uri")
        case "list" => println("list — shows account IDs, labels, issuer and parameters; excludes secrets. Example: list")
        case "code" => println("code <id> [unix-seconds] — shows a zero-padded code and seconds remaining. Example: code 1 59")
        case "rename" => println("rename <id> — prompts for a replacement label and issuer. Example: rename 1")
        case "remove" => println("remove <id> — deletes and clears an account. Example: remove 1")
        case "quit" => println("quit — clears this session and exits. EOF also exits.")
        case "help" => println("help [command] — lists commands or detailed usage. Example: help code")
        case "" => println("Commands: add, uri, list, code <id> [unix-seconds], rename <id>, remove <id>, help [command], quit\nUse help <command> for purpose, arguments and examples. Accounts are memory-only; capacity 16.")
        case _ => println("Unknown help topic. Use help.")
    }
}
func padded(n: Int64,digits: Int64): String { var s=n.toString(); while (s.size<digits) { s="0"+s }; s }
func run(accounts: AccountPort,clock: ClockPort): Unit {
    println("Authenticator · memory-only session · type help")
    while (true) {
        print("auth> ")
        let line=match (getStdIn().readln()) { case Some(s) => s.trimAscii() case None => return }
        let args=line.split(" ",removeEmpty:true); if (args.size==0) { continue }
        try {
            let command=args[0]
            if (command=="quit" && args.size==1) { return }
            if (command=="help" && args.size<=2) { help(if (args.size==2) { args[1] } else { "" }); continue }
            if (command=="add" && args.size==1) {
                let label=ask("Label"); let issuer=ask("Issuer (optional)"); let secret=ask("Base32 secret")
                let d=ask("Digits [6]"); let p=ask("Period [30]")
                let id=accounts.add(Enrollment(label,issuer,secret,if(d==""){6}else{decimal(d)},if(p==""){30}else{decimal(p)}))
                if (id<0) { println("Enrollment rejected (invalid input or capacity limit).") } else { println("Added account ${id}.") }; continue
            }
            if (command=="uri" && args.size==1) {
                let id=accounts.add(enrollmentURI(ask("TOTP URI")))
                if(id<0){println("Enrollment rejected (invalid input or capacity limit).") }else{println("Added account ${id}.")};continue
            }
            if (command=="list" && args.size==1) {
                let ids=accounts.ids(); if(ids.size==0){println("No accounts.")}
                for(id in ids){let m=accounts.read(id); println("${id} | ${m.label} | ${m.issuer} | ${m.digits} digits / ${m.period}s")};continue
            }
            if (command=="code" && (args.size==2 || args.size==3)) {
                let id=decimal(args[1]);let t=if(args.size==3){decimal(args[2])}else{clock.now()}
                let m=accounts.read(id);let n=accounts.code(id,t)
                if(n<0){println("Code request rejected.")}else{println("${padded(n,m.digits)} | ${accounts.remaining(t,m.period)}s remaining")};continue
            }
            if(command=="remove" && args.size==2){println(if(accounts.remove(decimal(args[1]))){"Removed."}else{"Unknown account."});continue}
            if(command=="rename" && args.size==2){let id=decimal(args[1]);let l=ask("New label");let i=ask("New issuer");println(if(accounts.rename(id,l,i)){"Renamed."}else{"Rename rejected."});continue}
            println("Invalid command or arguments. Use help.")
        } catch (_: Exception) { println("Request rejected. Check inputs and help; no change was committed by a rejected operation.") }
    }
}
main(): Unit { let accounts=CoreAccounts(); try { run(accounts,SystemClock()) } finally { accounts.close() } }
