// Cangjie side of the driving adapter. No OTP implementation belongs here.
@C
public func authenticatorCreate(): CPointer<Int64> {
    try { return authNew() } catch (_: Exception) { return CPointer<Int64>() }
}
@C
public func authenticatorDispatch(op: Int64,session: CPointer<Int64>,p: CPointer<Int64>,out: CPointer<Int64>): Int64 {
    try {
        match(op) {
            case 0 => authDestroy(session); return 0
            case 1 => return authAdd(session,unsafe{p+7},unsafe{(p+4).read()},unsafe{p+135},unsafe{(p+5).read()},unsafe{p+263},unsafe{(p+6).read()},unsafe{(p+2).read()},unsafe{(p+3).read()})
            case 2 => return authList(session,out)
            case 3 => return if(authRead(session,unsafe{p.read()},out)){1}else{0}
            case 4 => return if(authRename(session,unsafe{p.read()},unsafe{p+7},unsafe{(p+4).read()},unsafe{p+135},unsafe{(p+5).read()})){1}else{0}
            case 5 => return if(authRemove(session,unsafe{p.read()})){1}else{0}
            case 6 => return authCode(session,unsafe{p.read()},unsafe{(p+1).read()})
            case 7 => return authRemaining(unsafe{(p+1).read()},unsafe{(p+3).read()})
            case _ => return -10
        }
    } catch (_: Exception) { return -10 }
}
