// Full-byte comparison output, outside all timing paths.
func verifyAlloc(n: Int64): CPointer<Int64> {
    unsafe { CPointer<Int64>(calloc(UIntNative(n), UIntNative(8))) }
}
func verifyDump(direction: String, bits: Int64, n: Int64, p: CPointer<Int64>, length: Int64): Unit {
    var i: Int64 = 0
    while (i < length) {
        var line = "VERIFY,${bits},${n},${direction},${i}"
        for (j in 0..16) { line += ",${unsafe { (p+i+j).read() }}" }
        println(line)
        i += 16
    }
}
@Test
class Differential {
    @TestCase
    func compare(): Unit {
        for (bits in [128, 192, 256]) {
            let key = verifyAlloc(32); let schedule = verifyAlloc(240)
            let work = verifyAlloc(64); let iv = verifyAlloc(32)
            for (i in 0..(bits/8)) { unsafe { (key+i).write(i) } }
            let nr = aesExpandKey(key, bits/8, schedule)
            for (n in [16, 1024, 65536]) {
                let src = verifyAlloc(n); let cipher = verifyAlloc(n); let back = verifyAlloc(n)
                for (i in 0..n) { unsafe { (src+i).write((i*29+131)%256) } }
                for (i in 0..32) { unsafe { (iv+i).write(i) } }
                @Expect(aesIgeEncrypt(src,cipher,n,iv,schedule,nr,work), true)
                verifyDump("encrypt",bits,n,cipher,n)
                verifyDump("encrypt_iv",bits,n,iv,32)
                for (i in 0..32) { unsafe { (iv+i).write(i) } }
                @Expect(aesIgeDecrypt(cipher,back,n,iv,schedule,nr,work), true)
                verifyDump("decrypt",bits,n,back,n)
                verifyDump("decrypt_iv",bits,n,iv,32)
                for (i in 0..n) { @Expect(unsafe { (back+i).read() }, unsafe { (src+i).read() }) }
            }
        }
    }
}
