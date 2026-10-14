// Buffer setup and key expansion are outside throughput timing.
func benchAlloc(n: Int64): CPointer<Int64> {
    unsafe { CPointer<Int64>(calloc(UIntNative(n), UIntNative(8))) }
}
func resetIv(iv: CPointer<Int64>): Unit {
    for (i in 0..32) { unsafe { (iv+i).write(i) } }
}
func byteSum(p: CPointer<Int64>, n: Int64): Int64 {
    var result: Int64 = 0
    for (i in 0..n) { result += unsafe { (p+i).read() } }
    result
}
func benchSingle(name: String, n: Int64, ops: Int64, expected: Int64, work: () -> Int64): Unit {
    checked(work(), expected); checked(work(), expected)
    let reps = calibrate(work, 16777216)
    for (t in 0..7) { sample(name, "CJR", n, ops, t, reps, expected, work) }
}
@Test
class AesIgeBenchmark {
    @TestCase
    func throughput(): Unit {
        if (true) {
            let key = benchAlloc(32); let schedule = benchAlloc(240); let work = benchAlloc(64); let iv = benchAlloc(32)
            for (i in 0..16) { unsafe { (key+i).write(i) } }
            let nr = aesExpandKey(key, 16, schedule)
            benchSingle("key_128", 16, 1, 22008, { =>
                checked(aesExpandKey(key, 16, schedule), nr)
                byteSum(schedule, (nr+1)*16)
            })
            if (true) {
                let src = benchAlloc(16); let dst = benchAlloc(16); let ciphertext = benchAlloc(16)
                for (i in 0..16) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_128", 16, 16, 2014, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 16)
                })
                benchSingle("decrypt_128", 16, 16, 2248, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 16, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 16)
                })
            }
            if (true) {
                let src = benchAlloc(1024); let dst = benchAlloc(1024); let ciphertext = benchAlloc(1024)
                for (i in 0..1024) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_128", 1024, 1024, 129590, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 1024)
                })
                benchSingle("decrypt_128", 1024, 1024, 130560, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 1024, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 1024)
                })
            }
            if (true) {
                let src = benchAlloc(65536); let dst = benchAlloc(65536); let ciphertext = benchAlloc(65536)
                for (i in 0..65536) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_128", 65536, 65536, 8336742, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 65536)
                })
                benchSingle("decrypt_128", 65536, 65536, 8355840, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 65536, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 65536)
                })
            }
        }
        if (true) {
            let key = benchAlloc(32); let schedule = benchAlloc(240); let work = benchAlloc(64); let iv = benchAlloc(32)
            for (i in 0..24) { unsafe { (key+i).write(i) } }
            let nr = aesExpandKey(key, 24, schedule)
            benchSingle("key_192", 24, 1, 23558, { =>
                checked(aesExpandKey(key, 24, schedule), nr)
                byteSum(schedule, (nr+1)*16)
            })
            if (true) {
                let src = benchAlloc(16); let dst = benchAlloc(16); let ciphertext = benchAlloc(16)
                for (i in 0..16) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_192", 16, 16, 2070, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 16)
                })
                benchSingle("decrypt_192", 16, 16, 2248, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 16, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 16)
                })
            }
            if (true) {
                let src = benchAlloc(1024); let dst = benchAlloc(1024); let ciphertext = benchAlloc(1024)
                for (i in 0..1024) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_192", 1024, 1024, 128279, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 1024)
                })
                benchSingle("decrypt_192", 1024, 1024, 130560, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 1024, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 1024)
                })
            }
            if (true) {
                let src = benchAlloc(65536); let dst = benchAlloc(65536); let ciphertext = benchAlloc(65536)
                for (i in 0..65536) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_192", 65536, 65536, 8366608, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 65536)
                })
                benchSingle("decrypt_192", 65536, 65536, 8355840, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 65536, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 65536)
                })
            }
        }
        if (true) {
            let key = benchAlloc(32); let schedule = benchAlloc(240); let work = benchAlloc(64); let iv = benchAlloc(32)
            for (i in 0..32) { unsafe { (key+i).write(i) } }
            let nr = aesExpandKey(key, 32, schedule)
            benchSingle("key_256", 32, 1, 28276, { =>
                checked(aesExpandKey(key, 32, schedule), nr)
                byteSum(schedule, (nr+1)*16)
            })
            if (true) {
                let src = benchAlloc(16); let dst = benchAlloc(16); let ciphertext = benchAlloc(16)
                for (i in 0..16) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_256", 16, 16, 2114, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 16, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 16)
                })
                benchSingle("decrypt_256", 16, 16, 2248, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 16, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 16)
                })
            }
            if (true) {
                let src = benchAlloc(1024); let dst = benchAlloc(1024); let ciphertext = benchAlloc(1024)
                for (i in 0..1024) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_256", 1024, 1024, 132608, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 1024, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 1024)
                })
                benchSingle("decrypt_256", 1024, 1024, 130560, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 1024, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 1024)
                })
            }
            if (true) {
                let src = benchAlloc(65536); let dst = benchAlloc(65536); let ciphertext = benchAlloc(65536)
                for (i in 0..65536) { unsafe { (src+i).write((i*29+131)%256) } }
                resetIv(iv)
                if (!aesIgeEncrypt(src, ciphertext, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                benchSingle("encrypt_256", 65536, 65536, 8363389, { =>
                    resetIv(iv)
                    if (!aesIgeEncrypt(src, dst, 65536, iv, schedule, nr, work)) { throw Exception("encryption rejected") }
                    byteSum(dst, 65536)
                })
                benchSingle("decrypt_256", 65536, 65536, 8355840, { =>
                    resetIv(iv)
                    if (!aesIgeDecrypt(ciphertext, dst, 65536, iv, schedule, nr, work)) { throw Exception("decryption rejected") }
                    byteSum(dst, 65536)
                })
            }
        }
    }
}
