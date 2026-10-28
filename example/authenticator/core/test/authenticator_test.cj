// Runtime tests only: no user-facing CLI or platform adapters.
func allocWords(n: Int64): CPointer<Int64> { unsafe { CPointer<Int64>(calloc(UIntNative(n), UIntNative(8))) } }
func releaseWords(p: CPointer<Int64>): Unit { unsafe { free(CPointer<Unit>(p)) } }
func fillWords(p: CPointer<Int64>, data: Array<Int64>): Unit {
    for (i in 0..data.size) { unsafe { (p+i).write(data[i]) } }
}
func sameWords(p: CPointer<Int64>, data: Array<Int64>): Unit {
    for (i in 0..data.size) { @Expect(unsafe { (p+i).read() }, data[i]) }
}
func checkSha(data: Array<Int64>, expected: Array<Int64>): Unit {
    let src=allocWords(data.size+1); let dst=allocWords(22)
    fillWords(src,data); fillWords(dst,Array<Int64>(22,repeat:777))
    @Expect(authSha1(src,data.size,unsafe { dst+1 }),true)
    sameWords(unsafe { dst+1 },expected)
    @Expect(unsafe { dst.read() },777); @Expect(unsafe { (dst+21).read() },777)
    sameWords(src,data); releaseWords(src); releaseWords(dst)
}
func checkHmac(key: Array<Int64>, msg: Array<Int64>, expected: Array<Int64>): Unit {
    let kp=allocWords(key.size+1); let mp=allocWords(msg.size+1); let dst=allocWords(22)
    fillWords(kp,key); fillWords(mp,msg); fillWords(dst,Array<Int64>(22,repeat:777))
    @Expect(authHmac(kp,key.size,mp,msg.size,unsafe { dst+1 }),true)
    sameWords(unsafe { dst+1 },expected); sameWords(kp,key); sameWords(mp,msg)
    @Expect(unsafe { dst.read() },777); @Expect(unsafe { (dst+21).read() },777)
    releaseWords(kp); releaseWords(mp); releaseWords(dst)
}
func checkAliasedHmac(data: Array<Int64>, keyStart: Int64, keyLen: Int64,
    msgStart: Int64, msgLen: Int64, expected: Array<Int64>): Unit {
    let src=allocWords(data.size+1); let dst=allocWords(22)
    fillWords(src,data); fillWords(dst,Array<Int64>(22,repeat:777))
    @Expect(authHmac(unsafe { src+keyStart },keyLen,unsafe { src+msgStart },msgLen,unsafe { dst+1 }),true)
    sameWords(unsafe { dst+1 },expected); sameWords(src,data)
    @Expect(unsafe { dst.read() },777); @Expect(unsafe { (dst+21).read() },777)
    releaseWords(src); releaseWords(dst)
}
func checkBase32(src: Array<Int64>, expected: Array<Int64>): Unit {
    let p=allocWords(src.size); let out=allocWords(130)
    fillWords(p,src); fillWords(out,Array<Int64>(130,repeat:777))
    @Expect(authBase32(p,src.size,unsafe { out+1 }),expected.size)
    sameWords(unsafe { out+1 },expected)
    @Expect(unsafe { out.read() },777); @Expect(unsafe { (out+expected.size+1).read() },777)
    releaseWords(p); releaseWords(out)
}
@Test
class AuthenticatorTests {
    @TestCase
    func divisionCorrespondence(): Unit {
        @Expect(Int64(-7)/Int64(3),-2)
        @Expect(Int64(7)/Int64(-3),-2)
        @Expect(Int64(-7)/Int64(-3),2)
    }
    @TestCase
    func invalidCryptoInputs(): Unit {
        let p=allocWords(1); let out=allocWords(20)
        fillWords(p,[256]); fillWords(out,Array<Int64>(20,repeat:777))
        @Expect(authSha1(p,-1,out),false); @Expect(authSha1(p,2049,out),false)
        @Expect(authSha1(p,1,out),false); sameWords(out,Array<Int64>(20,repeat:777))
        @Expect(authHmac(p,0,p,0,out),false); @Expect(authHmac(p,129,p,0,out),false)
        @Expect(authHmac(p,1,p,1025,out),false); @Expect(authHmac(p,1,p,0,out),false)
        sameWords(out,Array<Int64>(20,repeat:777))
        @Expect(authTotp(p,1,0,0,6),-1); @Expect(authTotp(p,1,-1,30,6),-1)
        @Expect(authTotp(p,1,0,30,7),-1); @Expect(authTotp(p,1,0,2147483648,6),-1)
        @Expect(authHotp(p,1,-1,6),-1); @Expect(authRemaining(-1,30),-1)
        @Expect(authRemaining(0,0),-1); @Expect(authRemaining(0,30),30)
        releaseWords(p); releaseWords(out)
    }
    @TestCase
    func aliasedMessageByteFailureIsAtomic(): Unit {
        let src=allocWords(40); let out=allocWords(20)
        let before=Array<Int64>(40,{ i => if (i==30) { 256 } else { i } })
        fillWords(src,before); fillWords(out,Array<Int64>(20,repeat:777))
        @Expect(authHmac(src,16,unsafe { src+8 },32,out),false)
        sameWords(src,before); sameWords(out,Array<Int64>(20,repeat:777))
        releaseWords(src); releaseWords(out)
    }
    @TestCase
    func invalidBase32IsAtomic(): Unit {
        let p=allocWords(208); let out=allocWords(128)
        let bad: Array<Array<Int64>> = [[],[65],[65,65,65],[65,65,65,65,65,65],
            [77,90],[77,89,61],[77,89,61,61,61,61,61,61,61],
            [77,89,61,65,65,65,65,65],[77,48],[77,49],[77,56],[77,255],
            [77,89,32],[77,89,10],[61,61],[65,65,65,65,65,65,65,65,61,61,61,61,61,61,61,61]]
        for (data in bad) {
            fillWords(p,data); fillWords(out,Array<Int64>(128,repeat:777))
            @Expect(authBase32(p,data.size,out),-1); sameWords(out,Array<Int64>(128,repeat:777))
        }
        fillWords(p,Array<Int64>(208,repeat:65)); @Expect(authBase32(p,208,out),-1); sameWords(out,Array<Int64>(128,repeat:777))
        releaseWords(p); releaseWords(out)
    }
    @TestCase
    func sessionLifecycle(): Unit {
        let s=authNew(); let label=allocWords(128); let issuer=allocWords(128)
        let secret=allocWords(32); let ids=allocWords(16); let meta=allocWords(260)
        fillWords(label,[65]); fillWords(issuer,[66])
        // Base32 of RFC key 12345678901234567890.
        fillWords(secret,[71,69,90,68,71,78,66,86,71,89,51,84,81,79,74,81,71,69,90,68,71,78,66,86,71,89,51,84,81,79,74,81])
        @Expect(authList(s,ids),0)
        @Expect(authAdd(s,label,1,issuer,1,secret,32,8,30),1)
        @Expect(authCode(s,1,59),94287082); @Expect(authList(s,ids),1); sameWords(ids,[1])
        @Expect(authRead(s,1,meta),true); sameWords(meta,[8,30,1,1,65])
        @Expect(unsafe { (meta+132).read() },66)
        fillWords(label,[67,68]); @Expect(authRename(s,1,label,2,issuer,0),true)
        @Expect(authRead(s,1,meta),true); sameWords(meta,[8,30,2,0,67,68])
        @Expect(authCode(s,1,59),94287082)
        @Expect(authAdd(s,label,2,issuer,0,secret,32,6,30),2)
        @Expect(authCode(s,2,59),287082)
        @Expect(authRemove(s,1),true); sameWords(unsafe { s+2 },Array<Int64>(390,repeat:0))
        @Expect(authRemove(s,1),false)
        @Expect(authCode(s,1,59),-1); @Expect(authRead(s,1,meta),false)
        @Expect(authList(s,ids),1); sameWords(ids,[2])
        @Expect(authAdd(s,label,2,issuer,0,secret,32,6,30),3)
        @Expect(authList(s,ids),2); sameWords(ids,[3,2])
        @Expect(authRename(s,999,label,2,issuer,0),false)
        authDestroy(s); releaseWords(label); releaseWords(issuer); releaseWords(secret); releaseWords(ids); releaseWords(meta)
    }
    @TestCase
    func failurePreservesAllSessionWords(): Unit {
        let s=authNew(); let input=allocWords(208)
        fillWords(input,[77,89])
        @Expect(authAdd(s,input,2,input,0,input,2,6,30),1)
        let before=Array<Int64>(6242,{ i => unsafe { (s+i).read() } })
        fillWords(input,[77,90])
        @Expect(authAdd(s,input,2,input,0,input,2,6,30),-1)
        sameWords(s,before)
        @Expect(authRename(s,1,input,0,input,0),false); sameWords(s,before)
        @Expect(authRemove(s,999),false); sameWords(s,before)
        @Expect(authCode(s,1,-1),-1); sameWords(s,before)
        authDestroy(s); releaseWords(input)
    }
    @TestCase
    func identifierExhaustionIsAtomic(): Unit {
        let s=authNew(); let input=allocWords(2); fillWords(input,[77,89])
        unsafe { s.write(9223372036854775807) }
        let before=Array<Int64>(6242,{ i => unsafe { (s+i).read() } })
        @Expect(authAdd(s,input,2,input,0,input,2,6,30),-3); sameWords(s,before)
        authDestroy(s); releaseWords(input)
    }
    @TestCase
    func failuresPreserveSession(): Unit {
        let s=authNew(); let label=allocWords(128); let secret=allocWords(208); let ids=allocWords(16)
        fillWords(label,[65]); fillWords(secret,[77,89])
        @Expect(authAdd(s,label,1,label,0,secret,2,6,30),1)
        @Expect(authAdd(s,label,0,label,0,secret,2,6,30),-1)
        @Expect(authAdd(s,label,129,label,0,secret,2,6,30),-1)
        @Expect(authAdd(s,label,1,label,0,secret,2,7,30),-1)
        @Expect(authAdd(s,label,1,label,0,secret,2,6,0),-1)
        fillWords(secret,[77,90]); @Expect(authAdd(s,label,1,label,0,secret,2,6,30),-1)
        @Expect(authList(s,ids),1); sameWords(ids,[1])
        @Expect(authRename(s,1,label,0,label,0),false)
        fillWords(secret,[77,89]);
        for (i in 2..17) { @Expect(authAdd(s,label,1,label,0,secret,2,6,30),i) }
        @Expect(authAdd(s,label,1,label,0,secret,2,6,30),-2); @Expect(authList(s,ids),16)
        @Expect(authRemove(s,8),true); @Expect(authAdd(s,label,1,label,0,secret,2,6,30),17)
        let fresh=authNew(); @Expect(authList(fresh,ids),0); @Expect(authCode(fresh,1,0),-1)
        authDestroy(fresh); authDestroy(s); releaseWords(label); releaseWords(secret); releaseWords(ids)
    }
}
