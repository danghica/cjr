// Text/URI adapter: deliberately contains no Base32 or OTP implementation.
func decimal(s: String): Int64 {
    if (s.size==0) { throw Exception("Expected a nonnegative integer") }
    var n: Int64=0
    for (b in s.toArray()) {
        if (b<48 || b>57 || n>(9223372036854775807-Int64(b-48))/10) { throw Exception("Invalid integer") }
        n=n*10+Int64(b-48)
    }; n
}
func validateText(s: String, empty: Bool): Unit {
    if ((!empty && s.size==0) || s.size>128) { throw Exception("Metadata must fit 128 UTF-8 bytes") }
    for (b in s.toArray()) { if (b<32 || b==127) { throw Exception("Control characters are not allowed") } }
}
func hex(b: UInt8): Int64 {
    if (b>=48 && b<=57) { return Int64(b-48) }
    if (b>=65 && b<=70) { return Int64(b-65)+10 }
    if (b>=97 && b<=102) { return Int64(b-97)+10 }
    throw Exception("Invalid percent encoding")
}
func unescape(s: String): String {
    let src=s.toArray(); let dst=Array<UInt8>(src.size,repeat:0); var i=0; var n=0
    while (i<src.size) {
        if (src[i]==37) {
            if (i+2>=src.size) { throw Exception("Invalid percent encoding") }
            dst[n]=UInt8(hex(src[i+1])*16+hex(src[i+2])); i+=3
        } else { dst[n]=src[i]; i+=1 }; n+=1
    }; String.fromUtf8(Array<UInt8>(n,{j=>dst[j]}))
}
func enrollmentURI(uri: String): Enrollment {
    if (uri.size>4096 || !uri.startsWith("otpauth://totp/") || uri.contains("#")) { throw Exception("Expected an otpauth TOTP URI") }
    let parts=uri.split("?")
    if (parts.size!=2) { throw Exception("Expected URI parameters") }
    let raw=parts[0].toArray(); let label=unescape(String.fromUtf8(Array<UInt8>(raw.size-15,{i=>raw[i+15]})))
    if (label.contains("/")) { throw Exception("Invalid account label") }
    let names=Array<String>(5,repeat:""); let values=Array<String>(5,repeat:""); var count=0
    for (field in parts[1].split("&")) {
        let pair=field.split("=",2); if (pair.size!=2 || count==5) { throw Exception("Invalid URI parameters") }
        let name=unescape(pair[0]); let value=unescape(pair[1])
        if (!(name=="secret" || name=="issuer" || name=="algorithm" || name=="digits" || name=="period")) { throw Exception("Unsupported URI parameter") }
        for (j in 0..count) { if (names[j]==name) { throw Exception("Duplicate URI parameter") } }
        names[count]=name; values[count]=value; count+=1
    }
    var secret=""; var issuer=""; var digits: Int64=6; var period: Int64=30
    for (j in 0..count) {
        match(names[j]) {
            case "secret" => secret=values[j]
            case "issuer" => issuer=values[j]
            case "digits" => digits=decimal(values[j])
            case "period" => period=decimal(values[j])
            case "algorithm" => if (values[j]!="SHA1") { throw Exception("Only SHA1 is supported") }
            case _ => ()
        }
    }
    let labels=label.split(":"); var account=label
    if (labels.size>2) { throw Exception("Ambiguous issuer prefix") }
    if (labels.size==2) {
        if (labels[0].size==0 || (issuer.size>0 && issuer!=labels[0])) { throw Exception("Issuer mismatch") }
        issuer=labels[0]; account=labels[1]
    }
    validateText(account,false); validateText(issuer,true)
    Enrollment(account,issuer,secret,digits,period)
}
