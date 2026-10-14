#!/usr/bin/env python3
"""Generate independent fixtures through OpenSSL's concrete AES-IGE API."""
import argparse
import ctypes as C
import hashlib
import json
from pathlib import Path


def generate(library):
    lib=C.CDLL(str(library))
    class Key(C.Structure):
        _fields_=[('words',C.c_uint32*60),('rounds',C.c_int)]
    lib.AES_set_encrypt_key.argtypes=[C.c_void_p,C.c_int,C.POINTER(Key)]
    lib.AES_ige_encrypt.argtypes=[C.c_void_p,C.c_void_p,C.c_size_t,C.POINTER(Key),C.c_void_p,C.c_int]
    lib.OpenSSL_version.restype=C.c_char_p
    fixtures=[]
    for size in (16,24,32):
        key=bytes(range(size)); iv=bytes(range(32)); plain=bytes((i*29+131)%256 for i in range(64))
        k=Key(); assert lib.AES_set_encrypt_key(key,size*8,C.byref(k))==0
        out=C.create_string_buffer(len(plain)); state=C.create_string_buffer(iv,32)
        lib.AES_ige_encrypt(plain,out,len(plain),C.byref(k),state,1)
        fixtures.append(dict(bits=size*8,key=key.hex(),iv=iv.hex(),plaintext=plain.hex(),
                             ciphertext=out.raw.hex(),final_iv=state.raw.hex()))
    return dict(generator='OpenSSL AES_set_encrypt_key + AES_ige_encrypt',
                library=str(library),library_sha256=hashlib.sha256(library.read_bytes()).hexdigest(),
                version=lib.OpenSSL_version(0).decode(),fixtures=fixtures)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--library',type=Path,default=Path('/opt/homebrew/opt/openssl@3/lib/libcrypto.dylib'))
    p.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'test/reference-vectors.json')
    a=p.parse_args();a.output.write_text(json.dumps(generate(a.library),indent=2)+'\n')
