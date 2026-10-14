/* OpenSSL's native packed-byte IGE API; timing boundaries match Cangjie. */
#define OPENSSL_SUPPRESS_DEPRECATED
#include <openssl/aes.h>
#include <openssl/crypto.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void require(int ok) { if (!ok) { fputs("validation failed\n", stderr); exit(1); } }
static uint64_t now_ns(void) {
    struct timespec t;
    require(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
    return (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
}
static void reset_iv(unsigned char iv[32]) { for (int i=0; i<32; ++i) iv[i]=(unsigned char)i; }
static uint64_t byte_sum(const unsigned char *p, size_t n) {
    uint64_t s=0; for (size_t i=0; i<n; ++i) s+=p[i]; return s;
}
typedef struct {
    unsigned char key[32], iv[32];
    unsigned char *src, *dst;
    AES_KEY schedule;
    int bits, direction, expansion;
    size_t n;
} Work;
static uint64_t work(Work *w) {
    if (w->expansion) {
        require(AES_set_encrypt_key(w->key, w->bits, &w->schedule)==0);
        require(w->schedule.rounds==w->bits/32+6);
        return byte_sum((const unsigned char *)w->schedule.rd_key,
                        (size_t)(w->schedule.rounds+1)*16);
    }
    reset_iv(w->iv);
    AES_ige_encrypt(w->src,w->dst,w->n,&w->schedule,w->iv,w->direction);
    return byte_sum(w->dst,w->n);
}
static void bench(const char *name, Work *w, uint64_t expected) {
    require(work(w)==expected); require(work(w)==expected);
    uint64_t reps=1;
    for (;;) {
        uint64_t start=now_ns(), sum=0;
        for (uint64_t i=0; i<reps; ++i) sum+=work(w);
        uint64_t elapsed=now_ns()-start;
        require(sum==expected*reps);
        printf("CAL,%llu,%llu\n",(unsigned long long)reps,(unsigned long long)sum);
        if (elapsed>=20000000 || reps>=16777216) break;
        reps*=2;
    }
    for (int t=0; t<7; ++t) {
        uint64_t start=now_ns(), sum=0;
        for (uint64_t i=0; i<reps; ++i) sum+=work(w);
        uint64_t elapsed=now_ns()-start;
        require(sum==expected*reps);
        printf("BENCH,%s,OpenSSL,%zu,%d,%llu,%llu,%llu\n",name,w->n,t,
               (unsigned long long)elapsed,
               (unsigned long long)(reps*(w->expansion?1:w->n)),
               (unsigned long long)sum);
    }
}
static void dump(const char *direction, int bits, size_t n,
                 const unsigned char *out, size_t length) {
    for (size_t i=0; i<length; i+=16) {
        printf("VERIFY,%d,%zu,%s,%zu",bits,n,direction,i);
        for (size_t j=i; j<i+16; ++j) printf(",%u",out[j]);
        putchar('\n');
    }
}
int main(int argc, char **argv) {
    int verify=argc==2 && strcmp(argv[1],"--verify")==0;
    const size_t sizes[]={16,1024,65536};
    const uint64_t expected_key[]={22008,23558,28276};
    const uint64_t expected_enc[3][3]={{2014,129590,8336742},{2070,128279,8366608},{2114,132608,8363389}};
    const uint64_t expected_dec[]={2248,130560,8355840};
    if (!verify) fprintf(stderr,"%s\n",OpenSSL_version(OPENSSL_VERSION));
    for (int k=0; k<3; ++k) {
        int bits=128+64*k;
        Work w={0}; w.bits=bits; w.n=(size_t)bits/8; w.expansion=1;
        for (size_t i=0; i<w.n; ++i) w.key[i]=(unsigned char)i;
        char name[32]; snprintf(name,sizeof(name),"key_%d",bits);
        if (!verify) bench(name,&w,expected_key[k]);
        for (int s=0; s<3; ++s) {
            size_t n=sizes[s];
            unsigned char *plain=malloc(n), *cipher=malloc(n), *out=malloc(n);
            require(plain && cipher && out);
            for (size_t i=0; i<n; ++i) plain[i]=(unsigned char)(i*29+131);
            w.n=n; w.expansion=0; w.src=plain; w.dst=cipher; w.direction=AES_ENCRYPT;
            require(AES_set_encrypt_key(w.key,bits,&w.schedule)==0);
            require(work(&w)==expected_enc[k][s]);
            w.dst=out;
            if (verify) {
                require(work(&w)==expected_enc[k][s]);
                require(memcmp(out,cipher,n)==0);
                dump("encrypt",bits,n,out,n); dump("encrypt_iv",bits,n,w.iv,32);
            } else {
                snprintf(name,sizeof(name),"encrypt_%d",bits); bench(name,&w,expected_enc[k][s]);
            }
            w.src=cipher; w.direction=AES_DECRYPT;
            require(AES_set_decrypt_key(w.key,bits,&w.schedule)==0);
            if (verify) {
                require(work(&w)==expected_dec[s]); require(memcmp(out,plain,n)==0);
                dump("decrypt",bits,n,out,n); dump("decrypt_iv",bits,n,w.iv,32);
            } else {
                snprintf(name,sizeof(name),"decrypt_%d",bits); bench(name,&w,expected_dec[s]);
            }
            free(plain); free(cipher); free(out);
        }
    }
    return 0;
}
