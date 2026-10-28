// Runtime adapter for pinned Cangjie 1.0.5. Cangjie runs only on CJ tasks.
#include "AuthenticatorBridge.h"
#include "Cangjie.h"
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
extern int64_t *authenticatorCreate(void);
extern int64_t authenticatorDispatch(int64_t,int64_t *,int64_t *,int64_t *);
struct AuthSession { int64_t *core; };
static pthread_once_t once=PTHREAD_ONCE_INIT;
static pthread_mutex_t calls=PTHREAD_MUTEX_INITIALIZER;
static int ready=0;
static void initialize(void) {
    struct RuntimeParam p={0}; p.logParam.logLevel=RTLOG_ERROR;
    ready=InitCJRuntime(&p)==0 && InitCJLibrary(AUTH_LIBRARY)==0;
}
struct Task {
    pthread_mutex_t mutex; pthread_cond_t condition; int done;
    int64_t op; int64_t *session; int64_t *p; int64_t *out;
    int64_t result; int64_t *created;
};
static void *execute(void *arg) {
    struct Task *t=arg;
    if(t->op==-1) t->created=authenticatorCreate();
    else t->result=authenticatorDispatch(t->op,t->session,t->p,t->out);
    pthread_mutex_lock(&t->mutex); t->done=1;
    pthread_cond_signal(&t->condition); pthread_mutex_unlock(&t->mutex);
    return NULL;
}
static int perform(struct Task *t) {
    pthread_once(&once,initialize); if(!ready)return 0;
    pthread_mutex_init(&t->mutex,NULL);pthread_cond_init(&t->condition,NULL);
    CJThreadHandle task=RunCJTask(execute,t);
    if(task) {
        pthread_mutex_lock(&t->mutex);
        while(!t->done)pthread_cond_wait(&t->condition,&t->mutex);
        pthread_mutex_unlock(&t->mutex);ReleaseHandle(task);
    }
    pthread_cond_destroy(&t->condition);pthread_mutex_destroy(&t->mutex);
    return task!=NULL;
}
AuthSession *auth_session_create(void) {
    AuthSession *s=calloc(1,sizeof(*s)); if(!s)return NULL;
    struct Task t={.op=-1}; pthread_mutex_lock(&calls);
    int ok=perform(&t); pthread_mutex_unlock(&calls);
    if(!ok || !t.created){free(s);return NULL;} s->core=t.created;return s;
}
int64_t auth_session_destroy(AuthSession *s) {
    if(!s)return -10;
    struct Task t={.op=0,.session=s->core};pthread_mutex_lock(&calls);
    int ok=perform(&t);pthread_mutex_unlock(&calls);
    if(ok && t.result==0){s->core=NULL;free(s);}return ok?t.result:-10;
}
int64_t auth_session_call(AuthSession *s,int64_t op,const int64_t *p,size_t n,int64_t *out,size_t cap) {
    if(!s || !s->core || op<1 || op>7 || !p || n!=471)return -10;
    size_t need=op==2?16:op==3?260:0;
    if(cap<need || (need && !out))return -10;
    // Ensure the core cannot read outside fixed ABI fields, even on rejection.
    if((op==1 || op==4) && (p[4]<0 || p[4]>128 || p[5]<0 || p[5]>128))return -10;
    if(op==1 && (p[6]<0 || p[6]>208))return -10;
    int64_t copy[471];memcpy(copy,p,sizeof(copy));
    struct Task t={.op=op,.session=s->core,.p=copy,.out=out};
    pthread_mutex_lock(&calls);int ok=perform(&t);pthread_mutex_unlock(&calls);
    memset_s(copy,sizeof(copy),0,sizeof(copy));return ok?t.result:-10;
}
