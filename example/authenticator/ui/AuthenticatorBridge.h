#ifndef AUTHENTICATOR_BRIDGE_H
#define AUTHENTICATOR_BRIDGE_H
#include <stdint.h>
#include <stddef.h>
typedef struct AuthSession AuthSession;
/* One owning opaque handle per independent session. Destroy exactly once,
   after all users finish; never call with a stale or foreign handle. Calls are
   serialized internally. Returned metadata excludes decoded secret bytes. */
AuthSession *auth_session_create(void);
int64_t auth_session_destroy(AuthSession *session);
/* Operations: 1 add, 2 list, 3 read, 4 rename, 5 remove, 6 code, 7 remaining.
   p contains 471 Int64 words: id,timestamp,digits,period,labelLen,issuerLen,
   secretLen,label[128],issuer[128],secret[208]. Bytes occupy whole Int64 words.
   list needs out[16]; read needs out[260]: digits,period,labelLen,issuerLen,
   label[128],issuer[128]. Other operations need no output. All buffers are
   borrowed only for this synchronous call. No runtime objects cross this ABI.
   Returns the core result (add: positive id/-1 invalid/-2 full/-3 exhausted;
   list: count; read/rename/remove: 1 success/0 rejected; code: numeric or -1;
   remaining: seconds or -1). -10 means bridge/runtime/shape failure, before
   core dispatch where possible. Allocation success is a core assumption. */
int64_t auth_session_call(AuthSession *session,int64_t op,const int64_t *p,
                          size_t p_count,int64_t *out,size_t out_count);
#endif
