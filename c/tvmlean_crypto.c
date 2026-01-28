#include <lean/lean.h>
#include <sodium.h>

static bool tvmlean_sodium_init(void) {
  static int initialized = 0;
  if (initialized) {
    return true;
  }
  if (sodium_init() < 0) {
    return false;
  }
  initialized = 1;
  return true;
}

LEAN_EXPORT uint8_t tvmlean_ed25519_verify(b_lean_obj_arg msg, b_lean_obj_arg pk, b_lean_obj_arg sig) {
  if (!tvmlean_sodium_init()) {
    return 0;
  }

  size_t msg_len = lean_sarray_size(msg);
  size_t pk_len = lean_sarray_size(pk);
  size_t sig_len = lean_sarray_size(sig);
  if (pk_len != 32 || sig_len != 64) {
    return 0;
  }

  const unsigned char *msg_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)msg);
  const unsigned char *pk_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)pk);
  const unsigned char *sig_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)sig);

  int rc = crypto_sign_ed25519_verify_detached(sig_bytes, msg_bytes, (unsigned long long)msg_len, pk_bytes);
  return rc == 0 ? 1 : 0;
}
