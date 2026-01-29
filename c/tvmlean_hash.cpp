#include <lean/lean.h>
#include <sodium.h>

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#include "keccak.h"

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

static lean_obj_res tvmlean_mk_byte_array(const unsigned char *buf, size_t len) {
  lean_object *out = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(out), buf, len);
  return out;
}

extern "C" LEAN_EXPORT lean_obj_res tvmlean_hash_sha256(b_lean_obj_arg msg) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_mk_byte_array(NULL, 0);
  }
  size_t msg_len = lean_sarray_size(msg);
  const unsigned char *msg_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)msg);

  unsigned char out[crypto_hash_sha256_BYTES];
  crypto_hash_sha256(out, msg_bytes, (unsigned long long)msg_len);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

extern "C" LEAN_EXPORT lean_obj_res tvmlean_hash_sha512(b_lean_obj_arg msg) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_mk_byte_array(NULL, 0);
  }
  size_t msg_len = lean_sarray_size(msg);
  const unsigned char *msg_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)msg);

  unsigned char out[crypto_hash_sha512_BYTES];
  crypto_hash_sha512(out, msg_bytes, (unsigned long long)msg_len);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

extern "C" LEAN_EXPORT lean_obj_res tvmlean_hash_blake2b(b_lean_obj_arg msg) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_mk_byte_array(NULL, 0);
  }
  size_t msg_len = lean_sarray_size(msg);
  const unsigned char *msg_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)msg);

  unsigned char out[64];
  crypto_generichash(out, sizeof(out), msg_bytes, (unsigned long long)msg_len, NULL, 0);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

static lean_obj_res tvmlean_keccak_hash(b_lean_obj_arg msg, size_t out_len) {
  size_t msg_len = lean_sarray_size(msg);
  const uint8_t *msg_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)msg);

  keccak_state *st = NULL;
  if (keccak_init(&st, /* capacity_bytes = */ out_len * 2, /* rounds = */ 24) != 0 || st == NULL) {
    return tvmlean_mk_byte_array(NULL, 0);
  }

  if (keccak_absorb(st, msg_bytes, msg_len) != 0) {
    keccak_destroy(st);
    return tvmlean_mk_byte_array(NULL, 0);
  }

  unsigned char out[64];
  if (out_len > sizeof(out)) {
    keccak_destroy(st);
    return tvmlean_mk_byte_array(NULL, 0);
  }
  if (keccak_digest(st, out, out_len, /* padding = */ 1) != 0) {
    keccak_destroy(st);
    return tvmlean_mk_byte_array(NULL, 0);
  }
  keccak_destroy(st);
  return tvmlean_mk_byte_array(out, out_len);
}

extern "C" LEAN_EXPORT lean_obj_res tvmlean_hash_keccak256(b_lean_obj_arg msg) {
  return tvmlean_keccak_hash(msg, 32);
}

extern "C" LEAN_EXPORT lean_obj_res tvmlean_hash_keccak512(b_lean_obj_arg msg) {
  return tvmlean_keccak_hash(msg, 64);
}

