#include <lean/lean.h>
#include <sodium.h>

#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/ecdsa.h>
#include <openssl/evp.h>

#include <secp256k1.h>
#include <secp256k1_extrakeys.h>
#include <secp256k1_recovery.h>

#include <blst.h>

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

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
  if (len != 0 && buf != NULL) {
    memcpy(lean_sarray_cptr(out), buf, len);
  }
  return out;
}

static lean_obj_res tvmlean_empty_byte_array(void) {
  return tvmlean_mk_byte_array(NULL, 0);
}

static const secp256k1_context *tvmlean_secp256k1_ctx(void) {
  static secp256k1_context *ctx = NULL;
  if (ctx != NULL) {
    return ctx;
  }
  ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY);
  return ctx;
}

LEAN_EXPORT lean_obj_res tvmlean_secp256k1_ecrecover(b_lean_obj_arg hash32, b_lean_obj_arg sig65) {
  const secp256k1_context *ctx = tvmlean_secp256k1_ctx();
  if (ctx == NULL) {
    return tvmlean_empty_byte_array();
  }

  if (lean_sarray_size(hash32) != 32 || lean_sarray_size(sig65) != 65) {
    return tvmlean_empty_byte_array();
  }

  const unsigned char *hash = (const unsigned char *)lean_sarray_cptr((lean_object *)hash32);
  const unsigned char *sig = (const unsigned char *)lean_sarray_cptr((lean_object *)sig65);

  secp256k1_ecdsa_recoverable_signature signature;
  if (sig[64] > 3 ||
      !secp256k1_ecdsa_recoverable_signature_parse_compact(ctx, &signature, sig, (int)sig[64])) {
    return tvmlean_empty_byte_array();
  }

  secp256k1_pubkey pubkey;
  if (!secp256k1_ecdsa_recover(ctx, &pubkey, &signature, hash)) {
    return tvmlean_empty_byte_array();
  }

  unsigned char out[65];
  size_t out_len = sizeof(out);
  if (!secp256k1_ec_pubkey_serialize(ctx, out, &out_len, &pubkey, SECP256K1_EC_UNCOMPRESSED) || out_len != 65) {
    return tvmlean_empty_byte_array();
  }

  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_secp256k1_xonly_pubkey_tweak_add(b_lean_obj_arg key32, b_lean_obj_arg tweak32) {
  const secp256k1_context *ctx = tvmlean_secp256k1_ctx();
  if (ctx == NULL) {
    return tvmlean_empty_byte_array();
  }

  if (lean_sarray_size(key32) != 32 || lean_sarray_size(tweak32) != 32) {
    return tvmlean_empty_byte_array();
  }

  const unsigned char *key = (const unsigned char *)lean_sarray_cptr((lean_object *)key32);
  const unsigned char *tweak = (const unsigned char *)lean_sarray_cptr((lean_object *)tweak32);

  secp256k1_xonly_pubkey xonly_pubkey;
  if (!secp256k1_xonly_pubkey_parse(ctx, &xonly_pubkey, key)) {
    return tvmlean_empty_byte_array();
  }

  secp256k1_pubkey output_pubkey;
  if (!secp256k1_xonly_pubkey_tweak_add(ctx, &output_pubkey, &xonly_pubkey, tweak)) {
    return tvmlean_empty_byte_array();
  }

  unsigned char out[65];
  size_t out_len = sizeof(out);
  if (!secp256k1_ec_pubkey_serialize(ctx, out, &out_len, &output_pubkey, SECP256K1_EC_UNCOMPRESSED) || out_len != 65) {
    return tvmlean_empty_byte_array();
  }

  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT uint8_t tvmlean_p256_verify(b_lean_obj_arg data, b_lean_obj_arg pk33, b_lean_obj_arg sig64) {
  if (lean_sarray_size(pk33) != 33 || lean_sarray_size(sig64) != 64) {
    return 0;
  }

  const unsigned char *data_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)data);
  size_t data_len = lean_sarray_size(data);

  const unsigned char *pk_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)pk33);
  const unsigned char *sig_bytes = (const unsigned char *)lean_sarray_cptr((lean_object *)sig64);

  EVP_PKEY_CTX *pctx = EVP_PKEY_CTX_new_id(EVP_PKEY_EC, NULL);
  if (pctx == NULL) {
    return 0;
  }

  uint8_t ok = 0;
  EVP_PKEY *pkey = NULL;
  EVP_MD_CTX *md_ctx = NULL;
  ECDSA_SIG *sig = NULL;
  unsigned char *sig_der = NULL;

  do {
    if (EVP_PKEY_paramgen_init(pctx) <= 0) {
      break;
    }
    if (EVP_PKEY_CTX_set_ec_paramgen_curve_nid(pctx, NID_X9_62_prime256v1) <= 0) {
      break;
    }
    if (EVP_PKEY_paramgen(pctx, &pkey) <= 0 || pkey == NULL) {
      break;
    }
    if (EVP_PKEY_set1_tls_encodedpoint(pkey, pk_bytes, 33) <= 0) {
      break;
    }

    md_ctx = EVP_MD_CTX_new();
    if (md_ctx == NULL) {
      break;
    }
    if (EVP_DigestVerifyInit(md_ctx, NULL, EVP_sha256(), NULL, pkey) <= 0) {
      break;
    }

    sig = ECDSA_SIG_new();
    if (sig == NULL) {
      break;
    }
    unsigned char buf[33];
    buf[0] = 0;
    memcpy(buf + 1, sig_bytes, 32);
    BIGNUM *r = BN_bin2bn(buf, 33, NULL);
    memcpy(buf + 1, sig_bytes + 32, 32);
    BIGNUM *s = BN_bin2bn(buf, 33, NULL);
    if (r == NULL || s == NULL) {
      if (r != NULL) {
        BN_free(r);
      }
      if (s != NULL) {
        BN_free(s);
      }
      break;
    }
    if (ECDSA_SIG_set0(sig, r, s) != 1) {
      BN_free(r);
      BN_free(s);
      break;
    }

    int sig_der_len = i2d_ECDSA_SIG(sig, &sig_der);
    if (sig_der_len <= 0 || sig_der == NULL) {
      break;
    }

    if (EVP_DigestVerify(md_ctx, sig_der, (size_t)sig_der_len, data_bytes, data_len) == 1) {
      ok = 1;
    }
  } while (0);

  if (sig_der != NULL) {
    OPENSSL_free(sig_der);
  }
  if (sig != NULL) {
    ECDSA_SIG_free(sig);
  }
  if (md_ctx != NULL) {
    EVP_MD_CTX_free(md_ctx);
  }
  if (pkey != NULL) {
    EVP_PKEY_free(pkey);
  }
  EVP_PKEY_CTX_free(pctx);

  return ok;
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_from_hash(b_lean_obj_arg x1, b_lean_obj_arg x2) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_empty_byte_array();
  }
  if (lean_sarray_size(x1) != 32 || lean_sarray_size(x2) != 32) {
    return tvmlean_empty_byte_array();
  }

  const unsigned char *x1b = (const unsigned char *)lean_sarray_cptr((lean_object *)x1);
  const unsigned char *x2b = (const unsigned char *)lean_sarray_cptr((lean_object *)x2);

  unsigned char in[64];
  memcpy(in, x1b, 32);
  memcpy(in + 32, x2b, 32);

  unsigned char out[32];
  crypto_core_ristretto255_from_hash(out, in);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT uint8_t tvmlean_rist255_is_valid_point(b_lean_obj_arg x) {
  if (!tvmlean_sodium_init()) {
    return 0;
  }
  if (lean_sarray_size(x) != 32) {
    return 0;
  }
  const unsigned char *xb = (const unsigned char *)lean_sarray_cptr((lean_object *)x);
  return crypto_core_ristretto255_is_valid_point(xb) ? 1 : 0;
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_add(b_lean_obj_arg x, b_lean_obj_arg y) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_empty_byte_array();
  }
  if (lean_sarray_size(x) != 32 || lean_sarray_size(y) != 32) {
    return tvmlean_empty_byte_array();
  }

  const unsigned char *xb = (const unsigned char *)lean_sarray_cptr((lean_object *)x);
  const unsigned char *yb = (const unsigned char *)lean_sarray_cptr((lean_object *)y);
  unsigned char out[32];
  if (crypto_core_ristretto255_add(out, xb, yb) != 0) {
    return tvmlean_empty_byte_array();
  }
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_sub(b_lean_obj_arg x, b_lean_obj_arg y) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_empty_byte_array();
  }
  if (lean_sarray_size(x) != 32 || lean_sarray_size(y) != 32) {
    return tvmlean_empty_byte_array();
  }

  const unsigned char *xb = (const unsigned char *)lean_sarray_cptr((lean_object *)x);
  const unsigned char *yb = (const unsigned char *)lean_sarray_cptr((lean_object *)y);
  unsigned char out[32];
  if (crypto_core_ristretto255_sub(out, xb, yb) != 0) {
    return tvmlean_empty_byte_array();
  }
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_mul(b_lean_obj_arg n_le, b_lean_obj_arg x) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_empty_byte_array();
  }
  if (lean_sarray_size(n_le) != 32 || lean_sarray_size(x) != 32) {
    return tvmlean_empty_byte_array();
  }
  const unsigned char *nb = (const unsigned char *)lean_sarray_cptr((lean_object *)n_le);
  const unsigned char *xb = (const unsigned char *)lean_sarray_cptr((lean_object *)x);
  unsigned char out[32];
  if (crypto_scalarmult_ristretto255(out, nb, xb) != 0) {
    return tvmlean_empty_byte_array();
  }
  return tvmlean_mk_byte_array(out, sizeof(out));
}

static bool all_bytes_eq(const unsigned char *buf, size_t len, unsigned char value) {
  for (size_t i = 0; i < len; i++) {
    if (buf[i] != value) {
      return false;
    }
  }
  return true;
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_mul_base(b_lean_obj_arg n_le) {
  if (!tvmlean_sodium_init()) {
    return tvmlean_empty_byte_array();
  }
  if (lean_sarray_size(n_le) != 32) {
    return tvmlean_empty_byte_array();
  }
  const unsigned char *nb = (const unsigned char *)lean_sarray_cptr((lean_object *)n_le);

  unsigned char out[32];
  memset(out, 0xff, sizeof(out));
  if (crypto_scalarmult_ristretto255_base(out, nb) != 0) {
    if (all_bytes_eq(out, sizeof(out), 0xff)) {
      return tvmlean_empty_byte_array();
    }
  }
  return tvmlean_mk_byte_array(out, sizeof(out));
}

static const uint8_t tvmlean_bls_dst[] = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
static const size_t tvmlean_bls_dst_len = sizeof(tvmlean_bls_dst) - 1;

static void tvmlean_bls_g1_zero_bytes(uint8_t out[48]) {
  static int init = 0;
  static uint8_t z[48];
  if (!init) {
    blst_p1 p;
    memset(&p, 0, sizeof(p));
    blst_p1_compress(z, &p);
    init = 1;
  }
  memcpy(out, z, 48);
}

static void tvmlean_bls_g2_zero_bytes(uint8_t out[96]) {
  static int init = 0;
  static uint8_t z[96];
  if (!init) {
    blst_p2 p;
    memset(&p, 0, sizeof(p));
    blst_p2_compress(z, &p);
    init = 1;
  }
  memcpy(out, z, 96);
}

LEAN_EXPORT uint8_t tvmlean_bls_verify(b_lean_obj_arg pk48, b_lean_obj_arg msg, b_lean_obj_arg sig96) {
  if (lean_sarray_size(pk48) != 48 || lean_sarray_size(sig96) != 96) {
    return 0;
  }
  const uint8_t *pk_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)pk48);
  const uint8_t *sig_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)sig96);
  const uint8_t *msg_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)msg);
  size_t msg_len = lean_sarray_size(msg);

  blst_p1_affine pk;
  if (blst_p1_uncompress(&pk, pk_bytes) != BLST_SUCCESS) {
    return 0;
  }
  if (blst_p1_affine_is_inf(&pk)) {
    return 0;
  }
  blst_p2_affine sig;
  if (blst_p2_uncompress(&sig, sig_bytes) != BLST_SUCCESS) {
    return 0;
  }

  BLST_ERROR err = blst_core_verify_pk_in_g1(&pk, &sig, true, msg_bytes, msg_len, tvmlean_bls_dst, tvmlean_bls_dst_len, NULL, 0);
  return err == BLST_SUCCESS ? 1 : 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_aggregate(b_lean_obj_arg sigs_arr) {
  size_t n = lean_array_size(sigs_arr);
  if (n == 0) {
    return tvmlean_empty_byte_array();
  }

  blst_p2 acc;
  bool acc_set = false;

  for (size_t i = 0; i < n; i++) {
    lean_object *sig_ba = lean_array_get_core(sigs_arr, i);
    if (lean_sarray_size(sig_ba) != 96) {
      return tvmlean_empty_byte_array();
    }
    const uint8_t *sig_bytes = (const uint8_t *)lean_sarray_cptr(sig_ba);
    blst_p2_affine sig;
    if (blst_p2_uncompress(&sig, sig_bytes) != BLST_SUCCESS) {
      return tvmlean_empty_byte_array();
    }
    if (!acc_set) {
      blst_p2_from_affine(&acc, &sig);
      acc_set = true;
    } else {
      blst_p2_add_or_double_affine(&acc, &acc, &sig);
    }
  }

  uint8_t out[96];
  blst_p2_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT uint8_t tvmlean_bls_fast_aggregate_verify(b_lean_obj_arg pks_arr, b_lean_obj_arg msg, b_lean_obj_arg sig96) {
  size_t n = lean_array_size(pks_arr);
  if (n == 0) {
    return 0;
  }
  if (lean_sarray_size(sig96) != 96) {
    return 0;
  }

  const uint8_t *msg_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)msg);
  size_t msg_len = lean_sarray_size(msg);
  const uint8_t *sig_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)sig96);

  blst_p1 acc;
  bool acc_set = false;

  for (size_t i = 0; i < n; i++) {
    lean_object *pk_ba = lean_array_get_core(pks_arr, i);
    if (lean_sarray_size(pk_ba) != 48) {
      return 0;
    }
    const uint8_t *pk_bytes = (const uint8_t *)lean_sarray_cptr(pk_ba);
    blst_p1_affine pk;
    if (blst_p1_uncompress(&pk, pk_bytes) != BLST_SUCCESS) {
      return 0;
    }
    if (blst_p1_affine_is_inf(&pk)) {
      return 0;
    }
    if (!acc_set) {
      blst_p1_from_affine(&acc, &pk);
      acc_set = true;
    } else {
      blst_p1_add_or_double_affine(&acc, &acc, &pk);
    }
  }

  blst_p2_affine sig;
  if (blst_p2_uncompress(&sig, sig_bytes) != BLST_SUCCESS) {
    return 0;
  }

  blst_p1_affine agg_pk;
  blst_p1_to_affine(&agg_pk, &acc);

  BLST_ERROR err = blst_core_verify_pk_in_g1(&agg_pk, &sig, true, msg_bytes, msg_len, tvmlean_bls_dst, tvmlean_bls_dst_len, NULL, 0);
  return err == BLST_SUCCESS ? 1 : 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_aggregate_verify(b_lean_obj_arg pks_arr, b_lean_obj_arg msgs_arr, b_lean_obj_arg sig96) {
  size_t n = lean_array_size(pks_arr);
  if (n == 0) {
    return 0;
  }
  if (n != lean_array_size(msgs_arr)) {
    return 0;
  }
  if (lean_sarray_size(sig96) != 96) {
    return 0;
  }
  const uint8_t *sig_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)sig96);

  size_t ctx_size = blst_pairing_sizeof();
  blst_pairing *ctx = (blst_pairing *)malloc(ctx_size);
  if (ctx == NULL) {
    return 0;
  }
  blst_pairing_init(ctx, true, tvmlean_bls_dst, tvmlean_bls_dst_len);

  blst_p2_affine sig_zero;
  memset(&sig_zero, 0, sizeof(sig_zero));

  for (size_t i = 0; i < n; i++) {
    lean_object *pk_ba = lean_array_get_core(pks_arr, i);
    lean_object *msg_ba = lean_array_get_core(msgs_arr, i);
    if (lean_sarray_size(pk_ba) != 48) {
      free(ctx);
      return 0;
    }
    const uint8_t *pk_bytes = (const uint8_t *)lean_sarray_cptr(pk_ba);
    const uint8_t *msg_bytes = (const uint8_t *)lean_sarray_cptr(msg_ba);
    size_t msg_len = lean_sarray_size(msg_ba);

    blst_p1_affine pk;
    if (blst_p1_uncompress(&pk, pk_bytes) != BLST_SUCCESS) {
      free(ctx);
      return 0;
    }
    if (!blst_p1_affine_in_g1(&pk) || blst_p1_affine_is_inf(&pk)) {
      free(ctx);
      return 0;
    }
    if (blst_pairing_aggregate_pk_in_g1(ctx, &pk, &sig_zero, msg_bytes, msg_len, NULL, 0) != BLST_SUCCESS) {
      free(ctx);
      return 0;
    }
  }

  blst_pairing_commit(ctx);

  blst_p2_affine sig;
  if (blst_p2_uncompress(&sig, sig_bytes) != BLST_SUCCESS) {
    free(ctx);
    return 0;
  }
  if (!blst_p2_affine_in_g2(&sig)) {
    free(ctx);
    return 0;
  }

  blst_fp12 gtsig;
  blst_aggregated_in_g2(&gtsig, &sig);
  bool ok = blst_pairing_finalverify(ctx, &gtsig);

  free(ctx);
  return ok ? 1 : 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_add(b_lean_obj_arg a48, b_lean_obj_arg b48) {
  if (lean_sarray_size(a48) != 48 || lean_sarray_size(b48) != 48) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a48);
  const uint8_t *b_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)b48);

  blst_p1_affine a;
  blst_p1_affine b;
  if (blst_p1_uncompress(&a, a_bytes) != BLST_SUCCESS || blst_p1_uncompress(&b, b_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }

  blst_p1 acc;
  blst_p1_from_affine(&acc, &a);
  blst_p1_add_or_double_affine(&acc, &acc, &b);

  uint8_t out[48];
  blst_p1_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_sub(b_lean_obj_arg a48, b_lean_obj_arg b48) {
  if (lean_sarray_size(a48) != 48 || lean_sarray_size(b48) != 48) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a48);
  const uint8_t *b_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)b48);

  blst_p1_affine a;
  blst_p1_affine b;
  if (blst_p1_uncompress(&a, a_bytes) != BLST_SUCCESS || blst_p1_uncompress(&b, b_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }

  blst_p1 acc;
  blst_p1_from_affine(&acc, &b);
  blst_p1_cneg(&acc, true);
  blst_p1_add_or_double_affine(&acc, &acc, &a);

  uint8_t out[48];
  blst_p1_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_neg(b_lean_obj_arg a48) {
  if (lean_sarray_size(a48) != 48) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a48);
  blst_p1_affine a;
  if (blst_p1_uncompress(&a, a_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }
  blst_p1 acc;
  blst_p1_from_affine(&acc, &a);
  blst_p1_cneg(&acc, true);
  uint8_t out[48];
  blst_p1_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_mul(b_lean_obj_arg p48, b_lean_obj_arg scalar32_be) {
  if (lean_sarray_size(p48) != 48 || lean_sarray_size(scalar32_be) != 32) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p48);
  const uint8_t *x_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)scalar32_be);

  blst_p1_affine p_aff;
  if (blst_p1_uncompress(&p_aff, p_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }
  blst_p1 p;
  blst_p1_from_affine(&p, &p_aff);

  blst_scalar x;
  (void)blst_scalar_from_be_bytes(&x, x_bytes, 32);
  blst_p1_mult(&p, &p, x.b, 255);

  uint8_t out[48];
  blst_p1_compress(out, &p);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_multiexp(b_lean_obj_arg points_arr, b_lean_obj_arg scalars_arr) {
  size_t n = lean_array_size(points_arr);
  if (n == 0 || n != lean_array_size(scalars_arr)) {
    return tvmlean_empty_byte_array();
  }

  blst_p1_affine *points = (blst_p1_affine *)malloc(sizeof(blst_p1_affine) * n);
  const blst_p1_affine **point_ptrs = (const blst_p1_affine **)malloc(sizeof(blst_p1_affine *) * n);
  uint8_t *scalar_bytes = (uint8_t *)malloc(32 * n);
  const uint8_t **scalar_ptrs = (const uint8_t **)malloc(sizeof(uint8_t *) * n);
  limb_t *scratch = NULL;

  if (points == NULL || point_ptrs == NULL || scalar_bytes == NULL || scalar_ptrs == NULL) {
    free(points);
    free(point_ptrs);
    free(scalar_bytes);
    free(scalar_ptrs);
    return tvmlean_empty_byte_array();
  }

  for (size_t i = 0; i < n; i++) {
    lean_object *p_ba = lean_array_get_core(points_arr, i);
    lean_object *x_ba = lean_array_get_core(scalars_arr, i);
    if (lean_sarray_size(p_ba) != 48 || lean_sarray_size(x_ba) != 32) {
      free(points);
      free(point_ptrs);
      free(scalar_bytes);
      free(scalar_ptrs);
      return tvmlean_empty_byte_array();
    }
    const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr(p_ba);
    const uint8_t *x_le = (const uint8_t *)lean_sarray_cptr(x_ba);
    if (blst_p1_uncompress(&points[i], p_bytes) != BLST_SUCCESS) {
      free(points);
      free(point_ptrs);
      free(scalar_bytes);
      free(scalar_ptrs);
      return tvmlean_empty_byte_array();
    }
    memcpy(scalar_bytes + 32 * i, x_le, 32);
    point_ptrs[i] = &points[i];
    scalar_ptrs[i] = scalar_bytes + 32 * i;
  }

  size_t scratch_sz = blst_p1s_mult_pippenger_scratch_sizeof(n);
  scratch = (limb_t *)malloc(scratch_sz);
  if (scratch == NULL) {
    free(points);
    free(point_ptrs);
    free(scalar_bytes);
    free(scalar_ptrs);
    return tvmlean_empty_byte_array();
  }

  blst_p1 ret;
  blst_p1s_mult_pippenger(&ret, point_ptrs, n, scalar_ptrs, 256, scratch);

  uint8_t out[48];
  blst_p1_compress(out, &ret);

  free(scratch);
  free(points);
  free(point_ptrs);
  free(scalar_bytes);
  free(scalar_ptrs);

  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_zero(b_lean_obj_arg unit) {
  (void)unit;
  uint8_t out[48];
  tvmlean_bls_g1_zero_bytes(out);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_map_to_g1(b_lean_obj_arg fp48) {
  if (lean_sarray_size(fp48) != 48) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *fp_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)fp48);
  blst_fp fp;
  blst_fp_from_bendian(&fp, fp_bytes);
  blst_p1 p;
  blst_map_to_g1(&p, &fp, NULL);
  uint8_t out[48];
  blst_p1_compress(out, &p);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT uint8_t tvmlean_bls_g1_in_group(b_lean_obj_arg p48) {
  if (lean_sarray_size(p48) != 48) {
    return 0;
  }
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p48);
  blst_p1_affine p;
  if (blst_p1_uncompress(&p, p_bytes) != BLST_SUCCESS) {
    return 0;
  }
  return blst_p1_affine_in_g1(&p) ? 1 : 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_g1_is_zero(b_lean_obj_arg p48) {
  if (lean_sarray_size(p48) != 48) {
    return 0;
  }
  uint8_t z[48];
  tvmlean_bls_g1_zero_bytes(z);
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p48);
  return memcmp(z, p_bytes, 48) == 0 ? 1 : 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_add(b_lean_obj_arg a96, b_lean_obj_arg b96) {
  if (lean_sarray_size(a96) != 96 || lean_sarray_size(b96) != 96) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a96);
  const uint8_t *b_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)b96);

  blst_p2_affine a;
  blst_p2_affine b;
  if (blst_p2_uncompress(&a, a_bytes) != BLST_SUCCESS || blst_p2_uncompress(&b, b_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }

  blst_p2 acc;
  blst_p2_from_affine(&acc, &a);
  blst_p2_add_or_double_affine(&acc, &acc, &b);

  uint8_t out[96];
  blst_p2_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_sub(b_lean_obj_arg a96, b_lean_obj_arg b96) {
  if (lean_sarray_size(a96) != 96 || lean_sarray_size(b96) != 96) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a96);
  const uint8_t *b_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)b96);

  blst_p2_affine a;
  blst_p2_affine b;
  if (blst_p2_uncompress(&a, a_bytes) != BLST_SUCCESS || blst_p2_uncompress(&b, b_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }

  blst_p2 acc;
  blst_p2_from_affine(&acc, &b);
  blst_p2_cneg(&acc, true);
  blst_p2_add_or_double_affine(&acc, &acc, &a);

  uint8_t out[96];
  blst_p2_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_neg(b_lean_obj_arg a96) {
  if (lean_sarray_size(a96) != 96) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *a_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)a96);
  blst_p2_affine a;
  if (blst_p2_uncompress(&a, a_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }
  blst_p2 acc;
  blst_p2_from_affine(&acc, &a);
  blst_p2_cneg(&acc, true);
  uint8_t out[96];
  blst_p2_compress(out, &acc);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_mul(b_lean_obj_arg p96, b_lean_obj_arg scalar32_be) {
  if (lean_sarray_size(p96) != 96 || lean_sarray_size(scalar32_be) != 32) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p96);
  const uint8_t *x_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)scalar32_be);

  blst_p2_affine p_aff;
  if (blst_p2_uncompress(&p_aff, p_bytes) != BLST_SUCCESS) {
    return tvmlean_empty_byte_array();
  }
  blst_p2 p;
  blst_p2_from_affine(&p, &p_aff);

  blst_scalar x;
  (void)blst_scalar_from_be_bytes(&x, x_bytes, 32);
  blst_p2_mult(&p, &p, x.b, 255);

  uint8_t out[96];
  blst_p2_compress(out, &p);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_multiexp(b_lean_obj_arg points_arr, b_lean_obj_arg scalars_arr) {
  size_t n = lean_array_size(points_arr);
  if (n == 0 || n != lean_array_size(scalars_arr)) {
    return tvmlean_empty_byte_array();
  }

  blst_p2_affine *points = (blst_p2_affine *)malloc(sizeof(blst_p2_affine) * n);
  const blst_p2_affine **point_ptrs = (const blst_p2_affine **)malloc(sizeof(blst_p2_affine *) * n);
  uint8_t *scalar_bytes = (uint8_t *)malloc(32 * n);
  const uint8_t **scalar_ptrs = (const uint8_t **)malloc(sizeof(uint8_t *) * n);
  limb_t *scratch = NULL;

  if (points == NULL || point_ptrs == NULL || scalar_bytes == NULL || scalar_ptrs == NULL) {
    free(points);
    free(point_ptrs);
    free(scalar_bytes);
    free(scalar_ptrs);
    return tvmlean_empty_byte_array();
  }

  for (size_t i = 0; i < n; i++) {
    lean_object *p_ba = lean_array_get_core(points_arr, i);
    lean_object *x_ba = lean_array_get_core(scalars_arr, i);
    if (lean_sarray_size(p_ba) != 96 || lean_sarray_size(x_ba) != 32) {
      free(points);
      free(point_ptrs);
      free(scalar_bytes);
      free(scalar_ptrs);
      return tvmlean_empty_byte_array();
    }
    const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr(p_ba);
    const uint8_t *x_le = (const uint8_t *)lean_sarray_cptr(x_ba);
    if (blst_p2_uncompress(&points[i], p_bytes) != BLST_SUCCESS) {
      free(points);
      free(point_ptrs);
      free(scalar_bytes);
      free(scalar_ptrs);
      return tvmlean_empty_byte_array();
    }
    memcpy(scalar_bytes + 32 * i, x_le, 32);
    point_ptrs[i] = &points[i];
    scalar_ptrs[i] = scalar_bytes + 32 * i;
  }

  size_t scratch_sz = blst_p2s_mult_pippenger_scratch_sizeof(n);
  scratch = (limb_t *)malloc(scratch_sz);
  if (scratch == NULL) {
    free(points);
    free(point_ptrs);
    free(scalar_bytes);
    free(scalar_ptrs);
    return tvmlean_empty_byte_array();
  }

  blst_p2 ret;
  blst_p2s_mult_pippenger(&ret, point_ptrs, n, scalar_ptrs, 256, scratch);

  uint8_t out[96];
  blst_p2_compress(out, &ret);

  free(scratch);
  free(points);
  free(point_ptrs);
  free(scalar_bytes);
  free(scalar_ptrs);

  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_zero(b_lean_obj_arg unit) {
  (void)unit;
  uint8_t out[96];
  tvmlean_bls_g2_zero_bytes(out);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT lean_obj_res tvmlean_bls_map_to_g2(b_lean_obj_arg fp2_96) {
  if (lean_sarray_size(fp2_96) != 96) {
    return tvmlean_empty_byte_array();
  }
  const uint8_t *fp_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)fp2_96);
  blst_fp2 fp2;
  blst_fp_from_bendian(&fp2.fp[0], fp_bytes);
  blst_fp_from_bendian(&fp2.fp[1], fp_bytes + 48);
  blst_p2 p;
  blst_map_to_g2(&p, &fp2, NULL);
  uint8_t out[96];
  blst_p2_compress(out, &p);
  return tvmlean_mk_byte_array(out, sizeof(out));
}

LEAN_EXPORT uint8_t tvmlean_bls_g2_in_group(b_lean_obj_arg p96) {
  if (lean_sarray_size(p96) != 96) {
    return 0;
  }
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p96);
  blst_p2_affine p;
  if (blst_p2_uncompress(&p, p_bytes) != BLST_SUCCESS) {
    return 0;
  }
  return blst_p2_affine_in_g2(&p) ? 1 : 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_g2_is_zero(b_lean_obj_arg p96) {
  if (lean_sarray_size(p96) != 96) {
    return 0;
  }
  uint8_t z[96];
  tvmlean_bls_g2_zero_bytes(z);
  const uint8_t *p_bytes = (const uint8_t *)lean_sarray_cptr((lean_object *)p96);
  return memcmp(z, p_bytes, 96) == 0 ? 1 : 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_pairing(b_lean_obj_arg p1_arr, b_lean_obj_arg p2_arr) {
  size_t n = lean_array_size(p1_arr);
  if (n != lean_array_size(p2_arr)) {
    return 2;
  }

  size_t ctx_size = blst_pairing_sizeof();
  blst_pairing *ctx = (blst_pairing *)malloc(ctx_size);
  if (ctx == NULL) {
    return 2;
  }
  blst_pairing_init(ctx, true, tvmlean_bls_dst, tvmlean_bls_dst_len);

  for (size_t i = 0; i < n; i++) {
    lean_object *p1_ba = lean_array_get_core(p1_arr, i);
    lean_object *p2_ba = lean_array_get_core(p2_arr, i);
    if (lean_sarray_size(p1_ba) != 48 || lean_sarray_size(p2_ba) != 96) {
      free(ctx);
      return 2;
    }
    const uint8_t *p1_bytes = (const uint8_t *)lean_sarray_cptr(p1_ba);
    const uint8_t *p2_bytes = (const uint8_t *)lean_sarray_cptr(p2_ba);

    blst_p1_affine p1;
    blst_p2_affine p2;
    if (blst_p1_uncompress(&p1, p1_bytes) != BLST_SUCCESS || blst_p2_uncompress(&p2, p2_bytes) != BLST_SUCCESS) {
      free(ctx);
      return 2;
    }

    blst_pairing_raw_aggregate(ctx, &p2, &p1);
  }

  blst_pairing_commit(ctx);
  bool ok = blst_pairing_finalverify(ctx, NULL);
  free(ctx);
  return ok ? 1 : 0;
}
