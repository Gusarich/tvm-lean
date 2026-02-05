#include <lean/lean.h>

#include <stddef.h>
#include <stdint.h>

static lean_obj_res tvmlean_empty_byte_array(void) {
  return lean_alloc_sarray(1, 0, 0);
}

LEAN_EXPORT lean_obj_res tvmlean_secp256k1_ecrecover(b_lean_obj_arg hash32, b_lean_obj_arg sig65) {
  (void)hash32;
  (void)sig65;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_secp256k1_xonly_pubkey_tweak_add(b_lean_obj_arg key32, b_lean_obj_arg tweak32) {
  (void)key32;
  (void)tweak32;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_p256_verify(b_lean_obj_arg data, b_lean_obj_arg pk33, b_lean_obj_arg sig64) {
  (void)data;
  (void)pk33;
  (void)sig64;
  return 0;
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_from_hash(b_lean_obj_arg x1, b_lean_obj_arg x2) {
  (void)x1;
  (void)x2;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_rist255_is_valid_point(b_lean_obj_arg x) {
  (void)x;
  return 0;
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_add(b_lean_obj_arg x, b_lean_obj_arg y) {
  (void)x;
  (void)y;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_sub(b_lean_obj_arg x, b_lean_obj_arg y) {
  (void)x;
  (void)y;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_mul(b_lean_obj_arg n_le, b_lean_obj_arg x) {
  (void)n_le;
  (void)x;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_rist255_mul_base(b_lean_obj_arg n_le) {
  (void)n_le;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_bls_verify(b_lean_obj_arg pk48, b_lean_obj_arg msg, b_lean_obj_arg sig96) {
  (void)pk48;
  (void)msg;
  (void)sig96;
  return 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_aggregate(b_lean_obj_arg sigs_arr) {
  (void)sigs_arr;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_bls_fast_aggregate_verify(b_lean_obj_arg pks_arr, b_lean_obj_arg msg, b_lean_obj_arg sig96) {
  (void)pks_arr;
  (void)msg;
  (void)sig96;
  return 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_aggregate_verify(b_lean_obj_arg pks_arr, b_lean_obj_arg msgs_arr, b_lean_obj_arg sig96) {
  (void)pks_arr;
  (void)msgs_arr;
  (void)sig96;
  return 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_add(b_lean_obj_arg a48, b_lean_obj_arg b48) {
  (void)a48;
  (void)b48;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_sub(b_lean_obj_arg a48, b_lean_obj_arg b48) {
  (void)a48;
  (void)b48;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_neg(b_lean_obj_arg a48) {
  (void)a48;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_mul(b_lean_obj_arg p48, b_lean_obj_arg scalar32_be) {
  (void)p48;
  (void)scalar32_be;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_multiexp(b_lean_obj_arg points_arr, b_lean_obj_arg scalars_arr) {
  (void)points_arr;
  (void)scalars_arr;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g1_zero(b_lean_obj_arg unit) {
  (void)unit;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_map_to_g1(b_lean_obj_arg fp48) {
  (void)fp48;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_bls_g1_in_group(b_lean_obj_arg p48) {
  (void)p48;
  return 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_g1_is_zero(b_lean_obj_arg p48) {
  (void)p48;
  return 0;
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_add(b_lean_obj_arg a96, b_lean_obj_arg b96) {
  (void)a96;
  (void)b96;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_sub(b_lean_obj_arg a96, b_lean_obj_arg b96) {
  (void)a96;
  (void)b96;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_neg(b_lean_obj_arg a96) {
  (void)a96;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_mul(b_lean_obj_arg p96, b_lean_obj_arg scalar32_be) {
  (void)p96;
  (void)scalar32_be;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_multiexp(b_lean_obj_arg points_arr, b_lean_obj_arg scalars_arr) {
  (void)points_arr;
  (void)scalars_arr;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_g2_zero(b_lean_obj_arg unit) {
  (void)unit;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT lean_obj_res tvmlean_bls_map_to_g2(b_lean_obj_arg fp2_96) {
  (void)fp2_96;
  return tvmlean_empty_byte_array();
}

LEAN_EXPORT uint8_t tvmlean_bls_g2_in_group(b_lean_obj_arg p96) {
  (void)p96;
  return 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_g2_is_zero(b_lean_obj_arg p96) {
  (void)p96;
  return 0;
}

LEAN_EXPORT uint8_t tvmlean_bls_pairing(b_lean_obj_arg p1_arr, b_lean_obj_arg p2_arr) {
  (void)p1_arr;
  (void)p2_arr;
  return 0;
}

