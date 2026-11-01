#!/usr/bin/env python3
"""Evaluate the generated Nat cost expressions independently of Lean.

Diagnostic arithmetic, not a substitute for a Lean equality proof. No eval,
native_decide, or generated proof assumptions are involved.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]


W = 31104957928
R10_LOOP_OVERRIDES = {
    ("rlp_be_len", 0): ("MONO", 8, "w >>= 8 up to 8 bytes"),
    ("fq12_mul", 1): ("CTR", 12, "i < 12"),
    ("fq12_sqr", 1): ("CTR", 22, "i < 22"),
    ("modinv_bin", 0): ("MONO", 513, "u,v bitshift reduction <= 513"),
    ("modinv_bin", 1): ("MONO", 256, "even shift <= 256"),
    ("modinv_bin", 2): ("MONO", 256, "even shift <= 256"),
    ("bls_fp_inv_raw", 0): ("MONO", 769, "u,v bitshift reduction <= 769"),
    ("bls_fp_inv_raw", 1): ("MONO", 384, "even shift <= 384"),
    ("bls_fp_inv_raw", 2): ("MONO", 384, "even shift <= 384"),
    ("p256_fp_mul", 0): ("MONO", 2**65, "carry loop"),
    ("p256_fp_mul", 1): ("MONO", 2**64, "reduce loop"),
    ("p256_fp_sqr", 0): ("MONO", 2**65, "carry loop"),
    ("p256_fp_sqr", 1): ("MONO", 2**64, "reduce loop"),
    ("divmnu", 4): ("MONO", 3, "Knuth D3 qhat correction <= 2"),
    ("bn_divmnu", 4): ("MONO", 3, "Knuth D3 qhat correction <= 2"),
    ("_node_rlp_fill", 1): ("CTR", 16, "branch children i < 16"),
    ("bn254_miller_raw", 0): ("CTR", 64, "64-bit loop counter"),
    ("fq12_reduce", 0): ("CTR", 11, "i < 11"),
    ("fq_mul_small", 0): ("CTR", 64, "bit_length64 <= 64"),
    ("pair_miller_loop", 0): ("CTR", 63, "63-bit miller loop"),
    ("fp12_pow_absx", 0): ("CTR", 64, "64-bit exponent"),
    ("fp_pow", 0): ("CTR", 256, "256-bit exponent"),
    ("div64by32", 0): ("CTR", 32, "32-bit shift-subtract"),
    ("udivmod", 0): ("CTR", 64, "64-bit shift-subtract"),
    ("ecp_mul", 0): ("CTR", 256, "u256_bit_length <= 256"),
    ("htab_first_diff", 0): ("WALK", W + 1, "loadsByte a + i in ordinaryDomain"),
    ("htab_first_diff", 1): ("CTR", 8, "j < 8"),
    # Legacy stride coefficients below are normalized after the manifest.
    # The justification there counts residues, including modular wraparound.
    ("rlp_read_length", 0): ("WALK", W + 1, "loadsByte p + i"),
    ("rlp_list_count", 0): ("WALK", W + 1, "advances off >= 1 and loads p + off"),
    ("_rlp_validate_items_body", 0): ("STACK", 2 * W + 2, "pushes 24B on scratch or advances pos"),
    ("_decode_witness_node_body", 0): ("GUARD", (W // 88 + 2) * 64, "arena nodes * nibble depth"),
    ("trie_walk", 0): ("RO(2)", (W // 8 + 2) * 2**64, "pos walk"),
    ("htab_set", 0): ("RO(2)", (W // 8 + 2) * 2, "tree depth <= cnt <= W/8"),
    ("_mpt_insert_node", 0): ("GUARD", 2**66, "nibble depth <= 64"),
    ("_mpt_delete_node_body", 0): ("GUARD", 2**66, "nibble depth <= 64"),
    ("fe_add", 0): ("WALK", 8 * W + 16, "loads a + 32*i (or i < 4/6/8)"),
    ("fe_sub", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("fe_neg", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("fe_mul_small", 0): ("WALK", 8 * W + 16, "loads a + 32*i"),
    ("bn254_pairing_check", 0): ("WALK", 192 * W + 384, "loads pairs + 192*i in ordinaryDomain"),
    ("bls_g1_msm_exec", 0): ("WALK", 160 * W + 320, "loads in + 160*i in ordinaryDomain"),
    ("bls_g2_msm_exec", 0): ("WALK", 288 * W + 576, "loads in + 288*i in ordinaryDomain"),
    ("bls_pairing_exec", 0): ("WALK", 384 * W + 768, "loads in + 384*i in ordinaryDomain"),
    ("bn_divmnu", 0): ("WALK", 8 * W + 16, "loads u/q + 8*j in ordinaryDomain"),
    ("bn_divmnu", 1): ("WALK", 8 * W + 16, "loads v + 8*i in ordinaryDomain"),
    ("bn_divmnu", 2): ("WALK", 8 * W + 16, "loads u + 8*i in ordinaryDomain"),
    ("bn_divmnu", 3): ("WALK", 8 * W + 16, "stores q + 8*j in ordinaryDomain"),
    ("bn_divmnu", 5): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("bn_divmnu", 6): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("bn_divmnu", 7): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("bn_divmnu", 8): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("divmnu", 0): ("WALK", 8 * W + 16, "loads u + 8*j in ordinaryDomain"),
    ("divmnu", 1): ("WALK", 8 * W + 16, "loads v + 8*i in ordinaryDomain"),
    ("divmnu", 2): ("WALK", 8 * W + 16, "loads u + 8*i in ordinaryDomain"),
    ("divmnu", 3): ("WALK", 8 * W + 16, "stores q + 8*j in ordinaryDomain"),
    ("divmnu", 5): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("divmnu", 6): ("WALK", 8 * W + 16, "loads vn + 8*i in ordinaryDomain"),
    ("divmnu", 7): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("divmnu", 8): ("WALK", 8 * W + 16, "stores r + 8*i in ordinaryDomain"),
    ("bn_mul", 0): ("WALK", 8 * W + 16, "stores out + 8*i in ordinaryDomain"),
    ("bn_mul", 1): ("WALK", 8 * W + 16, "loads a + 8*i in ordinaryDomain"),
    ("bn_mul", 2): ("WALK", 8 * W + 16, "loads b + 8*j in ordinaryDomain"),
    ("destroy_storage", 0): ("CTR", 2**63, "signed i < cap; inner table may change, so no fixed-base walk is assumed"),
    # Mandatory input-array loads; execute_block is tightened separately below.
    ("execute_block", 0): ("WALK", 16 * W + 32, "loads txs lp + 16*i in ordinaryDomain"),
    ("run_attempt", 0): ("WALK", 16 * W + 32, "loads txs lp + 16*i in ordinaryDomain"),
    ("process_general_purpose_requests", 0): ("WALK", 8 * W + 16, "loads rls rp + 8*i in ordinaryDomain"),
    ("process_general_purpose_requests", 1): ("WALK", 8 * W + 16, "loads logs lp + 8*j in ordinaryDomain"),
}

# For a stride s, each residue modulo gcd(s, 2^64) is visited gcd(s, 2^64)
# times over the complete word index range.  This gives at most W + s residues
# in the ordinary interval; s * (W // s + 2) is a convenient upper bound.
# This argument includes arbitrary nonzero bases and does not count "s sweeps".
for _key, (_kind, _n, _why) in list(R10_LOOP_OVERRIDES.items()):
    if _kind == "WALK" and _n > W + 1:
        _stride = _n // W
        R10_LOOP_OVERRIDES[_key] = (_kind, _stride * (W // _stride + 2),
            _why + "; complete word-index residue count, including wraparound")
# The fe_* loads have stride 32, despite the legacy 8*W coefficient.
# Use their consecutive mandatory loads; the invalid gap is wider than 32.
for _fn in ("fe_add", "fe_sub", "fe_neg", "fe_mul_small"):
    R10_LOOP_OVERRIDES[(_fn, 0)] = ("WALK", 8 * (W // 8 + 2),
        "consecutive mandatory a + 32*i loads; no successful gap crossing")

# execute_block loads ptxs + 16*i on EVERY iteration.  Consecutive successful
# loads cannot cross the complement of ordinaryDomain (which is wider than 16).
# Its index starts at zero and the signed test exits before index wraparound.
R10_LOOP_OVERRIDES[("execute_block", 0)] = ("WALK", W // 16 + 2,
    "consecutive mandatory aligned loads ptxs + 16*i; no successful gap crossing")


def evaluate(expression, values):
    tokens = re.findall(r"«[^»]+»|Nat\.max|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()+*^\-/]", expression)
    if "".join(tokens) != re.sub(r"\s", "", expression):
        raise ValueError(f"unsupported Nat expression: {expression}")
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == "(":
            value = binary(0)
            assert tokens[cursor] == ")"
            cursor += 1
            return value
        if token == "Nat.max":
            return max(atom(), atom())
        if token.isdecimal():
            return int(token)
        return values[token.strip("«»")]

    def binary(minimum):
        nonlocal cursor
        value = atom()
        precedences = {"+": 1, "-": 1, "*": 2, "/": 2, "^": 3}
        while cursor < len(tokens) and precedences.get(tokens[cursor], -1) >= minimum:
            op = tokens[cursor]
            cursor += 1
            other = binary(precedences[op] + (op != "^"))
            if op == "+": value += other
            elif op == "-": value = max(0, value - other)
            elif op == "*": value *= other
            elif op == "/": value = value // other if other else 0
            else: value **= other
        return value

    value = binary(0)
    assert cursor == len(tokens), tokens[cursor:]
    return value


def main():
    source = (ROOT / "campaign/specs-proposed/GuestInv.lean").read_text()
    domain = re.search(r"theorem domainBytes_eq : domainBytes = ([0-9]+)", source)
    values = {"domainBytes": int(domain[1])}
    for name in ("maxChain", "evmPotS", "evmPotF", "evmPotMax"):
        expression = re.search(rf"^def {name} : Nat := (.*)$", source, re.M)[1]
        values[name] = evaluate(expression, values)
    costs = source.split("namespace K\n")[1].split("end K")[0]
    for name, expression in re.findall(r"^def «([^»]+)» : Nat := (.*)$", costs, re.M):
        values[name] = evaluate(expression, values)
    k_pan = values["main"] + 1
    target = 118223496 * k_pan + 119233963
    encoded = json.dumps({"K": target}, separators=(",", ":"))
    print(json.dumps({"K_pan": k_pan, "K_target": target, "K_pan_bits": k_pan.bit_length(),
                      "target_budget_ok": target <= 10 ** 122 - 1,
                      "target_decimal_digits": len(str(target)),
                      "minimal_claim_json_bytes": len(encoded.encode()),
                      "newline_terminated_claim_json_bytes": len(encoded.encode()) + 1,
                      "largest_policy_finite_K": 10 ** (128 - len('{"K":}')) - 1,
                      "policy_claim_byte_limit": 128}, indent=2))


if __name__ == "__main__":
    main()
