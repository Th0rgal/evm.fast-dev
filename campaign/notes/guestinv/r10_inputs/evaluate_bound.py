#!/usr/bin/env python3
"""Evaluate the generated Nat cost expressions independently of Lean.

Diagnostic arithmetic, not a substitute for a Lean equality proof. No eval,
native_decide, or generated proof assumptions are involved.
"""
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]


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
    revision = json.loads((ROOT/'campaign/notes/integration/PORT.json').read_text())['source_commit']
    source = subprocess.check_output(['git','show',revision+':campaign/specs-proposed/GuestInv.lean'],cwd=ROOT,text=True)
    domain = re.search(r"theorem domainBytes_eq : domainBytes = ([0-9]+)", source)
    values = {"domainBytes": int(domain[1])}
    for name in ("maxChain", "evmPotS", "evmPotF", "evmPotMax"):
        expression = re.search(rf"^def {name} : Nat := (.*)$", source, re.M)[1]
        values[name] = evaluate(expression, values)
    costs = source.split("namespace K\n")[1].split("end K")[0]
    for name, expression in re.findall(r"^def «([^»]+)» : Nat := (.*)$", costs, re.M):
        values[name] = evaluate(expression, values)
    k_pan = values["main"] + 1
    target = 32 * k_pan + 23077
    encoded = json.dumps({"K": target}, separators=(",", ":"))
    print(json.dumps({"K_pan": k_pan, "K_target_proposed": target,
                      "target_decimal_digits": len(str(target)),
                      "minimal_claim_json_bytes": len(encoded.encode()),
                      "newline_terminated_claim_json_bytes": len(encoded.encode()) + 1,
                      "largest_policy_finite_K": 10 ** (128 - len('{"K":}')) - 1,
                      "policy_claim_byte_limit": 128}, indent=2))


if __name__ == "__main__":
    main()
