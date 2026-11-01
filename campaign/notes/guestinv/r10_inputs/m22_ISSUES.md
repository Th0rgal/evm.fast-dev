# Counterexamples & Contract Issues — Micro-shard `m22` (`wave8/contracts-m22`)

Evaluated against frozen spec revision 9 (`campaign/specs-proposed/GuestInv.lean` @
`8a79d9f28bdd7a3522f8a9a81a892d9ecaabdeff`, tag `wave8-spec-frozen-r9`) and the real guest AST
(`Guest/SoftwareAst.lean`).

Summary:
- `ek_is_warm_storage_key` — **TRUE** (proved unconditionally in `ek_is_warm_storage_key.lean`).
- `ek_refill_frame_state_gas` — **TRUE** (proved unconditionally in `ek_refill_frame_state_gas.lean`).
- `ek_frame_halt`, `ek_get_storage_original`, `ek_depth0_prepare`, `ek_frame_start` — **FALSE** as
  literally stated in rev9; each has a kernel-verified refutation theorem (`not_ek_*`) with `0 sorry`
  and standard Lean axioms only.

---

## 1. `ek_frame_halt` (`Guest/SoftwareAst.lean:18756`) — FALSE

- **Frozen rev9 statement** (`GuestInv.lean:8689`):
  ```lean
  EvmKeeps EvmInv [] (ofString "frame_halt")
  ```
- **Bug / Counterexample**:
  `FunSpec` quantifies universally over all `s` satisfying `EvmInv s` without constraining the shape
  of parameter `s.locals.lookup (ofString "err")` (which `lookupCodeHOLFinite` checks at call sites,
  but `FunSpec` evaluates `body` directly on `s`).
  In `guestFn_frame_halt`:
  ```
  store (ev + 184) ((load .one (ev + 184)) + (load .one (ev + 64)));
  store (ev + 64) 0;
  store (ev + 160) err;
  return 0
  ```
  Take `s := fhCxState` (`EvmInv s`, `ev = 0xb0bec000`, `memW s (ev + 168) = 0xa1001000 ∈ S`) with
  `s.locals.lookup (ofString "err") = some (.rStruct [.val (.word 0), .val (.word 0)])`.
  In Pancake's `evaluateHOLFiniteState_store`, `panMemStoresHOL (ev + 160) (flattenHOL err)` writes
  two consecutive words (`0` to `ev + 160` and `0` to `ev + 168`, overwriting the `frame.addr`
  table pointer!) and `return 0` returns `some (.returned (.val (.word 0)))` (`Resumes` holds).
  In `post`, `memW post (ev + 168) = 0`, violating `FrameWF post S' (ev, cur_cont)` (`0 ∉ S'` since
  `0 ∉ ordinaryDomain`) and hence `¬ EvmInv post`.
- **Formal refutation & safe variant**:
  - `not_ek_frame_halt : ¬ EvmKeeps EvmInv [] (ofString "frame_halt")` (`ek_frame_halt.lean`)
  - `ek_frame_halt_safe : EvmKeeps EvmInvWordErr [] (ofString "frame_halt")` (`ek_frame_halt.lean`),
    proved unconditionally once `err` has 1-word shape (`∃ w, s.locals.lookup (ofString "err") = some (.val (.word w))`).
