import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.RlpHelpers

/-!
# R16k EncodeTransaction: `wk_encode_transaction_strong`

Strengthened `WorldKeeps` theorem for `encode_transaction` using the
`TxValidEncodeReady` precondition, which extends `TxValidAt` with `Inside`
conditions on every sub-array pointer read by `tx_encode_generic`.

## Proof strategy

`encode_transaction`'s body is a tail call `.call none "tx_encode_generic" [tx, 0, 0]`.
The proof proceeds by:
1. Establishing `HeapByteEff s post [] ["heap_ptr"]` for the resulting post-state.
2. Lifting via `HeapByteEff.to_worldStep`.

`HeapByteEff` requires showing all memory writes fall within `heapFree s` (new
allocation) or `freeGap s`. The step-by-step execution trace of `tx_encode_generic`
proceeds through:
  `tx_encode_bound` → `alloc(bound)` → writes within `[buf, buf+bound)` via
  `rlp_encode_word`, `tx_put_u256` (×5), `tx_put_to`, `rlp_encode_bytes` (data),
  `tx_put_access_list` (loop), `tx_put_blob_hashes` (loop),
  `tx_put_authorizations` (loop), `rlp_finish_list`.

Sub-array safety conditions in `TxValidEncodeAt` cover:
- `to` field   : `(tx+152, 20)` bytes for `rlp_encode_bytes`
- `data` bytes : `(memW s (tx+192), memW s (tx+200))` data payload
- access-list  : `(tx+208, 24·n_al)` entries each with keys sub-array
- blob hashes  : `(tx+256, 32·n_bl)` hashes
- setcode auths: `(tx+272, 120·n_sa)` authorizations
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Section 1: `TxValidEncodeAt` / `TxValidEncodeReady` definitions -/

/-- Extended validity condition for `encode_transaction` / `tx_encode_generic`.
Extends `TxValidAt` with `Inside` conditions for every byte-slice that
`tx_encode_generic` reads directly (the `to` field, data payload, access-list
entries, blob hashes, and setcode authorizations). These conditions ensure the
sub-arrays already reside in the allocated heap and are word-aligned, enabling
the step-by-step encoding proof. -/
def TxValidEncodeAt {F : Type} (s : PanSemStateFiniteExact 64 F) (tx : Nat) : Prop :=
  TxValidAt s tx ∧
  -- `to` field: 20-byte address at tx+152
  WordsOK s (memW s (tx + 152), 20) ∧
  Inside (memW s (tx + 152), 20) sourceBase (globN s "heap_ptr") ∧
  -- `data` payload: pointer at tx+192, length at tx+200
  Inside (memW s (tx + 192), memW s (tx + 200)) sourceBase (globN s "heap_ptr") ∧
  -- access-list entries: `n_al` entries of 24 bytes at tx+208, count at tx+216
  Inside (memW s (tx + 208), 24 * memW s (tx + 216)) sourceBase (globN s "heap_ptr") ∧
  -- access-list keys: for each entry the key sub-array is inside heap
  (∀ i, i < memW s (tx + 216) →
    Inside (memW s (memW s (tx + 208) + 24 * i + 8),
            32 * memW s (memW s (tx + 208) + 24 * i + 16))
           sourceBase (globN s "heap_ptr")) ∧
  -- blob hashes: 32-byte hashes at tx+256, count at tx+264
  Inside (memW s (tx + 256), 32 * memW s (tx + 264)) sourceBase (globN s "heap_ptr") ∧
  -- setcode authorizations: 120-byte entries at tx+272, count at tx+280
  Inside (memW s (tx + 272), 120 * memW s (tx + 280)) sourceBase (globN s "heap_ptr")

/-- Entry condition for `wk_encode_transaction_strong`:
`TxValidEncodeAt` instantiated at the `"tx"` local. -/
def TxValidEncodeReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxValidEncodeAt s (locN s "tx")

/-! ## Section 2: Lookup theorem -/

theorem lookup_encode_transaction_strong :
    originalRuntimeCode.lookup (ofString "encode_transaction") =
      some ([(ofString "tx", .one)],
        sourceFnBody Guest.Software.guestFn_encode_transaction,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 329 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_transaction) rfl

/-! ## Section 3: Auxiliary lemmas -/

/-- `TxValidEncodeReady` implies `TxValid` (the C08 precondition). -/
theorem txValidEncodeReady_txValid {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxValidEncodeReady s) : TxValid s :=
  h.1

/-- `encode_transaction`'s body is a tail call to `tx_encode_generic`. -/
private theorem encode_transaction_body :
    sourceFnBody Guest.Software.guestFn_encode_transaction =
    .call none (ofString "tx_encode_generic")
      [.var .local (ofString "tx"), .const 0, .const 0] := rfl

/-! ## Section 4: `wk_encode_transaction_strong` -/

/-- Strengthened `WorldKeeps` for `encode_transaction`: under the stronger
`TxValidEncodeReady` precondition (which adds sub-array `Inside` witnesses on
top of `TxValidAt`), the encoding function only grows `heap_ptr` and respects
all typed records and global buffers. -/
theorem «wk_encode_transaction_strong» :
    WorldKeeps (fun s => WorldOK s ∧ TxValidEncodeReady s) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_transaction") := by
  refine ⟨_, _, _, lookup_encode_transaction_strong,
    fun {F} s hcode hW _ hnt hres => ?_⟩
  have hWOK : WorldOK s := hW.1
  -- The body is a tail call; establish HeapByteEff for the post-state.
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_transaction)).2
      ([] ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h) (by intro g hg; simp at hg; exact Or.inl hg)
      hWOK (fun _ _ _ _ _ => trivial)
  simp only [List.append_nil, List.map_nil]
  rw [encode_transaction_body] at hnt hres ⊢
  -- The step-by-step HeapByteEff proof for the tx_encode_generic tail call:
  -- requires tracing ~15 sub-functions and establishing all writes fall in heapFree s.
  -- Each sub-function (tx_encode_bound, alloc, rlp_encode_word×2, tx_put_u256×5,
  -- tx_put_to, rlp_encode_bytes, tx_put_access_list, tx_put_blob_hashes,
  -- tx_put_authorizations, rlp_finish_list) needs an individual HeapByteEff combinator.
  -- This trace is analogous to EncodeReceipt.lean (4687 lines) but significantly larger.
  -- Pending: tx_put_u256_heapByteEff, tx_put_to_heapByteEff, tx_put_access_list_heapByteEff,
  --          tx_put_blob_hashes_heapByteEff, tx_put_authorizations_heapByteEff.
  sorry

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
