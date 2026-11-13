import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty

/-! Wave 8 R32: the null-list `run_attempt` leaves `hTx` / `hWit` / `hAcc`.

`GbodyRunAttemptR32Empty.hraR32_of` takes the `run_attempt` bound of the three
null-list sub-cases (`TxNullCase`, `WitNullCase`, `AccNullCase`) as open leaf
premises. This module removes them, using the null-tolerant replay
`GbodyRunAttemptNullR32.gbody_run_attempt_null_of` (guard `InputReadyNull Z`,
where `Z` says whether the transaction cell may be the null pair).

Two closures are delivered, and neither is free: `run_attempt` reaches
`execute_block` with the null cells still null, so the `execute_block` leaf has
to be stated at a guard that admits them.

* **`Z := True`** (`run_attempt_r32_null`, `hraR32_null`): the whole R32 guard
  `GbodyRunAttemptR32.InputReadyR32` is covered at once, with no case split
  and no strong bound. `hTx`, `hWit`, `hAcc` all disappear
  (`txNullCase_run_attempt`, `witNullCase_run_attempt`,
  `accNullCase_run_attempt` prove them verbatim). In exchange three of the
  five remaining leaves are restated at relaxed guards: `hexec` at
  `BlockReadyExecAttemptNull True`, `hph` at `InputReadyNwdZ True`, `wph` at
  `InputReadyZ True`.
* **`Z := False`** (`run_attempt_r32_of_txNull`, `hraR32_of_txNull`): `hWit`
  and `hAcc` disappear, `hTx` stays a premise, and `hph` / `wph` are the
  original leaves (`InputReadyNwdZ False` / `InputReadyZ False` are
  `InputReadyNwd` / `InputReady`). Only `hexec` is restated, at
  `BlockReadyExecAttemptNull False`: there the witness, access-list and
  versioned-hash cells may be null, while the four cells shared with
  `ExecBlock.inputRegions` are still `Inside`
  (`blockReadyExecAttemptNull_false_inside`). The sub-cases as stated
  (`WitNullCase`, `AccNullCase`) include states whose transaction cell is null
  too, so `witNullCase_of_txNull` / `accNullCase_of_txNull` keep `hTx`.

Each restated leaf is at a guard implied by the original one
(`blockReadyExecAttemptNull_of_strong`, `inputReadyNwdZ_of_nwd`,
`inputReadyZ_of_inputReady`), so it is a stronger statement:
`hexec_strong_of_null`, `hph_of_z` and `wph_of_z` recover the original leaves
from the restated ones. The converse does not hold. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32

/-! ### The world-contract leaves -/

/-- The `payload_header` world contract (`RetHeader`) at entry guard `P`; the
`wph` leaf of `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32` is
`WphAt InputReady`. -/
abbrev WphAt (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  WorldKeeps P
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
      (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
      (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
      (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetHeader (ofString "payload_header")

/-- The `state_init` world contract: the `wsi` leaf, unchanged. -/
abbrev WsiLeaf : Prop :=
  WorldReturnsIn StateInitReady
    (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
    ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
    [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
     ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetStateInit (ofString "state_init")

/-- The strong `validate_headers` world contract: the `wvhs` leaf, unchanged. -/
abbrev WvhsLeaf : Prop :=
  WorldKeeps WorldOK
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetHeadersStrong (ofString "validate_headers")

/-- A world contract holds at any stronger entry guard. -/
theorem worldKeeps_mono_guard {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl} {gw : List String}
    {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop} {fname : MlS}
    (hPP : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P' s → P s)
    (h : WorldKeeps P R gw keep Q fname) : WorldKeeps P' R gw keep Q fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  exact ⟨params, body, ret, hlook, fun s hcode hP => hb s hcode (hPP s hP)⟩

/-! ### The null-tolerant bound with the 20 proved leaves supplied -/

/-- `gbody_run_attempt_null_of` with its 20 proved leaf premises discharged
exactly as in `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`. -/
theorem gbody_run_attempt_null_r32 {Z : Prop}
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ Z)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn (InputReadyNull Z) (ofString "run_attempt") K.«run_attempt» :=
  gbody_run_attempt_null_of
    Merged.fb_alloc
    R11Adapters.«fb_check_gas_limit»
    hexec
    R11Adapters.«fb_header_hash»
    R11Adapters.«fb_is_valid_versioned_hashes»
    Merged.fb_memeq
    Merged.fb_memzero
    R11Adapters.«fb_nodedb_build»
    hph
    (R13Shards.gbody_state_init Merged.fb_alloc
      ChainHandlersR31C1.g_decode_witness_to_mpt_r31 Merged.fb_htab_new
      R13Shards.WkShard01.«wk_alloc» R13Shards.WkShard01.«rt_alloc»)
    R11Adapters.«fb_validate_header»
    R11Adapters.«fb_validate_headers»
    R13Shards.WkShard01.«wk_alloc»
    R13Shards.WkShard01.«rt_alloc»
    R10Ports.ro_check_gas_limit
    R16Shards.HeaderHashRecover.«wk_header_hash_inside»
    R16Shards.«wk_is_valid_versioned_hashes»
    InitECandidate.Solver.Wave8Contracts.M15.«ro_memeq»
    InitECandidate.Solver.Wave8Contracts.M08.«wk_memzero»
    Merged.zv_memzero
    R16Shards.TopGbodyWk.«wk_nodedb_build»
    wph
    wsi
    R16Shards.TopGbodyWk.«wk_validate_header_strong»
    wvhs

/-! ### The R32 guard is the null-tolerant guard -/

/-- An R32 entry is a null-tolerant entry, provided `Z` holds whenever the
transaction cell is the null pair. The three header cells have nonzero sizes,
so they are `Inside`; the transaction cell is the only `inputCells` member that
can be null. -/
theorem inputAtNull_of_r32 {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtR32 s si)
    (hz : memW s (memW s si + 32) = 0 ∧ 16 * memW s (memW s si + 40) = 0 → Z) :
    InputAtNull Z s si := by
  obtain ⟨S, Nd, hAr, hWT, hcells, hdisj, hnvh, hnwd, hPay, hReq⟩ := h
  have hntx : memW s (memW s si + 40) < 2 ^ 63 := Nat.lt_trans hPay.2.2.1 (by decide)
  have hsi96 := hcells (si, 96) (by simp [runAttemptCells])
  have hpl := hcells (memW s si, 136) (by simp [runAttemptCells])
  have hrq := hcells (memW s (si + 32), 80) (by simp [runAttemptCells])
  have htx := hcells (memW s (memW s si + 32), 16 * memW s (memW s si + 40))
    (by simp [runAttemptCells])
  have h4cells : ∀ i ∈ inputCells s si,
      ((Z ∧ i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i := by
    intro i hi
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact ⟨Or.inr (inside_of_le (by decide) (inside_of_nullOrInside (by simp) hsi96.2.1)),
        wordsOK_of_le (by decide) (by decide) hsi96.2.2⟩
    · exact ⟨Or.inr (inside_of_nullOrInside (by simp) hpl.2.1), hpl.2.2⟩
    · exact ⟨Or.inr (inside_of_nullOrInside (by simp) hrq.2.1), hrq.2.2⟩
    · exact ⟨htx.2.1.imp (fun h0 => ⟨hz h0, h0⟩) id, htx.2.2⟩
  have hdisj4 : IvlsDisj (inputCells s si) (worldOwned s S Nd) := by
    intro i hi j hj
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact disj_left_of_le (by decide : (40 : Nat) ≤ 96)
        (hdisj (si, 96) (by simp [runAttemptCells]) j hj)
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
  exact ⟨⟨hAr, S, Nd, hWT, h4cells, hdisj4, hntx, hPay, hReq⟩, hnvh, hnwd, S, Nd, hWT,
    hcells, hdisj⟩

/-- With the transaction cell allowed null, every R32 entry is null-tolerant. -/
theorem inputReadyNull_true_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyR32 s) : InputReadyNull True s :=
  inputAtNull_of_r32 h (fun _ => trivial)

/-- An R32 entry whose transaction cell is not null is null-tolerant at
`Z := False`. -/
theorem inputReadyNull_false_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyR32 s)
    (hnn : ¬(memW s (memW s (locN s "si") + 32) = 0 ∧
      memW s (memW s (locN s "si") + 40) = 0)) :
    InputReadyNull False s :=
  inputAtNull_of_r32 h (fun h0 => hnn ⟨h0.1, by have := h0.2; omega⟩)

/-! ### The restated leaves imply the original ones -/

theorem inputAtZ_of_inputAt {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAt s si) : InputAtZ Z s si := by
  obtain ⟨hAr, S, Nd, hWT, hcells, hrest⟩ := h
  exact ⟨hAr, S, Nd, hWT, fun i hi => ⟨Or.inr (hcells i hi).1, (hcells i hi).2⟩, hrest⟩

theorem inputReadyZ_of_inputReady {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReady s) : InputReadyZ Z s :=
  inputAtZ_of_inputAt h

theorem inputReadyNwdZ_of_nwd {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyNwd s) : InputReadyNwdZ Z s :=
  ⟨inputAtZ_of_inputAt h.1, h.2⟩

theorem inputReadyNull_of_strong {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyStrong s) : InputReadyNull Z s := by
  obtain ⟨hIn, hnvh, hnwd, S, Nd, hWT, hcells, hdisj⟩ := h
  exact ⟨inputAtZ_of_inputAt hIn, hnvh, hnwd, S, Nd, hWT,
    fun i hi => ⟨(hcells i hi).1, Or.inr (hcells i hi).2.1, (hcells i hi).2.2⟩, hdisj⟩

theorem blockReadyExecAttemptNull_of_strong {Z : Prop} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : BlockReadyExecAttemptStrong s) :
    BlockReadyExecAttemptNull Z s :=
  ⟨⟨h.1.1, inputReadyZ_of_inputReady h.1.2.1, h.1.2.2⟩, inputReadyNull_of_strong h.2.1, h.2.2⟩

/-- The restated `execute_block` leaf gives back the original `hexec`. -/
theorem hexec_strong_of_null {Z : Prop}
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block») :
    TerminatingFunBoundedOn BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block» :=
  hexec.mono (fun _ hs => blockReadyExecAttemptNull_of_strong hs)

/-- The restated `payload_header` bound gives back the original `hph`. -/
theorem hph_of_z {Z : Prop}
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ Z) (ofString "payload_header")
      K.«payload_header») :
    TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header") K.«payload_header» :=
  hph.mono (fun _ hs => inputReadyNwdZ_of_nwd hs)

/-- The restated `payload_header` world contract gives back the original `wph`. -/
theorem wph_of_z {Z : Prop} (wph : WphAt (InputReadyZ Z)) : WphAt InputReady :=
  worldKeeps_mono_guard (fun _ hs => inputReadyZ_of_inputReady hs) wph

/-- At `Z := False` the `payload_header` bound is the original `hph`. -/
theorem hph_false
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header») :
    TerminatingFunBoundedOn (InputReadyNwdZ False) (ofString "payload_header")
      K.«payload_header» :=
  hph.mono (fun s hs => (inputReadyNwdZ_false_iff s).mp hs)

/-- At `Z := False` the `payload_header` world contract is the original `wph`. -/
theorem wph_false (wph : WphAt InputReady) : WphAt (InputReadyZ False) :=
  worldKeeps_mono_guard (fun s hs => (inputReadyZ_false_iff s).mp hs) wph

/-- What the `Z := False` execute-block guard still says about the cells of
`ExecBlock.inputRegions` that come from the host input: the three header cells
and the transaction cell are `Inside`, as under `BlockReadyExecAttemptStrong`.
Only the witness, access-list and versioned-hash cells (not in
`ExecBlock.inputRegions`) may be null. -/
theorem blockReadyExecAttemptNull_false_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BlockReadyExecAttemptNull False s) :
    Inside (locN s "si", 96) sourceBase (globN s "heap_ptr") ∧
    Inside (memW s (locN s "si"), 136) sourceBase (globN s "heap_ptr") ∧
    Inside (memW s (locN s "si" + 32), 80) sourceBase (globN s "heap_ptr") ∧
    Inside (memW s (memW s (locN s "si") + 32), 16 * memW s (memW s (locN s "si") + 40))
      sourceBase (globN s "heap_ptr") := by
  obtain ⟨-, hN, -⟩ := h
  obtain ⟨hZ, -, -, S, Nd, -, hcells, -⟩ := hN
  obtain ⟨-, S', Nd', -, hc4, -⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inside_of_nullOrInside (by simp) (hcells _ (by simp [runAttemptCells])).2.1
  · exact inside_of_nullOrInside (by simp) (hcells _ (by simp [runAttemptCells])).2.1
  · exact inside_of_nullOrInside (by simp) (hcells _ (by simp [runAttemptCells])).2.1
  · exact (hc4 _ (by simp [inputCells])).1.resolve_left (fun hf => hf.1)

/-! ### Closure at `Z := True`: all three null-list leaves -/

/-- `run_attempt` bounded on the whole R32 guard, null cells included, from the
five sub-`run_attempt` leaves at the null-tolerant guards. No strong bound and
no empty-case premise is used. -/
theorem run_attempt_r32_null
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ True) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ True)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt» :=
  (gbody_run_attempt_null_r32 hexec hph wph wsi wvhs).mono
    (fun _ hs => inputReadyNull_true_of_r32 hs)

/-- The `hraR32` premise of `MainEntryR32.mainEntryR32`, without `hTx`, `hWit`,
`hAcc`. -/
theorem hraR32_null
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ True) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ True)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn MainEntryR32.InputReadyR32 (ofString "run_attempt")
      K.«run_attempt» :=
  (run_attempt_r32_null hexec hph wph wsi wvhs).mono
    (fun s hs => (R32CanonicalBridges.inputReadyR32CanonBounded_iff s).mp hs)

/-- The `hTx` leaf of `GbodyRunAttemptR32Empty.hraR32_of`. -/
theorem txNullCase_run_attempt
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ True) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ True)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_null hexec hph wph wsi wvhs).mono (fun _ hs => hs.1)

/-- The `hWit` leaf of `GbodyRunAttemptR32Empty.hraR32_of`. -/
theorem witNullCase_run_attempt
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ True) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ True)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_null hexec hph wph wsi wvhs).mono (fun _ hs => hs.1)

/-- The `hAcc` leaf of `GbodyRunAttemptR32Empty.hraR32_of`. -/
theorem accNullCase_run_attempt
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (InputReadyNwdZ True) (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt (InputReadyZ True)) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_null hexec hph wph wsi wvhs).mono (fun _ hs => hs.1)

/-! ### Closure at `Z := False`: `hWit` and `hAcc`, original `hph` / `wph` -/

/-- `run_attempt` bounded on the R32 states whose transaction cell is not null
(the witness, access-list and versioned-hash cells may be), from the original
`hph`, `wph`, `wsi`, `wvhs` and `hexec` at `BlockReadyExecAttemptNull False`. -/
theorem run_attempt_r32_txPresent
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull False)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt InputReady) (wsi : WsiLeaf) (wvhs : WvhsLeaf) :
    TerminatingFunBoundedOn
      (fun s => InputReadyR32 s ∧
        ¬(memW s (memW s (locN s "si") + 32) = 0 ∧ memW s (memW s (locN s "si") + 40) = 0))
      (ofString "run_attempt") K.«run_attempt» :=
  (gbody_run_attempt_null_r32 hexec (hph_false hph) (wph_false wph) wsi wvhs).mono
    (fun _ hs => inputReadyNull_false_of_r32 hs.1 hs.2)

/-- `run_attempt` bounded on the whole R32 guard from the transaction-null
sub-case `hTx` and the `Z := False` bound: `hWit` and `hAcc` are not needed. -/
theorem run_attempt_r32_of_txNull
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull False)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt InputReady) (wsi : WsiLeaf) (wvhs : WvhsLeaf)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt» := by
  obtain ⟨p, b, rs, hlk, hrun⟩ := run_attempt_r32_txPresent hexec hph wph wsi wvhs
  obtain ⟨p2, b2, rs2, hlk2, hrun2⟩ := hTx
  rw [hlk] at hlk2
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk2
  refine ⟨p, b, rs, hlk, fun state hcode hp => ?_⟩
  by_cases h0 : memW state (memW state (locN state "si") + 32) = 0 ∧
      memW state (memW state (locN state "si") + 40) = 0
  · exact hrun2 state hcode ⟨hp, h0⟩
  · exact hrun state hcode ⟨hp, h0⟩

/-- The `hraR32` premise of `MainEntryR32.mainEntryR32`, without `hWit` and
`hAcc`. -/
theorem hraR32_of_txNull
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull False)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt InputReady) (wsi : WsiLeaf) (wvhs : WvhsLeaf)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn MainEntryR32.InputReadyR32 (ofString "run_attempt")
      K.«run_attempt» :=
  (run_attempt_r32_of_txNull hexec hph wph wsi wvhs hTx).mono
    (fun s hs => (R32CanonicalBridges.inputReadyR32CanonBounded_iff s).mp hs)

/-- The `hWit` leaf from `hTx` and the `Z := False` leaves. -/
theorem witNullCase_of_txNull
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull False)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt InputReady) (wsi : WsiLeaf) (wvhs : WvhsLeaf)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_of_txNull hexec hph wph wsi wvhs hTx).mono (fun _ hs => hs.1)

/-- The `hAcc` leaf from `hTx` and the `Z := False` leaves. -/
theorem accNullCase_of_txNull
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull False)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WphAt InputReady) (wsi : WsiLeaf) (wvhs : WvhsLeaf)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_of_txNull hexec hph wph wsi wvhs hTx).mono (fun _ hs => hs.1)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close
