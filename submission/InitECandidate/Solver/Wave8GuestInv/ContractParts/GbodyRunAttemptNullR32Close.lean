import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNTR32

/-! Wave 8 R32: the transaction-null `run_attempt` leaf `hTx`.

`GbodyRunAttemptNTR32` closes the witness- and access-list null leaves `hWit`
and `hAcc` of `GbodyRunAttemptR32Empty.hraR32_of` and keeps `hTx`: the
transaction cell is one of `InputAt`'s `inputCells`, so `GbodyRunAttemptNT`
leaves it `Inside`. This module removes `hTx` as well, using the replay
`GbodyRunAttemptNullR32.gbody_run_attempt_null_of` at `Z := True`, whose guard
`InputReadyNull True` lets the transaction cell be the null pair too.

* `run_attempt_r32_null`, `hraR32_null`: `run_attempt` bounded on the whole R32
  guard `GbodyRunAttemptR32.InputReadyR32`, with no case split, no strong
  bound and no null-list premise.
* `txNullCase_run_attempt`: the `hTx` leaf, verbatim.

This is not free. `run_attempt` reaches `payload_header` and `execute_block`
with the transaction cell still null, so three of the five remaining leaves
are stated at guards that allow it: `hexec` at `BlockReadyExecAttemptNull True`,
`hph` at `InputReadyNwdZ True`, `wph` at `InputReadyZ True`. Each relaxed guard
is implied by the one it replaces, so each restated leaf implies the leaf it
replaces and the converse fails:

* `hexecNT_of_null` gives the `hexecNT` premise of
  `GbodyRunAttemptNTR32.gbody_run_attempt_nt_r32` (and `hexec_strong_of_null`
  the original `hexec`),
* `hph_of_z` and `wph_of_z` give the original `hph` and `wph`.

Only the `Z := True` instance of the replay is used here; at `Z := False` it
has the strength of `GbodyRunAttemptNT`, which is the module to use for the
route that keeps `hTx`. -/

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

/-! ### The `GbodyRunAttemptNT` guards imply the null-tolerant ones -/

/-- A run-attempt cell is kept by `GbodyRunAttemptNT.runAttemptCells` or is
the null pair. -/
theorem mem_nt_or_null {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat} {i : Ivl}
    (hi : i ∈ runAttemptCells s si) :
    i ∈ GbodyRunAttemptNT.runAttemptCells s si ∨ (i.1 = 0 ∧ i.2 = 0) := by
  by_cases h0 : i.1 = 0 ∧ i.2 = 0
  · exact Or.inr h0
  · refine Or.inl ?_
    unfold GbodyRunAttemptNT.runAttemptCells
    simp only [runAttemptCells, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_left _ (by simp)
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨by simp, decide_eq_true h0⟩)
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨by simp, decide_eq_true h0⟩)
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨by simp, decide_eq_true h0⟩)

/-- The cell facts of the null-tolerant guard hold of the null pair. -/
theorem nullCell_facts {F : Type} {s : PanSemStateFiniteExact 64 F} {i : Ivl} {lo hi : Nat}
    (h0 : i.1 = 0 ∧ i.2 = 0) :
    i.1 % 8 = 0 ∧ ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i lo hi) ∧ WordsOK s i := by
  obtain ⟨a, b⟩ := i
  dsimp only at h0
  obtain ⟨rfl, rfl⟩ := h0
  exact ⟨rfl, Or.inl ⟨rfl, rfl⟩, rfl, rfl, fun k hk => by simp at hk⟩

theorem inputAtNull_of_nt {Z : Prop} {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : GbodyRunAttemptNT.InputAtStrong s si) : InputAtNull Z s si := by
  obtain ⟨hIn, hnvh, hnwd, S, Nd, hWT, hcells, hdisj⟩ := h
  refine ⟨inputAtZ_of_inputAt hIn, hnvh, hnwd, S, Nd, hWT, fun i hi => ?_, fun i hi j hj => ?_⟩
  · rcases mem_nt_or_null hi with hm | h0
    · exact ⟨(hcells i hm).1, Or.inr (hcells i hm).2.1, (hcells i hm).2.2⟩
    · exact nullCell_facts h0
  · rcases mem_nt_or_null hi with hm | h0
    · exact hdisj i hm j hj
    · exact Or.inl h0.2

theorem blockReadyExecAttemptNull_of_nt {Z : Prop} {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : GbodyRunAttemptNT.BlockReadyExecAttemptStrong s) :
    BlockReadyExecAttemptNull Z s :=
  ⟨⟨h.1.1, inputReadyZ_of_inputReady h.1.2.1, h.1.2.2⟩, inputAtNull_of_nt h.2.1, h.2.2⟩

/-- The restated `execute_block` leaf gives the `hexecNT` premise of
`GbodyRunAttemptNTR32.gbody_run_attempt_nt_r32`. -/
theorem hexecNT_of_null {Z : Prop}
    (hexec : TerminatingFunBoundedOn (BlockReadyExecAttemptNull Z)
      (ofString "execute_block") K.«execute_block») :
    TerminatingFunBoundedOn GbodyRunAttemptNT.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block» :=
  hexec.mono (fun _ hs => blockReadyExecAttemptNull_of_nt hs)

/-! ### Closure at `Z := True` -/

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

/-- The `hraR32` premise of `MainEntryR32.mainEntryR32` with no null-list
premise. -/
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

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close
