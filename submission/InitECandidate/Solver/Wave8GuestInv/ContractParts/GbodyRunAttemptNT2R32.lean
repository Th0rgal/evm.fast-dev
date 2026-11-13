import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges

/-! Wave 8 R32 (GbodyRunAttemptNT2R32): the `run_attempt` bound at the R32
guard, with no decode-empty case premise, reduced to the `execute_block` and
`payload_header` premises at null-tolerant guards.

`GbodyRunAttemptNT2` replays the `run_attempt` proof over an `InputAt` whose
tx cell may be the null pair, so its guard `InputReadyStrong` holds in every
R32 `run_attempt` entry state:

* `inputReadyStrongNT2_of_r32` — `InputReadyR32 s → GbodyRunAttemptNT2.InputReadyStrong s`.
* `gbody_run_attempt_nt2_r32` — the `run_attempt` bound at
  `GbodyRunAttemptNT2.InputReadyStrong`, with the 20 leaf premises supplied as
  in `GbodyRunAttemptStrongR32` and the five sub-`run_attempt` hypotheses kept;
  `hexec`, `hph` and `wph` are at the null-tolerant guards of
  `GbodyRunAttemptNT2`, `wsi` and `wvhs` are unchanged.
* `run_attempt_r32_nt2`, `hraR32_nt2` — the bound at
  `GbodyRunAttemptR32.InputReadyR32` and at `MainEntryR32.InputReadyR32`, with
  no case premise.
* `txNullCase_run_attempt`, `witNullCase_run_attempt`,
  `accNullCase_run_attempt` (the `hTx` / `hWit` / `hAcc` premises of
  `GbodyRunAttemptR32Empty.hraR32_of`) are in `GbodyRunAttemptNT2R32Cases`;
  this file does not import `GbodyRunAttemptR32Empty`.
* `hexec_of_nt2`, `hph_of_nt2`, `wph_of_nt2` — each null-tolerant premise
  implies the corresponding premise of `gbody_run_attempt_strong_r32`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32

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

/-! ### The null-tolerant notions against the original ones -/

/-- A null-tolerant input cell is an original input cell. -/
theorem mem_inputCells_nt2 {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    {i : Ivl} (hi : i ∈ GbodyRunAttemptNT2.inputCells s si) : i ∈ inputCells s si := by
  rcases GbodyRunAttemptNT2.mem_inputCells hi with rfl | rfl | rfl | ⟨rfl, _⟩ <;>
    simp [inputCells]

/-- A null-tolerant run-attempt cell is an original run-attempt cell, and it
is one of the three header cells or not the null pair. -/
theorem mem_runAttemptCells_nt2 {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    {i : Ivl} (hi : i ∈ GbodyRunAttemptNT2.runAttemptCells s si) :
    i ∈ runAttemptCells s si ∧
      (i = (si, 96) ∨ i = (memW s si, 136) ∨ i = (memW s (si + 32), 80) ∨
        ¬(i.1 = 0 ∧ i.2 = 0)) := by
  unfold GbodyRunAttemptNT2.runAttemptCells at hi
  rcases List.mem_append.1 hi with h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨by simp [runAttemptCells], Or.inl rfl⟩
    · exact ⟨by simp [runAttemptCells], Or.inr (Or.inl rfl)⟩
    · exact ⟨by simp [runAttemptCells], Or.inr (Or.inr (Or.inl rfl))⟩
  · obtain ⟨hm, hp⟩ := List.mem_filter.1 h
    refine ⟨?_, Or.inr (Or.inr (Or.inr (of_decide_eq_true hp)))⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · simp [runAttemptCells]
    · simp [runAttemptCells]
    · simp [runAttemptCells]
    · simp [runAttemptCells]

/-- `InputAt` implies the null-tolerant `InputAt` (fewer cells). -/
theorem inputAtNT2_of {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAt s si) : GbodyRunAttemptNT2.InputAt s si := by
  obtain ⟨hA, S, Nd, hWT, hcells, hdisj, hrest⟩ := h
  exact ⟨hA, S, Nd, hWT, fun i hi => hcells i (mem_inputCells_nt2 hi),
    fun i hi => hdisj i (mem_inputCells_nt2 hi), hrest⟩

theorem inputReadyNT2_of {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReady s) : GbodyRunAttemptNT2.InputReady s :=
  inputAtNT2_of h

theorem inputReadyNwdNT2_of {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyNwd s) : GbodyRunAttemptNT2.InputReadyNwd s :=
  ⟨inputAtNT2_of h.1, h.2⟩

/-- The strong guard implies the null-tolerant one (fewer cells). -/
theorem inputAtStrongNT2_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtStrong s si) : GbodyRunAttemptNT2.InputAtStrong s si := by
  obtain ⟨hIn, hnvh, hnwd, S, Nd, hWT, hcells, hdisj⟩ := h
  exact ⟨inputAtNT2_of hIn, hnvh, hnwd, S, Nd, hWT,
    fun i hi => hcells i (mem_runAttemptCells_nt2 hi).1,
    fun i hi => hdisj i (mem_runAttemptCells_nt2 hi).1⟩

/-- The strong `execute_block` entry implies the null-tolerant one. -/
theorem blockReadyExecAttemptStrongNT2_of_strong {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : BlockReadyExecAttemptStrong s) :
    GbodyRunAttemptNT2.BlockReadyExecAttemptStrong s :=
  ⟨⟨h.1.1, inputReadyNT2_of h.1.2.1, h.1.2.2⟩, inputAtStrongNT2_of_strong h.2.1, h.2.2⟩

/-- The null-tolerant `execute_block` bound implies the `hexec` premise of
`GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`. -/
theorem hexec_of_nt2
    (hexec : TerminatingFunBoundedOn GbodyRunAttemptNT2.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block») :
    TerminatingFunBoundedOn BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block» :=
  hexec.mono (fun _ hs => blockReadyExecAttemptStrongNT2_of_strong hs)

/-- The null-tolerant `payload_header` bound implies the `hph` premise. -/
theorem hph_of_nt2
    (hph : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyNwd
      (ofString "payload_header") K.«payload_header») :
    TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header") K.«payload_header» :=
  hph.mono (fun _ hs => inputReadyNwdNT2_of hs)

/-- The null-tolerant `payload_header` world contract implies the `wph`
premise. -/
theorem wph_of_nt2
    (wph : WorldKeeps GbodyRunAttemptNT2.InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header")) :
    WorldKeeps InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header") := by
  obtain ⟨params, body, ret, hlook, hb⟩ := wph
  exact ⟨params, body, ret, hlook, fun s hcode hP hex hnt =>
    hb s hcode (inputReadyNT2_of hP) hex hnt⟩

/-! ### Every R32 `run_attempt` entry state is null-tolerant-strong -/

/-- An R32 input satisfies the null-tolerant strong guard: the three header
cells have nonzero sizes, so they are `Inside`; every other null-tolerant
cell is not the null pair, hence `Inside`. -/
theorem inputAtStrongNT2_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtR32 s si) : GbodyRunAttemptNT2.InputAtStrong s si := by
  obtain ⟨S, Nd, hAr, hWT, hcells, hdisj, hnvh, hnwd, hPay, hReq⟩ := h
  have hntx : memW s (memW s si + 40) < 2 ^ 63 := Nat.lt_trans hPay.2.2.1 (by decide)
  have hsi96 := hcells (si, 96) (by simp [runAttemptCells])
  have hpl := hcells (memW s si, 136) (by simp [runAttemptCells])
  have hrq := hcells (memW s (si + 32), 80) (by simp [runAttemptCells])
  have htxc := hcells (memW s (memW s si + 32), 16 * memW s (memW s si + 40))
    (by simp [runAttemptCells])
  have hsi96In : Inside (si, 96) sourceBase (globN s "heap_ptr") :=
    hsi96.2.1.resolve_left (fun h0 => absurd (show (96 : Nat) = 0 from h0.2) (by decide))
  have hplIn : Inside (memW s si, 136) sourceBase (globN s "heap_ptr") :=
    hpl.2.1.resolve_left (fun h0 => absurd (show (136 : Nat) = 0 from h0.2) (by decide))
  have hrqIn : Inside (memW s (si + 32), 80) sourceBase (globN s "heap_ptr") :=
    hrq.2.1.resolve_left (fun h0 => absurd (show (80 : Nat) = 0 from h0.2) (by decide))
  have h4cells : ∀ i ∈ GbodyRunAttemptNT2.inputCells s si,
      Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i := by
    intro i hi
    rcases GbodyRunAttemptNT2.mem_inputCells hi with rfl | rfl | rfl | ⟨rfl, hnn⟩
    · exact ⟨inside_of_le (by decide) hsi96In, wordsOK_of_le (by decide) (by decide) hsi96.2.2⟩
    · exact ⟨hplIn, hpl.2.2⟩
    · exact ⟨hrqIn, hrq.2.2⟩
    · exact ⟨htxc.2.1.resolve_left hnn, htxc.2.2⟩
  have hdisj4 : IvlsDisj (GbodyRunAttemptNT2.inputCells s si) (worldOwned s S Nd) := by
    intro i hi j hj
    rcases GbodyRunAttemptNT2.mem_inputCells hi with rfl | rfl | rfl | ⟨rfl, _⟩
    · exact disj_left_of_le (by decide : (40 : Nat) ≤ 96)
        (hdisj (si, 96) (by simp [runAttemptCells]) j hj)
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
  refine ⟨⟨hAr, S, Nd, hWT, h4cells, hdisj4, hntx, hPay, hReq⟩, hnvh, hnwd, S, Nd, hWT,
    fun i hi => ?_, fun i hi => hdisj i (mem_runAttemptCells_nt2 hi).1⟩
  obtain ⟨hmem, hcase⟩ := mem_runAttemptCells_nt2 hi
  refine ⟨(hcells i hmem).1, ?_, (hcells i hmem).2.2⟩
  rcases hcase with rfl | rfl | rfl | hnn
  · exact hsi96In
  · exact hplIn
  · exact hrqIn
  · exact (hcells i hmem).2.1.resolve_left hnn

/-- Every R32 `run_attempt` entry state satisfies the null-tolerant strong
guard. -/
theorem inputReadyStrongNT2_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyR32 s) : GbodyRunAttemptNT2.InputReadyStrong s :=
  inputAtStrongNT2_of_r32 h

/-! ### The null-tolerant `run_attempt` bound -/

/-- `GbodyRunAttemptNT2.gbody_run_attempt_strong_of` with the 20 leaf premises
discharged exactly as in `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`.
The five sub-`run_attempt` hypotheses stay premises; `hexec`, `hph` and `wph`
are at the null-tolerant guards of `GbodyRunAttemptNT2`, `wsi` and `wvhs` are
unchanged. -/
theorem gbody_run_attempt_nt2_r32
    (hexec : TerminatingFunBoundedOn GbodyRunAttemptNT2.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WorldKeeps GbodyRunAttemptNT2.InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeadersStrong (ofString "validate_headers")) :
    TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt» :=
  GbodyRunAttemptNT2.gbody_run_attempt_strong_of
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

/-- The `run_attempt` bound at the R32 guard from the null-tolerant bound
alone: every R32 state satisfies the null-tolerant guard. -/
theorem run_attempt_r32_nt2
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt» :=
  hnt.mono (fun _ hs => inputReadyStrongNT2_of_r32 hs)

/-- The `hra` premise of `MainEntryR32.mainEntryR32` from the null-tolerant
bound alone. This route uses none of the four decode-empty case theorems. -/
theorem hraR32_nt2
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn MainEntryR32.InputReadyR32 (ofString "run_attempt")
      K.«run_attempt» :=
  (run_attempt_r32_nt2 hnt).mono
    (fun _ hs => (R32CanonicalBridges.inputReadyR32CanonBounded_iff _).mp hs)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32
