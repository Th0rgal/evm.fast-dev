import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty

/-! Wave 8 R32 (GbodyRunAttemptNTR32): the witness- and access-list null
cases of `run_attempt`, reduced to one `execute_block` bound at a
null-tolerant guard.

`GbodyRunAttemptR32Empty.hraR32_of` takes the three decode-empty sub-cases
`TxNullCase`, `WitNullCase`, `AccNullCase` as premises (`hTx`, `hWit`,
`hAcc`). Unlike the vh-null case, `run_attempt` does not stop early in these
states: it runs the whole spine into `execute_block`, so none of them is
provable without an `execute_block` bound, and the `hexec` premise cannot
supply it (its guard `BlockReadyExecAttemptStrong` contains
`InputReadyStrong`, false whenever a run-attempt cell is null).

This module closes `hWit` and `hAcc` relative to the null-tolerant replay
`GbodyRunAttemptNT`:

* `gbody_run_attempt_nt_r32` — the `run_attempt` bound at
  `GbodyRunAttemptNT.InputReadyStrong`, with the 20 leaf premises supplied as
  in `GbodyRunAttemptStrongR32` and the five sub-`run_attempt` hypotheses kept
  (`hexec` now at `GbodyRunAttemptNT.BlockReadyExecAttemptStrong`).
* `inputReadyStrongNT_of_r32` — an R32 state whose tx cell is not the null
  pair satisfies the null-tolerant guard.
* `run_attempt_r32_nt` — the bound at `GbodyRunAttemptR32.InputReadyR32` from
  the null-tolerant bound and `hTx` alone.
* `witNullCase_run_attempt`, `accNullCase_run_attempt` — the `hWit` / `hAcc`
  premises of `hraR32_of`, verbatim.
* `hraR32_nt` — the `hra` premise of `MainEntryR32.mainEntryR32` from the
  null-tolerant bound and `hTx`.
* `hexec_of_nt` — the null-tolerant `execute_block` bound implies the `hexec`
  premise of `gbody_run_attempt_strong_r32`.

`hTx` stays a premise: the tx cell is one of `InputAt`'s `inputCells`, so a
null tx cell falsifies the guards of the `payload_header` premises as well. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNTR32

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

/-! ### The null-tolerant cells against the original ones -/

/-- A null-tolerant run-attempt cell is an original run-attempt cell, and it
is one of the four `InputAt` cells or not the null pair. -/
theorem mem_runAttemptCells_nt {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    {i : Ivl} (hi : i ∈ GbodyRunAttemptNT.runAttemptCells s si) :
    i ∈ runAttemptCells s si ∧
      (i = (si, 96) ∨ i = (memW s si, 136) ∨ i = (memW s (si + 32), 80) ∨
        i = (memW s (memW s si + 32), 16 * memW s (memW s si + 40)) ∨
        ¬(i.1 = 0 ∧ i.2 = 0)) := by
  unfold GbodyRunAttemptNT.runAttemptCells at hi
  rcases List.mem_append.1 hi with h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨by simp [runAttemptCells], Or.inl rfl⟩
    · exact ⟨by simp [runAttemptCells], Or.inr (Or.inl rfl)⟩
    · exact ⟨by simp [runAttemptCells], Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨by simp [runAttemptCells], Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · obtain ⟨hm, hp⟩ := List.mem_filter.1 h
    refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inr (of_decide_eq_true hp))))⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · simp [runAttemptCells]
    · simp [runAttemptCells]
    · simp [runAttemptCells]

/-- The strong guard implies the null-tolerant one (fewer cells). -/
theorem inputAtStrongNT_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtStrong s si) : GbodyRunAttemptNT.InputAtStrong s si := by
  obtain ⟨hIn, hnvh, hnwd, S, Nd, hWT, hcells, hdisj⟩ := h
  exact ⟨hIn, hnvh, hnwd, S, Nd, hWT,
    fun i hi => hcells i (mem_runAttemptCells_nt hi).1,
    fun i hi => hdisj i (mem_runAttemptCells_nt hi).1⟩

theorem inputReadyStrongNT_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyStrong s) : GbodyRunAttemptNT.InputReadyStrong s :=
  inputAtStrongNT_of_strong h

/-- The strong `execute_block` entry implies the null-tolerant one. -/
theorem blockReadyExecAttemptStrongNT_of_strong {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : BlockReadyExecAttemptStrong s) :
    GbodyRunAttemptNT.BlockReadyExecAttemptStrong s :=
  ⟨h.1, inputReadyStrongNT_of_strong h.2.1, h.2.2⟩

/-- The null-tolerant `execute_block` bound implies the `hexec` premise of
`GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`. -/
theorem hexec_of_nt
    (hexec : TerminatingFunBoundedOn GbodyRunAttemptNT.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block») :
    TerminatingFunBoundedOn BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block» :=
  hexec.mono (fun _ hs => blockReadyExecAttemptStrongNT_of_strong hs)

/-! ### R32 states with a non-null tx cell -/

/-- An R32 input whose tx cell is not the null pair satisfies the
null-tolerant strong guard: the three header cells have nonzero sizes, so
with the tx cell they are `Inside`, which rebuilds `InputAt`; every remaining
null-tolerant cell is not the null pair, hence `Inside`. -/
theorem inputAtStrongNT_of_r32 {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputAtR32 s si)
    (htx : ¬(memW s (memW s si + 32) = 0 ∧ memW s (memW s si + 40) = 0)) :
    GbodyRunAttemptNT.InputAtStrong s si := by
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
  have htxIn : Inside (memW s (memW s si + 32), 16 * memW s (memW s si + 40))
      sourceBase (globN s "heap_ptr") :=
    htxc.2.1.resolve_left (fun h0 => htx ⟨h0.1, by
      have h16 : 16 * memW s (memW s si + 40) = 0 := h0.2
      omega⟩)
  have h4cells : ∀ i ∈ inputCells s si,
      Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i := by
    intro i hi
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact ⟨inside_of_le (by decide) hsi96In, wordsOK_of_le (by decide) (by decide) hsi96.2.2⟩
    · exact ⟨hplIn, hpl.2.2⟩
    · exact ⟨hrqIn, hrq.2.2⟩
    · exact ⟨htxIn, htxc.2.2⟩
  have hdisj4 : IvlsDisj (inputCells s si) (worldOwned s S Nd) := by
    intro i hi j hj
    rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
    · exact disj_left_of_le (by decide : (40 : Nat) ≤ 96)
        (hdisj (si, 96) (by simp [runAttemptCells]) j hj)
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
    · exact hdisj _ (by simp [runAttemptCells]) j hj
  refine ⟨⟨hAr, S, Nd, hWT, h4cells, hdisj4, hntx, hPay, hReq⟩, hnvh, hnwd, S, Nd, hWT,
    fun i hi => ?_, fun i hi => hdisj i (mem_runAttemptCells_nt hi).1⟩
  obtain ⟨hmem, hcase⟩ := mem_runAttemptCells_nt hi
  refine ⟨(hcells i hmem).1, ?_, (hcells i hmem).2.2⟩
  rcases hcase with rfl | rfl | rfl | rfl | hnn
  · exact hsi96In
  · exact hplIn
  · exact hrqIn
  · exact htxIn
  · exact (hcells i hmem).2.1.resolve_left hnn

/-- An R32 `run_attempt` entry state is null-tolerant-strong or in the
tx-null case. -/
theorem inputReadyR32_cases_nt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : InputReadyR32 s) :
    GbodyRunAttemptNT.InputReadyStrong s ∨ TxNullCase s := by
  by_cases htx : memW s (memW s (locN s "si") + 32) = 0 ∧
      memW s (memW s (locN s "si") + 40) = 0
  · exact Or.inr ⟨h, htx.1, htx.2⟩
  · exact Or.inl (inputAtStrongNT_of_r32 h htx)

/-! ### The null-tolerant `run_attempt` bound -/

/-- `GbodyRunAttemptNT.gbody_run_attempt_strong_of` with the 20 leaf premises
discharged exactly as in `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`.
The five sub-`run_attempt` hypotheses stay premises; `hexec` is at the
null-tolerant `GbodyRunAttemptNT.BlockReadyExecAttemptStrong`, the other four
are the unchanged `hph`, `wph`, `wsi`, `wvhs`. -/
theorem gbody_run_attempt_nt_r32
    (hexec : TerminatingFunBoundedOn GbodyRunAttemptNT.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WorldKeeps InputReady
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
    TerminatingFunBoundedOn GbodyRunAttemptNT.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt» :=
  GbodyRunAttemptNT.gbody_run_attempt_strong_of
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

/-- The `run_attempt` bound at the R32 guard from the null-tolerant bound and
the tx-null sub-case alone: every R32 state outside `TxNullCase` satisfies
the null-tolerant guard (`inputReadyR32_cases_nt`). -/
theorem run_attempt_r32_nt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt»)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt» := by
  obtain ⟨p, b, rs, hlk, hrun⟩ := hnt
  obtain ⟨p2, b2, rs2, hlk2, hrun2⟩ := hTx
  rw [hlk] at hlk2
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk2
  refine ⟨p, b, rs, hlk, fun state hcode hp => ?_⟩
  rcases inputReadyR32_cases_nt hp with h | h
  · exact hrun state hcode h
  · exact hrun2 state hcode h

/-- The `hra` premise of `MainEntryR32.mainEntryR32` from the null-tolerant
bound and `hTx` alone. The null-tolerant guard also covers the vh-list-null
states, so this route does not use `GbodyRunAttemptR32VhNull`. -/
theorem hraR32_nt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt»)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn MainEntryR32.InputReadyR32 (ofString "run_attempt")
      K.«run_attempt» :=
  (run_attempt_r32_nt hnt hTx).mono
    (fun _ hs => (R32CanonicalBridges.inputReadyR32CanonBounded_iff _).mp hs)

/-- The witness-list-null sub-case (the `hWit` premise of
`GbodyRunAttemptR32Empty.hraR32_of`) from the null-tolerant bound and `hTx`. -/
theorem witNullCase_run_attempt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt»)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_nt hnt hTx).mono (fun _ hs => hs.1)

/-- The access-list-null sub-case (the `hAcc` premise of
`GbodyRunAttemptR32Empty.hraR32_of`) from the null-tolerant bound and `hTx`. -/
theorem accNullCase_run_attempt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt»)
    (hTx : TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_nt hnt hTx).mono (fun _ hs => hs.1)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNTR32
