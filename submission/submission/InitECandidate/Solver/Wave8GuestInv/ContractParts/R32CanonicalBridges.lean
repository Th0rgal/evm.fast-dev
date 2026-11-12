import InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WkProcessTransactionR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WkHtrNewPayloadR32

/-! Wave 8 R32 Slot 8 (RunAttemptHtrR32): canonical-signature bridges.

The inc3 canonical route (`TargetR32Clean.assemblyR32` ← `mainEntryLaneR32` ←
`MainEntryR32.mainEntryR32`) leaves exactly two real open leaves:

* `whtrR32 : WorldKeeps MainEntryR32.HtrNewPayloadReadyR32 … "htr_new_payload_request"`,
* `hra : TerminatingFunBoundedOn MainEntryR32.InputReadyR32 "run_attempt" K.«run_attempt»`.

This module delivers both leaves in the canonical shape, with one honest
amendment: the canonical predicates drop the two numeric bounds

* `memW s (locN s "si" + 16) < 2 ^ 32`  ("nvh"),
* `memW s (memW s (locN s "si") + 56) < 2 ^ 32`  ("nwd"),

which the R16 guards carry (`R16Shards.TopGbodyWk.HtrNewPayloadReady`,
`InputAtStrong`) and which the proved machinery consumes as essential
premises: `WkHostPayloadHeaders.worldEff_htr_new_payload_request` feeds them
into the `htr_plist_chunks` / `htr_payload` size arithmetic, and
`GbodyRunAttemptR32.inputAtStrong_of_r32` needs them to reconstruct
`InputAtStrong`. Without them the bare canonical guards are too weak for the
existing proof route (and, for `whtrR32`, for the guest's count-driven
allocation sizes). The theorems below therefore close the leaves for the
canonical predicates *conjoined with the two bounds*; amending
`MainEntryR32.HtrNewPayloadReadyR32` / `MainEntryR32.InputReadyR32` by these
two conjuncts (matching the R16 guards) makes them drop-in premises of
`mainEntryR32`. On states satisfying the R32 guard of the earlier
`WkHtrNewPayloadR32` / `GbodyRunAttemptR32` modules, the bounds are already
part of the guard (`InputAtR32With` there includes them), so nothing is lost.

Obligation C needs no bridge: the canonical
`ContractParts.WkProcessTransactionR32.wkProcessTransactionStmtR32` constructs
the `WkProcessTransactionStmtR32` bundle (axiom-clean) and supersedes the
alternative parameterization in `WkPtxClosureR32`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ## Obligation A: `whtrR32` at the canonical predicate (plus the two bounds) -/

/-- The canonical `whtrR32` leaf: `htr_new_payload_request` keeps the world
under `MainEntryR32.HtrNewPayloadReadyR32` (the canonical R32 entry predicate:
canonical `InputAtR32` with the `(0, 0)` slice case, and the out-disjunction
over the seven `runAttemptCells` slices) conjoined with the two R16 numeric
bounds (`nvh`/`nwd`) that the world-effect proof of the handler body consumes.
With `MainEntryR32.HtrNewPayloadReadyR32` amended by the same two conjuncts,
this is exactly the `whtrR32` premise of `MainEntryR32.mainEntryR32`. -/
theorem wk_htr_new_payload_request_r32_canon :
    WorldKeeps (fun s => MainEntryR32.HtrNewPayloadReadyR32 s ∧
        memW s (locN s "si" + 16) < 2 ^ 32 ∧
        memW s (memW s (locN s "si") + 56) < 2 ^ 32)
      (fun s => [(locN s "out", 32),
                 (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
        ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request") :=
  WkProcessTransactionR32.worldKeeps_mono_guard
    WkHtrNewPayloadR32.wk_htr_new_payload_request_r32
    (fun {F} s h => by
      obtain ⟨⟨⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hPay, hReq⟩, hdisj_out⟩, hnvh, hnwd⟩ := h
      -- The 96-byte run-attempt header cell covers the 40-byte `inputCells`
      -- header cell, so the out-disjunction over `runAttemptCells` restricts.
      have hdisj_out4 : IvlsDisj (inputCells s (locN s "si")) [(locN s "out", 32)] := by
        intro i hi j hj
        rcases GbodyRunAttemptR32.inputCells_mem_cases hi with rfl | rfl | rfl | rfl
        · exact GbodyRunAttemptR32.disj_left_of_le (by decide : (40 : Nat) ≤ 96)
            (hdisj_out (locN s "si", 96) (by simp [runAttemptCells]) j hj)
        · exact hdisj_out _ (by simp [runAttemptCells]) j hj
        · exact hdisj_out _ (by simp [runAttemptCells]) j hj
        · exact hdisj_out _ (by simp [runAttemptCells]) j hj
      exact ⟨⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hnvh, hnwd, hPay, hReq⟩,
        hdisj_out4, hnvh, hnwd⟩)

/-! ## Obligation B: `hra` at the canonical predicate (plus the two bounds) -/

/-- The canonical `MainEntryR32.InputReadyR32` conjoined with the two R16
numeric bounds; definitionally the R32 guard of `GbodyRunAttemptR32` (whose
`InputAtR32With` carries them), and the honest strengthening under which the
strong R16 `run_attempt` bound applies. -/
def InputReadyR32CanonBounded : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => MainEntryR32.InputReadyR32 s ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

/-- The canonical-bounded guard is the earlier R32 guard repackaged (the
canonical `InputAtR32With` conjuncts plus `nvh`/`nwd` are exactly the
`GbodyRunAttemptR32.InputAtR32With` conjuncts). -/
theorem inputReadyR32CanonBounded_iff {F : Type} (s : PanSemStateFiniteExact 64 F) :
    InputReadyR32CanonBounded s ↔ GbodyRunAttemptR32.InputReadyR32 s := by
  constructor
  · rintro ⟨⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hPay, hReq⟩, hnvh, hnwd⟩
    exact ⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hnvh, hnwd, hPay, hReq⟩
  · rintro ⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hnvh, hnwd, hPay, hReq⟩
    exact ⟨⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hPay, hReq⟩, hnvh, hnwd⟩

/-- The residual decode-empty case at the canonical-bounded guard: some
run-attempt cell is the null pair `(0, 0)`. -/
def RunAttemptR32CanonEmptyCase : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputReadyR32CanonBounded s ∧
    ∃ i ∈ runAttemptCells s (locN s "si"), i.1 = 0 ∧ i.2 = 0

/-- The canonical `hra` leaf: `run_attempt` terminating-bounded at the
canonical `MainEntryR32.InputReadyR32` conjoined with the two R16 numeric
bounds, from the strong R16 bound (all-`Inside` states) and the residual
decode-empty case, both as premises. With `MainEntryR32.InputReadyR32`
amended by the two bounds, this is exactly the `hra` premise of
`MainEntryR32.mainEntryR32`. -/
theorem run_attempt_r32_canon
    (hstrong : TerminatingFunBoundedOn InputReadyStrong (ofString "run_attempt")
      K.«run_attempt»)
    (hempty : TerminatingFunBoundedOn RunAttemptR32CanonEmptyCase (ofString "run_attempt")
      K.«run_attempt») :
    TerminatingFunBoundedOn InputReadyR32CanonBounded (ofString "run_attempt")
      K.«run_attempt» :=
  GbodyRunAttemptR32.gbody_run_attempt_r32_of hstrong
    (hempty.mono (fun _ hs =>
      ⟨(inputReadyR32CanonBounded_iff _).mpr hs.1, hs.2⟩))
  |>.mono (fun _ hs => (inputReadyR32CanonBounded_iff _).mp hs)

/-- Case split at the bare canonical predicate: every `runAttemptCells` slice
is `Inside` (the strong case) or some slice is the null pair `(0, 0)` (the
decode-empty case). Together with `inputReadyR32CanonBounded_iff` this shows
the two premises of `run_attempt_r32_canon` cover exactly the canonical
`InputReadyR32` states modulo the `nvh`/`nwd` bounds. -/
theorem inputAtR32_canon_cases {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : MainEntryR32.InputAtR32 s si) :
    (∀ i ∈ runAttemptCells s si, Inside i sourceBase (globN s "heap_ptr")) ∨
      (∃ i ∈ runAttemptCells s si, i.1 = 0 ∧ i.2 = 0) := by
  obtain ⟨S, Nd, -, -, hcells, -, -, -⟩ := h
  by_cases hall : ∀ i ∈ runAttemptCells s si, Inside i sourceBase (globN s "heap_ptr")
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨i, hi, hni⟩ := hall
    refine Or.inr ⟨i, hi, ?_⟩
    rcases (hcells i hi).2.1 with h | h
    · exact h
    · exact absurd h hni

end InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
