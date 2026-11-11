import InitECandidate.Solver.Wave8GuestInv.R16Shards.GbodyMain
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputMain
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure1
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_InitProofs
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_ForkEvm
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01
import InitECandidate.Solver.Wave8GuestInv.MergedLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32

/-! # Wave 8 R32 main entry (`mainEntryR32`)

R32 recomposition of `main` terminating-bounded on the covered entry state,
with the honest `RetInputStrongSound` decode post: every `runAttemptCells`
slice is `(0, 0)` (empty list, `ntx = 0`) or `Inside` the heap. This replaces
the legacy `InputAtNwd`-based lane, whose `RetInput` component is false at
`ntx = 0` (`Inside (0, 0) …` fails, see `WkDecodeHostInputMain.lean`).

The only open premises are `whtrR32` (the R32 `htr_new_payload_request`
world-effect contract) and `hra` (`run_attempt` terminating-bounded at the
R32 entry). `hChain`/`hWkPtx` are the R32 statement bundles of
`ContractParts.StrongBridgesR32`, carried as signature markers for the lanes
that close `hra`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ## 1. R32 entry predicates -/

/-- `InputAtWith` at R32 strength: `runAttemptCells` slices may be `(0, 0)`
(empty list) instead of unconditionally `Inside` the heap. -/
def InputAtR32With {F : Type} (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (si : Nat) :
    Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧
    (∀ i ∈ runAttemptCells s si, i.1 % 8 = 0 ∧
      ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i) ∧
    IvlsDisj (runAttemptCells s si) (worldOwned s S Nd) ∧
    PayloadAt s (memW s si) ∧ RequestsAt s (memW s (si + 32))

def InputAtR32 {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  ∃ S Nd, InputAtR32With s S Nd si

/-- The honest `run_attempt` entry guard at R32: `InputAtR32` conjoined with
the two R16 numeric bounds (`nvh` = the validator-header count at `si + 16`,
`nwd` = the withdrawal count at `pl + 56`). They are genuinely true at the
`decode_host_input` exit (the strengthened `RetInputStrongSound` post
provides them) and are what the `GbodyRunAttemptR32` spine needs to
reconstruct `InputAtStrong`. Equivalent to the guard
`R32CanonicalBridges.InputReadyR32CanonBounded`
(= `GbodyRunAttemptR32.InputReadyR32`). -/
def InputReadyR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtR32 s (locN s "si") ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

/-- The R32 replacement of `R16Shards.TopGbodyWk.HtrNewPayloadReady`: the
`InputAt` component becomes `InputAtR32` (the `(0, 0)` slice case is
accepted) and the slice set is `runAttemptCells`; the two R16 numeric
bounds (`nvh` = the validator-header count at `si + 16`, `nwd` = the
withdrawal count at `pl + 56`) are carried, since they are genuinely true at
the `decode_host_input` exit (the strengthened `RetInputStrongSound` post
provides them). -/
def HtrNewPayloadReadyR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputAtR32 s (locN s "si") ∧ IvlsDisj (runAttemptCells s (locN s "si")) [(locN s "out", 32)] ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

/-- `InputReadyWithRoot` at R32 strength, now carrying the two R16 numeric
bounds (`nvh`/`nwd`): they hold at the `decode_host_input` exit (the
strengthened `RetInputStrongSound` post) and are preserved by the `alloc`
resume (every read address lies in the unhit `(si, 96)` / `(pl, 136)`
slices). -/
def InputReadyWithRootR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_rt : BitVec 64, ∃ S Nd : List Nat,
    InputAtR32With s S Nd w_si.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "root") = some (.val (.word w_rt)) ∧
    w_rt.toNat % 8 = 0 ∧
    Inside (w_rt.toNat, 32) sourceBase (globN s "heap_ptr") ∧
    IvlsDisj [(w_rt.toNat, 32)] (worldOwned s S Nd) ∧
    IvlsDisj (runAttemptCells s w_si.toNat) [(w_rt.toNat, 32)] ∧
    memW s (w_si.toNat + 16) < 2 ^ 32 ∧
    memW s (memW s w_si.toNat + 56) < 2 ^ 32

theorem inputAtR32With_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (S Nd : List Nat) (si : Nat) :
    InputAtR32With { s with locals := locals, clock := k } S Nd si ↔ InputAtR32With s S Nd si := by
  simp only [InputAtR32With, worldTypedWith_with_locals, arenaReady_with_locals]
  exact Iff.rfl

theorem inputAtR32_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k si : Nat) :
    InputAtR32 { s with locals := locals, clock := k } si ↔ InputAtR32 s si := by
  constructor
  · rintro ⟨S, Nd, h⟩
    exact ⟨S, Nd, (inputAtR32With_with_locals s locals k S Nd si).1 h⟩
  · rintro ⟨S, Nd, h⟩
    exact ⟨S, Nd, (inputAtR32With_with_locals s locals k S Nd si).2 h⟩

theorem localsOnly_inputReadyR32 : LocalsOnly ["si"] InputReadyR32 := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  refine ⟨?_, ?_, ?_⟩
  · show InputAtR32 _ _
    rw [ht]
    exact (inputAtR32_with_locals s locals k _).2 hP.1
  · rw [ht]; exact hP.2.1
  · rw [ht]; exact hP.2.2

theorem inputReadyR32_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyR32 s) : GuestInv s := by
  obtain ⟨⟨S, Nd, hIA⟩, _, _⟩ := h
  exact hIA.1.1

theorem inputReadyWithRootR32_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyWithRootR32 s) : GuestInv s := by
  obtain ⟨_, _, _, _, hIA, _⟩ := h
  exact hIA.1.1

theorem callEntryOn_inputReadyR32 {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e) (hp : e.1 = [(ofString "si", .one)]) :
    CallEntryOn InputReadyR32 InputReadyR32 fname [.var .local (ofString "si")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "si") .one b r (by rw [hcode]; exact hl) values
    body' callee ret' hargs hlook
  have hsi : locN (callEntryStateHOLFinite state callee) "si" = locN state "si" := by
    simp only [locN, callEntryStateHOLFinite, hc]
  refine ⟨?_, ?_, ?_⟩
  · show InputAtR32 (callEntryStateHOLFinite state callee) (locN (callEntryStateHOLFinite state callee) "si")
    rw [hsi]
    exact (inputAtR32_with_locals state callee (state.clock - 1) _).2 hP.1
  · rw [hsi]; exact hP.2.1
  · rw [hsi]; exact hP.2.2

/-! ## 2. Preservation of `InputAtR32With` under a world step -/

/-- `runAttemptCells` slices are disjoint from a shrunken global buffer
region (the `inputCells` analogue; uniform in the slice values). -/
theorem runAttemptCells_disj_bufferRegion_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {si : Nat} (hdisj_ow : IvlsDisj (runAttemptCells s si) (worldOwned s S Nd))
    (gn : String × Nat) (hgn : gn ∈ globalBuffers) (n : Nat) (hle : n ≤ gn.2) :
    ∀ i ∈ runAttemptCells s si, Disj i (bufferRegion s (gn.1, n)) := by
  intro i hi
  have hd := hdisj_ow i hi (bufferRegion s gn) (bufferRegion_mem_worldOwned s S Nd hgn)
  by_cases hz : globN s gn.1 = 0
  · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
  · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
    unfold Disj at hd ⊢; dsimp only at hd ⊢; omega

/-- The `runAttemptCells` values are unchanged when every slice is unhit
(each read address lies in an unhit slice). -/
theorem runAttemptCells_eq_of_unhit_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {si : Nat}
    (hcells : ∀ i ∈ runAttemptCells s si, i.1 % 8 = 0 ∧
      ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i)
    (hlim : globN s "heap_ptr" ≤ 2 ^ 64)
    (hu : ∀ c ∈ runAttemptCells s si, IvlUnhit s post c) :
    runAttemptCells post si = runAttemptCells s si := by
  have hs := hcells (si, 96) (by simp [runAttemptCells])
  have hp := hcells (memW s si, 136) (by simp [runAttemptCells])
  have hsi_in : Inside (si, 96) sourceBase (globN s "heap_ptr") := by
    rcases hs.2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have hpl_in : Inside (memW s si, 136) sourceBase (globN s "heap_ptr") := by
    rcases hp.2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have hsi : ∀ off, off % 8 = 0 → off + 8 ≤ 96 → memW post (si + off) = memW s (si + off) := by
    intro off ho hb
    exact memW_eq_of_ivlUnhit (hu (si, 96) (by simp [runAttemptCells]))
      (by have := hs.1; omega) (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hpl : ∀ off, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (memW s si + off) = memW s (memW s si + off) := by
    intro off ho hb
    exact memW_eq_of_ivlUnhit (hu (memW s si, 136) (by simp [runAttemptCells]))
      (by have := hp.1; omega) (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  have h0 : memW post si = memW s si := by simpa using hsi 0 (by decide) (by decide)
  simp only [runAttemptCells, h0, hsi 32 (by decide) (by decide),
    hpl 32 (by decide) (by decide), hpl 40 (by decide) (by decide),
    hsi 40 (by decide) (by decide), hsi 48 (by decide) (by decide),
    hsi 56 (by decide) (by decide), hsi 64 (by decide) (by decide),
    hsi 72 (by decide) (by decide), hsi 80 (by decide) (by decide)]

/-- A world step preserves `InputAtR32With`: `(0, 0)` slices stay unhit
trivially, `Inside` slices survive via `heap_ivl_survives_step`, and the
payload/requests headers are re-established from the fixed-size unhit
slices. -/
theorem worldStep_preserves_inputAtR32With
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (h : InputAtR32With s S Nd si) (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s))
    (hnvh : memW s (si + 16) < 2 ^ 32) (hnwd : memW s (memW s si + 56) < 2 ^ 32) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ InputAtR32With post S' Nd' si ∧ Q s r post S' Nd' ∧
      memW post (si + 16) < 2 ^ 32 ∧ memW post (memW post si + 56) < 2 ^ 32 := by
  obtain ⟨hAs, hWT, hcells, hdisj_ow, hPay, hReq⟩ := h
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hw
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT ht
  have hold_z := worldOwned_zero_aligned hWT
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hlim : globN s "heap_ptr" ≤ 2 ^ 64 := by omega
  have hsi_mem : (si, 96) ∈ runAttemptCells s si := by simp [runAttemptCells]
  have hpl_mem : (memW s si, 136) ∈ runAttemptCells s si := by simp [runAttemptCells]
  have hsi_in : Inside (si, 96) sourceBase (globN s "heap_ptr") := by
    rcases (hcells _ hsi_mem).2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have hpl_in : Inside (memW s si, 136) sourceBase (globN s "heap_ptr") := by
    rcases (hcells _ hpl_mem).2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have hsurv : ∀ c ∈ runAttemptCells s si,
      ((c.1 = 0 ∧ c.2 = 0) ∨ Inside c sourceBase (globN post "heap_ptr")) ∧
      (∀ o ∈ worldOwned post S' Nd', Disj c o) ∧ IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hal, horc, hword⟩ := hcells c hcm
    rcases horc with ⟨h0, h0'⟩ | hin
    · refine ⟨Or.inl ⟨h0, h0'⟩, fun o _ => Or.inl h0', fun a _ hhit => ?_⟩
      have hc00 : c = (0, 0) := Prod.ext h0 h0'
      rw [hc00] at hhit
      exact absurd hhit (GbodyC17ToC21Common.not_cellHits_zero a.toNat)
    · obtain ⟨hin_post, hdisj, hunhit⟩ := heap_ivl_survives_step hAs.2 hhp hog hfr hold_z hz
        hal hword.2.1 hin (fun j hj => hdisj_ow c hcm j hj) (fun j hj => hc c hcm j hj)
      exact ⟨Or.inr hin_post, hdisj, hunhit⟩
  have hunhit : ∀ c ∈ runAttemptCells s si, IvlUnhit s post c := fun c hcm => (hsurv c hcm).2.2
  have hsi_u := hunhit _ hsi_mem
  have hpl_u := hunhit _ hpl_mem
  have hsi_al := (hcells _ hsi_mem).1
  have hpl_al := (hcells _ hpl_mem).1
  have hsi_eq : ∀ off, off % 8 = 0 → off + 8 ≤ 96 →
      memW post (si + off) = memW s (si + off) := fun off ho hb =>
    memW_eq_of_ivlUnhit hsi_u (by have := hsi_al; omega) (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hpl_eq : ∀ off, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (memW s si + off) = memW s (memW s si + off) := fun off ho hb =>
    memW_eq_of_ivlUnhit hpl_u (by have := hpl_al; omega) (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  have hsi0 : memW post si = memW s si := by simpa using hsi_eq 0 (by decide) (by decide)
  have heq : runAttemptCells post si = runAttemptCells s si := by
    simp only [runAttemptCells, hsi0, hsi_eq 32 (by decide) (by decide),
      hpl_eq 32 (by decide) (by decide), hpl_eq 40 (by decide) (by decide),
      hsi_eq 40 (by decide) (by decide), hsi_eq 48 (by decide) (by decide),
      hsi_eq 56 (by decide) (by decide), hsi_eq 64 (by decide) (by decide),
      hsi_eq 72 (by decide) (by decide), hsi_eq 80 (by decide) (by decide)]
  refine ⟨S', Nd', hsub, ⟨hAp, hWT', ?_, ?_, ?_, ?_⟩, hQ, ?_, ?_⟩
  · rw [heq]
    intro c hcm
    obtain ⟨hal, horc, hword⟩ := hcells c hcm
    rcases horc with ⟨h0, h0'⟩ | hin
    · exact ⟨hal, Or.inl ⟨h0, h0'⟩, wordsOK_transfer hAs.1 hAp.1 hword⟩
    · exact ⟨hal, (hsurv c hcm).1, wordsOK_transfer hAs.1 hAp.1 hword⟩
  · rw [heq]
    exact fun c hcm => (hsurv c hcm).2.1
  · rw [hsi0]
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hPay.1, ?_, ?_, ?_⟩
    · rw [hpl_eq 24 (by decide) (by decide)]; exact hPay.2.1
    · rw [hpl_eq 40 (by decide) (by decide)]; exact hPay.2.2.1
    · rw [hpl_eq 32 (by decide) (by decide), hpl_eq 40 (by decide) (by decide)]
      intro idx hidx
      have htx_mem : (memW s (memW s si + 32), 16 * memW s (memW s si + 40)) ∈
          runAttemptCells s si := by simp [runAttemptCells]
      obtain ⟨hal_t, hor_t, hword_t⟩ := hcells _ htx_mem
      rcases hor_t with ⟨h0_t, h0_t'⟩ | hin_t
      · exact absurd hidx (by have := h0_t'; omega)
      · have hu_t := hunhit _ htx_mem
        have hce : memW post (memW s (memW s si + 32) + 16 * idx + 8) =
            memW s (memW s (memW s si + 32) + 16 * idx + 8) :=
          memW_eq_of_ivlUnhit hu_t (by have := hal_t; omega)
            (by have := hin_t.2; omega) ⟨by omega, by omega⟩
        rw [hce]
        exact hPay.2.2.2 idx hidx
  · rw [hsi_eq 32 (by decide) (by decide)]
    refine ⟨wordsOK_transfer hAs.1 hAp.1 hReq.1, fun idx hidx => ?_⟩
    have hrq_mem : (memW s (si + 32), 80) ∈ runAttemptCells s si := by simp [runAttemptCells]
    obtain ⟨hal_r, hor_r, hword_r⟩ := hcells _ hrq_mem
    rcases hor_r with ⟨h0_r, h0_r'⟩ | hin_r
    · exact absurd h0_r' (by omega)
    · have hu_r := hunhit _ hrq_mem
      have hce : memW post (memW s (si + 32) + 16 * idx + 8) =
          memW s (memW s (si + 32) + 16 * idx + 8) :=
        memW_eq_of_ivlUnhit hu_r (by have := hal_r; omega)
          (by have := hin_r.2; omega) ⟨by omega, by omega⟩
      rw [hce]
      exact hReq.2 idx hidx
  · rw [hsi_eq 16 (by decide) (by decide)]
    exact hnvh
  · rw [hsi0, hpl_eq 56 (by decide) (by decide)]
    exact hnwd

/-! ## 3. The R32 attempt chain (`run_attempt` → … → `verify_stateless_new_payload`) -/

theorem «attemptR32_l1» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l1") K.«attempt_l1» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l1», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l1, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_run_attempt»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_run_attempt, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l1»; omega

theorem «attemptR32_l2» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l1") K.«attempt_l1») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l2") K.«attempt_l2» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l2», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l2, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l1»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l1, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l2»; omega

theorem «attemptR32_l3» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l2") K.«attempt_l2») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l3") K.«attempt_l3» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l3», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l3, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l2»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l2, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l3»; omega

theorem «attemptR32_l4» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l3") K.«attempt_l3») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l4") K.«attempt_l4» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l4», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l4, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l3»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l3, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l4»; omega

theorem «attemptR32_l5» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l4") K.«attempt_l4») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l5") K.«attempt_l5» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l5», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l5, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l4»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l4, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l5»; omega

theorem «attemptR32_l6» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l5") K.«attempt_l5») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l6") K.«attempt_l6» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l6», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l6, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l5»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l5, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l6»; omega

theorem «attemptR32_l7» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l6") K.«attempt_l6») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l7") K.«attempt_l7» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l7», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l7, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32 «lookup_attempt_l6»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l6, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l7»; omega

theorem «attemptR32_vsnp» :
    (TerminatingFunBoundedOn InputReadyR32 (ofString "attempt_l7") K.«attempt_l7») →
    TerminatingFunBoundedOn InputReadyR32 (ofString "verify_stateless_new_payload")
      K.«verify_stateless_new_payload» := by
  intro h1
  refine ⟨_, _, _, «lookup_verify_stateless_new_payload», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32) _ (by decide) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32_guestInv _ _ _
            (TerminatingProgBoundedOn.of_clock (seq_clock
              (fun s => _root_.InitECandidate.Solver.Wave8GuestInv.clock_assign s _ _ _)
              (fun s => _root_.InitECandidate.Solver.Wave8GuestInv.clock_assign s _ _ _))) _
            (callEntryOn_inputReadyR32 «lookup_attempt_l7»
              (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l7, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
                InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
          inputReadyR32_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))) ?_
  unfold K.«verify_stateless_new_payload»; omega

/-! ## 4. Spine helper lemmas -/

private theorem decCall_ne_none_of_cont {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hc : ∀ {F2 : Type} (t : PanSemStateFiniteExact 64 F2), (evaluateHOLFiniteState t cont).1 ≠ none) :
    (evaluateHOLFiniteState s (.decCall name sh fname args cont)).1 ≠ none := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨b, cal, rsh⟩
    · simp
    · dsimp only
      split_ifs with hz
      · simp
      · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨res, post⟩
        cases res with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split_ifs
            · dsimp only; exact hc _
            · simp
          | _ => simp

private theorem seq3_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.return e))))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | some _ => simp
  | none =>
    dsimp only; rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
    cases r2 with
    | some _ => simp
    | none =>
      dsimp only; rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState s2 p3 with ⟨r3, s3⟩
      cases r3 with
      | some _ => simp
      | none => exact return_ne_none s3 e

/-- The R32 decode Hoare: from `WorldOK` before the `decode_host_input`
call-with-handler, the fall-through result state carries an `si` local with
`InputAtR32` (the honest `RetInputStrongSound` post, `(0, 0)` slices
accepted). -/
theorem hdhi_hoare_r32 : ∀ (handler : ProgHOL 64),
    (∀ {F : Type} (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t handler).1 ≠ none) →
    Hoare WorldOK
      (.call (some (some (.local, ofString "si"), some (ofString "SszErr", ofString "err_code", handler)))
        (ofString "decode_host_input") [])
      (fun r t => r = none →
        ∃ w_si : BitVec 64, t.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
          InputAtR32 t w_si.toNat ∧
          memW t (w_si.toNat + 16) < 2 ^ 32 ∧
          memW t (memW t w_si.toNat + 56) < 2 ^ 32) := by
  intro handler hh_ne
  exact R16Shards.Hoare.callHandleDest_fall
      (R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound)
      (callEntryOn_of_localsFree localsFree_worldOK _ _) hh_ne
      (fun s callee post v _ hW hstep => by
        obtain ⟨hAs, S, hS⟩ := hW
        obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
        have hWT_entry := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hWT
        have hws := hstep (Or.inl ⟨v, rfl⟩)
        obtain ⟨S', Nd', _, hWT', _, _, hQ⟩ := hws.2.2.2.2 S Nd hWT_entry (fun i hi j hj => by
          change i ∈ [bufferRegion (callEntryStateHOLFinite s callee) ("ssz_offs", 64)] at hi
          simp only [List.mem_singleton] at hi; subst hi
          exact bufferRegion_disj_le hWT_entry ("ssz_offs", 64) (by decide) (by decide) 64 le_rfl j hj)
        obtain ⟨w_si, rfl, hcells, hdisj_ow, hntx63, hPay, hReq, hnvh, hnwd⟩ := hQ v rfl
        have hAp := hws.1
        have hIA_post : InputAtR32With post S' Nd' w_si.toNat :=
          ⟨hAp, hWT',
           fun i hi => by
             obtain ⟨hal, horc, hword⟩ := hcells i hi
             rcases horc with ⟨h0, h0'⟩ | hin
             · exact ⟨hal, Or.inl ⟨h0, h0'⟩, hword⟩
             · exact ⟨hal, Or.inr ⟨Nat.le_trans hAs.2.1 hin.1, hin.2⟩, hword⟩,
           hdisj_ow, hPay, hReq⟩
        set resSt := setVarHOLFinite (ofString "si") (.val (.word w_si)) { post with locals := s.locals }
        exact ⟨w_si,
          by simp [resSt, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
          ⟨S', Nd', (inputAtR32With_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post⟩,
          hnvh, hnwd⟩)

/-- The R32 `alloc` resume: from the `si`-local guard with `InputAtR32`,
`alloc 32` into `root` establishes `InputReadyWithRootR32`. -/
theorem resumeOn_alloc32_inputReadyR32
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn
      (fun s => ∃ w_si : BitVec 64, s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
        InputAtR32 s w_si.toNat ∧
        memW s (w_si.toNat + 16) < 2 ^ 32 ∧
        memW s (memW s w_si.toNat + 56) < 2 ^ 32)
      InputReadyWithRootR32
      (ofString "root") (ofString "alloc") [.const 32#64] := by
  intro F state values body callee ret value post hcode ⟨w_si, hlu_si, hIA0, hnvh0, hnwd0⟩ hargs hl hrun
  obtain ⟨S, Nd, hIA⟩ := hIA0
  have hAs := hIA.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact GbodyC17ToC21Common.lookup_alloc_fn) (.const 32#64) (.val (.word 32#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 32 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
    (localsFree_arenaReady state callee (state.clock - 1) hAs) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_rt, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hfb_in : Inside (w_rt.toNat, 32) (globN state "heap_ptr") (globN post "heap_ptr") := hfb.2.1
  have hIA_entry : InputAtR32With (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
    (inputAtR32With_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  obtain ⟨S', Nd', _, hIA_post, hQ, _, _⟩ :=
    worldStep_preserves_inputAtR32With hIA_entry hws
      (fun _ hj => by simp at hj) (fun _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
      hnvh0 hnwd0
  obtain ⟨w_rt', hw_eq, hav⟩ := hQ (.val (.word w_rt)) rfl
  injection hw_eq with hw_eq'; injection hw_eq' with hw_eq''; subst hw_eq''
  dsimp only at hav; rw [hn_loc] at hav
  set resumed := setVarHOLFinite (ofString "root") (.val (.word w_rt)) { post with locals := state.locals }
  have hsi_mem : (w_si.toNat, 96) ∈ runAttemptCells state w_si.toNat := by simp [runAttemptCells]
  have hpl_mem : (memW state w_si.toNat, 136) ∈ runAttemptCells state w_si.toNat := by
    simp [runAttemptCells]
  have hsi_in : Inside (w_si.toNat, 96) sourceBase (globN state "heap_ptr") := by
    rcases (hIA.2.2.1 _ hsi_mem).2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have hpl_in : Inside (memW state w_si.toNat, 136) sourceBase (globN state "heap_ptr") := by
    rcases (hIA.2.2.1 _ hpl_mem).2.1 with ⟨_, h0'⟩ | hin
    · exact absurd h0' (by omega)
    · exact hin
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hhp_lim : globN state "heap_ptr" ≤ heapLimit := hAs.2.2.1
  obtain ⟨_, hhp_grow, _, _, hStep0⟩ := hws
  obtain ⟨S1, Nd1, _, _, hog1, hfr1, _⟩ := hStep0 S Nd hIA_entry.2.1 (fun _ hx => by simp at hx)
  have hold_z := worldOwned_zero_aligned hIA_entry.2.1
  have hsi_u := (heap_ivl_survives_step hAs.2 hhp_grow hog1 hfr1 hold_z (fun _ hx => by simp at hx)
    (hIA.2.2.1 _ hsi_mem).1 (hIA.2.2.1 _ hsi_mem).2.2.2.1 hsi_in
    (fun j hj => hIA.2.2.2.1 _ hsi_mem j hj) (fun _ hx => by simp at hx)).2.2
  have hpl_u := (heap_ivl_survives_step hAs.2 hhp_grow hog1 hfr1 hold_z (fun _ hx => by simp at hx)
    (hIA.2.2.1 _ hpl_mem).1 (hIA.2.2.1 _ hpl_mem).2.2.2.1 hpl_in
    (fun j hj => hIA.2.2.2.1 _ hpl_mem j hj) (fun _ hx => by simp at hx)).2.2
  have hsi_eq : ∀ off, off % 8 = 0 → off + 8 ≤ 96 →
      memW post (w_si.toNat + off) = memW state (w_si.toNat + off) := fun off ho hb =>
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hpl_eq : ∀ off, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (memW state w_si.toNat + off) = memW state (memW state w_si.toNat + off) :=
    fun off ho hb =>
      memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).1; omega)
        (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  have hsi0_eq : memW post w_si.toNat = memW state w_si.toNat :=
    memW_eq_of_ivlUnhit hsi_u (hIA.2.2.1 _ hsi_mem).1
      (by have := hsi_in.2; omega) ⟨le_rfl, by omega⟩
  have hsi32_eq : memW post (w_si.toNat + 32) = memW state (w_si.toNat + 32) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi40_eq : memW post (w_si.toNat + 40) = memW state (w_si.toNat + 40) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi48_eq : memW post (w_si.toNat + 48) = memW state (w_si.toNat + 48) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi56_eq : memW post (w_si.toNat + 56) = memW state (w_si.toNat + 56) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi64_eq : memW post (w_si.toNat + 64) = memW state (w_si.toNat + 64) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi72_eq : memW post (w_si.toNat + 72) = memW state (w_si.toNat + 72) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hsi80_eq : memW post (w_si.toNat + 80) = memW state (w_si.toNat + 80) :=
    memW_eq_of_ivlUnhit hsi_u (by have := (hIA.2.2.1 _ hsi_mem).1; omega)
      (by have := hsi_in.2; omega) ⟨by omega, by omega⟩
  have hpl32_eq : memW post (memW state w_si.toNat + 32) = memW state (memW state w_si.toNat + 32) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).1; omega)
      (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  have hpl40_eq : memW post (memW state w_si.toNat + 40) = memW state (memW state w_si.toNat + 40) :=
    memW_eq_of_ivlUnhit hpl_u (by have := (hIA.2.2.1 _ hpl_mem).1; omega)
      (by have := hpl_in.2; omega) ⟨by omega, by omega⟩
  have hic_disj_rt : IvlsDisj (runAttemptCells post w_si.toNat) [(w_rt.toNat, 32)] := by
    intro c hc x hx
    simp only [List.mem_singleton] at hx; subst hx
    have hic_eq : runAttemptCells post w_si.toNat = runAttemptCells state w_si.toNat := by
      simp only [runAttemptCells, hsi0_eq, hsi32_eq, hpl32_eq, hpl40_eq, hsi40_eq,
        hsi48_eq, hsi56_eq, hsi64_eq, hsi72_eq, hsi80_eq]
    rw [hic_eq] at hc
    rcases (hIA.2.2.1 c hc).2.1 with ⟨_, h0''⟩ | hinc
    · exact Or.inl h0''
    · exact Or.inr (Or.inr (Or.inl (Nat.le_trans hinc.2 hfb_in.1)))
  have hmemR : ∀ a, memW resumed a = memW post a := fun _ => rfl
  have hnw_res : memW resumed (memW resumed w_si.toNat + 56) < 2 ^ 32 := by
    have h0 : memW resumed w_si.toNat = memW state w_si.toNat := by
      rw [hmemR _]; exact hsi0_eq
    rw [h0, hmemR _]
    rw [hpl_eq 56 (by decide) (by decide)]
    exact hnwd0
  refine ⟨w_si, w_rt, S', Nd',
    (inputAtR32With_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
    by have hne : ofString "root" ≠ ofString "si" := by decide
       simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_si],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hfb.1, ⟨Nat.le_trans hAs.2.1 hfb_in.1, hfb_in.2⟩, hav, hic_disj_rt,
    by rw [hmemR _]; rw [hsi_eq 16 (by decide) (by decide)]; exact hnvh0,
    hnw_res⟩

/-- The R32 `htr_new_payload_request` Hoare: from `InputReadyWithRootR32`
before the call, the fall-through result state satisfies `InputReadyR32`. -/
theorem hoare_htr_inputReadyR32
    (whtrR32 : WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request")) :
    Hoare InputReadyWithRootR32
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")])
      (fun r t => r = none → InputReadyR32 t) := by
  refine ⟨fun {F} state hcode hIR _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_rt, S, Nd, hIA, hlu_si, hlu_rt, hrt8, _, hdisj_rt, hdisj_ic_rt, hnvh_st, hnwd_st⟩ := hIR
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "si"), .var .local (ofString "root")] =
      some [.val (.word w_si), .val (.word w_rt)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hlu_si, hlu_rt]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "htr_new_payload_request")
      [.val (.word w_si), .val (.word w_rt)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "htr_new_payload_request")
              (ofString "si") (ofString "out") .one .one _ _
              (by rw [hcode]; exact R16Shards.lookup_htr_new_payload_request_fn)
              (.var .local (ofString "si")) (.var .local (ofString "root"))
              (.val (.word w_si)) (.val (.word w_rt))
              [.val (.word w_si), .val (.word w_rt)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hlu_si)
              (by simpa [evalAt, evalHOLExact] using hlu_rt) hargs hl
            have hsi_loc : locN (callEntryStateHOLFinite state callee) "si" = w_si.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.1]
            have hout_loc : locN (callEntryStateHOLFinite state callee) "out" = w_rt.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.2]
            have hIA_entry : InputAtR32With (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtR32With_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            have hmemE : ∀ a, memW (callEntryStateHOLFinite state callee) a = memW state a := fun _ => rfl
            have hReady_entry : HtrNewPayloadReadyR32 (callEntryStateHOLFinite state callee) := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [hsi_loc]; exact ⟨S, Nd, hIA_entry⟩
              · rw [hsi_loc, hout_loc]; exact hdisj_ic_rt
              · rw [hsi_loc, hmemE _]; exact hnvh_st
              · rw [hsi_loc]; simp only [hmemE]; exact hnwd_st
            have hstep := FunSpec.at_lookup whtrR32 state hcode _ body callee ret hl
              hReady_entry (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨v, rfl⟩)
            have hhz : ∀ j ∈ [(locN (callEntryStateHOLFinite state callee) "out", 32),
                bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)],
                j.2 = 0 → j.1 % 8 = 0 := by
              intro j hj
              simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · intro h0; dsimp at h0; omega
              · exact bufferRegion_zero_aligned _ "ssz_len_chunk" 32 (by omega)
            have hht : IvlsDisj [(locN (callEntryStateHOLFinite state callee) "out", 32),
                bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)]
                (worldTypedIvls (callEntryStateHOLFinite state callee) S Nd) := by
              intro j hj k hk
              simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · exact hdisj_rt (w_rt.toNat, 32) (by simp) k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
              · exact bufferRegion_disj_le hIA_entry.2.1 ("ssz_len_chunk", 32) (by decide) (by decide) 32 le_rfl k hk
            have hhi : IvlsDisj (runAttemptCells (callEntryStateHOLFinite state callee) w_si.toNat)
                [(locN (callEntryStateHOLFinite state callee) "out", 32),
                 bufferRegion (callEntryStateHOLFinite state callee) ("ssz_len_chunk", 32)] := by
              intro i hi j hj
              simp only [hout_loc, List.mem_cons, List.not_mem_nil, or_false] at hj
              rcases hj with rfl | rfl
              · exact hdisj_ic_rt i hi (w_rt.toNat, 32) (by simp)
              · exact runAttemptCells_disj_bufferRegion_le hIA_entry.2.2.2.1 ("ssz_len_chunk", 32) (by decide) 32 le_rfl i hi
            obtain ⟨S', Nd', _, hIA_post, hQ, hnvh_post, hnwd_post⟩ :=
              worldStep_preserves_inputAtR32With hIA_entry hws hhz hht hhi hnvh_st hnwd_st
            have hIR_res : InputReadyR32 { post with locals := state.locals } := by
              have hloc_si : locN { post with locals := state.locals } "si" = w_si.toNat := by
                simp [locN, hlu_si]
              show InputAtR32 _ _ ∧ _ ∧ _
              rw [hloc_si]
              exact ⟨⟨S', Nd', (inputAtR32With_with_locals post state.locals post.clock S' Nd' w_si.toNat).2 hIA_post⟩,
                hnvh_post, hnwd_post⟩
            rwa [hpost_eq] at hIR_res
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

/-! ## 5. The R32 main-entry composition -/

/-- The R32 main entry: `main` terminating-bounded on the covered entry
state, recomposed from the proved leaves over the honest `RetInputStrongSound`
decode post. Open premises: `whtrR32` and `hra`; `hChain`/`hWkPtx` are the
R32 statement bundles carried as lane markers. -/
theorem mainEntryR32 (hChain : ChainHandlersR32Stmt) (hWkPtx : WkProcessTransactionStmtR32)
    (whtrR32 : WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request"))
    (hra : TerminatingFunBoundedOn InputReadyR32 (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn MainEntry (ofString "main") K.«main» := by
  have hal := Merged.fb_alloc
  have hblake := R11Adapters.«fb_blake2_init»
  have hbls := R10Shards.P26_P28.fb_bls_precompiles_init
  have hbn := R10Shards.P26_P28.fb_bn254_init
  have hdhi := R11Adapters.«fb_decode_host_input»
  have hevm := R11Adapters.«fb_evm_init»
  have hfork := R11Adapters.«fb_fork_init»
  have hhdr := Merged.fb_header_init
  have hhtr := R11Adapters.«fb_htr_new_payload_request»
  have hkeccak := R10Shards.P26_P28.fb_keccak_init
  have hmem := Merged.fb_mem_init
  have hmz := Merged.fb_memzero
  have hmpt := R11Adapters.«fb_mpt_init»
  have houtw := Merged.fb_output_write
  have hrmd := R10Shards.P26_P28.fb_ripemd160_init
  have hsecp := R10Shards.P26_P28.fb_secp256k1_init
  have hser := Merged.fb_serialize_result
  have hsha := R10Shards.P26_P28.fb_sha256_init
  have hssz := Merged.fb_ssz_init
  have hu256 := R10Shards.P26_P28.fb_u256_ws_init
  have hvsnp := «attemptR32_vsnp» («attemptR32_l7» («attemptR32_l6» («attemptR32_l5»
    («attemptR32_l4» («attemptR32_l3» («attemptR32_l2» («attemptR32_l1» hra)))))))
  have wal := R13Shards.WkShard01.«wk_alloc»
  have rtal := R13Shards.WkShard01.«rt_alloc»
  have wblake := R10Shards.P26_P28.wk_blake2_init
  have wbls := R10Shards.P26_P28.wk_bls_precompiles_init
  have wbn := R10Shards.P26_P28.wk_bn254_init
  have wevm := R10Shards.P26_P28.wk_evm_init
  have wfork := R10Shards.P26_P28.wk_fork_init
  have whdr := R10Shards.P26_P28.wk_header_init
  have wkeccak := R10Shards.P26_P28.wk_keccak_init
  have wmpt := R10Shards.P26_P28.wk_mpt_init
  have wrmd := R10Shards.P26_P28.wk_ripemd160_init
  have rosecp := R10Shards.P26_P28.ro_secp256k1_init
  have wsha := R10Shards.P26_P28.wk_sha256_init
  have wssz := R10Shards.P26_P28.wk_ssz_init
  have wu256 := R10Shards.P26_P28.wk_u256_ws_init
  have hmem_world := mem_init_world
  have wmz := Merged.wk_memzero
  have hw_blake : KeepsOn WorldOK WorldOK (ofString "blake2_init") := by
    apply wblake.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("b2_iv", 64), bufferRegion s ("b2_sigma", 80)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("b2_iv", 64), by decide, by decide, rfl⟩
    · exact ⟨("b2_sigma", 80), by decide, by decide, rfl⟩
  have hw_bls : KeepsOn WorldOK WorldOK (ofString "bls_precompiles_init") := by
    apply wbls.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("bls_c", 7136), bufferRegion s ("bls_discount", 2048)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("bls_c", 7136), by decide, by decide, rfl⟩
    · exact ⟨("bls_discount", 2048), by decide, by decide, rfl⟩
  have hw_bn : KeepsOn WorldOK WorldOK (ofString "bn254_init") := by
    apply wbn.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("bn_expw", 352), bufferRegion s ("bn_gamma", 384)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨("bn_expw", 352), by decide, by decide, rfl⟩
    · exact ⟨("bn_gamma", 384), by decide, by decide, rfl⟩
  have hw_evm : KeepsOn WorldOK WorldOK (ofString "evm_init") := by
    apply wevm.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("evm_empty", 8), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("null_address", 24),
      bufferRegion s ("transfer_topic", 32), bufferRegion s ("vm_system_address", 24)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("evm_empty", 8), by decide, by decide, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
    · exact ⟨("null_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("transfer_topic", 32), by decide, by decide, rfl⟩
    · exact ⟨("vm_system_address", 24), by decide, by decide, rfl⟩
  have hw_fork : KeepsOn WorldOK WorldOK (ofString "fork_init") := by
    apply wfork.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("beacon_roots_address", 24), bufferRegion s ("builder_deposit_address", 24),
      bufferRegion s ("builder_exit_address", 24), bufferRegion s ("consolidation_request_address", 24),
      bufferRegion s ("deposit_contract_address", 24), bufferRegion s ("deposit_event_signature_hash", 32),
      bufferRegion s ("history_storage_address", 24), bufferRegion s ("precompile_addrs", 360),
      bufferRegion s ("withdrawal_request_address", 24), bufferRegion s ("zero32", 32)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨("beacon_roots_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("builder_deposit_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("builder_exit_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("consolidation_request_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("deposit_contract_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("deposit_event_signature_hash", 32), by decide, by decide, rfl⟩
    · exact ⟨("history_storage_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("precompile_addrs", 360), by decide, by decide, rfl⟩
    · exact ⟨("withdrawal_request_address", 24), by decide, by decide, rfl⟩
    · exact ⟨("zero32", 32), by decide, by decide, rfl⟩
  have hw_hdr : KeepsOn WorldOK WorldOK (ofString "header_init") := by
    apply whdr.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("hdr_zero8", 8)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("hdr_zero8", 8), by decide, by decide, rfl⟩
  have hw_keccak : KeepsOn WorldOK WorldOK (ofString "keccak_init") := by
    apply wkeccak.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("keccak_rc", 192)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("keccak_rc", 192), by decide, by decide, rfl⟩
  have hw_mpt : KeepsOn WorldOK WorldOK (ofString "mpt_init") := by
    apply wmpt.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("empty_code_hash", 32), bufferRegion s ("empty_trie_root", 32),
      bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact ⟨("empty_code_hash", 32), by decide, by decide, rfl⟩
    · exact ⟨("empty_trie_root", 32), by decide, by decide, rfl⟩
    · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
    · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
    · exact ⟨("mpt_hash_scratch", 40), by decide, by decide, rfl⟩
  have hw_rmd : KeepsOn WorldOK WorldOK (ofString "ripemd160_init") := by
    apply wrmd.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("rmd_tab", 160)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("rmd_tab", 160), by decide, by decide, rfl⟩
  have hw_secp : KeepsOn WorldOK WorldOK (ofString "secp256k1_init") :=
    rosecp.keepsOn localsFree_worldOK worldOK_guestInv
  have hw_ssz : KeepsOn WorldOK WorldOK (ofString "ssz_init") := by
    apply wssz.keepsOn_buffers; intro F s i hi
    change i ∈ [bufferRegion s ("zero_hashes", 2048)] at hi
    simp only [List.mem_singleton] at hi; subst hi
    exact ⟨("zero_hashes", 2048), by decide, by decide, rfl⟩
  have hmem_hoare : Hoare MainEntry (.call (some (none, none)) (ofString "mem_init") [])
      (fun r t => r = none → WorldOK t) :=
    Hoare.call0 hmem_world
      (callEntryOn_of_imp (Q := fun s => GuestInv s ∧ GlobalsZero s)
        (fun s locals k ⟨hg, hz⟩ => ⟨guestInv_with_locals_clock s locals k hg, hz⟩)
        (fun _ h => ⟨h.1.1, h.2.2⟩) _ _)
      (fun s _ post v _ _ hq _ => localsFree_worldOK post s.locals post.clock (hq v rfl))
      (fun _ _ hr _ h => absurd h hr)
  refine ⟨_, _, _, lookup_main_fn, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_main,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply TerminatingProgBoundedOn.mono_bound
  · exact TerminatingProgBoundedOn.seq_hoare_trans
      (TerminatingProgBoundedOn.call_on hmem _ _ (callEntryOn_of_imp localsFree_guestInv (fun _ h => h.1.1) _ _))
      hmem_hoare
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hsha _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK wsha.keepsOn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hkeccak _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_keccak _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hssz _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_ssz _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hmpt _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_mpt _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hu256 _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK wu256.keepsOn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hsecp _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_secp _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hbn _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_bn _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hbls _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_bls _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hrmd _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_rmd _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hblake _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_blake _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hhdr _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_hdr _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hevm _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_evm _)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hfork _ _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
        (Hoare.call_keeps localsFree_worldOK hw_fork _)
      (TerminatingProgBoundedOn.decCall_on hal _ _ _
        (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
        (KeepsOn.resumeOn localsFree_worldOK wal.keepsOn _ _)
        (TerminatingProgBoundedOn.decCall_on hal _ _ _
          (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _)
          (resumeOn_alloc_worldWithBuf "z32" 32 (by decide) (by decide) wal rtal)
          (TerminatingProgBoundedOn.seq_hoare_trans
            (TerminatingProgBoundedOn.call_on hmz _ _
              (callEntryOn_of_imp localsFree_guestInv worldWithBuf_guestInv _ _))
            (hoare_memzero_worldWithBuf "z32" 32 (by decide) wmz)
            (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
              (TerminatingProgBoundedOn.dec_on localsFree_worldOK _ _ _
                (TerminatingProgBoundedOn.seq_hoare_trans
                  (TerminatingProgBoundedOn.callHandle_on hdhi worldOK_guestInv _ _ _
                    (TerminatingProgBoundedOn.decCall_guestInv hser _ _ _
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.call_guestInv houtw _ _)
                          (TerminatingProgBoundedOn.seq_guestInv
                            (GbodyC17ToC21Common.straight_guestInv _ rfl)
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))
                    _ (callEntryOn_of_imp localsFree_guestInv worldOK_guestInv _ _))
                  (hdhi_hoare_r32 _ (fun t => decCall_ne_none_of_cont t _ _ _ _ _
                    (fun u => seq3_return_ne_none u _ _ _ _)))
                  (TerminatingProgBoundedOn.decCall_on hal _ _ _
                    (callEntryOn_of_imp (P := fun s => ∃ w_si : BitVec 64,
                        s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧ InputAtR32 s w_si.toNat ∧
                        memW s (w_si.toNat + 16) < 2 ^ 32 ∧
                        memW s (memW s w_si.toNat + 56) < 2 ^ 32)
                      localsFree_guestInv
                      (fun _ ⟨_, _, ⟨S', Nd', hIA⟩, _, _⟩ => hIA.1.1) _ _)
                    (resumeOn_alloc32_inputReadyR32 wal rtal)
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (TerminatingProgBoundedOn.call_on hhtr _ _
                        (callEntryOn_of_imp localsFree_guestInv inputReadyWithRootR32_guestInv _ _))
                      (hoare_htr_inputReadyR32 whtrR32)
                      (TerminatingProgBoundedOn.decCall_on hvsnp _ _ _
                        (callEntryOn_inputReadyR32 lookup_verify_stateless_new_payload_fn
                          (by simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload,
                            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                            Option.map_none, Option.map_some, List.map_cons, List.map_nil,
                            InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural]))
                        (decCallResumeOn_guestInv inputReadyR32_guestInv _ _ _)
                        (TerminatingProgBoundedOn.decCall_guestInv hser _ _ _
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.call_guestInv houtw _ _)
                              (TerminatingProgBoundedOn.seq_guestInv
                                (GbodyC17ToC21Common.straight_guestInv _ rfl)
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))
  · unfold K.«main»; omega

end InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryR32
