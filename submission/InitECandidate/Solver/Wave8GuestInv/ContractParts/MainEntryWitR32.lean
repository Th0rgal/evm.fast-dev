import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptWitR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Null

/-! Wave 8 R32 (MainEntryWitR32): the R32 main entry with the witness-slice
fact carried from the `decode_host_input` exit to the `run_attempt` call.

`GbodyRunAttemptWitR32` bounds `run_attempt` without the `state_init` world
premise, at the guard `InputReadyNull Z ∧ WS`. `MainEntryR32.mainEntryR32_honest`
calls `run_attempt` at `InputReadyR32`, which says nothing about the witness
slices. This module replays that composition at the guard
`InputReadyR32W = InputReadyR32 ∧ WitSlices (si)`.

The witness-slice fact has to come from `decode_host_input`. The proved
contract `wk_decode_host_input_strong_sound` does not state it, so it is a
premise here, `WdwLeaf`: when `decode_host_input` returns the word `w` from a
`WorldOK` state, every 16-byte slice record of the witness list of `w` is
`WitnessSliceOK` in the exit state. It is preserved by the `alloc 32` and
`htr_new_payload_request` steps (the input cells are unhit) and by the
attempt chain (which only renames locals). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryWitR32

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
open InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryR32
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32.Wit (WitSlices)

/-! ## 1. The premise and the guards -/

/-- The witness-slice post of `decode_host_input`: from a `WorldOK` state, a
returned word `w` has `WitSlices` in the exit state. -/
abbrev WdwLeaf : Prop :=
  FunSpec WorldOK
    (fun _ r post => ∀ w : BitVec 64, r = some (.returned (.val (.word w))) →
      WitSlices post w.toNat)
    (ofString "decode_host_input")

/-- `MainEntryR32.InputReadyR32` with the witness-slice fact at the local `si`. -/
def InputReadyR32W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputReadyR32 s ∧ WitSlices s (locN s "si")

/-- `MainEntryR32.InputReadyWithRootR32` with the witness-slice fact at the local `si`. -/
def InputReadyWithRootR32W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => InputReadyWithRootR32 s ∧ WitSlices s (locN s "si")

/-- Two specifications of one function at the same guard, conjoined. -/
theorem funSpec_and {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (h : FunSpec P Q fname) (h' : FunSpec P Q' fname) :
    FunSpec P (fun s r post => Q s r post ∧ Q' s r post) fname := by
  obtain ⟨ps, b, rs, hl, hq⟩ := h
  obtain ⟨ps', b', rs', hl', hq'⟩ := h'
  rw [hl] at hl'
  obtain ⟨rfl, rfl, rfl⟩ : ps = ps' ∧ b = b' ∧ rs = rs' := by simpa using hl'
  exact ⟨ps, b, rs, hl, fun s hc hp hv hnt => ⟨hq s hc hp hv hnt, hq' s hc hp hv hnt⟩⟩

theorem localsOnly_inputReadyR32W : LocalsOnly ["si"] InputReadyR32W := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "si" (hl "si" (by simp))
  refine ⟨localsOnly_inputReadyR32 s locals k hl hP.1, ?_⟩
  show WitSlices { s with locals := locals, clock := k } (locN { s with locals := locals, clock := k } "si")
  rw [ht]; exact hP.2

theorem inputReadyR32W_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyR32W s) : GuestInv s :=
  inputReadyR32_guestInv s h.1

theorem inputReadyWithRootR32W_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : InputReadyWithRootR32W s) : GuestInv s :=
  inputReadyWithRootR32_guestInv s h.1

theorem callEntryOn_inputReadyR32W {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e) (hp : e.1 = [(ofString "si", .one)]) :
    CallEntryOn InputReadyR32W InputReadyR32W fname [.var .local (ofString "si")] := by
  have h0 : CallEntryOn InputReadyR32 InputReadyR32 fname [.var .local (ofString "si")] :=
    callEntryOn_inputReadyR32 hl hp
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "si") .one b r (by rw [hcode]; exact hl) values
    body' callee ret' hargs hlook
  have hsi : locN (callEntryStateHOLFinite state callee) "si" = locN state "si" := by
    simp only [locN, callEntryStateHOLFinite, hc]
  refine ⟨h0 state values body' callee ret' hcode hP.1 hargs hlook, ?_⟩
  show WitSlices (callEntryStateHOLFinite state callee) (locN (callEntryStateHOLFinite state callee) "si")
  rw [hsi]; exact hP.2

/-! ## 2. `WitSlices` under a world step -/

/-- The input cells are unhit by a world step whose regions avoid them. -/
theorem worldStep_cells_unhit
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {si : Nat}
    (h : InputAtR32With s S Nd si) (hw : WorldStep R gw keep Q s r post)
    (hz : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (ht : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hc : IvlsDisj (runAttemptCells s si) (R s)) :
    ∀ c ∈ runAttemptCells s si, IvlUnhit s post c := by
  obtain ⟨hAs, hWT, hcells, hdisj_ow, _, _⟩ := h
  obtain ⟨_, hhp, _, _, hStep⟩ := hw
  obtain ⟨S', Nd', _, _, hog, hfr, _⟩ := hStep S Nd hWT ht
  have hold_z := worldOwned_zero_aligned hWT
  intro c hcm
  obtain ⟨hal, horc, hword⟩ := hcells c hcm
  rcases horc with ⟨h0, h0'⟩ | hin
  · intro a _ hhit
    have hc00 : c = (0, 0) := Prod.ext h0 h0'
    rw [hc00] at hhit
    exact absurd hhit (GbodyC17ToC21Common.not_cellHits_zero a.toNat)
  · exact (heap_ivl_survives_step hAs.2 hhp hog hfr hold_z hz
      hal hword.2.1 hin (fun j hj => hdisj_ow c hcm j hj) (fun j hj => hc c hcm j hj)).2.2

/-- `WitSlices` survives a step that leaves the input cells unhit. -/
theorem witSlices_unhit_r32 {F : Type} {s post : PanSemStateFiniteExact 64 F} {si : Nat}
    (hcells : ∀ i ∈ runAttemptCells s si, i.1 % 8 = 0 ∧
      ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i)
    (hhp_lim : globN s "heap_ptr" ≤ heapLimit)
    (hgs : GuestInv s) (hg : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hu : ∀ c ∈ runAttemptCells s si, IvlUnhit s post c)
    (hW : WitSlices s si) : WitSlices post si := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hsi_rc := hcells (si, 96) (by simp [runAttemptCells])
  have hsi_in : Inside (si, 96) sourceBase (globN s "heap_ptr") :=
    GbodyRunAttemptNullR32.inside_of_nullOrInside (by simp) hsi_rc.2.1
  have hsi_lt : si + 96 ≤ 2 ^ 64 := by unfold Inside at hsi_in; omega
  have hsi8 : si % 8 = 0 := hsi_rc.1
  have hsi_unhit := hu (si, 96) (by simp [runAttemptCells])
  have h40 : memW post (si + 40) = memW s (si + 40) :=
    memW_eq_of_ivlUnhit hsi_unhit (by omega) hsi_lt ⟨by omega, by omega⟩
  have h48 : memW post (si + 48) = memW s (si + 48) :=
    memW_eq_of_ivlUnhit hsi_unhit (by omega) hsi_lt ⟨by omega, by omega⟩
  intro j hj
  rw [h48] at hj
  rw [h40]
  have hsl := hW j hj
  have hmem : (memW s (si + 40), 16 * memW s (si + 48)) ∈ runAttemptCells s si := by
    simp [runAttemptCells]
  have hw_rc := hcells _ hmem
  have hw_in : Inside (memW s (si + 40), 16 * memW s (si + 48)) sourceBase
      (globN s "heap_ptr") :=
    GbodyRunAttemptNullR32.inside_of_nullOrInside
      (by show 16 * memW s (si + 48) ≠ 0; omega) hw_rc.2.1
  have hw_unhit := hu _ hmem
  have hw_lt : memW s (si + 40) + 16 * memW s (si + 48) ≤ 2 ^ 64 := by
    have := hw_in.2; dsimp only at this; omega
  have ha8 : memW s (si + 40) % 8 = 0 := hw_rc.1
  have hp : memW post (memW s (si + 40) + 16 * j) = memW s (memW s (si + 40) + 16 * j) :=
    memW_eq_of_ivlUnhit hw_unhit (by omega) hw_lt
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hn : memW post (memW s (si + 40) + 16 * j + 8) =
      memW s (memW s (si + 40) + 16 * j + 8) :=
    memW_eq_of_ivlUnhit hw_unhit (by omega) hw_lt
      ⟨by dsimp only; omega, by dsimp only; omega⟩
  exact R16Shards.EvmEkFk.StorageCreateFinish.witnessSliceOK_of_preserved hsl
    (wordsOK_transfer hgs hg hsl.1) hhp hp hn

/-! ## 3. The attempt chain at `InputReadyR32W` -/

theorem «attemptR32W_l1» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "run_attempt") K.«run_attempt») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l1") K.«attempt_l1» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l1», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l1, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_run_attempt»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_run_attempt, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l1»; omega

theorem «attemptR32W_l2» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l1") K.«attempt_l1») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l2") K.«attempt_l2» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l2», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l2, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l1»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l1, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l2»; omega

theorem «attemptR32W_l3» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l2") K.«attempt_l2») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l3") K.«attempt_l3» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l3», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l3, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l2»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l2, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l3»; omega

theorem «attemptR32W_l4» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l3") K.«attempt_l3») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l4") K.«attempt_l4» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l4», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l4, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l3»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l3, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l4»; omega

theorem «attemptR32W_l5» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l4") K.«attempt_l4») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l5") K.«attempt_l5» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l5», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l5, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l4»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l4, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l5»; omega

theorem «attemptR32W_l6» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l5") K.«attempt_l5») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l6") K.«attempt_l6» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l6», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l6, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l5»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l5, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l6»; omega

theorem «attemptR32W_l7» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l6") K.«attempt_l6») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l7") K.«attempt_l7» := by
  intro h1
  refine ⟨_, _, _, «lookup_attempt_l7», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l7, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _ (TerminatingProgBoundedOn.of_clock (seq_clock (fun s => clock_shMemStore s _ _ _) (fun s => clock_raise s _ _))) _
          (callEntryOn_inputReadyR32W «lookup_attempt_l6»
            (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l6, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
              InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
        inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))) ?_
  unfold K.«attempt_l7»; omega

theorem «attemptR32W_vsnp» :
    (TerminatingFunBoundedOn InputReadyR32W (ofString "attempt_l7") K.«attempt_l7») →
    TerminatingFunBoundedOn InputReadyR32W (ofString "verify_stateless_new_payload")
      K.«verify_stateless_new_payload» := by
  intro h1
  refine ⟨_, _, _, «lookup_verify_stateless_new_payload», ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals (localsOnly_inputReadyR32W) _ (by decide) _ _
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.callHandle_on h1 inputReadyR32W_guestInv _ _ _
            (TerminatingProgBoundedOn.of_clock (seq_clock
              (fun s => _root_.InitECandidate.Solver.Wave8GuestInv.clock_assign s _ _ _)
              (fun s => _root_.InitECandidate.Solver.Wave8GuestInv.clock_assign s _ _ _))) _
            (callEntryOn_inputReadyR32W «lookup_attempt_l7»
              (by simp only [sourceFunctionEntry, Guest.Software.guestFn_attempt_l7, InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, Option.map_none, Option.map_some, List.map_cons, List.map_nil,
                InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural])))
          inputReadyR32W_guestInv (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))) ?_
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

/-- The decode Hoare of `MainEntryR32.hdhi_hoare_r32` with the witness-slice fact of the
`wdw` premise added to the fall-through state. -/
theorem hdhi_hoare_w (wdw : WdwLeaf) : ∀ (handler : ProgHOL 64),
    (∀ {F : Type} (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t handler).1 ≠ none) →
    Hoare WorldOK
      (.call (some (some (.local, ofString "si"), some (ofString "SszErr", ofString "err_code", handler)))
        (ofString "decode_host_input") [])
      (fun r t => r = none →
        ∃ w_si : BitVec 64, t.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
          InputAtR32 t w_si.toNat ∧
          memW t (w_si.toNat + 16) < 2 ^ 32 ∧
          memW t (memW t w_si.toNat + 56) < 2 ^ 32 ∧
          WitSlices t w_si.toNat) := by
  intro handler hh_ne
  exact R16Shards.Hoare.callHandleDest_fall
      (funSpec_and R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound wdw)
      (callEntryOn_of_localsFree localsFree_worldOK _ _) hh_ne
      (fun s callee post v _ hW hstep => by
        obtain ⟨hAs, S, hS⟩ := hW
        obtain ⟨Nd, hWT⟩ := (worldTyped_iff_with s S).1 hS
        have hWT_entry := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hWT
        have hws := hstep.1 (Or.inl ⟨v, rfl⟩)
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
          hnvh, hnwd, hstep.2 w_si rfl⟩)

/-- The `alloc 32` resume of `MainEntryR32.resumeOn_alloc32_inputReadyR32`, carrying the
witness-slice fact: the input cells are unhit by `alloc`. -/
theorem resumeOn_alloc32_w
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn
      (fun s => ∃ w_si : BitVec 64, s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
        InputAtR32 s w_si.toNat ∧
        memW s (w_si.toNat + 16) < 2 ^ 32 ∧
        memW s (memW s w_si.toNat + 56) < 2 ^ 32 ∧
        WitSlices s w_si.toNat)
      InputReadyWithRootR32W
      (ofString "root") (ofString "alloc") [.const 32#64] := by
  intro F state values body callee ret value post hcode ⟨w_si, hlu_si, hIA0, hnvh0, hnwd0, hW0⟩
    hargs hl hrun
  refine ⟨resumeOn_alloc32_inputReadyR32 wal rtal state values body callee ret value post hcode
    ⟨w_si, hlu_si, hIA0, hnvh0, hnwd0⟩ hargs hl hrun, ?_⟩
  obtain ⟨S, Nd, hIA⟩ := hIA0
  have hAs := hIA.1
  have hW_state : WorldOK state := ⟨hAs, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hIA_entry : InputAtR32With (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
    (inputAtR32With_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
  have hu := worldStep_cells_unhit hIA_entry hws
    (fun _ hj => by simp at hj) (fun _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
  have hWp : WitSlices post w_si.toNat :=
    witSlices_unhit_r32 hIA_entry.2.2.1 hIA_entry.1.2.2.1 hIA_entry.1.1 hws.1.1 hws.2.1 hu hW0
  have hloc : locN (setVarHOLFinite (ofString "root") value { post with locals := state.locals })
      "si" = w_si.toNat := by
    have hne : ofString "root" ≠ ofString "si" := by decide
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne, hlu_si]
  show WitSlices _ (locN _ "si")
  rw [hloc]; exact hWp

/-- The witness-slice fact survives the `htr_new_payload_request` call: its written regions
(`out`, `ssz_len_chunk`) avoid the input cells. -/
theorem hoare_htr_ws
    (whtrR32 : WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request")) :
    Hoare InputReadyWithRootR32W
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")])
      (fun r t => r = none → WitSlices t (locN t "si")) := by
  refine ⟨fun {F} state hcode hIRW _ hr => ?_⟩
  obtain ⟨hIR, hWst⟩ := hIRW
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_rt, S, Nd, hIA, hlu_si, hlu_rt, hrt8, _, hdisj_rt, hdisj_ic_rt, hnvh_st, hnwd_st⟩ := hIR
  have hW0 : WitSlices state w_si.toNat := by
    have hloc : locN state "si" = w_si.toNat := by simp [locN, hlu_si]
    rw [← hloc]; exact hWst
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
            have hu := worldStep_cells_unhit hIA_entry hws hhz hht hhi
            have hWp : WitSlices post w_si.toNat :=
              witSlices_unhit_r32 hIA_entry.2.2.1 hIA_entry.1.2.2.1 hIA_entry.1.1 hws.1.1 hws.2.1
                hu hW0
            have hIR_res : WitSlices { post with locals := state.locals }
                (locN { post with locals := state.locals } "si") := by
              have hloc_si : locN { post with locals := state.locals } "si" = w_si.toNat := by
                simp [locN, hlu_si]
              rw [hloc_si]
              exact hWp
            rwa [hpost_eq] at hIR_res
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

/-- The `htr_new_payload_request` Hoare at the guards with the witness-slice fact. -/
theorem hoare_htr_w
    (whtrR32 : WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request")) :
    Hoare InputReadyWithRootR32W
      (.call (some (none, none)) (ofString "htr_new_payload_request")
        [.var .local (ofString "si"), .var .local (ofString "root")])
      (fun r t => r = none → InputReadyR32W t) :=
  ⟨fun s hc hP hnt hr => ⟨(hoare_htr_inputReadyR32 whtrR32).run s hc hP.1 hnt hr,
    (hoare_htr_ws whtrR32).run s hc hP hnt hr⟩⟩

/-! ## 5. The main-entry composition -/

/-- The R32 main entry with the witness-slice fact carried to `run_attempt`: open premises
`whtrR32`, the decode witness-slice post `wdw`, and `run_attempt` at `InputReadyR32W`. -/
theorem mainEntryR32_wit
    (whtrR32 : WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32), (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request"))
    (wdw : WdwLeaf)
    (hra : TerminatingFunBoundedOn InputReadyR32W (ofString "run_attempt") K.«run_attempt») :
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
  have hvsnp := «attemptR32W_vsnp» («attemptR32W_l7» («attemptR32W_l6» («attemptR32W_l5»
    («attemptR32W_l4» («attemptR32W_l3» («attemptR32W_l2» («attemptR32W_l1» hra)))))))
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
                  (hdhi_hoare_w wdw _ (fun t => decCall_ne_none_of_cont t _ _ _ _ _
                    (fun u => seq3_return_ne_none u _ _ _ _)))
                  (TerminatingProgBoundedOn.decCall_on hal _ _ _
                    (callEntryOn_of_imp (P := fun s => ∃ w_si : BitVec 64,
                        s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧ InputAtR32 s w_si.toNat ∧
                        memW s (w_si.toNat + 16) < 2 ^ 32 ∧
                        memW s (memW s w_si.toNat + 56) < 2 ^ 32 ∧
                        WitSlices s w_si.toNat)
                      localsFree_guestInv
                      (fun _ ⟨_, _, ⟨S', Nd', hIA⟩, _, _, _⟩ => hIA.1.1) _ _)
                    (resumeOn_alloc32_w wal rtal)
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (TerminatingProgBoundedOn.call_on hhtr _ _
                        (callEntryOn_of_imp localsFree_guestInv inputReadyWithRootR32W_guestInv _ _))
                      (hoare_htr_w whtrR32)
                      (TerminatingProgBoundedOn.decCall_on hvsnp _ _ _
                        (callEntryOn_inputReadyR32W lookup_verify_stateless_new_payload_fn
                          (by simp only [sourceFunctionEntry, Guest.Software.guestFn_verify_stateless_new_payload,
                            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                            Option.map_none, Option.map_some, List.map_cons, List.map_nil,
                            InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural]))
                        (decCallResumeOn_guestInv inputReadyR32W_guestInv _ _ _)
                        (TerminatingProgBoundedOn.decCall_guestInv hser _ _ _
                          (TerminatingProgBoundedOn.seq_guestInv
                            (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                            (TerminatingProgBoundedOn.seq_guestInv
                              (TerminatingProgBoundedOn.call_guestInv houtw _ _)
                              (TerminatingProgBoundedOn.seq_guestInv
                                (GbodyC17ToC21Common.straight_guestInv _ rfl)
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _))))))))))))))))))))))))))))
  · unfold K.«main»; omega

/-! ## 6. The `run_attempt` premise and the main lane from the leaves -/

/-- The `hra` premise of `mainEntryR32_wit` from the four leaves `hexec`, `hph`, `wph`, `wvhs`:
`GbodyRunAttemptNullR32.Wit.gbody_run_attempt_wit_r32` at `Z := True`, restricted to the
canonical entry guard with the witness-slice conjunct. No `wsi`. -/
theorem hraW
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header") K.«payload_header»)
    (wph : GbodyRunAttemptNullR32Close.WphAt (GbodyRunAttemptNullR32.InputReadyZ True))
    (wvhs : GbodyRunAttemptNullR32Close.WvhsLeaf) :
    TerminatingFunBoundedOn InputReadyR32W (ofString "run_attempt") K.«run_attempt» :=
  (GbodyRunAttemptNullR32.Wit.gbody_run_attempt_wit_r32 (Z := True) hexec hph wph wvhs).mono
    (fun s hs =>
      ⟨GbodyRunAttemptNullR32Close.inputReadyNull_true_of_r32
        ((R32CanonicalBridges.inputReadyR32CanonBounded_iff s).mp hs.1), hs.2⟩)

/-- The main lane from the canonical `htr_new_payload_request` contract, the decode
witness-slice premise `wdw` and the four `run_attempt` leaves. -/
theorem mainEntryR32_wit_of_leaves
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header") K.«payload_header»)
    (wph : GbodyRunAttemptNullR32Close.WphAt (GbodyRunAttemptNullR32.InputReadyZ True))
    (wdw : WdwLeaf)
    (wvhs : GbodyRunAttemptNullR32Close.WvhsLeaf) :
    TerminatingFunBoundedOn MainEntry (ofString "main") K.«main» :=
  mainEntryR32_wit R32CanonicalBridges.whtrR32 wdw (hraW hexec hph wph wvhs)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryWitR32
