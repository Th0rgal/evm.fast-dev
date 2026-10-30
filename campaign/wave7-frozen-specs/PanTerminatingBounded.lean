import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.PanRunBoundedExt
import InitECandidate.Solver.GuestUniformClockBound
import InitECandidate.Solver.HeapPotential

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# `InitECandidate.Solver.PanTerminatingBounded` — Terminating-Run Clock Bounds & Potential Frameworks

Frozen interface (`1 Cluster = 1 Leaf File < 350 LOC = 1 Worker`) for bounding `PanSem` ticks
consumed along runs that do NOT time out (`res ≠ some .timeOut`).

By `UniformSourceClock.source_terminate_minimal_input_clock` and
`UniformSourceClock.covered_source_pan_not_timeOut_at_uniform_clock`, any covered source run
(`declaredGasLimit input ≤ 200000000`, `sourceBehaviour input = .terminate outcome events`,
`coveredOutcome outcome`) has a finite minimal terminating clock `k_min`. Proving that every
non-`.timeOut` evaluation from `{ s_decls with clock := k }` consumes at most `K_pan_max` ticks
(`k - s_post.clock ≤ K_pan_max`) unconditionally establishes `CoveredSourceTicksConsumedBounded K_pan_max`
and `pan_not_timeOut` at `K_pan_max`—even for functions (such as open-addressed hash-table probes,
scratch-arena explicit stacks, binary extended GCD, polynomial GCD, and the EVM `run_frames` loop)
whose termination relies on runtime invariants or the non-`.timeOut` hypothesis itself.
-/

namespace InitECandidate.Solver.PanTerminatingBounded

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock

/-! ## 1. Core `TerminatingRunBounded`, `TerminatingProgBounded`, and `TerminatingFunBounded` -/

/-- Along any `PanSem` run of `prog` from `state` that does NOT time out (`res ≠ some .timeOut`),
at most `K` clock ticks are consumed (`state.clock - post.clock ≤ K`, equivalently
`state.clock ≤ post.clock + K`). -/
def TerminatingRunBounded {F : Type}
    (state : PanSemStateFiniteExact 64 F) (prog : ProgHOL 64) (K : Nat) : Prop :=
  let out := evaluateHOLFiniteState state prog
  out.1 ≠ some .timeOut →
    state.clock ≤ out.2.clock + K ∧ out.2.clock ≤ state.clock

/-- State-predicate-guarded `TerminatingProgBounded`: under `state.code = originalRuntimeCode`
and precondition `P state`, any non-`.timeOut` run of `prog` consumes at most `K` ticks. -/
def TerminatingProgBoundedOn
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (prog : ProgHOL 64) (K : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode →
    P state →
    TerminatingRunBounded state prog K

/-- Unconditional `TerminatingProgBounded` (`P = True`). -/
def TerminatingProgBounded (prog : ProgHOL 64) (K : Nat) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode →
    TerminatingRunBounded state prog K

/-- Function-level `TerminatingFunBounded`: `fname` is installed in `originalRuntimeCode` and its
body consumes at most `K` ticks on every non-`.timeOut` entry call. -/
def TerminatingFunBounded (fname : MlS) (K : Nat) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    TerminatingProgBounded body K

/-! ## 2. Scratch-Stack & EVM Frame Potentials -/

/-- Scratch arena start (`2952790016 = 0xb0000000`) and initial limit (`2965299200 = 0xb0bee000`),
giving `12,509,184` bytes (`≤ 521,216` 24-byte stack frames before `scratch_alloc` traps with 7). -/
def scratchBaseAddr : Nat := 2952790016
def scratchTopLimit : Nat := 2965299200
def maxScratchFrames24 : Nat := (scratchTopLimit - scratchBaseAddr) / 24

theorem maxScratchFrames24_eq : maxScratchFrames24 = 521216 := rfl

/-- Scratch-arena Remaining Capacity Potential (in bytes) when `scratch_ptr` holds `p`. -/
def scratchBytesRemaining {F : Type} (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.globals.lookup (ofString "scratch_ptr") with
  | some (.val (.word p)) => scratchTopLimit - p.toNat
  | _ => 0

/-- Abstract EVM Frame Execution Potential `Phi = 2050 * totalGas + 2 * activeFrames`, bounded by
`2050 * 200_000_000 + 2 * 1025 = 410_000_002_050` on covered 200M-gas inputs. -/
def evmFramePotential (totalGas activeFrames : Nat) : Nat :=
  2050 * totalGas + 2 * activeFrames

def maxEvmFramePotential : Nat := evmFramePotential maxCoveredGas 1025

theorem maxEvmFramePotential_eq : maxEvmFramePotential = 410000002050 := rfl

/-! ## 3. Bridging `ProgBounded` / `FunBounded` into `TerminatingProgBounded` / `TerminatingFunBounded` -/

theorem TerminatingRunBounded.weaken {F : Type}
    {state : PanSemStateFiniteExact 64 F} {prog : ProgHOL 64} {K K' : Nat}
    (h : TerminatingRunBounded state prog K) (hle : K ≤ K') :
    TerminatingRunBounded state prog K' := by
  intro hnt
  obtain ⟨h1, h2⟩ := h hnt
  exact ⟨by omega, h2⟩

theorem TerminatingProgBounded.weaken {prog : ProgHOL 64} {K K' : Nat}
    (h : TerminatingProgBounded prog K) (hle : K ≤ K') :
    TerminatingProgBounded prog K' :=
  fun state hcode => (h state hcode).weaken hle

theorem TerminatingFunBounded.weaken {fname : MlS} {K K' : Nat}
    (h : TerminatingFunBounded fname K) (hle : K ≤ K') :
    TerminatingFunBounded fname K' := by
  obtain ⟨params, body, retShape, hlook, hbody⟩ := h
  exact ⟨params, body, retShape, hlook, hbody.weaken hle⟩

/-- Every total `ProgBounded prog K` immediately yields `TerminatingProgBounded prog K`
at ANY initial clock `state.clock` via `UniformSourceClock.evaluateHOLFiniteState_ticks_consumed_invariant`! -/
theorem terminatingProgBounded_of_progBounded {prog : ProgHOL 64} {K : Nat}
    (h : ProgBounded prog K) :
    TerminatingProgBounded prog K := by
  intro F state hcode hnt
  have hle_clk : (evaluateHOLFiniteState state prog).2.clock ≤ state.clock :=
    evaluateHOLFiniteState_clock_le state prog
  rcases hrun : evaluateHOLFiniteState state prog with ⟨res, post⟩
  rw [hrun] at hnt hle_clk
  have hb := h { state with clock := K } hcode (Nat.le_refl K)
  rcases hrunK : evaluateHOLFiniteState { state with clock := K } prog with ⟨resK, postK⟩
  rw [hrunK] at hb
  obtain ⟨hspentK, hkeptK, hntK⟩ := hb
  have hstate_eq : ({ state with clock := state.clock } : PanSemStateFiniteExact 64 F) = state := by
    cases state; rfl
  have hrun' : evaluateHOLFiniteState { state with clock := state.clock } prog = (res, post) := by
    simpa only [hstate_eq] using hrun
  obtain ⟨_, _, hticks⟩ :=
    evaluateHOLFiniteState_ticks_consumed_invariant prog state post postK res resK state.clock K
      hrun' hnt hrunK hntK
  dsimp only at hspentK hkeptK hle_clk ⊢
  exact ⟨by omega, hle_clk⟩

/-- Every total `FunBounded fname K` immediately lifts to `TerminatingFunBounded fname K`. -/
theorem terminatingFunBounded_of_funBounded {fname : MlS} {K : Nat}
    (h : FunBounded fname K) :
    TerminatingFunBounded fname K := by
  obtain ⟨params, body, retShape, hlook, hprog⟩ := h
  exact ⟨params, body, retShape, hlook, terminatingProgBounded_of_progBounded hprog⟩

/-! ## 4. Structural Combinators for `TerminatingProgBounded` -/

theorem TerminatingProgBounded.straight (prog : ProgHOL 64)
    (hs : extStraightLine prog = true) :
    TerminatingProgBounded prog 0 :=
  terminatingProgBounded_of_progBounded (ProgBounded.straight prog hs)

theorem TerminatingProgBounded.seq {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBounded first a)
    (h2 : TerminatingProgBounded second b) :
    TerminatingProgBounded (.seq first second) (a + b) := by
  intro F state hcode hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  unfold TerminatingRunBounded
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  rw [hr1] at hmeta hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simp [hr1]
    obtain ⟨s1, k1⟩ := h1 state hcode hnt1
    rw [hr1] at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hnt
    exact ⟨by omega, by omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hnt1 : (evaluateHOLFiniteState state first).1 ≠ some .timeOut := by simpa [hr1] using hnt
    obtain ⟨s1, k1⟩ := h1 state hcode hnt1
    rw [hr1] at s1 k1
    exact ⟨by omega, k1⟩

theorem TerminatingProgBounded.ite {cond : ExpHOL 64} {yes no : ProgHOL 64} {a b : Nat}
    (hyes : TerminatingProgBounded yes a)
    (hno : TerminatingProgBounded no b) :
    TerminatingProgBounded (.ite cond yes no) (max a b) := by
  intro F state hcode hnt
  unfold TerminatingRunBounded at hnt ⊢
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  split at hnt ⊢
  · split at hnt ⊢
    · exact (hno state hcode hnt).weaken (Nat.le_max_right a b)
    · exact (hyes state hcode hnt).weaken (Nat.le_max_left a b)
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem TerminatingProgBounded.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBounded body K) :
    TerminatingProgBounded (.dec name shape init body) K := by
  intro F state hcode hnt
  unfold TerminatingRunBounded at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  split at hnt ⊢
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · split at hnt ⊢
    · rename_i val _ _
      have hb := hbody (setVarHOLFinite name val state) hcode hnt
      simpa using hb
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

/-! ## 5. Reduction from `TerminatingFunBounded "main"` to `CoveredSourceTicksConsumedBounded` -/

/-- Master bridge: if `"main"` satisfies `TerminatingFunBounded (ofString "main") K_body`,
then every covered input run consumes at most `K_body + 1` ticks (`CoveredSourceTicksConsumedBounded (K_body + 1)`),
and therefore `pan_not_timeOut` holds uniformly at `K_pan_max = K_body + 1`! -/
theorem coveredSourceTicksConsumedBounded_of_terminatingMain
    {K_body : Nat}
    (hmain : TerminatingFunBounded (ofString "main") K_body)
    (hmain_zero_args : ∃ retShape body,
      originalRuntimeCode.lookup (ofString "main") = some ([], body, retShape) ∧
      TerminatingProgBounded body K_body) :
    CoveredSourceTicksConsumedBounded (K_body + 1) := by
  intro input outcome events _hgas _hsource _hcov stCtxt s_decls _hst hdecls k res s_post hrun hnt
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  have hcode : s_decls.code = originalRuntimeCode := by
    rw [hmeta.code]
    exact B2PostDecls.map_ext rfl
  obtain ⟨retShape, body, hlook, hbody⟩ := hmain_zero_args
  rw [evaluateHOLFiniteState_call] at hrun
  have hargs : evalListHOLFinite { s_decls with clock := k }
      (h := fun a => Classical.propDecidable (({ s_decls with clock := k } :
        PanSemStateFiniteExact 64 Guest.HostMemory).memaddrs a)) [] = some [] := rfl
  rw [hargs] at hrun
  dsimp only at hrun
  have hlookup_call : lookupCodeHOLFinite ({ s_decls with clock := k } :
      PanSemStateFiniteExact 64 Guest.HostMemory).code.lookup (ofString "main") [] =
      some (body, HolFiniteMapExact.empty, retShape) := by
    change lookupCodeHOLFinite s_decls.code.lookup (ofString "main") [] = _
    rw [hcode]
    unfold lookupCodeHOLFinite
    simp [lookupCodeHOLExact, hlook]
  rw [hlookup_call] at hrun
  dsimp only at hrun
  by_cases hk0 : k = 0
  · subst hk0
    simp at hrun
    rcases hrun with ⟨rfl, _⟩
    exact absurd rfl hnt
  · simp only [hk0, ↓reduceIte] at hrun
    let entry := callEntryStateHOLFinite { s_decls with clock := k } HolFiniteMapExact.empty
    have hentry_code : entry.code = originalRuntimeCode := hcode
    have hentry_clk : entry.clock = k - 1 := rfl
    rcases hb_run : evaluateHOLFiniteState entry body with ⟨bres, bpost⟩
    have hkept_raw : bpost.clock ≤ entry.clock := by
      have hle := evaluateHOLFiniteState_clock_le entry body
      rw [hb_run] at hle
      exact hle
    have hfix : fixClockHOLFinite entry (bres, bpost) = (bres, bpost) := by
      simp [fixClockHOLFinite, Nat.not_lt.mpr hkept_raw]
    rw [hb_run, hfix] at hrun
    have hb_nt : bres ≠ some .timeOut := by
      intro hbt
      subst hbt
      simp at hrun
      rcases hrun with ⟨rfl, _⟩
      exact hnt rfl
    have hb_bound := hbody entry hentry_code (by rw [hb_run]; exact hb_nt)
    rw [hb_run] at hb_bound
    obtain ⟨hspent, _⟩ := hb_bound
    have hpost_clk : s_post.clock = bpost.clock := by
      cases bres with
      | none => simp at hrun; obtain ⟨_, rfl⟩ := hrun; rfl
      | some r =>
        cases r <;> simp [emptyLocalsHOLFinite] at hrun
        all_goals (try split at hrun) <;> obtain ⟨_, rfl⟩ := hrun <;> rfl
    omega

end InitECandidate.Solver.PanTerminatingBounded
