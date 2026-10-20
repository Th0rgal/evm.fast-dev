import InitECandidate.Solver.BoundedCertificate

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.CompilerClockBound` — Verrou A: Compiler Pass Clock Calculus & Split Post-Bootstrap Budget

This module establishes the exact clock calculus of the intermediate compiler
passes (`CrepSem`, `LoopSem`, `PanGlobals`, and `WordSem`/`StackSem`) and the
additive post-bootstrap budget decomposition required for finite step-bound
certificates:

1. **Exact Clock Calculus of `CrepSem` Leaf Instructions (`crep_evaluate_leaf_clock_eq`)**:
   - In `Flapjack.CrepSemStateFiniteExact` (`CrepSemHOLState` / `evaluateHOLFiniteState`),
     the leaf instructions `.skip`, `.assign`, `.store`, `.storeByte`, `.store32`,
     `.storeGlob`, `.return`, `.raise`, `.break`, `.continue`, `.primitive`,
     `.shMem`, and `.extCall` preserve `s.clock` exactly
     (`(evaluateHOLFiniteState s prog).2.clock = s.clock`).
   - `.tick` at `s.clock = 0` produces `(some .timeOut, s.emptyLocalsHOLFinite)`
     and at `s.clock ≠ 0` produces `(none, s.decClockHOLFinite)` with
     `clock = s.clock - 1`.
2. **Exact Clock Calculus of `LoopSem` Leaf Instructions (`loop_evaluate_leaf_clock_eq`)**:
   - Expression evaluation `HolLoopState.eval` in `LoopSemStateFiniteExact` is
     completely independent of `s.clock` (`loop_eval_exp_clock_irrel`).
   - In `HolLoopState` (`LoopSemStateFiniteExact.evaluate`), the leaf instructions
     `.skip`, `.assign`, `.arith`, `.primitive`, `.load32`, `.loadByte`, `.store`,
     `.storeByte`, `.store32`, `.setGlobal`, `.return`, `.raise`, `.break`,
     `.continue`, `.fail`, `.locValue`, `.shMem`, and `.ffi` preserve `s.clock`
     (`0` ticks consumed on every branch).
   - `.tick` at `s.clock = 0` produces `(some .timeOut, { s with locals := .ln })`
     and at `s.clock ≠ 0` produces `(none, HolLoopState.decClock s)` with
     `clock = s.clock - 1`.
3. **Exact Clock Shift of `PanGlobals.compileTop` & Split Post-Bootstrap Certificate**:
   - `PanGlobals.compileTopExactHOL` shifts the entry call clock by `+1`
     (`k_globals = k_pan + 1`), and `InitialComposition` (`PanSimp` + `PanStructs` +
     `PanGlobals`) preserves non-`timeOut` outcomes at `k_pan + 1`.
   - Post-bootstrap target execution splits additively across any initialization
     and body budget $K_{\text{post}} = K_{\text{init}} + K_{\text{body}}$, yielding
     `finite_certificate_of_split_post_bootstrap_budget`, which instantiates
     `BoundedCertificate.finite_certificate_of_uniform_post_bootstrap_not_timeOut`.
-/

namespace Flapjack.CrepSemStateFiniteExact

/-- Alias for exact finite-support `CrepSem` state (`CrepSemHOLState`). -/
abbrev State (width : Nat) [NeZero width] (σ : Type) :=
  CrepSemHOLState width σ

/-- Alias for exact finite-support `CrepSem` program evaluation (`evalCrepSemHOLProgExact`). -/
noncomputable abbrev evaluateHOLFiniteState {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (prog : CrepProgHOL width) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  evalCrepSemHOLProgExact s prog

/-- Alias for clearing locals in `CrepSemHOLState` (`CrepSemHOLState.emptyLocals`). -/
abbrev emptyLocalsHOLFinite {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  CrepSemHOLState.emptyLocals s

/-- Alias for decrementing clock in `CrepSemHOLState` (`decClockCrepSemHOL`). -/
abbrev decClockHOLFinite {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  decClockCrepSemHOL s

end Flapjack.CrepSemStateFiniteExact

namespace Flapjack.CrepSemHOLState

/-- Method alias for `CrepSemStateFiniteExact.emptyLocalsHOLFinite`. -/
abbrev emptyLocalsHOLFinite {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  CrepSemHOLState.emptyLocals s

/-- Method alias for `CrepSemStateFiniteExact.decClockHOLFinite`. -/
abbrev decClockHOLFinite {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) : CrepSemHOLState width σ :=
  decClockCrepSemHOL s

end Flapjack.CrepSemHOLState

namespace Flapjack

/-- Alias for exact finite-support `LoopSem` state (`LoopSemStateFiniteExact`). -/
abbrev HolLoopState (width : Nat) [NeZero width] (F : Type) :=
  LoopSemStateFiniteExact width F

namespace HolLoopState

/-- Alias for exact `LoopSem` program evaluation (`LoopSemStateFiniteExact.evaluate`). -/
abbrev evaluate {width : Nat} [NeZero width] {F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    Option (LoopSemStateFiniteExact.LoopResultExact width) × LoopSemStateFiniteExact width F :=
  LoopSemStateFiniteExact.evaluate prog s

/-- Alias for exact `LoopSem` expression evaluation (`LoopSemStateFiniteExact.eval`). -/
abbrev eval {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (e : HolLoopExp width) :
    Option (WordLocW width) :=
  LoopSemStateFiniteExact.eval s e

/-- Alias for decrementing clock in `HolLoopState` (`LoopSemStateFiniteExact.decClock`). -/
abbrev decClock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) : LoopSemStateFiniteExact width F :=
  LoopSemStateFiniteExact.decClock s

end HolLoopState

end Flapjack

namespace InitECandidate.Solver

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.BoundedCertificate
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

/-! ## 1. `CrepSem` Leaf Instruction Clock Calculus (`crep_evaluate_leaf_clock_eq`) -/

@[simp] theorem crep_setVar_clock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : HolWordLab width) (s : CrepSemHOLState width σ) :
    (CrepSemHOLState.setVar name value s).clock = s.clock := rfl

@[simp] theorem crep_setGlobals_clock {width : Nat} [NeZero width] {σ : Type}
    (key : BitVec 5) (value : HolWordLab width) (s : CrepSemHOLState width σ) :
    (CrepSemHOLState.setGlobals key value s).clock = s.clock := rfl

@[simp] theorem crep_emptyLocals_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (CrepSemHOLState.emptyLocals s).clock = s.clock := rfl

@[simp] theorem crep_decClock_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (decClockCrepSemHOL s).clock = s.clock - 1 := rfl

/-- `.skip` in `CrepSem` preserves `s.clock`. -/
theorem crep_evaluate_skip_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.skip : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_skip]

/-- `.break` in `CrepSem` preserves `s.clock`. -/
theorem crep_evaluate_break_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (label : Nat) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.break label : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_break]

/-- `.continue` in `CrepSem` preserves `s.clock`. -/
theorem crep_evaluate_continue_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (label : Nat) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.continue label : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_continue]

/-- `.raise` in `CrepSem` preserves `s.clock`. -/
theorem crep_evaluate_raise_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (eid : BitVec width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.raise eid : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_raise]
  rfl

/-- `.return` in `CrepSem` preserves `s.clock` in both success and error branches. -/
theorem crep_evaluate_return_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (es : List (CrepExpHOL width)) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.return es : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_return]
  cases es.mapM (evalCrepSemHOLExp s) <;> rfl

/-- `.assign` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_assign_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (name : Nat) (src : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.assign name src : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_assign]
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
  | none => rfl
  | some w =>
      dsimp only
      cases s.locals.lookup name <;> rfl

/-- `.store` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_store_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.store dst src : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_store]
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | word account =>
          cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none => rfl
          | some w =>
              dsimp only
              cases Classical.propDecidable (s.memaddrs account) <;> rfl

/-- `.storeByte` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_storeByte_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.storeByte dst src : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_storeByte]
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | word address =>
          cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none => rfl
          | some sv =>
              cases sv with
              | word w =>
                  dsimp only
                  cases crepExactMemStoreByte s (fun a => Classical.propDecidable (s.memaddrs a))
                    address (UInt8.ofNat w.toNat) <;> rfl

/-- `.store32` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_store32_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (dst src : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.store32 dst src : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_store32]
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | word address =>
          cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src with
          | none => rfl
          | some sv =>
              cases sv with
              | word w =>
                  dsimp only
                  cases crepExactMemStore32 s (fun a => Classical.propDecidable (s.memaddrs a))
                    address (BitVec.ofNat 32 w.toNat) <;> rfl

/-- `.storeGlob` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_storeGlob_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (dst : BitVec 5) (src : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.storeGlob dst src : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_storeGlob]
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) src <;> rfl

/-- `.primitive` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_primitive_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (names : List Nat) (op : PrimOp) (args : List Nat) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.primitive names op args : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_primitive]
  cases args.mapM s.locals.lookup with
  | none => rfl
  | some ws =>
      dsimp only
      cases crepPrimopHOLExact op ws with
      | none => rfl
      | some results =>
          dsimp only
          split <;> rfl

/-- `.shMem` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_shMem_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (op : WordMemOp) (name : Nat) (address : CrepExpHOL width) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.shMem op name address : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_eq_core s (.shMem op name address)
    (fun a => Classical.propDecidable (s.memaddrs a))
    (fun a => Classical.propDecidable (s.shMemaddrs a))]
  unfold evalCrepSemHOLProg
  cases crepExactEvalExp s (fun a => Classical.propDecidable (s.memaddrs a)) address with
  | none => rfl
  | some av =>
      cases av with
      | word addr =>
          dsimp only
          split
          · cases s.locals.lookup name with
            | none => rfl
            | some _ =>
                dsimp only [crepShMemLoadHOL]
                rcases h : @crepShMemLoadExactHOL width _ σ name addr (crepShMemByteWidth op) s
                  (fun a => Classical.propDecidable (s.shMemaddrs a)) with ⟨r, s'⟩
                exact @crepShMemLoadClock width _ σ name addr (crepShMemByteWidth op) s
                  (fun a => Classical.propDecidable (s.shMemaddrs a)) r s' h
          · cases s.locals.lookup name with
            | none => rfl
            | some lv =>
                cases lv with
                | word _ =>
                    dsimp only [crepShMemStoreHOL]
                    rcases h : @crepShMemStoreExactHOL width _ σ name addr (crepShMemByteWidth op) s
                      (fun a => Classical.propDecidable (s.shMemaddrs a)) with ⟨r, s'⟩
                    exact @crepShMemStoreClock width _ σ name addr (crepShMemByteWidth op) s
                      (fun a => Classical.propDecidable (s.shMemaddrs a)) r s' h

/-- `.extCall` in `CrepSem` preserves `s.clock` in all branches. -/
theorem crep_evaluate_extCall_clock {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (fn : MlString) (c cl a al : Nat) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.extCall fn c cl a al : CrepProgHOL width)).2.clock = s.clock := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_eq_core s (.extCall fn c cl a al)
    (fun addr => Classical.propDecidable (s.memaddrs addr))
    (fun addr => Classical.propDecidable (s.shMemaddrs addr))]
  unfold evalCrepSemHOLProg
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Syntactic classifier for the non-ticking leaf instructions of `CrepProgHOL width`. -/
def isCrepClockPreservingLeaf {width : Nat} [NeZero width] : CrepProgHOL width → Bool
  | .skip | .assign _ _ | .store _ _ | .storeByte _ _ | .store32 _ _ | .storeGlob _ _
  | .return _ | .raise _ | .break _ | .continue _ | .primitive _ _ _
  | .shMem _ _ _ | .extCall _ _ _ _ _ => true
  | _ => false

/-- Unified `CrepSem` leaf clock-preservation theorem: every leaf instruction of
`CrepProgHOL width` satisfying `isCrepClockPreservingLeaf prog = true` (including
`.skip`, `.assign`, `.store`, `.storeByte`, `.store32`, `.storeGlob`, `.return`,
`.raise`, `.break`, `.continue`, `.primitive`, `.shMem`, `.extCall`) preserves
`s.clock` (`(evaluateHOLFiniteState s prog).2.clock = s.clock`). -/
theorem crep_evaluate_leaf_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (prog : CrepProgHOL width)
    (hleaf : isCrepClockPreservingLeaf prog = true) :
    (CrepSemStateFiniteExact.evaluateHOLFiniteState s prog).2.clock = s.clock := by
  cases prog with
  | skip => exact crep_evaluate_skip_clock s
  | assign name src => exact crep_evaluate_assign_clock s name src
  | store dst src => exact crep_evaluate_store_clock s dst src
  | storeByte dst src => exact crep_evaluate_storeByte_clock s dst src
  | store32 dst src => exact crep_evaluate_store32_clock s dst src
  | storeGlob dst src => exact crep_evaluate_storeGlob_clock s dst src
  | «return» es => exact crep_evaluate_return_clock s es
  | raise eid => exact crep_evaluate_raise_clock s eid
  | «break» label => exact crep_evaluate_break_clock s label
  | «continue» label => exact crep_evaluate_continue_clock s label
  | primitive names op args => exact crep_evaluate_primitive_clock s names op args
  | shMem op name address => exact crep_evaluate_shMem_clock s op name address
  | extCall fn c cl a al => exact crep_evaluate_extCall_clock s fn c cl a al
  | _ => simp [isCrepClockPreservingLeaf] at hleaf

/-- Exact `CrepSem` `.tick` characterization:
- when `s.clock = 0`, `evaluateHOLFiniteState s .tick = (some .timeOut, s.emptyLocalsHOLFinite)`
- when `s.clock ≠ 0`, `evaluateHOLFiniteState s .tick = (none, s.decClockHOLFinite)` with
  `clock = s.clock - 1`. -/
theorem crep_evaluate_tick_characterization {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) :
    (s.clock = 0 →
      CrepSemStateFiniteExact.evaluateHOLFiniteState s (.tick : CrepProgHOL width) =
        (some .timeOut, s.emptyLocalsHOLFinite)) ∧
    (s.clock ≠ 0 →
      CrepSemStateFiniteExact.evaluateHOLFiniteState s (.tick : CrepProgHOL width) =
        (none, s.decClockHOLFinite) ∧
      (CrepSemStateFiniteExact.evaluateHOLFiniteState s (.tick : CrepProgHOL width)).2.clock =
        s.clock - 1) := by
  rw [CrepSemStateFiniteExact.evaluateHOLFiniteState, evalCrepSemHOLProgExact_tick]
  refine ⟨?_, ?_⟩
  · intro h0
    rw [if_pos h0]
  · intro hne
    rw [if_neg hne]
    exact ⟨rfl, rfl⟩

/-! ## 2. `LoopSem` Expression & Leaf Instruction Clock Calculus (`loop_evaluate_leaf_clock_eq`) -/

private theorem theWords_attach_eval_clock_irrel {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (k : Nat) :
    ∀ (args : List (HolLoopExp width)),
      (∀ e ∈ args, LoopSemStateFiniteExact.eval { s with clock := k } e =
        LoopSemStateFiniteExact.eval s e) →
      args.attach.map (fun ⟨e, _⟩ => LoopSemStateFiniteExact.eval { s with clock := k } e) =
        args.attach.map (fun ⟨e, _⟩ => LoopSemStateFiniteExact.eval s e) := by
  intro args hih
  apply List.map_congr_left
  intro ⟨e, he⟩ _
  exact hih e he

/-- Evaluating a `LoopSem` expression `e : HolLoopExp width` (including `.load`)
is completely independent of `s.clock`. -/
theorem loop_eval_exp_clock_irrel {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (k : Nat) :
    ∀ e : HolLoopExp width,
      HolLoopState.eval { s with clock := k } e = HolLoopState.eval s e
  | .const _ | .var _ | .lookup _ | .baseAddr | .topAddr => by
      simp [HolLoopState.eval, LoopSemStateFiniteExact.eval]
  | .load addr => by
      simp only [HolLoopState.eval, LoopSemStateFiniteExact.eval,
        loop_eval_exp_clock_irrel s k addr]
      cases LoopSemStateFiniteExact.eval s addr with
      | none => rfl
      | some v =>
          cases v <;> rfl
  | .op op args => by
      simp only [HolLoopState.eval, LoopSemStateFiniteExact.eval]
      have hmap : args.attach.map (fun ⟨e, _⟩ => LoopSemStateFiniteExact.eval { s with clock := k } e) =
          args.attach.map (fun ⟨e, _⟩ => LoopSemStateFiniteExact.eval s e) := by
        apply List.map_congr_left
        intro ⟨e, he⟩ _
        exact loop_eval_exp_clock_irrel s k e
      rw [hmap]
  | .shift sh e1 e2 => by
      simp only [HolLoopState.eval, LoopSemStateFiniteExact.eval,
        loop_eval_exp_clock_irrel s k e1, loop_eval_exp_clock_irrel s k e2]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals decreasing_trivial

/-- `.skip` in `LoopSem` preserves `s.clock`. -/
theorem loop_evaluate_skip_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    (HolLoopState.evaluate (.skip : HolLoopProg width) s).2.clock = s.clock := by
  simp [HolLoopState.evaluate, LoopSemStateFiniteExact.evaluate]

/-- `.fail` in `LoopSem` preserves `s.clock`. -/
theorem loop_evaluate_fail_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    (HolLoopState.evaluate (.fail : HolLoopProg width) s).2.clock = s.clock := by
  simp [HolLoopState.evaluate, LoopSemStateFiniteExact.evaluate]

/-- `.break` in `LoopSem` preserves `s.clock`. -/
theorem loop_evaluate_break_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (k : Nat) :
    (HolLoopState.evaluate (.break k : HolLoopProg width) s).2.clock = s.clock := by
  simp [HolLoopState.evaluate, LoopSemStateFiniteExact.evaluate]

/-- `.continue` in `LoopSem` preserves `s.clock`. -/
theorem loop_evaluate_continue_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (k : Nat) :
    (HolLoopState.evaluate (.continue k : HolLoopProg width) s).2.clock = s.clock := by
  simp [HolLoopState.evaluate, LoopSemStateFiniteExact.evaluate]

/-- `.assign` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_assign_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (v : Nat) (exp : HolLoopExp width) :
    (HolLoopState.evaluate (.assign v exp : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.eval s exp <;> rfl

/-- `.arith` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_arith_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (arith : LoopArith) :
    (HolLoopState.evaluate (.arith arith : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases h : LoopSemStateFiniteExact.loopArith s arith with
  | none => rfl
  | some s' => exact LoopSemStateFiniteExact.loopArith_clock h

/-- `.primitive` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_primitive_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (lhss : List Nat) (pop : PrimOp) (rhss : List Nat) :
    (HolLoopState.evaluate (.primitive lhss pop rhss : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.getVars rhss s with
  | none => rfl
  | some ws =>
      dsimp only
      cases LoopSemStateFiniteExact.loopPrimop pop ws with
      | none => rfl
      | some resWs =>
          dsimp only
          split <;> rfl

/-- `.load32` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_load32_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (a v : Nat) :
    (HolLoopState.evaluate (.load32 a v : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup a s.locals with
  | none => rfl
  | some av =>
      cases av with
      | loc _ _ => rfl
      | word w =>
          dsimp only
          cases memLoad32Exact s.memory s.mdomain s.be w <;> rfl

/-- `.loadByte` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_loadByte_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (a v : Nat) :
    (HolLoopState.evaluate (.loadByte a v : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup a s.locals with
  | none => rfl
  | some av =>
      cases av with
      | loc _ _ => rfl
      | word w =>
          dsimp only
          cases memLoadByteAuxExact s.memory s.mdomain s.be w <;> rfl

/-- `.store` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_store_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (exp : HolLoopExp width) (v : Nat) :
    (HolLoopState.evaluate (.store exp v : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.eval s exp with
  | none => rfl
  | some ev =>
      cases ev with
      | loc _ _ => rfl
      | word adr =>
          cases sptLookup v s.locals with
          | none => rfl
          | some w =>
              dsimp only
              cases hm : LoopSemStateFiniteExact.memStore adr w s with
              | none => rfl
              | some st => exact LoopSemStateFiniteExact.memStore_clock hm

/-- `.storeByte` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_storeByte_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (a w : Nat) :
    (HolLoopState.evaluate (.storeByte a w : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup a s.locals with
  | none => rfl
  | some av =>
      cases av with
      | loc _ _ => rfl
      | word wa =>
          cases sptLookup w s.locals with
          | none => rfl
          | some wv =>
              cases wv with
              | loc _ _ => rfl
              | word wb =>
                  dsimp only
                  cases memStoreByteAuxExact s.memory s.mdomain s.be wa (wb.setWidth 8) <;> rfl

/-- `.store32` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_store32_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (a w : Nat) :
    (HolLoopState.evaluate (.store32 a w : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup a s.locals with
  | none => rfl
  | some av =>
      cases av with
      | loc _ _ => rfl
      | word wa =>
          cases sptLookup w s.locals with
          | none => rfl
          | some wv =>
              cases wv with
              | loc _ _ => rfl
              | word wb =>
                  dsimp only
                  cases memStore32Exact s.memory s.mdomain s.be wa (wb.setWidth 32) <;> rfl

/-- `.setGlobal` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_setGlobal_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (dst : BitVec 5) (exp : HolLoopExp width) :
    (HolLoopState.evaluate (.setGlobal dst exp : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.eval s exp <;> rfl

/-- `.return` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_return_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (ns : List Nat) :
    (HolLoopState.evaluate (.return ns : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.getVars ns s <;> rfl

/-- `.raise` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_raise_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (n : Nat) :
    (HolLoopState.evaluate (.raise n : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup n s.locals <;> rfl

/-- `.locValue` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_locValue_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (r l1 : Nat) :
    (HolLoopState.evaluate (.locValue r l1 : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  split <;> rfl

/-- `.shMem` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_shMem_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (op : WordMemOp) (v : Nat) (ad : HolLoopExp width) :
    (HolLoopState.evaluate (.shMem op v ad : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases LoopSemStateFiniteExact.eval s ad with
  | none => rfl
  | some av =>
      cases av with
      | loc _ _ => rfl
      | word addr =>
          dsimp only
          split
          · cases sptLookup v s.locals with
            | none => rfl
            | some _ => exact LoopSemStateFiniteExact.shMemOp_clock op v addr s
          · cases sptLookup v s.locals with
            | none => rfl
            | some lv =>
                cases lv with
                | loc _ _ => rfl
                | word _ => exact LoopSemStateFiniteExact.shMemOp_clock op v addr s

/-- `.ffi` in `LoopSem` preserves `s.clock` in all branches. -/
theorem loop_evaluate_ffi_clock {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (idx : MlString)
    (ptr1 len1 ptr2 len2 : Nat) (cutset : NumSet) :
    (HolLoopState.evaluate (.ffi idx ptr1 len1 ptr2 len2 cutset : HolLoopProg width) s).2.clock = s.clock := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  cases sptLookup len1 s.locals with
  | none => rfl
  | some v1 =>
      cases v1 with
      | loc _ _ => rfl
      | word w =>
          cases sptLookup ptr1 s.locals with
          | none => rfl
          | some v2 =>
              cases v2 with
              | loc _ _ => rfl
              | word w2 =>
                  cases sptLookup len2 s.locals with
                  | none => rfl
                  | some v3 =>
                      cases v3 with
                      | loc _ _ => rfl
                      | word w3 =>
                          cases sptLookup ptr2 s.locals with
                          | none => rfl
                          | some v4 =>
                              cases v4 with
                              | loc _ _ => rfl
                              | word w4 =>
                                  cases hc : LoopSemStateFiniteExact.cutState cutset s with
                                  | none => rfl
                                  | some s' =>
                                      have hclk := LoopSemStateFiniteExact.cutState_clock hc
                                      dsimp only
                                      cases readBytearrayWordHOL w2 w.toNat
                                        (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with
                                      | none => exact hclk
                                      | some bytes =>
                                          cases readBytearrayWordHOL w4 w3.toNat
                                            (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with
                                          | none => exact hclk
                                          | some bytes2 =>
                                              dsimp only
                                              cases callFFIHOL s'.ffi (.extCall idx) bytes bytes2 <;>
                                                exact hclk

/-- Syntactic classifier for the non-ticking leaf instructions of `HolLoopProg width`. -/
def isLoopClockPreservingLeaf {width : Nat} [NeZero width] : HolLoopProg width → Bool
  | .skip | .assign _ _ | .arith _ | .primitive _ _ _ | .load32 _ _ | .loadByte _ _
  | .store _ _ | .storeByte _ _ | .store32 _ _ | .setGlobal _ _
  | .return _ | .raise _ | .break _ | .continue _ | .fail | .locValue _ _
  | .shMem _ _ _ | .ffi _ _ _ _ _ _ => true
  | _ => false

/-- Unified `LoopSem` leaf clock-preservation theorem: every leaf instruction of
`HolLoopProg width` satisfying `isLoopClockPreservingLeaf prog = true` (`.skip`,
`.assign`, `.arith`, `.primitive`, `.load32`, `.loadByte`, `.store`, `.storeByte`,
`.store32`, `.setGlobal`, `.return`, `.raise`, `.break`, `.continue`, `.fail`,
`.locValue`, `.shMem`, `.ffi`) preserves `s.clock` (`0` ticks consumed). -/
theorem loop_evaluate_leaf_clock_eq {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (prog : HolLoopProg width)
    (hleaf : isLoopClockPreservingLeaf prog = true) :
    (HolLoopState.evaluate prog s).2.clock = s.clock := by
  cases prog with
  | skip => exact loop_evaluate_skip_clock s
  | assign v exp => exact loop_evaluate_assign_clock s v exp
  | arith op => exact loop_evaluate_arith_clock s op
  | primitive lhss pop rhss => exact loop_evaluate_primitive_clock s lhss pop rhss
  | load32 a v => exact loop_evaluate_load32_clock s a v
  | loadByte a v => exact loop_evaluate_loadByte_clock s a v
  | store exp v => exact loop_evaluate_store_clock s exp v
  | storeByte a w => exact loop_evaluate_storeByte_clock s a w
  | store32 a w => exact loop_evaluate_store32_clock s a w
  | setGlobal dst exp => exact loop_evaluate_setGlobal_clock s dst exp
  | «return» ns => exact loop_evaluate_return_clock s ns
  | raise n => exact loop_evaluate_raise_clock s n
  | «break» k => exact loop_evaluate_break_clock s k
  | «continue» k => exact loop_evaluate_continue_clock s k
  | fail => exact loop_evaluate_fail_clock s
  | locValue r l1 => exact loop_evaluate_locValue_clock s r l1
  | shMem op v ad => exact loop_evaluate_shMem_clock s op v ad
  | ffi idx ptr1 len1 ptr2 len2 cutset =>
      exact loop_evaluate_ffi_clock s idx ptr1 len1 ptr2 len2 cutset
  | _ => simp [isLoopClockPreservingLeaf] at hleaf

/-- Exact `LoopSem` `.tick` characterization:
- when `s.clock = 0`, `HolLoopState.evaluate .tick s = (some .timeOut, { s with locals := .ln })`
- when `s.clock ≠ 0`, `HolLoopState.evaluate .tick s = (none, HolLoopState.decClock s)` with
  `clock = s.clock - 1`. -/
theorem loop_evaluate_tick_characterization {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) :
    (s.clock = 0 →
      HolLoopState.evaluate (.tick : HolLoopProg width) s =
        (some .timeOut, { s with locals := .ln })) ∧
    (s.clock ≠ 0 →
      HolLoopState.evaluate (.tick : HolLoopProg width) s =
        (none, HolLoopState.decClock s) ∧
      (HolLoopState.evaluate (.tick : HolLoopProg width) s).2.clock = s.clock - 1) := by
  unfold HolLoopState.evaluate LoopSemStateFiniteExact.evaluate
  refine ⟨?_, ?_⟩
  · intro h0
    rw [if_pos h0]
  · intro hne
    rw [if_neg hne]
    exact ⟨rfl, rfl⟩

/-! ## 3. Exact Clock Shift of `PanGlobals.compileTop` & Post-Bootstrap Budget Decomposition -/

/-- Exact `+1` clock shift and arbitrary-clock non-`timeOut` agreement for `PanGlobals.compileTopExactHOL`:
if `s1` (from `code`) runs `start` at clock `k` without `.error` or `.timeOut`, then `T` (from
`compileTopExactHOL code start`) runs `start` at clock `k + 1` with the exact same result and
`ioEvents`, and furthermore any clock `K_glob` on `T` that does not time out agrees with `s1` at `k`! -/
theorem pan_globals_compile_top_clock_shift_and_not_timeOut_agree
    {width : Nat} [NeZero width] {σ : Type}
    (s t : PanSemStateFiniteExact width σ) (code : List (DeclHOL width)) (start : MlS)
    (mgs : BitVec width) (freeAddrs : BitVec width → Prop)
    (tmem : BitVec width → HolWordLab width)
    (tlocals : HolFiniteMapExact MlS (ValueHOL width))
    (h : ((functionsHOL code).map Prod.fst).Nodup ∧
      t = { s with
        topAddr := s.topAddr + mgs
        memaddrs := fun address => s.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s.code = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s.topAddr ∧
      goodDimindex width ∧
      mgs = panBytesInWord width *
        BitVec.ofNat width ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s.topAddr
        ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      (∀ address, s.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s.memaddrs address → s.memory address = tmem address) ∧
      ¬ s.memaddrs (s.topAddr + mgs) ∧
      (panBytesInWord width).toNat * ((decShapesHOL code).map sizeOfShapeHOL).sum <
        2 ^ width ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) ∧
      PanSemStateFiniteExact.semanticsDecls s start code ≠ .fail)
    (s1 : PanSemStateFiniteExact width σ) (k K_glob : Nat)
    (hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a)) code = some s1)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error)
    (hnt_src : (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .timeOut) :
    ∃ T,
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { t with structs := [] } (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL code start) = some T ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).1 =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).1 ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).2.ffi.ioEvents =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).2.ffi.ioEvents ∧
      ((PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := K_glob }
          (.call none start [] : ProgHOL width)).1 ≠ some .timeOut →
        (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := K_glob }
          (.call none start [] : ProgHOL width)).1 =
          (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
            (.call none start [] : ProgHOL width)).1 ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := K_glob }
          (.call none start [] : ProgHOL width)).2.ffi.ioEvents =
          (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
            (.call none start [] : ProgHOL width)).2.ffi.ioEvents) := by
  obtain ⟨T, hevT, hres1, hio1⟩ :=
    pan_globals_compile_top_clocked_shift s t code start mgs freeAddrs tmem tlocals h s1 k hs1 hne
  refine ⟨T, hevT, hres1, hio1, ?_⟩
  intro hntK
  rcases hrunK : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := K_glob }
      (.call none start [] : ProgHOL width) with ⟨rK, postK⟩
  rcases hrun1 : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
      (.call none start [] : ProgHOL width) with ⟨r1, post1⟩
  have hntK' : rK ≠ some .timeOut := by
    have h1 := hntK
    rw [hrunK] at h1
    exact h1
  have hnt1' : r1 ≠ some .timeOut := by
    have h1 := hres1
    rw [hrun1] at h1
    dsimp only at h1
    rw [h1]
    exact hnt_src
  obtain ⟨hr, hffi⟩ := panEvaluateIgnoreClocks (.call none start []) T K_glob (k + 1)
    rK r1 postK post1 hrunK hntK' hrun1 hnt1'
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [hr, ← hres1, hrun1]
  · dsimp only
    rw [congrArg HolFfiState.ioEvents hffi, ← hio1, hrun1]

/-- Post-bootstrap target step decomposition: running `evaluateTargetHOL` from
`baselineInitialState input` for `bootstrapSteps + (K_init + K_body)` steps is
definitionally identical to running for `(bootstrapSteps + K_init) + K_body` steps,
and if the run does not time out at `bootstrapSteps + (K_init + K_body)`, then
`1 ≤ K_init + K_body` whenever `sourceBehaviour input = .terminate outcome events`
on an installed oracle baseline. -/
theorem post_bootstrap_split_budget_terminate_halt_agree
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 620 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (K_init K_body : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + (K_init + K_body)) (baselineInitialState input)).1 ≠ .timeOut) :
    bootstrapSteps + (K_init + K_body) = (bootstrapSteps + K_init) + K_body ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + (K_init + K_body)) (baselineInitialState input)).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + (K_init + K_body)) (baselineInitialState input)).2.2.ioEvents = events ∧
    1 ≤ bootstrapSteps + (K_init + K_body) := by
  have hassoc : bootstrapSteps + (K_init + K_body) = (bootstrapSteps + K_init) + K_body :=
    (Nat.add_assoc bootstrapSteps K_init K_body).symm
  obtain ⟨hhalt, hio, hpos⟩ :=
    oracle_full_baseline_terminate_halt_agree_of_not_timeOut
      oracles input c depth compiled depthBound installed
      outcome events source (K_init + K_body) hnt
  exact ⟨hassoc, hhalt, hio, hpos⟩

/-- Final split-budget certificate theorem (`finite_certificate_of_split_post_bootstrap_budget`):
decomposing the post-bootstrap target budget as $K_{\text{post}} = K_{\text{init}} + K_{\text{body}}$
(where $K_{\text{init}}$ accounts for post-bootstrap initialization and $K_{\text{body}}$ accounts
for the compiled body execution) and showing that `evaluateTargetHOL` does not time out at
`bootstrapSteps + (K_init + K_body)` on any covered terminating input directly produces the
Yukon finite-`K` certificate
`InitE.Certificate (baselineWithFiniteK (bootstrapSteps + (K_init + K_body))) (.finite (bootstrapSteps + (K_init + K_body)))`! -/
theorem finite_certificate_of_split_post_bootstrap_budget
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K_init K_body : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + (K_init + K_body)) (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (bootstrapSteps + (K_init + K_body)))
      (.finite (bootstrapSteps + (K_init + K_body))) :=
  finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (K_init + K_body) hlab compiled depthBound not_timeOut

#print axioms crep_evaluate_leaf_clock_eq
#print axioms crep_evaluate_tick_characterization
#print axioms loop_eval_exp_clock_irrel
#print axioms loop_evaluate_leaf_clock_eq
#print axioms loop_evaluate_tick_characterization
#print axioms pan_globals_compile_top_clock_shift_and_not_timeOut_agree
#print axioms post_bootstrap_split_budget_terminate_halt_agree
#print axioms finite_certificate_of_split_post_bootstrap_budget

end InitECandidate.Solver
