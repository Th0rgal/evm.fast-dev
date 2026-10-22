import InitECandidate.Solver.GuestStepBound
import InitECandidate.Solver.SourceTerminationBound
import InitECandidate.Solver.FastBoundedPanToWord

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SourceCallGraphBound` — Verrou B: Source `PanSem` Call-Graph & Loop Clock-Budget Calculus

This module establishes the source-level (`PanSem`) clock decrement laws for
function calls (`.call` and `.decCall`), the compositional clock-budget algebra
for bounded `while` loops (`loopClockBudget iterBound bodyBudget := iterBound * (bodyBudget + 1)`)
and the acyclic `Guest.guestAst` call graph (depth `≤ 18`, `825` functions,
`guestMaxFrameBound = 348`), and the constructive bridge with
`semanticsDecls_terminate_extract` and `semanticsDecls_terminate_at_clock`
from `InitECandidate.Proofs.BoundedPanToWord` showing that every terminating
source execution `sourceBehaviour input = .terminate outcome events` admits a
finite non-`.timeOut` source clock `k_pan` and stabilizes at every clock `K_pan ≥ k_pan`.
-/

namespace InitECandidate.Solver

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.GuestStepBound
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)

/-! ## 1. `PanSem` Clock Decrement Laws for `.decCall` and `.call` -/

/-- Any non-`.timeOut` evaluation of `.decCall rt sh fname args cont` when argument
evaluation and code lookup succeed requires `1 ≤ s.clock` and decreases the clock
by at least `1` (`post.clock ≤ s.clock - 1`). -/
theorem panSem_evaluate_decCall_not_timeOut_clock_dec {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ)
    (rt : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL width)) (cont : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (retShape : ShapeHOL)
    (hargs : @PanSemStateFiniteExact.evalListHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values =
      some (body, callee, retShape))
    (hnt : (PanSemStateFiniteExact.evaluateHOLFiniteState s
      (.decCall rt sh fname args cont : ProgHOL width)).1 ≠ some .timeOut) :
    1 ≤ s.clock ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState s
        (.decCall rt sh fname args cont : ProgHOL width)).2.clock ≤ s.clock - 1 := by
  by_cases h0 : s.clock = 0
  · rw [panSem_evaluate_decCall_clock_zero s rt sh fname args cont values body callee retShape
      hargs hlookup h0] at hnt
    exact absurd rfl hnt
  · refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite, hargs]
    dsimp only
    rw [hlookup]
    dsimp only
    rw [if_neg h0]
    let entry := PanSemStateFiniteExact.callEntryStateHOLFinite s callee
    let bodyOutput := PanSemStateFiniteExact.evaluateHOLFiniteState entry body
    have hentry_clk : entry.clock = s.clock - 1 := rfl
    have hbody_le : bodyOutput.2.clock ≤ s.clock - 1 := by
      have h := evaluateHOLFiniteState_clock_le entry body
      rw [hentry_clk] at h
      exact h
    cases hbo : bodyOutput.1 with
    | none => exact hbody_le
    | some r =>
        cases r with
        | «break» => exact hbody_le
        | «continue» => exact hbody_le
        | error => exact hbody_le
        | timeOut => exact hbody_le
        | finalFfi _ => exact hbody_le
        | exception _ _ => exact hbody_le
        | returned value =>
            dsimp only
            split
            · let contState :=
                PanSemStateFiniteExact.setVarHOLFinite rt value
                  { bodyOutput.2 with locals := s.locals }
              have hcont_le :
                  (PanSemStateFiniteExact.evaluateHOLFiniteState contState cont).2.clock ≤
                    s.clock - 1 := by
                have hc := evaluateHOLFiniteState_clock_le contState cont
                have hcs : contState.clock = bodyOutput.2.clock := rfl
                rw [hcs] at hc
                exact Nat.le_trans hc hbody_le
              exact hcont_le
            · exact hbody_le

/-- Evaluating `.call info fname args` at `s.clock = 0` when argument evaluation
and code lookup succeed immediately produces `(some .timeOut, emptyLocalsHOLFinite s)`. -/
theorem panSem_evaluate_call_clock_zero {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (args : List (ExpHOL width))
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (retShape : ShapeHOL)
    (hargs : @PanSemStateFiniteExact.evalListHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values =
      some (body, callee, retShape))
    (h0 : s.clock = 0) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s (.call info fname args : ProgHOL width) =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite s) :=
  evaluateHOLFiniteState_call_clock_zero s info fname args values body callee retShape
    hargs hlookup h0

/-- Any non-`.timeOut` evaluation of `.call info fname args` when argument evaluation
and code lookup succeed requires `1 ≤ s.clock` and decreases the clock by at least `1`
(`post.clock ≤ s.clock - 1`). -/
theorem panSem_evaluate_call_not_timeOut_clock_dec {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (args : List (ExpHOL width))
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (retShape : ShapeHOL)
    (hargs : @PanSemStateFiniteExact.evalListHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values =
      some (body, callee, retShape))
    (hnt : (PanSemStateFiniteExact.evaluateHOLFiniteState s
      (.call info fname args : ProgHOL width)).1 ≠ some .timeOut) :
    1 ≤ s.clock ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState s
        (.call info fname args : ProgHOL width)).2.clock ≤ s.clock - 1 := by
  by_cases h0 : s.clock = 0
  · rw [panSem_evaluate_call_clock_zero s info fname args values body callee retShape
      hargs hlookup h0] at hnt
    exact absurd rfl hnt
  · refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
    rw [evaluateHOLFiniteState_call, hargs]
    dsimp only
    rw [hlookup]
    dsimp only
    rw [if_neg h0]
    let entry := PanSemStateFiniteExact.callEntryStateHOLFinite s callee
    have hentry_clk : entry.clock = s.clock - 1 := rfl
    have hbody_le : (PanSemStateFiniteExact.evaluateHOLFiniteState entry body).2.clock ≤
        s.clock - 1 := by
      have h := evaluateHOLFiniteState_clock_le entry body
      rw [hentry_clk] at h
      exact h
    rcases hbo : PanSemStateFiniteExact.evaluateHOLFiniteState entry body with ⟨resBody, st⟩
    rw [hbo] at hbody_le
    dsimp only at hbody_le ⊢
    cases resBody with
    | none => exact hbody_le
    | some r =>
        cases r with
        | «break» => exact hbody_le
        | «continue» => exact hbody_le
        | error => exact hbody_le
        | timeOut => exact hbody_le
        | finalFfi _ => exact hbody_le
        | returned value =>
            dsimp only
            split
            · cases info with
              | none => exact hbody_le
              | some pair =>
                  obtain ⟨retOpt, _⟩ := pair
                  cases retOpt with
                  | none => exact hbody_le
                  | some kv =>
                      obtain ⟨kind, name⟩ := kv
                      dsimp only
                      split
                      · rw [GuestStepBound.setKvarHOLFinite_clock]
                        exact hbody_le
                      · exact hbody_le
            · exact hbody_le
        | exception eid value =>
            dsimp only
            cases info with
            | none => exact hbody_le
            | some pair =>
                obtain ⟨_, hopt⟩ := pair
                cases hopt with
                | none => exact hbody_le
                | some triple =>
                    obtain ⟨handlerId, handlerVar, handlerProg⟩ := triple
                    dsimp only
                    split
                    · cases s.eshapes.lookup eid with
                      | none => exact hbody_le
                      | some shape =>
                          dsimp only
                          split
                          · let hState :=
                              PanSemStateFiniteExact.setVarHOLFinite handlerVar value
                                { st with locals := s.locals }
                            have hh_le :
                                (PanSemStateFiniteExact.evaluateHOLFiniteState hState handlerProg).2.clock ≤
                                  s.clock - 1 := by
                              have hc := evaluateHOLFiniteState_clock_le hState handlerProg
                              have hcs : hState.clock = st.clock := rfl
                              rw [hcs] at hc
                              exact Nat.le_trans hc hbody_le
                            exact hh_le
                          · exact hbody_le
                    · exact hbody_le

/-! ## 2. Acyclic Call-Graph & Bounded-Loop Clock Budget Algebra -/

/-- Clock budget of a bounded `while` loop with at most `iterBound` iterations
where each loop body execution consumes at most `bodyBudget` ticks (plus `1` tick
for the loop header `decClockHOLFinite`). -/
def loopClockBudget (iterBound bodyBudget : Nat) : Nat :=
  iterBound * (bodyBudget + 1)

/-- Clock budget of a function call (`.call` or `.decCall`): `1` tick for call entry
(`callEntryStateHOLFinite`) plus `calleeBudget` for the callee body, plus `contBudget`
for the caller continuation/handler. -/
def callClockBudget (calleeBudget contBudget : Nat) : Nat :=
  1 + calleeBudget + contBudget

/-- Static call-graph depth bound of `Guest.guestAst` (`18` levels). -/
def guestCallGraphMaxDepth : Nat := 18

/-- Static count of function declarations in `Guest.guestAst` (`825` functions). -/
def guestFunctionCount : Nat := 825

/-- One-step induction law for `loopClockBudget`: `0` iterations require `0` ticks,
and `n + 1` iterations decompose as `(bodyBudget + 1) + loopClockBudget n bodyBudget`
with monotonicity in both `iterBound` and `bodyBudget`. -/
theorem loopClockBudget_step_and_mono (n m b1 b2 : Nat)
    (hn : n ≤ m) (hb : b1 ≤ b2) :
    loopClockBudget 0 b1 = 0 ∧
      loopClockBudget (n + 1) b1 = (b1 + 1) + loopClockBudget n b1 ∧
      loopClockBudget n b1 ≤ loopClockBudget m b2 := by
  unfold loopClockBudget
  refine ⟨Nat.zero_mul (b1 + 1), ?_, ?_⟩
  · rw [Nat.succ_mul, Nat.add_comm]
  · exact Nat.mul_le_mul hn (Nat.add_le_add_right hb 1)

/-- Call-graph depth & frame-bound certificate for `Guest.guestAst`:
1. `(frameBounds Guest.guestAst).length = guestFunctionCount = 825`,
2. `guestMaxFrameBound = 348`,
3. Any acyclic call chain of depth `d ≤ guestCallGraphMaxDepth` (`d ≤ 18`) consumes at
   most `d ≤ 18` call-entry ticks and requires at most `d * guestMaxFrameBound ≤ 18 * 348 = 6264`
   words of source stack frames. -/
theorem guestCallGraph_frame_and_tick_bound (d : Nat)
    (hd : d ≤ guestCallGraphMaxDepth) :
    (frameBounds Guest.guestAst).length = guestFunctionCount ∧
      guestMaxFrameBound = 348 ∧
      d * guestMaxFrameBound ≤ 6264 ∧
      ∀ calleeBudget contBudget : Nat,
        1 ≤ callClockBudget calleeBudget contBudget ∧
        callClockBudget calleeBudget contBudget = 1 + calleeBudget + contBudget := by
  have hlen : (frameBounds Guest.guestAst).length = guestFunctionCount :=
    GuestStepBound.guestAst_functions_length_eq
  have hframe : guestMaxFrameBound = 348 :=
    GuestStepBound.guestMaxFrameBound_eq
  have hd18 : guestCallGraphMaxDepth = 18 := rfl
  refine ⟨hlen, hframe, ?_, ?_⟩
  · rw [hframe]
    rw [hd18] at hd
    omega
  · intro calleeBudget contBudget
    unfold callClockBudget
    refine ⟨?_, rfl⟩
    omega

/-! ## 3. Bridge to `semanticsDecls_terminate_at_clock` and Source Clock Stabilization -/

/-- Source termination clock-stabilization bridge: whenever
`sourceBehaviour input = .terminate outcome events`, the declaration evaluation of
`sourceDeclarations` succeeds (`stCtxt`, `s_decls`), there exists a finite source clock
`k_pan` at which `evaluateHOLFiniteState { s_decls with clock := k_pan } (.call none (ofString "main") [])`
completes with `panEntryClass res_src = .CompleteResult outcome` (`res_src ≠ some .timeOut`)
and `s_src_post.ffi.ioEvents = events`, and furthermore **every** clock `K_pan ≥ k_pan`
produces the exact same non-`.timeOut` result `res_src`, post-state FFI `s_src_post.ffi`,
and `.CompleteResult outcome`! -/
theorem sourceBehaviour_terminate_clock_stabilizes
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events) :
    ∃ stCtxt s_decls k_pan res_src s_src_post,
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls ∧
      PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
        (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post) ∧
      res_src ≠ some .timeOut ∧
      panEntryClass res_src = .CompleteResult outcome ∧
      s_src_post.ffi.ioEvents = events ∧
      ∀ K_pan : Nat, k_pan ≤ K_pan →
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
          (.call none (ofString "main") [] : ProgHOL 64)).1 = res_src ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
          (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut ∧
        panEntryClass (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
          (.call none (ofString "main") [] : ProgHOL 64)).1 = .CompleteResult outcome ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
          (.call none (ofString "main") [] : ProgHOL 64)).2.ffi.ioEvents = events := by
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans hsource
  obtain ⟨stCtxt, s_decls, hst, hev_decls, _, k_pan, res_src, s_src_post, hev_call, hclass, hio⟩ :=
    semanticsDecls_terminate_extract (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm
  have hnt : res_src ≠ some .timeOut := by
    intro h
    subst h
    cases hclass
  refine ⟨stCtxt, s_decls, k_pan, res_src, s_src_post, hst, hev_decls, hev_call, hnt, hclass, hio, ?_⟩
  intro K_pan hle
  have hadd := panPropsEvaluateAddClockEq (.call none (ofString "main") [] : ProgHOL 64)
    { s_decls with clock := k_pan } res_src s_src_post (K_pan - k_pan) ⟨hev_call, hnt⟩
  have hclk_eq : k_pan + (K_pan - k_pan) = K_pan := Nat.add_sub_of_le hle
  have hst_eq : ({ { s_decls with clock := k_pan } with clock := k_pan + (K_pan - k_pan) } :
      PanSemStateFiniteExact 64 Guest.HostMemory) = { s_decls with clock := K_pan } := by
    simp only [hclk_eq]
  rw [hst_eq] at hadd
  rw [hadd]
  dsimp only
  exact ⟨rfl, hnt, hclass, hio⟩

/-- Bridge from any upper bound `B_pan` where `evaluateHOLFiniteState { s_decls with clock := B_pan }`
does not time out to `semanticsDecls_terminate_at_clock` and `1 ≤ B_pan`:
under `sourceBehaviour input = .terminate outcome events`, if `s_decls` runs `"main"`
at clock `B_pan` without `.timeOut`, then `1 ≤ B_pan`, its result has
`panEntryClass res_B = .CompleteResult outcome`, and its FFI I/O events equal `events`. -/
theorem sourceBehaviour_not_timeOut_at_budget_complete
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (B_pan : Nat) (res_B : Option (PanSemResultExact 64))
    (s_B_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hev_B : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := B_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_B, s_B_post))
    (hnt_B : res_B ≠ some .timeOut) :
    panEntryClass res_B = .CompleteResult outcome ∧
      s_B_post.ffi.ioEvents = events := by
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans hsource
  exact semanticsDecls_terminate_at_clock (sourceInitialState input) (ofString "main")
    sourceDeclarations outcome events hterm stCtxt s_decls hst hev_decls
    B_pan res_B s_B_post hev_B hnt_B


end InitECandidate.Solver
