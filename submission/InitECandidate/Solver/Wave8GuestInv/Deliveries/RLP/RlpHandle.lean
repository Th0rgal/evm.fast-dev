import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpEnc

/-! RLP family, part 6: guarded call with an exception handler (`rlp_validate_items`). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

/-- Call with a handler, guarded by `GuestInv` (the statement of the spec's proposed
`callHandle_guestInv`, proved here independently). -/
theorem callHandle_guestInv' {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) := by
  obtain ⟨params, fbody, ret, hlook, hbody⟩ := hf
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨_, hrunBound⟩ := callee_body_bound hlook hbody (callEntryOn_guestInv fname arguments)
        state hcode hP values body' callee ret' hargs hl
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body').1
        have hpost := guestInv_evaluate (callEntryStateHOLFinite state callee) body'
          (guestInv_callEntry state callee hP)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta hpost ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | timeOut => simp at hnt
          | returned v =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only
            rcases destination with _ | ⟨kind, name⟩ <;> (repeat' split) <;>
              simp [emptyLocalsHOLFinite, setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite] <;>
              (try split) <;> (try simp) <;> omega
          | exception eid v =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            dsimp only at hnt ⊢
            by_cases heid : eid = exn
            · simp only [heid, ↓reduceIte] at hnt ⊢
              rcases hsh : state.eshapes.lookup exn with _ | shape
              · simp only [hsh]; omega
              · simp only [hsh] at hnt ⊢
                by_cases hc : (shapeEqHOL (shapeOfHOLExact v) shape &&
                    isValidValueHOLExact state.toExact VarKind.local var v) = true
                · simp only [hc, ↓reduceIte] at hnt ⊢
                  set resumed := setVarHOLFinite var v { post with locals := state.locals } with hres
                  have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
                  have hresInv : GuestInv resumed :=
                    guestInv_setVar var v _ (guestInv_with_locals_clock post state.locals post.clock hpost)
                  obtain ⟨hsc, hkc⟩ := hh resumed hresCode hresInv hnt
                  have hrc : resumed.clock = post.clock := by simp [hres, setVarHOLFinite]
                  exact ⟨by omega, by omega⟩
                · simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega
            · simp only [heid, ↓reduceIte]
              simp [emptyLocalsHOLFinite]; omega
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

macro_rules
  | `(tactic| loop_auto) => `(tactic|
      (apply callHandle_guestInv'
       · known_fb
       · fb_auto))

end InitECandidate.Solver.Wave8Leaves.Rlp
