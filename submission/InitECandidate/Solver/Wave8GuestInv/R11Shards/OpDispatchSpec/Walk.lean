import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Base

/-! # `DispatchSpecWalk` combinators and `op_dispatch` AST group slices (R11) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. `DispatchSpecWalk`: structural walker over `op_dispatch` branches -/

theorem return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem seq_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  cases r with
  | none => exact return_ne_none t e
  | some _ => simp

theorem raise_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_raise]
  split <;> dsimp only
  · split <;> simp
  · simp

theorem evmRun_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (h : EvmRun s) :
    EvmRun (callEntryStateHOLFinite s callee) :=
  ⟨localsFree_evmInv s callee (s.clock - 1) h.1,
   fun hd => h.2 ((evmDone_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).1 hd)⟩

structure DispatchSpecWalk (p : ProgHOL 64) : Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → EvmRun s →
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none →
      (evaluateHOLFiniteState s p).2 = s) ∧
    ((evaluateHOLFiniteState s p).1 ≠ none →
      OpDispatchPost s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2)

theorem DispatchSpecWalk.skip : DispatchSpecWalk .skip := by
  refine ⟨fun s _ _ _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

theorem DispatchSpecWalk.raise (e : ExpHOL 64) :
    DispatchSpecWalk (.raise (ofString "EvmErr") e) := by
  refine ⟨fun {F} s _ hRun _ => ⟨fun hn => (raise_ne_none s _ e hn).elim, fun _ => ?_⟩⟩
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine ⟨?_, fun _ => ?_⟩
      · rintro ⟨_, h⟩
        cases h
      · have hInv' : EvmInv (emptyLocalsHOLFinite s) :=
          localsFree_evmInv s (emptyLocalsHOLFinite s).locals s.clock hRun.1
        have hcongr := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
        exact ⟨hInv', hcongr.2.2.1, le_of_eq hcongr.2.1⟩
    · exact opDispatchPost_error s s
  · exact opDispatchPost_error s s

theorem DispatchSpecWalk.seqRaiseReturn (e1 e2 : ExpHOL 64) :
    DispatchSpecWalk (.seq (.raise (ofString "EvmErr") e1) (.return e2)) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "EvmErr") e1) with ⟨r, mid⟩
  simp only [hr] at hnt ⊢
  cases r with
  | none =>
    have hnn := raise_ne_none s (ofString "EvmErr") e1
    rw [hr] at hnn
    exact (hnn rfl).elim
  | some _ =>
    have h1 := (DispatchSpecWalk.raise e1).run s hcode hRun (by rw [hr]; exact hnt)
    rw [hr] at h1
    refine ⟨?_, fun _ => h1.2 (by simp)⟩
    intro h
    cases h

theorem return_const0_post {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {v : ValueHOL 64}
    (hpost : OpDispatchPost (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    OpDispatchPost s
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).1
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).2 := by
  rw [evaluateHOLFiniteState_return]
  have hc0 : @evalHOLExact 64 F _ ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (cpost.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  rw [hc0]; dsimp only
  have hsz : sizeOfShapeWithContextHOL cpost.structs
      (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]; dsimp only
  obtain ⟨hInv_cp, hPot_cp⟩ := hpost.1 ⟨v, rfl⟩
  have hcongr_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
  have hcongr_ret := evm_congr (s := cpost)
    (t := emptyLocalsHOLFinite { cpost with locals := s.locals }) rfl rfl
  have hInv_ret : EvmInv (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    localsFree_evmInv cpost _ cpost.clock hInv_cp
  refine ⟨fun _ => ⟨hInv_ret, by rw [hcongr_ret.1, ← hcongr_ce.1]; exact hPot_cp⟩, ?_⟩
  rintro ⟨_, h⟩
  cases h

theorem call_exception_post {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {eid : MlS} {ev : ValueHOL 64}
    (hQ : OpDispatchPost (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    OpDispatchPost s (some (.exception eid ev)) cpost.emptyLocalsHOLFinite := by
  by_cases heid : eid = ofString "EvmErr"
  · subst heid
    exact opDispatchPost_congr_lc (s := s) (s' := callEntryStateHOLFinite s callee)
      (post := cpost) (post' := cpost.emptyLocalsHOLFinite) rfl rfl rfl hQ
  · refine opDispatchPost_other (by intro _ h; cases h) ?_
    rintro ⟨_, h⟩
    injection h with h'; injection h' with h1 _; exact heid h1

theorem DispatchSpecWalk.callReturn {fname : MlS}
    (hf : OpHandlerSpec fname) (args : List (ExpHOL 64)) :
    DispatchSpecWalk (.seq (.call (some (none, none)) fname args) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s s
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s s
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
        have hce_run : EvmRun (callEntryStateHOLFinite s callee) := evmRun_callEntry s callee hRun
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        have hQ (hsafe : res ≠ some .timeOut) :
            OpDispatchPost (callEntryStateHOLFinite s callee) res cpost := by
          have hbody : body' = body :=
            lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
              retShape ret' values callee (by rw [hcode]; exact hlook) hl
          subst body'
          have hce_ex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
              some (body, (callEntryStateHOLFinite s callee).locals, retShape) := by
            refine ⟨values, ?_⟩
            rw [← hcode] at hlook ⊢
            have hret : ret' = retShape := by
              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                s.code.lookup fname values body callee ret' hl
              simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
              split at hx
              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              · cases hx
            subst hret; exact hl
          have := hspec (callEntryStateHOLFinite s callee) hce_code hce_run hce_ex (by rw [hrun]; exact hsafe)
          rw [hrun] at this; exact this
        cases res with
        | none => exact opDispatchPost_error s cpost
        | some r0 =>
          cases r0 with
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte]
              exact return_const0_post (hQ (by simp))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s cpost
          | timeOut => simp at hnt
          | exception eid ev =>
            exact call_exception_post (hQ (by simp))
          | «break» =>
            exact opDispatchPost_error s cpost
          | «continue» =>
            exact opDispatchPost_error s cpost
          | finalFfi f =>
            refine opDispatchPost_other (s := s) (t := cpost.emptyLocalsHOLFinite)
              (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error =>
            exact opDispatchPost_error s cpost.emptyLocalsHOLFinite

theorem DispatchSpecWalk.seq {p q : ProgHOL 64}
    (h1 : DispatchSpecWalk p) (h2 : DispatchSpecWalk q) :
    DispatchSpecWalk (.seq p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState s p with ⟨r1, mid⟩
  simp only [hr1] at hnt ⊢
  cases r1 with
  | none =>
    have hp := h1.run s hcode hRun (by rw [hr1]; simp)
    rw [hr1] at hp
    have hmid : mid = s := hp.1 rfl
    subst mid
    exact h2.run s hcode hRun hnt
  | some _ =>
    have hp := h1.run s hcode hRun (by rw [hr1]; exact hnt)
    rw [hr1] at hp
    refine ⟨?_, fun _ => hp.2 (by simp)⟩
    intro h
    cases h

theorem DispatchSpecWalk.ite (c : ExpHOL 64) {p q : ProgHOL 64}
    (h1 : DispatchSpecWalk p) (h2 : DispatchSpecWalk q) :
    DispatchSpecWalk (.ite c p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w _
    by_cases hw : w = 0
    · simp only [hw, ↓reduceIte]
      intro hnt
      exact h2.run s hcode hRun hnt
    · simp only [hw, ↓reduceIte]
      intro hnt
      exact h1.run s hcode hRun hnt
  · intro _
    refine ⟨?_, fun _ => opDispatchPost_error s s⟩
    intro h
    cases h

/-! ## 2. AST group slices of `guestFn_op_dispatch` -/

def binaryAt : List Nat → ProgHOL 64 → ProgHOL 64
  | [], p => p
  | i :: rest, .seq a b => binaryAt rest (if i = 0 then a else b)
  | i :: rest, .ite _ a b => binaryAt rest (if i = 0 then a else b)
  | _, _ => .skip

def seqCut : Nat → ProgHOL 64 → ProgHOL 64 → ProgHOL 64
  | 0, _, tail => tail
  | n + 1, .seq a b, tail => .seq a (seqCut n b tail)
  | _, p, _ => p

def dispatchCode : ProgHOL 64 :=
  (sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2.2.1

theorem lookup_op_dispatch : originalRuntimeCode.lookup (ofString "op_dispatch") =
    some ((sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 577 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_dispatch) rfl

def dispatchGroup01 : ProgHOL 64 :=
  binaryAt [0, 0, 0, 0] dispatchCode

def dispatchGroup02 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 6 (binaryAt [0, 0, 0, 1] dispatchCode) tail

def dispatchGroup03 : ProgHOL 64 :=
  binaryAt [0, 0, 0, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchGroup04 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 9 (binaryAt [1, 0, 0, 0, 0] dispatchCode) tail

def dispatchGroup05 : ProgHOL 64 :=
  binaryAt [1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchGroup06 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 12 (binaryAt [1, 0, 0, 0, 1] dispatchCode) tail

def dispatchGroup07 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 6 (binaryAt [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode) tail

def dispatchGroup08 : ProgHOL 64 :=
  binaryAt [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

def dispatchGroup09 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 1 (binaryAt [1, 1] dispatchCode) tail

def dispatchGroup10 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 4 (binaryAt [1, 1, 1] dispatchCode) tail

def dispatchGroup11 (tail : ProgHOL 64) : ProgHOL 64 :=
  seqCut 7 (binaryAt [1, 1, 1, 1, 1, 1, 1] dispatchCode) tail

def dispatchGroup12 : ProgHOL 64 :=
  binaryAt [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] dispatchCode

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
