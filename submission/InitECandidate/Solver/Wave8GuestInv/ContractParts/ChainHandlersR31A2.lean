import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A1
/-! # Wave 8 R31 S1: Chain-WF handler specs for the remaining opcodes (part A2)

wsSafe cascade (addmod/mulmod), dynamic-gas handlers, and the closing
`OpHandlerChainSpec` bridges.  Imports the infrastructure from `ChainHandlersR31A1`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09ChainWF


/-! ## 6. addmod/mulmod: wsSafe cascade -/

private theorem shapeEqHOL_symm_g31 {a b : ShapeHOL} (h : shapeEqHOL a b = true) :
    shapeEqHOL b a = true :=
  (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp h).symm


private def digitsLenBody_g31 : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_digits_len).body

private theorem lookup_u256_to_digits_locals_g31
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "u256_to_digits") vals = some (body, callee, rs)) :
    ∃ vp va, vals = [vp, va] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_digits).body ∧
      callee.lookup (ofString "p") = some vp ∧
      callee.lookup (ofString "a") = some va ∧
      shapeEqHOL (shapeOfHOLExact vp) .one = true ∧
      shapeEqHOL (shapeOfHOLExact va) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_u256_to_digits, List.length] at hraw
  rcases vals with _ | ⟨vp, _ | ⟨va, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      have hp := congrFun hfn (ofString "p")
      have ha := congrFun hfn (ofString "a")
      refine ⟨vp, va, rfl, hb, ?_, ?_,
        shapeEqHOL_symm_g31 hshapes.2.2.1, shapeEqHOL_symm_g31 hshapes.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "p" ≠ ofString "a" by decide] using hp
      · simpa [FUPDATE_LIST, FUPDATE] using ha
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_digits_len_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_len") vals = some (body, callee, rs)) :
    ∃ vp vn, vals = [vp, vn] ∧
      body = digitsLenBody_g31 ∧
      callee.lookup (ofString "p") = some vp ∧
      callee.lookup (ofString "n") = some vn ∧
      shapeEqHOL (shapeOfHOLExact vp) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vn) .one = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_len, List.length] at hraw
  rcases vals with _ | ⟨vp, _ | ⟨vn, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      have hp := congrFun hfn (ofString "p")
      have hn := congrFun hfn (ofString "n")
      refine ⟨vp, vn, rfl, hb, ?_, ?_,
        shapeEqHOL_symm_g31 hshapes.2.2.1, shapeEqHOL_symm_g31 hshapes.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "p" ≠ ofString "n" by decide] using hp
      · simpa [FUPDATE_LIST, FUPDATE] using hn
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_divmnu_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "divmnu") vals = some (body, callee, rs)) :
    ∃ vq vr vu vm vv vn, vals = [vq, vr, vu, vm, vv, vn] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_divmnu).body ∧
      callee.lookup (ofString "q") = some vq ∧
      callee.lookup (ofString "r") = some vr ∧
      callee.lookup (ofString "u") = some vu ∧
      callee.lookup (ofString "m") = some vm ∧
      callee.lookup (ofString "v") = some vv ∧
      callee.lookup (ofString "n") = some vn ∧
      shapeEqHOL (shapeOfHOLExact vu) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vv) .one = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_divmnu, List.length] at hraw
  rcases vals with _ | ⟨vq, _ | ⟨vr, _ | ⟨vu, _ | ⟨vm, _ | ⟨vv, _ | ⟨vn, _ | _⟩⟩⟩⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vq, vr, vu, vm, vv, vn, rfl, hb, ?_, ?_, ?_, ?_, ?_, ?_,
        shapeEqHOL_symm_g31 hshapes.2.2.2.2.1, shapeEqHOL_symm_g31 hshapes.2.2.2.2.2.2.1⟩
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "q" ≠ ofString "n" by decide,
          show ofString "q" ≠ ofString "v" by decide,
          show ofString "q" ≠ ofString "m" by decide,
          show ofString "q" ≠ ofString "u" by decide,
          show ofString "q" ≠ ofString "r" by decide] using congrFun hfn (ofString "q")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "r" ≠ ofString "n" by decide,
          show ofString "r" ≠ ofString "v" by decide,
          show ofString "r" ≠ ofString "m" by decide,
          show ofString "r" ≠ ofString "u" by decide] using congrFun hfn (ofString "r")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "u" ≠ ofString "n" by decide,
          show ofString "u" ≠ ofString "v" by decide,
          show ofString "u" ≠ ofString "m" by decide] using congrFun hfn (ofString "u")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "m" ≠ ofString "n" by decide,
          show ofString "m" ≠ ofString "v" by decide] using congrFun hfn (ofString "m")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "v" ≠ ofString "n" by decide,
          show ofString "v" ≠ ofString "n" by decide] using congrFun hfn (ofString "v")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "n")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_digits_divmod_locals_g31
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") vals = some (body, callee, rs)) :
    ∃ vu vm vd, vals = [vu, vm, vd] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_digits_divmod).body ∧
      callee.lookup (ofString "u") = some vu ∧
      callee.lookup (ofString "m") = some vm ∧
      callee.lookup (ofString "d") = some vd ∧
      shapeEqHOL (shapeOfHOLExact vu) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vm) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vd) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod, List.length] at hraw
  rcases vals with _ | ⟨vu, _ | ⟨vm, _ | ⟨vd, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vu, vm, vd, rfl, hb, ?_, ?_, ?_,
        shapeEqHOL_symm_g31 hshapes.2.2.1, shapeEqHOL_symm_g31 hshapes.2.2.2.1, shapeEqHOL_symm_g31 hshapes.2.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "u" ≠ ofString "d" by decide,
          show ofString "u" ≠ ofString "m" by decide] using congrFun hfn (ofString "u")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "m" ≠ ofString "d" by decide] using congrFun hfn (ofString "m")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "d")
    · simp at hraw
  · simp [List.length] at hraw

private theorem evalList_two_eq_g31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [e1, e2] = some vals) :
    ∃ v1 v2,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 = some v2 ∧
      vals = [v1, v2] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  refine ⟨v1, v2, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2] using h.symm

private theorem evalList_three_eq_g31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 = some v2 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 = some v3 ∧
      vals = [v1, v2, v3] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 with _ | v3
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

private theorem eval_u256_ws_plus_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {off : Nat} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "u256_ws"), .const (BitVec.ofNat 64 off)]) = some v) :
    v = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off)) := by
  simp only [evalHOLExact, evalListHOLExact, wordOpHOL] at hev
  rcases hgl : s.globals.lookup (ofString "u256_ws") with _ | gv
  · simp [hgl] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _ <;> simp [hgl, valueIsWord, valueWord, wordOp] at hev
    have hgw := eval_global_word_eq_ofNat he.globals hgl
    rw [hgw] at hev
    simpa [BitVec.add_zero] using hev.symm

private theorem eval_or4_ne_zero_g31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {b0 b1 b2 b3 : BitVec 64}
    (hb : s.locals.lookup nm =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (hcmp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 0#64))) :
    (b0 ||| b1 ||| b2 ||| b3) ≠ 0 := by
  intro hz
  have h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 1#64)) := by
    simp only [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    have hz' : OrOp.or b0 (OrOp.or b1 (OrOp.or b2 (OrOp.or b3 0))) = 0#64 := by
      change (b0 ||| (b1 ||| (b2 ||| (b3 ||| 0#64)))) = 0#64
      simpa [BitVec.or_zero, BitVec.or_assoc] using hz
    rw [hz']
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [h1] at hcmp
  simp at hcmp

private theorem ite_return_skip_none_g31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond retExp : ExpHOL 64}
    (hn : (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).1 = none) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word 0#64)) ∧
    (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          exact ⟨rfl, by simp [evaluateHOLFiniteState_skip]⟩
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_return] at hn
          exfalso; revert hn
          split; · simp
          split <;> simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem ite_tail_skip_none_g31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {fname : MlS} {args : List (ExpHOL 64)}
    (hn : (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).1 = none) :
    (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          simp [evaluateHOLFiniteState_skip]
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_call] at hn
          exfalso; revert hn
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, cal, rs⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, cp⟩
                cases rb with
                | none => simp
                | some r0 =>
                  cases r0 with
                  | returned _ => dsimp only; split <;> simp
                  | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem call_void_u256_to_digits_wsSafe_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {pExp aExp : ExpHOL 64} {off : Nat}
    (hoff : off + 64 ≤ 640)
    (hp : ∀ vp, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp = some vp →
      vp = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).2.locals = s.locals) := by
  refine ⟨WsSafe.call_void ?_, ?_⟩
  · intro vals body callee rs hargs hl _
    obtain ⟨v1, v2, hv1, _, rfl⟩ := evalList_two_eq_g31 hargs
    have hv1_eq := hp v1 hv1; subst hv1_eq
    rw [he.code] at hl
    obtain ⟨_, _, hinj_v, rfl, hp_cal, ha_cal, _, hsh_a⟩ := lookup_u256_to_digits_locals_g31 hl
    simp only [List.cons.injEq] at hinj_v
    obtain ⟨rfl, rfl, _⟩ := hinj_v
    obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inr hsh_a)
    exact (u256_to_digits_wsSafe_and_post (he.with_locals_clock callee _) hoff hp_cal ha_cal).1
  · rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, aExp] with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup (ofString "u256_to_digits") vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
          cases rb with
          | none => simp
          | some r0 =>
            cases r0 with
            | returned _ => dsimp only; split <;> simp
            | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp

private theorem call_tail_digits_divmod_wsSafe_g31 {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {uExp dExp : ExpHOL 64} {mv : Nat} {d0 d1 d2 d3 : BitVec 64}
    (hm_le : mv ≤ 16)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dExp =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)]))
    (hd_nz : (d0 ||| d1 ||| d2 ||| d3) ≠ 0) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (.call none (ofString "digits_divmod") [uExp, .const (BitVec.ofNat 64 mv), dExp])) := by
  refine WsSafe.call_tail ?_
  intro vals body callee rs hargs hl _
  obtain ⟨v1, v2, v3, _, hv2, hv3, rfl⟩ := evalList_three_eq_g31 hargs
  have hv2_eq : v2 = .val (.word (BitVec.ofNat 64 mv)) := by simpa [evalHOLExact] using hv2.symm
  have hv3_eq : v3 = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)] := by
    rw [hd] at hv3; exact Option.some.inj hv3.symm
  subst hv2_eq hv3_eq
  rw [he.code] at hl
  obtain ⟨_, _, _, hinj3, rfl, hu_c, hm_c, hd_c, hsh_u, _, _⟩ := lookup_digits_divmod_locals_g31 hl
  simp only [List.cons.injEq] at hinj3
  obtain ⟨rfl, rfl, rfl, _⟩ := hinj3
  obtain ⟨uw, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_u)
  exact digits_divmod_wsSafe (he.with_locals_clock callee _) hu_c hm_c hd_c hm_le hd_nz

private theorem lookup_three_comb4_locals_g31 {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ m0 m1 m2 m3, callee.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | ⟨vm, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨m0, m1, m2, m3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2.2)
      refine ⟨hb, ⟨m0, m1, m2, m3, ?_⟩⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "m")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_u256_addmod_g31 :
    originalRuntimeCode.lookup (ofString "u256_addmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_addmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 75 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_addmod) rfl

private theorem lookup_u256_mulmod_g31 :
    originalRuntimeCode.lookup (ofString "u256_mulmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mulmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 76 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mulmod) rfl


theorem epsA_u256_addmod :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True)
      (ofString "u256_addmod") := by
  refine epsA_of_wsSafe_g31 75 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_addmod rfl ?_
  intro F s he ⟨vals0, hlk0⟩
  obtain ⟨_, m0, m1, m2, m3, hm⟩ := lookup_three_comb4_locals_g31 lookup_u256_addmod_g31 hlk0
  dsimp only [extractFn, Guest.Software.guestFn_u256_addmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  -- 1. `if ((m0 | m1 | m2 | m3) == 0) return 0`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_m0 _
  obtain ⟨hcmp_m0, hs_m0⟩ := ite_return_skip_none_g31 hn_m0
  have hm_nz : (m0 ||| m1 ||| m2 ||| m3) ≠ 0 := eval_or4_ne_zero_g31 hm hcmp_m0
  rw [hs_m0]
  -- 2. `decCall "s" .comb5 "u256_add_carry" [a, b]`
  refine WsSafe.decCall_ro he (by decide) fun vs cpost_s hs1_env _ _ => ?_
  set s1 := setVarHOLFinite (ofString "s") vs { cpost_s with locals := s.locals }
  -- 3. `dec "sum" .comb4 ...`
  refine WsSafe.dec fun vsum _ _ => ?_
  set s2 := setVarHOLFinite (ofString "sum") vsum s1
  have hs2_env : WsEnv s s2 := hs1_env.with_locals_clock _ _
  -- 4. `if (s.4 == 0) (call none "u256_mod" [sum, m]) else skip`
  refine WsSafe.seq
    (WsSafe.ite
      (fun _ _ _ => WsSafe.call_tail fun _ _ _ _ _ hl _ => call_u256_mod_wsSafe_g31 hs2_env hl)
      (fun _ => WsSafe.skip _ _)) ?_
  intro hn_ite _
  rw [ite_tail_skip_none_g31 hn_ite]
  -- 5. `dec "u" (u256_ws + 424)`
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus_g31 hs2_env hvu]
  set s3 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) s2
  have hs3_env : WsEnv s s3 := hs2_env.with_locals_clock _ _
  have hu_s3 : s3.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s3, setVarHOLFinite, FUPDATE]
  have hm_s3 : s3.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    simp [s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "u" ≠ ofString "m" by decide,
      show ofString "sum" ≠ ofString "m" by decide,
      show ofString "s" ≠ ofString "m" by decide, hm]
  -- 6. `u256_to_digits(u, sum)` (`424..488`)
  have htd := call_void_u256_to_digits_wsSafe_g31 hs3_env
    (pExp := .var .local (ofString "u")) (aExp := .var .local (ofString "sum")) (off := 424)
    (by omega) (fun vp hvp => by simpa [evalHOLExact, hu_s3] using hvp.symm)
  refine WsSafe.seq htd.1 fun hn_td heff_td => ?_
  set s4 := (evaluateHOLFiniteState s3 _).2
  have hs4_env : WsEnv s s4 := hs3_env.step heff_td
  have hs4_loc : s4.locals = s3.locals := htd.2 hn_td
  have hu_s4 : s4.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs4_loc]; exact hu_s3
  have hu_add : ∀ c : Nat, c < 100 →
      BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424 + BitVec.ofNat 64 c =
        BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 (424 + c) := by
    intro c hc
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- 7. `store (u + 64) 1` (`488`), `store (u + 72) 0` (`496`), tail-call `digits_divmod(u, 10, m)`
  refine WsSafe.seq_store_ws_const_off hs4_env (off := 488)
    (by
      simp only [evalHOLExact, evalListHOLExact, hu_s4, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (64#64 + 0 : BitVec 64) = 64#64 from BitVec.add_zero _]
      exact hu_add 64 (by omega))
    (by omega)
    (fun _ hv => eval_word_of_const hv) fun s5 hs5_env hs5_loc => ?_
  have hu_s5 : s5.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs5_loc]; exact hu_s4
  refine WsSafe.seq_store_ws_const_off hs5_env (off := 496)
    (by
      simp only [evalHOLExact, evalListHOLExact, hu_s5, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (72#64 + 0 : BitVec 64) = 72#64 from BitVec.add_zero _]
      exact hu_add 72 (by omega))
    (by omega)
    (fun _ hv => eval_word_of_const hv) fun s6 hs6_env hs6_loc => ?_
  have hm_s6 : s6.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    rw [hs6_loc, hs5_loc, hs4_loc]; exact hm_s3
  exact call_tail_digits_divmod_wsSafe_g31 hs6_env (by omega)
    (by simp only [evalHOLExact]; exact hm_s6) hm_nz

theorem epsA_u256_mulmod :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True)
      (ofString "u256_mulmod") := by
  refine epsA_of_wsSafe_g31 76 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mulmod rfl ?_
  intro F s he ⟨vals0, hlk0⟩
  obtain ⟨_, m0, m1, m2, m3, hm⟩ := lookup_three_comb4_locals_g31 lookup_u256_mulmod_g31 hlk0
  dsimp only [extractFn, Guest.Software.guestFn_u256_mulmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  -- 1. `if ((m0 | m1 | m2 | m3) == 0) return 0`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_m0 _
  obtain ⟨hcmp_m0, hs_m0⟩ := ite_return_skip_none_g31 hn_m0
  have hm_nz : (m0 ||| m1 ||| m2 ||| m3) ≠ 0 := eval_or4_ne_zero_g31 hm hcmp_m0
  rw [hs_m0]
  -- 2. `dec "u" (u256_ws + 424)`
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus_g31 he hvu]
  set s1 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) s
  have hs1_env : WsEnv s s1 := he.with_locals_clock _ _
  have hu_s1 : s1.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s1, setVarHOLFinite, FUPDATE]
  have hm_s1 : s1.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    simp [s1, setVarHOLFinite, FUPDATE, show ofString "u" ≠ ofString "m" by decide, hm]
  -- 3. `if (high limbs == 0) { decCall p mul64x64 ... } else skip`
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)
    refine WsSafe.decCall_ro hs1_env (by decide) fun vp cpost_p hs2_env _ _ => ?_
    set s2 := setVarHOLFinite (ofString "p") vp { cpost_p with locals := s1.locals }
    refine WsSafe.seq
      (WsSafe.ite
        (fun _ _ _ => WsSafe.call_tail fun _ _ _ _ _ hl _ => call_u256_mod_wsSafe_g31 hs2_env hl)
        (fun _ => WsSafe.skip _ _)) ?_
    intro hn_p1 _
    rw [ite_tail_skip_none_g31 hn_p1]
    have hu_s2 : s2.locals.lookup (ofString "u") =
        some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "u" by decide, hu_s1]
    have htd_p := call_void_u256_to_digits_wsSafe_g31 hs2_env
      (pExp := .var .local (ofString "u"))
      (aExp := .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64])
      (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s2] using hv.symm)
    refine WsSafe.seq htd_p.1 fun hn_tdp heff_tdp => ?_
    set s3 := (evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "u256_to_digits")
        [.var .local (ofString "u"),
         .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])).2
    have hs3_env : WsEnv s s3 := hs2_env.step heff_tdp
    have hm_s3 : s3.locals.lookup (ofString "m") =
        some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
      rw [htd_p.2 hn_tdp]
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "m" by decide, hm_s1]
    exact call_tail_digits_divmod_wsSafe_g31 hs3_env (by omega)
      (by simp only [evalHOLExact]; exact hm_s3) hm_nz
  -- Continuation when fast-path `ite` finishes with `none`: fast-path ends in tail-call `digits_divmod`, so `.1 = none` implies `s1`!
  intro hn_fast _
  have hs_fast := by
    let p_fast : ProgHOL 64 :=
      .ite (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                                  .rfield 2 (.var .local (ofString "a")),
                                  .rfield 3 (.var .local (ofString "a")),
                                  .rfield 1 (.var .local (ofString "b")),
                                  .rfield 2 (.var .local (ofString "b")),
                                  .rfield 3 (.var .local (ofString "b"))]) (.const 0#64))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.seq
            (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "p"))) (.const 0#64))
              (.call none (ofString "u256_mod")
                [.rstruct [.rfield 0 (.var .local (ofString "p")), .const 0#64, .const 0#64, .const 0#64],
                 .var .local (ofString "m")])
              .skip)
            (.seq
              (.call (some (none, none)) (ofString "u256_to_digits")
                [.var .local (ofString "u"),
                 .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])
              (.call none (ofString "digits_divmod")
                [.var .local (ofString "u"), .const 4#64, .var .local (ofString "m")]))))
        .skip
    show (evaluateHOLFiniteState s1 p_fast).2 = s1
    change (evaluateHOLFiniteState s1 p_fast).1 = none at hn_fast
    dsimp only [p_fast] at hn_fast ⊢
    rw [evaluateHOLFiniteState_ite] at hn_fast ⊢
    rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                             .rfield 2 (.var .local (ofString "a")),
                             .rfield 3 (.var .local (ofString "a")),
                             .rfield 1 (.var .local (ofString "b")),
                             .rfield 2 (.var .local (ofString "b")),
                             .rfield 3 (.var .local (ofString "b"))]) (.const 0#64)) with _ | v
    · simp [hcond] at hn_fast
    · cases v with
      | val hl =>
        cases hl with
        | word w =>
          simp only [hcond] at hn_fast ⊢
          by_cases hw0 : w = 0
          · subst hw0; simp [evaluateHOLFiniteState_skip]
          · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_decCall_fixClockRewrite] at hn_fast
            exfalso; revert hn_fast
            rcases evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vals
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64") vals with _ | ⟨bd, cal, rs⟩
              · simp
              · dsimp only; split
                · simp
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal) bd with ⟨rb, cp⟩
                  cases rb with
                  | none => simp
                  | some r0 =>
                    cases r0 with
                    | returned rv =>
                      dsimp only; split
                      · rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState _ (.ite _ _ _) with ⟨ri, si⟩
                        cases ri; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState si (.call (some (none, none)) _ _) with ⟨rc1, sc1⟩
                        cases rc1; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_call]
                        rcases evalListHOLFinite sc1 (h := fun a => Classical.propDecidable (sc1.memaddrs a)) _ with _ | vals2
                        · simp
                        · dsimp only
                          rcases lookupCodeHOLFinite sc1.code.lookup (ofString "digits_divmod") vals2 with _ | ⟨bd2, cal2, rs2⟩
                          · simp
                          · dsimp only; split
                            · simp
                            · rcases evaluateHOLFiniteState (callEntryStateHOLFinite sc1 cal2) bd2 with ⟨rb2, cp2⟩
                              cases rb2 with
                              | none => simp
                              | some r2 =>
                                cases r2 with
                                | returned _ => dsimp only; split <;> simp
                                | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
                      · simp
                    | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
      | rStruct _ => simp [hcond] at hn_fast
      | nStruct _ _ => simp [hcond] at hn_fast
  rw [hs_fast]
  -- 4. Full path: `decCall "f" .comb8 "u256_mul_full" [a, b]`
  refine WsSafe.decCall_ro hs1_env (by decide) fun vf cpost_f hs4_env _ _ => ?_
  set s4 := setVarHOLFinite (ofString "f") vf { cpost_f with locals := s1.locals }
  have hu_s4 : s4.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "u" by decide, hu_s1]
  have htd_lo := call_void_u256_to_digits_wsSafe_g31 hs4_env
    (pExp := .var .local (ofString "u"))
    (aExp := .rstruct [.rfield 0 (.var .local (ofString "f")), .rfield 1 (.var .local (ofString "f")),
                       .rfield 2 (.var .local (ofString "f")), .rfield 3 (.var .local (ofString "f"))])
    (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s4] using hv.symm)
  refine WsSafe.seq htd_lo.1 fun hn_lo heff_lo => ?_
  set s5 := (evaluateHOLFiniteState s4 _).2
  have hs5_env : WsEnv s s5 := hs4_env.step heff_lo
  have hs5_loc : s5.locals = s4.locals := htd_lo.2 hn_lo
  have hu_s5 : s5.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs5_loc]; exact hu_s4
  have htd_hi := call_void_u256_to_digits_wsSafe_g31 hs5_env
    (pExp := .op .add [.var .local (ofString "u"), .const 64#64])
    (aExp := .rstruct [.rfield 4 (.var .local (ofString "f")), .rfield 5 (.var .local (ofString "f")),
                       .rfield 6 (.var .local (ofString "f")), .rfield 7 (.var .local (ofString "f"))])
    (off := 488) (by omega)
    (fun v hv => by
      simp only [evalHOLExact, evalListHOLExact, hu_s5, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr] at hv
      injection hv with hv'
      rw [← hv']; congr 2
      rw [show (64#64 + 0 : BitVec 64) = 64#64 from BitVec.add_zero _, BitVec.add_assoc]
      congr 1)
  refine WsSafe.seq htd_hi.1 fun hn_hi heff_hi => ?_
  set s6 := (evaluateHOLFiniteState s5 _).2
  have hs6_env : WsEnv s s6 := hs5_env.step heff_hi
  have hm_s6 : s6.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    rw [htd_hi.2 hn_hi, hs5_loc]
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "m" by decide, hm_s1]
  exact call_tail_digits_divmod_wsSafe_g31 hs6_env (by omega)
    (by simp only [evalHOLExact]; exact hm_s6) hm_nz

theorem op_addmod_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_addmod") := by
  refine opHandlerSpecA_of_run 482 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_addmod rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_addmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · refine HandlerRunA.decCall_simple epsA_u256_addmod ?_
    refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
    exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_addmod_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_addmod") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_addmod_specA)

theorem op_mulmod_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_mulmod") := by
  refine opHandlerSpecA_of_run 483 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mulmod rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_mulmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · refine HandlerRunA.decCall_simple epsA_u256_mulmod ?_
    refine HandlerRunA.seq_call_simple epsA_stack_push_g09 ?_
    exact HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_mulmod_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mulmod") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_mulmod_specA)

/-! ## 7. `op_exp` (dynamic gas) and `op_stop` -/

theorem epsA_u256_byte_length_le32 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ 32)
      (ofString "u256_byte_length") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := Group09ChainWF.epsA_of_readOnly 79 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_byte_length rfl opRoCallees opRoCallees_good rfl
  have hlk_eq := M13.lookup_u256_byte_length.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, M13.lookup_u256_byte_length, ?_⟩
  intro F s hcode hInv hWF hP hlookup hnt
  have hs := hro s hcode hInv hWF hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨⟨h1, hWFp⟩, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨⟨h1, hWFp⟩, h2, h3, hlf, M13.u256_byte_length_body_le_32 s hcode v hv⟩

theorem op_exp_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_exp") := by
  refine opHandlerSpecA_of_run 484 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_exp rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_exp, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine Group09ChainWF.HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine Group09ChainWF.HandlerRunA.decCall
    (Q := fun t => ∃ nbw : BitVec 64, t.locals.lookup (ofString "nb") = some (.val (.word nbw)) ∧ nbw.toNat ≤ 32)
    epsA_u256_byte_length_le32
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ _ _ _ _ _ _ _ hQc => by
      obtain ⟨_, nbw, rfl, hle⟩ := hQc
      exact ⟨nbw, by simp [setVarHOLFinite, FUPDATE], hle⟩)
    (Group09ChainWF.HandlerRunA.seq_charge_gas_exact
      (Q := fun _ => True)
      (fun t w hw _ _ ⟨nbw, hnb, hle⟩ => by
        have hev_amt : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.op .add [.const 10#64, .panop .mul [.const 50#64, .var .local (ofString "nb")]]) =
            some (.val (.word (10#64 + 50#64 * nbw))) := by
          simp [evalHOLExact, evalListHOLExact, hnb, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
        rw [hev_amt] at hw
        injection hw with h1; injection h1 with h2; injection h2 with h3
        subst h3
        have hmul : (50#64 * nbw).toNat = 50 * nbw.toNat := by
          rw [BitVec.toNat_mul, show (50#64 : BitVec 64).toNat = 50 by decide, Nat.mod_eq_of_lt (by omega)]
        rw [BitVec.toNat_add, show (10#64 : BitVec 64).toNat = 10 by decide, hmul,
            Nat.mod_eq_of_lt (by omega)]
        omega)
      (fun t cpost amtw _ _ _ _ _ _ _ _ _ _ => trivial)
      (Group09ChainWF.HandlerRunA.decCall_simple epsA_u256_exp
        (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09
          (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))))

theorem op_exp_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_exp") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_exp_specA)

theorem op_stop_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_stop") := by
  refine opHandlerSpecA_of_run 502 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_stop rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  have hRun : EvmRun s0 := ⟨hInv0, hnd0⟩
  dsimp only [Guest.Software.guestFn_op_stop, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  intro t hc hi hw hlen hR _ hnt
  simp only [Bool.false_eq_true, ↓reduceIte] at hR
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hi
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const 104#64]) (.const 0#64)) with ⟨r1, s1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error' hst; subst herr
    exact Group09ChainWF.opDispatchPostA_error s0 s1
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨w1, hw1_ev, hs1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := t) (post := s1)
      (gname := "ev") (gbase := globN t "ev") (off := 104) hevw hevw_nat (by omega)
      (fun v hv => by
        simp only [evalHOLExact] at hv
        injection hv with hv'
        exact ⟨0#64, hv'.symm⟩) hst
    have hw1_zero : w1 = 0#64 := by
      simp only [evalHOLExact] at hw1_ev
      injection hw1_ev with h1; injection h1 with h2; injection h2 with h3
      exact h3.symm
    subst hw1_zero
    have hGs1 : GuestInv s1 := guestInv_congr (s := t)
      (by simp [hs1_eq]) (by simp [hs1_eq]) (by simp [hs1_eq]) (by simp [hs1_eq]) hi.1.1
    have hglob_s1 : s1.globals = t.globals := by simp [hs1_eq]
    have hbe_s1 : s1.be = t.be := by simp [hs1_eq]
    have hcode_s1 : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hc
    have hmem_ne_s1 : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN t "ev" + 104) →
        s1.memory x = t.memory x := by
      intro x hx
      rw [hs1_eq]; dsimp only [R14Shards.OpHandlersA.updW]
      rw [if_neg hx]
    have hmem_out_s1 : ∀ x : BitVec 64,
        (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off)) →
        s1.memory x = t.memory x := fun x hx =>
      hmem_ne_s1 x (hx 104 (by simp [nonStructFrameOffs]))
    obtain ⟨hInv_s1, hch_s1, hR_s1⟩ := evmInv_of_head_nonstruct hi hGs1 hglob_s1 hbe_s1 hmem_out_s1
    have hWF_s1 : HeadMemChainWF s1 :=
      headMemChainWF_store_headSafe' hi hw
        (x := BitVec.ofNat 64 (globN t "ev" + 104))
        (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact Or.inl ⟨104, rfl, by omega, by omega, by omega, by omega⟩)
        hglob_s1 hch_s1 hmem_ne_s1
    have hm104_s1 : memW s1 (globN t "ev" + 104) = 0 := by
      rw [hs1_eq]; simpa using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0#64
    -- step through `call (some (none, none)) "pc_add" [1]`
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
    have hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) [.const 1#64] =
        some [.val (.word 1#64)] := by
      rw [evalListHOLFinite_eq_toExact]; rfl
    simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s1.code.lookup (ofString "pc_add") [.val (.word 1#64)] with _ | ⟨body', callee, ret'⟩
    · exact Group09ChainWF.opDispatchPostA_error s0 s1
    · simp only [hl] at hnt ⊢
      by_cases hz : s1.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "pc_add") [.val (.word 1#64)] =
            some (body', callee, ret') := by rwa [← hcode_s1]
        obtain ⟨rfl, rfl, _, _, _⟩ := one_word_arg_lookup lookup_pc_add hl_orig
        have hbody_pc : sourceFnBody Guest.Software.guestFn_pc_add =
            .seq
              (.store (.op .add [.var .global (ofString "ev"), .const 0])
                (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
              (.return (.const 0)) := rfl
        let ce := callEntryStateHOLFinite s1 callee
        have hInv_ce : EvmInv ce := localsFree_evmInv s1 callee (s1.clock - 1) hInv_s1
        have hWF_ce : HeadMemChainWF ce := headMemChainWF_locals s1 callee (s1.clock - 1) hWF_s1
        have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          change s1.globals.lookup (ofString "ev") = _; rw [hglob_s1]; exact hevw
        rw [hbody_pc, evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst_pc : evaluateHOLFiniteState ce
            (.store (.op .add [.var .global (ofString "ev"), .const 0])
              (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) with ⟨rpc, spc⟩
        simp only [hst_pc] at hnt ⊢
        cases rpc with
        | some res_pc =>
          have herr_pc := store_some_eq_error' hst_pc; subst herr_pc
          dsimp only at hnt ⊢
          exact Group09ChainWF.opDispatchPostA_error s0 spc.emptyLocalsHOLFinite
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨wpc, _, hspc_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := ce) (post := spc)
            (gname := "ev") (gbase := globN t "ev") (off := 0) hevw_ce hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv; revert hv
              rcases @evalListHOLExact 64 F _ ce.toExact (fun a => Classical.propDecidable (ce.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) hst_pc
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact]
          have hsz0 : sizeOfShapeWithContextHOL spc.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0]
          dsimp only
          have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          simp only [hsh0, ↓reduceIte]
          let s2 : PanSemStateFiniteExact 64 F := { (emptyLocalsHOLFinite spc) with locals := s1.locals }
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact]
          have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
              (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0_s2]
          dsimp only
          let post := emptyLocalsHOLFinite s2
          have hGpost : GuestInv post := guestInv_congr (s := t)
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            hi.1.1
          have hglob_post : post.globals = t.globals := by
            simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq]
          have hbe_post : post.be = t.be := by
            simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq]
          have hmem_out_post : ∀ x : BitVec 64,
              (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off)) →
              post.memory x = t.memory x := by
            intro x hx
            change spc.memory x = t.memory x
            rw [hspc_eq]; dsimp only [R14Shards.OpHandlersA.updW]
            rw [if_neg (hx 0 (by simp [nonStructFrameOffs]))]
            exact hmem_out_s1 x hx
          obtain ⟨hInv_post, hch_post, hR_post⟩ :=
            evmInv_of_head_nonstruct hi hGpost hglob_post hbe_post hmem_out_post
          have hmem_ne_post : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN t "ev" + 0) →
              post.memory x = s1.memory x := by
            intro x hx
            change spc.memory x = s1.memory x
            rw [hspc_eq]; dsimp only [R14Shards.OpHandlersA.updW]
            rw [if_neg hx]
            rfl
          have hWF_post : HeadMemChainWF post :=
            headMemChainWF_store_headSafe' hInv_s1 hWF_s1
              (x := BitVec.ofNat 64 (globN t "ev" + 0))
              (by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                exact Or.inl ⟨0, by simp [globN, hglob_s1], by omega, by omega, by omega, by omega⟩)
              (hglob_post.trans hglob_s1.symm) (hch_post.trans hch_s1.symm) hmem_ne_post
          have hDone_post : EvmDone post := by
            right; left
            have hgev : globN post "ev" = globN t "ev" := by simp [globN, hglob_post]
            rw [hgev]
            change memW spc (globN t "ev" + 104) = 0
            rw [hspc_eq, R14Shards.OpHandlersA.memW_updW_ne ce (globN t "ev" + 0) (globN t "ev" + 104) wpc (by omega) (by omega) (by omega)]
            exact hm104_s1
          have hpot_lt : evmPot post < evmPot s0 :=
            evmPot_lt_of_done hRun hInv_post hDone_post
              (by rw [hch_post, hlen]) (by rw [hR_post]; exact hR)
          refine ⟨fun _ => ⟨⟨hInv_post, hWF_post⟩, hpot_lt⟩, ?_⟩
          rintro ⟨_, h⟩; cases h

theorem op_stop_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_stop") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_stop_specA)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A
