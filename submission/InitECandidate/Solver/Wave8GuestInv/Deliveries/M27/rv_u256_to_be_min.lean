import InitECandidate.Solver.Wave8GuestInv.Defs

/-! Value contract `rv_u256_to_be_min` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs`.
Restates `FunSpec` and `RetLe` verbatim from `campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28`
so they delta-reduce definitionally (`rfl`) to the spec statement in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M27

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FunSpec_u256 (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- Value contract (verbatim from `GuestInv.lean` @ `8a79d9f28`): a normal return is a word at most
`B` of the entry state. -/
def RetLe_u256 (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec_u256 GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

private def WordBound (M : Nat) (v : ValueHOL 64) : Prop :=
  ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ M

private theorem lookup_bit_length64 :
    originalRuntimeCode.lookup (ofString "bit_length64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bit_length64, .one) :=
  lookup_of_guestAst_getElem 77 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bit_length64) rfl

private theorem lookup_u256_bit_length :
    originalRuntimeCode.lookup (ofString "u256_bit_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_bit_length, .one) :=
  lookup_of_guestAst_getElem 78 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_bit_length) rfl

private theorem lookup_u256_byte_length :
    originalRuntimeCode.lookup (ofString "u256_byte_length") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_byte_length, .one) :=
  lookup_of_guestAst_getElem 79 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_byte_length) rfl

theorem lookup_u256_to_be_min :
    originalRuntimeCode.lookup (ofString "u256_to_be_min") =
      some ((sourceFunctionEntry Guest.Software.guestFn_u256_to_be_min).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 88 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_be_min) rfl

private theorem bit_length64_body_returns_le64 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_bit_length64) =
      (some (.returned retVal), post)) :
    WordBound 64 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_bit_length64,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hrun
  let s0 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) state
  have stepIte : ∀ {st : PanSemStateFiniteExact 64 F} {n x : BitVec 64} (k : BitVec 64)
      (hklt : k.toNat < 64) (tail : ProgHOL 64),
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "x") = some (.val (.word x)) →
      evaluateHOLFiniteState st
        (.seq
          (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k))
              (.const 0#64))
            (.seq
              (.assign .local (ofString "n")
                (.op .add [.var .local (ofString "n"), .const k]))
              (.assign .local (ofString "x")
                (.shift .lsr (.var .local (ofString "x")) (.const k))))
            .skip)
          tail) =
      evaluateHOLFiniteState
        (if (x >>> k.toNat) ≠ 0#64 then
          setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
            (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)
         else st)
        tail := by
    intro st n x k hklt tail hn hx
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hnotge : ¬ (64 ≤ k.toNat) := Nat.not_le.mpr hklt
    have hcond : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const k))
          (.const 0#64)) =
        some (.val (.word (if (x >>> k.toNat) ≠ 0#64 then 1#64 else 0#64))) := by
      simp only [evalHOLExact, hx, wordShiftHOL, hnotge, if_false,
        Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hnz : (x >>> k.toNat) ≠ 0#64 <;> simp [hnz]
    rw [hcond]
    by_cases hnz : (x >>> k.toNat) ≠ 0#64
    · rw [if_pos hnz]
      have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
      simp only [h10, if_false, if_pos hnz]
      have hassign1 : evaluateHOLFiniteState st
          (.assign .local (ofString "n")
            (.op .add [.var .local (ofString "n"), .const k])) =
          (none, setVarHOLFinite (ofString "n") (.val (.word (n + k))) st) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
          PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      have hx' : (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st).locals.lookup
          (ofString "x") = some (.val (.word x)) := by
        have hne : ofString "n" ≠ ofString "x" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hx]
      have hassign2 : evaluateHOLFiniteState
          (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)
          (.assign .local (ofString "x")
            (.shift .lsr (.var .local (ofString "x")) (.const k))) =
          (none,
            setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
              (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st)) := by
        simp [evaluateHOLFiniteState_assign, evalHOLExact, hx', wordShiftHOL, hnotge,
          lookupKvarHOLExact, PanSemStateFiniteExact.isValidValueHOLFinite,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_seq_line780, hassign1]
      dsimp only
      rw [hassign2]
    · rw [if_neg hnz, if_neg hnz]
      have h00 : (0#64 : BitVec 64) = 0 := rfl
      simp only [h00, if_true, evaluateHOLFiniteState_skip]
  have hrun1 := (Prod.mk.inj hrun).1
  clear hrun
  rcases hx0 : s0.locals.lookup (ofString "x") with _ | vx
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
    have hnone : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64)) (.const 0#64)) =
        none := by
      simp [evalHOLExact, hx0]
    rw [hnone] at hrun1
    simp at hrun1
  · cases vx with
    | rStruct _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
      have hnone :
          @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64))
              (.const 0#64)) = none := by
        simp [evalHOLExact, hx0]
      rw [hnone] at hrun1
      simp at hrun1
    | nStruct _ _ =>
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun1
      have hnone :
          @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
            (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64))
              (.const 0#64)) = none := by
        simp [evalHOLExact, hx0]
      rw [hnone] at hrun1
      simp at hrun1
    | val wlx =>
      cases wlx with
      | word x0 =>
        have stepRun : ∀ (st : PanSemStateFiniteExact 64 F) (n x k : BitVec 64) (M : Nat)
            (tail : ProgHOL 64),
            st.locals.lookup (ofString "n") = some (.val (.word n)) →
            st.locals.lookup (ofString "x") = some (.val (.word x)) →
            x.toNat < 2 ^ (2 * k.toNat) →
            n.toNat ≤ M →
            M ≤ 64 →
            2 * k.toNat ≤ 64 →
            0 < k.toNat →
            ∃ (st' : PanSemStateFiniteExact 64 F) (n' x' : BitVec 64),
              evaluateHOLFiniteState st
                (.seq
                  (.ite (.cmp .notEqual
                      (.shift .lsr (.var .local (ofString "x")) (.const k))
                      (.const 0#64))
                    (.seq
                      (.assign .local (ofString "n")
                        (.op .add [.var .local (ofString "n"), .const k]))
                      (.assign .local (ofString "x")
                        (.shift .lsr (.var .local (ofString "x")) (.const k))))
                    .skip)
                  tail) =
                evaluateHOLFiniteState st' tail ∧
              st'.locals.lookup (ofString "n") = some (.val (.word n')) ∧
              st'.locals.lookup (ofString "x") = some (.val (.word x')) ∧
              x'.toNat < 2 ^ k.toNat ∧
              n'.toNat ≤ M + k.toNat := by
          intro st n x k M tail hn hx hxlt hnle hm64 hk64 hkpos
          have hklt : k.toNat < 64 := by omega
          by_cases hnz : (x >>> k.toNat) ≠ 0#64
          · refine ⟨setVarHOLFinite (ofString "x") (.val (.word (x >>> k.toNat)))
              (setVarHOLFinite (ofString "n") (.val (.word (n + k))) st),
              n + k, x >>> k.toNat, ?_, ?_, ?_, ?_, ?_⟩
            · rw [stepIte k hklt tail hn hx, if_pos hnz]
            · have hne : ofString "x" ≠ ofString "n" := by decide
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
            · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have hpow : 2 ^ (2 * k.toNat) = 2 ^ k.toNat * 2 ^ k.toNat := by
                rw [Nat.two_mul, Nat.pow_add]
              rw [hpow] at hxlt
              exact Nat.div_lt_of_lt_mul hxlt
            · have h264 : 2 ^ 64 = 18446744073709551616 := rfl
              rw [BitVec.toNat_add_of_lt (by omega)]
              omega
          · refine ⟨st, n, x, ?_, hn, hx, ?_, by omega⟩
            · rw [stepIte k hklt tail hn hx, if_neg hnz]
            · have hzeq : x >>> k.toNat = 0#64 := Classical.not_not.mp hnz
              have hz0 : (x >>> k.toNat).toNat = 0 := by rw [hzeq]; rfl
              rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hz0
              by_contra hge
              have hle : 2 ^ k.toNat ≤ x.toNat := Nat.not_lt.mp hge
              have hpos_pow : 0 < 2 ^ k.toNat := Nat.pos_of_ne_zero (by positivity)
              have hdiv_pos : 0 < x.toNat / 2 ^ k.toNat := Nat.div_pos hle hpos_pow
              omega
        have hn0 : s0.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
          simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨s1, n1, x1, heq1, hn1, hx1, hx1lt, hn1le⟩ :=
          stepRun s0 0#64 x0 32#64 0 _ hn0 hx0 x0.isLt (by decide) (by decide) (by decide)
            (by decide)
        rw [heq1] at hrun1; clear heq1
        obtain ⟨s2, n2, x2, heq2, hn2, hx2, hx2lt, hn2le⟩ :=
          stepRun s1 n1 x1 16#64 32 _ hn1 hx1 hx1lt hn1le (by decide) (by decide) (by decide)
        rw [heq2] at hrun1; clear heq2
        obtain ⟨s3, n3, x3, heq3, hn3, hx3, hx3lt, hn3le⟩ :=
          stepRun s2 n2 x2 8#64 48 _ hn2 hx2 hx2lt hn2le (by decide) (by decide) (by decide)
        rw [heq3] at hrun1; clear heq3
        obtain ⟨s4, n4, x4, heq4, hn4, hx4, hx4lt, hn4le⟩ :=
          stepRun s3 n3 x3 4#64 56 _ hn3 hx3 hx3lt hn3le (by decide) (by decide) (by decide)
        rw [heq4] at hrun1; clear heq4
        obtain ⟨s5, n5, x5, heq5, hn5, hx5, hx5lt, hn5le⟩ :=
          stepRun s4 n4 x4 2#64 60 _ hn4 hx4 hx4lt hn4le (by decide) (by decide) (by decide)
        rw [heq5] at hrun1; clear heq5
        obtain ⟨s6, n6, x6, heq6, hn6, hx6, hx6lt, hn6le⟩ :=
          stepRun s5 n5 x5 1#64 62 _ hn5 hx5 hx5lt hn5le (by decide) (by decide) (by decide)
        have hretEq : evaluateHOLFiniteState s6
            (.return (.op .add [.var .local (ofString "n"), .var .local (ofString "x")])) =
            (some (.returned (.val (.word (n6 + x6)))), s6.emptyLocalsHOLFinite) := by
          simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hn6, hx6,
            wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact,
            sizeOfShapeWithContextHOL]
        rw [heq6, hretEq] at hrun1
        clear heq6 hretEq
        have hret : retVal = .val (.word (n6 + x6)) := by
          cases hrun1
          rfl
        refine ⟨n6 + x6, hret, ?_⟩
        have hx6le : x6.toNat ≤ 1 := by change x6.toNat < 2 at hx6lt; omega
        have hn6le' : n6.toNat ≤ 63 := hn6le
        have h264 : 2 ^ 64 = 18446744073709551616 := rfl
        rw [BitVec.toNat_add_of_lt (by omega)]
        omega

private theorem decCall_returned_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {name function : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64} {retVal : ValueHOL 64}
    (hrun : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) =
      (some (.returned retVal), post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (w : ValueHOL 64) (bodyPost inner : PanSemStateFiniteExact 64 F),
      s.clock ≠ 0 ∧
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned w), bodyPost) ∧
      evaluateHOLFiniteState (setVarHOLFinite name w {bodyPost with locals := s.locals})
        continuation = (some (.returned retVal), inner) := by
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none s name shape function arguments continuation args] at hrun
    simp at hrun
  | some values =>
    rw [evaluateHOLFiniteState_decCall_total, args] at hrun
    dsimp only at hrun
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at hrun; simp at hrun
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      rw [lookup] at hrun
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · rename_i hclk
        have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at hrun remaining
          have fixed : fixClockHOLFinite (callEntryStateHOLFinite s callee) (r1, bodyPost) =
              (r1, bodyPost) := by
            simp [fixClockHOLFinite, Nat.not_lt.mpr remaining]
          rw [fixed] at hrun
          dsimp only at hrun
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at hrun; done)
            | skip
          simp only [] at hrun
          split at hrun
          · obtain ⟨e, _⟩ := Prod.mk.inj hrun
            exact ⟨values, body, callee, returnShape, w, bodyPost, _, hclk, rfl, lookup, bodyRun,
              Prod.ext e rfl⟩
          · simp at hrun

private theorem tailCall_returned_inv {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {function : MlS}
    {arguments : List (ExpHOL 64)} {retVal : ValueHOL 64}
    (hrun : evaluateHOLFiniteState s (.call none function arguments) =
      (some (.returned retVal), post)) :
    ∃ (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (bodyPost : PanSemStateFiniteExact 64 F),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
        some values ∧
      lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned retVal), bodyPost) := by
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      arguments with
  | none =>
    rw [evaluateHOLFiniteState_call, args] at hrun
    simp at hrun
  | some values =>
    rw [evaluateHOLFiniteState_call, args] at hrun
    dsimp only at hrun
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at hrun; simp at hrun
    | some installed =>
      obtain ⟨body, callee, returnShape⟩ := installed
      rw [lookup] at hrun
      dsimp only at hrun
      split at hrun
      · simp at hrun
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk r1 bodyPost =>
          rw [bodyRun] at hrun
          rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
          all_goals first
            | (simp at hrun; done)
            | skip
          dsimp only at hrun
          split at hrun
          · simp only [Prod.mk.injEq, Option.some.injEq, PanSemResultExact.returned.injEq] at hrun
            obtain ⟨rfl, _⟩ := hrun
            exact ⟨values, body, callee, returnShape, bodyPost, rfl, lookup, bodyRun⟩
          · simp at hrun

private theorem u256_bit_length_body_returns_le256 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_bit_length) =
      (some (.returned retVal), post)) :
    WordBound 256 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_bit_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  have branchBound : ∀ {st stPost : PanSemStateFiniteExact 64 F} {nm : MlS} {arg : ExpHOL 64}
      {off : BitVec 64} {r : ValueHOL 64},
      st.code = originalRuntimeCode →
      off.toNat ≤ 192 →
      evaluateHOLFiniteState st
        (.decCall nm .one (ofString "bit_length64") [arg]
          (.return (.op .add [.const off, .var .local nm]))) =
        (some (.returned r), stPost) →
      WordBound 256 r := by
    intro st stPost nm arg off r hstCode hoff hbr
    obtain ⟨vs, b, loc, rs, w, bPost, inner, _, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hbr
    have hbEq := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "bit_length64")
      _ _ b _ rs vs loc (by rw [hstCode]; exact lookup_bit_length64) hlk
    subst hbEq
    obtain ⟨nw, rfl, hnwle⟩ := bit_length64_body_returns_le64 _ bPost w hbRun
    have hnm : (setVarHOLFinite nm (.val (.word nw)) {bPost with locals := st.locals}).locals.lookup
        nm = some (.val (.word nw)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hretEq : evaluateHOLFiniteState
        (setVarHOLFinite nm (.val (.word nw)) {bPost with locals := st.locals})
        (.return (.op .add [.const off, .var .local nm])) =
        (some (.returned (.val (.word (off + nw)))),
          (setVarHOLFinite nm (.val (.word nw))
            {bPost with locals := st.locals}).emptyLocalsHOLFinite) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hnm,
        wordOpHOL, wordOp, valueIsWord, valueWord, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hretEq] at hcont
    cases hcont
    refine ⟨off + nw, rfl, ?_⟩
    have h264 : 2 ^ 64 = 18446744073709551616 := rfl
    rw [BitVec.toNat_add_of_lt (by omega)]
    omega
  have stepSeqIte : ∀ {st stPost : PanSemStateFiniteExact 64 F} {cond : ExpHOL 64}
      {nm : MlS} {arg : ExpHOL 64} {off : BitVec 64} {tail : ProgHOL 64},
      st.code = originalRuntimeCode →
      off.toNat ≤ 192 →
      evaluateHOLFiniteState st
        (.seq (.ite cond (.decCall nm .one (ofString "bit_length64") [arg]
            (.return (.op .add [.const off, .var .local nm]))) .skip) tail) =
        (some (.returned retVal), stPost) →
      WordBound 256 retVal ∨ evaluateHOLFiniteState st tail = (some (.returned retVal), stPost) := by
    intro st stPost cond nm arg off tail hstCode hoff hseq
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hseq
    split at hseq
    · split at hseq
      · rw [evaluateHOLFiniteState_skip] at hseq
        exact Or.inr hseq
      · cases hcall : evaluateHOLFiniteState st
            (.decCall nm .one (ofString "bit_length64") [arg]
              (.return (.op .add [.const off, .var .local nm]))) with
        | mk r1 mid =>
          rw [hcall] at hseq
          cases r1 with
          | none =>
            obtain ⟨_, _, _, _, _, hcont, _⟩ :=
              decCall_flowing (Or.inl rfl) hcall
            rw [evaluateHOLFiniteState_return] at hcont
            split at hcont <;> first | simp at hcont | (split at hcont <;> simp at hcont)
          | some r1v =>
            dsimp only at hseq
            rw [hseq] at hcall
            exact Or.inl (branchBound hstCode hoff hcall)
    · simp at hseq
  rcases stepSeqIte hcode (by decide) hrun with h | hrun2
  · exact h
  · rcases stepSeqIte hcode (by decide) hrun2 with h | hrun3
    · exact h
    · rcases stepSeqIte hcode (by decide) hrun3 with h | hrun4
      · exact h
      · obtain ⟨vs, b, loc, rs, bPost, _, hlk, hbRun⟩ := tailCall_returned_inv hrun4
        have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "bit_length64")
          _ _ b _ rs vs loc (by rw [hcode]; exact lookup_bit_length64) hlk
        subst hbEq
        obtain ⟨nw, rfl, hnwle⟩ := bit_length64_body_returns_le64 _ bPost retVal hbRun
        exact ⟨nw, rfl, by omega⟩

private theorem u256_byte_length_body_returns_le32 {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (hrun : evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_u256_byte_length) =
      (some (.returned retVal), post)) :
    WordBound 32 retVal := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
    at hrun
  obtain ⟨vs, b, loc, rs, w, bPost, inner, _, _, hlk, hbRun, hcont⟩ := decCall_returned_inv hrun
  have hbEq := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_bit_length")
    _ _ b _ rs vs loc (by rw [hcode]; exact lookup_u256_bit_length) hlk
  subst hbEq
  obtain ⟨nw, rfl, hnwle⟩ :=
    u256_bit_length_body_returns_le256 (callEntryStateHOLFinite state loc) bPost w hcode hbRun
  have hn : (setVarHOLFinite (ofString "n") (.val (.word nw))
      {bPost with locals := state.locals}).locals.lookup (ofString "n") =
      some (.val (.word nw)) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnotge : ¬ (64 ≤ (3#64 : BitVec 64).toNat) := by decide
  have hretEq : evaluateHOLFiniteState
      (setVarHOLFinite (ofString "n") (.val (.word nw)) {bPost with locals := state.locals})
      (.return (.shift .lsr (.op .add [.var .local (ofString "n"), .const 7#64]) (.const 3#64))) =
      (some (.returned (.val (.word ((nw + 7#64) >>> (3#64).toNat)))),
        (setVarHOLFinite (ofString "n") (.val (.word nw))
          {bPost with locals := state.locals}).emptyLocalsHOLFinite) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp,
      valueIsWord, valueWord, wordShiftHOL, hnotge, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hretEq] at hcont
  cases hcont
  refine ⟨(nw + 7#64) >>> (3#64).toNat, rfl, ?_⟩
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h264 : 2 ^ 64 = 18446744073709551616 := rfl
  have h7 : (7#64 : BitVec 64).toNat = 7 := rfl
  have hadd : (nw + 7#64).toNat = nw.toNat + 7 := by
    rw [BitVec.toNat_add_of_lt (by omega)]
    exact congrArg (nw.toNat + ·) h7
  rw [hadd]
  change (nw.toNat + 7) / 8 ≤ 32
  omega

private def noReturnProg : ProgHOL 64 → Bool
  | .return _ => false
  | .seq first second => noReturnProg first && noReturnProg second
  | .ite _ yes no => noReturnProg yes && noReturnProg no
  | .dec _ _ _ body => noReturnProg body
  | .decCall _ _ _ _ cont => noReturnProg cont
  | .while _ body => noReturnProg body
  | .skip | .assign _ _ _ | .store _ _ | .storeByte _ _
  | .break | .continue | .raise _ _ | .annot _ _ => true
  | _ => false

private theorem evaluate_noReturnProg {F : Type} (p : ProgHOL 64) (hp : noReturnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases hshape : p with
  | «return» _ => simp [hshape, noReturnProg] at hp
  | seq a b =>
    have hab : noReturnProg a = true ∧ noReturnProg b = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    have hrem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnProg a hab.1 s v
    cases hra : evaluateHOLFiniteState s a with
    | mk r1 mid =>
      rw [hra] at ha hrem
      cases r1 with
      | none => exact evaluate_noReturnProg b hab.2 mid v
      | some _ => exact ha
  | ite c yes no =>
    have hy : noReturnProg yes = true ∧ noReturnProg no = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnProg no hy.2 s v
      · exact evaluate_noReturnProg yes hy.1 s v
    · simp
  | dec nm sh init body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noReturnProg body hb _ v
      · simp
  | decCall nm sh fn args cont =>
    have hc : noReturnProg cont = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rcases hpair : evaluateHOLFiniteState s (.decCall nm sh fn args cont) with ⟨res, post⟩
    rw [hpair] at hret
    dsimp only at hret
    subst hret
    obtain ⟨_, bbody, blocals, _, rv, bpost, inner, hclk, _, _, hb, hcont⟩ := decCall_returned_inv hpair
    have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s blocals) bbody
    rw [hb] at hrem
    have hclk_lt : (setVarHOLFinite nm rv {bpost with locals := s.locals}).clock < s.clock := by
      change bpost.clock < s.clock
      change bpost.clock ≤ s.clock - 1 at hrem
      omega
    have hno := evaluate_noReturnProg cont hc (setVarHOLFinite nm rv {bpost with locals := s.locals}) v
    rw [hcont] at hno
    exact hno rfl
  | «while» cond body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rw [evaluateHOLFiniteState_while_total] at hret
    split at hret
    · split at hret
      · split at hret
        · simp at hret
        · dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          cases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r1 mid =>
            rw [hbr] at hret hrem
            have hclk_lt : mid.clock < s.clock := by
              change mid.clock ≤ s.clock - 1 at hrem
              omega
            cases r1 with
            | none => exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
            | some r1' =>
              cases r1' with
              | «continue» =>
                exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
              | «break» => simp at hret
              | returned rv =>
                have hno := evaluate_noReturnProg body hb (decClockHOLFinite s) rv
                rw [hbr] at hno
                exact hno rfl
              | _ => simp at hret
      · simp at hret
    · simp at hret
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot _ _ => simp [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | assign _ _ _ => rw [evaluateHOLFiniteState_assign]; repeat' first | split | simp
  | store _ _ =>
    rcases (PanRunBounded.evaluate_store_control_frame s _ _).1 with h | h <;> rw [h] <;> simp
  | storeByte _ _ =>
    rcases (PanRunBounded.evaluate_storeByte_control_frame s _ _).1 with h | h <;> rw [h] <;> simp
  | _ => simp [hshape, noReturnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

/-- `u256_to_be_min` (AST line 2302): returns its byte count, at most 32 (value contract). -/
theorem rv_u256_to_be_min :
    RetLe_u256 (fun _ => 32) (ofString "u256_to_be_min") := by
  refine ⟨_, (sourceFunctionEntry Guest.Software.guestFn_u256_to_be_min).2.2.1, _, lookup_u256_to_be_min, ?_⟩
  intro F state hcode _ _ _ v hv
  rcases hpair : evaluateHOLFiniteState state
      (sourceFunctionEntry Guest.Software.guestFn_u256_to_be_min).2.2.1 with ⟨res, post⟩
  rw [hpair] at hv
  dsimp only at hv
  subst hv
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map] at hpair
  obtain ⟨vs, bbody, blocals, brs, lenv, bpost, inner, _, _, hlookup, hb, hdec⟩ :=
    decCall_returned_inv hpair
  have hbody := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "u256_byte_length")
    _ _ bbody _ brs vs blocals (by rw [hcode]; exact lookup_u256_byte_length) hlookup
  subst hbody
  obtain ⟨lenw, rfl, hlen_le⟩ :=
    u256_byte_length_body_returns_le32 (callEntryStateHOLFinite state blocals) bpost lenv hcode hb
  let s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) {bpost with locals := state.locals}
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_dec_total] at hdec
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at hdec
  let s1i := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
  have hs1i_len : s1i.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
    have hne : ofString "i" ≠ ofString "len" := by decide
    simp [s1i, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hs1_len]
  let wprog : ProgHOL 64 :=
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
      (.dec (ofString "pos") .one
        (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
        (.decCall (ofString "l") .one (ofString "u256_limb")
          [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
          (.seq
            (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
              (.op .and
                [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul
                      [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                  .const 255#64]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1#64])))))
  have hseq : (evaluateHOLFiniteState s1i (.seq wprog (.return (.var .local (ofString "len"))))).1 =
      some (.returned v) := (Prod.mk.inj hdec).1
  rw [evaluateHOLFiniteState_seq_line780] at hseq
  have hno_ret := evaluate_noReturnProg wprog (by decide) s1i
  have hpreserve_raw := PanRunBounded.evaluate_avoidsLocal_flowing (ofString "len") wprog (by decide) s1i
  cases hwh : evaluateHOLFiniteState s1i wprog with
  | mk rw sw =>
    rw [hwh] at hseq hno_ret hpreserve_raw
    dsimp only at hseq hno_ret hpreserve_raw
    cases rw with
    | some rw' =>
      cases rw' with
      | returned rv => exact False.elim (hno_ret rv rfl)
      | _ => simp at hseq
    | none =>
      dsimp only at hseq
      have hsw_len : sw.locals.lookup (ofString "len") = some (.val (.word lenw)) :=
        (hpreserve_raw (Or.inl rfl)).trans hs1i_len
      rw [evaluateHOLFiniteState_return] at hseq
      simp [evalHOLExact, lookupKvarHOLExact, hsw_len, shapeOfHOLExact,
        sizeOfShapeWithContextHOL] at hseq
      exact ⟨lenw, hseq.symm, hlen_le⟩

end InitECandidate.Solver.Wave8Contracts.M27
