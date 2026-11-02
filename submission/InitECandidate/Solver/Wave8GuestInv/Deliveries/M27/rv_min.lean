import InitECandidate.Solver.Wave8GuestInv.MemoryViews

/-! Value contract `rv_min` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews`.
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
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
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
def RetLe (B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat) (fname : MlS) : Prop :=
  FunSpec GuestInv (fun s r _ => ∀ v, r = some (.returned v) →
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ B s) fname

theorem lookup_min :
    originalRuntimeCode.lookup (ofString "min") =
      some ((sourceFunctionEntry Guest.Software.guestFn_min).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

theorem min_body_ret {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s
      (sourceFunctionEntry Guest.Software.guestFn_min).2.2.1).1 = some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ min (locN s "a") (locN s "b") := by
  have hb : (sourceFunctionEntry Guest.Software.guestFn_min).2.2.1 =
      .seq (.ite (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b")))
        (.return (.var .local (ofString "a"))) .skip)
        (.return (.var .local (ofString "b"))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases ha : s.locals.lookup (ofString "a") with _ | va
  · simp [evalHOLExact, ha] at hret
  · rcases va with ⟨⟨wa⟩⟩ | fs | ⟨nm, fs⟩
    · rcases hbl : s.locals.lookup (ofString "b") with _ | vb
      · simp [evalHOLExact, ha, hbl] at hret
      · rcases vb with ⟨⟨wb⟩⟩ | fs | ⟨nm, fs⟩
        · have hev : @evalHOLExact 64 F _ s.toExact
              (fun x => Classical.propDecidable (s.memaddrs x))
              (.cmp .lower (.var .local (ofString "a")) (.var .local (ofString "b"))) =
              some (.val (.word (if wa.toNat < wb.toNat then 1 else 0))) := by
            simp [evalHOLExact, ha, hbl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
              decide_eq_true_eq]
          rw [hev] at hret
          have hla : locN s "a" = wa.toNat := by simp [locN, ha]
          have hlb : locN s "b" = wb.toNat := by simp [locN, hbl]
          rw [hla, hlb]
          by_cases hlt : wa.toNat < wb.toNat
          · simp [hlt, show (1 : BitVec 64) ≠ 0 by decide,
              evaluateHOLFiniteState_return, evalHOLExact, lookupKvarHOLExact, ha,
              shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            exact ⟨wa, hret.symm, by omega⟩
          · simp [hlt, evaluateHOLFiniteState_skip,
              evaluateHOLFiniteState_return, evalHOLExact, lookupKvarHOLExact, hbl,
              shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            exact ⟨wb, hret.symm, by omega⟩
        · simp [evalHOLExact, ha, hbl] at hret
        · simp [evalHOLExact, ha, hbl] at hret
    · simp [evalHOLExact, ha] at hret
    · simp [evalHOLExact, ha] at hret

/-- `min` (AST line 667): returns at most `a` (value contract). -/
theorem rv_min :
    RetLe (fun s => locN s "a") (ofString "min") := by
  refine ⟨_, _, _, lookup_min, ?_⟩
  intro F s _ _ _ _ v hv
  obtain ⟨w, rfl, hle⟩ := min_body_ret s v hv
  exact ⟨w, rfl, Nat.le_trans hle (Nat.min_le_left _ _)⟩

end InitECandidate.Solver.Wave8Contracts.M27
