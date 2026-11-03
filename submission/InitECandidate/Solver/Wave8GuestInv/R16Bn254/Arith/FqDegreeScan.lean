import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeBodyZero

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def DegreeScanResult (coefficients : Nat → Limbs256) (n : Nat)
    (result : Option (PanSemResultExact 64)) : Prop :=
  (result = none → ∀ j, j < n → (coefficients j).toNat = 0) ∧
  (∀ ret, result = some (.returned ret) → ∃ j : Nat,
    j < n ∧ ret = .val (.word (BitVec.ofNat 64 j)) ∧ (coefficients j).toNat ≠ 0 ∧
    ∀ k, j < k → k < n → (coefficients k).toNat = 0)

/-- Complete source degree-loop invariant: fallthrough means all scanned
coefficients vanish; a return identifies the greatest nonzero scanned index. -/
theorem fqDegreeLoop_scan {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (n : Nat)
    (hn : n ≤ 13) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 n))))
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients) :
    DegreeScanResult coefficients n (evaluateHOLFiniteState s fqDegreeLoop).1 := by
  rw [fqDegreeLoop, evaluateHOLFiniteState_while_fixClockRewrite]
  by_cases hn0 : n = 0
  · subst n
    simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, DegreeScanResult]
  · have hpos : 0 < n := by omega
    have hnlt : n < 18446744073709551616 := by omega
    have hg : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.const 0) (.var .local (ofString "i"))) = some (.val (.word 1)) := by
      simp [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
        Nat.mod_eq_of_lt hnlt, hpos]
    rw [hg]
    dsimp only
    rw [if_pos (show (1 : BitVec 64) ≠ 0 by decide)]
    by_cases hz : s.clock = 0
    · simp [hz, DegreeScanResult]
    · rw [if_neg hz]
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) fqDegreeBody with ⟨res,middle⟩
      cases res with
      | none =>
          dsimp only
          have hi' := fqDegreeBody_flow_lookup (decClockHOLFinite s) (BitVec.ofNat 64 n)
            hi (Or.inl (by rw [hbody]))
          rw [hbody, degreeIndex_decrement n hpos hn] at hi'
          have hbase := evaluate_avoidsLocal_flowing (ofString "a") fqDegreeBody (by decide)
            (decClockHOLFinite s) (Or.inl (by rw [hbody]))
          rw [hbody] at hbase
          have ha' : middle.locals.lookup (ofString "a") = some (.val (.word base)) := hbase.trans ha
          have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite s) fqDegreeBody
          rw [hbody] at hmeta
          have hc' : middle.code = originalRuntimeCode := hmeta.1.trans hc
          have hdom : middle.memaddrs = s.memaddrs := hmeta.2.1
          have hmem := fqDegreeBody_memoryPure (decClockHOLFinite s) hc
          rw [hbody] at hmem
          change middle.memory = s.memory at hmem
          have hd' : DomainPolynomial middle.memaddrs base := by rw [hdom]; exact hd
          have hm' : MemoryPolynomial middle.memory base coefficients := by rw [hmem]; exact hm
          have hzero := fqDegreeBody_zero (decClockHOLFinite s) middle base coefficients n
            hpos hn hc ha hi halign hbound hd hm hbody
          have ih := fqDegreeLoop_scan middle base coefficients (n-1) (by omega)
            hc' ha' hi' halign hbound hd' hm'
          constructor
          · intro hnone j hj
            by_cases he : j = n-1
            · simpa only [he] using hzero
            · exact ih.1 hnone j (by omega)
          · intro ret hret
            obtain ⟨j,hj,he,hne,habove⟩ := ih.2 ret hret
            refine ⟨j, by omega, he, hne, ?_⟩
            intro k hjk hkn
            by_cases he : k = n-1
            · simpa only [he] using hzero
            · exact habove k hjk (by omega)
      | some result =>
          cases result with
          | «continue» =>
              have hno := evaluate_noTopContinue fqDegreeBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak fqDegreeBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | returned value =>
              have hv := fqDegreeBody_returned (s := decClockHOLFinite s) (BitVec.ofNat 64 n) hi hbody
              rw [degreeIndex_decrement n hpos hn] at hv
              have hne := fqDegreeBody_nonzero (decClockHOLFinite s) middle base coefficients n value
                hpos hn hc ha hi halign hbound hd hm hbody
              constructor
              · intro h; cases h
              · intro ret he
                have hev : value = ret := by simpa using he
                exact ⟨n-1, by omega, hev.symm.trans hv, hne, by intro k hk hkn; omega⟩
          | _ => simp [DegreeScanResult]
termination_by n
decreasing_by omega

end InitECandidate.Solver.Wave8GuestInv.Arith
