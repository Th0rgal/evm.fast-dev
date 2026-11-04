import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroBytesSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def ZeroByteSuffix (bytes : Nat → UInt8) (start : Nat) : Prop :=
  ∀ j, start ≤ j → j < 32 → bytes j = 0

def ZeroByteScanResult (bytes : Nat → UInt8) (start : Nat)
    (result : Option (PanSemResultExact 64)) : Prop :=
  (result = none → ZeroByteSuffix bytes start) ∧
  (∀ ret, result = some (.returned ret) →
    ret = .val (.word 0) ∧ ¬ ZeroByteSuffix bytes start)

def ZeroBytes32Reads {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (bytes : Nat → UInt8) : Prop :=
  ∀ j, j < 32 → @panMemLoadByteHOL 64 _ s.memory s.memaddrs
    (fun a => Classical.propDecidable (s.memaddrs a)) s.be (base + BitVec.ofNat 64 j) = some (bytes j)

theorem zeroByteSuffix_step (bytes : Nat → UInt8) (i : Nat) (hz : bytes i = 0) :
    ZeroByteSuffix bytes i ↔ ZeroByteSuffix bytes (i + 1) := by
  constructor
  · intro h j hj hn; exact h j (by omega) hn
  · intro h j hj hn
    by_cases he : j = i
    · simpa [he] using hz
    · exact h j (by omega) hn

theorem zeroBytes_guard {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Nat)
    (hb : i ≤ 32)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 32))) :
    arithEval s (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word (if i < 32 then 1 else 0))) := by
  have hib : i < 18446744073709551616 := by omega
  simp [arithEval, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL,
    BitVec.lt_def, Nat.mod_eq_of_lt hib]

theorem uint8_widen_zero_iff (byte : UInt8) : BitVec.ofNat 64 byte.toNat = 0 ↔ byte = 0 := by
  have hb := byte.toNat_lt_size
  constructor
  · intro h
    apply UInt8.toNat_inj.mp
    have hh := congrArg BitVec.toNat h
    change byte.toNat % 2 ^ 64 = 0 at hh
    change byte.toNat = 0
    change byte.toNat < 256 at hb
    omega
  · intro h; simp [h]

theorem zeroBytesLoop_spec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (bytes : Nat → UInt8) (i : Nat) (hb : i ≤ 32)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 32)))
    (hreads : ZeroBytes32Reads s base bytes) :
    ZeroByteScanResult bytes i (evaluateHOLFiniteState s zeroBytesLoop).1 := by
  rw [zeroBytesLoop, evaluateHOLFiniteState_while_fixClockRewrite]
  have hg := zeroBytes_guard s i hb hi hn
  change evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ = _ at hg
  rw [hg]
  dsimp only
  by_cases hlt : i < 32
  · rw [if_pos hlt, if_pos (show (1 : BitVec 64) ≠ 0 by decide)]
    by_cases hclock : s.clock = 0
    · simp [hclock, ZeroByteScanResult]
    · rw [if_neg hclock]
      have hload := zeroBytes_load (decClockHOLFinite s) base i (bytes i) hp hi (hreads i hlt)
      rw [zeroBytes_body (decClockHOLFinite s) (BitVec.ofNat 64 i)
        (BitVec.ofNat 64 (bytes i).toNat) hi hload]
      by_cases hz : bytes i = 0
      · rw [if_pos ((uint8_widen_zero_iff (bytes i)).mpr hz)]
        dsimp only
        let next := setVarHOLFinite (ofString "i")
          (.val (.word (BitVec.ofNat 64 i + 1))) (decClockHOLFinite s)
        have hp' : next.locals.lookup (ofString "p") = some (.val (.word base)) := by
          simpa [next, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "p" by decide] using hp
        have hn' : next.locals.lookup (ofString "n") = some (.val (.word 32)) := by
          simpa [next, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "n" by decide] using hn
        have hi' : next.locals.lookup (ofString "i") =
            some (.val (.word (BitVec.ofNat 64 (i + 1)))) := by
          simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, BitVec.ofNat_add]
        have ih := zeroBytesLoop_spec next base bytes (i + 1) (by omega) hp' hi' hn' hreads
        change ZeroByteScanResult bytes i (evaluateHOLFiniteState next zeroBytesLoop).1
        simpa only [ZeroByteScanResult, zeroByteSuffix_step bytes i hz] using ih
      · rw [if_neg (fun h => hz ((uint8_widen_zero_iff (bytes i)).mp h))]
        simp only [ZeroByteScanResult, reduceCtorEq, false_implies, Option.some.injEq,
          PanSemResultExact.returned.injEq, true_and]
        intro ret he
        refine ⟨he.symm, ?_⟩
        intro hall
        exact hz (hall i (by omega) hlt)
  · have he : i = 32 := by omega
    subst i
    simp [ZeroByteScanResult, ZeroByteSuffix]
    intro j hj hjlt
    omega
termination_by 32 - i
decreasing_by omega

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
