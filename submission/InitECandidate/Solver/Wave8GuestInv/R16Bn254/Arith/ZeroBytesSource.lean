import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryByteZero
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256MemoryPure

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def zeroBytesLoad : ExpHOL 64 :=
  .loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
def zeroBytesIncrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])
def zeroBytesBody : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual zeroBytesLoad (.const 0)) (.return (.const 0)) .skip)
    zeroBytesIncrement
def zeroBytesLoop : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) zeroBytesBody

theorem zeroBytes_source_eq : arithSourceBody Guest.Software.guestFn_is_zero_bytes =
    .dec (ofString "i") .one (.const 0) (.seq zeroBytesLoop (.return (.const 1))) := rfl

theorem zeroBytes_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_is_zero_bytes) :=
  memoryPure_noCalls _ (by decide)

theorem zeroBytes_increment {F : Type} (s : PanSemStateFiniteExact 64 F) (i : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    evaluateHOLFiniteState s zeroBytesIncrement =
      (none, setVarHOLFinite (ofString "i") (.val (.word (i + 1))) s) := by
  simp [zeroBytesIncrement, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact,
    hi, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]

theorem zeroBytes_body {F : Type} (s : PanSemStateFiniteExact 64 F) (i w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hr : arithEval s zeroBytesLoad = some (.val (.word w))) :
    evaluateHOLFiniteState s zeroBytesBody =
      if w = 0 then (none, setVarHOLFinite (ofString "i") (.val (.word (i + 1))) s)
      else (some (.returned (.val (.word 0))), emptyLocalsHOLFinite s) := by
  classical
  unfold zeroBytesBody
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  change evalHOLExact s.toExact zeroBytesLoad = _ at hr
  simp only [evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hz : w = 0
  · simp [hz, evaluateHOLFiniteState_skip, zeroBytes_increment s i hi]
  · change w ≠ 0#64 at hz
    simp [hz, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
      sizeOfShapeWithContextHOL]

theorem zeroBytes_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (i : Nat) (byte : UInt8)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hr : @panMemLoadByteHOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be (base + BitVec.ofNat 64 i) = some byte) :
    arithEval s zeroBytesLoad = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  simp [arithEval, zeroBytesLoad, evalHOLExact, evalListHOLExact, hp, hi,
    wordOpHOL, wordOp, valueIsWord, valueWord, hr]

end InitECandidate.Solver.Wave8GuestInv.Arith
