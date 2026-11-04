import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256Eval

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def writeMemoryWord (memory : BitVec 64 → HolWordLab 64) (address word : BitVec 64) :
    BitVec 64 → HolWordLab 64 := fun x => if x = address then .word word else memory x

theorem eval_load_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (address word : BitVec 64)
    (he : arithEval s expression = some (.val (.word address)))
    (hd : s.memaddrs address) (hm : s.memory address = .word word) :
    arithEval s (.load .one expression) = some (.val (.word word)) := by
  classical
  simp only [arithEval,evalHOLExact,isWfShapeExactHOL]
  change evalHOLExact s.toExact expression = _ at he
  rw [he]
  simp [memLoadHOLExact,hd,hm]

theorem eval_store_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination source : ExpHOL 64) (address word : BitVec 64)
    (ha : arithEval s destination = some (.val (.word address)))
    (hv : arithEval s source = some (.val (.word word))) (hd : s.memaddrs address) :
    evaluateHOLFiniteState s (.store destination source) =
      (none,{s with memory := writeMemoryWord s.memory address word}) := by
  classical
  rw [evaluateHOLFiniteState_store]
  change evalHOLExact s.toExact destination = _ at ha
  change evalHOLExact s.toExact source = _ at hv
  rw [ha,hv]
  simp [flattenHOL,panMemStoresHOL,panMemStoreHOL,hd]
  rfl

theorem writeMemoryWord_preserves (memory : BitVec 64 → HolWordLab 64) (address source word : BitVec 64)
    (value : Limbs256) (hout : address ∉ u256Addresses source) (hm : MemoryU256 memory source value) :
    MemoryU256 (writeMemoryWord memory address word) source value := by
  simp only [u256Addresses,List.mem_cons,List.not_mem_nil,or_false,not_or] at hout
  rcases hm with ⟨h0,h1,h2,h3⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [writeMemoryWord, if_neg (Ne.symm hout.1)] using h0
  · simpa only [writeMemoryWord, if_neg (Ne.symm hout.2.1)] using h1
  · simpa only [writeMemoryWord, if_neg (Ne.symm hout.2.2.1)] using h2
  · simpa only [writeMemoryWord, if_neg (Ne.symm hout.2.2.2)] using h3

theorem writeMemoryWord_four (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64) (v : Limbs256) :
    writeMemoryWord
      (writeMemoryWord (writeMemoryWord (writeMemoryWord memory address v.l0) (address+8) v.l1)
        (address+16) v.l2) (address+24) v.l3 = writeU256 memory address v := rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
