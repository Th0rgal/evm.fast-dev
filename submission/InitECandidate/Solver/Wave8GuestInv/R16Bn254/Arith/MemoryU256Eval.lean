import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The four concrete machine addresses of a coefficient. -/
def u256Addresses (address : BitVec 64) : List (BitVec 64) :=
  [address, address + 8, address + 16, address + 24]

theorem writeU256_frame (memory : BitVec 64 → HolWordLab 64) (address x : BitVec 64)
    (value : Limbs256) (outside : x ∉ u256Addresses address) :
    writeU256 memory address value x = memory x := by
  simp only [u256Addresses, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  simp only [writeU256, if_neg outside.1, if_neg outside.2.1,
    if_neg outside.2.2.1, if_neg outside.2.2.2]

theorem writeU256_preserves (memory : BitVec 64 → HolWordLab 64) (address other : BitVec 64)
    (value old : Limbs256)
    (disjoint : ∀ x ∈ u256Addresses other, x ∉ u256Addresses address)
    (hv : MemoryU256 memory other old) :
    MemoryU256 (writeU256 memory address value) other old := by
  rcases hv with ⟨h0,h1,h2,h3⟩
  refine ⟨?_,?_,?_,?_⟩
  all_goals rw [writeU256_frame memory address _ value (disjoint _ (by simp [u256Addresses]))]
  all_goals assumption

theorem eval_load_u256 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) (address : BitVec 64) (value : Limbs256)
    (he : arithEval s expression = some (.val (.word address)))
    (hd : DomainU256 s.memaddrs address) (hv : MemoryU256 s.memory address value) :
    arithEval s (.load (.comb [.one,.one,.one,.one]) expression) = some value.toValue := by
  classical
  simp only [arithEval, evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL,
    Bool.true_and, ↓reduceIte]
  change evalHOLExact s.toExact expression = _ at he
  rw [he]
  exact memLoad_u256 s.memory address value s.memaddrs s.structs hd hv

theorem eval_store_u256 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (destination source : ExpHOL 64) (address : BitVec 64) (value : Limbs256)
    (ha : arithEval s destination = some (.val (.word address)))
    (hv : arithEval s source = some value.toValue)
    (hd : DomainU256 s.memaddrs address) :
    evaluateHOLFiniteState s (.store destination source) =
      (none, {s with memory := writeU256 s.memory address value}) := by
  classical
  rw [evaluateHOLFiniteState_store]
  change evalHOLExact s.toExact destination = _ at ha
  change evalHOLExact s.toExact source = _ at hv
  rw [ha, hv]
  dsimp only
  rw [memStore_u256 s.memory address value s.memaddrs hd]

end InitECandidate.Solver.Wave8GuestInv.Arith
