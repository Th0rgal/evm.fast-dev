import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemcpyAlignedSource

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

theorem memcpyAlignedBody_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src index : BitVec 64) (v : Limbs256)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (hd : DomainU256 s.memaddrs (dst+index))
    (hs : DomainU256 s.memaddrs (src+index))
    (hm : MemoryU256 s.memory (src+index) v)
    (hsep : ∀ a ∈ u256Addresses (dst+index), a ∉ u256Addresses (src+index)) :
    evaluateHOLFiniteState s memcpyAlignedBody =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index+32)))
        {s with memory := writeU256 s.memory (dst+index) v}) := by
  let s1 : PanSemStateFiniteExact 64 F := {s with memory := writeMemoryWord s.memory (dst+index) v.l0}
  have hm1 : MemoryU256 s1.memory (src+index) v :=
    writeMemoryWord_preserves s.memory (dst+index) (src+index) v.l0 v
      (hsep _ (by simp [u256Addresses])) hm
  have he0 : evaluateHOLFiniteState s (memcpyWord 0) = (none,s1) := by
    simpa only [s1, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      memcpyWord_eval s dst src index v.l0 0 hdst hsrc hi (by simpa using hd.1) (by simpa using hs.1) (by simpa using hm.1)
  let s2 : PanSemStateFiniteExact 64 F := {s1 with memory := writeMemoryWord s1.memory (dst+index+8) v.l1}
  have hm2 : MemoryU256 s2.memory (src+index) v :=
    writeMemoryWord_preserves s1.memory (dst+index+8) (src+index) v.l1 v
      (hsep _ (by simp [u256Addresses])) hm1
  have he1 : evaluateHOLFiniteState s1 (memcpyWord 8) = (none,s2) := by
    simpa only [s1,s2, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      memcpyWord_eval s1 dst src index v.l1 8 hdst hsrc hi hd.2.1 hs.2.1 hm1.2.1
  let s3 : PanSemStateFiniteExact 64 F := {s2 with memory := writeMemoryWord s2.memory (dst+index+16) v.l2}
  have hm3 : MemoryU256 s3.memory (src+index) v :=
    writeMemoryWord_preserves s2.memory (dst+index+16) (src+index) v.l2 v
      (hsep _ (by simp [u256Addresses])) hm2
  have he2 : evaluateHOLFiniteState s2 (memcpyWord 16) = (none,s3) := by
    simpa only [s1,s2,s3, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      memcpyWord_eval s2 dst src index v.l2 16 hdst hsrc hi hd.2.2.1 hs.2.2.1 hm2.2.2.1
  let s4 : PanSemStateFiniteExact 64 F := {s3 with memory := writeMemoryWord s3.memory (dst+index+24) v.l3}
  have he3 : evaluateHOLFiniteState s3 (memcpyWord 24) = (none,s4) := by
    simpa only [s1,s2,s3,s4, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      memcpyWord_eval s3 dst src index v.l3 24 hdst hsrc hi hd.2.2.2 hs.2.2.2 hm3.2.2.2
  have hinc : evaluateHOLFiniteState s4 memcpyIncrement =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index+32))) s4) := by
    simp [memcpyIncrement,evaluateHOLFiniteState_assign,polyDivVar,
      evalHOLExact,evalListHOLExact,hi,s4,s3,s2,s1,wordOpHOL,wordOp,valueIsWord,valueWord,
      lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeEqHOL,shapeOfHOLExact]
  rw [memcpyAlignedBody,evaluateHOLFiniteState_seq_line780,he0]
  simp only [evaluateHOLFiniteState_seq_line780,he1,he2,he3,hinc]
  rfl

end InitECandidate.Solver.Wave8GuestInv.Arith
