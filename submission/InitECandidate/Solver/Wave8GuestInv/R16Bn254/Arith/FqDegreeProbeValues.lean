import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroBytesCalls

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem fqDegreeProbe_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base i : BitVec 64)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "a"),
        .panop .mul [.var .local (ofString "i"), .const 32]], .const 32] =
      some [.val (.word (base + i * 32)), .val (.word 32)] := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hi,
    wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]

theorem fqDegreeProbe_returned_nonzero {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base i : BitVec 64) (coefficient : Limbs256) (ret : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (halign : (base + i * 32).toNat % 8 = 0)
    (hbound : (base + i * 32).toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 s.memaddrs (base + i * 32))
    (hm : MemoryU256 s.memory (base + i * 32) coefficient)
    (hr : evaluateHOLFiniteState s fqDegreeProbe = (some (.returned ret), post)) :
    coefficient.toNat ≠ 0 := by
  unfold fqDegreeProbe at hr
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, hclock, hrun, hshape, hlocals, hcode, hcont, hpost⟩ := arith_decCall_returned hr
  have hv : values = [.val (.word (base + i * 32)), .val (.word 32)] :=
    Option.some.inj (hargs.symm.trans (fqDegreeProbe_arguments s base i ha hi))
  subst values
  have hz := zeroBytes_u256_callee_returned s bpost (base+i*32) coefficient value body callee rs
    hc halign hbound hd hm hlk hrun
  have hzl : resumed.locals.lookup (ofString "z") =
      some (.val (.word (if coefficient.toNat = 0 then 1 else 0))) := by
    rw [hlocals, hz]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  intro hzero
  rw [evaluateHOLFiniteState_ite] at hcont
  simp [evalHOLExact, hzl, hzero, Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_skip] at hcont

theorem fqDegreeProbe_none_zero {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base i : BitVec 64) (coefficient : Limbs256)
    (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (halign : (base + i * 32).toNat % 8 = 0)
    (hbound : (base + i * 32).toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 s.memaddrs (base + i * 32))
    (hm : MemoryU256 s.memory (base + i * 32) coefficient)
    (hr : evaluateHOLFiniteState s fqDegreeProbe = (none, post)) : coefficient.toNat = 0 := by
  unfold fqDegreeProbe at hr
  obtain ⟨values, body, callee, rs, value, bpost, resumed, inner,
    hargs, hlk, hclock, hrun, hshape, hlocals, hcode, hcont, hpost⟩ := arith_decCall_none hr
  have hv : values = [.val (.word (base + i * 32)), .val (.word 32)] :=
    Option.some.inj (hargs.symm.trans (fqDegreeProbe_arguments s base i ha hi))
  subst values
  have hz := zeroBytes_u256_callee_returned s bpost (base+i*32) coefficient value body callee rs
    hc halign hbound hd hm hlk hrun
  have hzl : resumed.locals.lookup (ofString "z") =
      some (.val (.word (if coefficient.toNat = 0 then 1 else 0))) := by
    rw [hlocals, hz]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hil : resumed.locals.lookup (ofString "i") = some (.val (.word i)) := by
    rw [hlocals]
    simpa [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "z" ≠ ofString "i" by decide] using hi
  by_contra hzero
  rw [evaluateHOLFiniteState_ite] at hcont
  simp [evalHOLExact, hzl, hil, hzero, Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hcont

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
