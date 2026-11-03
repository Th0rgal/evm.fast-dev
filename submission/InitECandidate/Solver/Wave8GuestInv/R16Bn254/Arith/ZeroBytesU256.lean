import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroBytesCorrect
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryByteU256

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual byte-scanning source function recognizes zero U256 values in
aligned, nonwrapping memory. The theorem supports both byte orders. -/
theorem zeroBytes_u256_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (value : Limbs256) (ret : ValueHOL 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word base)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 32)))
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 s.memaddrs base) (hm : MemoryU256 s.memory base value)
    (hr : evaluateHOLFiniteState s (arithSourceBody Guest.Software.guestFn_is_zero_bytes) =
      (some (.returned ret), post)) :
    ret = .val (.word (if value.toNat = 0 then 1 else 0)) := by
  classical
  let bytes := u256ByteAt value base s.be
  have hreads : ZeroBytes32Reads s base bytes := by
    intro j hj
    exact memByte_u256 s.memory s.memaddrs s.be base value ha hb hd hm j hj
  have hzero : (∀ j, j < 32 → bytes j = 0) ↔ value.toNat = 0 := by
    rw [← memByte_zero_iff_u256 s.memory s.memaddrs s.be base value ha hb hd hm]
    constructor
    · intro h j hj
      rw [hreads j hj, h j hj]
    · intro h j hj
      have hh := h j hj
      rw [hreads j hj] at hh
      exact Option.some.inj hh
  rcases zeroBytes32_returned s post base bytes ret hp hn hreads hr with
    ⟨he,hz⟩ | ⟨he,hz⟩
  · rw [if_pos (hzero.mp hz)]
    exact he
  · rw [if_neg (fun h => hz (hzero.mpr h))]
    exact he

end InitECandidate.Solver.Wave8GuestInv.Arith
