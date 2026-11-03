import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.ZeroBytesU256
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

theorem arith_lookup_is_zero_bytes :
    originalRuntimeCode.lookup (ofString "is_zero_bytes") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        arithSourceBody Guest.Software.guestFn_is_zero_bytes, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 19 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_zero_bytes) rfl

theorem zeroBytes_function_memoryPure : MemoryPureFunction (ofString "is_zero_bytes") :=
  memoryPureFunction_of_installed _ _ _ _ arith_lookup_is_zero_bytes zeroBytes_memoryPure

theorem fqDegree_memoryPure : MemoryPure (arithSourceBody Guest.Software.guestFn_fq_poly_deg) := by
  apply memoryPure_of_syntax (fun n => decide (n = ofString "is_zero_bytes"))
  · intro n hn
    have he : n = ofString "is_zero_bytes" := of_decide_eq_true hn
    subst n
    exact zeroBytes_function_memoryPure
  · decide

theorem zeroBytes_u256_callee_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (value : Limbs256) (ret : ValueHOL 64)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 s.memaddrs base) (hm : MemoryU256 s.memory base value)
    (hlk : lookupCodeHOLFinite s.code.lookup (ofString "is_zero_bytes")
      [.val (.word base), .val (.word 32)] = some (body, callee, rs))
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned ret), post)) :
    ret = .val (.word (if value.toNat = 0 then 1 else 0)) := by
  rw [hc] at hlk
  obtain ⟨_,_,rfl,rfl,rfl⟩ := arith_two_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "is_zero_bytes") (ofString "p") (ofString "n") .one .one .one
    (arithSourceBody Guest.Software.guestFn_is_zero_bytes) (.val (.word base)) (.val (.word 32))
    (by decide) arith_lookup_is_zero_bytes hlk
  exact zeroBytes_u256_returned (callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "p", .val (.word base))).update
      (ofString "n", .val (.word 32)))) post base value ret
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "p" by decide])
    (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ha hb hd hm hr

end InitECandidate.Solver.Wave8GuestInv.Arith
