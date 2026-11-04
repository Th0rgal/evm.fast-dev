import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeOrder

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup

/-- The actual discarded subtraction call followed by the actual local-result
scan strictly lowers the signed degree and its natural rank. Canonicality,
inverse/quotient relations and buffer validity remain explicit caller duties. -/
theorem polySubmul_scan_progress {F : Type} (state mid post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256) (inverse : Nat)
    (dest : MlS) (subArgs scanArgs : List (ExpHOL 64))
    (hdbBound : db < 13) (htarget : shift+db < 13)
    (hc : state.code = originalRuntimeCode)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b) (halign : a.toNat % 8 = 0)
    (hbound : a.toNat + 416 ≤ 2^64)
    (hdegree : PolynomialDegreeBelow A (shift+db+1))
    (hinv : Nat.ModEq fqModulus.toNat ((B db).toNat*inverse) (2^256*2^256))
    (hq : Nat.ModEq fqModulus.toNat (2^256*q.toNat) ((A (shift+db)).toNat*inverse))
    (hsubArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) subArgs =
      some [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))])
    (hsub : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "fq_poly_submul") subArgs) =
      (none,mid))
    (hscanArgs : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a)) scanArgs =
      some [.val (.word a), .val (.word 13)])
    (hscan : evaluateHOLFiniteState mid (.call (some (some (.local,dest),none))
      (ofString "fq_poly_deg") scanArgs) = (none,post)) :
    ∃ (C : Nat → Limbs256) (after : BitVec 64), CanonicalPolynomial C ∧
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      PolynomialDegreeValue C (.val (.word after)) ∧
      post.locals = mid.locals.update (dest,.val (.word after)) ∧
      wordCmpHOL .less after (BitVec.ofNat 64 (shift+db)) = true ∧
      polynomialDegreeRank after < polynomialDegreeRank (BitVec.ofNat 64 (shift+db)) ∧
      polynomialDegreeRank after ≤ 13 ∧ PolynomialFrame state.memory post.memory a := by
  obtain ⟨C,hC,hmC,hmB',hrange,hframe⟩ := polySubmul_call_none_correct state mid a b shift db A B q
    hdbBound htarget hc hACanon hBCanon hdA hdB hmA hmB hsep subArgs hsubArgs hsub
  have hbelow := submulRange_degree_decrease q inverse shift db A B C htarget hACanon hrange hdegree hinv hq
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "fq_poly_submul") subArgs)
  rw [hsub] at hmeta
  dsimp only at hmeta
  obtain ⟨value,hvalue,hlocals,hmem⟩ := fqDegree_call_none_correct mid post a C dest scanArgs
    (hmeta.1.trans hc) halign hbound (by simpa only [hmeta.2.1] using hdA) hmC hscanArgs hscan
  have hword : ∃ after : BitVec 64, value = .val (.word after) := by
    rcases hvalue with ⟨he,_⟩ | ⟨j,hj,he,_⟩
    · exact ⟨0-1,he⟩
    · exact ⟨BitVec.ofNat 64 j,he⟩
  obtain ⟨after,rfl⟩ := hword
  obtain ⟨hsigned,hrank⟩ := polynomialDegree_signed_progress C after (shift+db) htarget hvalue hbelow
  refine ⟨C,after,hC,?_,?_,hvalue,hlocals,hsigned,hrank,polynomialDegreeRank_bound C after hvalue,?_⟩
  · rw [hmem]; exact hmC
  · rw [hmem]; exact hmB'
  · rw [hmem]; exact hframe

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
