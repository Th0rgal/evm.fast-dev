import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulTail
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulScopedFrame

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
open InitECandidate.Solver.GuestCodeLookup

/-- One actual polynomial subtraction iteration performs exactly one U256
write, with canonical Montgomery multiplication and modular subtraction. -/
theorem polySubmulBody_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b shift i : BitVec 64) (A B q : Limbs256)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word shift)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i)))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hACanon : A.toNat < fqModulus.toNat) (hBCanon : B.toNat < fqModulus.toNat)
    (hdA : DomainU256 state.memaddrs (a+(shift+i)*32))
    (hdB : DomainU256 state.memaddrs (b+i*32))
    (hmA : MemoryU256 state.memory (a+(shift+i)*32) A)
    (hmB : MemoryU256 state.memory (b+i*32) B)
    (hr : evaluateHOLFiniteState state polySubmulBody = (none,post)) :
    ∃ product out : Limbs256, product.toNat < fqModulus.toNat ∧ out.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2^256*product.toNat) (q.toNat*B.toNat) ∧
      Nat.ModEq fqModulus.toNat (out.toNat+product.toNat) A.toNat ∧
      post.memory = writeU256 state.memory (a+(shift+i)*32) out := by
  unfold polySubmulBody at hr
  obtain ⟨valueB,postB,hinitB,hshapeB,hmul,hrestoreB⟩ := arith_dec_none_state hr
  have hloadB := eval_load_u256 state polySubmulSrc (b+i*32) B
    (polySubmul_src_eval state b i hb hi) hdB hmB
  have hvB : valueB = B.toValue := Option.some.inj (hinitB.symm.trans hloadB)
  subst valueB
  let declaredB := setVarHOLFinite (ofString "bi") B.toValue state
  have hqB : declaredB.locals.lookup (ofString "q") = some q.toValue := by
    simpa [declaredB,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "bi" ≠ ofString "q" by decide] using hq
  have hbiB : declaredB.locals.lookup (ofString "bi") = some B.toValue := by
    simp [declaredB,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨product,resumed,inner,hPCanon,hprod,hlocals,hcode,hmem,hdomain,hloadA,hpostlocals,hpostmem⟩ :=
    fqMul_decCall_none_frame (s := declaredB) (post := postB) (ofString "p")
      [polySubmulVar "q",polySubmulVar "bi"] polySubmulLoadA q B hc hBCanon
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,polySubmulVar,hqB,hbiB]) hmul
  have haR : resumed.locals.lookup (ofString "a") = some (.val (.word a)) := by
    rw [hlocals]
    simpa [declaredB,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "p" ≠ ofString "a" by decide,
      show ofString "bi" ≠ ofString "a" by decide] using ha
  have hsR : resumed.locals.lookup (ofString "s") = some (.val (.word shift)) := by
    rw [hlocals]
    simpa [declaredB,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "p" ≠ ofString "s" by decide,
      show ofString "bi" ≠ ofString "s" by decide] using hs
  have hiR : resumed.locals.lookup (ofString "i") = some (.val (.word i)) := by
    rw [hlocals]
    simpa [declaredB,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "p" ≠ ofString "i" by decide,
      show ofString "bi" ≠ ofString "i" by decide] using hi
  have hPR : resumed.locals.lookup (ofString "p") = some product.toValue := by
    simp [hlocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have hdAR : DomainU256 resumed.memaddrs (a+(shift+i)*32) := by
    rw [hdomain]; exact hdA
  have hmAR : MemoryU256 resumed.memory (a+(shift+i)*32) A := by
    rw [hmem]; exact hmA
  unfold polySubmulLoadA at hloadA
  obtain ⟨valueA,tailPost,hinitA,hshapeA,htail,hrestoreA⟩ := arith_dec_none_state hloadA
  have heA := eval_load_u256 resumed polySubmulDst (a+(shift+i)*32) A
    (polySubmul_dst_eval resumed a shift i haR hsR hiR) hdAR hmAR
  have hvA : valueA = A.toValue := Option.some.inj (hinitA.symm.trans heA)
  subst valueA
  let declaredA := setVarHOLFinite (ofString "ai") A.toValue resumed
  have haA : declaredA.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [declaredA,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ai" ≠ ofString "a" by decide] using haR
  have hsA : declaredA.locals.lookup (ofString "s") = some (.val (.word shift)) := by
    simpa [declaredA,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ai" ≠ ofString "s" by decide] using hsR
  have hiA : declaredA.locals.lookup (ofString "i") = some (.val (.word i)) := by
    simpa [declaredA,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ai" ≠ ofString "i" by decide] using hiR
  have hPA : declaredA.locals.lookup (ofString "p") = some product.toValue := by
    simpa [declaredA,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ai" ≠ ofString "p" by decide] using hPR
  have hAA : declaredA.locals.lookup (ofString "ai") = some A.toValue := by
    simp [declaredA,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨out,hout,hsub,hwrite⟩ := polySubmulTail_none declaredA tailPost a shift i A product
    (hcode.trans hc) haA hsA hiA hAA hPA hACanon hPCanon hdAR htail
  refine ⟨product,out,hPCanon,hout,hprod,hsub,?_⟩
  rw [hrestoreB]
  change postB.memory = _
  rw [hpostmem,hrestoreA]
  change tailPost.memory = _
  rw [hwrite]
  change writeU256 resumed.memory (a+(shift+i)*32) out = _
  rw [hmem]
  rfl

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
