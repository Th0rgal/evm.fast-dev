import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.FqMulLeftCanonical
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulExactTail
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulNoReturn
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceReturned

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def ExactSubmulCoefficient (q A B out : Limbs256) : Prop :=
  ∃ product : Limbs256, product.toNat < fqModulus.toNat ∧
    Nat.ModEq fqModulus.toNat (2 ^ 256 * product.toNat) (q.toNat * B.toNat) ∧
    out = modSub256 A product fqModulus

def ExactSubmulRange (q : Limbs256) (shift first last : Nat)
    (A B C : Nat → Limbs256) : Prop :=
  (∀ j, j < shift + first ∨ shift + last < j → C j = A j) ∧
  (∀ k, first ≤ k → k ≤ last → ExactSubmulCoefficient q (A (shift + k)) (B k) (C (shift + k)))

theorem exactSubmulRange_empty (q : Limbs256) (shift first last : Nat) (A B : Nat → Limbs256)
    (hempty : last < first) : ExactSubmulRange q shift first last A B A := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro k hfirst hlast
  omega

theorem exactSubmulRange_step (q out : Limbs256) (shift first last : Nat) (A B C : Nat → Limbs256)
    (hindex : first ≤ last)
    (hstep : ExactSubmulCoefficient q (A (shift + first)) (B first) out)
    (hrest : ExactSubmulRange q shift (first + 1) last
      (fun j => if j = shift + first then out else A j) B C) :
    ExactSubmulRange q shift first last A B C := by
  constructor
  · intro j hj
    have hr := hrest.1 j (by rcases hj with h | h; exact Or.inl (by omega); exact Or.inr h)
    have hne : j ≠ shift + first := by rcases hj with h | h <;> omega
    simpa only [if_neg hne] using hr
  · intro k hk hlast
    by_cases he : k = first
    · subst k
      have hr := hrest.1 (shift + first) (Or.inl (by omega))
      simp only [ite_true] at hr
      rw [hr]
      exact hstep
    · have hr := hrest.2 k (by omega) hlast
      have hne : shift + k ≠ shift + first := by omega
      simpa only [if_neg hne] using hr

/-- One actual submul iteration with canonical quotient `q` and arbitrary
dividend `A` and divisor `B`. -/
theorem polySubmulBody_exact_left_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b shift i : BitVec 64) (A B q : Limbs256)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word shift)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i)))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hqCanon : q.toNat < fqModulus.toNat)
    (hdA : DomainU256 state.memaddrs (a + (shift + i) * 32))
    (hdB : DomainU256 state.memaddrs (b + i * 32))
    (hmA : MemoryU256 state.memory (a + (shift + i) * 32) A)
    (hmB : MemoryU256 state.memory (b + i * 32) B)
    (hr : evaluateHOLFiniteState state polySubmulBody = (none, post)) :
    ∃ product : Limbs256, product.toNat < fqModulus.toNat ∧
      Nat.ModEq fqModulus.toNat (2 ^ 256 * product.toNat) (q.toNat * B.toNat) ∧
      post.memory = writeU256 state.memory (a + (shift + i) * 32) (modSub256 A product fqModulus) := by
  unfold polySubmulBody at hr
  obtain ⟨valueB, postB, hinitB, hshapeB, hmul, hrestoreB⟩ := arith_dec_none_state hr
  have hloadB := eval_load_u256 state polySubmulSrc (b + i * 32) B
    (polySubmul_src_eval state b i hb hi) hdB hmB
  have hvB : valueB = B.toValue := Option.some.inj (hinitB.symm.trans hloadB)
  subst valueB
  let declaredB := setVarHOLFinite (ofString "bi") B.toValue state
  have hqB : declaredB.locals.lookup (ofString "q") = some q.toValue := by
    simpa [declaredB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "bi" ≠ ofString "q" by decide] using hq
  have hbiB : declaredB.locals.lookup (ofString "bi") = some B.toValue := by
    simp [declaredB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨product, resumed, inner, hPCanon, hprod, hlocals, hcode, hmem, hdomain, hloadA, hpostlocals, hpostmem⟩ :=
    fqMul_decCall_none_frame_left (s := declaredB) (post := postB) (ofString "p")
      [polySubmulVar "q", polySubmulVar "bi"] polySubmulLoadA q B hc hqCanon
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, polySubmulVar, hqB, hbiB]) hmul
  have haR : resumed.locals.lookup (ofString "a") = some (.val (.word a)) := by
    rw [hlocals]
    simpa [declaredB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "a" by decide,
      show ofString "bi" ≠ ofString "a" by decide] using ha
  have hsR : resumed.locals.lookup (ofString "s") = some (.val (.word shift)) := by
    rw [hlocals]
    simpa [declaredB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "s" by decide,
      show ofString "bi" ≠ ofString "s" by decide] using hs
  have hiR : resumed.locals.lookup (ofString "i") = some (.val (.word i)) := by
    rw [hlocals]
    simpa [declaredB, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "p" ≠ ofString "i" by decide,
      show ofString "bi" ≠ ofString "i" by decide] using hi
  have hPR : resumed.locals.lookup (ofString "p") = some product.toValue := by
    simp [hlocals, HolFiniteMapExact.lookup_update, FUPDATE]
  have hdAR : DomainU256 resumed.memaddrs (a + (shift + i) * 32) := by
    rw [hdomain]; exact hdA
  have hmAR : MemoryU256 resumed.memory (a + (shift + i) * 32) A := by
    rw [hmem]; exact hmA
  unfold polySubmulLoadA at hloadA
  obtain ⟨valueA, tailPost, hinitA, hshapeA, htail, hrestoreA⟩ := arith_dec_none_state hloadA
  have heA := eval_load_u256 resumed polySubmulDst (a + (shift + i) * 32) A
    (polySubmul_dst_eval resumed a shift i haR hsR hiR) hdAR hmAR
  have hvA : valueA = A.toValue := Option.some.inj (hinitA.symm.trans heA)
  subst valueA
  let declaredA := setVarHOLFinite (ofString "ai") A.toValue resumed
  have haA : declaredA.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [declaredA, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ai" ≠ ofString "a" by decide] using haR
  have hsA : declaredA.locals.lookup (ofString "s") = some (.val (.word shift)) := by
    simpa [declaredA, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ai" ≠ ofString "s" by decide] using hsR
  have hiA : declaredA.locals.lookup (ofString "i") = some (.val (.word i)) := by
    simpa [declaredA, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ai" ≠ ofString "i" by decide] using hiR
  have hPA : declaredA.locals.lookup (ofString "p") = some product.toValue := by
    simpa [declaredA, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "ai" ≠ ofString "p" by decide] using hPR
  have hAA : declaredA.locals.lookup (ofString "ai") = some A.toValue := by
    simp [declaredA, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hwrite := polySubmulTail_exact_none declaredA tailPost a shift i A product
    (hcode.trans hc) haA hsA hiA hAA hPA hdAR htail
  refine ⟨product, hPCanon, hprod, ?_⟩
  rw [hrestoreB]
  change postB.memory = _
  rw [hpostmem, hrestoreA]
  change tailPost.memory = _
  rw [hwrite]
  change writeU256 resumed.memory (a + (shift + i) * 32) (modSub256 A product fqModulus) = _
  rw [hmem]
  rfl

theorem polySubmulBody_exact_polynomial {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift i : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hiBound : i < 13) (htarget : shift + i < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hqCanon : q.toNat < fqModulus.toNat)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (hr : evaluateHOLFiniteState state polySubmulBody = (none, post)) :
    ∃ out : Limbs256,
      ExactSubmulCoefficient q (A (shift + i)) (B i) out ∧
      MemoryPolynomial post.memory a (fun j => if j = shift + i then out else A j) ∧
      MemoryPolynomial post.memory b B ∧ PolynomialFrame state.memory post.memory a := by
  have hdA' : DomainU256 state.memaddrs (a + (BitVec.ofNat 64 shift + BitVec.ofNat 64 i) * 32) := by
    rw [coefficientAddress_shift]; exact hdA (shift + i) htarget
  have hdB' : DomainU256 state.memaddrs (b + BitVec.ofNat 64 i * 32) := by
    rw [coefficientAddress_source]; exact hdB i hiBound
  have hmA' : MemoryU256 state.memory (a + (BitVec.ofNat 64 shift + BitVec.ofNat 64 i) * 32) (A (shift + i)) := by
    rw [coefficientAddress_shift]; exact hmA (shift + i) htarget
  have hmB' : MemoryU256 state.memory (b + BitVec.ofNat 64 i * 32) (B i) := by
    rw [coefficientAddress_source]; exact hmB i hiBound
  obtain ⟨product, hprodCanon, hprod, hwrite⟩ := polySubmulBody_exact_left_none state post
    a b (BitVec.ofNat 64 shift) (BitVec.ofNat 64 i) (A (shift + i)) (B i) q
    hc ha hb hs hi hq hqCanon hdA' hdB' hmA' hmB' hr
  rw [coefficientAddress_shift] at hwrite
  let out := modSub256 (A (shift + i)) product fqModulus
  refine ⟨out, ⟨product, hprodCanon, hprod, rfl⟩, ?_, ?_, ?_⟩
  · rw [hwrite]
    exact writeCoefficient_polynomial state.memory a A (shift + i) out htarget hmA
  · rw [hwrite]
    exact writeCoefficient_disjoint state.memory a b B (shift + i) out htarget hsep hmB
  · rw [hwrite]
    exact writeCoefficient_frame state.memory a (shift + i) out htarget

theorem polySubmulLoop_exact_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift i db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hiBound : i ≤ db + 1) (hdbBound : db < 13) (htarget : shift + db < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hqCanon : q.toNat < fqModulus.toNat)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (hr : evaluateHOLFiniteState state polySubmulLoop = (none, post)) :
    ∃ C : Nat → Limbs256, MemoryPolynomial post.memory a C ∧
      MemoryPolynomial post.memory b B ∧ ExactSubmulRange q shift i db A B C ∧
      PolynomialFrame state.memory post.memory a := by
  unfold polySubmulLoop at hr
  rw [evaluateHOLFiniteState_while_fixClockRewrite] at hr
  have hg := polySubmul_guard state i db hiBound hdbBound hi hdb
  change evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) _ = _ at hg
  rw [hg] at hr
  dsimp only at hr
  by_cases hindex : i ≤ db
  · rw [if_pos hindex, if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
    by_cases hclock : state.clock = 0
    · simp [hclock] at hr
    · rw [if_neg hclock] at hr
      rcases hbody : evaluateHOLFiniteState (decClockHOLFinite state) polySubmulBody with ⟨res, mid⟩
      rw [hbody] at hr
      cases res with
      | none =>
          obtain ⟨out, hstep, hmA', hmB', hframe⟩ := polySubmulBody_exact_polynomial
            (decClockHOLFinite state) mid a b shift i A B q (by omega) (by omega)
            hc ha hb hs hi hq hqCanon hdA hdB hmA hmB hsep hbody
          let nextA := fun j => if j = shift + i then out else A j
          have ha' : mid.locals.lookup (ofString "a") = some (.val (.word a)) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "a") (by simp) hbody).trans ha
          have hb' : mid.locals.lookup (ofString "b") = some (.val (.word b)) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "b") (by simp) hbody).trans hb
          have hs' : mid.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "s") (by simp) hbody).trans hs
          have hq' : mid.locals.lookup (ofString "q") = some q.toValue :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "q") (by simp) hbody).trans hq
          have hdb' : mid.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))) :=
            (polySubmulBody_keeps (decClockHOLFinite state) mid (ofString "db") (by simp) hbody).trans hdb
          have hi' := polySubmulBody_index (decClockHOLFinite state) mid i hi hbody
          have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite state) polySubmulBody
          rw [hbody] at hmeta
          have hc' : mid.code = originalRuntimeCode := hmeta.1.trans hc
          have hdom : mid.memaddrs = state.memaddrs := hmeta.2.1
          have hdA' : DomainPolynomial mid.memaddrs a := by rw [hdom]; exact hdA
          have hdB' : DomainPolynomial mid.memaddrs b := by rw [hdom]; exact hdB
          obtain ⟨C, hmemC, hmemB, hrange, hframe'⟩ := polySubmulLoop_exact_none mid post a b shift (i + 1) db
            nextA B q (by omega) hdbBound htarget hc' ha' hb' hs' hi' hdb' hq' hqCanon
            hdA' hdB' hmA' hmB' hsep hr
          exact ⟨C, hmemC, hmemB, exactSubmulRange_step q out shift i db A B C hindex hstep hrange,
            polynomialFrame_trans state.memory mid.memory post.memory a hframe hframe'⟩
      | some result =>
          cases result with
          | «continue» =>
              have hno := evaluate_noTopContinue polySubmulBody (by decide) (decClockHOLFinite state)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                polySubmulBody (by decide) (decClockHOLFinite state)
              rw [hbody] at hno
              exact False.elim (hno rfl)
          | _ => simp at hr
  · rw [if_neg hindex, if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
    have he : state = post := (Prod.mk.inj hr).2
    subst post
    exact ⟨A, hmA, hmB, exactSubmulRange_empty q shift i db A B (by omega),
      polynomialFrame_refl state.memory a⟩
termination_by db + 1 - i
decreasing_by omega

theorem polySubmul_exact_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256) (ret : ValueHOL 64)
    (hdbBound : db < 13) (htarget : shift + db < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hdb : state.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hqCanon : q.toNat < fqModulus.toNat)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (hr : evaluateHOLFiniteState state (arithSourceBody Guest.Software.guestFn_fq_poly_submul) =
      (some (.returned ret), post)) :
    ∃ C : Nat → Limbs256, ret = .val (.word 0) ∧
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      ExactSubmulRange q shift 0 db A B C ∧ PolynomialFrame state.memory post.memory a := by
  rw [polySubmul_source_eq] at hr
  obtain ⟨value, inner, hinit, hshape, hbody, hrestore⟩ := arith_dec_returned_state hr
  have hv : value = .val (.word 0) := by
    simpa [evalHOLFinite, evalHOLExact] using hinit.symm
  subst value
  let entry := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have ha' : entry.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "a" by decide] using ha
  have hb' : entry.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "b" by decide] using hb
  have hs' : entry.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "s" by decide] using hs
  have hdb' : entry.locals.lookup (ofString "db") = some (.val (.word (BitVec.ofNat 64 db))) := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "db" by decide] using hdb
  have hq' : entry.locals.lookup (ofString "q") = some q.toValue := by
    simpa [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "q" by decide] using hq
  rcases arith_seq_returned hbody with hloopret | ⟨mid, hloop, hreturn⟩
  · exact False.elim (polySubmulLoop_not_returned entry ret (congrArg Prod.fst hloopret))
  · obtain ⟨C, hmemC, hmemB, hrange, hframe⟩ := polySubmulLoop_exact_none entry mid a b shift 0 db A B q
      (by omega) hdbBound htarget hc ha' hb' hs'
      (by simp [entry, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hdb' hq'
      hqCanon hdA hdB hmA hmB hsep hloop
    have hreturn' : evaluateHOLFiniteState mid (.return (.const 0)) =
        (some (.returned (.val (.word 0))), emptyLocalsHOLFinite mid) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    rw [hreturn'] at hreturn
    have he : ret = .val (.word 0) := by
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using (Prod.mk.inj hreturn).1.symm
    have hmem : post.memory = mid.memory := by
      rw [hrestore, ← (Prod.mk.inj hreturn).2]
      rfl
    refine ⟨C, he, ?_, ?_, hrange, ?_⟩
    · rw [hmem]; exact hmemC
    · rw [hmem]; exact hmemB
    · rw [hmem]; exact hframe

theorem polySubmul_exact_call_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift + db < 13)
    (hc : state.code = originalRuntimeCode)
    (hqCanon : q.toNat < fqModulus.toNat)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (args : List (ExpHOL 64))
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))])
    (hr : evaluateHOLFiniteState state (.call (some (none, none)) (ofString "fq_poly_submul") args) =
      (none, post)) :
    ∃ C : Nat → Limbs256,
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      ExactSubmulRange q shift 0 db A B C ∧ PolynomialFrame state.memory post.memory a := by
  obtain ⟨values, body, callee, rs, ret, bpost, he, hlk, hclock, hrun, hshape, hpost⟩ :=
    arith_call_discard_none_state hr
  have hv := Option.some.inj (he.symm.trans hargs)
  subst values
  rw [hc, polySubmul_lookup] at hlk
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hlk
  obtain ⟨C, _, hmemC, hmemB, hrange, hframe⟩ := polySubmul_exact_returned
    (callEntryStateHOLFinite state (polySubmulLocals a b q shift db)) bpost a b shift db A B q ret
    hdbBound htarget hc
    (by simp [callEntryStateHOLFinite, polySubmulLocals, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "db" ≠ ofString "a" by decide,
      show ofString "s" ≠ ofString "a" by decide,
      show ofString "q" ≠ ofString "a" by decide,
      show ofString "b" ≠ ofString "a" by decide])
    (by simp [callEntryStateHOLFinite, polySubmulLocals, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "db" ≠ ofString "b" by decide,
      show ofString "s" ≠ ofString "b" by decide,
      show ofString "q" ≠ ofString "b" by decide])
    (by simp [callEntryStateHOLFinite, polySubmulLocals, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "db" ≠ ofString "s" by decide])
    (by simp [callEntryStateHOLFinite, polySubmulLocals, HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [callEntryStateHOLFinite, polySubmulLocals, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "db" ≠ ofString "q" by decide,
      show ofString "s" ≠ ofString "q" by decide])
    hqCanon hdA hdB hmA hmB hsep hrun
  simpa only [hpost] using ⟨C, hmemC, hmemB, hrange, hframe⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
