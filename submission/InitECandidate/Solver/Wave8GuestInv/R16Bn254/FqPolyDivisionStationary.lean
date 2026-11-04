import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.FqPolySubmulExact
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDivisionSameHead
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDivisionHeadRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqReviewedRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionBound
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionEntry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators
open InitECandidate.Solver.Wave8GuestInv

private theorem signed_less_eq_stat (left right : BitVec 64) :
    holAsmSignedLess left right = left.slt right := by
  have bl := left.isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

structure PolyDivGenContext (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) : Prop where
  positive : 0 < d1
  bound : d1 < 13
  degree : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d1)))
  inverseCanonical : inverse.toNat < fqModulus.toNat
  inverseRelation : Nat.ModEq fqModulus.toNat ((B d1).toNat * inverse.toNat) (2 ^ 256 * 2 ^ 256)
  separateAB : PolynomialDisjoint a b
  separateAQ : PolynomialDisjoint a quotient
  separateQB : PolynomialDisjoint quotient b
  aligned : a.toNat % 8 = 0
  nonwrapping : a.toNat + 416 ≤ 2 ^ 64

structure PolyDivGenInvariant {F : Type} (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) (s : PanSemStateFiniteExact 64 F) : Prop where
  r0 : s.locals.lookup (ofString "r0") = some (.val (.word a))
  r1 : s.locals.lookup (ofString "r1") = some (.val (.word b))
  q : s.locals.lookup (ofString "q") = some (.val (.word quotient))
  degree1 : s.locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1)))
  linv : s.locals.lookup (ofString "linv") = some inverse.toValue
  domainA : DomainPolynomial s.memaddrs a
  domainB : DomainPolynomial s.memaddrs b
  domainQ : DomainPolynomial s.memaddrs quotient
  divisor : MemoryPolynomial s.memory b B
  dividend : ∃ (A Q : Nat → Limbs256) (degree : BitVec 64),
    MemoryPolynomial s.memory a A ∧ MemoryPolynomial s.memory quotient Q ∧
    PolynomialDegreeValue A (.val (.word degree)) ∧
    s.locals.lookup (ofString "d0") = some (.val (.word degree))

theorem polyDivGenInvariant_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (h : PolyDivGenInvariant a b quotient d1 B inverse s) :
    PolyDivGenInvariant a b quotient d1 B inverse (decClockHOLFinite s) :=
  ⟨h.r0, h.r1, h.q, h.degree1, h.linv, h.domainA, h.domainB, h.domainQ, h.divisor, h.dividend⟩

/-- Machine-state rank bounded by `13` on every active head:
`reviewedDivisionRank fqModulus.toNat d0 d1 linv top slot`. -/
def polyDivReviewedStateRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "r0"), s.locals.lookup (ofString "q"),
    s.locals.lookup (ofString "d0"), s.locals.lookup (ofString "d1") with
  | some (.val (.word a)), some (.val (.word q)),
    some (.val (.word d0)), some (.val (.word d1)) =>
      if d0.toNat < 13 ∧ 1 ≤ d1.toNat ∧ d1.toNat ≤ d0.toNat then
        reviewedDivisionRank fqModulus.toNat d0.toNat d1.toNat 1
          (polynomialMemoryCoefficients s.memory a d0.toNat).toNat
          (polynomialMemoryCoefficients s.memory q (d0.toNat - d1.toNat)).toNat
      else 0
  | _, _, _, _ => 0

theorem polyDivReviewedStateRank_bound {F : Type} (s : PanSemStateFiniteExact 64 F) :
    polyDivReviewedStateRank s ≤ 13 := by
  unfold polyDivReviewedStateRank
  split
  · split
    · rename_i h
      exact reviewedDivisionRank_le13 fqModulus.toNat _ _ 1 _ _ h.1 h.2.1
    · omega
  · omega

theorem polyDivReviewedStateRank_represented {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b q : BitVec 64) (d0 d1 : Nat) (top slot : Limbs256)
    (h0 : d0 < 13) (hpos : 1 ≤ d1) (hle : d1 ≤ d0)
    (hl : PolyDivLocals s.locals a b q d0 d1)
    (ht : MemoryU256 s.memory (coefficientAddress a d0) top)
    (hs : MemoryU256 s.memory (coefficientAddress q (d0 - d1)) slot) :
    polyDivReviewedStateRank s =
      reviewedDivisionRank fqModulus.toNat d0 d1 1 top.toNat slot.toNat := by
  have h064 : d0 < 2 ^ 64 := by omega
  have h164 : d1 < 2 ^ 64 := by omega
  have hcond_ok : d0 < 13 ∧ 1 ≤ d1 ∧ d1 ≤ d0 := ⟨h0, hpos, hle⟩
  simp only [polyDivReviewedStateRank, hl.r0, hl.q, hl.degree0, hl.degree1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h064, Nat.mod_eq_of_lt h164, if_pos hcond_ok]
  rw [polynomialMemoryCoefficient_read s.memory a d0 top ht,
    polynomialMemoryCoefficient_read s.memory q (d0 - d1) slot hs]

/-- Zero-quotient submul call with arbitrary divisor coefficients (via `polySubmul_exact_call_none`). -/
theorem polySubmul_zero_exact_call_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift db : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hdbBound : db < 13) (htarget : shift + db < 13)
    (hc : state.code = originalRuntimeCode)
    (hqzero : q.toNat = 0)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (args : List (ExpHOL 64))
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word a), .val (.word b), q.toValue,
        .val (.word (BitVec.ofNat 64 shift)), .val (.word (BitVec.ofNat 64 db))])
    (hr : evaluateHOLFiniteState state (.call (some (none, none)) (ofString "fq_poly_submul") args) =
      (none, post)) :
    post.memory = state.memory := by
  have hqCanon : q.toNat < fqModulus.toNat := by
    rw [hqzero]; exact Nat.lt_trans (by decide) fqModulus_gt_one
  obtain ⟨C, hmC, hmB', hrange, hframe⟩ := polySubmul_exact_call_none state post a b shift db A B q
    hdbBound htarget hc hqCanon hdA hdB hmA hmB hsep args hargs hr
  have hCeq : ∀ j, j < 13 → C j = A j := by
    intro j hj
    by_cases hlt : j < shift
    · exact hrange.1 j (Or.inl (by omega))
    · by_cases hgt : shift + db < j
      · exact hrange.1 j (Or.inr hgt)
      · have hk : j - shift ≤ db := by omega
        have hsum : shift + (j - shift) = j := by omega
        obtain ⟨product, hpCanon, hprod, hout⟩ := hrange.2 (j - shift) (by omega) hk
        have hpzero : product.toNat = 0 :=
          fqMultiple_product_zero q.toNat (B (j - shift)).toNat product.toNat
            (by rw [hqzero]; rfl) hpCanon hprod
        rw [← hsum, hout, fqSub_zero_eq _ _ hpzero]
  funext x
  by_cases hout : PolynomialOutside a x
  · exact hframe x hout
  · simp only [PolynomialOutside, Classical.not_forall, Classical.not_not] at hout
    obtain ⟨j, hj, hxj⟩ := hout
    have hCj := hmC j hj
    rw [hCeq j hj] at hCj
    have hAj := hmA j hj
    simp only [u256Addresses, List.mem_cons, List.not_mem_nil, or_false] at hxj
    rcases hxj with rfl | rfl | rfl | rfl
    · exact hCj.1.trans hAj.1.symm
    · exact hCj.2.1.trans hAj.2.1.symm
    · exact hCj.2.2.1.trans hAj.2.2.1.symm
    · exact hCj.2.2.2.trans hAj.2.2.2.symm

/-- Exact tail execution for ANY `cf < p`, arbitrary dividend `A` and divisor `B`. -/
theorem polyDivTail_exact_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d0 d1 : Nat) (A B Q : Nat → Limbs256) (cf : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hle : d1 ≤ d0)
    (hc : state.code = originalRuntimeCode) (hl : PolyDivLocals state.locals a b quotient d0 d1)
    (hcf : state.locals.lookup (ofString "cf") = some cf.toValue)
    (hcfCanon : cf.toNat < fqModulus.toNat)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hdQ : DomainPolynomial state.memaddrs quotient)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hmQ : MemoryPolynomial state.memory quotient Q)
    (hAB : PolynomialDisjoint a b) (hAQ : PolynomialDisjoint a quotient)
    (hQB : PolynomialDisjoint quotient b)
    (halign : a.toNat % 8 = 0) (hbound : a.toNat + 416 ≤ 2 ^ 64)
    (hr : evaluateHOLFiniteState state polyDivTail = (none, post)) :
    ∃ (C : Nat → Limbs256) (after : BitVec 64),
      MemoryPolynomial post.memory a C ∧ MemoryPolynomial post.memory b B ∧
      MemoryPolynomial post.memory quotient (fun j => if j = d0 - d1 then cf else Q j) ∧
      ExactSubmulRange cf (d0 - d1) 0 d1 A B C ∧
      PolynomialDegreeValue C (.val (.word after)) ∧
      post.locals = state.locals.update (ofString "d0", .val (.word after)) ∧
      (cf.toNat = 0 → post.memory = writeU256 state.memory (coefficientAddress quotient (d0 - d1)) cf) ∧
      ∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = state.memory x := by
  have hshift : d0 - d1 < 13 := by omega
  let stored : PanSemStateFiniteExact 64 F :=
    { state with memory := writeU256 state.memory (coefficientAddress quotient (d0 - d1)) cf }
  have hstore := eval_store_u256 state polyDivQAddress (polyDivVar "cf")
    (coefficientAddress quotient (d0 - d1)) cf (polyDiv_q_eval state a b quotient d0 d1 hl h1 hle)
    (by simpa [arithEval, polyDivVar, evalHOLExact] using hcf) (hdQ _ hshift)
  change evaluateHOLFiniteState state polyDivStore = (none, stored) at hstore
  rw [polyDivTail, evaluateHOLFiniteState_seq_line780, hstore] at hr
  dsimp only at hr
  obtain ⟨mid, hsub, hscan⟩ := arith_seq_none hr
  have hmidlocals : mid.locals = state.locals := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, he⟩ := arith_call_discard_none_state hsub
    rw [he]
  have hmA' : MemoryPolynomial stored.memory a A :=
    writeCoefficient_disjoint state.memory quotient a A (d0 - d1) cf hshift
      (polynomialDisjoint_symm a quotient hAQ) hmA
  have hmB' : MemoryPolynomial stored.memory b B :=
    writeCoefficient_disjoint state.memory quotient b B (d0 - d1) cf hshift hQB hmB
  have hmQ' : MemoryPolynomial stored.memory quotient (fun j => if j = d0 - d1 then cf else Q j) :=
    writeCoefficient_polynomial state.memory quotient Q (d0 - d1) cf hshift hmQ
  have hsubArgs := polyDiv_sub_args stored a b quotient d0 d1 cf hl h1 hle hcf
  obtain ⟨C, hmC, hmB_mid, hrange, hframe⟩ := polySubmul_exact_call_none stored mid a b (d0 - d1) d1
    A B cf h1 (by omega) hc hcfCanon hdA hdB hmA' hmB' hAB polyDivSubArgs hsubArgs hsub
  have hmeta := evaluateHOLFiniteState_metadata stored polyDivSubCall
  rw [hsub] at hmeta
  have hscanArgs : evalListHOLFinite mid (h := fun x => Classical.propDecidable (mid.memaddrs x)) polyDivScanArgs =
      some [.val (.word a), .val (.word 13)] := by
    have hr0 : mid.locals.lookup (ofString "r0") = some (.val (.word a)) := by
      rw [hmidlocals]; exact hl.r0
    simp [polyDivScanArgs, polyDivVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, hr0]
  obtain ⟨val, hval, hlocals, hmem⟩ := fqDegree_call_none_correct mid post a C (ofString "d0")
    polyDivScanArgs (hmeta.1.trans hc) halign hbound
    (by rw [hmeta.2.1]; exact hdA) hmC hscanArgs hscan
  have hword : ∃ after : BitVec 64, val = .val (.word after) := by
    rcases hval with ⟨he, _⟩ | ⟨j, _, he, _, _⟩
    · exact ⟨0 - 1, he⟩
    · exact ⟨BitVec.ofNat 64 j, he⟩
  obtain ⟨after, rfl⟩ := hword
  refine ⟨C, after, ?_, ?_, ?_, hrange, hval, ?_, ?_, ?_⟩
  · rw [hmem]; exact hmC
  · rw [hmem]; exact hmB_mid
  · rw [hmem]; exact polynomialFrame_preserves stored.memory mid.memory a quotient _ hframe hAQ hmQ'
  · rw [hlocals, hmidlocals]
  · intro hz
    have hmidEq := polySubmul_zero_exact_call_none stored mid a b (d0 - d1) d1 A B cf
      h1 (by omega) hc hz hdA hdB hmA' hmB' hAB polyDivSubArgs hsubArgs hsub
    exact hmem.trans hmidEq
  · intro x hxa hxq
    rw [hmem, hframe x hxa]
    exact writeU256_frame state.memory _ x cf (hxq _ hshift)

/-- Complete `polyDivBody` step under `PolyDivGenInvariant` (arbitrary noncanonical `A` and `B`):
either `polyDivReviewedStateRank` strictly drops or `post = {s with clock := post.clock}` (`SameHead`). -/
theorem polyDivBody_stationary_step {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (ctx : PolyDivGenContext a b quotient d1 B inverse)
    (hc : s.code = originalRuntimeCode) (hi : PolyDivGenInvariant a b quotient d1 B inverse s)
    (word : BitVec 64)
    (hguard : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
      some (.val (.word word))) (hnz : word ≠ 0)
    (hr : evaluateHOLFiniteState s polyDivBody = (none, post)) :
    PolyDivGenInvariant a b quotient d1 B inverse post ∧
      (polyDivReviewedStateRank post < polyDivReviewedStateRank s ∨
        post = { s with clock := post.clock }) ∧
      (∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x) := by
  obtain ⟨A, Q, degree, hmA, hmQ, hdegree, hlocal⟩ := hi.dividend
  obtain ⟨w, v, hw, hv, hcmp⟩ := cmp_counter_active s (ofString "d0") .notLess (polyDivVar "d1") word hguard hnz
  have hw' : w = degree := by
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using hw.symm.trans hlocal
  have hv' : v = BitVec.ofNat 64 d1 := by
    simpa [polyDivVar, evalHOLFinite, evalHOLExact, hi.degree1] using hv.symm
  subst w; subst v
  have hpositive : 0 < (BitVec.ofNat 64 d1).toInt := by
    rw [degreeIndex_toInt d1 ctx.bound]
    exact_mod_cast ctx.positive
  obtain ⟨d0, db, h0, hdb, hdbpos, hle, he0, he1, hshift, hbelow⟩ :=
    polynomialDegree_guard_indices A B degree (BitVec.ofNat 64 d1) hdegree ctx.degree hpositive hcmp
  have hdbEq : db = d1 := by
    have he := congrArg BitVec.toNat he1
    simp only [BitVec.toNat_ofNat] at he
    have hd1 := ctx.bound
    omega
  subst db
  have hd0_nz : (A d0).toNat ≠ 0 :=
    polynomialDegreeValue_at_index A d0 h0 (by simpa only [he0] using hdegree)
  have hl : PolyDivLocals s.locals a b quotient d0 d1 :=
    ⟨hi.r0, hi.r1, hi.q, by simpa only [he0] using hlocal, hi.degree1⟩
  have hcontext := polyDivBody_context s hc
  rw [hr] at hcontext
  have hmeta := evaluateHOLFiniteState_metadata s polyDivBody
  rw [hr] at hmeta
  -- Unfold polyDivBody: load top, multiply cf = fq_mul(top, linv), run polyDivTail
  have hr_orig := hr
  unfold polyDivBody at hr
  obtain ⟨topVal, postTop, hinit, hshape, hmul, hrestore⟩ := arith_dec_none_state hr
  have hload := eval_load_u256 s polyDivTopAddress (coefficientAddress a d0) (A d0)
    (polyDiv_top_eval s a b quotient d0 d1 hl) (hi.domainA d0 h0) (hmA d0 h0)
  have ht : topVal = (A d0).toValue := Option.some.inj (hinit.symm.trans hload)
  subst topVal
  let declared := setVarHOLFinite (ofString "top") (A d0).toValue s
  have hlD : PolyDivLocals declared.locals a b quotient d0 d1 :=
    hl.update_temp (ofString "top") (A d0).toValue (Or.inl rfl)
  have htD : declared.locals.lookup (ofString "top") = some (A d0).toValue := by
    simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hiD : declared.locals.lookup (ofString "linv") = some inverse.toValue := by
    simpa [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "top" ≠ ofString "linv" by decide] using hi.linv
  obtain ⟨cf, resumed, inner, hcfCanon, hprod, hlocals, hcode, hmem, hdomain, htail, hpostLocals, hpostMem⟩ :=
    fqMul_decCall_none_frame (s := declared) (post := postTop) (ofString "cf")
      [polyDivVar "top", polyDivVar "linv"] polyDivTail (A d0) inverse hc ctx.inverseCanonical
      (by simp [polyDivVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, htD, hiD]) hmul
  have hlR : PolyDivLocals resumed.locals a b quotient d0 d1 := by
    rw [hlocals]; exact hlD.update_temp (ofString "cf") cf.toValue (Or.inr rfl)
  have hcfR : resumed.locals.lookup (ofString "cf") = some cf.toValue := by
    simp [hlocals, HolFiniteMapExact.lookup_update, FUPDATE]
  have hmemR : resumed.memory = s.memory := hmem
  have hdomainR : resumed.memaddrs = s.memaddrs := hdomain
  obtain ⟨C, after, hmC_in, hmB_in, hmQ_in, hrange, hdegC, hloc_in, hzeroMem, hframe_in⟩ :=
    polyDivTail_exact_none resumed inner a b quotient d0 d1 A B Q cf h0 ctx.bound hle
      (hcode.trans hc) hlR hcfR hcfCanon
      (by rw [hdomainR]; exact hi.domainA) (by rw [hdomainR]; exact hi.domainB)
      (by rw [hdomainR]; exact hi.domainQ)
      (by rw [hmemR]; exact hmA) (by rw [hmemR]; exact hi.divisor) (by rw [hmemR]; exact hmQ)
      ctx.separateAB ctx.separateAQ ctx.separateQB ctx.aligned ctx.nonwrapping htail
  have hfinalMem : post.memory = inner.memory := by rw [hrestore]; exact hpostMem
  have hfinalD0 : post.locals.lookup (ofString "d0") = some (.val (.word after)) := by
    rw [hrestore]
    change (HolFiniteMapExact.resVarEq postTop.locals (ofString "top", s.locals.lookup (ofString "top"))).lookup
      (ofString "d0") = _
    simp [PanRunBounded.resVarEq_lookup, hpostLocals, hloc_in, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "d0" ≠ ofString "top" by decide, show ofString "d0" ≠ ofString "cf" by decide]
  have hmC : MemoryPolynomial post.memory a C := by rw [hfinalMem]; exact hmC_in
  have hmB : MemoryPolynomial post.memory b B := by rw [hfinalMem]; exact hmB_in
  let Q' : Nat → Limbs256 := fun j => if j = d0 - d1 then cf else Q j
  have hmQ' : MemoryPolynomial post.memory quotient Q' := by rw [hfinalMem]; exact hmQ_in
  have hframe : ∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x := by
    intro x hxa hxq
    rw [hfinalMem, hframe_in x hxa hxq, hmemR]
  have hinv_post : PolyDivGenInvariant a b quotient d1 B inverse post := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmB, ⟨C, Q', after, hmC, hmQ', hdegC, hfinalD0⟩⟩
    · exact (polyDivBody_keeps s post (ofString "r0") (by simp) hr_orig).trans hi.r0
    · exact (polyDivBody_keeps s post (ofString "r1") (by simp) hr_orig).trans hi.r1
    · exact (polyDivBody_keeps s post (ofString "q") (by simp) hr_orig).trans hi.q
    · exact (polyDivBody_keeps s post (ofString "d1") (by simp) hr_orig).trans hi.degree1
    · exact (polyDivBody_keeps s post (ofString "linv") (by simp) hr_orig).trans hi.linv
    · rw [hmeta.2.1]; exact hi.domainA
    · rw [hmeta.2.1]; exact hi.domainB
    · rw [hmeta.2.1]; exact hi.domainQ
  have hr_before := polyDivReviewedStateRank_represented s a b quotient d0 d1 (A d0) (Q (d0 - d1))
    h0 ctx.positive hle hl (hmA d0 h0) (hmQ (d0 - d1) (by omega))
  refine ⟨hinv_post, ?_, hframe⟩
  -- Case split on whether (A d0) is a multiple of fqModulus
  by_cases hmult : (A d0).toNat % fqModulus.toNat = 0
  · -- Modulus multiple: cf = 0
    have hcfzero : cf.toNat = 0 :=
      fqMultiple_product_zero (A d0).toNat inverse.toNat cf.toNat hmult hcfCanon hprod
    have hcfeq : cf = fqZeroLimbs := limbs256_eq_zero cf hcfzero
    have hmem_zero : post.memory = writeU256 s.memory (coefficientAddress quotient (d0 - d1)) fqZeroLimbs := by
      rw [hfinalMem, hzeroMem hcfzero, hmemR, hcfeq]
    have hC_A : ∀ j, j < 13 → C j = A j := by
      intro j hj
      have hc1 := hmC j hj
      rw [hmem_zero] at hc1
      have hc2 := writeCoefficient_disjoint s.memory quotient a A (d0 - d1) fqZeroLimbs (by omega)
        (polynomialDisjoint_symm a quotient ctx.separateAQ) hmA j hj
      exact (polynomialMemoryCoefficient_read _ a j (C j) hc1).symm.trans
        (polynomialMemoryCoefficient_read _ a j (A j) hc2)
    have hdegA' : PolynomialDegreeValue A (.val (.word after)) := by
      rcases hdegC with ⟨he, hz⟩ | ⟨j, hj, he, hjnz, hab⟩
      · exact Or.inl ⟨he, fun j hj => by rw [← hC_A j hj]; exact hz j hj⟩
      · exact Or.inr ⟨j, hj, he, by rw [← hC_A j hj]; exact hjnz,
          fun k hjk hk => by rw [← hC_A k hk]; exact hab k hjk hk⟩
    have hafter_eq : ValueHOL.val (.word after) = .val (.word (BitVec.ofNat 64 d0)) :=
      polynomialDegreeValue_of_top A d0 (.val (.word after)) h0 hd0_nz hbelow hdegA'
    have hafter_w : after = BitVec.ofNat 64 d0 := by
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using hafter_eq
    have hlocals_eq : post.locals = s.locals := by
      rw [hrestore]
      change HolFiniteMapExact.resVarEq postTop.locals (ofString "top", s.locals.lookup (ofString "top")) = s.locals
      rw [hpostLocals, hloc_in, hafter_w, hlocals]
      apply HolFiniteMapExact.ext
      funext key
      by_cases hk1 : key = ofString "top"
      · subst key; simp [PanRunBounded.resVarEq_lookup]
      · by_cases hk2 : key = ofString "cf"
        · subst key
          simp [PanRunBounded.resVarEq_lookup, declared, setVarHOLFinite,
            HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cf" ≠ ofString "top" by decide,
            show ofString "top" ≠ ofString "cf" by decide,
            show ofString "d0" ≠ ofString "cf" by decide]
        · by_cases hk3 : key = ofString "d0"
          · subst key
            simpa [PanRunBounded.resVarEq_lookup, declared, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "d0" ≠ ofString "top" by decide,
              show ofString "d0" ≠ ofString "cf" by decide] using hl.degree0.symm
          · simp [PanRunBounded.resVarEq_lookup, declared, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE,
              hk1, hk2, hk3, Ne.symm hk1, Ne.symm hk2, Ne.symm hk3]
    by_cases hslot0 : (Q (d0 - d1)).toNat = 0
    · -- Phase 0: SameHead!
      have hslot_eq : Q (d0 - d1) = fqZeroLimbs := limbs256_eq_zero _ hslot0
      have hm_same : post.memory = s.memory := by
        rw [hmem_zero, writeU256_same s.memory _ fqZeroLimbs (hslot_eq ▸ hmQ (d0 - d1) (by omega))]
      exact Or.inr (state_eq_of_arithContext s post hcontext hm_same hlocals_eq)
    · -- Phase 1 -> Phase 0: cleanup drop!
      left
      have hl_post : PolyDivLocals post.locals a b quotient d0 d1 := by rw [hlocals_eq]; exact hl
      have hQ'_slot : Q' (d0 - d1) = fqZeroLimbs := by simp [Q', hcfeq]
      rw [polyDivReviewedStateRank_represented post a b quotient d0 d1 (C d0) fqZeroLimbs
            h0 ctx.positive hle hl_post (hmC d0 h0) (hQ'_slot ▸ hmQ' (d0 - d1) (by omega)),
          hC_A d0 h0, hr_before]
      exact reviewedDivisionRank_cleanup fqModulus.toNat d0 d1 1 (A d0).toNat (Q (d0 - d1)).toNat
        hd0_nz hmult hslot0
  · -- Phase 2: (A d0) % p ≠ 0!
    left
    have hsum : d0 - d1 + d1 = d0 := Nat.sub_add_cancel hle
    obtain ⟨product, hpCanon, hprodB, hout⟩ := hrange.2 d1 (by omega) (Nat.le_refl d1)
    rw [hsum] at hout
    have hprod_res : product.toNat = (A d0).toNat % fqModulus.toNat :=
      fqProduct_eq_residue (A d0).toNat (B d1).toNat inverse.toNat cf.toNat product.toNat
        hpCanon ctx.inverseRelation hprod (by simpa only [Nat.mul_comm] using hprodB)
    have hCd0_mult : (C d0).toNat % fqModulus.toNat = 0 := by
      rw [hout]; exact fqSub_residue_multiple (A d0) product hprod_res
    have habove_d0 : ∀ k, d0 < k → k < 13 → (C k).toNat = 0 := by
      intro k hgt hk
      rw [hrange.1 k (Or.inr (by omega))]
      exact hbelow k hk (by omega)
    -- Check if post is still active in the inner loop (after >= d1 signed) or exited (after < d1 signed)
    by_cases hstill : (d1 : Int) ≤ after.toInt
    · obtain ⟨next, hnext13, hafter_eq, hCnext_nz, _⟩ :=
        polynomialDegreeValue_nonnegative C after hdegC (by omega)
      have hnext_ge : d1 ≤ next := by
        rw [hafter_eq, degreeIndex_toInt next hnext13] at hstill; omega
      have hnext_le : next ≤ d0 := by
        by_contra hgt
        exact hCnext_nz (habove_d0 next (by omega) hnext13)
      have hl_post : PolyDivLocals post.locals a b quotient next d1 :=
        ⟨hinv_post.r0, hinv_post.r1, hinv_post.q,
         by simpa only [hafter_eq] using hfinalD0, hinv_post.degree1⟩
      rw [polyDivReviewedStateRank_represented post a b quotient next d1 (C next) (Q' (next - d1))
            hnext13 ctx.positive hnext_ge hl_post (hmC next hnext13) (hmQ' (next - d1) (by omega)),
          hr_before]
      by_cases heq_next : next = d0
      · subst next
        exact reviewedDivisionRank_residue fqModulus.toNat d0 d1 1 (A d0).toNat (Q (d0 - d1)).toNat
          (C d0).toNat (Q' (d0 - d1)).toNat (Or.inr hmult) hCnext_nz hCd0_mult
      · exact reviewedDivisionRank_degree fqModulus.toNat d0 d1 next 1 (A d0).toNat (Q (d0 - d1)).toNat
          (C next).toNat (Q' (next - d1)).toNat (by decide) (Or.inr hmult) hnext_ge (by omega)
    · -- Exited inner loop: after.toInt < d1, so polyDivReviewedStateRank post = 0!
      have hr_zero : polyDivReviewedStateRank post = 0 := by
        unfold polyDivReviewedStateRank
        rw [hinv_post.r0, hinv_post.q, hfinalD0, hinv_post.degree1]
        dsimp only
        rw [if_neg]
        rintro ⟨ha13, _, hged⟩
        have hd1_64 : (BitVec.ofNat 64 d1).toNat = d1 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d1 < 2 ^ 64 by have := ctx.bound; omega)]
        rw [hd1_64] at hged
        rcases hdegC with ⟨he, _⟩ | ⟨j, hj, he, _, _⟩
        · have hw : after = 0 - 1 := by simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using he
          subst after; simp at ha13
        · have hw : after = BitVec.ofNat 64 j := by simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using he
          subst after
          rw [degreeIndex_toInt j hj] at hstill
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at hged
          omega
      rw [hr_zero, hr_before]
      have hphase2 : reviewedDivisionPhase fqModulus.toNat (A d0).toNat (Q (d0 - d1)).toNat = 2 := by
        simp [reviewedDivisionPhase, hmult]
      simp only [reviewedDivisionRank, hphase2]
      omega

/-- Clock bound `(14 + 1) * (polyDivisionBodyCost + 1)` on `polyDivLoop` for arbitrary noncanonical
represented polynomials! Uses `TerminatingProgBoundedOn.while_rank_stationary` with `N = 14`. -/
theorem polyDivLoop_stationary_bounded (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (inverse : Limbs256) (ctx : PolyDivGenContext a b quotient d1 B inverse) :
    TerminatingProgBoundedOn
      (fun s => GuestInv s ∧ PolyDivGenInvariant a b quotient d1 B inverse s)
      polyDivLoop ((14 + 1) * (polyDivisionBodyCost + 1)) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧ PolyDivGenInvariant a b quotient d1 B inverse s
  refine @TerminatingProgBoundedOn.while_rank_stationary P polyDivGuard polyDivBody
    polyDivisionBodyCost 14 polyDivReviewedStateRank
    (fun s hp => ⟨guestInv_congr (s := s) rfl rfl rfl rfl hp.1,
      polyDivGenInvariant_decClock s a b quotient d1 B inverse hp.2⟩)
    (fun s hc hp => polyDivBody_bounded s hc hp.1)
    (fun s _ _ _ => Nat.le_trans (polyDivReviewedStateRank_bound s) (by decide))
    ?_
  intro F s hc hp hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  have hw_finite : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
      some (.val (.word word)) := by
    rw [evalHOLFinite_eq_toExact]; exact hw
  have hw_dec : evalHOLFinite (decClockHOLFinite s)
      (h := fun x => Classical.propDecidable ((decClockHOLFinite s).memaddrs x)) polyDivGuard =
      some (.val (.word word)) := hw_finite
  have hn : (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue polyDivBody (by decide) (decClockHOLFinite s))
  have hr : evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody =
      (none, (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2) := Prod.ext hn rfl
  obtain ⟨hinv', hstep, _⟩ := polyDivBody_stationary_step (decClockHOLFinite s)
    (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2 a b quotient d1 B inverse ctx hc
    (polyDivGenInvariant_decClock s a b quotient d1 B inverse hp.2) word hw_dec hnz hr
  have hrank_dec : polyDivReviewedStateRank (decClockHOLFinite s) = polyDivReviewedStateRank s := rfl
  rw [hrank_dec] at hstep
  refine ⟨⟨guestInv_evaluate (decClockHOLFinite s) polyDivBody
      (guestInv_congr (s := s) rfl rfl rfl rfl hp.1), hinv'⟩, ?_⟩
  rcases hstep with hlt | hsame
  · exact Or.inl hlt
  · refine Or.inr (Or.inl ?_)
    have hs_dec : { decClockHOLFinite s with
        clock := (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2.clock } =
        { s with clock := (evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody).2.clock } := rfl
    exact hsame.trans hs_dec

/-- Normal-exit postcondition of `polyDivLoop` under `PolyDivGenInvariant` (by clock induction,
because stationary repeats never exit with `none`!). -/
theorem polyDivLoop_stationary_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (inverse : Limbs256)
    (ctx : PolyDivGenContext a b quotient d1 B inverse)
    (hc : s.code = originalRuntimeCode) (hi : PolyDivGenInvariant a b quotient d1 B inverse s)
    (hr : evaluateHOLFiniteState s polyDivLoop = (none, post)) :
    PolyDivGenInvariant a b quotient d1 B inverse post ∧
      (∃ degree : BitVec 64, post.locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
        degree.toInt < (d1 : Int)) ∧
      (∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x) := by
  have hall : ∀ k (s : PanSemStateFiniteExact 64 F), s.clock ≤ k →
      s.code = originalRuntimeCode → PolyDivGenInvariant a b quotient d1 B inverse s →
      evaluateHOLFiniteState s polyDivLoop = (none, post) →
      PolyDivGenInvariant a b quotient d1 B inverse post ∧
        (∃ degree : BitVec 64, post.locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
          degree.toInt < (d1 : Int)) ∧
        (∀ x, PolynomialOutside a x → PolynomialOutside quotient x → post.memory x = s.memory x) := by
    intro k
    induction k with
    | zero =>
      intro s hk hc hi hr
      obtain ⟨A, Q, degree, hmA, hmQ, hdegree, hlocal⟩ := hi.dividend
      rw [polyDivLoop, evaluateHOLFiniteState_while_fixClockRewrite] at hr
      have hg : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
          some (.val (.word (if wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) then 1 else 0))) := by
        simp [evalHOLFinite, evalHOLExact, polyDivGuard, polyDivVar, hlocal, hi.degree1]
      rw [hg] at hr; dsimp only at hr
      by_cases hcmp : wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) = true
      · have hz : s.clock = 0 := by omega
        simp [hcmp, hz] at hr
      · rw [if_neg hcmp, if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
        have he : s = post := (Prod.mk.inj hr).2
        subst post
        have hslt : degree.slt (BitVec.ofNat 64 d1) = true := by
          simpa only [wordCmpHOL, signed_less_eq_stat, Bool.not_eq_true', Bool.eq_false_iff, not_not] using hcmp
        have hlt := BitVec.slt_iff_toInt_lt.mp hslt
        rw [degreeIndex_toInt d1 ctx.bound] at hlt
        exact ⟨hi, ⟨degree, hlocal, hlt⟩, fun _ _ _ => rfl⟩
    | succ k ih =>
      intro s hk hc hi hr
      obtain ⟨A, Q, degree, hmA, hmQ, hdegree, hlocal⟩ := hi.dividend
      rw [polyDivLoop, evaluateHOLFiniteState_while_fixClockRewrite] at hr
      have hg : evalHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) polyDivGuard =
          some (.val (.word (if wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) then 1 else 0))) := by
        simp [evalHOLFinite, evalHOLExact, polyDivGuard, polyDivVar, hlocal, hi.degree1]
      rw [hg] at hr; dsimp only at hr
      by_cases hcmp : wordCmpHOL .notLess degree (BitVec.ofNat 64 d1) = true
      · rw [if_pos hcmp, if_pos (show (1 : BitVec 64) ≠ 0 by decide)] at hr
        by_cases hclock : s.clock = 0
        · simp [hclock] at hr
        · rw [if_neg hclock] at hr
          rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) polyDivBody with ⟨result, mid⟩
          rw [hbody] at hr
          cases result with
          | none =>
            have hactive : evalHOLFinite (decClockHOLFinite s)
                (h := fun x => Classical.propDecidable ((decClockHOLFinite s).memaddrs x)) polyDivGuard =
                some (.val (.word 1)) := by
              simp [evalHOLFinite, evalHOLExact, polyDivGuard, polyDivVar, decClockHOLFinite,
                hlocal, hi.degree1, hcmp]
            obtain ⟨hi_mid, _, hframe_step⟩ := polyDivBody_stationary_step (decClockHOLFinite s) mid
              a b quotient d1 B inverse ctx hc
              (polyDivGenInvariant_decClock s a b quotient d1 B inverse hi) 1 hactive (by decide) hbody
            have hmeta := evaluateHOLFiniteState_metadata (decClockHOLFinite s) polyDivBody
            rw [hbody] at hmeta
            have hclk_le := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) polyDivBody
            rw [hbody] at hclk_le
            change mid.clock ≤ s.clock - 1 at hclk_le
            obtain ⟨hi', hexit, hframe_rest⟩ := ih mid (by omega) (hmeta.1.trans hc) hi_mid hr
            refine ⟨hi', hexit, ?_⟩
            intro x hxa hxq
            rw [hframe_rest x hxa hxq, hframe_step x hxa hxq]
            rfl
          | some r =>
            cases r with
            | «continue» =>
              have hno := evaluate_noTopContinue polyDivBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno; exact False.elim (hno rfl)
            | «break» =>
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                polyDivBody (by decide) (decClockHOLFinite s)
              rw [hbody] at hno; exact False.elim (hno rfl)
            | _ => simp at hr
      · rw [if_neg hcmp, if_neg (show ¬ (0 : BitVec 64) ≠ 0 by simp)] at hr
        have he : s = post := (Prod.mk.inj hr).2
        subst post
        have hslt : degree.slt (BitVec.ofNat 64 d1) = true := by
          simpa only [wordCmpHOL, signed_less_eq_stat, Bool.not_eq_true', Bool.eq_false_iff, not_not] using hcmp
        have hlt := BitVec.slt_iff_toInt_lt.mp hslt
        rw [degreeIndex_toInt d1 ctx.bound] at hlt
        exact ⟨hi, ⟨degree, hlocal, hlt⟩, fun _ _ _ => rfl⟩
  exact hall s.clock s (Nat.le_refl _) hc hi hr

/-- Generalized entry context for `polyDivPrepare` without `CanonicalPolynomial B`. -/
structure PolyDivGenEntryContext (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) : Prop where
  positive : 0 < d1
  bound : d1 < 13
  degree : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d1)))
  separateAB : PolynomialDisjoint a b
  separateAQ : PolynomialDisjoint a quotient
  separateQB : PolynomialDisjoint quotient b
  aligned : a.toNat % 8 = 0
  nonwrapping : a.toNat + 416 ≤ 2 ^ 64

/-- Generalized entry invariant for `polyDivPrepare` without `CanonicalPolynomial` on `A`, `B`, `Q`. -/
structure PolyDivGenEntryInvariant {F : Type} (a b quotient : BitVec 64) (d1 : Nat)
    (B : Nat → Limbs256) (s : PanSemStateFiniteExact 64 F) : Prop where
  r0 : s.locals.lookup (ofString "r0") = some (.val (.word a))
  r1 : s.locals.lookup (ofString "r1") = some (.val (.word b))
  q : s.locals.lookup (ofString "q") = some (.val (.word quotient))
  degree1 : s.locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1)))
  domainA : DomainPolynomial s.memaddrs a
  domainB : DomainPolynomial s.memaddrs b
  domainQ : DomainPolynomial s.memaddrs quotient
  divisor : MemoryPolynomial s.memory b B
  dividend : ∃ (A Q : Nat → Limbs256) (degree : BitVec 64),
    MemoryPolynomial s.memory a A ∧ MemoryPolynomial s.memory quotient Q ∧
    PolynomialDegreeValue A (.val (.word degree)) ∧
    s.locals.lookup (ofString "d0") = some (.val (.word degree))

/-- `polyDivPrepare` establishes `PolyDivGenContext` and `PolyDivGenInvariant` without canonicality. -/
theorem polyDivPrepare_gen_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (cont : ProgHOL 64)
    (ctx : PolyDivGenEntryContext a b quotient d1 B)
    (hc : state.code = originalRuntimeCode) (hi : PolyDivGenEntryInvariant a b quotient d1 B state)
    (hr : evaluateHOLFiniteState state (polyDivPrepare cont) = (none, post)) :
    ∃ (inverse : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      PolyDivGenContext a b quotient d1 B inverse ∧
      PolyDivGenInvariant a b quotient d1 B inverse resumed ∧
      resumed.code = state.code ∧ resumed.memory = state.memory ∧ resumed.memaddrs = state.memaddrs ∧
      (∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
        resumed.locals.lookup name = state.locals.lookup name) ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧ post.memory = inner.memory ∧
      ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
        post.locals.lookup name = inner.locals.lookup name := by
  unfold polyDivPrepare at hr
  obtain ⟨lead, postLead, hinit, _, hinverse, hrestore⟩ := arith_dec_none_state hr
  have haddr : arithEval state polyDivLeadAddress = some (.val (.word (coefficientAddress b d1))) := by
    rw [← coefficientAddress_source]
    simp [arithEval, polyDivLeadAddress, polyDivVar, evalHOLExact, evalListHOLExact, hi.r1, hi.degree1,
      wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
  have hload := eval_load_u256 state polyDivLeadAddress (coefficientAddress b d1) (B d1)
    haddr (hi.domainB d1 ctx.bound) (hi.divisor d1 ctx.bound)
  have hlead : lead = (B d1).toValue := Option.some.inj (hinit.symm.trans hload)
  subst lead
  let declared := setVarHOLFinite (ofString "lead") (B d1).toValue state
  have hleadD : declared.locals.lookup (ofString "lead") = some (B d1).toValue := by
    simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨inverse, resumed, inner, hcanon, hinv, hlocals, hcode, hmem, hdomain, hcont, hpostLocals, hpostMem⟩ :=
    fqInverse_decCall_none_frame (s := declared) (post := postLead) (ofString "linv")
      [polyDivVar "lead"] cont (B d1) hc (polynomialDegreeValue_at_index B d1 ctx.bound ctx.degree)
      (by simp [polyDivVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, hleadD]) hinverse
  have hkeep : ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
      resumed.locals.lookup name = state.locals.lookup name := by
    intro name hnLead hnInv
    simp [hlocals, declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      Ne.symm hnLead, Ne.symm hnInv]
  have hInvLocal : resumed.locals.lookup (ofString "linv") = some inverse.toValue := by
    simp [hlocals, HolFiniteMapExact.lookup_update, FUPDATE]
  have hinvariant : PolyDivGenInvariant a b quotient d1 B inverse resumed := by
    refine ⟨(hkeep _ (by decide) (by decide)).trans hi.r0,
      (hkeep _ (by decide) (by decide)).trans hi.r1,
      (hkeep _ (by decide) (by decide)).trans hi.q,
      (hkeep _ (by decide) (by decide)).trans hi.degree1,
      hInvLocal, hdomain ▸ hi.domainA, hdomain ▸ hi.domainB, hdomain ▸ hi.domainQ,
      hmem ▸ hi.divisor, ?_⟩
    obtain ⟨A, Q, degree, hmA, hmQ, hdA, hlocal⟩ := hi.dividend
    exact ⟨A, Q, degree, hmem ▸ hmA, hmem ▸ hmQ, hdA, (hkeep _ (by decide) (by decide)).trans hlocal⟩
  have hcontext : PolyDivGenContext a b quotient d1 B inverse :=
    ⟨ctx.positive, ctx.bound, ctx.degree, hcanon, hinv,
      ctx.separateAB, ctx.separateAQ, ctx.separateQB, ctx.aligned, ctx.nonwrapping⟩
  refine ⟨inverse, resumed, inner, hcontext, hinvariant, hcode, hmem, hdomain, hkeep, hcont, ?_, ?_⟩
  · rw [hrestore]; exact hpostMem
  · intro name hnLead hnInv
    rw [hrestore, InitECandidate.Solver.PanRunBounded.resVarEq_lookup]
    simp only [hnLead, ↓reduceIte]
    rw [hpostLocals, InitECandidate.Solver.PanRunBounded.resVarEq_lookup]
    simp [hnInv]

/-- Combined `polyDivPrepare (.seq polyDivLoop cont)` normal-exit step under `PolyDivGenEntryInvariant`. -/
theorem polyDivPreparedLoop_gen_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (cont : ProgHOL 64)
    (ctx : PolyDivGenEntryContext a b quotient d1 B)
    (hc : state.code = originalRuntimeCode) (hi : PolyDivGenEntryInvariant a b quotient d1 B state)
    (hr : evaluateHOLFiniteState state (polyDivPrepare (.seq polyDivLoop cont)) = (none, post)) :
    ∃ (inverse : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      PolyDivGenContext a b quotient d1 B inverse ∧
      PolyDivGenInvariant a b quotient d1 B inverse resumed ∧
      (∃ degree : BitVec 64, resumed.locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
        degree.toInt < (d1 : Int)) ∧
      resumed.code = state.code ∧
      (∀ name, name ∈ [ofString "r0", ofString "r1", ofString "s0", ofString "s1", ofString "tmp", ofString "q"] →
        resumed.locals.lookup name = state.locals.lookup name) ∧
      (∀ x, PolynomialOutside a x → PolynomialOutside quotient x → resumed.memory x = state.memory x) ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧ post.memory = inner.memory ∧
      ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
        post.locals.lookup name = inner.locals.lookup name := by
  obtain ⟨inverse, entry, inner, hctx, hentry, hcode, hmem, _, hkeep, hseq, hfinalMem, hfinalLocals⟩ :=
    polyDivPrepare_gen_none state post a b quotient d1 B (.seq polyDivLoop cont) ctx hc hi hr
  obtain ⟨resumed, hloop, hcont⟩ := arith_seq_none hseq
  obtain ⟨hinv, hexit, hframe⟩ :=
    polyDivLoop_stationary_none entry resumed a b quotient d1 B inverse hctx (hcode.trans hc) hentry hloop
  have hmeta := evaluateHOLFiniteState_metadata entry polyDivLoop
  rw [hloop] at hmeta
  have hkeepLoop : ∀ name, name ∈ [ofString "r0", ofString "r1", ofString "s0", ofString "s1", ofString "tmp", ofString "q"] →
      resumed.locals.lookup name = state.locals.lookup name := by
    intro name hmem_n
    have havoid : avoidsLocal name polyDivLoop = true := by
      rcases List.mem_cons.mp hmem_n with rfl | hmem_n
      · decide
      · rcases List.mem_cons.mp hmem_n with rfl | hmem_n
        · decide
        · rcases List.mem_cons.mp hmem_n with rfl | hmem_n
          · decide
          · rcases List.mem_cons.mp hmem_n with rfl | hmem_n
            · decide
            · rcases List.mem_cons.mp hmem_n with rfl | hmem_n
              · decide
              · rcases List.mem_cons.mp hmem_n with rfl | hmem_n
                · decide
                · cases hmem_n
    have hfl := evaluate_avoidsLocal_flowing name polyDivLoop havoid entry
    rw [hloop] at hfl
    have heq_entry : resumed.locals.lookup name = entry.locals.lookup name := hfl (Or.inl rfl)
    refine heq_entry.trans (hkeep name ?_ ?_)
    · rintro rfl; exact absurd hmem_n (by decide)
    · rintro rfl; exact absurd hmem_n (by decide)
  refine ⟨inverse, resumed, inner, hctx, hinv, hexit, hmeta.1.trans hcode, hkeepLoop, ?_, hcont, hfinalMem, hfinalLocals⟩
  intro x hxa hxq
  rw [hframe x hxa hxq, hmem]

end InitECandidate.Solver.Wave8GuestInv.Arith
