import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionLoop
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseScopedFrame

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
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

def polyDivLeadAddress : ExpHOL 64 :=
  .op .add [polyDivVar "r1",.panop .mul [polyDivVar "d1",.const 32]]
def polyDivPrepare (cont : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "lead") arithU256Shape (.load arithU256Shape polyDivLeadAddress)
    (.decCall (ofString "linv") arithU256Shape (ofString "fq_inv") [polyDivVar "lead"] cont)

def polyDivAfterLoop : ProgHOL 64 :=
  polyDivSourceAt (arithSourceBody Guest.Software.guestFn_fq12_inv)
    ([false,false,false,false,false,false,false] ++
     [true,true,true,true,true,true,true,true,true] ++
     [false,false,false,true,false,true,false,false,true])

theorem polyDivPrepare_source_eq :
    polyDivSourceAt (arithSourceBody Guest.Software.guestFn_fq12_inv)
      ([false,false,false,false,false,false,false] ++
       [true,true,true,true,true,true,true,true,true] ++
       [false,false,false,true,false,true]) =
      polyDivPrepare (.seq polyDivLoop polyDivAfterLoop) := rfl

/-- Source-side entry requirements, before fq_inv supplies its output. -/
structure PolyDivEntryContext (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) : Prop where
  positive : 0 < d1
  bound : d1 < 13
  canonical : CanonicalPolynomial B
  degree : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d1)))
  separateAB : PolynomialDisjoint a b
  separateAQ : PolynomialDisjoint a quotient
  separateQB : PolynomialDisjoint quotient b
  aligned : a.toNat % 8 = 0
  nonwrapping : a.toNat + 416 ≤ 2^64

structure PolyDivEntryInvariant {F : Type} (a b quotient : BitVec 64) (d1 : Nat)
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
    CanonicalPolynomial A ∧ CanonicalPolynomial Q ∧
    MemoryPolynomial s.memory a A ∧ MemoryPolynomial s.memory quotient Q ∧
    PolynomialDegreeValue A (.val (.word degree)) ∧
    s.locals.lookup (ofString "d0") = some (.val (.word degree))

theorem polynomialDegreeValue_at_index (B : Nat → Limbs256) (d : Nat) (hd : d < 13)
    (h : PolynomialDegreeValue B (.val (.word (BitVec.ofNat 64 d)))) : (B d).toNat ≠ 0 := by
  rcases h with ⟨he,hzero⟩ | ⟨j,hj,he,hne,habove⟩
  · have hw : BitVec.ofNat 64 d = 0-1 := by
      simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    have hi := congrArg BitVec.toInt hw
    rw [degreeIndex_toInt d hd] at hi
    change (d : Int) = -1 at hi
    omega
  · have hw : BitVec.ofNat 64 d = BitVec.ofNat 64 j := by
      simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using he
    have hi := congrArg BitVec.toNat hw
    simp only [BitVec.toNat_ofNat] at hi
    have hjd : j = d := by omega
    simpa only [hjd] using hne

/-- A successful actual leading-coefficient load and scoped fq_inv call
establish the division invariant, without an assumed inverse relation. -/
theorem polyDivPrepare_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (cont : ProgHOL 64)
    (ctx : PolyDivEntryContext a b quotient d1 B)
    (hc : state.code = originalRuntimeCode) (hi : PolyDivEntryInvariant a b quotient d1 B state)
    (hr : evaluateHOLFiniteState state (polyDivPrepare cont) = (none,post)) :
    ∃ (inverse : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      PolyDivContext a b quotient d1 B inverse ∧
      PolyDivInvariant a b quotient d1 B inverse resumed ∧
      resumed.code = state.code ∧ resumed.memory = state.memory ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧ post.memory = inner.memory ∧
      ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
        post.locals.lookup name = inner.locals.lookup name := by
  unfold polyDivPrepare at hr
  obtain ⟨lead,postLead,hinit,hshape,hinverse,hrestore⟩ := arith_dec_none_state hr
  have haddr : arithEval state polyDivLeadAddress = some (.val (.word (coefficientAddress b d1))) := by
    rw [← coefficientAddress_source]
    simp [arithEval,polyDivLeadAddress,polyDivVar,evalHOLExact,evalListHOLExact,hi.r1,hi.degree1,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]
  have hload := eval_load_u256 state polyDivLeadAddress (coefficientAddress b d1) (B d1)
    haddr (hi.domainB d1 ctx.bound) (hi.divisor d1 ctx.bound)
  have hlead : lead = (B d1).toValue := Option.some.inj (hinit.symm.trans hload)
  subst lead
  let declared := setVarHOLFinite (ofString "lead") (B d1).toValue state
  have hleadD : declared.locals.lookup (ofString "lead") = some (B d1).toValue := by
    simp [declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨inverse,resumed,inner,hcanon,hinv,hlocals,hcode,hmem,hdomain,hcont,hpostLocals,hpostMem⟩ :=
    fqInverse_decCall_none_frame (s := declared) (post := postLead) (ofString "linv")
      [polyDivVar "lead"] cont (B d1) hc (polynomialDegreeValue_at_index B d1 ctx.bound ctx.degree)
      (by simp [polyDivVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,hleadD]) hinverse
  have hmemR : resumed.memory = state.memory := hmem
  have hdomainR : resumed.memaddrs = state.memaddrs := hdomain
  have hkeep : ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
      resumed.locals.lookup name = state.locals.lookup name := by
    intro name hnLead hnInv
    simp [hlocals,declared,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm hnLead,Ne.symm hnInv]
  have hInvLocal : resumed.locals.lookup (ofString "linv") = some inverse.toValue := by
    simp [hlocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have hinvariant : PolyDivInvariant a b quotient d1 B inverse resumed := by
    refine ⟨?_,?_,?_,?_,hInvLocal,?_,?_,?_,?_,?_⟩
    · exact (hkeep (ofString "r0") (by decide) (by decide)).trans hi.r0
    · exact (hkeep (ofString "r1") (by decide) (by decide)).trans hi.r1
    · exact (hkeep (ofString "q") (by decide) (by decide)).trans hi.q
    · exact (hkeep (ofString "d1") (by decide) (by decide)).trans hi.degree1
    · rw [hdomainR]; exact hi.domainA
    · rw [hdomainR]; exact hi.domainB
    · rw [hdomainR]; exact hi.domainQ
    · rw [hmemR]; exact hi.divisor
    · obtain ⟨A,Q,degree,hA,hQ,hmA,hmQ,hdegree,hlocal⟩ := hi.dividend
      refine ⟨A,Q,degree,hA,hQ,?_,?_,hdegree,?_⟩
      · rw [hmemR]; exact hmA
      · rw [hmemR]; exact hmQ
      · exact (hkeep (ofString "d0") (by decide) (by decide)).trans hlocal
  refine ⟨inverse,resumed,inner,
    ⟨ctx.positive,ctx.bound,ctx.canonical,ctx.degree,hcanon,hinv,
      ctx.separateAB,ctx.separateAQ,ctx.separateQB,ctx.aligned,ctx.nonwrapping⟩,
    hinvariant,hcode,hmemR,hcont,?_,?_⟩
  · rw [hrestore]; exact hpostMem
  · intro name hnLead hnInv
    rw [hrestore]
    change (HolFiniteMapExact.resVarEq postLead.locals (ofString "lead",state.locals.lookup (ofString "lead"))).lookup name = _
    simp [PanRunBounded.resVarEq_lookup,hpostLocals,hnLead,hnInv]

end InitECandidate.Solver.Wave8GuestInv.Arith
