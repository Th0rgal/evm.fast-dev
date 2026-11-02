import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.HybridScoreBounds
import InitECandidate.Solver.B2PostDecls
import InitECandidate.Solver.B2Oracle
import InitECandidate.Solver.HeapPotential
import InitE.Challenge
import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitE.SourceMainFacts
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAssembly

set_option autoImplicit false

namespace InitECandidate.Solver.UniformSourceClock

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.PanPropsEvalStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

def maxCoveredGas : Nat := 200000000

def uniformSourceClock : Nat := HybridScoreBounds.WORST_CASE_block

theorem maxCoveredGas_eq : maxCoveredGas = 200000000 := rfl

theorem uniformSourceClock_eq : uniformSourceClock = 459564194 := rfl

theorem evaluateHOLFiniteState_clock_sub {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (t : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
    (ck : Nat)
    (hrun : evaluateHOLFiniteState t p = (res, { st with clock := st.clock + ck }))
    (hnt : res ≠ some .timeOut) :
    evaluateHOLFiniteState { t with clock := t.clock - ck } p = (res, st) := by
  have hpair : evaluateHOLFinitePair (ofPanSemFinite t) p =
      (res, { ofPanSemFinite st with clock := (ofPanSemFinite st).clock + ck }) := by
    simp only [evaluateHOLFinitePair, toPanSemFinite_ofPanSemFinite, hrun]
    rfl
  have hsub := evaluateClockSubHOLFinite p (ofPanSemFinite t) res (ofPanSemFinite st) ck hpair hnt
  have heq := congrArg (fun q => (q.1, q.2.toPanSemFinite)) hsub
  simp only [evaluateHOLFinitePair, toPanSemFinite_ofPanSemFinite] at heq
  have ht : ({ ofPanSemFinite t with clock := (ofPanSemFinite t).clock - ck } :
      PanPropsEvalStateFiniteExact width σ).toPanSemFinite = { t with clock := t.clock - ck } := rfl
  rw [ht] at heq
  exact (Prod.eta (evaluateHOLFiniteState { t with clock := t.clock - ck } p)).symm.trans heq

theorem evaluateHOLFiniteState_exact_ticks_consumed {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s s_post : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (k : Nat)
    (hrun : evaluateHOLFiniteState { s with clock := k } p = (res, s_post))
    (hnt : res ≠ some .timeOut) :
    evaluateHOLFiniteState { s with clock := k - s_post.clock } p =
      (res, { s_post with clock := 0 }) := by
  have hpost : ({ { s_post with clock := 0 } with clock := (0 : Nat) + s_post.clock } :
      PanSemStateFiniteExact width σ) = s_post := by
    cases s_post
    simp only [Nat.zero_add]
  have hrun' : evaluateHOLFiniteState { s with clock := k } p =
      (res, { { s_post with clock := 0 } with clock := ({ s_post with clock := 0 }).clock + s_post.clock }) := by
    simpa only [hpost] using hrun
  exact evaluateHOLFiniteState_clock_sub p { s with clock := k } res
    { s_post with clock := 0 } s_post.clock hrun' hnt

theorem evaluateHOLFiniteState_ticks_consumed_invariant {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s s₁ s₂ : PanSemStateFiniteExact width σ)
    (res₁ res₂ : Option (PanSemResultExact width)) (k₁ k₂ : Nat)
    (hrun₁ : evaluateHOLFiniteState { s with clock := k₁ } p = (res₁, s₁))
    (hnt₁ : res₁ ≠ some .timeOut)
    (hrun₂ : evaluateHOLFiniteState { s with clock := k₂ } p = (res₂, s₂))
    (hnt₂ : res₂ ≠ some .timeOut) :
    res₁ = res₂ ∧
    { s₁ with clock := 0 } = { s₂ with clock := 0 } ∧
    k₁ - s₁.clock = k₂ - s₂.clock := by
  have hle₁ := evaluateHOLFiniteState_clock_le_result { s with clock := k₁ } p res₁ s₁ hrun₁
  have hle₂ := evaluateHOLFiniteState_clock_le_result { s with clock := k₂ } p res₂ s₂ hrun₂
  simp only at hle₁ hle₂
  have hadd₁ := panPropsEvaluateAddClockEq p { s with clock := k₁ } res₁ s₁ k₂ ⟨hrun₁, hnt₁⟩
  have hadd₂ := panPropsEvaluateAddClockEq p { s with clock := k₂ } res₂ s₂ k₁ ⟨hrun₂, hnt₂⟩
  simp only [Nat.add_comm k₂ k₁] at hadd₂
  rw [hadd₁] at hadd₂
  injection hadd₂ with hres hst
  have hclk : s₁.clock + k₂ = s₂.clock + k₁ := congrArg PanSemStateFiniteExact.clock hst
  have hzero : ({ s₁ with clock := 0 } : PanSemStateFiniteExact width σ) =
      { s₂ with clock := 0 } := by
    cases s₁
    cases s₂
    injection hst with h1 h2 h3 h4 h5 h6 h7 h8 _ h10 h11 h12 h13
    subst h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13
    rfl
  exact ⟨hres, hzero, by omega⟩

theorem evaluateHOLFiniteState_not_timeOut_at_clock_iff {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s s_post : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (k K : Nat)
    (hrun : evaluateHOLFiniteState { s with clock := k } p = (res, s_post))
    (hnt : res ≠ some .timeOut) :
    (evaluateHOLFiniteState { s with clock := K } p).1 ≠ some .timeOut ↔
      k - s_post.clock ≤ K := by
  constructor
  · intro hntK
    rcases hrunK : evaluateHOLFiniteState { s with clock := K } p with ⟨resK, sK⟩
    rw [hrunK] at hntK
    have hleK := evaluateHOLFiniteState_clock_le_result { s with clock := K } p resK sK hrunK
    simp only at hleK
    obtain ⟨_, _, hticks⟩ :=
      evaluateHOLFiniteState_ticks_consumed_invariant p s s_post sK res resK k K
        hrun hnt hrunK hntK
    omega
  · intro hle
    have hexact := evaluateHOLFiniteState_exact_ticks_consumed p s s_post res k hrun hnt
    have hpad := panPropsEvaluateAddClockEq p
      { s with clock := k - s_post.clock } res { s_post with clock := 0 }
      (K - (k - s_post.clock)) ⟨hexact, hnt⟩
    have hclk : k - s_post.clock + (K - (k - s_post.clock)) = K := by omega
    simp only [hclk] at hpad
    rw [hpad]
    exact hnt

theorem source_terminate_minimal_input_clock
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hsource : sourceBehaviour input = .terminate outcome events) :
    ∃ (stCtxt : StructContextExact)
      (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
      (k_min : Nat)
      (res : Option (PanSemResultExact 64))
      (s_post : PanSemStateFiniteExact 64 Guest.HostMemory),
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls ∧
      s_decls.code = GuestCodeLookup.originalRuntimeCode ∧
      s_decls.memaddrs = ordinaryDomain ∧
      s_decls.shMemaddrs = sharedDomain ∧
      s_decls.memory = sourceMemory ∧
      s_decls.ffi = sourceFfi input ∧
      s_decls.be = false ∧
      s_decls.locals = HolFiniteMapExact.empty ∧
      s_decls.baseAddr = BitVec.ofNat 64 sourceBase ∧
      s_decls.topAddr = BitVec.ofNat 64 heapEnd ∧
      s_decls.clock = 0 ∧
      OracleConsistent sourceOracle (Guest.guestHostMemory input) s_decls.ffi ∧
      evaluateHOLFiniteState { s_decls with clock := k_min }
        (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post) ∧
      s_post.clock = 0 ∧
      panEntryClass res = .CompleteResult outcome ∧
      s_post.ffi.ioEvents = events ∧
      OracleConsistent sourceOracle (Guest.guestHostMemory input) s_post.ffi ∧
      (∀ k' : Nat, k' < k_min →
        (evaluateHOLFiniteState { s_decls with clock := k' }
          (.call none (ofString "main") [] : ProgHOL 64)).1 = some .timeOut) := by
  have hsem := Flapjack.Pancake.PanToTarget.semanticsDecls_mainFirstHOL
    (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map declToHOL) sourceHasMain
  have hterm : semanticsDecls (sourceInitialState input) (ofString "main")
      sourceDeclarations = .terminate outcome events := hsem.trans hsource
  obtain ⟨stCtxt, s_decls, hst, hdecls, -, k₀, res₀, s_post₀, hrun₀, hclass₀, hio₀⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_extract
      (sourceInitialState input) (ofString "main") sourceDeclarations
      outcome events hterm
  have hmeta := B2PostDecls.evaluateDecls_meta sourceDeclarations
    { sourceInitialState input with structs := stCtxt } s_decls
    (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a)) hdecls
  have hcode : s_decls.code = GuestCodeLookup.originalRuntimeCode := by
    rw [hmeta.code]
    exact B2PostDecls.map_ext rfl
  have hnt₀ : res₀ ≠ some .timeOut := by
    intro ht
    subst ht
    cases hclass₀
  have hexact := evaluateHOLFiniteState_exact_ticks_consumed
    (.call none (ofString "main") [] : ProgHOL 64) s_decls s_post₀ res₀ k₀ hrun₀ hnt₀
  have hffi_init : OracleConsistent sourceOracle (Guest.guestHostMemory input)
      s_decls.ffi := by
    rw [hmeta.ffi]
    exact initial_oracle_consistent sourceOracle (Guest.guestHostMemory input)
  have hffi_post : OracleConsistent sourceOracle (Guest.guestHostMemory input)
      ({ s_post₀ with clock := 0 } : PanSemStateFiniteExact 64 Guest.HostMemory).ffi := by
    have hc := B2Oracle.evaluate_consistent sourceOracle (Guest.guestHostMemory input)
      (.call none (ofString "main") [] : ProgHOL 64)
      { s_decls with clock := k₀ - s_post₀.clock } hffi_init
    rw [hexact] at hc
    exact hc
  refine ⟨stCtxt, s_decls, k₀ - s_post₀.clock, res₀, { s_post₀ with clock := 0 },
    hst, hdecls, hcode, hmeta.memaddrs, hmeta.shMemaddrs, hmeta.memory, hmeta.ffi,
    hmeta.be, hmeta.locals, hmeta.baseAddr, hmeta.topAddr, hmeta.clock, hffi_init,
    hexact, rfl, hclass₀, hio₀, hffi_post, ?_⟩
  intro k' hk'
  by_contra hnt'
  have hle := (evaluateHOLFiniteState_not_timeOut_at_clock_iff
    (.call none (ofString "main") [] : ProgHOL 64)
    s_decls { s_post₀ with clock := 0 } res₀ (k₀ - s_post₀.clock) k'
    hexact hnt₀).mp hnt'
  simp only [Nat.sub_zero] at hle
  omega

def CoveredSourceTicksConsumedBounded (K : Nat) : Prop :=
  ∀ (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
    sourceBehaviour input = .terminate outcome events →
    coveredOutcome outcome →
    ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls →
      ∀ (k : Nat) (res : Option (PanSemResultExact 64))
        (s_post : PanSemStateFiniteExact 64 Guest.HostMemory),
        evaluateHOLFiniteState { s_decls with clock := k }
          (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post) →
        res ≠ some .timeOut →
        k - s_post.clock ≤ K

def CoveredSourceHasClockWithin (K : Nat) : Prop :=
  ∀ (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
    sourceBehaviour input = .terminate outcome events →
    coveredOutcome outcome →
    ∃ (k : Nat) (stCtxt : StructContextExact)
      (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
      (res : Option (PanSemResultExact 64))
      (s_post : PanSemStateFiniteExact 64 Guest.HostMemory),
      k ≤ K ∧
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls ∧
      evaluateHOLFiniteState { s_decls with clock := k }
        (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post) ∧
      panEntryClass res = .CompleteResult outcome ∧
      s_post.ffi.ioEvents = events

def CoveredSourceUniformNotTimeOut (K : Nat) : Prop :=
  ∀ (input : Guest.InputBlob),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
    ∀ (outcome : HolOutcome) (events : List HolIoEvent),
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
        @evaluateDeclsHOLFinite 64 Guest.HostMemory _
          { sourceInitialState input with structs := stCtxt }
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
          sourceDeclarations = some s_decls →
        (evaluateHOLFiniteState { s_decls with clock := K }
          (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut

def CoveredSourceUniformTerminates (K : Nat) : Prop :=
  ∀ (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent),
    Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
    sourceBehaviour input = .terminate outcome events →
    coveredOutcome outcome →
    ∃ (stCtxt : StructContextExact)
      (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
      (res : Option (PanSemResultExact 64))
      (s_post : PanSemStateFiniteExact 64 Guest.HostMemory),
      decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _
        { sourceInitialState input with structs := stCtxt }
        (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
        sourceDeclarations = some s_decls ∧
      evaluateHOLFiniteState { s_decls with clock := K }
        (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post) ∧
      panEntryClass res = .CompleteResult outcome ∧
      s_post.ffi.ioEvents = events

theorem covered_source_has_clock_within_of_ticks_bounded {K : Nat}
    (hbound : CoveredSourceTicksConsumedBounded K) :
    CoveredSourceHasClockWithin K := by
  intro input outcome events hgas hsource hcov
  obtain ⟨stCtxt, s_decls, k_min, res, s_post, hst, hdecls,
    -, -, -, -, -, -, -, -, -, -, -, hrun, hclk0, hclass, hio, -, -⟩ :=
    source_terminate_minimal_input_clock input outcome events hsource
  have hnt : res ≠ some .timeOut := by
    intro ht
    subst ht
    cases hclass
  have hk_sub : k_min - s_post.clock ≤ K :=
    hbound input outcome events hgas hsource hcov stCtxt s_decls hst hdecls
      k_min res s_post hrun hnt
  have hk : k_min ≤ K := by omega
  exact ⟨k_min, stCtxt, s_decls, res, s_post, hk, hst, hdecls, hrun, hclass, hio⟩

theorem covered_source_uniform_not_timeOut_of_has_clock_within {K : Nat}
    (hwithin : CoveredSourceHasClockWithin K) :
    CoveredSourceUniformNotTimeOut K := by
  intro input hgas outcome events hsource hcov stCtxt s_decls hst hdecls
  obtain ⟨k, stCtxt', s_decls', res, s_post, hk, hst', hdecls', hrun, hclass, -⟩ :=
    hwithin input outcome events hgas hsource hcov
  rw [hst] at hst'
  cases hst'
  rw [hdecls] at hdecls'
  cases hdecls'
  have hnt : res ≠ some .timeOut := by
    intro ht
    subst ht
    cases hclass
  exact (evaluateHOLFiniteState_not_timeOut_at_clock_iff
    (.call none (ofString "main") [] : ProgHOL 64)
    s_decls s_post res k K hrun hnt).mpr (by omega)

theorem covered_source_uniform_terminates_of_uniform_not_timeOut {K : Nat}
    (hnt_unif : CoveredSourceUniformNotTimeOut K) :
    CoveredSourceUniformTerminates K := by
  intro input outcome events hgas hsource hcov
  have hsem := Flapjack.Pancake.PanToTarget.semanticsDecls_mainFirstHOL
    (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map declToHOL) sourceHasMain
  have hterm : semanticsDecls (sourceInitialState input) (ofString "main")
      sourceDeclarations = .terminate outcome events := hsem.trans hsource
  obtain ⟨stCtxt, s_decls, hst, hdecls, -, -⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_extract
      (sourceInitialState input) (ofString "main") sourceDeclarations
      outcome events hterm
  rcases hrunK : evaluateHOLFiniteState { s_decls with clock := K }
      (.call none (ofString "main") [] : ProgHOL 64) with ⟨res, s_post⟩
  have hnt : res ≠ some .timeOut := by
    have h := hnt_unif input hgas outcome events hsource hcov stCtxt s_decls hst hdecls
    rw [hrunK] at h
    exact h
  obtain ⟨hclass, hio⟩ :=
    SelfContainedStageBounds.semanticsDecls_terminate_at_clock
      (sourceInitialState input) (ofString "main") sourceDeclarations
      outcome events hterm stCtxt s_decls hst hdecls K res s_post hrunK hnt
  exact ⟨stCtxt, s_decls, res, s_post, hst, hdecls, hrunK, hclass, hio⟩

theorem covered_source_ticks_bounded_of_uniform_terminates {K : Nat}
    (hterm_unif : CoveredSourceUniformTerminates K) :
    CoveredSourceTicksConsumedBounded K := by
  intro input outcome events hgas hsource hcov stCtxt s_decls hst hdecls k res s_post hrun hnt
  obtain ⟨stCtxt', s_decls', resK, s_postK, hst', hdecls', hrunK, hclassK, -⟩ :=
    hterm_unif input outcome events hgas hsource hcov
  rw [hst] at hst'
  cases hst'
  rw [hdecls] at hdecls'
  cases hdecls'
  have hntK : resK ≠ some .timeOut := by
    intro ht
    subst ht
    cases hclassK
  exact (evaluateHOLFiniteState_not_timeOut_at_clock_iff
    (.call none (ofString "main") [] : ProgHOL 64)
    s_decls s_post res k K hrun hnt).mp (by rw [hrunK]; exact hntK)

theorem covered_source_ticks_bounded_iff_has_clock_within (K : Nat) :
    CoveredSourceTicksConsumedBounded K ↔ CoveredSourceHasClockWithin K :=
  ⟨covered_source_has_clock_within_of_ticks_bounded,
   fun h => covered_source_ticks_bounded_of_uniform_terminates
     (covered_source_uniform_terminates_of_uniform_not_timeOut
       (covered_source_uniform_not_timeOut_of_has_clock_within h))⟩

theorem covered_source_has_clock_within_iff_uniform_not_timeOut (K : Nat) :
    CoveredSourceHasClockWithin K ↔ CoveredSourceUniformNotTimeOut K :=
  ⟨covered_source_uniform_not_timeOut_of_has_clock_within,
   fun h => covered_source_has_clock_within_of_ticks_bounded
     (covered_source_ticks_bounded_of_uniform_terminates
       (covered_source_uniform_terminates_of_uniform_not_timeOut h))⟩

theorem covered_source_uniform_not_timeOut_iff_uniform_terminates (K : Nat) :
    CoveredSourceUniformNotTimeOut K ↔ CoveredSourceUniformTerminates K :=
  ⟨covered_source_uniform_terminates_of_uniform_not_timeOut,
   fun h => covered_source_uniform_not_timeOut_of_has_clock_within
     (covered_source_has_clock_within_of_ticks_bounded
       (covered_source_ticks_bounded_of_uniform_terminates h))⟩

theorem covered_source_ticks_bounded_iff_uniform_terminates (K : Nat) :
    CoveredSourceTicksConsumedBounded K ↔ CoveredSourceUniformTerminates K :=
  ⟨fun h => covered_source_uniform_terminates_of_uniform_not_timeOut
     (covered_source_uniform_not_timeOut_of_has_clock_within
       (covered_source_has_clock_within_of_ticks_bounded h)),
   covered_source_ticks_bounded_of_uniform_terminates⟩

theorem covered_source_terminates_at_uniform_clock
    (hbound : CoveredSourceTicksConsumedBounded uniformSourceClock) :
    ∀ (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent),
      Guest.GasLimit.declaredGasLimit input ≤ maxCoveredGas →
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∃ (stCtxt : StructContextExact)
        (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
        (res : Option (PanSemResultExact 64))
        (s_post : PanSemStateFiniteExact 64 Guest.HostMemory),
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt ∧
        @evaluateDeclsHOLFinite 64 Guest.HostMemory _
          { sourceInitialState input with structs := stCtxt }
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
          sourceDeclarations = some s_decls ∧
        evaluateHOLFiniteState { s_decls with clock := uniformSourceClock }
          (.call none (ofString "main") [] : ProgHOL 64) = (res, s_post) ∧
        panEntryClass res = .CompleteResult outcome ∧
        s_post.ffi.ioEvents = events :=
  (covered_source_ticks_bounded_iff_uniform_terminates uniformSourceClock).mp hbound

theorem covered_source_pan_not_timeOut_at_uniform_clock
    (hbound : CoveredSourceTicksConsumedBounded uniformSourceClock) :
    ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (evaluateHOLFiniteState { s_decls with clock := uniformSourceClock }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut :=
  covered_source_uniform_not_timeOut_of_has_clock_within
    (covered_source_has_clock_within_of_ticks_bounded hbound)

end InitECandidate.Solver.UniformSourceClock

