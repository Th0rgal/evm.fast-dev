import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import InitE.SourceMainFacts
import Flapjack.Pancake.PanToTarget.MainFirstSemantics
import InitECandidate.Solver.GuestCodeLookup
import InitECandidate.Solver.GuestGlobalKeep

set_option autoImplicit false

namespace InitECandidate.Solver.B2PostDecls
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Pancake.PanToTarget
open Flapjack.Basis.Pure.MlString
open InitE

theorem map_ext {α β : Type} {m₁ m₂ : HolFiniteMapExact α β} (h : m₁.lookup = m₂.lookup) :
    m₁ = m₂ := by
  cases m₁
  cases m₂
  cases h
  rfl

structure DeclsMeta {σ : Type} (s s' : PanSemStateFiniteExact 64 σ)
    (decls : List (DeclHOL 64)) : Prop where
  code : s'.code = s.code.updateList (functionsHOL decls)
  memaddrs : s'.memaddrs = s.memaddrs
  ffi : s'.ffi = s.ffi
  be : s'.be = s.be
  locals : s'.locals = s.locals
  memory : s'.memory = s.memory
  shMemaddrs : s'.shMemaddrs = s.shMemaddrs
  baseAddr : s'.baseAddr = s.baseAddr
  topAddr : s'.topAddr = s.topAddr
  clock : s'.clock = s.clock

theorem evaluateDecls_meta {σ : Type} :
    ∀ (decls : List (DeclHOL 64)) (s s' : PanSemStateFiniteExact 64 σ)
      (h : DecidablePred s.memaddrs),
      @evaluateDeclsHOLFinite 64 σ _ s h decls = some s' → DeclsMeta s s' decls := by
  intro decls
  induction decls with
  | nil =>
      intro s s' h run
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at run
      subst run
      exact ⟨map_ext rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons d rest ih =>
      intro s s' h run
      cases d with
      | name _ _ =>
          simp only [evaluateDeclsHOLFinite] at run
          have m := ih s s' h run
          exact ⟨m.code, m.memaddrs, m.ffi, m.be, m.locals, m.memory, m.shMemaddrs,
            m.baseAddr, m.topAddr, m.clock⟩
      | decl shape name expression =>
          simp only [evaluateDeclsHOLFinite] at run
          split at run
          · split at run
            · have m := ih _ s' _ run
              exact ⟨m.code, m.memaddrs, m.ffi, m.be, m.locals, m.memory, m.shMemaddrs,
                m.baseAddr, m.topAddr, m.clock⟩
            · cases run
          · cases run
      | function fi =>
          simp only [evaluateDeclsHOLFinite] at run
          split at run
          · have m := ih _ s' _ run
            refine ⟨?_, m.memaddrs, m.ffi, m.be, m.locals, m.memory, m.shMemaddrs,
              m.baseAddr, m.topAddr, m.clock⟩
            rw [m.code]
            exact map_ext rfl
          · cases run
      | exnDecl exceptionName shape =>
          simp only [evaluateDeclsHOLFinite] at run
          split at run
          · have m := ih _ s' _ run
            exact ⟨m.code, m.memaddrs, m.ffi, m.be, m.locals, m.memory, m.shMemaddrs,
              m.baseAddr, m.topAddr, m.clock⟩
          · cases run

theorem sourceBehaviour_terminate_post (input : Guest.InputBlob) (outcome : HolOutcome)
    (events : List HolIoEvent) (h : sourceBehaviour input = .terminate outcome events) :
    ∃ s' : PanSemStateFiniteExact 64 Guest.HostMemory,
      s'.code = GuestCodeLookup.originalRuntimeCode ∧
      s'.memaddrs = ordinaryDomain ∧
      s'.ffi = sourceFfi input ∧
      s'.be = false ∧
      s'.locals = HolFiniteMapExact.empty ∧
      s'.memory = sourceMemory ∧
      s'.baseAddr = BitVec.ofNat 64 sourceBase ∧
      semantics s' (ofString "main") = .terminate outcome events := by
  unfold sourceBehaviour at h
  rw [← semanticsDecls_mainFirstHOL _ _ _ sourceHasMain] at h
  change semanticsDecls (sourceInitialState input) (ofString "main") sourceDeclarations = _ at h
  unfold semanticsDecls at h
  split at h
  · cases h
  · rename_i stCtxt _
    split at h
    · cases h
    · rename_i s' hs'
      have m := evaluateDecls_meta sourceDeclarations _ s' _ hs'
      refine ⟨s', ?_, m.memaddrs, m.ffi, m.be, m.locals, m.memory, m.baseAddr, h⟩
      rw [m.code]
      exact map_ext rfl

end InitECandidate.Solver.B2PostDecls
