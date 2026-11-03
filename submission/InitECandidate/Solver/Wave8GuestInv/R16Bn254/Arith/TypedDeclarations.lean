import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.DecOnInit
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.InverseOuterBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded

def hasU256Locals (keys : List MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ key ∈ keys, ∃ a : Limbs256, s.locals.lookup key = some a.toValue

theorem hasU256Locals_update {F : Type} (s : PanSemStateFiniteExact 64 F)
    (keys : List MlS) (name : MlS) (a : Limbs256) (hp : hasU256Locals keys s) :
    hasU256Locals (name :: keys) (setVarHOLFinite name a.toValue s) := by
  intro key hk
  by_cases he : name = key
  · subst key
    exact ⟨a, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · have hk' : key ∈ keys := (List.mem_cons.mp hk).resolve_left (Ne.symm he)
    obtain ⟨b, hb⟩ := hp key hk'
    exact ⟨b, by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he] using hb⟩

theorem dec_u256_bound (keys : List MlS) (name : MlS) (init : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn (hasU256Locals (name :: keys)) body B) :
    TerminatingProgBoundedOn (hasU256Locals keys) (.dec name arithU256Shape init body) B := by
  apply TerminatingProgBoundedOn.dec_on_init name arithU256Shape init hbody
  intro F state value hc hp he hs
  obtain ⟨a, rfl⟩ := arith_shape_u256 hs
  exact hasU256Locals_update state keys name a hp

/-- A successful local initializer also proves the source local has four limbs. -/
theorem dec_u256_local_bound (keys : List MlS) (name source : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn (hasU256Locals (name :: source :: keys)) body B) :
    TerminatingProgBoundedOn (hasU256Locals keys)
      (.dec name arithU256Shape (.var .local source) body) B := by
  apply TerminatingProgBoundedOn.dec_on_init name arithU256Shape (.var .local source) hbody
  intro F state value hc hp he hs
  obtain ⟨a, rfl⟩ := arith_shape_u256 hs
  have hl : state.locals.lookup source = some a.toValue := by
    simpa [evalHOLFinite, evalHOLExact] using he
  apply hasU256Locals_update state (source :: keys) name a
  intro key hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨a, hl⟩
  · exact hp key hk

end InitECandidate.Solver.Wave8GuestInv.Arith
