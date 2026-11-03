import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.DecOnInit
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BlsCallFacts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded

def hasU384Locals (keys : List MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ key ∈ keys, ∃ a : Limbs384, s.locals.lookup key = some a.toValue

theorem hasU384Locals_update {F : Type} (s : PanSemStateFiniteExact 64 F)
    (keys : List MlS) (name : MlS) (a : Limbs384) (hp : hasU384Locals keys s) :
    hasU384Locals (name :: keys) (setVarHOLFinite name a.toValue s) := by
  intro key hk
  by_cases he : name = key
  · subst key
    exact ⟨a, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · have hk' : key ∈ keys := (List.mem_cons.mp hk).resolve_left (Ne.symm he)
    obtain ⟨b, hb⟩ := hp key hk'
    exact ⟨b, by simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he] using hb⟩

theorem dec_u384_bound (keys : List MlS) (name : MlS) (init : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn (hasU384Locals (name :: keys)) body B) :
    TerminatingProgBoundedOn (hasU384Locals keys) (.dec name blsU384Shape init body) B := by
  apply TerminatingProgBoundedOn.dec_on_init name blsU384Shape init hbody
  intro F state value hc hp he hs
  obtain ⟨a, rfl⟩ := bls_shape_u384 hs
  exact hasU384Locals_update state keys name a hp

/-- A successful local initializer also proves the source local has four limbs. -/
theorem dec_u384_local_bound (keys : List MlS) (name source : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn (hasU384Locals (name :: source :: keys)) body B) :
    TerminatingProgBoundedOn (hasU384Locals keys)
      (.dec name blsU384Shape (.var .local source) body) B := by
  apply TerminatingProgBoundedOn.dec_on_init name blsU384Shape (.var .local source) hbody
  intro F state value hc hp he hs
  obtain ⟨a, rfl⟩ := bls_shape_u384 hs
  have hl : state.locals.lookup source = some a.toValue := by
    simpa [evalHOLFinite, evalHOLExact] using he
  apply hasU384Locals_update state (source :: keys) name a
  intro key hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact ⟨a, hl⟩
  · exact hp key hk
end InitECandidate.Solver.Wave8GuestInv.Arith
