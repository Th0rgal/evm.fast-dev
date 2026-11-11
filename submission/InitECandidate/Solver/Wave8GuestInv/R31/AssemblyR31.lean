import InitECandidate.Solver.Wave8GuestInv.Assembly
import InitECandidate.Solver.Wave8GuestInv.R31.PrimitivesProvedR31

/-! # Wave 8 R32 `AssemblyR31` (parameterized, compile-true wiring)

Canonical Shadow Integrator R32d parameterized cutover of
`Wave8GuestInv.assembly`: identical to the proved round-3 conditional
assembly ruling, but taking the primitive instance as an explicit parameter so
both the legacy `primitives` and the R31/R32 `primitivesR31` instances feed
the same kernel-checked chain. No primitive instance is assumed; the
124-line predecessor `Assembly.lean` stays untouched. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R31

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Parameterized conditional assembly: the primitive obligations imply the
campaign target, for any `Primitives` instance (legacy or R31-strong). -/
theorem assemblyR31 (P : Primitives) : CoveredSourceTicksConsumedBounded K_pan :=
  assembly P

end InitECandidate.Solver.Wave8GuestInv.R31
