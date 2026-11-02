import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.Bridge
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelFinal

/-! `htab_del_spec` and `htab_del_progress_spec`: verified against R11 `Wave8GuestInv` definitions. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.HtabC00Ports

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv

theorem htab_del_spec :
    FunSpec HtabArgWF (OnReturn HtabExit) (ofString "htab_del") := by
  rcases Wave8M19.Htab.htab_del_spec_proof with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hpre _ hnt v hv
  exact exit_from_light s _ (hrun s hc (arg_to_light s hpre) hnt v hv) hpre.1.2.2.2.2.2.2.2.2.2

theorem htab_del_progress_spec :
    FunSpec HtabArgWF (OnReturn HtabDelProgress) (ofString "htab_del") := by
  rcases Wave8M19.Htab.htab_del_progress_spec_proof with ⟨ps, body, ret, hl, hrun⟩
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hpre _ hnt v hv
  exact hrun s hc (arg_to_light s hpre) hnt v hv

end InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
