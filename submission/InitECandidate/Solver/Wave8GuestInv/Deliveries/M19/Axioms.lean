import InitECandidate.Solver.Wave8GuestInv.Contracts
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.DelSpecs
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.TruncateSpec

set_option Elab.async false
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.M19

theorem htab_del_progress_spec :
    InitECandidate.Solver.Wave8GuestInv.FunSpec
      InitECandidate.Solver.Wave8GuestInv.HtabArgWF
      (InitECandidate.Solver.Wave8GuestInv.OnReturn InitECandidate.Solver.Wave8GuestInv.HtabDelProgress)
      (Flapjack.Basis.Pure.MlString.ofString "htab_del") :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_del_progress_spec

theorem htab_del_spec :
    InitECandidate.Solver.Wave8GuestInv.FunSpec
      InitECandidate.Solver.Wave8GuestInv.HtabArgWF
      (InitECandidate.Solver.Wave8GuestInv.OnReturn InitECandidate.Solver.Wave8GuestInv.HtabExit)
      (Flapjack.Basis.Pure.MlString.ofString "htab_del") :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_del_spec

theorem htab_truncate_spec :
    InitECandidate.Solver.Wave8GuestInv.FunSpec
      InitECandidate.Solver.Wave8GuestInv.HtabArgWF
      (InitECandidate.Solver.Wave8GuestInv.OnReturn InitECandidate.Solver.Wave8GuestInv.HtabExit)
      (Flapjack.Basis.Pure.MlString.ofString "htab_truncate") :=
  InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.htab_truncate_spec

end InitECandidate.Solver.Wave8GuestInv.M19
