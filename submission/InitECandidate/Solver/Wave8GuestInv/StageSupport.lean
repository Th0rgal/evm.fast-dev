import InitECandidate.Solver.Wave8Stage.WordToStackSharedClock
import InitECandidate.Solver.Wave8Stage.WordToStackSeqClock
import InitECandidate.Solver.Wave8Stage.WordToStackIfClock
import InitECandidate.Solver.Wave8Stage.WordToStackLoopClock

/-! Exact bounded constructor theorems consumed from wave8/stage1to3 @
452960237cf08ce1e8b360bff7794faf9067341b. The concrete entry-call transfer
still needs the bounded call constructors and the quantitative induction. -/

namespace InitECandidate.Solver.Wave8GuestInv.StageSupport

theorem raise_bounded :
    type_of% @Wave8Stage.WordToStackBounded.compCorrectRaise :=
  @Wave8Stage.WordToStackBounded.compCorrectRaise

theorem shared_bounded :
    type_of% @Wave8Stage.WordToStackSharedClock.compCorrectShareInst :=
  @Wave8Stage.WordToStackSharedClock.compCorrectShareInst

theorem seq_bounded :
    type_of% @Wave8Stage.WordToStackSeqClock.compCorrectSeq :=
  @Wave8Stage.WordToStackSeqClock.compCorrectSeq

theorem if_bounded :
    type_of% @Wave8Stage.WordToStackIfClock.compCorrectIf :=
  @Wave8Stage.WordToStackIfClock.compCorrectIf

theorem loop_bounded :
    type_of% @Wave8Stage.WordToStackLoopClock.compCorrectLoop :=
  @Wave8Stage.WordToStackLoopClock.compCorrectLoop

end InitECandidate.Solver.Wave8GuestInv.StageSupport
