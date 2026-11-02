import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.GuestUniformClockBound

/-! R10 primitive shard P10. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

private theorem fbOn_of_funBounded {f : MlS} {k K : Nat}
    (h : FunBounded f k) (hle : k ≤ K) :
    TerminatingFunBoundedOn GuestInv f K :=
  (TerminatingFunBoundedOn.of_unconditional
    (terminatingFunBounded_of_funBounded h)).weaken hle

theorem fb_max :
    TerminatingFunBoundedOn GuestInv (ofString "max") K.«max» := by
  refine fbOn_of_funBounded (f := ofString "max") (k := 0) (K := K.«max») ?_ (by decide)
  exact InitECandidate.Solver.GuestUniformClockBound.funBounded_of_guestAst
    32 (by rw [guestAst_len]; decide) Guest.Software.guestFn_max 0 rfl
    (ProgBounded.straight _ rfl)

theorem fb_require_not_static :
    TerminatingFunBoundedOn GuestInv (ofString "require_not_static") K.«require_not_static» := by
  refine fbOn_of_funBounded (f := ofString "require_not_static") (k := 0)
    (K := K.«require_not_static») ?_ (by decide)
  refine InitECandidate.Solver.GuestUniformClockBound.funBounded_of_guestAst
    470 (by rw [guestAst_len]; decide) Guest.Software.guestFn_require_not_static 0 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_require_not_static,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.seq
    (ProgBounded.ite _ (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl))
    (ProgBounded.straight _ rfl)

theorem fb_u256_to_be32 :
    TerminatingFunBoundedOn GuestInv (ofString "u256_to_be32") K.«u256_to_be32» := by
  refine fbOn_of_funBounded (f := ofString "u256_to_be32") (k := 20)
    (K := K.«u256_to_be32») ?_ (by decide)
  refine InitECandidate.Solver.GuestUniformClockBound.funBounded_of_guestAst
    87 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_to_be32 20 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (InitECandidate.Solver.GuestUniformClockBound.ProgBounded.iteMax _
        (ProgBounded.decCall InitECandidate.Solver.GuestUniformClockBound.funBounded_bswap64 _ _ _
          (ProgBounded.seq (ProgBounded.straight _ rfl)
            (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_bswap64 _ _)
              (ProgBounded.seq (ProgBounded.straight _ rfl)
                (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_bswap64 _ _)
                  (ProgBounded.seq (ProgBounded.straight _ rfl)
                    (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_bswap64 _ _)
                      (ProgBounded.seq (ProgBounded.straight _ rfl) (ProgBounded.straight _ rfl)))))))))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_st_be64 none _)
        (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_st_be64 none _)
          (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_st_be64 none _)
            (ProgBounded.seq (ProgBounded.call InitECandidate.Solver.GuestUniformClockBound.funBounded_st_be64 none _)
              (ProgBounded.straight _ rfl))))))
    (by decide)

theorem ro_require_not_static :
    ReadOnlyFn (ofString "require_not_static") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 470 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_require_not_static) rfl, ?_⟩
  intro F s hcode hInv hshape hnt hres
  simp only [sourceFunctionEntry, Guest.Software.guestFn_require_not_static,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  dsimp only [extractFn]
  simp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split <;> try split <;> simp only [evaluateHOLFiniteState_raise,
    evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return] <;> try rfl
  all_goals first | rfl | (split <;> try simp only [evaluateHOLFiniteState_raise,
    evaluateHOLFiniteState_skip, evaluateHOLFiniteState_return] <;> try rfl)
  all_goals try simp only [evalHOLExact, shapeOfHOLExact]
  all_goals split <;> try split <;> rfl
  all_goals first | rfl | (unfold emptyLocalsHOLFinite; rfl)

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P10

