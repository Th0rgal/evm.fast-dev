import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q5X
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q6T

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4Q6: the stable-logs segment `p4Run_g8` (instructions 31-39)

The lane theorem owed to `WkPtxPhase4Wire.PtxPhase4QStep`.  The input is the
`p4Run_g7` continuation bundle at `s` (with the current receipt-slice bound
threaded from the receipt store of instruction 27); the continuation
receives the final state together with the phase-5 handoff
`PtxAfterPhase4`.

The two branches of the `p4Run_g7` pin run the same prefix (the capacity
clamp, the `lst_new` allocation, the count store and the copy loop) and meet
at the loop-38 exit bundle `P4Q8Exit` (`p4Q8_exit_nz` for a non-null
out-record list, `p4Q8_exit_zero` for the empty copy); `p4Q8_tail` then runs
the final `lst_push` into the `bo+72` receipts-logs list and the slot store,
and assembles `PtxAfterPhase4`. -/

theorem p4Run_g8 {F : Type}
    {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64}
    (h : P4Data entry s s_pmc w_out)
    (hc : s.code = originalRuntimeCode)
    (rest : ProgHOL 64)
    (nl_w lp_w : BitVec 64)
    (hnl : s.locals.lookup (ofString "nl") = some (.val (.word nl_w)))
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hpin : (nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8) ∧
        lp_w.toNat = memW s (memW s (w_out.toNat + 16)) ∧
        LogsListOK s (memW s (w_out.toNat + 16)) ∧
        LogsDisjFixed s (memW s (w_out.toNat + 16)) ∧
        memW s (w_out.toNat + 16) ≠ 0 ∧
        nl_w.toNat < 2 ^ 28) ∨
      nl_w.toNat = 0)
    (hrc32 : memW s (memW s (globN s "bo" + 32) + 16 * locN entry "index" + 8) < 2 ^ 40)
    (htail : ∀ s' : PanSemStateFiniteExact 64 F,
      s'.code = originalRuntimeCode →
      PtxAfterPhase4 entry s' →
      PtxRelRunStrong entry rest s') :
    PtxRelRunStrong entry
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl")) (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0x0000000000000000#64)) (.assign .local (ofString "stable_log_cap") (.const 0x0000000000000001#64)) .skip) (.decCall (ofString "stable_logs") .one (ofString "lst_new") [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))] (.seq (.store (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000008#64)]) (.var .local (ofString "nl"))) (.dec (ofString "stable_lp") .one (.load .one (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000000#64)])) (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64)) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) (.seq (.store (.op .add [(.var .local (ofString "stable_lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]) (.load .one (.op .add [(.var .local (ofString "lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)])))) (.decCall (ofString "rl") .one (ofString "lst_push") [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000048#64)])), (.const 0x0000000000000008#64)] (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest))))))))) s := by
  rcases hpin with ⟨hnl_eq, hlp_eq, hLL, hDF, hd_nz, hnl28⟩ | hnl0
  · exact p4Q8_exit_nz h hc _ nl_w lp_w hnl hlp hd_nz hnl_eq hlp_eq hLL hDF hnl28 hrc32
      (fun _ _ _ hE => p4Q8_tail hE rest htail)
  · exact p4Q8_exit_zero h hc _ nl_w lp_w hnl hlp hnl0 hrc32
      (fun _ _ _ hE => p4Q8_tail hE rest htail)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
