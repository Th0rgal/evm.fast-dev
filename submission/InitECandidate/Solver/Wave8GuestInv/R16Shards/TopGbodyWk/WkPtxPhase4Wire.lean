import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4P

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

/-! # Phase 4 top-level wiring (`WkPtxPhase4Wire`)

The full phase-4 cut `PtxRelCutStrong R13Shards.ptxPhase4 PtxAfterPhase3
PtxAfterPhase4`, composed from the proven lane runners `p4Run_head` (4M),
`p4Run_g5` (4N) and `p4Run_g7` (4P) after the `ptxPhase4_eq` spine
decomposition, and parameterized over the two lane theorems not yet closed
in this shard chain:

* `PtxPhase4OStep` — owed by `WkPtxPhase4O.lean` (`p4Run_g6`, the
  `encode_receipt` call and the two receipt-record stores, instructions
  24-30);
* `PtxPhase4QStep` — owed by `WkPtxPhase4Q.lean` (`p4Run_g8`, the
  stable-logs segment, instructions 31-39), whose continuation receives the
  phase-5 handoff `PtxAfterPhase4` at the final state.

Instantiating `hG6`/`hG8` with the two lane theorems (once compiled) yields
the unconditional phase-4 cut. -/

/-- The step theorem owed by `WkPtxPhase4O.lean`: instructions 24-30 of the
phase-4 spine (the `encode_receipt` call plus the two receipt-record stores
into the `bo+32` array).  The input is the full `p4Run_g5` continuation
bundle at `s`; the continuation receives the same bundle at the post-store
state. -/
abbrev PtxPhase4OStep : Prop :=
  ∀ {F : Type} {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64},
    P4Data entry s s_pmc w_out →
    s.code = originalRuntimeCode →
    ∀ rest : ProgHOL 64,
    ∀ wl succw : BitVec 64,
    s.locals.lookup (ofString "logs") = some (.val (.word wl)) →
    s.locals.lookup (ofString "succeeded") = some (.val (.word succw)) →
    LogsListOK s wl.toNat →
    LogsDisjFixed s wl.toNat →
    (wl.toNat = memW s (w_out.toNat + 16) ∨
      (memW s wl.toNat = wl.toNat + 24 ∧
        memW s (wl.toNat + 8) = 0 ∧
        WordAt s wl.toNat ∧ WordAt s (wl.toNat + 8) ∧
        wl.toNat + 32 ≤ globN s "heap_ptr")) →
    (∀ (s' : PanSemStateFiniteExact 64 F) (wl' succw' : BitVec 64),
      P4Data entry s' s_pmc w_out →
      s'.code = originalRuntimeCode →
      s'.locals.lookup (ofString "logs") = some (.val (.word wl')) →
      s'.locals.lookup (ofString "succeeded") = some (.val (.word succw')) →
      LogsListOK s' wl'.toNat →
      LogsDisjFixed s' wl'.toNat →
      (wl'.toNat = memW s' (w_out.toNat + 16) ∨
        (memW s' wl'.toNat = wl'.toNat + 24 ∧
          memW s' (wl'.toNat + 8) = 0 ∧
          WordAt s' wl'.toNat ∧ WordAt s' (wl'.toNat + 8) ∧
          wl'.toNat + 32 ≤ globN s' "heap_ptr")) →
      PtxRelRunStrong entry rest s') →
    PtxRelRunStrong entry
      (.decCall (ofString "rc") (.comb [.one, .one]) (ofString "encode_receipt") [(.load .one (.op .add [(.var .local (ofString "tx")), (.const 0x0000000000000000#64)])), (.var .local (ofString "succeeded")), (.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000010#64)])), (.var .local (ofString "logs"))] (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000020#64)])), (.panop .mul [(.var .local (ofString "index")), (.const 0x0000000000000010#64)])]) (.rfield 0 (.var .local (ofString "rc")))) (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000020#64)])), (.panop .mul [(.var .local (ofString "index")), (.const 0x0000000000000010#64)]), (.const 0x0000000000000008#64)]) (.rfield 1 (.var .local (ofString "rc")))) rest))) s

/-- The step theorem owed by `WkPtxPhase4Q.lean`: instructions 31-39 of the
phase-4 spine (the stable-logs segment).  The input is exactly the
`p4Run_g7` continuation bundle at `s`; the continuation receives the final
state together with the phase-5 handoff `PtxAfterPhase4`. -/
abbrev PtxPhase4QStep : Prop :=
  ∀ {F : Type} {entry s s_pmc : PanSemStateFiniteExact 64 F} {w_out : BitVec 64},
    P4Data entry s s_pmc w_out →
    s.code = originalRuntimeCode →
    ∀ rest : ProgHOL 64,
    ∀ nl_w lp_w : BitVec 64,
    s.locals.lookup (ofString "nl") = some (.val (.word nl_w)) →
    s.locals.lookup (ofString "lp") = some (.val (.word lp_w)) →
    ((nl_w.toNat = memW s (memW s (w_out.toNat + 16) + 8) ∧
        lp_w.toNat = memW s (memW s (w_out.toNat + 16)) ∧
        LogsListOK s (memW s (w_out.toNat + 16)) ∧
        LogsDisjFixed s (memW s (w_out.toNat + 16)) ∧
        memW s (w_out.toNat + 16) ≠ 0 ∧
        nl_w.toNat < 2 ^ 28) ∨
      nl_w.toNat = 0) →
    (∀ s' : PanSemStateFiniteExact 64 F,
      P4Data entry s' s_pmc w_out →
      s'.code = originalRuntimeCode →
      PtxAfterPhase4 entry s' →
      PtxRelRunStrong entry rest s') →
    PtxRelRunStrong entry
      (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl")) (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0x0000000000000000#64)) (.assign .local (ofString "stable_log_cap") (.const 0x0000000000000001#64)) .skip) (.decCall (ofString "stable_logs") .one (ofString "lst_new") [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))] (.seq (.store (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000008#64)]) (.var .local (ofString "nl"))) (.dec (ofString "stable_lp") .one (.load .one (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000000#64)])) (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64)) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) (.seq (.store (.op .add [(.var .local (ofString "stable_lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]) (.load .one (.op .add [(.var .local (ofString "lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)])))) (.decCall (ofString "rl") .one (ofString "lst_push") [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000048#64)])), (.const 0x0000000000000008#64)] (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs"))) rest))))))))) s

/-- The full phase-4 cut, parameterized over the two open lane theorems
(`WkPtxPhase4O.p4Run_g6` and `WkPtxPhase4Q.p4Run_g8`). -/
theorem ptxPhase4_relCut_strong_of
    (hG6 : PtxPhase4OStep) (hG8 : PtxPhase4QStep) :
    PtxRelCutStrong R13Shards.ptxPhase4 PtxAfterPhase3 PtxAfterPhase4 := by
  intro F entry tail htail s hc hA3
  obtain ⟨s_pmc, w_out, hd3⟩ := hA3
  have hD : P4Data entry s s_pmc w_out := p4Data_of_afterPhase3 hd3
  rw [ptxPhase4_eq]
  refine p4Run_head hD hc _ ?_
  intro s1 hD1 hc1
  refine p4Run_g5 hD1 hc1 _ ?_
  intro s2 wl2 succw2 hD2 hc2 hlogs2 hsucc2 hLL2 hDF2 hdisj2
  refine hG6 hD2 hc2 _ wl2 succw2 hlogs2 hsucc2 hLL2 hDF2 hdisj2 ?_
  intro s3 wl3 succw3 hD3 hc3 hlogs3 hsucc3 hLL3 hDF3 hdisj3
  refine p4Run_g7 hD3 hc3 _ wl3 succw3 hlogs3 hsucc3 hLL3 hDF3 hdisj3 ?_
  intro s4 nl4 lp4 hD4 hc4 hnl4 hlp4 hpin4
  refine hG8 hD4 hc4 _ nl4 lp4 hnl4 hlp4 hpin4 ?_
  intro s5 hD5 hc5 hAfter5
  exact htail s5 hc5 hAfter5

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
