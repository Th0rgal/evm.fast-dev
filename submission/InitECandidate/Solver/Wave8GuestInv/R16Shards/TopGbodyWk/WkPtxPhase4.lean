import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxRelBasePhase3

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

/-! # Phase 4 of `process_transaction`: gas accounting, receipts and stable logs -/

/-- The phase-4 spine: instructions 99-138 of the `process_transaction` body,
with the phase-5 continuation (`dec del ...`) replaced by `tail`. -/
theorem ptxPhase4_eq (tail : ProgHOL 64) :
    R13Shards.ptxPhase4 tail =
      (.dec (ofString "used_before_refund") .one (.op .sub [(.op .sub [(.var .local (ofString "gas")), (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000000#64)]))]), (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000038#64)]))]) (.decCall (ofString "ubr5") .one (ofString "udiv_small5") [(.var .local (ofString "used_before_refund"))] (.decCall (ofString "refund") .one (ofString "min") [(.var .local (ofString "ubr5")), (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000008#64)]))] (.dec (ofString "used_after_refund") .one (.op .sub [(.var .local (ofString "used_before_refund")), (.var .local (ofString "refund"))]) (.decCall (ofString "tx_gas_used") .one (ofString "max") [(.var .local (ofString "used_after_refund")), (.rfield 2 (.var .local (ofString "intrinsic")))] (.dec (ofString "tx_gas_left") .one (.op .sub [(.var .local (ofString "gas")), (.var .local (ofString "tx_gas_used"))]) (.decCall (ofString "gra") (.comb [.one, .one, .one, .one, .one]) (ofString "fee_mul") [(.var .local (ofString "tx_gas_left")), (.var .local (ofString "price"))] (.decCall (ofString "priority_fee") (.comb [.one, .one, .one, .one]) (ofString "u256_sub") [(.var .local (ofString "price")), (.load (.comb [.one, .one, .one, .one]) (.op .add [(.var .global (ofString "be")), (.const 0x0000000000000030#64)]))] (.decCall (ofString "tf") (.comb [.one, .one, .one, .one, .one]) (ofString "fee_mul") [(.var .local (ofString "tx_gas_used")), (.var .local (ofString "priority_fee"))] (.seq (.call (some (none, none)) (ofString "create_ether") [(.var .local (ofString "sender")), (.rstruct [(.rfield 1 (.var .local (ofString "gra"))), (.rfield 2 (.var .local (ofString "gra"))), (.rfield 3 (.var .local (ofString "gra"))), (.rfield 4 (.var .local (ofString "gra")))])]) (.seq (.call (some (none, none)) (ofString "create_ether") [(.load .one (.op .add [(.var .global (ofString "be")), (.const 0x0000000000000020#64)])), (.rstruct [(.rfield 1 (.var .local (ofString "tf"))), (.rfield 2 (.var .local (ofString "tf"))), (.rfield 3 (.var .local (ofString "tf"))), (.rfield 4 (.var .local (ofString "tf")))])]) (.dec (ofString "tx_state_gas") .one (.op .add [(.rfield 1 (.var .local (ofString "intrinsic"))), (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000048#64)]))]) (.dec (ofString "tx_state_gas_nat") .one (.var .local (ofString "tx_state_gas")) (.seq (.ite (.cmp .less (.var .local (ofString "tx_state_gas")) (.const 0x0000000000000000#64)) (.assign .local (ofString "tx_state_gas_nat") (.const 0x0000000000000000#64)) .skip) (.decCall (ofString "tx_regular_gas") .one (ofString "max") [(.op .sub [(.var .local (ofString "used_before_refund")), (.var .local (ofString "tx_state_gas_nat"))]), (.rfield 2 (.var .local (ofString "intrinsic")))] (.seq (.store (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000000#64)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000000#64)])), (.var .local (ofString "tx_regular_gas"))])) (.seq (.store (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000008#64)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000008#64)])), (.var .local (ofString "tx_state_gas_nat"))])) (.seq (.store (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000030#64)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000030#64)])), (.var .local (ofString "tx_blob_gas_used"))])) (.seq (.store (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000010#64)]) (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000010#64)])), (.var .local (ofString "tx_gas_used"))])) (.seq .skip (.dec (ofString "logs") .one (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000010#64)])) (.seq (.ite (.cmp .equal (.var .local (ofString "logs")) (.const 0x0000000000000000#64)) (.call (some (some (.local, (ofString "logs")), none)) (ofString "lst_new") [(.const 0x0000000000000008#64), (.const 0x0000000000000001#64)]) .skip) (.dec (ofString "succeeded") .one (.const 0x0000000000000001#64) (.seq (.ite (.cmp .notEqual (.load .one (.op .add [(.var .local (ofString "out")), (.const 0x0000000000000020#64)])) (.const 0x0000000000000000#64)) (.assign .local (ofString "succeeded") (.const 0x0000000000000000#64)) .skip) (.decCall (ofString "rc") (.comb [.one, .one]) (ofString "encode_receipt") [(.load .one (.op .add [(.var .local (ofString "tx")), (.const 0x0000000000000000#64)])), (.var .local (ofString "succeeded")), (.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000010#64)])), (.var .local (ofString "logs"))] (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000020#64)])), (.panop .mul [(.var .local (ofString "index")), (.const 0x0000000000000010#64)])]) (.rfield 0 (.var .local (ofString "rc")))) (.seq (.store (.op .add [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000020#64)])), (.panop .mul [(.var .local (ofString "index")), (.const 0x0000000000000010#64)]), (.const 0x0000000000000008#64)]) (.rfield 1 (.var .local (ofString "rc")))) (.dec (ofString "nl") .one (.load .one (.op .add [(.var .local (ofString "logs")), (.const 0x0000000000000008#64)])) (.dec (ofString "lp") .one (.load .one (.op .add [(.var .local (ofString "logs")), (.const 0x0000000000000000#64)])) (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64)) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) (.decCall (ofString "slot") .one (ofString "lst_push") [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000028#64)])), (.const 0x0000000000000008#64)] (.seq (.store (.var .local (ofString "slot")) (.load .one (.op .add [(.var .local (ofString "lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)]))))) (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl")) (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0x0000000000000000#64)) (.assign .local (ofString "stable_log_cap") (.const 0x0000000000000001#64)) .skip) (.decCall (ofString "stable_logs") .one (ofString "lst_new") [(.const 0x0000000000000008#64), (.var .local (ofString "stable_log_cap"))] (.seq (.store (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000008#64)]) (.var .local (ofString "nl"))) (.dec (ofString "stable_lp") .one (.load .one (.op .add [(.var .local (ofString "stable_logs")), (.const 0x0000000000000000#64)])) (.seq (.assign .local (ofString "i") (.const 0x0000000000000000#64)) (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) (.seq (.store (.op .add [(.var .local (ofString "stable_lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]) (.load .one (.op .add [(.var .local (ofString "lp")), (.panop .mul [(.var .local (ofString "i")), (.const 0x0000000000000008#64)])]))) (.assign .local (ofString "i") (.op .add [(.var .local (ofString "i")), (.const 0x0000000000000001#64)])))) (.decCall (ofString "rl") .one (ofString "lst_push") [(.load .one (.op .add [(.var .global (ofString "bo")), (.const 0x0000000000000048#64)])), (.const 0x0000000000000008#64)] (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))  tail))))))))))))))))))))))))))))))))))))))))
 := by
  unfold R13Shards.ptxPhase4 R13Shards.ptxCode
  simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
    FrontendCodecComputation.declToHOLStructural,
    FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural,
    FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural,
    FrontendCodecComputation.shapeToHOLStructural,
    FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil,
    R13Shards.spineAt, R13Shards.spinePlug]

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
