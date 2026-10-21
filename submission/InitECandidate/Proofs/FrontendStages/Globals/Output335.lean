import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data335
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate319
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody335_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64,
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 8#64])])

def globalBody335_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody335_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody335_0 globalBody335_1

def globalBody335_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def globalBody335_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 27#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 28#64)])) globalBody335_3 globalBody335_1

def globalBody335_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 44#64)

def globalBody335_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
  (Flapjack.Exp.const 35#64)) globalBody335_5 globalBody335_1

def globalBody335_7 : Prog (BitVec 64) :=
.seq globalBody335_4 globalBody335_6

def globalBody335_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody335_7 globalBody335_1

def globalBody335_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "fits"), none)) "u256_fits_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "sh"]

def globalBody335_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 45#64)

def globalBody335_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) globalBody335_10 globalBody335_1

def globalBody335_12 : Prog (BitVec 64) :=
.seq globalBody335_9 globalBody335_11

def globalBody335_13 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.const 1#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sh")])

def globalBody335_14 : Prog (BitVec 64) :=
.seq globalBody335_12 globalBody335_13

def globalBody335_15 : Prog (BitVec 64) :=
.decCall ("sh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_shr") ([Flapjack.Exp.var Flapjack.VarKind.local "vm", Flapjack.Exp.const 1#64]) globalBody335_14

def globalBody335_16 : Prog (BitVec 64) :=
.decCall ("vm") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) globalBody335_15

def globalBody335_17 : Prog (BitVec 64) :=
.seq globalBody335_8 globalBody335_16

def globalBody335_18 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody335_17

def globalBody335_19 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) globalBody335_18

def globalBody335_20 : Prog (BitVec 64) :=
.seq globalBody335_2 globalBody335_19

def globalData335 : Decl (BitVec 64) :=
.function { name := "tx_chain_id", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := globalBody335_20, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput335 := Pancake.PanLang.declToHOL globalData335
end InitECandidate.Proofs.FrontendStages.Declarations
