import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify319
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body335_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64,
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 8#64])])

def body335_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body335_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body335_0 body335_1

def body335_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rStruct [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body335_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 27#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
        (Flapjack.Exp.const 28#64)])) body335_3 body335_1

def body335_5 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 44#64)

def body335_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
  (Flapjack.Exp.const 35#64)) body335_5 body335_1

def body335_7 : Prog (BitVec 64) :=
.seq body335_4 body335_6

def body335_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body335_7 body335_1

def body335_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "fits"), none)) "u256_fits_word"
  [Flapjack.Exp.var Flapjack.VarKind.local "sh"]

def body335_10 : Prog (BitVec 64) :=
Flapjack.Prog.raise "TxErr" (Flapjack.Exp.const 45#64)

def body335_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fits") (Flapjack.Exp.const 0#64)) body335_10 body335_1

def body335_12 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.const 1#64, Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sh")])

def body335_13 : Prog (BitVec 64) :=
.seq body335_11 body335_12

def body335_14 : Prog (BitVec 64) :=
.seq body335_9 body335_13

def body335_15 : Prog (BitVec 64) :=
.decCall ("sh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_shr") ([Flapjack.Exp.var Flapjack.VarKind.local "vm", Flapjack.Exp.const 1#64]) body335_14

def body335_16 : Prog (BitVec 64) :=
.decCall ("vm") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body335_15

def body335_17 : Prog (BitVec 64) :=
.seq body335_8 body335_16

def body335_18 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body335_17

def body335_19 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) body335_18

def body335_20 : Prog (BitVec 64) :=
.seq body335_2 body335_19

def body335_21 : Prog (BitVec 64) :=
.seq body335_9 body335_11

def body335_22 : Prog (BitVec 64) :=
.seq body335_21 body335_12

def body335_23 : Prog (BitVec 64) :=
.decCall ("sh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_shr") ([Flapjack.Exp.var Flapjack.VarKind.local "vm", Flapjack.Exp.const 1#64]) body335_22

def body335_24 : Prog (BitVec 64) :=
.decCall ("vm") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 35#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]]) body335_23

def body335_25 : Prog (BitVec 64) :=
.seq body335_8 body335_24

def body335_26 : Prog (BitVec 64) :=
.decCall ("fits") (Flapjack.Shape.one) ("u256_fits_word") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body335_25

def body335_27 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 288#64])) body335_26

def body335_28 : Prog (BitVec 64) :=
.seq body335_2 body335_27

def originalData335 : Decl (BitVec 64) :=
.function { name := "tx_chain_id", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body335_20, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData335 : Decl (BitVec 64) :=
.function { name := "tx_chain_id", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body335_28, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original335 := Pancake.PanLang.declToHOL originalData335
def simplified335 := Pancake.PanLang.declToHOL simplifiedData335
end InitECandidate.Proofs.FrontendStages.Declarations
