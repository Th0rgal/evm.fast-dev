import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data282
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate266
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody282_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "cached",
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 16#64])])

def globalBody282_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody282_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cached") (Flapjack.Exp.const 0#64)) globalBody282_0 globalBody282_1

def globalBody282_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def globalBody282_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody282_3 globalBody282_1

def globalBody282_5 : Prog (BitVec 64) :=
.seq globalBody282_2 globalBody282_4

def globalBody282_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_fill" [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def globalBody282_7 : Prog (BitVec 64) :=
.seq globalBody282_5 globalBody282_6

def globalBody282_8 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 16#64])])

def globalBody282_9 : Prog (BitVec 64) :=
.seq globalBody282_7 globalBody282_8

def globalBody282_10 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64])) globalBody282_9

def globalData282 : Decl (BitVec 64) :=
.function { name := "node_rlp", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := globalBody282_10, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput282 := Pancake.PanLang.declToHOL globalData282
end InitECandidate.Proofs.FrontendStages.Declarations
