import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify266
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body282_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.var Flapjack.VarKind.local "cached",
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 16#64])])

def body282_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body282_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cached") (Flapjack.Exp.const 0#64)) body282_0 body282_1

def body282_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def body282_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) body282_3 body282_1

def body282_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_fill" [Flapjack.Exp.var Flapjack.VarKind.local "node"]

def body282_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 16#64])])

def body282_7 : Prog (BitVec 64) :=
.seq body282_5 body282_6

def body282_8 : Prog (BitVec 64) :=
.seq body282_4 body282_7

def body282_9 : Prog (BitVec 64) :=
.seq body282_2 body282_8

def body282_10 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64])) body282_9

def body282_11 : Prog (BitVec 64) :=
.seq body282_2 body282_4

def body282_12 : Prog (BitVec 64) :=
.seq body282_11 body282_5

def body282_13 : Prog (BitVec 64) :=
.seq body282_12 body282_6

def body282_14 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64])) body282_13

def originalData282 : Decl (BitVec 64) :=
.function { name := "node_rlp", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body282_10, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData282 : Decl (BitVec 64) :=
.function { name := "node_rlp", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body282_14, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original282 := Pancake.PanLang.declToHOL originalData282
def simplified282 := Pancake.PanLang.declToHOL simplifiedData282
end InitECandidate.Proofs.FrontendStages.Declarations
