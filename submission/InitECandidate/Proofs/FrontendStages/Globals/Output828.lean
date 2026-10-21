import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data828
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate812
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody828_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "entry", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def globalBody828_1 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "bloom", Flapjack.Exp.var Flapjack.VarKind.local "byte_index"])
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.loadByte
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "bloom", Flapjack.Exp.var Flapjack.VarKind.local "byte_index"]),
      Flapjack.Exp.var Flapjack.VarKind.local "bv"])

def globalBody828_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "idx"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 2#64])

def globalBody828_3 : Prog (BitVec 64) :=
.seq globalBody828_1 globalBody828_2

def globalBody828_4 : Prog (BitVec 64) :=
.dec ("bv") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsl (Flapjack.Exp.const 1#64)
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.const 7#64,
      Flapjack.Exp.op Flapjack.BinOp.and
        [Flapjack.Exp.var Flapjack.VarKind.local "bit_index", Flapjack.Exp.const 7#64]])) globalBody828_3

def globalBody828_5 : Prog (BitVec 64) :=
.dec ("byte_index") (Flapjack.Shape.one) (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "bit_index") (Flapjack.Exp.const 3#64)) globalBody828_4

def globalBody828_6 : Prog (BitVec 64) :=
.dec ("bit_index") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.const 2047#64, Flapjack.Exp.var Flapjack.VarKind.local "bit"]) globalBody828_5

def globalBody828_7 : Prog (BitVec 64) :=
.dec ("bit") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.op Flapjack.BinOp.or
      [Flapjack.Exp.shift Flapjack.Shift.lsl
          (Flapjack.Exp.loadByte
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "idx"]))
          (Flapjack.Exp.const 8#64),
        Flapjack.Exp.loadByte
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "idx",
              Flapjack.Exp.const 1#64])],
    Flapjack.Exp.const 2047#64]) globalBody828_6

def globalBody828_8 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "idx") (Flapjack.Exp.const 6#64)) globalBody828_7

def globalBody828_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody828_10 : Prog (BitVec 64) :=
.seq globalBody828_8 globalBody828_9

def globalBody828_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody828_12 : Prog (BitVec 64) :=
.seq globalBody828_10 globalBody828_11

def globalBody828_13 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody828_12

def globalBody828_14 : Prog (BitVec 64) :=
.seq globalBody828_0 globalBody828_13

def globalBody828_15 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody828_14

def globalBody828_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody828_15

def globalData828 : Decl (BitVec 64) :=
.function { name := "add_to_bloom", inline := false, exported := false, params := [("bloom", Flapjack.Shape.one), ("entry", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := globalBody828_16, returnShape := (Flapjack.Shape.one) }
def globalOutput828 := Pancake.PanLang.declToHOL globalData828
end InitECandidate.Proofs.FrontendStages.Declarations
