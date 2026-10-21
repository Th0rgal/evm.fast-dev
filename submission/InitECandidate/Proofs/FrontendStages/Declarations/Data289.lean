import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify273
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body289_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.global "mpt_key_scratch",
    Flapjack.Exp.var Flapjack.VarKind.local "klen",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "slice_arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul
            [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add
        [Flapjack.Exp.var Flapjack.VarKind.local "slice_arr",
          Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64],
          Flapjack.Exp.const 8#64])]

def body289_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body289_2 : Prog (BitVec 64) :=
.seq body289_0 body289_1

def body289_3 : Prog (BitVec 64) :=
.decCall ("klen") (Flapjack.Shape.one) ("rlp_encode_word") ([Flapjack.Exp.var Flapjack.VarKind.global "mpt_key_scratch", Flapjack.Exp.var Flapjack.VarKind.local "i"]) body289_2

def body289_4 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body289_3

def body289_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_root"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body289_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body289_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body289_8 : Prog (BitVec 64) :=
.seq body289_6 body289_7

def body289_9 : Prog (BitVec 64) :=
.seq body289_5 body289_8

def body289_10 : Prog (BitVec 64) :=
.seq body289_4 body289_9

def body289_11 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body289_10

def body289_12 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("mpt_new") ([Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body289_11

def body289_13 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body289_12

def body289_14 : Prog (BitVec 64) :=
.seq body289_4 body289_5

def body289_15 : Prog (BitVec 64) :=
.seq body289_14 body289_6

def body289_16 : Prog (BitVec 64) :=
.seq body289_15 body289_7

def body289_17 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body289_16

def body289_18 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("mpt_new") ([Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body289_17

def body289_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body289_18

def originalData289 : Decl (BitVec 64) :=
.function { name := "build_mpt_indexed", inline := false, exported := false, params := [("slice_arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body289_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData289 : Decl (BitVec 64) :=
.function { name := "build_mpt_indexed", inline := false, exported := false, params := [("slice_arr", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body289_19, returnShape := (Flapjack.Shape.one) }
def original289 := Pancake.PanLang.declToHOL originalData289
def simplified289 := Pancake.PanLang.declToHOL simplifiedData289
end InitECandidate.Proofs.FrontendStages.Declarations
