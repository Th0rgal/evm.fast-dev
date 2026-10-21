import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify814
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body830_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "hl"],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64],
    Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def body830_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "rlp_encode_list_header"
  [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.var Flapjack.VarKind.local "payload"]

def body830_2 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "hl", Flapjack.Exp.var Flapjack.VarKind.local "payload"])

def body830_3 : Prog (BitVec 64) :=
.seq body830_1 body830_2

def body830_4 : Prog (BitVec 64) :=
.seq body830_0 body830_3

def body830_5 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body830_4

def body830_6 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "payload_end",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]]) body830_5

def body830_7 : Prog (BitVec 64) :=
.seq body830_0 body830_1

def body830_8 : Prog (BitVec 64) :=
.seq body830_7 body830_2

def body830_9 : Prog (BitVec 64) :=
.decCall ("hl") (Flapjack.Shape.one) ("rlp_list_header_len") ([Flapjack.Exp.var Flapjack.VarKind.local "payload"]) body830_8

def body830_10 : Prog (BitVec 64) :=
.dec ("payload") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.sub
  [Flapjack.Exp.var Flapjack.VarKind.local "payload_end",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "dst", Flapjack.Exp.const 9#64]]) body830_9

def originalData830 : Decl (BitVec 64) :=
.function { name := "rlp_finish_list", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("payload_end", Flapjack.Shape.one)], body := body830_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData830 : Decl (BitVec 64) :=
.function { name := "rlp_finish_list", inline := false, exported := false, params := [("dst", Flapjack.Shape.one), ("payload_end", Flapjack.Shape.one)], body := body830_10, returnShape := (Flapjack.Shape.one) }
def original830 := Pancake.PanLang.declToHOL originalData830
def simplified830 := Pancake.PanLang.declToHOL simplifiedData830
end InitECandidate.Proofs.FrontendStages.Declarations
