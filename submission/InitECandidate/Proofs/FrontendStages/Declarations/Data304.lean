import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify288
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body304_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "tx"),
      some
        ("RlpErr", "rc",
          Flapjack.Prog.raise "TxErr"
            (Flapjack.Exp.op Flapjack.BinOp.add
              [Flapjack.Exp.const 100#64, Flapjack.Exp.var Flapjack.VarKind.local "rc"]))))
  "decode_transaction_rlp" [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "len"]

def body304_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "tx")

def body304_2 : Prog (BitVec 64) :=
.seq body304_0 body304_1

def body304_3 : Prog (BitVec 64) :=
.dec ("rc") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body304_2

def body304_4 : Prog (BitVec 64) :=
.dec ("tx") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body304_3

def originalData304 : Decl (BitVec 64) :=
.function { name := "decode_transaction", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body304_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData304 : Decl (BitVec 64) :=
.function { name := "decode_transaction", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("len", Flapjack.Shape.one)], body := body304_4, returnShape := (Flapjack.Shape.one) }
def original304 := Pancake.PanLang.declToHOL originalData304
def simplified304 := Pancake.PanLang.declToHOL simplifiedData304
end InitECandidate.Proofs.FrontendStages.Declarations
