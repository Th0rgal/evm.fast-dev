import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify511
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body527_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def body527_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.const 100#64]

def body527_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "kv", Flapjack.Exp.var Flapjack.VarKind.local "key"]

def body527_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_transient_storage"
  [Flapjack.Exp.var Flapjack.VarKind.local "target", Flapjack.Exp.var Flapjack.VarKind.local "key",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body527_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def body527_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body527_6 : Prog (BitVec 64) :=
.seq body527_4 body527_5

def body527_7 : Prog (BitVec 64) :=
.seq body527_3 body527_6

def body527_8 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body527_7

def body527_9 : Prog (BitVec 64) :=
.seq body527_2 body527_8

def body527_10 : Prog (BitVec 64) :=
.dec ("key") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "evm_key_buf") body527_9

def body527_11 : Prog (BitVec 64) :=
.seq body527_1 body527_10

def body527_12 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body527_11

def body527_13 : Prog (BitVec 64) :=
.decCall ("kv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body527_12

def body527_14 : Prog (BitVec 64) :=
.seq body527_0 body527_13

def body527_15 : Prog (BitVec 64) :=
.seq body527_3 body527_4

def body527_16 : Prog (BitVec 64) :=
.seq body527_15 body527_5

def body527_17 : Prog (BitVec 64) :=
.dec ("target") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
      Flapjack.Exp.const 32#64])) body527_16

def body527_18 : Prog (BitVec 64) :=
.seq body527_2 body527_17

def body527_19 : Prog (BitVec 64) :=
.dec ("key") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.global "evm_key_buf") body527_18

def body527_20 : Prog (BitVec 64) :=
.seq body527_1 body527_19

def body527_21 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body527_20

def body527_22 : Prog (BitVec 64) :=
.decCall ("kv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) body527_21

def body527_23 : Prog (BitVec 64) :=
.seq body527_0 body527_22

def originalData527 : Decl (BitVec 64) :=
.function { name := "op_tstore", inline := false, exported := false, params := [], body := body527_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData527 : Decl (BitVec 64) :=
.function { name := "op_tstore", inline := false, exported := false, params := [], body := body527_23, returnShape := (Flapjack.Shape.one) }
def original527 := Pancake.PanLang.declToHOL originalData527
def simplified527 := Pancake.PanLang.declToHOL simplifiedData527
end InitECandidate.Proofs.FrontendStages.Declarations
