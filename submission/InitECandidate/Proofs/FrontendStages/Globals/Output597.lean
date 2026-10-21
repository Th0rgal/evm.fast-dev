import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data597
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate581
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody597_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "require_not_static" []

def globalBody597_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def globalBody597_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "u256_to_be32"
  [Flapjack.Exp.var Flapjack.VarKind.local "saltv", Flapjack.Exp.var Flapjack.VarKind.local "salt"]

def globalBody597_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def globalBody597_4 : Prog (BitVec 64) :=
.seq globalBody597_2 globalBody597_3

def globalBody597_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "compute_create2_contract_address"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "salt",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
              Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "s"],
    Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "ca"]

def globalBody597_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody597_7 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody597_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "started") (Flapjack.Exp.const 0#64)) globalBody597_6 globalBody597_7

def globalBody597_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody597_10 : Prog (BitVec 64) :=
.seq globalBody597_8 globalBody597_9

def globalBody597_11 : Prog (BitVec 64) :=
.decCall ("started") (Flapjack.Shape.one) ("generic_create") ([Flapjack.Exp.var Flapjack.VarKind.local "endowment", Flapjack.Exp.var Flapjack.VarKind.local "ca",
  Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody597_10

def globalBody597_12 : Prog (BitVec 64) :=
.seq globalBody597_5 globalBody597_11

def globalBody597_13 : Prog (BitVec 64) :=
.decCall ("ca") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) globalBody597_12

def globalBody597_14 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart"]) globalBody597_13

def globalBody597_15 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 112#64])) globalBody597_14

def globalBody597_16 : Prog (BitVec 64) :=
.seq globalBody597_4 globalBody597_15

def globalBody597_17 : Prog (BitVec 64) :=
.decCall ("salt") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) globalBody597_16

def globalBody597_18 : Prog (BitVec 64) :=
.seq globalBody597_1 globalBody597_17

def globalBody597_19 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.const 12000#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 6#64, Flapjack.Exp.var Flapjack.VarKind.local "w"],
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) globalBody597_18

def globalBody597_20 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody597_19

def globalBody597_21 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "msize"]) globalBody597_20

def globalBody597_22 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "msize"]) globalBody597_21

def globalBody597_23 : Prog (BitVec 64) :=
.decCall ("saltv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody597_22

def globalBody597_24 : Prog (BitVec 64) :=
.decCall ("msize") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody597_23

def globalBody597_25 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody597_24

def globalBody597_26 : Prog (BitVec 64) :=
.decCall ("endowment") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody597_25

def globalBody597_27 : Prog (BitVec 64) :=
.seq globalBody597_0 globalBody597_26

def globalData597 : Decl (BitVec 64) :=
.function { name := "op_create2", inline := false, exported := false, params := [], body := globalBody597_27, returnShape := (Flapjack.Shape.one) }
def globalOutput597 := Pancake.PanLang.declToHOL globalData597
end InitECandidate.Proofs.FrontendStages.Declarations
