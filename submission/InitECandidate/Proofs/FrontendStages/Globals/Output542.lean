import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data542
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate526
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody542_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "charge_gas" [Flapjack.Exp.var Flapjack.VarKind.local "cost"]

def globalBody542_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "warm_after_charge"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def globalBody542_2 : Prog (BitVec 64) :=
.seq globalBody542_0 globalBody542_1

def globalBody542_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "extend_memory"
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "x")]

def globalBody542_4 : Prog (BitVec 64) :=
.seq globalBody542_2 globalBody542_3

def globalBody542_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "buffer_read"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "code"),
    Flapjack.Exp.var Flapjack.VarKind.local "cs", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.load Flapjack.Shape.one
                (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
              Flapjack.Exp.const 24#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "ms"]]

def globalBody542_6 : Prog (BitVec 64) :=
.decCall ("cs") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "cstart"]) globalBody542_5

def globalBody542_7 : Prog (BitVec 64) :=
.decCall ("ms") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart"]) globalBody542_6

def globalBody542_8 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody542_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "n") (Flapjack.Exp.const 0#64)) globalBody542_7 globalBody542_8

def globalBody542_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pc_add" [Flapjack.Exp.const 1#64]

def globalBody542_11 : Prog (BitVec 64) :=
.seq globalBody542_9 globalBody542_10

def globalBody542_12 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody542_13 : Prog (BitVec 64) :=
.seq globalBody542_11 globalBody542_12

def globalBody542_14 : Prog (BitVec 64) :=
.decCall ("code") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("ext_code_of") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody542_13

def globalBody542_15 : Prog (BitVec 64) :=
.seq globalBody542_4 globalBody542_14

def globalBody542_16 : Prog (BitVec 64) :=
.decCall ("cost") (Flapjack.Shape.one) ("add_sat") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.const 100#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "w"]],
  Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "x")]) globalBody542_15

def globalBody542_17 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("access_gas_cost") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody542_16

def globalBody542_18 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("extend_memory_cost1") ([Flapjack.Exp.var Flapjack.VarKind.local "mstart", Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody542_17

def globalBody542_19 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("words_of") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) globalBody542_18

def globalBody542_20 : Prog (BitVec 64) :=
.decCall ("n") (Flapjack.Shape.one) ("sat_word") ([Flapjack.Exp.var Flapjack.VarKind.local "size"]) globalBody542_19

def globalBody542_21 : Prog (BitVec 64) :=
.decCall ("size") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody542_20

def globalBody542_22 : Prog (BitVec 64) :=
.decCall ("cstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody542_21

def globalBody542_23 : Prog (BitVec 64) :=
.decCall ("mstart") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody542_22

def globalBody542_24 : Prog (BitVec 64) :=
.decCall ("addr") (Flapjack.Shape.one) ("to_address_masked") ([Flapjack.Exp.var Flapjack.VarKind.local "av"]) globalBody542_23

def globalBody542_25 : Prog (BitVec 64) :=
.decCall ("av") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("stack_pop") ([]) globalBody542_24

def globalData542 : Decl (BitVec 64) :=
.function { name := "op_extcodecopy", inline := false, exported := false, params := [], body := globalBody542_25, returnShape := (Flapjack.Shape.one) }
def globalOutput542 := Pancake.PanLang.declToHOL globalData542
end InitECandidate.Proofs.FrontendStages.Declarations
