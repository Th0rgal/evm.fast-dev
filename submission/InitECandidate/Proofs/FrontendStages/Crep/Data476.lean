import InitECandidate.Proofs.FrontendStages.Crep.Translate460
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody476_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "charge_gas" [Flapjack.CrepExp.const 3#64]

def crepBody476_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody476_0

def crepBody476_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "code_imm" []

def crepBody476_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 2)

def crepBody476_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody476_5 : CrepProg (BitVec 64) :=
.seq crepBody476_3 crepBody476_4

def crepBody476_6 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 10#64) crepBody476_5

def crepBody476_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 8#64

def crepBody476_8 : CrepProg (BitVec 64) :=
.seq crepBody476_6 crepBody476_7

def crepBody476_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.const 81#64) (Flapjack.CrepExp.var 1)),
    Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.const 0#64)
      (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 1) (Flapjack.CrepExp.const 128#64))]) crepBody476_8 crepBody476_4

def crepBody476_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64])

def crepBody476_11 : CrepProg (BitVec 64) :=
.seq crepBody476_10 crepBody476_4

def crepBody476_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64])

def crepBody476_13 : CrepProg (BitVec 64) :=
.seq crepBody476_12 crepBody476_4

def crepBody476_14 : CrepProg (BitVec 64) :=
.seq crepBody476_11 crepBody476_13

def crepBody476_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64])

def crepBody476_16 : CrepProg (BitVec 64) :=
.seq crepBody476_15 crepBody476_4

def crepBody476_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 6
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 29#64, Flapjack.CrepExp.var 3])

def crepBody476_18 : CrepProg (BitVec 64) :=
.seq crepBody476_17 crepBody476_4

def crepBody476_19 : CrepProg (BitVec 64) :=
.seq crepBody476_16 crepBody476_18

def crepBody476_20 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 4)) crepBody476_14 crepBody476_19

def crepBody476_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "max" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody476_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody476_23 : CrepProg (BitVec 64) :=
.seq crepBody476_22 crepBody476_4

def crepBody476_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 2#64) crepBody476_23

def crepBody476_25 : CrepProg (BitVec 64) :=
.seq crepBody476_24 crepBody476_7

def crepBody476_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
        Flapjack.CrepExp.const 16#64]))
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 1#64])) crepBody476_25 crepBody476_4

def crepBody476_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "stack_swap_positions" [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6]

def crepBody476_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody476_27

def crepBody476_29 : CrepProg (BitVec 64) :=
.seq crepBody476_26 crepBody476_28

def crepBody476_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "pc_add" [Flapjack.CrepExp.const 2#64]

def crepBody476_31 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody476_30

def crepBody476_32 : CrepProg (BitVec 64) :=
.seq crepBody476_29 crepBody476_31

def crepBody476_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody476_34 : CrepProg (BitVec 64) :=
.seq crepBody476_32 crepBody476_33

def crepBody476_35 : CrepProg (BitVec 64) :=
.seq crepBody476_21 crepBody476_34

def crepBody476_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody476_35

def crepBody476_37 : CrepProg (BitVec 64) :=
.seq crepBody476_20 crepBody476_36

def crepBody476_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody476_37

def crepBody476_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody476_38

def crepBody476_40 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 15#64]) crepBody476_39

def crepBody476_41 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 4#64)) crepBody476_40

def crepBody476_42 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.op Flapjack.BinOp.xor [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 143#64]) crepBody476_41

def crepBody476_43 : CrepProg (BitVec 64) :=
.seq crepBody476_9 crepBody476_42

def crepBody476_44 : CrepProg (BitVec 64) :=
.seq crepBody476_2 crepBody476_43

def crepBody476_45 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody476_44

def crepBody476_46 : CrepProg (BitVec 64) :=
.seq crepBody476_1 crepBody476_45

def data476 : CrepProg (BitVec 64) := crepBody476_46
def output476 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8], [], crepProgToHOL data476)
end InitECandidate.Proofs.FrontendStages.Crep
