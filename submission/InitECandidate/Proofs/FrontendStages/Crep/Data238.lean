import InitECandidate.Proofs.FrontendStages.Crep.Translate222
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody238_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "mpt_fail" [Flapjack.CrepExp.const 2#64]

def crepBody238_1 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody238_0

def crepBody238_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody238_3 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody238_1 crepBody238_2

def crepBody238_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "memeq"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3], Flapjack.CrepExp.var 5]

def crepBody238_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 56#64])]

def crepBody238_6 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody238_5 crepBody238_2

def crepBody238_7 : CrepProg (BitVec 64) :=
.seq crepBody238_4 crepBody238_6

def crepBody238_8 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody238_7

def crepBody238_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5)
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3])) crepBody238_8 crepBody238_2

def crepBody238_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody238_11 : CrepProg (BitVec 64) :=
.seq crepBody238_9 crepBody238_10

def crepBody238_12 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody238_11

def crepBody238_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 1#64)) crepBody238_12 crepBody238_2

def crepBody238_14 : CrepProg (BitVec 64) :=
.seq crepBody238_3 crepBody238_13

def crepBody238_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower
  (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]) (Flapjack.CrepExp.var 5)) crepBody238_10 crepBody238_2

def crepBody238_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody238_10 crepBody238_2

def crepBody238_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody238_18 : CrepProg (BitVec 64) :=
.seq crepBody238_17 crepBody238_2

def crepBody238_19 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 5]) crepBody238_18

def crepBody238_20 : CrepProg (BitVec 64) :=
.seq crepBody238_16 crepBody238_19

def crepBody238_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 7)

def crepBody238_22 : CrepProg (BitVec 64) :=
.seq crepBody238_21 crepBody238_2

def crepBody238_23 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 48#64])) crepBody238_22

def crepBody238_24 : CrepProg (BitVec 64) :=
.seq crepBody238_20 crepBody238_23

def crepBody238_25 : CrepProg (BitVec 64) :=
.seq crepBody238_4 crepBody238_24

def crepBody238_26 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody238_25

def crepBody238_27 : CrepProg (BitVec 64) :=
.seq crepBody238_15 crepBody238_26

def crepBody238_28 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64])) crepBody238_27

def crepBody238_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody238_10 crepBody238_2

def crepBody238_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.var 5]

def crepBody238_31 : CrepProg (BitVec 64) :=
.seq crepBody238_29 crepBody238_30

def crepBody238_32 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 168#64])) crepBody238_31

def crepBody238_33 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody238_32 crepBody238_2

def crepBody238_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 0 (Flapjack.CrepExp.var 5)

def crepBody238_35 : CrepProg (BitVec 64) :=
.seq crepBody238_34 crepBody238_2

def crepBody238_36 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
        [Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3]),
          Flapjack.CrepExp.const 8#64]])) crepBody238_35

def crepBody238_37 : CrepProg (BitVec 64) :=
.seq crepBody238_33 crepBody238_36

def crepBody238_38 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 5)

def crepBody238_39 : CrepProg (BitVec 64) :=
.seq crepBody238_38 crepBody238_2

def crepBody238_40 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody238_39

def crepBody238_41 : CrepProg (BitVec 64) :=
.seq crepBody238_37 crepBody238_40

def crepBody238_42 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 2#64)) crepBody238_28 crepBody238_41

def crepBody238_43 : CrepProg (BitVec 64) :=
.seq crepBody238_14 crepBody238_42

def crepBody238_44 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64])) crepBody238_43

def crepBody238_45 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 0) (Flapjack.CrepExp.const 0#64)) crepBody238_44

def crepBody238_46 : CrepProg (BitVec 64) :=
.seq crepBody238_45 crepBody238_10

def crepBody238_47 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody238_46

def data238 : CrepProg (BitVec 64) := crepBody238_47
def output238 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [116#8, 114#8, 105#8, 101#8, 95#8, 119#8, 97#8, 108#8, 107#8], [0, 1, 2], crepProgToHOL data238)
end InitECandidate.Proofs.FrontendStages.Crep
