import InitECandidate.Proofs.FrontendStages.Crep.Translate553
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody569_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody569_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody569_2 : CrepProg (BitVec 64) :=
.seq crepBody569_0 crepBody569_1

def crepBody569_3 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody569_2

def crepBody569_4 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]]) crepBody569_3

def crepBody569_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 6)

def crepBody569_6 : CrepProg (BitVec 64) :=
.seq crepBody569_5 crepBody569_1

def crepBody569_7 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody569_6

def crepBody569_8 : CrepProg (BitVec 64) :=
.seq crepBody569_4 crepBody569_7

def crepBody569_9 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5)
  (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 3])) crepBody569_8

def crepBody569_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.const 0#64)

def crepBody569_11 : CrepProg (BitVec 64) :=
.seq crepBody569_10 crepBody569_1

def crepBody569_12 : CrepProg (BitVec 64) :=
.seq crepBody569_9 crepBody569_11

def crepBody569_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody569_14 : CrepProg (BitVec 64) :=
.seq crepBody569_13 crepBody569_1

def crepBody569_15 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 4294967295#64]) crepBody569_14

def crepBody569_16 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]) crepBody569_15

def crepBody569_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7
  (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 32#64))

def crepBody569_18 : CrepProg (BitVec 64) :=
.seq crepBody569_17 crepBody569_1

def crepBody569_19 : CrepProg (BitVec 64) :=
.seq crepBody569_16 crepBody569_18

def crepBody569_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 11)

def crepBody569_21 : CrepProg (BitVec 64) :=
.seq crepBody569_20 crepBody569_1

def crepBody569_22 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 1#64]) crepBody569_21

def crepBody569_23 : CrepProg (BitVec 64) :=
.seq crepBody569_19 crepBody569_22

def crepBody569_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.var 6,
        Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.var 2,
              Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]])],
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.var 9,
          Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 8#64]]),
    Flapjack.CrepExp.var 7]) crepBody569_23

def crepBody569_25 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.var 3)) crepBody569_24

def crepBody569_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody569_27 : CrepProg (BitVec 64) :=
.seq crepBody569_26 crepBody569_1

def crepBody569_28 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 7) crepBody569_27

def crepBody569_29 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 8#64]]) crepBody569_28

def crepBody569_30 : CrepProg (BitVec 64) :=
.seq crepBody569_25 crepBody569_29

def crepBody569_31 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 10)

def crepBody569_32 : CrepProg (BitVec 64) :=
.seq crepBody569_31 crepBody569_1

def crepBody569_33 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody569_32

def crepBody569_34 : CrepProg (BitVec 64) :=
.seq crepBody569_30 crepBody569_33

def crepBody569_35 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 4,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]]) crepBody569_34

def crepBody569_36 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody569_35

def crepBody569_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody569_36

def crepBody569_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 0,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]])) crepBody569_37

def crepBody569_39 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 1)) crepBody569_38

def crepBody569_40 : CrepProg (BitVec 64) :=
.seq crepBody569_12 crepBody569_39

def crepBody569_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody569_42 : CrepProg (BitVec 64) :=
.seq crepBody569_40 crepBody569_41

def crepBody569_43 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody569_42

def data569 : CrepProg (BitVec 64) := crepBody569_43
def output569 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [98#8, 110#8, 95#8, 109#8, 117#8, 108#8], [0, 1, 2, 3, 4], crepProgToHOL data569)
end InitECandidate.Proofs.FrontendStages.Crep
