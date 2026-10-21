import InitECandidate.Proofs.FrontendStages.Crep.Translate377
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody393_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4, 5, 6], none)) "htab_item"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
    Flapjack.CrepExp.var 3]

def crepBody393_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 10)

def crepBody393_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody393_3 : CrepProg (BitVec 64) :=
.seq crepBody393_1 crepBody393_2

def crepBody393_4 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 24#64])]) crepBody393_3

def crepBody393_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12, 13, 14], none)) "htab_item" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 11]

def crepBody393_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([15], none)) "htab_has" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 13]

def crepBody393_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 1 (Flapjack.CrepExp.var 16)

def crepBody393_8 : CrepProg (BitVec 64) :=
.seq crepBody393_7 crepBody393_2

def crepBody393_9 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 1#64]) crepBody393_8

def crepBody393_10 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.const 0#64)) crepBody393_9 crepBody393_2

def crepBody393_11 : CrepProg (BitVec 64) :=
.seq crepBody393_6 crepBody393_10

def crepBody393_12 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody393_11

def crepBody393_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.const 0#64)) crepBody393_12 crepBody393_2

def crepBody393_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 15)

def crepBody393_15 : CrepProg (BitVec 64) :=
.seq crepBody393_14 crepBody393_2

def crepBody393_16 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 1#64]) crepBody393_15

def crepBody393_17 : CrepProg (BitVec 64) :=
.seq crepBody393_13 crepBody393_16

def crepBody393_18 : CrepProg (BitVec 64) :=
.seq crepBody393_5 crepBody393_17

def crepBody393_19 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody393_18

def crepBody393_20 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody393_19

def crepBody393_21 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody393_20

def crepBody393_22 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 10)) crepBody393_21

def crepBody393_23 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody393_22

def crepBody393_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.const 24#64])) crepBody393_23

def crepBody393_25 : CrepProg (BitVec 64) :=
.seq crepBody393_4 crepBody393_24

def crepBody393_26 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 8#64])) crepBody393_25

def crepBody393_27 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64])) crepBody393_26

def crepBody393_28 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 6) crepBody393_27

def crepBody393_29 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.const 0#64)) crepBody393_28 crepBody393_2

def crepBody393_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 7)

def crepBody393_31 : CrepProg (BitVec 64) :=
.seq crepBody393_30 crepBody393_2

def crepBody393_32 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 1#64]) crepBody393_31

def crepBody393_33 : CrepProg (BitVec 64) :=
.seq crepBody393_29 crepBody393_32

def crepBody393_34 : CrepProg (BitVec 64) :=
.seq crepBody393_0 crepBody393_33

def crepBody393_35 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody393_34

def crepBody393_36 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody393_35

def crepBody393_37 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody393_36

def crepBody393_38 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.var 2)) crepBody393_37

def crepBody393_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "udiv" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 2000#64]

def crepBody393_40 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 5)

def crepBody393_41 : CrepProg (BitVec 64) :=
.seq crepBody393_40 crepBody393_2

def crepBody393_42 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 40#64) crepBody393_41

def crepBody393_43 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 4#64

def crepBody393_44 : CrepProg (BitVec 64) :=
.seq crepBody393_42 crepBody393_43

def crepBody393_45 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 1)) crepBody393_44 crepBody393_2

def crepBody393_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody393_47 : CrepProg (BitVec 64) :=
.seq crepBody393_45 crepBody393_46

def crepBody393_48 : CrepProg (BitVec 64) :=
.seq crepBody393_39 crepBody393_47

def crepBody393_49 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody393_48

def crepBody393_50 : CrepProg (BitVec 64) :=
.seq crepBody393_38 crepBody393_49

def crepBody393_51 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody393_50

def crepBody393_52 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 216#64]),
      Flapjack.CrepExp.const 24#64])) crepBody393_51

def crepBody393_53 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody393_52

def data393 : CrepProg (BitVec 64) := crepBody393_53
def output393 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 97#8, 99#8, 99#8,
    101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 103#8, 97#8, 115#8, 95#8, 108#8, 105#8, 109#8, 105#8,
    116#8], [0], crepProgToHOL data393)
end InitECandidate.Proofs.FrontendStages.Crep
