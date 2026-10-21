import InitECandidate.Proofs.FrontendStages.Crep.Translate758
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody774_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 0#64]),
    Flapjack.CrepExp.const 20#64]

def crepBody774_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 9)

def crepBody774_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody774_3 : CrepProg (BitVec 64) :=
.seq crepBody774_1 crepBody774_2

def crepBody774_4 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]) crepBody774_3

def crepBody774_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.load
          (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]),
        Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 32#64]],
    Flapjack.CrepExp.const 32#64]

def crepBody774_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 13)

def crepBody774_7 : CrepProg (BitVec 64) :=
.seq crepBody774_6 crepBody774_2

def crepBody774_8 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 8]) crepBody774_7

def crepBody774_9 : CrepProg (BitVec 64) :=
.seq crepBody774_5 crepBody774_8

def crepBody774_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12 (Flapjack.CrepExp.var 13)

def crepBody774_11 : CrepProg (BitVec 64) :=
.seq crepBody774_10 crepBody774_2

def crepBody774_12 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 1#64]) crepBody774_11

def crepBody774_13 : CrepProg (BitVec 64) :=
.seq crepBody774_9 crepBody774_12

def crepBody774_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 11)) crepBody774_13

def crepBody774_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_finish_list" [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10]

def crepBody774_16 : CrepProg (BitVec 64) :=
.seq crepBody774_14 crepBody774_15

def crepBody774_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 8])

def crepBody774_18 : CrepProg (BitVec 64) :=
.seq crepBody774_17 crepBody774_2

def crepBody774_19 : CrepProg (BitVec 64) :=
.seq crepBody774_16 crepBody774_18

def crepBody774_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_encode_bytes"
  [Flapjack.CrepExp.var 7,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 32#64])]

def crepBody774_21 : CrepProg (BitVec 64) :=
.seq crepBody774_19 crepBody774_20

def crepBody774_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.var 13)

def crepBody774_23 : CrepProg (BitVec 64) :=
.seq crepBody774_22 crepBody774_2

def crepBody774_24 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]) crepBody774_23

def crepBody774_25 : CrepProg (BitVec 64) :=
.seq crepBody774_21 crepBody774_24

def crepBody774_26 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_finish_list" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 7]

def crepBody774_27 : CrepProg (BitVec 64) :=
.seq crepBody774_25 crepBody774_26

def crepBody774_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 13)

def crepBody774_29 : CrepProg (BitVec 64) :=
.seq crepBody774_28 crepBody774_2

def crepBody774_30 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 8]) crepBody774_29

def crepBody774_31 : CrepProg (BitVec 64) :=
.seq crepBody774_27 crepBody774_30

def crepBody774_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 13)

def crepBody774_33 : CrepProg (BitVec 64) :=
.seq crepBody774_32 crepBody774_2

def crepBody774_34 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64]) crepBody774_33

def crepBody774_35 : CrepProg (BitVec 64) :=
.seq crepBody774_31 crepBody774_34

def crepBody774_36 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody774_35

def crepBody774_37 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 16#64])) crepBody774_36

def crepBody774_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 9#64]) crepBody774_37

def crepBody774_39 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.var 7) crepBody774_38

def crepBody774_40 : CrepProg (BitVec 64) :=
.seq crepBody774_4 crepBody774_39

def crepBody774_41 : CrepProg (BitVec 64) :=
.seq crepBody774_0 crepBody774_40

def crepBody774_42 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody774_41

def crepBody774_43 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 9#64]) crepBody774_42

def crepBody774_44 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 3,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 8#64]])) crepBody774_43

def crepBody774_45 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 2)) crepBody774_44

def crepBody774_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "rlp_finish_list" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]

def crepBody774_47 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 6]

def crepBody774_48 : CrepProg (BitVec 64) :=
.seq crepBody774_46 crepBody774_47

def crepBody774_49 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody774_48

def crepBody774_50 : CrepProg (BitVec 64) :=
.seq crepBody774_45 crepBody774_49

def crepBody774_51 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody774_50

def crepBody774_52 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 9#64]) crepBody774_51

def crepBody774_53 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody774_52

def crepBody774_54 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 8#64])) crepBody774_53

def data774 : CrepProg (BitVec 64) := crepBody774_54
def output774 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 108#8, 111#8, 103#8, 115#8], [0, 1], crepProgToHOL data774)
end InitECandidate.Proofs.FrontendStages.Crep
