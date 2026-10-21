import InitECandidate.Proofs.FrontendStages.Crep.Translate349
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody365_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_union_into"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 24#64])]

def crepBody365_1 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody365_0

def crepBody365_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_union_into"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 8#64])]

def crepBody365_3 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody365_2

def crepBody365_4 : CrepProg (BitVec 64) :=
.seq crepBody365_1 crepBody365_3

def crepBody365_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_union_into"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 40#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 40#64])]

def crepBody365_6 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody365_5

def crepBody365_7 : CrepProg (BitVec 64) :=
.seq crepBody365_4 crepBody365_6

def crepBody365_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_union_into"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 16#64])]

def crepBody365_9 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody365_8

def crepBody365_10 : CrepProg (BitVec 64) :=
.seq crepBody365_7 crepBody365_9

def crepBody365_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "htab_union_into"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
          Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
          Flapjack.CrepExp.const 48#64])]

def crepBody365_12 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody365_11

def crepBody365_13 : CrepProg (BitVec 64) :=
.seq crepBody365_10 crepBody365_12

def crepBody365_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7], none)) "htab_item" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 4]

def crepBody365_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9], none)) "htab_get" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 6]

def crepBody365_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 8#64]

def crepBody365_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "htab_set"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 10]

def crepBody365_18 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody365_17

def crepBody365_19 : CrepProg (BitVec 64) :=
.seq crepBody365_16 crepBody365_18

def crepBody365_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 9)

def crepBody365_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody365_22 : CrepProg (BitVec 64) :=
.seq crepBody365_20 crepBody365_21

def crepBody365_23 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody365_19 crepBody365_22

def crepBody365_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "htab_union_into" [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 7]

def crepBody365_25 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody365_24

def crepBody365_26 : CrepProg (BitVec 64) :=
.seq crepBody365_23 crepBody365_25

def crepBody365_27 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody365_26

def crepBody365_28 : CrepProg (BitVec 64) :=
.seq crepBody365_15 crepBody365_27

def crepBody365_29 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody365_28

def crepBody365_30 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody365_29

def crepBody365_31 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody365_30 crepBody365_21

def crepBody365_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 4 (Flapjack.CrepExp.var 8)

def crepBody365_33 : CrepProg (BitVec 64) :=
.seq crepBody365_32 crepBody365_21

def crepBody365_34 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 1#64]) crepBody365_33

def crepBody365_35 : CrepProg (BitVec 64) :=
.seq crepBody365_31 crepBody365_34

def crepBody365_36 : CrepProg (BitVec 64) :=
.seq crepBody365_14 crepBody365_35

def crepBody365_37 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody365_36

def crepBody365_38 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody365_37

def crepBody365_39 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody365_38

def crepBody365_40 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 4) (Flapjack.CrepExp.var 3)) crepBody365_39

def crepBody365_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody365_42 : CrepProg (BitVec 64) :=
.seq crepBody365_40 crepBody365_41

def crepBody365_43 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody365_42

def crepBody365_44 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 24#64])) crepBody365_43

def crepBody365_45 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 176#64]),
      Flapjack.CrepExp.const 32#64])) crepBody365_44

def crepBody365_46 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
      Flapjack.CrepExp.const 32#64])) crepBody365_45

def crepBody365_47 : CrepProg (BitVec 64) :=
.seq crepBody365_13 crepBody365_46

def data365 : CrepProg (BitVec 64) := crepBody365_47
def output365 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [109#8, 101#8, 114#8, 103#8, 101#8, 95#8, 116#8, 120#8, 95#8, 105#8, 110#8, 116#8, 111#8, 95#8, 98#8, 108#8, 111#8,
    99#8, 107#8], [], crepProgToHOL data365)
end InitECandidate.Proofs.FrontendStages.Crep
