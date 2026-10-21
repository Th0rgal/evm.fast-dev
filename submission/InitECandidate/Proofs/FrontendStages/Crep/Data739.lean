import InitECandidate.Proofs.FrontendStages.Crep.Translate723
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody739_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([2, 3, 4, 5], none)) "u256_from_be" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]

def crepBody739_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody739_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.var 12)

def crepBody739_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 13)

def crepBody739_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 14)

def crepBody739_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 15)

def crepBody739_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody739_7 : CrepProg (BitVec 64) :=
.seq crepBody739_5 crepBody739_6

def crepBody739_8 : CrepProg (BitVec 64) :=
.seq crepBody739_4 crepBody739_7

def crepBody739_9 : CrepProg (BitVec 64) :=
.seq crepBody739_3 crepBody739_8

def crepBody739_10 : CrepProg (BitVec 64) :=
.seq crepBody739_2 crepBody739_9

def crepBody739_11 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.const 0#64) crepBody739_10

def crepBody739_12 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody739_11

def crepBody739_13 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody739_12

def crepBody739_14 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody739_13

def crepBody739_15 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 1) crepBody739_14

def crepBody739_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody739_17 : CrepProg (BitVec 64) :=
.seq crepBody739_15 crepBody739_16

def crepBody739_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 1#64)) crepBody739_17 crepBody739_6

def crepBody739_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11, 12, 13, 14], none)) "u256_sub"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 9,
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody739_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 15) (Flapjack.CrepExp.var 16)

def crepBody739_21 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 17)

def crepBody739_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 18)

def crepBody739_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 19)

def crepBody739_24 : CrepProg (BitVec 64) :=
.seq crepBody739_23 crepBody739_6

def crepBody739_25 : CrepProg (BitVec 64) :=
.seq crepBody739_22 crepBody739_24

def crepBody739_26 : CrepProg (BitVec 64) :=
.seq crepBody739_21 crepBody739_25

def crepBody739_27 : CrepProg (BitVec 64) :=
.seq crepBody739_20 crepBody739_26

def crepBody739_28 : CrepProg (BitVec 64) :=
.dec 19 (Flapjack.CrepExp.var 14) crepBody739_27

def crepBody739_29 : CrepProg (BitVec 64) :=
.dec 18 (Flapjack.CrepExp.var 13) crepBody739_28

def crepBody739_30 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 12) crepBody739_29

def crepBody739_31 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 11) crepBody739_30

def crepBody739_32 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 1) crepBody739_31

def crepBody739_33 : CrepProg (BitVec 64) :=
.seq crepBody739_32 crepBody739_16

def crepBody739_34 : CrepProg (BitVec 64) :=
.seq crepBody739_19 crepBody739_33

def crepBody739_35 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody739_34

def crepBody739_36 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody739_35

def crepBody739_37 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody739_36

def crepBody739_38 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody739_37

def crepBody739_39 : CrepProg (BitVec 64) :=
.seq crepBody739_18 crepBody739_38

def crepBody739_40 : CrepProg (BitVec 64) :=
.seq crepBody739_1 crepBody739_39

def crepBody739_41 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody739_40

def crepBody739_42 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
          Flapjack.CrepExp.const 1344#64],
      Flapjack.CrepExp.const 24#64])) crepBody739_41

def crepBody739_43 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
          Flapjack.CrepExp.const 1344#64],
      Flapjack.CrepExp.const 16#64])) crepBody739_42

def crepBody739_44 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.load
            (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
          Flapjack.CrepExp.const 1344#64],
      Flapjack.CrepExp.const 8#64])) crepBody739_43

def crepBody739_45 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 392#64]),
      Flapjack.CrepExp.const 1344#64])) crepBody739_44

def crepBody739_46 : CrepProg (BitVec 64) :=
.seq crepBody739_0 crepBody739_45

def crepBody739_47 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody739_46

def crepBody739_48 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody739_47

def crepBody739_49 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody739_48

def crepBody739_50 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.const 0#64) crepBody739_49

def data739 : CrepProg (BitVec 64) := crepBody739_50
def output739 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [107#8, 122#8, 103#8, 95#8, 110#8, 101#8, 103#8, 95#8, 115#8, 99#8, 97#8, 108#8, 97#8, 114#8], [0, 1], crepProgToHOL data739)
end InitECandidate.Proofs.FrontendStages.Crep
