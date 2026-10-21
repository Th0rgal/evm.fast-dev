import InitECandidate.Proofs.FrontendStages.Crep.Translate366
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody382_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "st_le64"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64])]

def crepBody382_1 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody382_0

def crepBody382_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64], Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.const 20#64]

def crepBody382_3 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody382_2

def crepBody382_4 : CrepProg (BitVec 64) :=
.seq crepBody382_1 crepBody382_3

def crepBody382_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 28#64],
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]

def crepBody382_6 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody382_5

def crepBody382_7 : CrepProg (BitVec 64) :=
.seq crepBody382_4 crepBody382_6

def crepBody382_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3, 4], none)) "htab_get"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 240#64]),
    Flapjack.CrepExp.var 2]

def crepBody382_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.load (Flapjack.CrepExp.var 4),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 24#64])]

def crepBody382_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody382_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody382_9 crepBody382_10

def crepBody382_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5, 6, 7, 8], none)) "get_pre_tx_storage" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1]

def crepBody382_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody382_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.var 11)

def crepBody382_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 12)

def crepBody382_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 13)

def crepBody382_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 10, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 14)

def crepBody382_18 : CrepProg (BitVec 64) :=
.seq crepBody382_17 crepBody382_10

def crepBody382_19 : CrepProg (BitVec 64) :=
.seq crepBody382_16 crepBody382_18

def crepBody382_20 : CrepProg (BitVec 64) :=
.seq crepBody382_15 crepBody382_19

def crepBody382_21 : CrepProg (BitVec 64) :=
.seq crepBody382_14 crepBody382_20

def crepBody382_22 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 8) crepBody382_21

def crepBody382_23 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 7) crepBody382_22

def crepBody382_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 6) crepBody382_23

def crepBody382_25 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.var 5) crepBody382_24

def crepBody382_26 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.var 9) crepBody382_25

def crepBody382_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "st_le64"
  [Flapjack.CrepExp.var 2,
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 224#64])]

def crepBody382_28 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody382_27

def crepBody382_29 : CrepProg (BitVec 64) :=
.seq crepBody382_26 crepBody382_28

def crepBody382_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 8#64], Flapjack.CrepExp.var 0,
    Flapjack.CrepExp.const 20#64]

def crepBody382_31 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody382_30

def crepBody382_32 : CrepProg (BitVec 64) :=
.seq crepBody382_29 crepBody382_31

def crepBody382_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memcpy"
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 28#64],
    Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]

def crepBody382_34 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody382_33

def crepBody382_35 : CrepProg (BitVec 64) :=
.seq crepBody382_32 crepBody382_34

def crepBody382_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "htab_set"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 240#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 9]

def crepBody382_37 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody382_36

def crepBody382_38 : CrepProg (BitVec 64) :=
.seq crepBody382_35 crepBody382_37

def crepBody382_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 8]

def crepBody382_40 : CrepProg (BitVec 64) :=
.seq crepBody382_38 crepBody382_39

def crepBody382_41 : CrepProg (BitVec 64) :=
.seq crepBody382_13 crepBody382_40

def crepBody382_42 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody382_41

def crepBody382_43 : CrepProg (BitVec 64) :=
.seq crepBody382_12 crepBody382_42

def crepBody382_44 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody382_43

def crepBody382_45 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody382_44

def crepBody382_46 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody382_45

def crepBody382_47 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody382_46

def crepBody382_48 : CrepProg (BitVec 64) :=
.seq crepBody382_11 crepBody382_47

def crepBody382_49 : CrepProg (BitVec 64) :=
.seq crepBody382_8 crepBody382_48

def crepBody382_50 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody382_49

def crepBody382_51 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody382_50

def crepBody382_52 : CrepProg (BitVec 64) :=
.seq crepBody382_7 crepBody382_51

def crepBody382_53 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 248#64])) crepBody382_52

def data382 : CrepProg (BitVec 64) := crepBody382_53
def output382 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [105#8, 100#8, 120#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8], [0, 1], crepProgToHOL data382)
end InitECandidate.Proofs.FrontendStages.Crep
