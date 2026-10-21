import InitECandidate.Proofs.FrontendStages.Crep.Translate343
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody359_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "get_account" [Flapjack.CrepExp.var 0]

def crepBody359_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "u256_lt"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody359_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 8)

def crepBody359_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody359_4 : CrepProg (BitVec 64) :=
.seq crepBody359_2 crepBody359_3

def crepBody359_5 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 4#64) crepBody359_4

def crepBody359_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 7#64

def crepBody359_7 : CrepProg (BitVec 64) :=
.seq crepBody359_5 crepBody359_6

def crepBody359_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody359_7 crepBody359_3

def crepBody359_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "acct_copy" [Flapjack.CrepExp.var 6]

def crepBody359_10 : CrepProg (BitVec 64) :=
.seq crepBody359_8 crepBody359_9

def crepBody359_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11], none)) "u256_sub"
  [Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody359_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody359_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 14)

def crepBody359_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 15)

def crepBody359_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 16)

def crepBody359_16 : CrepProg (BitVec 64) :=
.seq crepBody359_15 crepBody359_3

def crepBody359_17 : CrepProg (BitVec 64) :=
.seq crepBody359_14 crepBody359_16

def crepBody359_18 : CrepProg (BitVec 64) :=
.seq crepBody359_13 crepBody359_17

def crepBody359_19 : CrepProg (BitVec 64) :=
.seq crepBody359_12 crepBody359_18

def crepBody359_20 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 11) crepBody359_19

def crepBody359_21 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 10) crepBody359_20

def crepBody359_22 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 9) crepBody359_21

def crepBody359_23 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 8) crepBody359_22

def crepBody359_24 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 6, Flapjack.CrepExp.const 8#64]) crepBody359_23

def crepBody359_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "modify_state_commit" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 6]

def crepBody359_26 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody359_25

def crepBody359_27 : CrepProg (BitVec 64) :=
.seq crepBody359_24 crepBody359_26

def crepBody359_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "get_account" [Flapjack.CrepExp.var 1]

def crepBody359_29 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "acct_copy" [Flapjack.CrepExp.var 12]

def crepBody359_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10, 11], none)) "u256_add"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64],
          Flapjack.CrepExp.const 24#64]),
    Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]

def crepBody359_31 : CrepProg (BitVec 64) :=
.seq crepBody359_29 crepBody359_30

def crepBody359_32 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody359_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 15)

def crepBody359_34 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 16)

def crepBody359_35 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 17)

def crepBody359_36 : CrepProg (BitVec 64) :=
.seq crepBody359_35 crepBody359_3

def crepBody359_37 : CrepProg (BitVec 64) :=
.seq crepBody359_34 crepBody359_36

def crepBody359_38 : CrepProg (BitVec 64) :=
.seq crepBody359_33 crepBody359_37

def crepBody359_39 : CrepProg (BitVec 64) :=
.seq crepBody359_32 crepBody359_38

def crepBody359_40 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 11) crepBody359_39

def crepBody359_41 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 10) crepBody359_40

def crepBody359_42 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 9) crepBody359_41

def crepBody359_43 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 8) crepBody359_42

def crepBody359_44 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]) crepBody359_43

def crepBody359_45 : CrepProg (BitVec 64) :=
.seq crepBody359_31 crepBody359_44

def crepBody359_46 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([13], none)) "modify_state_commit" [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 12]

def crepBody359_47 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.const 0#64) crepBody359_46

def crepBody359_48 : CrepProg (BitVec 64) :=
.seq crepBody359_45 crepBody359_47

def crepBody359_49 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody359_50 : CrepProg (BitVec 64) :=
.seq crepBody359_48 crepBody359_49

def crepBody359_51 : CrepProg (BitVec 64) :=
.seq crepBody359_28 crepBody359_50

def crepBody359_52 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody359_51

def crepBody359_53 : CrepProg (BitVec 64) :=
.seq crepBody359_27 crepBody359_52

def crepBody359_54 : CrepProg (BitVec 64) :=
.seq crepBody359_11 crepBody359_53

def crepBody359_55 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody359_54

def crepBody359_56 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody359_55

def crepBody359_57 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody359_56

def crepBody359_58 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody359_57

def crepBody359_59 : CrepProg (BitVec 64) :=
.seq crepBody359_10 crepBody359_58

def crepBody359_60 : CrepProg (BitVec 64) :=
.seq crepBody359_1 crepBody359_59

def crepBody359_61 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody359_60

def crepBody359_62 : CrepProg (BitVec 64) :=
.seq crepBody359_0 crepBody359_61

def crepBody359_63 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody359_62

def data359 : CrepProg (BitVec 64) := crepBody359_63
def output359 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode [109#8, 111#8, 118#8, 101#8, 95#8, 101#8, 116#8, 104#8, 101#8, 114#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data359)
end InitECandidate.Proofs.FrontendStages.Crep
