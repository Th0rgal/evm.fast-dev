import InitECandidate.Proofs.FrontendStages.Crep.Translate300
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody316_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "count_tokens_in_data" [Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody316_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "u256_is_zero"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 8#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 16#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add
        [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 160#64],
          Flapjack.CrepExp.const 24#64])]

def crepBody316_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 12000#64)

def crepBody316_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody316_4 : CrepProg (BitVec 64) :=
.seq crepBody316_2 crepBody316_3

def crepBody316_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9
  (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
    [Flapjack.CrepExp.const 2#64,
      Flapjack.CrepExp.shift Flapjack.Shift.lsr
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 31#64])
        (Flapjack.CrepExp.const 5#64)])

def crepBody316_6 : CrepProg (BitVec 64) :=
.seq crepBody316_5 crepBody316_3

def crepBody316_7 : CrepProg (BitVec 64) :=
.seq crepBody316_4 crepBody316_6

def crepBody316_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "memeq"
  [Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 20#64]

def crepBody316_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.const 3000#64)

def crepBody316_10 : CrepProg (BitVec 64) :=
.seq crepBody316_9 crepBody316_3

def crepBody316_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 8 (Flapjack.CrepExp.var 11)

def crepBody316_12 : CrepProg (BitVec 64) :=
.seq crepBody316_11 crepBody316_3

def crepBody316_13 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 8, Flapjack.CrepExp.const 6000#64]) crepBody316_12

def crepBody316_14 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 0#64)) crepBody316_13 crepBody316_3

def crepBody316_15 : CrepProg (BitVec 64) :=
.seq crepBody316_10 crepBody316_14

def crepBody316_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 10) (Flapjack.CrepExp.const 0#64)) crepBody316_15 crepBody316_3

def crepBody316_17 : CrepProg (BitVec 64) :=
.seq crepBody316_8 crepBody316_16

def crepBody316_18 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody316_17

def crepBody316_19 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 0#64)) crepBody316_7 crepBody316_18

def crepBody316_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 16)

def crepBody316_21 : CrepProg (BitVec 64) :=
.seq crepBody316_20 crepBody316_3

def crepBody316_22 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 3000#64, Flapjack.CrepExp.const 100#64],
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
      [Flapjack.CrepExp.var 15,
        Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 2100#64, Flapjack.CrepExp.const 100#64]]]) crepBody316_21

def crepBody316_23 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 16)

def crepBody316_24 : CrepProg (BitVec 64) :=
.seq crepBody316_23 crepBody316_3

def crepBody316_25 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 80#64,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 15, Flapjack.CrepExp.const 128#64]]) crepBody316_24

def crepBody316_26 : CrepProg (BitVec 64) :=
.seq crepBody316_22 crepBody316_25

def crepBody316_27 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 14 (Flapjack.CrepExp.var 16)

def crepBody316_28 : CrepProg (BitVec 64) :=
.seq crepBody316_27 crepBody316_3

def crepBody316_29 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 1#64]) crepBody316_28

def crepBody316_30 : CrepProg (BitVec 64) :=
.seq crepBody316_26 crepBody316_29

def crepBody316_31 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.var 12,
      Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 24#64],
      Flapjack.CrepExp.const 16#64])) crepBody316_30

def crepBody316_32 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 14) (Flapjack.CrepExp.var 13)) crepBody316_31

def crepBody316_33 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.const 0#64) crepBody316_32

def crepBody316_34 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 216#64])) crepBody316_33

def crepBody316_35 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 208#64])) crepBody316_34

def crepBody316_36 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody316_35 crepBody316_3

def crepBody316_37 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 12)

def crepBody316_38 : CrepProg (BitVec 64) :=
.seq crepBody316_37 crepBody316_3

def crepBody316_39 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 16#64]]) crepBody316_38

def crepBody316_40 : CrepProg (BitVec 64) :=
.seq crepBody316_36 crepBody316_39

def crepBody316_41 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 12
  (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul
    [Flapjack.CrepExp.const 7816#64,
      Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 280#64])])

def crepBody316_42 : CrepProg (BitVec 64) :=
.seq crepBody316_41 crepBody316_3

def crepBody316_43 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 0#64]))
  (Flapjack.CrepExp.const 4#64)) crepBody316_42 crepBody316_3

def crepBody316_44 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 16, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 17]

def crepBody316_45 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 14, Flapjack.CrepExp.const 16#64],
    Flapjack.CrepExp.var 15]) crepBody316_44

def crepBody316_46 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.var 15, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 10,
    Flapjack.CrepExp.var 12]) crepBody316_45

def crepBody316_47 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.const 12000#64, Flapjack.CrepExp.var 8]) crepBody316_46

def crepBody316_48 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 11]) crepBody316_47

def crepBody316_49 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 4#64]) crepBody316_48

def crepBody316_50 : CrepProg (BitVec 64) :=
.seq crepBody316_43 crepBody316_49

def crepBody316_51 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody316_50

def crepBody316_52 : CrepProg (BitVec 64) :=
.seq crepBody316_40 crepBody316_51

def crepBody316_53 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody316_52

def crepBody316_54 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody316_53

def crepBody316_55 : CrepProg (BitVec 64) :=
.seq crepBody316_19 crepBody316_54

def crepBody316_56 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody316_55

def crepBody316_57 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody316_56

def crepBody316_58 : CrepProg (BitVec 64) :=
.seq crepBody316_1 crepBody316_57

def crepBody316_59 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody316_58

def crepBody316_60 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 152#64])) crepBody316_59

def crepBody316_61 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.crepOp Flapjack.CrepOp.mul [Flapjack.CrepExp.var 4, Flapjack.CrepExp.const 4#64]) crepBody316_60

def crepBody316_62 : CrepProg (BitVec 64) :=
.seq crepBody316_0 crepBody316_61

def crepBody316_63 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody316_62

def crepBody316_64 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 200#64])) crepBody316_63

def crepBody316_65 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 192#64])) crepBody316_64

def data316 : CrepProg (BitVec 64) := crepBody316_65
def output316 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 105#8, 110#8, 116#8, 114#8, 105#8, 110#8, 115#8,
    105#8, 99#8, 95#8, 99#8, 111#8, 115#8, 116#8], [0, 1], crepProgToHOL data316)
end InitECandidate.Proofs.FrontendStages.Crep
