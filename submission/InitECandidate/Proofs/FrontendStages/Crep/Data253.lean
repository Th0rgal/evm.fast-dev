import InitECandidate.Proofs.FrontendStages.Crep.Translate237
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody253_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc"
  [Flapjack.CrepExp.op Flapjack.BinOp.add
      [Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64),
        Flapjack.CrepExp.const 2#64]]

def crepBody253_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.const 1#64)

def crepBody253_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody253_3 : CrepProg (BitVec 64) :=
.seq crepBody253_1 crepBody253_2

def crepBody253_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody253_3 crepBody253_2

def crepBody253_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "nibble_list_to_compact"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 32#64]),
    Flapjack.CrepExp.var 6, Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 4]

def crepBody253_6 : CrepProg (BitVec 64) :=
.seq crepBody253_4 crepBody253_5

def crepBody253_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "rlp_bytes_encoded_len"
  [Flapjack.CrepExp.loadByte (Flapjack.CrepExp.var 4), Flapjack.CrepExp.var 5]

def crepBody253_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 8)

def crepBody253_9 : CrepProg (BitVec 64) :=
.seq crepBody253_8 crepBody253_2

def crepBody253_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9], none)) "rlp_value_encoded_len"
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 48#64]),
    Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 56#64])]

def crepBody253_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 3 (Flapjack.CrepExp.var 10)

def crepBody253_12 : CrepProg (BitVec 64) :=
.seq crepBody253_11 crepBody253_2

def crepBody253_13 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.var 9]) crepBody253_12

def crepBody253_14 : CrepProg (BitVec 64) :=
.seq crepBody253_10 crepBody253_13

def crepBody253_15 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody253_14

def crepBody253_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 1#64)) crepBody253_15 crepBody253_2

def crepBody253_17 : CrepProg (BitVec 64) :=
.seq crepBody253_9 crepBody253_16

def crepBody253_18 : CrepProg (BitVec 64) :=
.seq crepBody253_7 crepBody253_17

def crepBody253_19 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody253_18

def crepBody253_20 : CrepProg (BitVec 64) :=
.seq crepBody253_6 crepBody253_19

def crepBody253_21 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody253_20

def crepBody253_22 : CrepProg (BitVec 64) :=
.seq crepBody253_0 crepBody253_21

def crepBody253_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 40#64])) crepBody253_22

def crepBody253_24 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 2) (Flapjack.CrepExp.const 3#64)) crepBody253_23 crepBody253_2

def crepBody253_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody253_26 : CrepProg (BitVec 64) :=
.seq crepBody253_25 crepBody253_2

def crepBody253_27 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 4) crepBody253_26

def crepBody253_28 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 24#64]) crepBody253_27

def crepBody253_29 : CrepProg (BitVec 64) :=
.seq crepBody253_24 crepBody253_28

def crepBody253_30 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 5) crepBody253_26

def crepBody253_31 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64]) crepBody253_30

def crepBody253_32 : CrepProg (BitVec 64) :=
.seq crepBody253_29 crepBody253_31

def crepBody253_33 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 3) crepBody253_26

def crepBody253_34 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 40#64]) crepBody253_33

def crepBody253_35 : CrepProg (BitVec 64) :=
.seq crepBody253_32 crepBody253_34

def crepBody253_36 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody253_37 : CrepProg (BitVec 64) :=
.seq crepBody253_35 crepBody253_36

def crepBody253_38 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody253_37

def crepBody253_39 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody253_38

def crepBody253_40 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody253_39

def crepBody253_41 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 1, Flapjack.CrepExp.const 0#64])) crepBody253_40

def data253 : CrepProg (BitVec 64) := crepBody253_41
def output253 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 98#8, 101#8, 103#8, 105#8, 110#8], [0, 1], crepProgToHOL data253)
end InitECandidate.Proofs.FrontendStages.Crep
