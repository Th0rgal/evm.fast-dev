import InitECandidate.Proofs.FrontendStages.Crep.Translate524
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody540_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([1], none)) "state_snapshot" []

def crepBody540_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "destroy_storage" [Flapjack.CrepExp.var 2]

def crepBody540_2 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody540_1

def crepBody540_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "mark_account_created" [Flapjack.CrepExp.var 2]

def crepBody540_4 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody540_3

def crepBody540_5 : CrepProg (BitVec 64) :=
.seq crepBody540_2 crepBody540_4

def crepBody540_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "increment_nonce" [Flapjack.CrepExp.var 2]

def crepBody540_7 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody540_6

def crepBody540_8 : CrepProg (BitVec 64) :=
.seq crepBody540_5 crepBody540_7

def crepBody540_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "process_message" [Flapjack.CrepExp.var 0]

def crepBody540_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 6)

def crepBody540_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody540_12 : CrepProg (BitVec 64) :=
.seq crepBody540_10 crepBody540_11

def crepBody540_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.var 3) crepBody540_12

def crepBody540_14 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]) crepBody540_13

def crepBody540_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody540_16 : CrepProg (BitVec 64) :=
.seq crepBody540_15 crepBody540_11

def crepBody540_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "state_restore" [Flapjack.CrepExp.var 1]

def crepBody540_18 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody540_17

def crepBody540_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "refill_frame_state_gas" []

def crepBody540_20 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody540_19

def crepBody540_21 : CrepProg (BitVec 64) :=
.seq crepBody540_18 crepBody540_20

def crepBody540_22 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "frame_halt" [Flapjack.CrepExp.var 5]

def crepBody540_23 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody540_22

def crepBody540_24 : CrepProg (BitVec 64) :=
.seq crepBody540_21 crepBody540_23

def crepBody540_25 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.var 7)

def crepBody540_26 : CrepProg (BitVec 64) :=
.seq crepBody540_25 crepBody540_11

def crepBody540_27 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 264#64])) crepBody540_26

def crepBody540_28 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 120#64]) crepBody540_27

def crepBody540_29 : CrepProg (BitVec 64) :=
.seq crepBody540_24 crepBody540_28

def crepBody540_30 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody540_26

def crepBody540_31 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.add
  [Flapjack.CrepExp.load
      (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]),
    Flapjack.CrepExp.const 128#64]) crepBody540_30

def crepBody540_32 : CrepProg (BitVec 64) :=
.seq crepBody540_29 crepBody540_31

def crepBody540_33 : CrepProg (BitVec 64) :=
.seq crepBody540_16 crepBody540_32

def crepBody540_34 : CrepProg (BitVec 64) :=
.call (some (([6]), some ((8#64), crepBody540_33))) ("create_finish") ([Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 3])

def crepBody540_35 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody540_34

def crepBody540_36 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.var 4) crepBody540_26

def crepBody540_37 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64]) crepBody540_36

def crepBody540_38 : CrepProg (BitVec 64) :=
.seq crepBody540_35 crepBody540_37

def crepBody540_39 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 3]

def crepBody540_40 : CrepProg (BitVec 64) :=
.seq crepBody540_38 crepBody540_39

def crepBody540_41 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody540_40

def crepBody540_42 : CrepProg (BitVec 64) :=
.seq crepBody540_14 crepBody540_41

def crepBody540_43 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 256#64])) crepBody540_42

def crepBody540_44 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal
  (Flapjack.CrepExp.load
    (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 3, Flapjack.CrepExp.const 160#64]))
  (Flapjack.CrepExp.const 0#64)) crepBody540_43 crepBody540_11

def crepBody540_45 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "state_restore" [Flapjack.CrepExp.var 1]

def crepBody540_46 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody540_45

def crepBody540_47 : CrepProg (BitVec 64) :=
.seq crepBody540_44 crepBody540_46

def crepBody540_48 : CrepProg (BitVec 64) :=
.seq crepBody540_47 crepBody540_39

def crepBody540_49 : CrepProg (BitVec 64) :=
.seq crepBody540_9 crepBody540_48

def crepBody540_50 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody540_49

def crepBody540_51 : CrepProg (BitVec 64) :=
.seq crepBody540_8 crepBody540_50

def crepBody540_52 : CrepProg (BitVec 64) :=
.dec 2 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.const 32#64])) crepBody540_51

def crepBody540_53 : CrepProg (BitVec 64) :=
.seq crepBody540_0 crepBody540_52

def crepBody540_54 : CrepProg (BitVec 64) :=
.dec 1 (Flapjack.CrepExp.const 0#64) crepBody540_53

def data540 : CrepProg (BitVec 64) := crepBody540_54
def output540 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 109#8, 101#8,
    115#8, 115#8, 97#8, 103#8, 101#8], [0], crepProgToHOL data540)
end InitECandidate.Proofs.FrontendStages.Crep
