import InitECandidate.Proofs.FrontendStages.Crep.Translate216
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody232_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 7 (Flapjack.CrepExp.loadGlob 0#5)

def crepBody232_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody232_2 : CrepProg (BitVec 64) :=
.seq crepBody232_0 crepBody232_1

def crepBody232_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 3#64]

def crepBody232_4 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody232_3

def crepBody232_5 : CrepProg (BitVec 64) :=
.seq crepBody232_2 crepBody232_4

def crepBody232_6 : CrepProg (BitVec 64) :=
.call (some (([3, 4, 5, 6]), some ((1#64), crepBody232_5))) ("rlp_item") ([Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2])

def crepBody232_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody232_8 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 0#64)) crepBody232_7 crepBody232_1

def crepBody232_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "mpt_fail" [Flapjack.CrepExp.const 10#64]

def crepBody232_10 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody232_9

def crepBody232_11 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.notEqual (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 32#64)) crepBody232_10 crepBody232_1

def crepBody232_12 : CrepProg (BitVec 64) :=
.seq crepBody232_8 crepBody232_11

def crepBody232_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9, 10], none)) "nodedb_lookup" [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 4]

def crepBody232_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "node_new_hashed" [Flapjack.CrepExp.var 4]

def crepBody232_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 0#64, Flapjack.CrepExp.const 0#64]

def crepBody232_16 : CrepProg (BitVec 64) :=
.seq crepBody232_14 crepBody232_15

def crepBody232_17 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody232_16

def crepBody232_18 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody232_17 crepBody232_1

def crepBody232_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 9, Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 4]

def crepBody232_20 : CrepProg (BitVec 64) :=
.seq crepBody232_18 crepBody232_19

def crepBody232_21 : CrepProg (BitVec 64) :=
.seq crepBody232_13 crepBody232_20

def crepBody232_22 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody232_21

def crepBody232_23 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody232_22

def crepBody232_24 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody232_23

def crepBody232_25 : CrepProg (BitVec 64) :=
.seq crepBody232_12 crepBody232_24

def crepBody232_26 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 3) (Flapjack.CrepExp.const 0#64)) crepBody232_25 crepBody232_1

def crepBody232_27 : CrepProg (BitVec 64) :=
.seq crepBody232_6 crepBody232_26

def crepBody232_28 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.const 1#64, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.const 0#64]

def crepBody232_29 : CrepProg (BitVec 64) :=
.seq crepBody232_27 crepBody232_28

def crepBody232_30 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody232_29

def crepBody232_31 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody232_30

def crepBody232_32 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody232_31

def crepBody232_33 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody232_32

def crepBody232_34 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody232_33

def data232 : CrepProg (BitVec 64) := crepBody232_34
def output232 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [95#8, 114#8, 101#8, 115#8, 111#8, 108#8, 118#8, 101#8, 95#8, 115#8, 116#8, 101#8, 112#8], [0, 1, 2], crepProgToHOL data232)
end InitECandidate.Proofs.FrontendStages.Crep
