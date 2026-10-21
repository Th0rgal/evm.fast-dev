import InitECandidate.Proofs.FrontendStages.Crep.Translate336
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody352_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "get_account_optional" [Flapjack.CrepExp.var 0]

def crepBody352_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeGlob (0#5) (Flapjack.CrepExp.var 7)

def crepBody352_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody352_3 : CrepProg (BitVec 64) :=
.seq crepBody352_1 crepBody352_2

def crepBody352_4 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 3#64) crepBody352_3

def crepBody352_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.raise 7#64

def crepBody352_6 : CrepProg (BitVec 64) :=
.seq crepBody352_4 crepBody352_5

def crepBody352_7 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 6) (Flapjack.CrepExp.const 1#64)) crepBody352_6 crepBody352_2

def crepBody352_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8, 9], none)) "htab_get" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 0]

def crepBody352_9 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "htab_new" [Flapjack.CrepExp.const 32#64, Flapjack.CrepExp.const 8#64]

def crepBody352_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "jset"
  [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 10]

def crepBody352_11 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody352_10

def crepBody352_12 : CrepProg (BitVec 64) :=
.seq crepBody352_9 crepBody352_11

def crepBody352_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 10 (Flapjack.CrepExp.var 9)

def crepBody352_14 : CrepProg (BitVec 64) :=
.seq crepBody352_13 crepBody352_2

def crepBody352_15 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody352_12 crepBody352_14

def crepBody352_16 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody352_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)

def crepBody352_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 14)

def crepBody352_19 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 15)

def crepBody352_20 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 16)

def crepBody352_21 : CrepProg (BitVec 64) :=
.seq crepBody352_20 crepBody352_2

def crepBody352_22 : CrepProg (BitVec 64) :=
.seq crepBody352_19 crepBody352_21

def crepBody352_23 : CrepProg (BitVec 64) :=
.seq crepBody352_18 crepBody352_22

def crepBody352_24 : CrepProg (BitVec 64) :=
.seq crepBody352_17 crepBody352_23

def crepBody352_25 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 5) crepBody352_24

def crepBody352_26 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 4) crepBody352_25

def crepBody352_27 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 3) crepBody352_26

def crepBody352_28 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 2) crepBody352_27

def crepBody352_29 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.var 11) crepBody352_28

def crepBody352_30 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "jset"
  [Flapjack.CrepExp.var 10, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 11]

def crepBody352_31 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody352_30

def crepBody352_32 : CrepProg (BitVec 64) :=
.seq crepBody352_29 crepBody352_31

def crepBody352_33 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody352_34 : CrepProg (BitVec 64) :=
.seq crepBody352_32 crepBody352_33

def crepBody352_35 : CrepProg (BitVec 64) :=
.seq crepBody352_16 crepBody352_34

def crepBody352_36 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody352_35

def crepBody352_37 : CrepProg (BitVec 64) :=
.seq crepBody352_15 crepBody352_36

def crepBody352_38 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody352_37

def crepBody352_39 : CrepProg (BitVec 64) :=
.seq crepBody352_8 crepBody352_38

def crepBody352_40 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody352_39

def crepBody352_41 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody352_40

def crepBody352_42 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.load
  (Flapjack.CrepExp.op Flapjack.BinOp.add
    [Flapjack.CrepExp.load
        (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.topAddr, Flapjack.CrepExp.const 184#64]),
      Flapjack.CrepExp.const 32#64])) crepBody352_41

def crepBody352_43 : CrepProg (BitVec 64) :=
.seq crepBody352_7 crepBody352_42

def crepBody352_44 : CrepProg (BitVec 64) :=
.seq crepBody352_0 crepBody352_43

def crepBody352_45 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody352_44

def data352 : CrepProg (BitVec 64) := crepBody352_45
def output352 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [115#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8], [0, 1, 2, 3, 4, 5], crepProgToHOL data352)
end InitECandidate.Proofs.FrontendStages.Crep
