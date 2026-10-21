import InitECandidate.Proofs.FrontendStages.Crep.Translate357
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody373_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([7], none)) "bal_ensure_account" [Flapjack.CrepExp.var 0]

def crepBody373_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([9, 10], none)) "htab_get" [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1]

def crepBody373_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "lst_new" [Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.const 2#64]

def crepBody373_3 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "htab_set"
  [Flapjack.CrepExp.var 8, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 11]

def crepBody373_4 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody373_3

def crepBody373_5 : CrepProg (BitVec 64) :=
.seq crepBody373_2 crepBody373_4

def crepBody373_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 11 (Flapjack.CrepExp.var 10)

def crepBody373_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody373_8 : CrepProg (BitVec 64) :=
.seq crepBody373_6 crepBody373_7

def crepBody373_9 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 9) (Flapjack.CrepExp.const 0#64)) crepBody373_5 crepBody373_8

def crepBody373_10 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "lst_upsert_idx"
  [Flapjack.CrepExp.var 11, Flapjack.CrepExp.const 40#64, Flapjack.CrepExp.var 2]

def crepBody373_11 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.var 13) (Flapjack.CrepExp.var 14)

def crepBody373_12 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 8#64])
  (Flapjack.CrepExp.var 15)

def crepBody373_13 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 16#64])
  (Flapjack.CrepExp.var 16)

def crepBody373_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.store (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.const 24#64])
  (Flapjack.CrepExp.var 17)

def crepBody373_15 : CrepProg (BitVec 64) :=
.seq crepBody373_14 crepBody373_7

def crepBody373_16 : CrepProg (BitVec 64) :=
.seq crepBody373_13 crepBody373_15

def crepBody373_17 : CrepProg (BitVec 64) :=
.seq crepBody373_12 crepBody373_16

def crepBody373_18 : CrepProg (BitVec 64) :=
.seq crepBody373_11 crepBody373_17

def crepBody373_19 : CrepProg (BitVec 64) :=
.dec 17 (Flapjack.CrepExp.var 6) crepBody373_18

def crepBody373_20 : CrepProg (BitVec 64) :=
.dec 16 (Flapjack.CrepExp.var 5) crepBody373_19

def crepBody373_21 : CrepProg (BitVec 64) :=
.dec 15 (Flapjack.CrepExp.var 4) crepBody373_20

def crepBody373_22 : CrepProg (BitVec 64) :=
.dec 14 (Flapjack.CrepExp.var 3) crepBody373_21

def crepBody373_23 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 12, Flapjack.CrepExp.const 8#64]) crepBody373_22

def crepBody373_24 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody373_25 : CrepProg (BitVec 64) :=
.seq crepBody373_23 crepBody373_24

def crepBody373_26 : CrepProg (BitVec 64) :=
.seq crepBody373_10 crepBody373_25

def crepBody373_27 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody373_26

def crepBody373_28 : CrepProg (BitVec 64) :=
.seq crepBody373_9 crepBody373_27

def crepBody373_29 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody373_28

def crepBody373_30 : CrepProg (BitVec 64) :=
.seq crepBody373_1 crepBody373_29

def crepBody373_31 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody373_30

def crepBody373_32 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody373_31

def crepBody373_33 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.load (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 0#64])) crepBody373_32

def crepBody373_34 : CrepProg (BitVec 64) :=
.seq crepBody373_0 crepBody373_33

def crepBody373_35 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.const 0#64) crepBody373_34

def data373 : CrepProg (BitVec 64) := crepBody373_35
def output373 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8], [0, 1, 2, 3, 4, 5, 6], crepProgToHOL data373)
end InitECandidate.Proofs.FrontendStages.Crep
