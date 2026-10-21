import InitECandidate.Proofs.FrontendStages.Crep.Translate536
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody552_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([8], none)) "u256_is_zero"
  [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 3]

def crepBody552_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 9 (Flapjack.CrepExp.const 2300#64)

def crepBody552_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody552_3 : CrepProg (BitVec 64) :=
.seq crepBody552_1 crepBody552_2

def crepBody552_4 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.equal (Flapjack.CrepExp.var 8) (Flapjack.CrepExp.const 0#64)) crepBody552_3 crepBody552_2

def crepBody552_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([10], none)) "add_sat" [Flapjack.CrepExp.var 7, Flapjack.CrepExp.var 6]

def crepBody552_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([11], none)) "add_sat" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 7]

def crepBody552_7 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([12], none)) "add_sat" [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 9]

def crepBody552_8 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.var 11, Flapjack.CrepExp.var 12]

def crepBody552_9 : CrepProg (BitVec 64) :=
.seq crepBody552_7 crepBody552_8

def crepBody552_10 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.const 0#64) crepBody552_9

def crepBody552_11 : CrepProg (BitVec 64) :=
.seq crepBody552_6 crepBody552_10

def crepBody552_12 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.const 0#64) crepBody552_11

def crepBody552_13 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.var 10)) crepBody552_12 crepBody552_2

def crepBody552_14 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 13 (Flapjack.CrepExp.var 12)

def crepBody552_15 : CrepProg (BitVec 64) :=
.seq crepBody552_14 crepBody552_2

def crepBody552_16 : CrepProg (BitVec 64) :=
.ite (Flapjack.CrepExp.cmp Flapjack.Cmp.lower (Flapjack.CrepExp.var 12) (Flapjack.CrepExp.var 13)) crepBody552_15 crepBody552_2

def crepBody552_17 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return
  [Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 7],
    Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 13, Flapjack.CrepExp.var 9]]

def crepBody552_18 : CrepProg (BitVec 64) :=
.seq crepBody552_16 crepBody552_17

def crepBody552_19 : CrepProg (BitVec 64) :=
.dec 13 (Flapjack.CrepExp.var 4) crepBody552_18

def crepBody552_20 : CrepProg (BitVec 64) :=
.dec 12 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.var 11,
    Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 11) (Flapjack.CrepExp.const 6#64)]) crepBody552_19

def crepBody552_21 : CrepProg (BitVec 64) :=
.dec 11 (Flapjack.CrepExp.op Flapjack.BinOp.sub
  [Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.var 5, Flapjack.CrepExp.var 6], Flapjack.CrepExp.var 7]) crepBody552_20

def crepBody552_22 : CrepProg (BitVec 64) :=
.seq crepBody552_13 crepBody552_21

def crepBody552_23 : CrepProg (BitVec 64) :=
.seq crepBody552_5 crepBody552_22

def crepBody552_24 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.const 0#64) crepBody552_23

def crepBody552_25 : CrepProg (BitVec 64) :=
.seq crepBody552_4 crepBody552_24

def crepBody552_26 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.const 0#64) crepBody552_25

def crepBody552_27 : CrepProg (BitVec 64) :=
.seq crepBody552_0 crepBody552_26

def crepBody552_28 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.const 0#64) crepBody552_27

def data552 : CrepProg (BitVec 64) := crepBody552_28
def output552 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8,
    95#8, 99#8, 97#8, 108#8, 108#8, 95#8, 103#8, 97#8, 115#8], [0, 1, 2, 3, 4, 5, 6, 7], crepProgToHOL data552)
end InitECandidate.Proofs.FrontendStages.Crep
