import InitECandidate.Proofs.FrontendStages.Crep.Translate754
import InitECandidate.Proofs.FrontendStages.Crep.Context
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open Flapjack Flapjack.Pancake.PanLang
namespace InitECandidate.Proofs.FrontendStages.Crep
def crepBody770_0 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([3], none)) "heap_mark" []

def crepBody770_1 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([4], none)) "alloc" [Flapjack.CrepExp.const 32#64]

def crepBody770_2 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([5], none)) "keccak256"
  [Flapjack.CrepExp.var 1, Flapjack.CrepExp.var 2, Flapjack.CrepExp.var 4]

def crepBody770_3 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody770_2

def crepBody770_4 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.storeByte (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8])
  (Flapjack.CrepExp.op Flapjack.BinOp.or
    [Flapjack.CrepExp.loadByte
        (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 0, Flapjack.CrepExp.var 8]),
      Flapjack.CrepExp.var 9])

def crepBody770_5 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.assign 5 (Flapjack.CrepExp.var 10)

def crepBody770_6 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.skip

def crepBody770_7 : CrepProg (BitVec 64) :=
.seq crepBody770_5 crepBody770_6

def crepBody770_8 : CrepProg (BitVec 64) :=
.dec 10 (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 2#64]) crepBody770_7

def crepBody770_9 : CrepProg (BitVec 64) :=
.seq crepBody770_4 crepBody770_8

def crepBody770_10 : CrepProg (BitVec 64) :=
.dec 9 (Flapjack.CrepExp.shift Flapjack.Shift.lsl (Flapjack.CrepExp.const 1#64)
  (Flapjack.CrepExp.op Flapjack.BinOp.sub
    [Flapjack.CrepExp.const 7#64,
      Flapjack.CrepExp.op Flapjack.BinOp.and [Flapjack.CrepExp.var 7, Flapjack.CrepExp.const 7#64]])) crepBody770_9

def crepBody770_11 : CrepProg (BitVec 64) :=
.dec 8 (Flapjack.CrepExp.shift Flapjack.Shift.lsr (Flapjack.CrepExp.var 7) (Flapjack.CrepExp.const 3#64)) crepBody770_10

def crepBody770_12 : CrepProg (BitVec 64) :=
.dec 7 (Flapjack.CrepExp.op Flapjack.BinOp.sub [Flapjack.CrepExp.const 2047#64, Flapjack.CrepExp.var 6]) crepBody770_11

def crepBody770_13 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.op Flapjack.BinOp.and
  [Flapjack.CrepExp.op Flapjack.BinOp.or
      [Flapjack.CrepExp.shift Flapjack.Shift.lsl
          (Flapjack.CrepExp.loadByte
            (Flapjack.CrepExp.op Flapjack.BinOp.add [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5]))
          (Flapjack.CrepExp.const 8#64),
        Flapjack.CrepExp.loadByte
          (Flapjack.CrepExp.op Flapjack.BinOp.add
            [Flapjack.CrepExp.var 4, Flapjack.CrepExp.var 5, Flapjack.CrepExp.const 1#64])],
    Flapjack.CrepExp.const 2047#64]) crepBody770_12

def crepBody770_14 : CrepProg (BitVec 64) :=
.while (Flapjack.CrepExp.cmp Flapjack.Cmp.less (Flapjack.CrepExp.var 5) (Flapjack.CrepExp.const 6#64)) crepBody770_13

def crepBody770_15 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.call (some ([6], none)) "heap_release" [Flapjack.CrepExp.var 3]

def crepBody770_16 : CrepProg (BitVec 64) :=
.dec 6 (Flapjack.CrepExp.const 0#64) crepBody770_15

def crepBody770_17 : CrepProg (BitVec 64) :=
.seq crepBody770_14 crepBody770_16

def crepBody770_18 : CrepProg (BitVec 64) :=
Flapjack.CrepProg.return [Flapjack.CrepExp.const 0#64]

def crepBody770_19 : CrepProg (BitVec 64) :=
.seq crepBody770_17 crepBody770_18

def crepBody770_20 : CrepProg (BitVec 64) :=
.dec 5 (Flapjack.CrepExp.const 0#64) crepBody770_19

def crepBody770_21 : CrepProg (BitVec 64) :=
.seq crepBody770_3 crepBody770_20

def crepBody770_22 : CrepProg (BitVec 64) :=
.seq crepBody770_1 crepBody770_21

def crepBody770_23 : CrepProg (BitVec 64) :=
.dec 4 (Flapjack.CrepExp.const 0#64) crepBody770_22

def crepBody770_24 : CrepProg (BitVec 64) :=
.seq crepBody770_0 crepBody770_23

def crepBody770_25 : CrepProg (BitVec 64) :=
.dec 3 (Flapjack.CrepExp.const 0#64) crepBody770_24

def data770 : CrepProg (BitVec 64) := crepBody770_25
def output770 : MlS × List Nat × CrepProgHOL 64 :=
  (Flapjack.Basis.Pure.MlString.MlString.implode
  [97#8, 100#8, 100#8, 95#8, 116#8, 111#8, 95#8, 98#8, 108#8, 111#8, 111#8, 109#8], [0, 1, 2], crepProgToHOL data770)
end InitECandidate.Proofs.FrontendStages.Crep
