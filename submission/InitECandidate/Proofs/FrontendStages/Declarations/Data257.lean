import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify241
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body257_0 : Prog (BitVec 64) :=
Flapjack.Prog.call
  (some
    (some (Flapjack.VarKind.local, "it"),
      some ("RlpErr", "e", Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 3#64])))
  "rlp_item" [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "n"]

def body257_1 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body257_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body257_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 0#64)) body257_1 body257_2

def body257_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 10#64]

def body257_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 32#64)) body257_4 body257_2

def body257_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.var Flapjack.VarKind.local "hn", Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64])

def body257_7 : Prog (BitVec 64) :=
.decCall ("hn") (Flapjack.Shape.one) ("node_new_hashed") ([Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) body257_6

def body257_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"))
  (Flapjack.Exp.const 0#64)) body257_7 body257_2

def body257_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it")])

def body257_10 : Prog (BitVec 64) :=
.seq body257_8 body257_9

def body257_11 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("nodedb_lookup") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "it")]) body257_10

def body257_12 : Prog (BitVec 64) :=
.seq body257_5 body257_11

def body257_13 : Prog (BitVec 64) :=
.seq body257_3 body257_12

def body257_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 0#64)) body257_13 body257_2

def body257_15 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "n",
      Flapjack.Exp.const 0#64])

def body257_16 : Prog (BitVec 64) :=
.seq body257_14 body257_15

def body257_17 : Prog (BitVec 64) :=
.seq body257_0 body257_16

def body257_18 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body257_17

def body257_19 : Prog (BitVec 64) :=
.dec ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body257_18

def body257_20 : Prog (BitVec 64) :=
.seq body257_3 body257_5

def body257_21 : Prog (BitVec 64) :=
.seq body257_20 body257_11

def body257_22 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "it"))
  (Flapjack.Exp.const 0#64)) body257_21 body257_2

def body257_23 : Prog (BitVec 64) :=
.seq body257_0 body257_22

def body257_24 : Prog (BitVec 64) :=
.seq body257_23 body257_15

def body257_25 : Prog (BitVec 64) :=
.dec ("e") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body257_24

def body257_26 : Prog (BitVec 64) :=
.dec ("it") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body257_25

def originalData257 : Decl (BitVec 64) :=
.function { name := "_resolve_step", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body257_19, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData257 : Decl (BitVec 64) :=
.function { name := "_resolve_step", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body257_26, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original257 := Pancake.PanLang.declToHOL originalData257
def simplified257 := Pancake.PanLang.declToHOL simplifiedData257
end InitECandidate.Proofs.FrontendStages.Declarations
