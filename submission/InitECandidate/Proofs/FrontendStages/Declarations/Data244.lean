import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify228
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body244_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "empty_trie_root"), none)) "alloc" [Flapjack.Exp.const 32#64]

def body244_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "empty_code_hash"), none)) "alloc" [Flapjack.Exp.const 32#64]

def body244_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "mpt_nib_scratch"), none)) "alloc" [Flapjack.Exp.const 64#64]

def body244_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "mpt_hash_scratch"), none)) "alloc" [Flapjack.Exp.const 40#64]

def body244_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.global, "mpt_key_scratch"), none)) "alloc" [Flapjack.Exp.const 16#64]

def body244_5 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch") (Flapjack.Exp.const 128#64)

def body244_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 1#64,
    Flapjack.Exp.var Flapjack.VarKind.global "empty_trie_root"]

def body244_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.global "mpt_hash_scratch", Flapjack.Exp.const 0#64,
    Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash"]

def body244_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body244_9 : Prog (BitVec 64) :=
.seq body244_7 body244_8

def body244_10 : Prog (BitVec 64) :=
.seq body244_6 body244_9

def body244_11 : Prog (BitVec 64) :=
.seq body244_5 body244_10

def body244_12 : Prog (BitVec 64) :=
.seq body244_4 body244_11

def body244_13 : Prog (BitVec 64) :=
.seq body244_3 body244_12

def body244_14 : Prog (BitVec 64) :=
.seq body244_2 body244_13

def body244_15 : Prog (BitVec 64) :=
.seq body244_1 body244_14

def body244_16 : Prog (BitVec 64) :=
.seq body244_0 body244_15

def body244_17 : Prog (BitVec 64) :=
.seq body244_0 body244_1

def body244_18 : Prog (BitVec 64) :=
.seq body244_17 body244_2

def body244_19 : Prog (BitVec 64) :=
.seq body244_18 body244_3

def body244_20 : Prog (BitVec 64) :=
.seq body244_19 body244_4

def body244_21 : Prog (BitVec 64) :=
.seq body244_20 body244_5

def body244_22 : Prog (BitVec 64) :=
.seq body244_21 body244_6

def body244_23 : Prog (BitVec 64) :=
.seq body244_22 body244_7

def body244_24 : Prog (BitVec 64) :=
.seq body244_23 body244_8

def originalData244 : Decl (BitVec 64) :=
.function { name := "mpt_init", inline := false, exported := false, params := [], body := body244_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData244 : Decl (BitVec 64) :=
.function { name := "mpt_init", inline := false, exported := false, params := [], body := body244_24, returnShape := (Flapjack.Shape.one) }
def original244 := Pancake.PanLang.declToHOL originalData244
def simplified244 := Pancake.PanLang.declToHOL simplifiedData244
end InitECandidate.Proofs.FrontendStages.Declarations
