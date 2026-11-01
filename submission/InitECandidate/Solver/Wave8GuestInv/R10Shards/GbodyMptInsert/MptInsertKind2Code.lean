import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptCuts

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def lv (n : String) : ExpHOL 64 := .var .local (ofString n)
def constant (n : Nat) : ExpHOL 64 := .const (BitVec.ofNat 64 n)
def assign (n : String) (e : ExpHOL 64) : ProgHOL 64 := .assign .local (ofString n) e
def load (n : String) (off : Nat) : ExpHOL 64 := .load .one (.op .add [lv n, constant off])
def yes : ProgHOL 64 → ProgHOL 64 | .ite _ a _ => a | _ => .skip
def no : ProgHOL 64 → ProgHOL 64 | .ite _ _ b => b | _ => .skip
def continuation : ProgHOL 64 → ProgHOL 64 | .decCall _ _ _ _ b => b | _ => .skip

def core := mptDecBody (mptDecBody (mptDecBody (mptDecBody mptInsertBody)))
def selection := mptLeft (mptRight core)
def nonnull := no selection
def kinds := mptRight (mptRight (mptDecBody nonnull))
def extension := yes (no kinds)
def extDecision := continuation (mptDecBody (mptDecBody extension))
def descend := yes extDecision
def splitExt := no extDecision
def tail := mptRight (mptRight core)

theorem body_eq : mptInsertBody =
    .dec (ofString "r") .one (constant 0)
      (.dec (ofString "next_node") .one (constant 0)
        (.dec (ofString "next_slot") .one (constant 0)
          (.dec (ofString "next_level") .one (constant 0) core))) := rfl

theorem core_eq : core = .seq (assign "go" (constant 0)) (.seq selection tail) := rfl

theorem selection_eq : selection = .ite (.cmp .equal (lv "node") (constant 0))
    (yes selection) nonnull := rfl

theorem nonnull_eq : nonnull = .dec (ofString "k") .one (load "node" 0)
    (.seq (.ite (.cmp .equal (lv "k") (constant 0))
      (.call (some (none, none)) (ofString "mpt_fail") [constant 2]) .skip)
      (.seq (.call (some (none, none)) (ofString "node_invalidate") [lv "node"]) kinds)) := rfl

theorem kinds_eq : kinds = .ite (.cmp .equal (lv "k") (constant 1)) (yes kinds)
    (.ite (.cmp .equal (lv "k") (constant 2)) extension (no (no kinds))) := rfl

theorem extension_eq : extension =
    .dec (ofString "seg") .one (load "node" 32)
      (.dec (ofString "sl") .one (load "node" 40)
        (.decCall (ofString "pl") .one (ofString "common_prefix_length")
          [lv "seg", lv "sl", .op .add [lv "key", lv "level"],
            .op .sub [lv "klen", lv "level"]] extDecision)) := rfl

theorem extDecision_eq : extDecision =
    .ite (.cmp .equal (lv "pl") (lv "sl")) descend splitExt := rfl

theorem descend_eq : descend =
    .seq (assign "r" (lv "node"))
      (.seq (assign "next_node" (load "node" 48))
        (.seq (assign "next_slot" (.op .add [lv "node", constant 48]))
          (.seq (assign "next_level" (.op .add [lv "level", lv "pl"]))
            (assign "go" (constant 1))))) := rfl

theorem splitExt_eq : splitExt =
    .decCall (ofString "br") .one (ofString "_split_extension")
      [lv "node", .op .add [lv "key", lv "level"],
        .op .sub [lv "klen", lv "level"], lv "vptr", lv "vlen", lv "pl"]
      (.ite (.cmp .lower (constant 0) (lv "pl"))
        (.call (some (some (.local, ofString "r"), none)) (ofString "node_new_ext")
          [lv "seg", lv "pl", lv "br"])
        (assign "r" (lv "br"))) := rfl

theorem tail_eq : tail =
    .seq (.ite (.cmp .equal (lv "slot") (constant 0))
      (assign "result" (lv "r")) (.store (lv "slot") (lv "r")))
      (.seq (assign "node" (lv "next_node"))
        (.seq (assign "slot" (lv "next_slot")) (assign "level" (lv "next_level")))) := rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
