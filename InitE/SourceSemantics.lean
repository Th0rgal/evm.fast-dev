import InitE.Parameters
import Guest.Model
import Flapjack.FfiBridge
import Flapjack.Misc.Alignment
import Flapjack.Pancake.Semantics.PanSem.Semantics
import Flapjack.Compiler.Backend.StackRemove

/-! The challenge fixes `Guest.Software.guestAst` and uses the exact evaluator in
the general compiler theorem reused by
`InitE.panToTargetCompileSemanticsOraclesRiscVSource`.
`Guest.Model` supplies byte-level host specifications, not its
stepped program evaluator. -/
namespace InitE
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString

/-- The common byte oracle, with terminal runtime calls. Their final event
retains the name and configuration, so traps can be classified separately. -/
def sourceOracle : HolOracle Guest.HostMemory := fun name host configuration bytes =>
  match name with
  | .extCall name =>
      if name = ofString "halt" ∨ name = ofString "trap" then .final .failed
      else
        match Guest.guestOracle (.extCall (toStringOfBytes name)) host
            (configuration.map bitsToByte) (bytes.map bitsToByte) with
        | .returned next result => .ret next (result.map byteToBits)
        | .final .failed => .final .failed
        | .final .diverged => .final .diverged
  | .sharedMem op =>
      let op := match op with
        | .mappedRead => FfiShmemOp.mappedRead
        | .mappedWrite => FfiShmemOp.mappedWrite
      match Guest.guestOracle (.sharedMem op) host
          (configuration.map bitsToByte) (bytes.map bitsToByte) with
      | .returned next result => .ret next (result.map byteToBits)
      | .final .failed => .final .failed
      | .final .diverged => .final .diverged

def sourceFfi (input : Guest.InputBlob) : HolFfiState Guest.HostMemory :=
  initialHolFfiState sourceOracle (Guest.guestHostMemory input)

/-- Word-cell domain required by the compiler, excluding the globals tail. -/
def ordinaryDomain : BitVec 64 → Prop :=
  fun address =>
    (scratchStart ≤ address.toNat ∧ address.toNat < scratchEnd) ∨
    StackRemove.addresses (BitVec.ofNat 64 sourceBase)
      ((stackStart - sourceBase) / 8 - globalsWords) address

def sharedDomain (address : BitVec 64) : Prop :=
  holByteAligned address = true ∧
    ((inputStart ≤ address.toNat ∧ address.toNat < inputEnd) ∨
      (outputStart ≤ address.toNat ∧ address.toNat < outputEnd))

/-- Ordinary scratch and heap cells start at zero. -/
def sourceMemory (_address : BitVec 64) : HolWordLab 64 := .word 0

def sourceInitialState (input : Guest.InputBlob) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  { locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    structs := []
    code := HolFiniteMapExact.empty
    eshapes := HolFiniteMapExact.empty
    memory := sourceMemory
    memaddrs := ordinaryDomain
    shMemaddrs := sharedDomain
    clock := 0
    be := false
    ffi := sourceFfi input
    baseAddr := BitVec.ofNat 64 sourceBase
    topAddr := BitVec.ofNat 64 heapEnd }

/-- Authoritative source behavior, on the fixed literal AST. -/
noncomputable def sourceBehaviour (input : Guest.InputBlob) : HolBehaviour :=
  PanSemStateFiniteExact.semanticsDecls (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL)

theorem source_empty_maps (input : Guest.InputBlob) :
    (sourceInitialState input).locals = HolFiniteMapExact.empty ∧
    (sourceInitialState input).globals = HolFiniteMapExact.empty ∧
    (sourceInitialState input).code = HolFiniteMapExact.empty ∧
    (sourceInitialState input).eshapes = HolFiniteMapExact.empty :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem source_memory_domain (input : Guest.InputBlob) :
    (sourceInitialState input).memaddrs = ordinaryDomain := rfl

theorem halt_is_terminal (host : Guest.HostMemory) (config bytes : List (BitVec 8)) :
    sourceOracle (.extCall (ofString "halt")) host config bytes = .final .failed := by
  simp [sourceOracle]

theorem trap_is_terminal (host : Guest.HostMemory) (config bytes : List (BitVec 8)) :
    sourceOracle (.extCall (ofString "trap")) host config bytes = .final .failed := by
  simp [sourceOracle]

end InitE
