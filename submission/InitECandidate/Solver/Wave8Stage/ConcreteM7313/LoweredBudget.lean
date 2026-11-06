import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stubs

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
open InitE Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open StackPasses StackToLabClock BackendDecomposition

/-- Lower an entry with its actual function identifier and global frame information. -/
def lowerEntry (info : Spt Nat) (entry : Nat × HolProg 64) : Nat × HolProg 64 :=
  StackRemove.progComp (oracleCompilerConfig []).stackConf.jump
    riscvConfig.addrOffset pointer
    (StackAlloc.progComp (entry.1, StackRawCall.compTop info entry.2))

def Bounded (info : Spt Nat) (table : List (Nat × HolProg 64)) : Prop :=
  ∀ entry ∈ table, stepCost (lowerEntry info entry).2 ≤ 7313

theorem bounded_nil (info : Spt Nat) : Bounded info [] := by
  intro entry h
  cases h

theorem bounded_cons (info : Spt Nat) (entry : Nat × HolProg 64)
    (table : List (Nat × HolProg 64))
    (head : stepCost (lowerEntry info entry).2 ≤ 7313)
    (tail : Bounded info table) : Bounded info (entry :: table) := by
  intro candidate h
  rcases List.mem_cons.mp h with h | h
  · subst candidate
    exact head
  · exact tail candidate h

theorem bounded_append (info : Spt Nat) (left right : List (Nat × HolProg 64))
    (hl : Bounded info left) (hr : Bounded info right) :
    Bounded info (left ++ right) := by
  intro entry h
  rcases List.mem_append.mp h with h | h
  · exact hl entry h
  · exact hr entry h

theorem budget (oracles : List (Option (Spt Nat)))
    (table : List (Nat × HolProg 64)) (info : Spt Nat)
    (collected : StackRawCall.collectInfo table .ln = info)
    (bounded : Bounded info table) :
    Stage4.codeStepBudget (stackPasses oracles table) ≤ 7313 := by
  apply budget_of_bodies oracles table 7313 (stubs_bounded oracles)
  intro entry hentry
  change stepCost (lowerEntry (StackRawCall.collectInfo table .ln) entry).2 ≤ 7313
  rw [collected]
  exact bounded entry hentry

/-- Assemble the native compilation and the globally collected frame budget
into the backend obligation for a concrete witness. -/
theorem backendBound
    (w : InitECandidate.Solver.Wave8GuestInv.LeanBridge.ConcreteOracleCompilationWitness)
    (hlen : w.oracles.length = ConcreteCompilerWord.source.length)
    (bodies : List (Nat × HolProg 64)) (frames : List Nat)
    (bitmaps : AppList (BitVec 64) × Nat) (info : Spt Nat)
    (compiled : WordToStack.Native.compileWordToStackNative riscvConfig false registers
      ((ConcreteCompilerWord.source.zip w.oracles).map (fun p => wordFunction p.2 p.1))
      (.list [4], 1) = (bodies, frames, bitmaps))
    (collected : StackRawCall.collectInfo (nativeStubs ++ bodies) .ln = info)
    (bounded : Bounded info (nativeStubs ++ bodies)) :
    ConcreteStageTransferBridge.BackendBound w := by
  apply backendBound_of_table w hlen bodies frames bitmaps compiled
  exact budget w.oracles (nativeStubs ++ bodies) info collected bounded

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.LoweredBudget
