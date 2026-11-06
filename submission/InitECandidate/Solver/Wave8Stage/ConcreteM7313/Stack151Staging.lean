import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Stack151Frame
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Function150
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.StackCompileComposition

open Lean Elab Command

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313

private def stageCommand (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

elab "wave8_stack151_parts " start:num count:num : command => do
  for i in List.range count.getNat do
    let n := start.getNat + i
    let state := if n = 0 then "Function150.stackResult.2.2" else s!"result{n-1}.2"
    stageCommand s!"wave8_certified_reduce program{n} := WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (oracle151.getD .ln)) Word151ClashTree.part{n})"
    stageCommand s!"wave8_certified_reduce result{n} := WordToStack.Native.compNative riscvConfig false program{n} {state} (registers, frame, stackVariables)"

end InitECandidate.Solver.Wave8Stage.ConcreteM7313
