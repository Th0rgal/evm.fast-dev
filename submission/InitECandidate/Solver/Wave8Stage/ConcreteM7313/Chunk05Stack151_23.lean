import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Word151ClashLeaves00
import InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151Support

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151.Shard23
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.Wave8Stage
open BackendDecomposition Chunk05Stack151

def parts : List (WordLangProgHOL (BitVec 64)) := [Word151ClashTree.part0, Word151ClashTree.part1, Word151ClashTree.part2, Word151ClashTree.part3, Word151ClashTree.part4, Word151ClashTree.part5, Word151ClashTree.part6, Word151ClashTree.part7, Word151ClashTree.part8, Word151ClashTree.part9, Word151ClashTree.part10, Word151ClashTree.part11, Word151ClashTree.part12, Word151ClashTree.part13, Word151ClashTree.part14, Word151ClashTree.part15, Word151ClashTree.part16, Word151ClashTree.part17, Word151ClashTree.part18, Word151ClashTree.part19, Word151ClashTree.part20, Word151ClashTree.part21, Word151ClashTree.part22, Word151ClashTree.part23, Word151ClashTree.part24, Word151ClashTree.part25, Word151ClashTree.part26, Word151ClashTree.part27, Word151ClashTree.part28, Word151ClashTree.part29, Word151ClashTree.part30, Word151ClashTree.part31, Word151ClashTree.part32, Word151ClashTree.part33, Word151ClashTree.part34, Word151ClashTree.part35, Word151ClashTree.part36, Word151ClashTree.part37, Word151ClashTree.part38, Word151ClashTree.part39, Word151ClashTree.part40, Word151ClashTree.part41, Word151ClashTree.part42, Word151ClashTree.part43, Word151ClashTree.part44, Word151ClashTree.part45, Word151ClashTree.part46, Word151ClashTree.part47, Word151ClashTree.part48, Word151ClashTree.part49, Word151ClashTree.part50, Word151ClashTree.part51, Word151ClashTree.part52, Word151ClashTree.part53, Word151ClashTree.part54, Word151ClashTree.part55, Word151ClashTree.part56]

wave8_kernel_reduce progs := parts.map (transform oracle151)
wave8_kernel_reduce maxV := maxListProg progs
wave8_kernel_reduce comp := compList riscvConfig false (22, 15, 14) progs (.nil, 127)

end InitECandidate.Solver.Wave8Stage.ConcreteM7313.Chunk05Stack151.Shard23
