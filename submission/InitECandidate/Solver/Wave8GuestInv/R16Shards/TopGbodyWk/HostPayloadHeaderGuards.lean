import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.FrameBase

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open InitECandidate.Solver.Wave8GuestInv

def HtrNewPayloadReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    InputAt s (locN s "si") ∧
    IvlsDisj (inputCells s (locN s "si")) [(locN s "out", 32)] ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

def ValidateHeaderReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    WorldOK s ∧
    HeaderOK s ∧
    HeaderHashRecover.HeaderAtStrong s (locN s "parent") ∧
    (∀ iv ∈ R14Shards.OpHandlersA.untypedGlobalBufIvls s, Disj (locN s "parent", 248) iv)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
