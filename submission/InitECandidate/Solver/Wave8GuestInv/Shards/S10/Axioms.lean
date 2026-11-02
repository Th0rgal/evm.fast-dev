import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Stop
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Leaves1
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.CheckGas
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.RetdataSize
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Slotnum
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Prevrandao
import InitECandidate.Solver.Wave8GuestInv.Shards.S10.Shl

/-! Axiom audit for verified s10 leaves. -/

namespace InitECandidate.Solver.Wave8Leaves.S10

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded

example : type_of% fb_op_stop = (
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop») := rfl


example : type_of% fb_op_sub = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_sub") K.«u256_sub») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub») := rfl


example : type_of% fb_check_gas =
    TerminatingFunBoundedOn GuestInv (ofString "check_gas") K.«check_gas» := rfl


example : type_of% fb_op_returndatasize = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize») := rfl


example : type_of% fb_op_slotnum = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push_word") K.«stack_push_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum») := rfl


example : type_of% fb_op_prevrandao = (
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "block_env") K.«block_env») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_from_be") K.«u256_from_be») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao») := rfl


example : type_of% fb_op_shl = (
    (TerminatingFunBoundedOn GuestInv (ofString "stack_pop") K.«stack_pop») →
    (TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas») →
    (TerminatingFunBoundedOn GuestInv (ofString "sat_word") K.«sat_word») →
    (TerminatingFunBoundedOn GuestInv (ofString "u256_shl") K.«u256_shl») →
    (TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push») →
    (TerminatingFunBoundedOn GuestInv (ofString "pc_add") K.«pc_add») →
      TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl») := rfl


end InitECandidate.Solver.Wave8Leaves.S10
