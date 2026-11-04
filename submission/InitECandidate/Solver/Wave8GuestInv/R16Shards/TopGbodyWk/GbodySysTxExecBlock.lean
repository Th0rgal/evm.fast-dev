import InitECandidate.Solver.Wave8GuestInv.ContractParts.C18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R13PayloadStateInit

/-! ## 1. `gbody_process_unchecked_system_transaction_strong` -/

/-- Entry parameters of `process_unchecked_system_transaction` (`target`, `data`, `data_n`, all `.one`)
hold 1-word values. Guaranteed automatically by `lookupCodeHOLFinite` at every call site. -/
def WordSysTxLocals {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ w : BitVec 64, s.locals.lookup (ofString "target") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "data") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "data_n") = some (.val (.word w)))

/-- Strengthened entry guard for `process_unchecked_system_transaction`: `WorldOK` together with
1-word parameter locals (`vm_system_address` and `be` are already 1-word globals via `WorldOK → ArenaReady → GlobalsWord`). -/
def SysTxReadyStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => WorldOK s ∧ WordSysTxLocals s

theorem sysTxReadyStrong_worldOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxReadyStrong s) : WorldOK s := h.1

theorem sysTxReadyStrong_sysTxEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxReadyStrong s) : SysTxEntry s := by
  obtain ⟨hW, ht, hd, hdn⟩ := h
  have hgw := hW.1.2.2.2.2.2.2.2.2.2
  exact ⟨hW, ht, hd, hdn, hgw "vm_system_address" (by decide), hgw "be" (by decide)⟩

theorem localsOnly_sysTxReadyStrong : LocalsOnly ["target", "data", "data_n"] SysTxReadyStrong := by
  intro F s locals k hl ⟨hW, ht, hd, hdn⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := ht; exact ⟨w, (hl "target" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hd; exact ⟨w, (hl "data" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hdn; exact ⟨w, (hl "data_n" (by simp)).trans hw⟩

private theorem shapeEqHOL_one_iff_word {v : ValueHOL 64} :
    shapeEqHOL .one (shapeOfHOLExact v) = true ↔ ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · simp [shapeOfHOLExact, shapeEqHOL]
  · simp [shapeOfHOLExact, shapeEqHOL]
  · simp [shapeOfHOLExact, shapeEqHOL]

/-- Any call to `process_unchecked_system_transaction` from a `WorldOK`-implying caller predicate `P`
automatically satisfies `SysTxReadyStrong` at callee entry because `lookupCodeHOLFinite` checks that
all three `.one` parameters receive 1-word values. -/
theorem callEntryOn_sysTxReadyStrong
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hPW : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → WorldOK s)
    (arguments : List (ExpHOL 64)) :
    CallEntryOn P SysTxReadyStrong (ofString "process_unchecked_system_transaction") arguments := by
  intro F state values body' callee ret' hcode hP _hargs hlook
  refine ⟨localsFree_worldOK state callee (state.clock - 1) (hPW state hP), ?_⟩
  have hfn : state.code.lookup (ofString "process_unchecked_system_transaction") =
      some ([(ofString "target", .one), (ofString "data", .one), (ofString "data_n", .one)],
        sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction, .one) := by
    rw [hcode]; exact GuestTrapAndLookup.lookup_process_unchecked_system_transaction
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hfn] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, hlen, hsh⟩ := hcond
      rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
      · simp at hlen
      · simp at hlen
      · simp at hlen
      · simp only [List.zip, List.zipWith_cons_cons, List.zipWith_nil_left,
          List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hsh
        obtain ⟨hsh1, hsh2, hsh3⟩ := hsh
        obtain ⟨w1, rfl⟩ := shapeEqHOL_one_iff_word.1 hsh1
        obtain ⟨w2, rfl⟩ := shapeEqHOL_one_iff_word.1 hsh2
        obtain ⟨w3, rfl⟩ := shapeEqHOL_one_iff_word.1 hsh3
        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
          not_or, List.not_mem_nil, or_false] at hnd
        refine ⟨⟨w1, ?_⟩, ⟨w2, ?_⟩, ⟨w3, ?_⟩⟩
        · simp [callEntryStateHOLFinite, List.zip, List.foldl, hnd.1.1, hnd.1.2]
        · simp [callEntryStateHOLFinite, List.zip, List.foldl, hnd.2.1]
        · simp [callEntryStateHOLFinite, List.zip, List.foldl]
      · simp at hlen
    · cases raw

def GBody.«process_unchecked_system_transaction_strong» : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc») →
  (TerminatingFunBoundedOn GuestInv (ofString "ext_code_of") K.«ext_code_of») →
  (TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new») →
  (TerminatingFunBoundedOn WorldOK (ofString "incorporate_tx_into_block") K.«incorporate_tx_into_block») →
  (TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») →
  (TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new») →
  (TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release») →
  (TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx») →
  (TerminatingFunBoundedOn GuestInv (ofString "te_new") K.«te_new») →
  (WorldKeeps WorldOK (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "ext_code_of")) →
  (type_of% @htab_new_spec) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 176)])) (ofString "msg_new")) →
  (Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0)
    (ofString "msg_new")) →
  (WorldKeepsIn MsgReady (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)]) (fun s => [(locN s "msg", 176), (globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128), (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352), (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384), (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64), (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96), (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40), (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128), (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128), (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128), (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64), (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52), (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
    ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    RetMessageOutput (ofString "process_message_call")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr", "journal_n", "ts"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "state_fresh_tx")) →
  (WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (RetAvoids (fun _ _ w => [(w, 200)])) (ofString "te_new")) →
  (Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0)
    (ofString "te_new")) →
  TerminatingFunBoundedOn SysTxReadyStrong
    (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction»

theorem gbody_process_unchecked_system_transaction_strong :
    GBody.«process_unchecked_system_transaction_strong» := by
  intro hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte wext hnspec wmn rtmn wpmc wsf wte rtte
  refine ⟨_, _, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_unchecked_system_transaction, ?_⟩
  intro F state hcode hP
  exact bounded_process_unchecked_system_transaction_wordArgs
    hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte
    wext hnspec wmn rtmn wpmc wsf wte rtte
    state hcode (sysTxReadyStrong_sysTxEntry hP)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
