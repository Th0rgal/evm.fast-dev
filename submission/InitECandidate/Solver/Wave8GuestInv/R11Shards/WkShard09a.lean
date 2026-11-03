import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Core

/-! Proof of `wk_block_rlp_length` (`R12-Wk09`, shard a). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard09a

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv

private theorem lookup_block_rlp_length :
    originalRuntimeCode.lookup (ofString "block_rlp_length") =
      some ([(ofString "hdr", .one), (ofString "pl", .one)],
        sourceFnBody Guest.Software.guestFn_block_rlp_length, .one) :=
  lookup_of_guestAst_getElem 862 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_block_rlp_length) rfl

private theorem locN_h_eq_zero_of_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    {body : ProgHOL 64}
    (hex : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "block_rlp_length") values = some (body, s.locals, .one)) :
    locN s "h" = 0 := by
  obtain ⟨values, hl⟩ := hex
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · cases hl
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hl
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc_eq, _⟩
    unfold lookupCodeHOLExact at raw
    rw [lookup_block_rlp_length] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, _⟩
      have hlen : values.length = 2 := hcond.2.1.symm
      rcases values with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩ <;> simp at hlen
      have hlookup : s.locals.lookup (ofString "h") = none := by
        rw [← hloc_eq]
        change exactLocals (ofString "h") = none
        rw [← hloc]
        simp [show ofString "h" ≠ ofString "pl" by decide,
          show ofString "h" ≠ ofString "hdr" by decide]
      simp [locN, hlookup]
    · cases raw

theorem «wk_block_rlp_length» :
    WorldKeeps ((fun s => WorldOK s ∧ HeaderOK s)) (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
     ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "block_rlp_length") := by
  refine ⟨_, _, _, lookup_block_rlp_length, fun {F} s _ ⟨hWOK, hHdr⟩ hex _ _ => ?_⟩
  exfalso
  have hh0 : locN s "h" = 0 := locN_h_eq_zero_of_lookup s hex
  have hlt0 : 0 < (locN s "h", 248).2 / 8 := by dsimp only; omega
  have hw0 : WordAt s 0 := by
    have hk := hHdr.1.2.2 0 hlt0
    simpa [hh0] using hk
  obtain ⟨_, hdom0, _⟩ := hw0
  rw [hWOK.1.1.memaddrs] at hdom0
  have hord := (M13.ordinaryDomain_iff (BitVec.ofNat 64 0)).1 hdom0
  have hbv0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
  omega

example (P : Primitives) : (type_of% @«wk_block_rlp_length») =
    (type_of% P.«wk_block_rlp_length») := rfl

end InitECandidate.Solver.Wave8GuestInv.R11Shards.WkShard09a
