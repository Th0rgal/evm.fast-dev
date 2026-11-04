import InitECandidate.Solver.Wave8GuestInv.ContractParts.C08
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21

theorem lookup_block_rlp_length :
    originalRuntimeCode.lookup (ofString "block_rlp_length") =
      some ([(ofString "hdr", .one), (ofString "pl", .one)],
        sourceFnBody Guest.Software.guestFn_block_rlp_length, .one) :=
  lookup_of_guestAst_getElem 862 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_block_rlp_length) rfl

theorem «wk_block_rlp_length» :
    WorldKeeps (fun s => WorldOK s ∧ HeaderOK s) (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "block_rlp_length") := by
  refine ⟨[(ofString "hdr", .one), (ofString "pl", .one)],
    sourceFnBody Guest.Software.guestFn_block_rlp_length, .one,
    lookup_block_rlp_length, ?_⟩
  intro F s _ ⟨hW, hHdr⟩ ⟨values, hlc⟩ _ _
  exfalso
  obtain ⟨⟨hG, _⟩, _⟩ := hW
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup
    (ofString "block_rlp_length") values
    (sourceFnBody Guest.Software.guestFn_block_rlp_length) s.locals .one hlc
  simp only [lookupCodeHOLExact, lookup_block_rlp_length] at hx
  rcases values with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    have hloc_h : locN s "h" = 0 := by
      unfold locN
      have hl := congrFun hL.symm (ofString "h")
      rw [hl]
      have hne1 : ofString "h" ≠ ofString "pl" := by decide
      have hne2 : ofString "h" ≠ ofString "hdr" := by decide
      simp [hne1, hne2]
    unfold HeaderOK HeaderAt WordsOK at hHdr
    rw [hloc_h] at hHdr
    obtain ⟨_, hma0, _⟩ := hHdr.1.2.2 0 (by decide)
    rw [hG.memaddrs, ordinaryDomain_iff] at hma0
    have hsb : sourceBase = 2701131776 := rfl
    have hz : (BitVec.ofNat 64 (0 + 8 * 0)).toNat = 0 := rfl
    rw [hz, hsb] at hma0
    omega
  · simp at hx

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
