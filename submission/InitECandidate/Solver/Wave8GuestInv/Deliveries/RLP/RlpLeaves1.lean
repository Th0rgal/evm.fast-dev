import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpCore

/-! RLP / byte-decoding family, part 3: nibble helpers, `pack_bytes`, RLP header helpers. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

/-- `key_to_nibbles` (AST line 9807): #0 WALK (`key + i`), #1 (`i < n`) strict counter. -/
theorem «fb_key_to_nibbles» :
    TerminatingFunBoundedOn GuestInv (ofString "key_to_nibbles") K.«key_to_nibbles» := by
  fb_prove 248 Guest.Software.guestFn_key_to_nibbles K.«key_to_nibbles»

/-- `compact_to_nibbles` (AST line 9849): loop-free. -/
theorem «fb_compact_to_nibbles» :
    TerminatingFunBoundedOn GuestInv (ofString "compact_to_nibbles") K.«compact_to_nibbles» := by
  fb_prove 249 Guest.Software.guestFn_compact_to_nibbles K.«compact_to_nibbles»

/-- `nibbles_concat` (AST line 9922): loop-free. -/
theorem «fb_nibbles_concat» :
    TerminatingFunBoundedOn GuestInv (ofString "nibbles_concat") K.«nibbles_concat» := by
  fb_prove 252 Guest.Software.guestFn_nibbles_concat K.«nibbles_concat»

/-- `pack_bytes` (AST line 8213): loop-free. -/
theorem «fb_pack_bytes» : TerminatingFunBoundedOn GuestInv (ofString "pack_bytes") K.«pack_bytes» := by
  fb_prove 192 Guest.Software.guestFn_pack_bytes K.«pack_bytes»

/-- `rlp_item_header` (AST line 4432): loop-free. -/
theorem «fb_rlp_item_header» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_header") K.«rlp_item_header» := by
  fb_prove 109 Guest.Software.guestFn_rlp_item_header K.«rlp_item_header»

/-- `rlp_item_total_unchecked` (AST line 4600): loop-free. -/
theorem «fb_rlp_item_total_unchecked» : TerminatingFunBoundedOn GuestInv
    (ofString "rlp_item_total_unchecked") K.«rlp_item_total_unchecked» := by
  fb_prove 114 Guest.Software.guestFn_rlp_item_total_unchecked K.«rlp_item_total_unchecked»

end InitECandidate.Solver.Wave8Leaves.Rlp
