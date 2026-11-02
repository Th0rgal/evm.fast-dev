import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpLoops

/-! RLP / byte-decoding family, part 5: RLP encoders and length helpers. -/

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

theorem «fb__node_needs_rlp» : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp» := by
  fb_prove 283 Guest.Software.guestFn__node_needs_rlp K.«_node_needs_rlp»

theorem «fb_rlp_be_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_be_len") K.«rlp_be_len» := by
  fb_prove 118 Guest.Software.guestFn_rlp_be_len K.«rlp_be_len»

theorem «fb_rlp_header_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_header_len") K.«rlp_header_len» := by
  fb_prove 121 Guest.Software.guestFn_rlp_header_len K.«rlp_header_len»

theorem «fb_rlp_bytes_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_bytes_encoded_len") K.«rlp_bytes_encoded_len» := by
  fb_prove 125 Guest.Software.guestFn_rlp_bytes_encoded_len K.«rlp_bytes_encoded_len»

theorem «fb_rlp_value_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_value_encoded_len") K.«rlp_value_encoded_len» := by
  fb_prove 286 Guest.Software.guestFn_rlp_value_encoded_len K.«rlp_value_encoded_len»

theorem «fb_rlp_put_be» : TerminatingFunBoundedOn GuestInv (ofString "rlp_put_be") K.«rlp_put_be» := by
  fb_prove 119 Guest.Software.guestFn_rlp_put_be K.«rlp_put_be»

theorem «fb_rlp_write_header» : TerminatingFunBoundedOn GuestInv (ofString "rlp_write_header") K.«rlp_write_header» := by
  fb_prove 120 Guest.Software.guestFn_rlp_write_header K.«rlp_write_header»

theorem «fb_rlp_encode_bytes» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_bytes") K.«rlp_encode_bytes» := by
  fb_prove 122 Guest.Software.guestFn_rlp_encode_bytes K.«rlp_encode_bytes»

theorem «fb_rlp_encode_list_header» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_list_header") K.«rlp_encode_list_header» := by
  fb_prove 124 Guest.Software.guestFn_rlp_encode_list_header K.«rlp_encode_list_header»

theorem «fb_rlp_list_header_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_list_header_len") K.«rlp_list_header_len» := by
  fb_prove 126 Guest.Software.guestFn_rlp_list_header_len K.«rlp_list_header_len»

theorem «fb_rlp_encode_word» : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word» := by
  fb_prove 123 Guest.Software.guestFn_rlp_encode_word K.«rlp_encode_word»

theorem «fb_rlp_finish_list» : TerminatingFunBoundedOn GuestInv (ofString "rlp_finish_list") K.«rlp_finish_list» := by
  fb_prove 833 Guest.Software.guestFn_rlp_finish_list K.«rlp_finish_list»

theorem «fb_rlp_word_encoded_len» : TerminatingFunBoundedOn GuestInv (ofString "rlp_word_encoded_len") K.«rlp_word_encoded_len» := by
  fb_prove 127 Guest.Software.guestFn_rlp_word_encoded_len K.«rlp_word_encoded_len»

theorem «fb_withdrawal_rlp_len» : TerminatingFunBoundedOn GuestInv (ofString "withdrawal_rlp_len") K.«withdrawal_rlp_len» := by
  fb_prove 837 Guest.Software.guestFn_withdrawal_rlp_len K.«withdrawal_rlp_len»

theorem «fb_encode_withdrawal_rlp» : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp» := by
  fb_prove 838 Guest.Software.guestFn_encode_withdrawal_rlp K.«encode_withdrawal_rlp»

end InitECandidate.Solver.Wave8Leaves.Rlp
