import InitECandidate.Solver.Wave8GuestInv.ContractParts.C02
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.Common
import InitECandidate.Solver.GuestGlobalKeep
import Guest.SoftwareAst

/-! Proof of `nk_mpt_nibble_key : RetNibbles (ofString "mpt_nibble_key")` for R13-M4b-MptKeepsTwin. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R13MptKeepsTwin

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.M13

theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_key_to_nibbles :
    originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
  lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_key_to_nibbles) rfl

theorem lookup_mpt_nibble_key :
    originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ([(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_nibble_key, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl

/-! ### 1. `keccak256` preserves all globals -/

def keccakGood (f : MlS) : Bool :=
  (["keccak256", "keccak_absorb_block", "keccak_f1600", "memcpy", "memzero"] : List String).map ofString |>.contains f

theorem keccak_bodies (watched : MlS) :
    ∀ f, keccakGood f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      keepsG watched keccakGood body = true := by
  intro f hf values body callee rs hl
  simp only [keccakGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak256) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memcpy) rfl) hl
    subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memzero) rfl) hl
    subst hb; rfl

theorem call_keccak256_globals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "keccak256") args)).2.globals = s.globals := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  exact evaluate_keepsG key keccakGood (keccak_bodies key)
    (.call (some (none, none)) (ofString "keccak256") args) rfl s hc

/-! ### 2. Single nibble store helper (`b >> 4` and `b & 15` are `< 16`) -/

private theorem memB_eq_memByteAt_local {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memB s a = (memByteAt s.memory s.be (BitVec.ofNat 64 a)).toNat := by
  unfold memB memByteAt memWordAt
  cases s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w => rfl

private theorem byteAlign_lt_heapEnd_local {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    addr.toNat < 33806089704 := by
  rw [hma, M11.ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  omega

theorem storeByte_nibble_step {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {addr val : BitVec 64}
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word addr)))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some (.val (.word val)))
    (hval16 : val.toNat < 16)
    (hrun : evaluateHOLFiniteState s (.storeByte dstExp valExp) = (none, post)) :
    post.locals = s.locals ∧ post.globals = s.globals ∧
    post.memaddrs = ordinaryDomain ∧
    addr.toNat < 33806089704 ∧
    memB post addr.toNat < 16 ∧
    (∀ a : Nat, a < 2 ^ 64 → a ≠ addr.toNat → memB post a = memB s a) := by
  by_cases hdom : s.memaddrs (panByteAlignHOL addr)
  · obtain ⟨mem', hev, hsame, hdiff, _⟩ := evaluate_storeByte_word hdst hval hdom
    rw [hev] at hrun
    injection hrun with _ hpost
    subst hpost
    refine ⟨rfl, rfl, hma, byteAlign_lt_heapEnd_local hma addr hdom, ?_, ?_⟩
    · rw [memB_eq_memByteAt_local]
      dsimp only
      have had : BitVec.ofNat 64 addr.toNat = addr := BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt addr.isLt)
      rw [had, hsame, UInt8.toNat_ofNat']
      have h256 : (2 ^ 8 : Nat) = 256 := by decide
      rw [h256]
      omega
    · intro a ha hne
      simp only [memB_eq_memByteAt_local]
      have hbne : BitVec.ofNat 64 a ≠ addr := by
        intro heq
        apply hne
        have := congrArg BitVec.toNat heq
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at this
      exact congrArg UInt8.toNat (hdiff (BitVec.ofNat 64 a) hbne)
  · rw [evaluateHOLFiniteState_storeByte, hdst, hval] at hrun
    unfold panMemStoreByteWord8HOL at hrun
    dsimp only at hrun
    cases s.memory (panByteAlignHOL addr) with
    | word cell => simp [hdom] at hrun

private theorem lsr4_lt_16 (b : BitVec 64) (hb : b.toNat < 256) :
    (b >>> (4 : Nat)).toNat < 16 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change b.toNat / 16 < 16
  omega

private theorem and15_lt_16 (b : BitVec 64) :
    (b &&& 15#64).toNat < 16 := by
  have hle : (b &&& 15#64).toNat ≤ (15#64 : BitVec 64).toNat := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  have h15 : (15#64 : BitVec 64).toNat = 15 := rfl
  omega

private theorem loadByte_lt_256 {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.loadByte e) = some v) :
    ∃ b : BitVec 64, v = .val (.word b) ∧ b.toNat < 256 := by
  simp only [evalHOLExact] at h
  split at h
  · rename_i addr _
    simp only [panMemLoadByteHOL] at h
    cases hm : s.memory (panByteAlignHOL addr) with
    | word cell =>
      simp only [hm] at h
      split at h
      · simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨BitVec.ofNat 64 (panGetByteHOL addr cell s.be).toNat, rfl, ?_⟩
        have hb : (panGetByteHOL addr cell s.be).toNat < 256 := (panGetByteHOL addr cell s.be).toNat_lt_size
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact hb
      · simp at h
  · simp at h

/-! ### 3. `key_to_nibbles` nibble-writing postcondition (with no-wrap from `ordinaryDomain`) -/

def KeyToNibblesInv {F : Type} (key0 n0 out0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.memaddrs = ordinaryDomain ∧
  out0.toNat ≤ heapLimit ∧
  ∃ iv : BitVec 64,
    s.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
    s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat ≤ n0.toNat ∧
    out0.toNat + 2 * iv.toNat ≤ 33806089704 ∧
    NibblesOK s out0.toNat (2 * iv.toNat)

private theorem ktn_pair_step {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (_key0 _n0 out0 iv bv : BitVec 64) (bName : String) (off : Nat)
    (hoff : off < 4)
    (hma : s.memaddrs = ordinaryDomain)
    (hdom_prev : out0.toNat + 2 * (iv.toNat + off) ≤ 33806089704)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hl_b : s.locals.lookup (ofString bName) = some (.val (.word bv)))
    (hb256 : bv.toNat < 256)
    (hnib : NibblesOK s out0.toNat (2 * (iv.toNat + off)))
    (stHi stLo : ProgHOL 64)
    (hstHi : stHi = if off = 0 then
        .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")]])
          (.shift .lsr (.var .local (ofString bName)) (.const 4#64))
      else
        .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off))])
          (.shift .lsr (.var .local (ofString bName)) (.const 4#64)))
    (hstLo : stLo = .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off + 1))])
          (.op .and [.var .local (ofString bName), .const 15#64])) :
    ∀ post, evaluateHOLFiniteState s (.seq stHi stLo) = (none, post) →
      post.locals = s.locals ∧ post.globals = s.globals ∧
      post.memaddrs = ordinaryDomain ∧
      out0.toNat + 2 * (iv.toNat + off + 1) ≤ 33806089704 ∧
      NibblesOK post out0.toNat (2 * (iv.toNat + off + 1)) := by
  intro post hseq
  have h264 : (33806089704 : Nat) + 8 < 2 ^ 64 := by decide
  have h2i_lt : 2 * iv.toNat < 2 ^ 64 := by omega
  have hmul_eq : (2#64 * iv).toNat = 2 * iv.toNat := by
    rw [BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h2i_lt]
  have ha0_nat : (out0 + (2#64 * iv + BitVec.ofNat 64 (2 * off))).toNat = out0.toNat + 2 * (iv.toNat + off) := by
    have h1 : (BitVec.ofNat 64 (2 * off)).toNat = 2 * off := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (2#64 * iv + BitVec.ofNat 64 (2 * off)).toNat = 2 * iv.toNat + 2 * off := by
      rw [BitVec.toNat_add, hmul_eq, h1, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, h2, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [evaluateHOLFiniteState_seq_line780] at hseq
  rcases hr1 : evaluateHOLFiniteState s stHi with ⟨r1, s1⟩
  rw [hr1] at hseq
  cases r1 with
  | some _ => simp at hseq
  | none =>
    dsimp only at hseq
    have hev_hi_val : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.shift .lsr (.var .local (ofString bName)) (.const 4#64)) = some (.val (.word (bv >>> 4))) := by
      simp [evalHOLExact, hl_b, wordShiftHOL]
    have hev_hi_dst : ∃ addrHi : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (if off = 0 then
            .op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")]]
          else
            .op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off))]) =
          some (.val (.word addrHi)) ∧
        addrHi.toNat = out0.toNat + 2 * (iv.toNat + off) := by
      by_cases h0 : off = 0
      · subst h0
        refine ⟨out0 + (2#64 * iv + 0#64), ?_, ?_⟩
        · simp [evalHOLExact, evalListHOLExact, hl_out, hl_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        · rw [BitVec.add_zero, BitVec.toNat_add, hmul_eq, Nat.mod_eq_of_lt (by omega)]; omega
      · refine ⟨out0 + (2#64 * iv + (BitVec.ofNat 64 (2 * off) + 0#64)), ?_, ?_⟩
        · simp [h0, evalHOLExact, evalListHOLExact, hl_out, hl_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        · rw [BitVec.add_zero]; exact ha0_nat
    obtain ⟨addrHi, hdstHi, haddrHi_nat⟩ := hev_hi_dst
    have hr1' : evaluateHOLFiniteState s
        (.storeByte (if off = 0 then
            .op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")]]
          else
            .op .add [.var .local (ofString "out"), .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off))])
          (.shift .lsr (.var .local (ofString bName)) (.const 4#64))) = (none, s1) := by
      rw [hstHi] at hr1
      split at hr1 <;> rename_i hc <;> simp [hc] at hr1 ⊢ <;> exact hr1
    obtain ⟨hl1, hg1, hma1, hdom1, hmb1, hother1⟩ :=
      storeByte_nibble_step hma hdstHi hev_hi_val (lsr4_lt_16 bv hb256) hr1'
    rw [haddrHi_nat] at hdom1
    have ha1_nat : (out0 + (2#64 * iv + (BitVec.ofNat 64 (2 * off + 1) + 0#64))).toNat = out0.toNat + 2 * (iv.toNat + off) + 1 := by
      have h1 : (BitVec.ofNat 64 (2 * off + 1)).toNat = 2 * off + 1 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.add_zero]
      have h2 : (2#64 * iv + BitVec.ofNat 64 (2 * off + 1)).toNat = 2 * iv.toNat + (2 * off + 1) := by
        rw [BitVec.toNat_add, hmul_eq, h1, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toNat_add, h2, Nat.mod_eq_of_lt (by omega)]
      omega
    subst hstLo
    have hev_lo_dst : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off + 1))]) =
        some (.val (.word (out0 + (2#64 * iv + (BitVec.ofNat 64 (2 * off + 1) + 0#64))))) := by
      simp [evalHOLExact, evalListHOLExact, hl1, hl_out, hl_i, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hev_lo_val : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.op .and [.var .local (ofString bName), .const 15#64]) =
        some (.val (.word (bv &&& (15#64 &&& 18446744073709551615#64)))) := by
      simp only [evalHOLExact, evalListHOLExact, hl1, hl_b, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      rfl
    have hand_lt : (bv &&& (15#64 &&& 18446744073709551615#64)).toNat < 16 := by
      have hm : (15#64 &&& 18446744073709551615#64 : BitVec 64) = 15#64 := by decide
      rw [hm]; exact and15_lt_16 bv
    obtain ⟨hl2, hg2, hma2, hdom2, hmb2, hother2⟩ :=
      storeByte_nibble_step hma1 hev_lo_dst hev_lo_val hand_lt hseq
    rw [ha1_nat] at hdom2
    refine ⟨hl2.trans hl1, hg2.trans hg1, hma2, by omega, ?_⟩
    intro k hk
    by_cases hk_last : k = 2 * (iv.toNat + off) + 1
    · subst hk_last
      have heq_a : out0.toNat + (2 * (iv.toNat + off) + 1) =
          (out0 + (2#64 * iv + (BitVec.ofNat 64 (2 * off + 1) + 0#64))).toNat := by omega
      rw [heq_a]; exact hmb2
    · have hne2 : out0.toNat + k ≠ (out0 + (2#64 * iv + (BitVec.ofNat 64 (2 * off + 1) + 0#64))).toNat := by omega
      rw [hother2 (out0.toNat + k) (by omega) hne2]
      by_cases hk_prev : k = 2 * (iv.toNat + off)
      · subst hk_prev
        rw [← haddrHi_nat]; exact hmb1
      · have hne1 : out0.toNat + k ≠ addrHi.toNat := by omega
        rw [hother1 (out0.toNat + k) (by omega) hne1]
        exact hnib k (by omega)

private theorem ktn_dec_byte_step {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (key0 n0 out0 iv : BitVec 64) (bName : String) (off : Nat)
    (hb_ne_key : ofString bName ≠ ofString "key")
    (hb_ne_n : ofString bName ≠ ofString "n")
    (hb_ne_out : ofString bName ≠ ofString "out")
    (hb_ne_i : ofString bName ≠ ofString "i")
    (hoff : off < 4)
    (hma : s.memaddrs = ordinaryDomain)
    (hdom_prev : out0.toNat + 2 * (iv.toNat + off) ≤ 33806089704)
    (hl_key : s.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hnib : NibblesOK s out0.toNat (2 * (iv.toNat + off)))
    (ldExp : ExpHOL 64) (stHi stLo tail : ProgHOL 64)
    (hstHi : stHi = if off = 0 then
        .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")]])
          (.shift .lsr (.var .local (ofString bName)) (.const 4#64))
      else
        .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off))])
          (.shift .lsr (.var .local (ofString bName)) (.const 4#64)))
    (hstLo : stLo = .storeByte (.op .add [.var .local (ofString "out"),
          .panop .mul [.const 2#64, .var .local (ofString "i")], .const (BitVec.ofNat 64 (2 * off + 1))])
          (.op .and [.var .local (ofString bName), .const 15#64]))
    (htail : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.memaddrs = ordinaryDomain →
      mid.globals = s.globals →
      mid.locals.lookup (ofString "key") = some (.val (.word key0)) →
      mid.locals.lookup (ofString "n") = some (.val (.word n0)) →
      mid.locals.lookup (ofString "out") = some (.val (.word out0)) →
      mid.locals.lookup (ofString "i") = some (.val (.word iv)) →
      out0.toNat + 2 * (iv.toNat + off + 1) ≤ 33806089704 →
      NibblesOK mid out0.toNat (2 * (iv.toNat + off + 1)) →
      ∀ u, evaluateHOLFiniteState mid tail = (none, u) →
        u.memaddrs = ordinaryDomain ∧ u.globals = s.globals ∧
        ∃ iv' : BitVec 64,
          u.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
          u.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
          u.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
          u.locals.lookup (ofString "i") = some (.val (.word iv')) ∧
          iv'.toNat ≤ n0.toNat ∧
          out0.toNat + 2 * iv'.toNat ≤ 33806089704 ∧
          NibblesOK u out0.toNat (2 * iv'.toNat)) :
    ∀ post, evaluateHOLFiniteState s
      (.dec (ofString bName) .one (.loadByte ldExp) (.seq stHi (.seq stLo tail))) = (none, post) →
      post.memaddrs = ordinaryDomain ∧ post.globals = s.globals ∧
      ∃ iv' : BitVec 64,
        post.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
        post.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
        post.locals.lookup (ofString "i") = some (.val (.word iv')) ∧
        iv'.toNat ≤ n0.toNat ∧
        out0.toNat + 2 * iv'.toNat ≤ 33806089704 ∧
        NibblesOK post out0.toNat (2 * iv'.toNat) := by
  intro post hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  rcases hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte ldExp) with _ | bvVal
  · rw [hld] at hrun; simp at hrun
  · rw [hld] at hrun
    obtain ⟨bv, rfl, hb256⟩ := loadByte_lt_256 s ldExp bvVal hld
    have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word bv) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hrun; rw [if_pos hsh] at hrun
    let sb := setVarHOLFinite (ofString bName) (.val (.word bv)) s
    have hsb_out : sb.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out, hb_ne_out]
    have hsb_i : sb.locals.lookup (ofString "i") = some (.val (.word iv)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_i, hb_ne_i]
    have hsb_key : sb.locals.lookup (ofString "key") = some (.val (.word key0)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_key, hb_ne_key]
    have hsb_n : sb.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_n, hb_ne_n]
    have hsb_b : sb.locals.lookup (ofString bName) = some (.val (.word bv)) := by
      simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hresVarEq_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (nm k : MlS)
        (o : Option (ValueHOL 64)), k ≠ nm → (HolFiniteMapExact.resVarEq mp (nm, o)).lookup k = mp.lookup k := by
      intro mp nm k o hne
      rcases o with _ | vo
      · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne]
      · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
        split
        · rename_i heq; exact absurd heq hne
        · rfl
    have hseq_assoc : ∀ (p1 p2 p3 : ProgHOL 64) (st0 : PanSemStateFiniteExact 64 F),
        evaluateHOLFiniteState st0 (.seq p1 (.seq p2 p3)) =
          evaluateHOLFiniteState st0 (.seq (.seq p1 p2) p3) := by
      intro p1 p2 p3 st0
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_seq_line780,
          evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState st0 p1 with ⟨r, m⟩
      cases r
      · dsimp only
        rw [evaluateHOLFiniteState_seq_line780]
      · rfl
    change (let res := evaluateHOLFiniteState sb (.seq stHi (.seq stLo tail))
      (res.1, { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString bName, s.locals.lookup (ofString bName)) })) =
      (none, post) at hrun
    rw [hseq_assoc, evaluateHOLFiniteState_seq_line780] at hrun
    rcases hp12 : evaluateHOLFiniteState sb (.seq stHi stLo) with ⟨r12, mid⟩
    rw [hp12] at hrun
    cases r12 with
    | some _ => simp at hrun
    | none =>
      dsimp only at hrun
      obtain ⟨hmid_loc, hmid_glob, hmid_ma, hmid_dom, hmid_nib⟩ :=
        ktn_pair_step sb key0 n0 out0 iv bv bName off hoff hma hdom_prev
          hsb_out hsb_i hsb_b hb256 hnib stHi stLo hstHi hstLo mid hp12
      rcases htail_run : evaluateHOLFiniteState mid tail with ⟨rt, u⟩
      rw [htail_run] at hrun
      cases rt with
      | some _ => simp at hrun
      | none =>
        dsimp only at hrun
        injection hrun with _ hpost
        subst hpost
        obtain ⟨hu_ma, hu_glob, iv', hu_key, hu_n, hu_out, hu_i, hu_le, hu_dom, hu_nib⟩ :=
          htail mid hmid_ma hmid_glob (hmid_loc.symm ▸ hsb_key) (hmid_loc.symm ▸ hsb_n)
            (hmid_loc.symm ▸ hsb_out) (hmid_loc.symm ▸ hsb_i) hmid_dom hmid_nib u htail_run
        refine ⟨hu_ma, hu_glob, iv', ?_, ?_, ?_, ?_, hu_le, hu_dom, hu_nib⟩
        · rw [hresVarEq_ne _ _ _ _ hb_ne_key.symm]; exact hu_key
        · rw [hresVarEq_ne _ _ _ _ hb_ne_n.symm]; exact hu_n
        · rw [hresVarEq_ne _ _ _ _ hb_ne_out.symm]; exact hu_out
        · rw [hresVarEq_ne _ _ _ _ hb_ne_i.symm]; exact hu_i

private def ktnLoop1 : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_key_to_nibbles with
  | .dec _ _ _ (.seq l1 _) => l1
  | _ => .skip

private def ktnLoop2 : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn_key_to_nibbles with
  | .dec _ _ _ (.seq _ (.seq l2 _)) => l2
  | _ => .skip

private def ktnBody1 : ProgHOL 64 :=
  match ktnLoop1 with
  | .while _ b => b
  | _ => .skip

private def ktnBody2 : ProgHOL 64 :=
  match ktnLoop2 with
  | .while _ b => b
  | _ => .skip

private def noBreakOrCont : ProgHOL 64 → Bool
  | .dec _ _ _ b => noBreakOrCont b
  | .seq a b => noBreakOrCont a && noBreakOrCont b
  | .storeByte _ _ | .assign .local _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreakOrCont {F : Type} (p : ProgHOL 64) (hp : noBreakOrCont p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue ∧
    (∀ rv, (evaluateHOLFiniteState s p).1 ≠ some (.returned rv)) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨by simp, by simp, fun _ => by simp⟩
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> exact ⟨by simp, by simp, fun _ => by simp⟩
      · exact ⟨by simp, by simp, fun _ => by simp⟩
    · exact ⟨by simp, by simp, fun _ => by simp⟩
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreakOrCont] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨by simp, by simp, fun _ => by simp⟩
      · split <;> exact ⟨by simp, by simp, fun _ => by simp⟩
  | dec nm _ _ b =>
    have hb : noBreakOrCont b = true := by simpa [shape, noBreakOrCont] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨by simp, by simp, fun _ => by simp⟩
    · rename_i val _
      split
      · have ih := evaluate_noBreakOrCont b hb (setVarHOLFinite nm val s)
        exact ⟨ih.1, ih.2.1, ih.2.2⟩
      · exact ⟨by simp, by simp, fun _ => by simp⟩
  | seq a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreakOrCont a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreakOrCont b hab.2 m
    | some _ => exact ha
  | _ => simp [shape, noBreakOrCont] at hp

private theorem ktn_assign_i_step {F : Type}
    (s : PanSemStateFiniteExact 64 F) (key0 n0 out0 iv : BitVec 64) (step : Nat)
    (hma : s.memaddrs = ordinaryDomain)
    (hl_key : s.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hl_n : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_i : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hstep_le : iv.toNat + step ≤ n0.toNat)
    (hstep_lt64 : step < 64)
    (hdom_next : out0.toNat + 2 * (iv.toNat + step) ≤ 33806089704)
    (hnib : NibblesOK s out0.toNat (2 * (iv.toNat + step))) :
    ∀ u, evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) = (none, u) →
      u.memaddrs = ordinaryDomain ∧ u.globals = s.globals ∧
      ∃ iv' : BitVec 64,
        u.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
        u.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
        u.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
        u.locals.lookup (ofString "i") = some (.val (.word iv')) ∧
        iv'.toNat ≤ n0.toNat ∧
        out0.toNat + 2 * iv'.toNat ≤ 33806089704 ∧
        NibblesOK u out0.toNat (2 * iv'.toNat) := by
  intro u hrun
  rw [evaluateHOLFiniteState_assign] at hrun
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]) =
      some (.val (.word (iv + (BitVec.ofNat 64 step + 0#64)))) := by
    simp [evalHOLExact, evalListHOLExact, hl_i, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hev] at hrun; dsimp only at hrun
  have hvalid : isValidValueHOLFinite s .local (ofString "i") (.val (.word (iv + (BitVec.ofNat 64 step + 0#64)))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, hl_i, shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hvalid] at hrun
  injection hrun with _ hu; subst hu
  let iv' := iv + (BitVec.ofNat 64 step + 0#64)
  have hiv'_nat : iv'.toNat = iv.toNat + step := by
    have hn_lt := n0.isLt
    have hs_nat : (BitVec.ofNat 64 step).toNat = step := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    dsimp only [iv']
    rw [BitVec.add_zero, BitVec.toNat_add, hs_nat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hma, rfl, iv', ?_, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_key,
      show ofString "i" ≠ ofString "key" by decide]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_n,
      show ofString "i" ≠ ofString "n" by decide]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out,
      show ofString "i" ≠ ofString "out" by decide]
  · simp [iv', setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [hiv'_nat]; exact hnib

private theorem ktn_while1_none {F : Type}
    (key0 n0 out0 : BitVec 64) :
    ∀ (k : Nat) (s post : PanSemStateFiniteExact 64 F),
      s.clock = k →
      KeyToNibblesInv key0 n0 out0 s →
      evaluateHOLFiniteState s ktnLoop1 = (none, post) →
      KeyToNibblesInv key0 n0 out0 post ∧ post.globals = s.globals := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s post hclk hinv hrun
    obtain ⟨hma, hout_lim, iv, hl_key, hl_n, hl_out, hl_i, hiv_le, hdom_prev, hnib⟩ := hinv
    have hl1_eq : ktnLoop1 =
        .while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 4#64])) ktnBody1 := rfl
    rw [hl1_eq, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    have h264 : (33806089704 : Nat) + 8 < 2 ^ 64 := by decide
    have hiv4_eq : (iv + 4#64).toNat = iv.toNat + 4 := by
      rw [BitVec.toNat_add, show (4#64 : BitVec 64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hev_cond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 4#64])) =
        some (.val (.word (if iv.toNat + 4 ≤ n0.toNat then 1#64 else 0#64))) := by
      simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hl_n, hl_i,
        wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def, hiv4_eq]
    rw [hev_cond] at hrun; dsimp only at hrun
    by_cases hc : iv.toNat + 4 ≤ n0.toNat
    · rw [if_pos hc] at hrun
      have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hrun
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hrun
      · rw [if_neg hk0] at hrun
        have hnbc := evaluate_noBreakOrCont ktnBody1 rfl (decClockHOLFinite s)
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) ktnBody1
        rcases hb_run : evaluateHOLFiniteState (decClockHOLFinite s) ktnBody1 with ⟨rb, mid⟩
        rw [hb_run] at hrun hnbc hrem
        have hmid_clk : mid.clock < k := by
          change mid.clock ≤ s.clock - 1 at hrem; omega
        cases rb with
        | none =>
          change evaluateHOLFiniteState (decClockHOLFinite s) ktnBody1 = (none, mid) at hb_run
          dsimp only [ktnBody1, ktnLoop1, sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
            List.map, Option.map] at hb_run
          obtain ⟨hma_m, hg_m, iv', hk_m, hn_m, ho_m, hi_m, hle_m, hdom_m, hnib_m⟩ :=
            ktn_dec_byte_step (decClockHOLFinite s) key0 n0 out0 iv "b0" 0
              (by decide) (by decide) (by decide) (by decide) (by omega)
              hma (by simpa using hdom_prev) hl_key hl_n hl_out hl_i
              (show NibblesOK s out0.toNat (2 * (iv.toNat + 0)) by simpa using hnib)
              _ _ _ _ rfl rfl
              (fun m1 hm1ma hm1g hm1k hm1n hm1o hm1i hm1dom hm1nib u1 hu1 => by
                obtain ⟨hma2, hg2, iv2, hk2, hn2, ho2, hi2, hle2, hdom2, hnib2⟩ :=
                  ktn_dec_byte_step m1 key0 n0 out0 iv "b1" 1
                    (by decide) (by decide) (by decide) (by decide) (by omega)
                    hm1ma (by simpa using hm1dom) hm1k hm1n hm1o hm1i (by simpa using hm1nib)
                    _ _ _ _ rfl rfl
                    (fun m2 hm2ma hm2g hm2k hm2n hm2o hm2i hm2dom hm2nib u2 hu2 => by
                      obtain ⟨hma3, hg3, iv3, hk3, hn3, ho3, hi3, hle3, hdom3, hnib3⟩ :=
                        ktn_dec_byte_step m2 key0 n0 out0 iv "b2" 2
                          (by decide) (by decide) (by decide) (by decide) (by omega)
                          hm2ma (by simpa using hm2dom) hm2k hm2n hm2o hm2i (by simpa using hm2nib)
                          _ _ _ _ rfl rfl
                          (fun m3 hm3ma hm3g hm3k hm3n hm3o hm3i hm3dom hm3nib u3 hu3 => by
                            obtain ⟨hma4, hg4, iv4, hk4, hn4, ho4, hi4, hle4, hdom4, hnib4⟩ :=
                              ktn_dec_byte_step m3 key0 n0 out0 iv "b3" 3
                                (by decide) (by decide) (by decide) (by decide) (by omega)
                                hm3ma (by simpa using hm3dom) hm3k hm3n hm3o hm3i (by simpa using hm3nib)
                                _ _ _ _ rfl rfl
                                (fun m4 hm4ma hm4g hm4k hm4n hm4o hm4i hm4dom hm4nib u4 hu4 => by
                                  obtain ⟨hma5, hg5, iv5, hk5, hn5, ho5, hi5, hle5, hdom5, hnib5⟩ :=
                                    ktn_assign_i_step m4 key0 n0 out0 iv 4 hm4ma hm4k hm4n hm4o hm4i
                                      hc (by decide) (by simpa [Nat.add_assoc] using hm4dom)
                                      (by simpa [Nat.add_assoc] using hm4nib) u4 hu4
                                  exact ⟨hma5, hg5.trans hm4g, iv5, hk5, hn5, ho5, hi5, hle5, hdom5, hnib5⟩)
                                u3 hu3
                            exact ⟨hma4, hg4.trans hm3g, iv4, hk4, hn4, ho4, hi4, hle4, hdom4, hnib4⟩)
                          u2 hu2
                      exact ⟨hma3, hg3.trans hm2g, iv3, hk3, hn3, ho3, hi3, hle3, hdom3, hnib3⟩)
                    u1 hu1
                exact ⟨hma2, hg2.trans hm1g, iv2, hk2, hn2, ho2, hi2, hle2, hdom2, hnib2⟩)
              mid hb_run
          obtain ⟨hpost_inv, hpost_g⟩ :=
            ih mid.clock hmid_clk mid post rfl ⟨hma_m, hout_lim, iv', hk_m, hn_m, ho_m, hi_m, hle_m, hdom_m, hnib_m⟩ hrun
          exact ⟨hpost_inv, hpost_g.trans hg_m⟩
        | some r =>
          cases r with
          | «break» => exact False.elim (hnbc.1 rfl)
          | «continue» => exact False.elim (hnbc.2.1 rfl)
          | _ => simp at hrun
    · rw [if_neg hc] at hrun
      have h00 : ¬ ((0#64 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00] at hrun
      injection hrun with _ hpost; subst hpost
      exact ⟨⟨hma, hout_lim, iv, hl_key, hl_n, hl_out, hl_i, hiv_le, hdom_prev, hnib⟩, rfl⟩

private theorem ktn_while2_none {F : Type}
    (key0 n0 out0 : BitVec 64) :
    ∀ (k : Nat) (s post : PanSemStateFiniteExact 64 F),
      s.clock = k →
      KeyToNibblesInv key0 n0 out0 s →
      evaluateHOLFiniteState s ktnLoop2 = (none, post) →
      post.memaddrs = ordinaryDomain ∧ post.globals = s.globals ∧
      out0.toNat + 2 * n0.toNat ≤ 33806089704 ∧
      NibblesOK post out0.toNat (2 * n0.toNat) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s post hclk hinv hrun
    obtain ⟨hma, hout_lim, iv, hl_key, hl_n, hl_out, hl_i, hiv_le, hdom_prev, hnib⟩ := hinv
    have hl2_eq : ktnLoop2 =
        .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) ktnBody2 := rfl
    rw [hl2_eq, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    have hev_cond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iv.toNat < n0.toNat then 1#64 else 0#64))) := by
      simp [evalHOLFinite, evalHOLExact, hl_n, hl_i,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hev_cond] at hrun; dsimp only at hrun
    by_cases hc : iv.toNat < n0.toNat
    · rw [if_pos hc] at hrun
      have h10 : (1#64 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hrun
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hrun
      · rw [if_neg hk0] at hrun
        have hnbc := evaluate_noBreakOrCont ktnBody2 rfl (decClockHOLFinite s)
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) ktnBody2
        rcases hb_run : evaluateHOLFiniteState (decClockHOLFinite s) ktnBody2 with ⟨rb, mid⟩
        rw [hb_run] at hrun hnbc hrem
        have hmid_clk : mid.clock < k := by
          change mid.clock ≤ s.clock - 1 at hrem; omega
        cases rb with
        | none =>
          change evaluateHOLFiniteState (decClockHOLFinite s) ktnBody2 = (none, mid) at hb_run
          dsimp only [ktnBody2, ktnLoop2, sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
            List.map, Option.map] at hb_run
          obtain ⟨hma_m, hg_m, iv', hk_m, hn_m, ho_m, hi_m, hle_m, hdom_m, hnib_m⟩ :=
            ktn_dec_byte_step (decClockHOLFinite s) key0 n0 out0 iv "b" 0
              (by decide) (by decide) (by decide) (by decide) (by omega)
              hma (by simpa using hdom_prev) hl_key hl_n hl_out hl_i
              (show NibblesOK s out0.toNat (2 * (iv.toNat + 0)) by simpa using hnib)
              _ _ _ _ rfl rfl
              (fun m1 hm1ma hm1g hm1k hm1n hm1o hm1i hm1dom hm1nib u1 hu1 => by
                obtain ⟨hma2, hg2, iv2, hk2, hn2, ho2, hi2, hle2, hdom2, hnib2⟩ :=
                  ktn_assign_i_step m1 key0 n0 out0 iv 1 hm1ma hm1k hm1n hm1o hm1i
                    (by omega) (by decide) (by simpa using hm1dom) (by simpa using hm1nib) u1 hu1
                exact ⟨hma2, hg2.trans hm1g, iv2, hk2, hn2, ho2, hi2, hle2, hdom2, hnib2⟩)
              mid hb_run
          obtain ⟨hp_ma, hp_g, hp_dom, hp_nib⟩ :=
            ih mid.clock hmid_clk mid post rfl ⟨hma_m, hout_lim, iv', hk_m, hn_m, ho_m, hi_m, hle_m, hdom_m, hnib_m⟩ hrun
          exact ⟨hp_ma, hp_g.trans hg_m, hp_dom, hp_nib⟩
        | some r =>
          cases r with
          | «break» => exact False.elim (hnbc.1 rfl)
          | «continue» => exact False.elim (hnbc.2.1 rfl)
          | _ => simp at hrun
    · rw [if_neg hc] at hrun
      have h00 : ¬ ((0#64 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00] at hrun
      injection hrun with _ hpost; subst hpost
      have heq_in : iv.toNat = n0.toNat := by omega
      rw [heq_in] at hdom_prev hnib
      exact ⟨hma, rfl, hdom_prev, hnib⟩

private theorem while_no_return_of_body {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64) (hb : noBreakOrCont body = true) :
    ∀ (kk : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = kk →
      ∀ v', (evaluateHOLFiniteState st (.while cond body)).1 ≠ some (.returned v') := by
  intro kk
  induction kk using Nat.strong_induction_on with
  | h kk ih =>
    intro st hkk v' hbad
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hbad
    split at hbad
    · split at hbad
      · split at hbad
        · simp at hbad
        · have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hnr_b := (evaluate_noBreakOrCont body hb (decClockHOLFinite st)).2.2
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨rb1, mb1⟩
          rw [hbr] at hbad hrem hnr_b
          cases rb1 with
          | none => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
          | some rb1' =>
            cases rb1' with
            | «continue» => exact ih mb1.clock (by simp [decClockHOLFinite, hkk] at hrem ⊢; omega) mb1 rfl v' hbad
            | returned v'' => exact hnr_b v'' rfl
            | _ => simp at hbad
      · simp at hbad
    · simp at hbad

theorem eval_call_key_to_nibbles_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (keyExp nExp outExp : ExpHOL 64) (key0 n0 out0 : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hout_lim : out0.toNat ≤ heapLimit)
    (hkey : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) keyExp =
      some (.val (.word key0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (post : PanSemStateFiniteExact 64 F)
    (hcall : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "key_to_nibbles") [keyExp, nExp, outExp]) = (none, post)) :
    post.globals = s.globals ∧ post.locals = s.locals ∧
    out0.toNat + 2 * n0.toNat ≤ 33806089704 ∧
    NibblesOK post out0.toNat (2 * n0.toNat) := by
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [keyExp, nExp, outExp] =
      some [.val (.word key0), .val (.word n0), .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hkey, hn, hout]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "key_to_nibbles")
    (ofString "key") (ofString "n") (ofString "out")
    (sourceFnBody Guest.Software.guestFn_key_to_nibbles) key0 n0 out0
    (by decide) (by decide) (by decide) (by rw [hcode]; exact lookup_key_to_nibbles)
  rw [hargs] at hcall; dsimp only at hcall; rw [hlk] at hcall; dsimp only at hcall
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hcall
  · rw [if_neg hclk0] at hcall
    let cmap := ((HolFiniteMapExact.empty.update (ofString "key", ValueHOL.val (.word key0))).update
      (ofString "n", ValueHOL.val (.word n0))).update (ofString "out", ValueHOL.val (.word out0))
    let ent := callEntryStateHOLFinite s cmap
    have hb_eq : sourceFnBody Guest.Software.guestFn_key_to_nibbles =
        .dec (ofString "i") .one (.const 0#64)
          (.seq ktnLoop1 (.seq ktnLoop2 (.return (.const 0#64)))) := rfl
    rcases hbody : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_key_to_nibbles) with ⟨rb, sb⟩
    have hbody' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_key_to_nibbles) = (rb, sb) := hbody
    rw [hbody'] at hcall
    cases rb with
    | none => simp at hcall
    | some rb' =>
      cases rb' with
      | returned rv =>
        dsimp only at hcall
        split at hcall
        · injection hcall with _ hpost; subst hpost
          rw [hb_eq, evaluateHOLFiniteState_dec_total] at hbody
          dsimp only at hbody
          have hev0 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a)) (.const 0#64) =
              some (.val (.word 0#64)) := rfl
          have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [hev0] at hbody; dsimp only at hbody; rw [if_pos hsh0] at hbody
          let e1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) ent
          have hhl_he : heapLimit ≤ 33806089704 := by decide
          have he1_inv : KeyToNibblesInv key0 n0 out0 e1 := by
            refine ⟨hma, hout_lim, 0#64, ?_, ?_, ?_, ?_, Nat.zero_le _, ?_, fun k hk => by simp at hk⟩
            · simp [e1, ent, cmap, setVarHOLFinite, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "i" ≠ ofString "key" by decide,
                show ofString "out" ≠ ofString "key" by decide,
                show ofString "n" ≠ ofString "key" by decide]
            · simp [e1, ent, cmap, setVarHOLFinite, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "i" ≠ ofString "n" by decide,
                show ofString "out" ≠ ofString "n" by decide]
            · simp [e1, ent, cmap, setVarHOLFinite, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "i" ≠ ofString "out" by decide]
            · simp [e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · show out0.toNat + 2 * 0 ≤ 33806089704; omega
          change (let res := evaluateHOLFiniteState e1 (.seq ktnLoop1 (.seq ktnLoop2 (.return (.const 0#64))))
            (res.1, { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "i", ent.locals.lookup (ofString "i")) })) =
            (some (.returned rv), sb) at hbody
          rw [evaluateHOLFiniteState_seq_line780] at hbody
          rcases hl1 : evaluateHOLFiniteState e1 ktnLoop1 with ⟨rl1, m1⟩
          rw [hl1] at hbody
          cases rl1 with
          | some r =>
            dsimp only at hbody
            injection hbody with hr1 _
            have hl1_eq : ktnLoop1 = .while (.cmp .notLower (.var .local (ofString "n"))
                (.op .add [.var .local (ofString "i"), .const 4#64])) ktnBody1 := rfl
            exact False.elim (while_no_return_of_body _ ktnBody1 rfl e1.clock e1 rfl rv
              (by rw [← hl1_eq, hl1]; exact hr1))
          | none =>
            dsimp only at hbody
            obtain ⟨hm1_inv, hm1_g⟩ := ktn_while1_none key0 n0 out0 e1.clock e1 m1 rfl he1_inv hl1
            rw [evaluateHOLFiniteState_seq_line780] at hbody
            rcases hl2 : evaluateHOLFiniteState m1 ktnLoop2 with ⟨rl2, m2⟩
            rw [hl2] at hbody
            cases rl2 with
            | some r =>
              dsimp only at hbody
              injection hbody with hr2 _
              have hl2_eq : ktnLoop2 = .while (.cmp .lower (.var .local (ofString "i"))
                  (.var .local (ofString "n"))) ktnBody2 := rfl
              exact False.elim (while_no_return_of_body _ ktnBody2 rfl m1.clock m1 rfl rv
                (by rw [← hl2_eq, hl2]; exact hr2))
            | none =>
              dsimp only at hbody
              obtain ⟨_, hm2_g, hm2_dom, hm2_nib⟩ := ktn_while2_none key0 n0 out0 m1.clock m1 m2 rfl hm1_inv hl2
              rw [evaluateHOLFiniteState_return] at hbody
              simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hbody
              have hsz : (1 : Nat) ≤ 32 := by decide
              rw [if_pos hsz] at hbody; dsimp only at hbody
              injection hbody with _ hsb
              have hsb_mem : sb.memory = m2.memory := by rw [← hsb]; rfl
              have hsb_be : sb.be = m2.be := by rw [← hsb]; rfl
              have hsb_g : sb.globals = s.globals := by
                rw [← hsb]; dsimp only [emptyLocalsHOLFinite]; exact hm2_g.trans hm1_g
              refine ⟨hsb_g, rfl, hm2_dom, ?_⟩
              intro k hk
              have hmk := hm2_nib k hk
              unfold memB at hmk ⊢
              rw [hsb_mem, hsb_be]
              exact hmk
        · simp at hcall
      | _ => simp at hcall

private theorem call_void_no_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fname : MlS) (args : List (ExpHOL 64)) (rv : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned rv) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · rename_i b callee rs _
      split
      · simp
      · dsimp only
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨rb, sb⟩
        cases rb with
        | none => simp
        | some rb' =>
          cases rb' <;> dsimp only
          case returned => split <;> simp
          all_goals simp

private theorem seq_decCall_return_ne_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nb : MlS) (sh : ShapeHOL) (fn : MlS)
    (args : List (ExpHOL 64)) (p1 : ProgHOL 64) (retExp : ExpHOL 64) :
    (evaluateHOLFiniteState s
      (.decCall nb sh fn args (.seq p1 (.return retExp)))).1 ≠ none := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · simp
  · split
    · simp
    · rename_i b callee rs _
      split
      · simp
      · dsimp only
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨ra, sa⟩
        cases ra with
        | none => simp
        | some ra' =>
          cases ra' <;> dsimp only
          case returned rva =>
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780]
              rcases evaluateHOLFiniteState
                (setVarHOLFinite nb rva { sa with locals := s.locals }) p1 with ⟨r1, s1⟩
              cases r1 with
              | some _ => simp
              | none =>
                dsimp only
                rw [evaluateHOLFiniteState_return]
                split
                · simp
                · split <;> simp
            · simp
          all_goals simp

/-! ### 4. Main theorem `nk_mpt_nibble_key` -/

theorem nk_mpt_nibble_key_proof : RetNibbles (ofString "mpt_nibble_key") := by
  refine ⟨_, _, _, lookup_mpt_nibble_key, ?_⟩
  intro F s hcode hAR _ _hnt v hret
  have hb : sourceFnBody Guest.Software.guestFn_mpt_nibble_key =
      .seq
        (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64))
          (.seq
            (.call (some (none, none)) (ofString "keccak256")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
            (.decCall (ofString "nb") .one (ofString "alloc") [.const 64#64]
              (.seq
                (.call (some (none, none)) (ofString "key_to_nibbles")
                  [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")])
                (.return (.rstruct [.var .local (ofString "nb"), .const 64#64])))))
          .skip)
        (.decCall (ofString "nb2") .one (ofString "alloc")
          [.panop .mul [.const 2#64, .var .local (ofString "klen")]]
          (.seq
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])
            (.return (.rstruct [.var .local (ofString "nb2"),
              .panop .mul [.const 2#64, .var .local (ofString "klen")]])))) := rfl
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_nibble_key)).2
  change ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
    NibblesOK post p.toNat l.toNat ∧
    (locN s "klen" ≤ 32 → l.toNat ≤ 64) ∧
    Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr")
  have hr_pair : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mpt_nibble_key) =
      (some (.returned v), post) := Prod.ext hret rfl
  clear hret
  -- Shared continuation runner for `decCall nbName alloc [szExp] (seq (call key_to_nibbles ...) (return rStruct))`
  have run_alloc_ktn : ∀ (st : PanSemStateFiniteExact 64 F) (nbName : String)
      (szExp keyExp nExp : ExpHOL 64) (n0 : BitVec 64),
      st.code = originalRuntimeCode →
      ArenaReady st →
      globN st "heap_ptr" = globN s "heap_ptr" →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) szExp =
        some (.val (.word (2#64 * n0))) →
      (∀ (st' : PanSemStateFiniteExact 64 F) (p q : BitVec 64),
        st'.memaddrs = st.memaddrs →
        st'.locals = st.locals.update (ofString nbName, .val (.word p)) →
        st'.globals = st.globals.update (ofString "heap_ptr", .val (.word q)) →
        ∃ kv : BitVec 64,
          @evalHOLExact 64 F _ st'.toExact (fun a => Classical.propDecidable (st'.memaddrs a)) keyExp =
            some (.val (.word kv)) ∧
          @evalHOLExact 64 F _ st'.toExact (fun a => Classical.propDecidable (st'.memaddrs a)) nExp =
            some (.val (.word n0)) ∧
          @evalHOLExact 64 F _ st'.toExact (fun a => Classical.propDecidable (st'.memaddrs a)) szExp =
            some (.val (.word (2#64 * n0)))) →
      evaluateHOLFiniteState st
        (.decCall (ofString nbName) .one (ofString "alloc") [szExp]
          (.seq
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [keyExp, nExp, .var .local (ofString nbName)])
            (.return (.rstruct [.var .local (ofString nbName), szExp])))) =
        (some (.returned v), post) →
      ∃ p l : BitVec 64, v = .rStruct [.val (.word p), .val (.word l)] ∧
        l = 2#64 * n0 ∧
        l.toNat = 2 * n0.toNat ∧
        NibblesOK post p.toNat l.toNat ∧
        Inside (p.toNat, l.toNat) (globN s "heap_ptr") (globN post "heap_ptr") := by
    intro st nbName szExp keyExp nExp n0 hst_code hst_AR hst_hp hsz_ev hex_after hdec
    have hsb_pos : 0 < sourceBase := by decide
    have hp_lo := hst_AR.2.1
    have hp_hi := hst_AR.2.2.1
    obtain ⟨hpw, hhp_lk, hhp_eq⟩ := M11.global_word_of_pos st "heap_ptr" (by omega)
    have hp_le_cMax : hpw.toNat ≤ cMax.toNat := by
      have : cMax.toNat = heapLimit := rfl
      omega
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hdec
    have hargs_a : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) [szExp] =
        some [.val (.word (2#64 * n0))] := by
      simp [evalListHOLFinite, evalListHOLExact, hsz_ev]
    have hlk_a := pan_one_word_lookup st.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) (2#64 * n0)
      (by rw [hst_code]; exact lookup_alloc)
    rw [hargs_a] at hdec; dsimp only at hdec; rw [hlk_a] at hdec; dsimp only at hdec
    by_cases hclk0 : st.clock = 0
    · simp [hclk0] at hdec
    · rw [if_neg hclk0] at hdec
      let ent_a := callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "n", .val (.word (2#64 * n0))))
      have hent_n : ent_a.locals.lookup (ofString "n") = some (.val (.word (2#64 * n0))) := by
        simp [ent_a, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases ha_run : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
      have ha_run' : evaluateHOLFiniteState (callEntryStateHOLFinite st (HolFiniteMapExact.empty.update (ofString "n", .val (.word (2#64 * n0)))))
          (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := ha_run
      rw [ha_run'] at hdec
      cases ra with
      | none => simp at hdec
      | some ra' =>
        cases ra' with
        | returned rva =>
          obtain ⟨rfl, hsa_g, hsa_mem, hp_add_le_q, hq_le_cMax, _⟩ :=
            evaluate_alloc_body_general ent_a hpw (2#64 * n0) hst_code hp_le_cMax hhp_lk hent_n rva (by rw [ha_run])
          rw [ha_run] at hsa_g hsa_mem; dsimp only at hsa_g hsa_mem
          have hsa_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_a (sourceFnBody Guest.Software.guestFn_alloc)
          rw [ha_run] at hsa_meta; dsimp only at hsa_meta
          have hsh_a : (shapeEqHOL (shapeOfHOLExact (.val (.word hpw) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word hpw) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only at hdec; rw [if_pos hsh_a] at hdec
          let q := (hpw + (2#64 * n0 + 7)) &&& ((0 : BitVec 64) - 8)
          let st1 := setVarHOLFinite (ofString nbName) (.val (.word hpw)) { sa with locals := st.locals }
          have hst1_code : st1.code = originalRuntimeCode := hsa_meta.1.trans hst_code
          have hst1_ma : st1.memaddrs = st.memaddrs := hsa_meta.2.1
          have hst1_ma_ord : st1.memaddrs = ordinaryDomain := hst1_ma.trans hst_AR.1.memaddrs
          obtain ⟨kv, hkv_ev, hn0_ev, _⟩ := hex_after st1 hpw q hst1_ma rfl hsa_g
          have hnb_ev : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
              (.var .local (ofString nbName)) = some (.val (.word hpw)) := by
            simp [st1, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [evaluateHOLFiniteState_seq_line780] at hdec
          have hktn_meta := (PanRunBounded.evaluateHOLFiniteState_metadata st1
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [keyExp, nExp, .var .local (ofString nbName)])).2.1
          rcases hktn : evaluateHOLFiniteState st1
              (.call (some (none, none)) (ofString "key_to_nibbles")
                [keyExp, nExp, .var .local (ofString nbName)]) with ⟨rk, sk⟩
          rw [hktn] at hdec hktn_meta
          cases rk with
          | some rk' =>
            dsimp only at hdec
            injection hdec with hrk _
            exact False.elim (call_void_no_returned st1 (ofString "key_to_nibbles")
              [keyExp, nExp, .var .local (ofString nbName)] v (by rw [hktn]; exact hrk))
          | none =>
            dsimp only at hdec
            obtain ⟨hsk_g, hsk_loc, h2n_dom, hsk_nib⟩ :=
              eval_call_key_to_nibbles_returned st1 keyExp nExp (.var .local (ofString nbName))
                kv n0 hpw hst1_code hst1_ma_ord (by omega) hkv_ev hn0_ev hnb_ev sk hktn
            have h2n_lt : 2 * n0.toNat < 2 ^ 64 := by
              have : (33806089704 : Nat) < 2 ^ 64 := by decide
              omega
            have hl_nat : (2#64 * n0).toNat = 2 * n0.toNat := by
              rw [BitVec.toNat_mul, show (2#64 : BitVec 64).toNat = 2 from rfl, Nat.mod_eq_of_lt h2n_lt]
            have hsk_ma : sk.memaddrs = st.memaddrs := hktn_meta.trans hst1_ma
            obtain ⟨_, hn0_sk_ev, hsz_sk_ev⟩ := hex_after sk hpw q hsk_ma hsk_loc (hsk_g.trans hsa_g)
            have hnb_sk_lk : sk.locals.lookup (ofString nbName) = some (.val (.word hpw)) := by
              rw [hsk_loc]
              simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_return] at hdec
            have hev_ret : @evalHOLExact 64 F _ sk.toExact (fun a => Classical.propDecidable (sk.memaddrs a))
                (.rstruct [.var .local (ofString nbName), szExp]) =
                some (.rStruct [.val (.word hpw), .val (.word (2#64 * n0))]) := by
              simp [evalHOLExact, evalListHOLExact, hnb_sk_lk, hsz_sk_ev]
            rw [hev_ret] at hdec; dsimp only at hdec
            have hsz_ok : sizeOfShapeWithContextHOL sk.structs
                (shapeOfHOLExact (.rStruct [.val (.word hpw), .val (.word (2#64 * n0))] : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            rw [if_pos hsz_ok] at hdec; dsimp only at hdec
            injection hdec with hv_eq hpost_eq
            injection hv_eq with hv_eq'
            injection hv_eq' with hv_eq''
            have hpost_mem : post.memory = sk.memory := by rw [← hpost_eq]; rfl
            have hpost_be : post.be = sk.be := by rw [← hpost_eq]; rfl
            have hpost_g : post.globals = st.globals.update (ofString "heap_ptr", .val (.word q)) := by
              rw [← hpost_eq]; dsimp only [emptyLocalsHOLFinite]; exact hsk_g.trans hsa_g
            have hpost_hp : globN post "heap_ptr" = q.toNat := by
              simp [globN, hpost_g, HolFiniteMapExact.lookup_update, FUPDATE]
            refine ⟨hpw, 2#64 * n0, hv_eq''.symm, rfl, hl_nat, ?_, ?_⟩
            · rw [hl_nat]
              intro k hk
              have hmk := hsk_nib k hk
              unfold memB at hmk ⊢
              rw [hpost_mem, hpost_be]
              exact hmk
            · unfold Inside
              rw [← hst_hp, ← hhp_eq, hpost_hp]
              exact ⟨Nat.le_refl _, hp_add_le_q⟩
        | _ => simp at hdec
  -- Now split on `ite` branch in `mpt_nibble_key`:
  rw [hb, evaluateHOLFiniteState_seq_line780] at hr_pair
  rcases hite : evaluateHOLFiniteState s
      (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64))
        (.seq
          (.call (some (none, none)) (ofString "keccak256")
            [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
          (.decCall (ofString "nb") .one (ofString "alloc") [.const 64#64]
            (.seq
              (.call (some (none, none)) (ofString "key_to_nibbles")
                [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")])
              (.return (.rstruct [.var .local (ofString "nb"), .const 64#64])))))
        .skip) with ⟨r_ite, s_ite⟩
  rw [hite] at hr_pair
  cases r_ite with
  | some r_i =>
    dsimp only at hr_pair
    injection hr_pair with hr_eq hpost_eq
    injection hr_eq with hr_eq'
    subst hr_eq'
    rw [evaluateHOLFiniteState_ite] at hite
    split at hite
    · split at hite
      · rw [evaluateHOLFiniteState_skip] at hite; cases hite
      · rw [evaluateHOLFiniteState_seq_line780] at hite
        have hskc_meta := PanRunBounded.evaluateHOLFiniteState_metadata s
          (.call (some (none, none)) (ofString "keccak256")
            [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
        rcases hkc : evaluateHOLFiniteState s
            (.call (some (none, none)) (ofString "keccak256")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]) with ⟨rkc, skc⟩
        rw [hkc] at hite hskc_meta
        cases rkc with
        | some rkc' =>
          dsimp only at hite
          injection hite with hbad _
          exact False.elim (call_void_no_returned s (ofString "keccak256")
            [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]
            v (by rw [hkc]; exact hbad))
        | none =>
          dsimp only at hite
          have hskc_g : skc.globals = s.globals := by
            have hg := call_keccak256_globals s hcode
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]
            rw [hkc] at hg; exact hg
          have hskc_code : skc.code = originalRuntimeCode := hskc_meta.1.trans hcode
          have hskc_AR : ArenaReady skc := by
            have hge := guestInv_evaluate s
              (.call (some (none, none)) (ofString "keccak256")
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")])
              hAR.1
            rw [hkc] at hge
            have hok : ArenaOK { s with globals := skc.globals } := by
              rw [hskc_g]; exact hAR.2
            exact ⟨hge, hok⟩
          have hmhs_word : ∃ mhsw : BitVec 64, s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word mhsw)) := by
            rw [evaluateHOLFiniteState_call] at hkc
            rcases hargs_kc : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")] with _ | vs_kc
            · rw [hargs_kc] at hkc; simp at hkc
            · rw [hargs_kc] at hkc; dsimp only at hkc
              rcases hlk_kc : lookupCodeHOLFinite s.code.lookup (ofString "keccak256") vs_kc with _ | ⟨bkc, ckc, rskc⟩
              · rw [hlk_kc] at hkc; simp at hkc
              · rw [evalListHOLFinite_eq_toExact] at hargs_kc
                simp only [evalListHOLExact, evalHOLExact] at hargs_kc
                rcases hkey0 : s.locals.lookup (ofString "key") with _ | kv0
                · simp [hkey0] at hargs_kc
                · rcases hklen0 : s.locals.lookup (ofString "klen") with _ | klv0
                  · simp [hkey0, hklen0] at hargs_kc
                  · rcases hg_mhs : s.globals.lookup (ofString "mpt_hash_scratch") with _ | mhsv0
                    · simp [hkey0, hklen0, hg_mhs] at hargs_kc
                    · simp only [hkey0, hklen0, hg_mhs, Option.some.injEq] at hargs_kc
                      subst hargs_kc
                      rcases mhsv0 with ⟨⟨mhsw⟩⟩ | fs | ⟨nm, fs⟩
                      · exact ⟨mhsw, rfl⟩
                      · exfalso
                        rw [hcode] at hlk_kc
                        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlk_kc
                        have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "keccak256")
                            [kv0, klv0, .rStruct fs] = none := by
                          have hlk_keccak : originalRuntimeCode.lookup (ofString "keccak256") =
                              some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
                                sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
                            lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
                              (extractFn Guest.Software.guestFn_keccak256) rfl
                          simp [lookupCodeHOLExact, hlk_keccak, shapeOfHOLExact, shapeEqHOL]
                        split at hlk_kc
                        · simp at hlk_kc
                        · rename_i _ _ _ hrw; rw [hraw] at hrw; cases hrw
                      · exfalso
                        rw [hcode] at hlk_kc
                        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlk_kc
                        have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "keccak256")
                            [kv0, klv0, .nStruct nm fs] = none := by
                          have hlk_keccak : originalRuntimeCode.lookup (ofString "keccak256") =
                              some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
                                sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
                            lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
                              (extractFn Guest.Software.guestFn_keccak256) rfl
                          simp [lookupCodeHOLExact, hlk_keccak, shapeOfHOLExact, shapeEqHOL]
                        split at hlk_kc
                        · simp at hlk_kc
                        · rename_i _ _ _ hrw; rw [hraw] at hrw; cases hrw
          obtain ⟨mhsw, hmhs_lk⟩ := hmhs_word
          rw [hpost_eq] at hite
          obtain ⟨p, l, rfl, rfl, hl_nat, hnib, hin⟩ :=
            run_alloc_ktn skc "nb" (.const 64#64) (.var .global (ofString "mpt_hash_scratch")) (.const 32#64) 32#64
              hskc_code hskc_AR (by simp [globN, hskc_g]) rfl
              (fun st' p' q' _ _ hst'_g => by
                refine ⟨mhsw, ?_, rfl, rfl⟩
                simp [evalHOLExact, hst'_g, HolFiniteMapExact.lookup_update, FUPDATE, hskc_g, hmhs_lk,
                  show ofString "heap_ptr" ≠ ofString "mpt_hash_scratch" by decide])
              hite
          exact ⟨p, 2#64 * 32#64, rfl, hnib, fun _ => by decide, hin⟩
    · injection hite with hr1 _; cases hr1
  | none =>
    dsimp only at hr_pair
    have hs_ite_eq : s = s_ite := by
      rw [evaluateHOLFiniteState_ite] at hite
      split at hite
      · split at hite
        · rw [evaluateHOLFiniteState_skip] at hite; exact (Prod.mk.inj hite).2
        · exfalso
          rw [evaluateHOLFiniteState_seq_line780] at hite
          rcases hkc0 : evaluateHOLFiniteState s
              (.call (some (none, none)) (ofString "keccak256")
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]) with ⟨rkc, skc⟩
          rw [hkc0] at hite
          cases rkc with
          | some _ => simp at hite
          | none =>
            exact seq_decCall_return_ne_none skc _ _ _ _ _ _ (congrArg Prod.fst hite)
      · cases hite
    subst hs_ite_eq
    -- Unsecured branch: `decCall "nb2" .one "alloc" [2 * klen] ...`
    -- Extract `key` and `klen` words from `hr_pair`
    have hkl_word : ∃ keyw klenw : BitVec 64,
        s.locals.lookup (ofString "key") = some (.val (.word keyw)) ∧
        s.locals.lookup (ofString "klen") = some (.val (.word klenw)) := by
      rcases hklen : s.locals.lookup (ofString "klen") with _ | klv
      · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr_pair
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hklen] at hr_pair
      · rcases klv with ⟨⟨klenw⟩⟩ | _ | _
        · have hbad_key :
              (∀ sa : PanSemStateFiniteExact 64 F, sa.code = originalRuntimeCode →
                ∀ rva : ValueHOL 64,
                  (evaluateHOLFiniteState (setVarHOLFinite (ofString "nb2") rva { sa with locals := s.locals })
                    (.call (some (none, none)) (ofString "key_to_nibbles")
                      [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])).1 =
                    some .error) → False := by
            intro herr
            rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr_pair
            have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.panop .mul [.const 2#64, .var .local (ofString "klen")]] =
                some [.val (.word (2#64 * klenw))] := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hklen, panOpHOL, valueIsWord, valueWord]
            have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
              (sourceFnBody Guest.Software.guestFn_alloc) (2#64 * klenw) (by rw [hcode]; exact lookup_alloc)
            rw [hargs] at hr_pair; dsimp only at hr_pair; rw [hlk] at hr_pair; dsimp only at hr_pair
            split at hr_pair
            · simp at hr_pair
            · let ent_a0 := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (2#64 * klenw))))
              have hm_a := (PanRunBounded.evaluateHOLFiniteState_metadata ent_a0 (sourceFnBody Guest.Software.guestFn_alloc)).1
              rcases ha_r : evaluateHOLFiniteState ent_a0 (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
              have ha_r' : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (2#64 * klenw)))))
                  (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := ha_r
              rw [ha_r'] at hr_pair
              rw [ha_r] at hm_a
              cases ra with
              | none => simp at hr_pair
              | some ra' =>
                cases ra' <;> dsimp only at hr_pair
                case returned rva =>
                  split at hr_pair
                  · rw [evaluateHOLFiniteState_seq_line780] at hr_pair
                    have he := herr sa (hm_a.trans hcode) rva
                    rcases hk_r : evaluateHOLFiniteState (setVarHOLFinite (ofString "nb2") rva { sa with locals := s.locals })
                        (.call (some (none, none)) (ofString "key_to_nibbles")
                          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")]) with ⟨rk0, sk0⟩
                    rw [hk_r] at he hr_pair
                    dsimp only at he
                    subst he
                    simp at hr_pair
                  · simp at hr_pair
                all_goals simp at hr_pair
          rcases hkey : s.locals.lookup (ofString "key") with _ | kv
          · exfalso
            apply hbad_key
            intro sa _ rva
            let st1 := setVarHOLFinite (ofString "nb2") rva { sa with locals := s.locals }
            change (evaluateHOLFiniteState st1
              (.call (some (none, none)) (ofString "key_to_nibbles")
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])).1 = some .error
            rw [evaluateHOLFiniteState_call]
            have hargs_none : evalListHOLFinite st1 (h := fun a => Classical.propDecidable (st1.memaddrs a))
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")] = none := by
              simp [st1, evalListHOLFinite, evalListHOLExact, evalHOLExact, setVarHOLFinite,
                HolFiniteMapExact.lookup_update, FUPDATE, hkey, show ofString "nb2" ≠ ofString "key" by decide]
            rw [hargs_none]
          · rcases kv with ⟨⟨keyw⟩⟩ | fs | ⟨nm, fs⟩
            · exact ⟨keyw, klenw, rfl, rfl⟩
            · exfalso
              apply hbad_key
              intro sa hsa_c rva
              let st1 := setVarHOLFinite (ofString "nb2") rva { sa with locals := s.locals }
              change (evaluateHOLFiniteState st1
                (.call (some (none, none)) (ofString "key_to_nibbles")
                  [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])).1 = some .error
              rw [evaluateHOLFiniteState_call]
              have hargs_k : evalListHOLFinite st1 (h := fun a => Classical.propDecidable (st1.memaddrs a))
                  [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")] =
                  some [.rStruct fs, .val (.word klenw), rva] := by
                simp [st1, evalListHOLFinite, evalListHOLExact, evalHOLExact, setVarHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE, hkey, hklen,
                  show ofString "nb2" ≠ ofString "key" by decide,
                  show ofString "nb2" ≠ ofString "klen" by decide]
              have hnone_k : PanSemStateFiniteExact.lookupCodeHOLFinite st1.code.lookup (ofString "key_to_nibbles")
                  [.rStruct fs, .val (.word klenw), rva] = none := by
                change PanSemStateFiniteExact.lookupCodeHOLFinite sa.code.lookup _ _ = none
                rw [hsa_c]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "key_to_nibbles")
                    [.rStruct fs, .val (.word klenw), rva] = none := by
                  simp [lookupCodeHOLExact, lookup_key_to_nibbles, shapeOfHOLExact, shapeEqHOL]
                split
                · rfl
                · rename_i _ _ _ hrw; rw [hraw] at hrw; cases hrw
              rw [hargs_k]; dsimp only; rw [hnone_k]
            · exfalso
              apply hbad_key
              intro sa hsa_c rva
              let st1 := setVarHOLFinite (ofString "nb2") rva { sa with locals := s.locals }
              change (evaluateHOLFiniteState st1
                (.call (some (none, none)) (ofString "key_to_nibbles")
                  [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])).1 = some .error
              rw [evaluateHOLFiniteState_call]
              have hargs_k : evalListHOLFinite st1 (h := fun a => Classical.propDecidable (st1.memaddrs a))
                  [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")] =
                  some [.nStruct nm fs, .val (.word klenw), rva] := by
                simp [st1, evalListHOLFinite, evalListHOLExact, evalHOLExact, setVarHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE, hkey, hklen,
                  show ofString "nb2" ≠ ofString "key" by decide,
                  show ofString "nb2" ≠ ofString "klen" by decide]
              have hnone_k : PanSemStateFiniteExact.lookupCodeHOLFinite st1.code.lookup (ofString "key_to_nibbles")
                  [.nStruct nm fs, .val (.word klenw), rva] = none := by
                change PanSemStateFiniteExact.lookupCodeHOLFinite sa.code.lookup _ _ = none
                rw [hsa_c]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
                have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "key_to_nibbles")
                    [.nStruct nm fs, .val (.word klenw), rva] = none := by
                  simp [lookupCodeHOLExact, lookup_key_to_nibbles, shapeOfHOLExact, shapeEqHOL]
                split
                · rfl
                · rename_i _ _ _ hrw; rw [hraw] at hrw; cases hrw
              rw [hargs_k]; dsimp only; rw [hnone_k]
        · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr_pair
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hklen, panOpHOL, valueIsWord] at hr_pair
        · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr_pair
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hklen, panOpHOL, valueIsWord] at hr_pair
    obtain ⟨keyw, klenw, hkey_lk, hklen_lk⟩ := hkl_word
    have hklen_loc : locN s "klen" = klenw.toNat := by simp [locN, hklen_lk]
    obtain ⟨p, l, rfl, rfl, hl_nat, hnib, hin⟩ :=
      run_alloc_ktn s "nb2"
        (.panop .mul [.const 2#64, .var .local (ofString "klen")])
        (.var .local (ofString "key"))
        (.var .local (ofString "klen"))
        klenw hcode hAR rfl
        (by simp [evalHOLExact, evalListHOLExact, hklen_lk, panOpHOL, valueIsWord, valueWord])
        (fun st' p' q' _ hst'_loc _ => by
          refine ⟨keyw, ?_, ?_, ?_⟩
          · simp [evalHOLExact, hst'_loc, HolFiniteMapExact.lookup_update, FUPDATE, hkey_lk,
              show ofString "nb2" ≠ ofString "key" by decide]
          · simp [evalHOLExact, hst'_loc, HolFiniteMapExact.lookup_update, FUPDATE, hklen_lk,
              show ofString "nb2" ≠ ofString "klen" by decide]
          · simp [evalHOLExact, evalListHOLExact, hst'_loc, HolFiniteMapExact.lookup_update, FUPDATE, hklen_lk,
              panOpHOL, valueIsWord, valueWord, show ofString "nb2" ≠ ofString "klen" by decide])
        hr_pair
    exact ⟨p, 2#64 * klenw, rfl, hnib, fun hle32 => by rw [hl_nat]; rw [hklen_loc] at hle32; omega, hin⟩

end InitECandidate.Solver.Wave8GuestInv.R13MptKeepsTwin
