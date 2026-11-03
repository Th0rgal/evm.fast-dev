import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Common

/-! Exact RLP header/bytes/word/list, `st_be64`, `memcpy`, `memzero`, and `keccak256`
`HeapByteEff` combinators for `R16e-WkBlockTxEnc`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Pure RLP length model (`rlpBeLenAux`, `rlpHeaderLenPure`) -/

def rlpBeLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, v => if v = 0 then 0 else 1 + rlpBeLenAux k (v / 256)

def rlpHeaderLenPure (n : Nat) : Nat :=
  if n ≤ 55 then 1 else 1 + rlpBeLenAux 8 n

theorem rlpBeLenAux_le (k v : Nat) : rlpBeLenAux k v ≤ k := by
  induction k generalizing v with
  | zero => simp [rlpBeLenAux]
  | succ k ih =>
    simp only [rlpBeLenAux]
    split
    · omega
    · have := ih (v / 256); omega

theorem rlpHeaderLenPure_bounds (n : Nat) :
    1 ≤ rlpHeaderLenPure n ∧ rlpHeaderLenPure n ≤ 9 := by
  unfold rlpHeaderLenPure
  split
  · omega
  · have := rlpBeLenAux_le 8 n; omega

theorem rlpHeaderLenPure_of_le55 {n : Nat} (h : n ≤ 55) :
    rlpHeaderLenPure n = 1 := by
  simp [rlpHeaderLenPure, h]

/-! ## 2. Exact deterministic evaluation of `rlp_be_len`, `rlp_header_len`, `rlp_list_header_len` -/

theorem lookup_rlp_header_len :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_rlp_header_len, .one) :=
  lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_header_len) rfl

theorem lookup_rlp_encode_bytes :
    originalRuntimeCode.lookup (ofString "rlp_encode_bytes") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_bytes, .one) :=
  lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl

theorem lookup_rlp_encode_word :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst", .one), (ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one) :=
  lookup_of_guestAst_getElem 123 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_word) rfl

theorem lookup_rlp_encode_list_header :
    originalRuntimeCode.lookup (ofString "rlp_encode_list_header") =
      some ([(ofString "dst", .one), (ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_list_header, .one) :=
  lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl

theorem lookup_rlp_list_header_len :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_list_header_len, .one) :=
  lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl

theorem lookup_rlp_finish_list :
    originalRuntimeCode.lookup (ofString "rlp_finish_list") =
      some ([(ofString "dst", .one), (ofString "payload_end", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_finish_list, .one) :=
  lookup_of_guestAst_getElem 833 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_finish_list) rfl

theorem lookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

theorem lookup_st_be32 :
    originalRuntimeCode.lookup (ofString "st_be32") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
  lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be32) rfl

theorem lookup_st_be64 :
    originalRuntimeCode.lookup (ofString "st_be64") =
      some ([(ofString "p", .one), (ofString "v", .one)],
        sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
  lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_st_be64) rfl

private def rlpBeLenLoopP : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
    (.seq
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))

private theorem eval_rlp_be_len_while_exact {F : Type} :
    ∀ (rem : Nat) (s : PanSemStateFiniteExact 64 F) (vw nw : BitVec 64),
      rem = 8 - nw.toNat →
      nw.toNat ≤ 8 →
      vw.toNat < 256 ^ rem →
      s.locals.lookup (ofString "v") = some (.val (.word vw)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      (evaluateHOLFiniteState s rlpBeLenLoopP).1 ≠ some .timeOut →
      (evaluateHOLFiniteState s rlpBeLenLoopP).1 = none ∧
      (evaluateHOLFiniteState s rlpBeLenLoopP).2.locals.lookup (ofString "n") =
        some (.val (.word (BitVec.ofNat 64 (nw.toNat + rlpBeLenAux rem vw.toNat)))) ∧
      M13.LocFrame s (evaluateHOLFiniteState s rlpBeLenLoopP).2 := by
  intro rem
  induction rem with
  | zero =>
    intro s vw nw hrem hn_le hv_lt hv hn _
    have hv0_nat : vw.toNat = 0 := by simp at hv_lt; omega
    have hv0 : vw = 0 := BitVec.eq_of_toNat_eq hv0_nat
    subst hv0
    unfold rlpBeLenLoopP
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) = some (.val (.word 0)) := by
      simp [evalHOLFinite, evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc]; dsimp only
    have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
    rw [if_neg h00]
    simp [rlpBeLenAux, hn, BitVec.ofNat_toNat]
    exact M13.LocFrame.refl s
  | succ rem ih =>
    intro s vw nw hrem hn_le hv_lt hv hn hnt
    unfold rlpBeLenLoopP at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) =
        some (.val (.word (if vw ≠ 0 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hvz : vw = 0
    · subst hvz
      simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hnt ⊢
      have haux0 : rlpBeLenAux (rem + 1) (0 : BitVec 64).toNat = 0 := by simp [rlpBeLenAux]
      rw [haux0, Nat.add_zero, BitVec.ofNat_toNat]
      exact ⟨trivial, hn, M13.LocFrame.refl s⟩
    · have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos hvz, if_pos h10] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        have hvz_nat : vw.toNat ≠ 0 := fun h => hvz (BitVec.eq_of_toNat_eq h)
        have hstep : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
              (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat)))
                (decClockHOLFinite s))) := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hv_d : (decClockHOLFinite s).locals.lookup (ofString "v") = some (.val (.word vw)) := hv
          have hn_d : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word nw)) := hn
          have hne_vn : ofString "v" ≠ ofString "n" := by decide
          simp [evalHOLExact, evalListHOLExact, hv_d, hn_d, hne_vn, Ne.symm hne_vn,
            isValidValueHOLFinite, lookupKvarHOLFinite, shapeOfHOLExact, shapeEqHOL,
            setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            evaluateHOLFiniteState_assign, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hstep] at hnt ⊢; dsimp only at hnt ⊢
        set mid := setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
          (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat)))
            (decClockHOLFinite s))
        have hnw1 : (nw + 1).toNat = nw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (nw.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hv_sh : (vw >>> (8 : BitVec 64).toNat).toNat = vw.toNat / 256 := by
          change vw.toNat >>> 8 = vw.toNat / 256
          rw [Nat.shiftRight_eq_div_pow]
        have hv'_lt : (vw >>> (8 : BitVec 64).toNat).toNat < 256 ^ rem := by
          rw [hv_sh]
          have hp : 256 ^ (rem + 1) = 256 ^ rem * 256 := Nat.pow_succ 256 rem
          rw [hp, Nat.mul_comm] at hv_lt
          exact Nat.div_lt_of_lt_mul hv_lt
        have hmid_v : mid.locals.lookup (ofString "v") =
            some (.val (.word (vw >>> (8 : BitVec 64).toNat))) := by
          have hne : ofString "n" ≠ ofString "v" := by decide
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
        have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word (nw + 1))) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨hnone, hlk_n, hlf_m⟩ := ih mid (vw >>> (8 : BitVec 64).toNat) (nw + 1)
          (by omega) (by omega) hv'_lt hmid_v hmid_n hnt
        unfold rlpBeLenLoopP at hnone hlk_n hlf_m
        have haux_step : nw.toNat + 1 + rlpBeLenAux rem (vw.toNat / 256) =
            nw.toNat + rlpBeLenAux (rem + 1) vw.toNat := by
          simp [rlpBeLenAux, hvz_nat]; omega
        rw [hnw1, hv_sh, haux_step] at hlk_n
        have hlf0 : M13.LocFrame s mid := by cases s; rfl
        exact ⟨hnone, hlk_n, hlf0.trans hlf_m⟩

theorem eval_rlp_be_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vw : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (rlpBeLenAux 8 vw.toNat))))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_be_len =
      .dec (ofString "n") .one (.const 0)
        (.seq rlpBeLenLoopP (.return (.var .local (ofString "n")))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "n") (.val (.word 0)) s
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    have hne : ofString "n" ≠ ofString "v" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hv]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hv_lt : vw.toNat < 256 ^ 8 := by
    have h256 : (256 ^ 8 : Nat) = 2 ^ 64 := by decide
    rw [h256]; exact vw.isLt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hl : evaluateHOLFiniteState s1 rlpBeLenLoopP with ⟨rl, sl⟩
  have hnt_l : rl ≠ some .timeOut := by
    rintro rfl; rw [hl] at hnt; exact hnt rfl
  obtain ⟨hnone, hsl_n, hlf_l⟩ := eval_rlp_be_len_while_exact 8 s1 vw 0
    rfl (by decide) hv_lt hs1_v hs1_n (by rw [hl]; exact hnt_l)
  rw [hl] at hnone hsl_n hlf_l
  dsimp only at hnone hsl_n hlf_l
  subst hnone
  have hsl_n' : sl.locals.lookup (ofString "n") =
      some (.val (.word (BitVec.ofNat 64 (rlpBeLenAux 8 vw.toNat)))) := by
    simpa using hsl_n
  dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev_n : @evalHOLExact 64 F _ sl.toExact
      (fun a => Classical.propDecidable (sl.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word (BitVec.ofNat 64 (rlpBeLenAux 8 vw.toNat)))) := hsl_n'
  rw [hev_n]; dsimp only
  have hsz : sizeOfShapeWithContextHOL sl.structs
      (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpBeLenAux 8 vw.toNat))) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  have hlf0 : M13.LocFrame s s1 := by cases s; rfl
  exact ⟨rfl, ((hlf0.trans hlf_l).emptyLocals).locals _⟩

theorem eval_rlp_header_len_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 ≠
      some .timeOut) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat))))) ∧
    M13.LocFrame s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2 := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.return (.const 1))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if nw.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hn55 : nw.toNat ≤ 55
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_pos hn55, if_neg h10, evaluateHOLFiniteState_return]
    have hc1 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) (.const 1#64) =
        some (.val (.word 1#64)) := rfl
    dsimp only [OfNat.ofNat, BitVec.ofNat] at hc1 ⊢
    rw [hc1]; simp [shapeOfHOLExact, rlpHeaderLenPure, hn55]
    exact (M13.LocFrame.refl s).emptyLocals
  · rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
    have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
      (sourceFnBody Guest.Software.guestFn_rlp_be_len) nw (by rw [hcode]; exact M11.lookup_rlp_be_len)
    simp only [ha, hlk] at hnt ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · simp only [hcz, ↓reduceIte] at hnt ⊢
      set cmap := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word nw))
      set ent := callEntryStateHOLFinite s cmap
      have hent_v : ent.locals.lookup (ofString "v") = some (.val (.word nw)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨rbl, sbl⟩
      have hnt_bl : rbl ≠ some .timeOut := by
        rintro rfl; rw [hbl] at hnt; exact hnt rfl
      obtain ⟨hr_bl, hlf_bl⟩ := eval_rlp_be_len_body_exact ent nw hent_v (by rw [hbl]; exact hnt_bl)
      rw [hbl] at hr_bl hlf_bl
      dsimp only at hr_bl hlf_bl
      subst hr_bl
      set ll := BitVec.ofNat 64 (rlpBeLenAux 8 nw.toNat)
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hbl, hsh, ↓reduceIte]
      set mid := setVarHOLFinite (ofString "ll") (.val (.word ll)) { sbl with locals := s.locals }
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [evaluateHOLFiniteState_return]
      have hev_ret : @evalHOLExact 64 F _ mid.toExact
          (fun a => Classical.propDecidable (mid.memaddrs a))
          (.op .add [.const 1, .var .local (ofString "ll")]) =
          some (.val (.word (1 + ll))) := by
        simp [evalHOLExact, evalListHOLExact, hmid_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hev_ret]; dsimp only
      have hsz : sizeOfShapeWithContextHOL mid.structs
          (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]; dsimp only
      have h1ll : 1 + ll = BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat) := by
        have hb8 := rlpBeLenAux_le 8 nw.toNat
        apply BitVec.eq_of_toNat_eq
        change (1 + ll).toNat = (BitVec.ofNat 64 (rlpHeaderLenPure nw.toNat)).toNat
        rw [BitVec.toNat_add]
        have h1_nat : (1 : BitVec 64).toNat = 1 := by decide
        have hll_nat : ll.toNat = rlpBeLenAux 8 nw.toNat := by
          dsimp [ll]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        rw [h1_nat, hll_nat, BitVec.toNat_ofNat]
        simp only [rlpHeaderLenPure, hn55, ↓reduceIte]
      rw [h1ll]
      have hlf_ent : M13.LocFrame s ent := by cases s; rfl
      exact ⟨rfl, ((((hlf_ent.trans hlf_bl).locals _).setVar _ _).emptyLocals).locals _⟩

theorem eval_decCall_rlp_list_header_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (pExp : ExpHOL 64) (pw : BitVec 64)
    (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [pExp] cont)).1 ≠
      some .timeOut) :
    let hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      hl.toNat = rlpHeaderLenPure pw.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_list_header_len") [pExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro hl
  have hb_lhl : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp] =
      some [.val (.word pw)] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_list_header_len") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_list_header_len) pw
    (by rw [hcode]; exact lookup_rlp_list_header_len)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "payload_len", ValueHOL.val (.word pw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_p : ent.locals.lookup (ofString "payload_len") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hb_lhl, evaluateHOLFiniteState_call] at hnt ⊢
    have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "payload_len")] = some [.val (.word pw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_p]
    have hlk2 := pan_one_word_lookup ent.code.lookup (ofString "rlp_header_len") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_header_len) pw
      (by change s.code.lookup _ = _; rw [hcode]; exact lookup_rlp_header_len)
    simp only [ha2, hlk2] at hnt ⊢
    by_cases hcz2 : ent.clock = 0
    · simp [hcz2] at hnt
    · simp only [hcz2, ↓reduceIte] at hnt ⊢
      set cmap2 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word pw))
      set ent2 := callEntryStateHOLFinite ent cmap2
      have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word pw)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hhl : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rhl, shl⟩
      have hnt_hl : rhl ≠ some .timeOut := by
        rintro rfl; rw [hhl] at hnt; exact hnt rfl
      obtain ⟨hr_hl, hlf_hl⟩ := eval_rlp_header_len_body_exact ent2 pw hcode hent2_n (by rw [hhl]; exact hnt_hl)
      rw [hhl] at hr_hl hlf_hl
      dsimp only at hr_hl hlf_hl
      subst hr_hl
      have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat))) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hhl] at hnt ⊢
      rw [if_pos hsh1] at hnt ⊢
      dsimp only at hnt ⊢
      rw [if_pos hsh2] at hnt ⊢
      let mid := setVarHOLFinite (ofString lname) (.val (.word hl)) { shl.emptyLocalsHOLFinite with locals := s.locals }
      have hlf_all : M13.LocFrame s mid := by
        have h1 : M13.LocFrame s ent2 := by cases s; rfl
        exact (((h1.trans hlf_hl).emptyLocals).locals _).setVar _ _
      have hbnd := rlpHeaderLenPure_bounds pw.toNat
      have hhl_nat : hl.toNat = rlpHeaderLenPure pw.toNat := by
        dsimp [hl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      exact ⟨mid, hhl_nat, by omega, by omega, hlf_all.globals, hlf_all.memory, rfl,
        HeapByteEff.of_locFrame hAR hlf_all Rl gw, hnt, rfl⟩

/-! ## 3. Exact `rlp_write_header` & `rlp_encode_list_header` & `rlp_encode_word` & `rlp_encode_bytes` -/

private theorem storeByte_only_none_or_error {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

private theorem storeByte_local_dst_lt_heapEnd {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst0 : BitVec 64) (val : ExpHOL 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hdst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hnone : (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none) :
    dst0.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  simp only [evalHOLExact, hdst] at hnone
  split at hnone
  · split at hnone
    · rename_i m' hst
      unfold panMemStoreByteWord8HOL at hst; dsimp only at hst
      cases hm : t.memory (panByteAlignHOL dst0) with
      | word cell =>
        by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
        · exact (M11.byteAlign_lt_heapEnd hma dst0 hdom).2
        · simp [hm, hdom] at hst
    · simp at hnone
  · simp at hnone

theorem eval_rlp_write_header_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 base0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hbase : s.locals.lookup (ofString "base") = some (.val (.word base0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)
    let hl := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
    (∀ rv, out.1 = some (.returned rv) →
      rv = .val (.word hl) ∧ dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_write_header =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]))
            (.return (.const 1)))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.seq
            (.storeByte (.var .local (ofString "dst"))
              (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]))
            (.seq
              (.call (some (none, none)) (ofString "rlp_put_be")
                [.op .add [.var .local (ofString "dst"), .const 1],
                 .var .local (ofString "n"),
                 .var .local (ofString "ll")])
              (.return (.op .add [.const 1, .var .local (ofString "ll")]))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hn55 : n0.toNat ≤ 55
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_pos hn55, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases storeByte_only_none_or_error s (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .var .local (ofString "n")]) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hnt ⊢
      have hdst_lt_he := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        rw [rlpHeaderLenPure_of_le55 hn55] at h2
        exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        subst hrv''
        simp only [rlpHeaderLenPure_of_le55 hn55]
        exact ⟨rfl, hdst_lt_he, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
      injection hr with hr'; subst hr'; exact not_resumes_error
  · rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
    have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "n")] = some [.val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
      (sourceFnBody Guest.Software.guestFn_rlp_be_len) n0 (by rw [hcode]; exact M11.lookup_rlp_be_len)
    simp only [ha, hlk] at hnt ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · simp only [hcz, ↓reduceIte] at hnt ⊢
      set cmap := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word n0))
      set ent := callEntryStateHOLFinite s cmap
      have hent_v : ent.locals.lookup (ofString "v") = some (.val (.word n0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hbl : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨rbl, sbl⟩
      have hnt_bl : rbl ≠ some .timeOut := by
        rintro rfl; rw [hbl] at hnt; exact hnt rfl
      obtain ⟨hr_bl, hlf_bl⟩ := eval_rlp_be_len_body_exact ent n0 hent_v (by rw [hbl]; exact hnt_bl)
      rw [hbl] at hr_bl hlf_bl
      dsimp only at hr_bl hlf_bl
      subst hr_bl
      set ll := BitVec.ofNat 64 (rlpBeLenAux 8 n0.toNat)
      have hll_le8 : ll.toNat ≤ 8 := by
        have := rlpBeLenAux_le 8 n0.toNat
        dsimp [ll]; rw [BitVec.toNat_ofNat]; omega
      have hll_eq : ll.toNat = rlpBeLenAux 8 n0.toNat := by
        have := rlpBeLenAux_le 8 n0.toNat
        dsimp [ll]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have hhl_eq : rlpHeaderLenPure n0.toNat = 1 + ll.toNat := by
        simp [rlpHeaderLenPure, hn55, hll_eq]
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hbl, hsh, ↓reduceIte] at hnt ⊢
      set mid := setVarHOLFinite (ofString "ll") (.val (.word ll)) { sbl with locals := s.locals }
      have hlf_mid : M13.LocFrame s mid := by
        have h1 : M13.LocFrame s ent := by cases s; rfl
        exact ((h1.trans hlf_bl).locals _).setVar _ _
      have hmid_code : mid.code = originalRuntimeCode := hlf_mid.code.trans hcode
      have hmid_ma : mid.memaddrs = ordinaryDomain := by
        have hm : mid.memaddrs = s.memaddrs := by unfold M13.LocFrame at hlf_mid; rw [hlf_mid]
        exact hm.trans hma
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
          show ofString "ll" ≠ ofString "dst" by decide]
      have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
          show ofString "ll" ≠ ofString "n" by decide]
      have heff_s_mid : M11.ByteRegionEffect s mid Rl := by
        have hm := hlf_mid
        unfold M13.LocFrame at hm; rw [hm]
        exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock _ _
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
      simp only [hsb] at hnt ⊢
      rcases storeByte_only_none_or_error mid (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")]) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hnt ⊢
        have hdst_lt_he := storeByte_local_dst_lt_heapEnd mid dst0 _ hmid_ma hmid_dst (by rw [hsb])
        obtain ⟨heff_hdr, hs2_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, h1, by omega⟩)
        have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
        have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hs2_loc]; exact hmid_dst
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by
          rw [hs2_loc]; exact hmid_n
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs2_loc]; exact hmid_ll
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
          have hhe := hdst_lt_he; rw [heapEnd_val] at hhe
          rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
          have hhe := hdst_lt_he; rw [heapEnd_val] at hhe; omega
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hc_put : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .var .local (ofString "n"),
             .var .local (ofString "ll")]) with ⟨rc, s3⟩
        have hnt_put : rc ≠ some .timeOut := by
          rintro rfl; rw [hc_put] at hnt; exact hnt rfl
        have hput := M11.eval_call_rlp_put_be s2
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.var .local (ofString "n"))
          (.var .local (ofString "ll"))
          (dst0 + 1) n0 ll Rl hs2_code
          (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by simp [evalHOLExact, hs2_n])
          (by simp [evalHOLExact, hs2_ll])
          hfit
          (fun _ => by
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat, hhl_eq] at *; omega⟩)
          (by rw [hc_put]; exact hnt_put)
        dsimp only at hput
        rw [hc_put] at hput
        simp only [hc_put] at hnt ⊢
        cases rc with
        | some r =>
          dsimp only
          have hnr := hput.2 (by simp)
          refine ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)), fun r' hr' _ => ?_⟩
          injection hr' with hr''; subst hr''; exact hnr
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
          have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
            rw [hs3_loc]; exact hs2_ll
          rw [evaluateHOLFiniteState_return]
          have hev_ret : @evalHOLExact 64 F _ s3.toExact
              (fun a => Classical.propDecidable (s3.memaddrs a))
              (.op .add [.const 1, .var .local (ofString "ll")]) =
              some (.val (.word (1 + ll))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret]; dsimp only
          have hsz : sizeOfShapeWithContextHOL s3.structs
              (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz]; dsimp only
          have h1ll_eq : 1 + ll = BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, hhl_eq, BitVec.toNat_ofNat]
            change (1 + ll.toNat) % 2 ^ 64 = (1 + ll.toNat) % 2 ^ 64; rfl
          refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
          · injection hrv with hrv'; injection hrv' with hrv''
            rw [← hrv'', h1ll_eq]
            exact ⟨rfl, hdst_lt_he,
              (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
          · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
      · rw [hsb] at hse; dsimp only at hse; subst hse
        refine ⟨fun _ h => by simp at h, fun r hr _ => ?_⟩
        injection hr with hr'; subst hr'; exact not_resumes_error

theorem eval_call_rlp_encode_list_header {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp pExp : ExpHOL 64)
    (dst0 pw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure pw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, pExp])).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_encode_list_header") [dstExp, pExp])
    (out.1 = none → dst0.toNat < heapEnd ∧ HeapByteEff s out.2 Rl gw ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  have hb_elh : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
      .call none (ofString "rlp_write_header")
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pExp] = some [.val (.word dst0), .val (.word pw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hp]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 pw (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_list_header)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_len", ValueHOL.val (.word pw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_len" ≠ ofString "dst" by decide]
    have hent_p : ent.locals.lookup (ofString "payload_len") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hb_elh, evaluateHOLFiniteState_call] at hnt ⊢
    have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] =
        some [.val (.word dst0), .val (.word 192), .val (.word pw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_p]
    have hlk2 := pan_three_word_lookup ent.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 192 pw
      (by decide) (by decide) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact M11.lookup_rlp_write_header)
    simp only [ha2, hlk2] at hnt ⊢
    by_cases hcz2 : ent.clock = 0
    · simp [hcz2] at hnt
    · simp only [hcz2, ↓reduceIte] at hnt ⊢
      set cmap2 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 192))).update (ofString "n", ValueHOL.val (.word pw))
      set ent2 := callEntryStateHOLFinite ent cmap2
      have hent2_dst : ent2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent2_base : ent2.locals.lookup (ofString "base") = some (.val (.word 192)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word pw)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hwh : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; rw [hwh] at hnt; exact hnt rfl
      obtain ⟨hret, hnonret⟩ := eval_rlp_write_header_body_exact ent2 dst0 192 pw Rl
        hcode hAR.1.memaddrs hent2_dst hent2_base hent2_n hin_ivl (by rw [hwh]; exact hnt_wh)
      rw [hwh] at hret hnonret
      dsimp only at hret hnonret
      simp only [hwh] at hnt ⊢
      cases rwh with
      | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          exact ⟨fun h => by simp at h, fun _ => hnonret (.exception eid ev) rfl (fun _ h => by cases h)⟩
        | returned rv =>
          obtain ⟨rfl, hdst_lt_he, heff_wh⟩ := hret rv rfl
          set hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
          have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only; rw [if_pos hsh]; dsimp only; rw [if_pos hsh]; dsimp only
          have heff0 : M11.ByteRegionEffect s ent2 Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent2.locals ent2.clock
          have heff_tot : M11.ByteRegionEffect s { swh.emptyLocalsHOLFinite with locals := s.locals } Rl :=
            ((heff0.trans heff_wh).with_locals_clock _ _).with_locals_clock _ _
          exact ⟨fun _ => ⟨hdst_lt_he, HeapByteEff.of_m11_bre hAR heff_tot, rfl⟩,
            fun h => False.elim (h rfl)⟩
        | «break» | «continue» | error =>
          exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
        | finalFfi _ =>
          exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem eval_decCall_rlp_encode_list_header {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp pExp : ExpHOL 64)
    (dst0 pw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + rlpHeaderLenPure pw.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)).1) :
    let hl := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
    ∃ mid : PanSemStateFiniteExact 64 F,
      hl.toNat = rlpHeaderLenPure pw.toNat ∧
      1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hl)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_list_header") [dstExp, pExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro hl
  have hb_elh : sourceFnBody Guest.Software.guestFn_rlp_encode_list_header =
      .call none (ofString "rlp_write_header")
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pExp] = some [.val (.word dst0), .val (.word pw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hp]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_list_header")
    (ofString "dst") (ofString "payload_len")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_list_header) dst0 pw (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_list_header)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_len", ValueHOL.val (.word pw))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_len" ≠ ofString "dst" by decide]
    have hent_p : ent.locals.lookup (ofString "payload_len") = some (.val (.word pw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rw [hb_elh, evaluateHOLFiniteState_call] at hnt hres ⊢
    have ha2 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
        [.var .local (ofString "dst"), .const 192, .var .local (ofString "payload_len")] =
        some [.val (.word dst0), .val (.word 192), .val (.word pw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hent_dst, hent_p]
    have hlk2 := pan_three_word_lookup ent.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 192 pw
      (by decide) (by decide) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact M11.lookup_rlp_write_header)
    simp only [ha2, hlk2] at hnt hres ⊢
    by_cases hcz2 : ent.clock = 0
    · simp [hcz2] at hnt
    · simp only [hcz2, ↓reduceIte] at hnt hres ⊢
      set cmap2 := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 192))).update (ofString "n", ValueHOL.val (.word pw))
      set ent2 := callEntryStateHOLFinite ent cmap2
      have hent2_dst : ent2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent2_base : ent2.locals.lookup (ofString "base") = some (.val (.word 192)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent2_n : ent2.locals.lookup (ofString "n") = some (.val (.word pw)) := by
        simp [ent2, cmap2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hwh : evaluateHOLFiniteState ent2 (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; rw [hwh] at hnt; exact hnt rfl
      obtain ⟨hret, hnonret⟩ := eval_rlp_write_header_body_exact ent2 dst0 192 pw Rl
        hcode hAR.1.memaddrs hent2_dst hent2_base hent2_n hin_ivl (by rw [hwh]; exact hnt_wh)
      rw [hwh] at hret hnonret
      dsimp only at hret hnonret
      simp only [hwh] at hnt hres ⊢
      cases rwh with
      | none => exact False.elim (not_resumes_error hres)
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hres)
        | returned rv =>
          obtain ⟨rfl, hdst_lt_he, heff_wh⟩ := hret rv rfl
          have hsh1 : shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          have hsh2 : (shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only at hnt hres ⊢
          rw [if_pos hsh1] at hnt hres ⊢
          dsimp only at hnt hres ⊢
          rw [if_pos hsh2] at hnt hres ⊢
          let mid := setVarHOLFinite (ofString lname) (.val (.word hl))
            { swh.emptyLocalsHOLFinite with locals := s.locals }
          have heff0 : M11.ByteRegionEffect s ent2 Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent2.locals ent2.clock
          have heff_mid : M11.ByteRegionEffect s mid Rl :=
            ((heff0.trans heff_wh).with_locals_clock _ _).with_locals_clock mid.locals mid.clock
          have hbnd := rlpHeaderLenPure_bounds pw.toNat
          have hhl_nat : hl.toNat = rlpHeaderLenPure pw.toNat := by
            dsimp [hl]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          exact ⟨mid, hhl_nat, by omega, by omega, hdst_lt_he, heff_mid.globals, rfl,
            HeapByteEff.of_m11_bre hAR heff_mid, hnt, hres, rfl⟩
        | «break» | «continue» | error =>
          exact False.elim (not_resumes_error hres)
        | finalFfi _ =>
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-! ## 4. `rlp_encode_word` & `rlp_encode_bytes` & `rlp_finish_list` combinators -/

theorem eval_rlp_encode_word_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 w0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ len : BitVec 64, rv = .val (.word len) ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 9 ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_word =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
          .skip)
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
            (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) (.return (.const 1)))
            .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
            (.seq
              (.storeByte (.var .local (ofString "dst"))
                (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
      some (.val (.word (if w0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc1] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases hwz : w0 = 0
  · rw [if_pos hwz, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hnt ⊢
    rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.const 128) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only
      have hdst_lt := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
      obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
      refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
      · injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨1, hrv''.symm, by decide, by decide, hdst_lt, heff1.with_locals_clock _ _⟩
      · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
    · rw [hsb] at hse; dsimp only at hse; subst hse
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
  · rw [if_neg hwz, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
    have hc2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
        some (.val (.word (if w0 < 128 then 1 else 0))) := by
      simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc2] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hw128 : w0 < 128
    · rw [if_pos hw128, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hsb : evaluateHOLFiniteState s
          (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
      simp only [hsb] at hnt ⊢
      rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.var .local (ofString "w")) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only
        have hdst_lt := storeByte_local_dst_lt_heapEnd s dst0 _ hma hdst (by rw [hsb])
        obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hdst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
        rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
        refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
        · injection hrv with hrv'; injection hrv' with hrv''
          exact ⟨1, hrv''.symm, by decide, by decide, hdst_lt, heff1.with_locals_clock _ _⟩
        · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
    · rw [if_neg hw128, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
      dsimp only at hnt ⊢
      obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
        M11.eval_decCall_rlp_be_len s "ll" (.var .local (ofString "w")) w0 _ hcode
          (by simp [evalHOLExact, hw]) hnt
      rw [hr_eq, hs_eq]
      have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
      have hmid_ma : mid.memaddrs = ordinaryDomain := by rw [hmid_eq]; exact hma
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hw,
          show ofString "ll" ≠ ofString "w" by decide]
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hdst,
          show ofString "ll" ≠ ofString "dst" by decide]
      have heff_s_mid : M11.ByteRegionEffect s mid Rl := by
        rw [hmid_eq]; exact (M11.ByteRegionEffect.refl s Rl).with_locals_clock mid.locals mid.clock
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
      rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
      simp only [hsb] at hnt_m ⊢
      rcases storeByte_only_none_or_error mid (.var .local (ofString "dst"))
          (.op .add [.const 128, .var .local (ofString "ll")]) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hnt_m ⊢
        have hdst_lt := storeByte_local_dst_lt_heapEnd mid dst0 _ hmid_ma hmid_dst (by rw [hsb])
        obtain ⟨heff_hdr, hs2_loc⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev; obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
        have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
        have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hs2_loc]; exact hmid_dst
        have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w0)) := by
          rw [hs2_loc]; exact hmid_w
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs2_loc]; exact hmid_ll
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
          have hhe := hdst_lt; rw [heapEnd_val] at hhe
          rw [BitVec.toNat_add]; change (dst0.toNat + 1) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
          have hhe := hdst_lt; rw [heapEnd_val] at hhe; omega
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m ⊢
        rcases hc_put : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .var .local (ofString "w"),
             .var .local (ofString "ll")]) with ⟨rc, s3⟩
        have hnt_put : rc ≠ some .timeOut := by
          rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
        have hput := M11.eval_call_rlp_put_be s2
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.var .local (ofString "w"))
          (.var .local (ofString "ll"))
          (dst0 + 1) w0 ll Rl hs2_code
          (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by simp [evalHOLExact, hs2_w])
          (by simp [evalHOLExact, hs2_ll])
          hfit
          (fun _ => by
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
          (by rw [hc_put]; exact hnt_put)
        dsimp only at hput; rw [hc_put] at hput; simp only [hc_put] at hnt_m ⊢
        cases rc with
        | some r =>
          dsimp only
          have hnr := hput.2 (by simp)
          refine ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)), fun r' hr' _ => ?_⟩
          injection hr' with hr''; subst hr''; exact hnr
        | none =>
          dsimp only at hnt_m ⊢
          obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
          have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
            rw [hs3_loc]; exact hs2_ll
          rw [evaluateHOLFiniteState_return]
          have hev_ret : @evalHOLExact 64 F _ s3.toExact
              (fun a => Classical.propDecidable (s3.memaddrs a))
              (.op .add [.const 1, .var .local (ofString "ll")]) =
              some (.val (.word (1 + ll))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret]; dsimp only
          have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz]; dsimp only
          have h1ll_nat : (1 + ll).toNat = 1 + ll.toNat := by
            rw [BitVec.toNat_add]; change (1 + ll.toNat) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
          refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
          · injection hrv with hrv'; injection hrv' with hrv''
            exact ⟨1 + ll, hrv''.symm, by omega, by omega, hdst_lt,
              (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
          · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩

theorem eval_decCall_rlp_encode_word {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp wExp : ExpHOL 64)
    (dst0 w0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hw : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp =
      some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1) :
    ∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ len.toNat ∧ len.toNat ≤ 9 ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, wExp] = some [.val (.word dst0), .val (.word w0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hw]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_encode_word")
    (ofString "dst") (ofString "w")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_word) dst0 w0 (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_word)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "w", ValueHOL.val (.word w0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "dst" by decide]
    have hent_w : ent.locals.lookup (ofString "w") = some (.val (.word w0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hew : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨rew, sew⟩
    have hnt_ew : rew ≠ some .timeOut := by
      rintro rfl; rw [hew] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_word_body_exact ent dst0 w0 Rl
      hcode hAR.1.memaddrs hent_dst hent_w hin_ivl (by rw [hew]; exact hnt_ew)
    rw [hew] at hret hnonret
    dsimp only at hret hnonret
    simp only [hew] at hnt hres ⊢
    cases rew with
    | none => exact False.elim (not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_ew
      | exception eid ev =>
        exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hres)
      | returned rv =>
        obtain ⟨len, rfl, hlen1, hlen9, hdst_lt, heff_ew⟩ := hret rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt hres ⊢
        rw [if_pos hsh] at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word len))
          { sew with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_ew).with_locals_clock mid.locals mid.clock
        exact ⟨len, mid, hlen1, hlen9, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid, hnt, hres, rfl⟩
      | «break» | «continue» | error =>
        exact False.elim (not_resumes_error hres)
      | finalFfi _ =>
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem eval_rlp_encode_bytes_body_exact {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)
    (∀ rv, out.1 = some (.returned rv) →
      ∃ len : BitVec 64, rv = .val (.word len) ∧
        len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧
        dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s out.2 Rl) ∧
    (∀ r, out.1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_bytes =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
          (.dec (ofString "b") .one (.loadByte (.var .local (ofString "src")))
            (.ite (.cmp .lower (.var .local (ofString "b")) (.const 128))
              (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) (.return (.const 1)))
              .skip))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_write_header")
          [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
  dsimp only
  rw [hb] at hnt ⊢
  let tailP : ProgHOL 64 :=
    .decCall (ofString "h") .one (ofString "rlp_write_header")
      [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"),
           .var .local (ofString "n")])
        (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))
  have htail : ∀ (t : PanSemStateFiniteExact 64 F),
      M11.ByteRegionEffect s t Rl →
      t.locals = s.locals →
      (evaluateHOLFiniteState t tailP).1 ≠ some .timeOut →
      (∀ rv, (evaluateHOLFiniteState t tailP).1 = some (.returned rv) →
        ∃ len : BitVec 64, rv = .val (.word len) ∧
          len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧
          dst0.toNat < heapEnd ∧ M11.ByteRegionEffect s (evaluateHOLFiniteState t tailP).2 Rl) ∧
      (∀ r, (evaluateHOLFiniteState t tailP).1 = some r → (∀ rv, r ≠ .returned rv) → ¬ Resumes (some r)) := by
    intro t heff_t ht_loc hnt_t
    have ht_code : t.code = originalRuntimeCode := heff_t.code.trans hcode
    have ht_ma : t.memaddrs = ordinaryDomain := heff_t.memaddrs.trans hma
    have ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [ht_loc]; exact hdst
    have ht_src : t.locals.lookup (ofString "src") = some (.val (.word src0)) := by rw [ht_loc]; exact hsrc
    have ht_n : t.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [ht_loc]; exact hn
    dsimp only [tailP] at hnt_t ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_t ⊢
    have ha : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
        some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht_dst, ht_n]
    have hlk := pan_three_word_lookup t.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
      (by decide) (by decide) (by decide)
      (by rw [ht_code]; exact M11.lookup_rlp_write_header)
    simp only [ha, hlk] at hnt_t ⊢
    by_cases hcz : t.clock = 0
    · simp [hcz] at hnt_t
    · simp only [hcz, ↓reduceIte] at hnt_t ⊢
      set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "base", ValueHOL.val (.word 128))).update (ofString "n", ValueHOL.val (.word n0))
      set ent := callEntryStateHOLFinite t cmap
      have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent_base : ent.locals.lookup (ofString "base") = some (.val (.word 128)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hwh : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; rw [hwh] at hnt_t; exact hnt_t rfl
      obtain ⟨hret_wh, hnonret_wh⟩ := eval_rlp_write_header_body_exact ent dst0 128 n0 Rl
        ht_code ht_ma hent_dst hent_base hent_n
        (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
        (by rw [hwh]; exact hnt_wh)
      rw [hwh] at hret_wh hnonret_wh
      dsimp only at hret_wh hnonret_wh
      simp only [hwh] at hnt_t ⊢
      cases rwh with
      | none => exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
      | some r =>
        cases r with
        | timeOut => exact absurd rfl hnt_wh
        | exception eid ev =>
          refine ⟨fun _ h => by simp at h, fun r' hr' _ => ?_⟩
          injection hr' with hr''; subst hr''
          exact hnonret_wh (.exception eid ev) rfl (fun _ h => by cases h)
        | returned rv =>
          obtain ⟨rfl, hdst_lt, heff_wh⟩ := hret_wh rv rfl
          set h := BitVec.ofNat 64 (rlpHeaderLenPure n0.toNat)
          have hbnd := rlpHeaderLenPure_bounds n0.toNat
          have hh_nat : h.toNat = rlpHeaderLenPure n0.toNat := by
            dsimp [h]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
          have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word h) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          dsimp only at hnt_t ⊢; rw [if_pos hsh] at hnt_t ⊢; dsimp only at hnt_t ⊢
          set mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := t.locals }
          have heff_t_mid : M11.ByteRegionEffect t mid Rl :=
            ((M11.ByteRegionEffect.refl t Rl |>.with_locals_clock ent.locals ent.clock).trans heff_wh).with_locals_clock mid.locals mid.clock
          have hmid_code : mid.code = originalRuntimeCode := heff_t_mid.code.trans ht_code
          have hmid_ma : mid.memaddrs = ordinaryDomain := heff_t_mid.memaddrs.trans ht_ma
          have hmid_h : mid.locals.lookup (ofString "h") = some (.val (.word h)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_dst,
              show ofString "h" ≠ ofString "dst" by decide]
          have hmid_src : mid.locals.lookup (ofString "src") = some (.val (.word src0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_src,
              show ofString "h" ≠ ofString "src" by decide]
          have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
            simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht_n,
              show ofString "h" ≠ ofString "n" by decide]
          have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat := by
            have hhe := hdst_lt; rw [heapEnd_val] at hhe
            rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          rcases hc_mc : evaluateHOLFiniteState mid
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"),
               .var .local (ofString "n")]) with ⟨rmc, smc⟩
          have hnt_mc : rmc ≠ some .timeOut := by
            rintro rfl; rw [hc_mc] at hnt_t; exact hnt_t rfl
          have hmc := M11.eval_call_memcpy_bre_gen mid
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "h")])
            (.var .local (ofString "src"))
            (.var .local (ofString "n"))
            (dst0 + h) src0 n0 Rl hmid_code hmid_ma
            (by simp [evalHOLExact, evalListHOLExact, hmid_dst, hmid_h, wordOpHOL, wordOp, valueIsWord, valueWord])
            (by simp [evalHOLExact, hmid_src])
            (by simp [evalHOLExact, hmid_n])
            (fun off hoff _ => by
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
              exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
            (fun off hoff _ => by
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
              exact ⟨ivl, hivl, by rw [hdsth_nat, hh_nat]; omega, by rw [hdsth_nat, hh_nat]; omega⟩)
            (by rw [hc_mc]; exact hnt_mc)
          dsimp only at hmc; rw [hc_mc] at hmc; simp only [hc_mc] at hnt_t ⊢
          cases rmc with
          | some r' =>
            dsimp only
            have hnr := hmc.2 (by simp)
            refine ⟨fun rv' hrv' => False.elim (hnr (Or.inl ⟨rv', hrv'⟩)), fun r'' hr'' _ => ?_⟩
            injection hr'' with hr'''; subst hr'''; exact hnr
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mc, hsmc_loc⟩ := hmc.1 rfl
            have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by
              rw [hsmc_loc]; exact hmid_h
            have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by
              rw [hsmc_loc]; exact hmid_n
            rw [evaluateHOLFiniteState_return]
            have hev_ret : @evalHOLExact 64 F _ smc.toExact
                (fun a => Classical.propDecidable (smc.memaddrs a))
                (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                some (.val (.word (h + n0))) := by
              simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret]; dsimp only
            have hsz : sizeOfShapeWithContextHOL smc.structs (shapeOfHOLExact (.val (.word (h + n0)) : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact]
            rw [if_pos hsz]; dsimp only
            have hhn_le : (h + n0).toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat := by
              rw [BitVec.toNat_add, hh_nat]; exact Nat.mod_le _ _
            refine ⟨fun rv' hrv' => ?_, fun r' hr' hnr => ?_⟩
            · injection hrv' with h1; injection h1 with h2
              exact ⟨h + n0, h2.symm, hhn_le, hdst_lt,
                (((heff_t.trans heff_t_mid).trans heff_mc).with_locals_clock _ _).with_locals_clock _ _⟩
            · injection hr' with hr''; subst hr''; exact absurd rfl (hnr _)
        | «break» | «continue» | error =>
          dsimp only
          exact ⟨fun _ h => by simp at h, fun r' hr' _ => by injection hr' with hr''; subst hr''; exact not_resumes_error⟩
        | finalFfi _ =>
          dsimp only
          exact ⟨fun _ h => by simp at h, fun r' hr' _ hr => by
            injection hr' with hr''; subst hr''
            rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hev_n1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
      some (.val (.word (if n0 = 1 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_n1] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases hn1 : n0 = 1
  · rw [if_pos hn1, if_neg h10, evaluateHOLFiniteState_dec_total] at hnt ⊢
    dsimp only at hnt ⊢
    rcases hlb : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.var .local (ofString "src"))) with _ | bv
    · simp only [hlb]
      exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
    · have hbv_w : ∃ b0 : BitVec 64, bv = .val (.word b0) := by
        simp only [evalHOLExact, hsrc] at hlb
        unfold panMemLoadByteHOL at hlb; dsimp only at hlb
        cases hm : s.memory (panByteAlignHOL src0) with
        | word cell =>
          simp only [hm] at hlb; split at hlb
          · simp only [Option.map, Option.some.injEq] at hlb; exact ⟨_, hlb.symm⟩
          · simp at hlb
      obtain ⟨b0, rfl⟩ := hbv_w
      have hsh_b : shapeEqHOL .one (shapeOfHOLExact (.val (.word b0) : ValueHOL 64)) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      simp only [hlb] at hnt ⊢
      rw [if_pos hsh_b] at hnt ⊢
      set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) s
      have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
          show ofString "b" ≠ ofString "dst" by decide]
      rw [evaluateHOLFiniteState_ite] at hnt ⊢
      have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
          (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
          some (.val (.word (if b0 < 128 then 1 else 0))) := by
        simp [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_blt] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hblt : b0 < 128
      · rw [if_pos hblt, if_neg h10, evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst : evaluateHOLFiniteState sb
            (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with ⟨rst, s1⟩
        simp only [hst] at hnt ⊢
        rcases storeByte_only_none_or_error sb (.var .local (ofString "dst")) (.var .local (ofString "b")) with hsn | hse
        · rw [hst] at hsn; dsimp only at hsn; subst hsn; dsimp only
          have hdst_lt := storeByte_local_dst_lt_heapEnd sb dst0 _ hma hsb_dst (by rw [hst])
          obtain ⟨heff1, _⟩ := M11.ByteRegionEffect.of_storeByte (Rl := Rl) hst (fun addr hdst_ev _ => by
            simp only [evalHOLExact, hsb_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
            subst hdst_ev
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            have := rlpHeaderLenPure_bounds n0.toNat
            exact ⟨ivl, hivl, h1, by omega⟩)
          rw [evaluateHOLFiniteState_return]
          simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.one_le_ofNat, ↓reduceIte]
          have hbnd := rlpHeaderLenPure_bounds n0.toNat
          have heff_s_sb : M11.ByteRegionEffect s sb Rl :=
            (M11.ByteRegionEffect.refl s Rl).with_locals_clock sb.locals sb.clock
          refine ⟨fun rv hrv => ?_, fun r hr hnr => ?_⟩
          · injection hrv with h1; injection h1 with h2
            exact ⟨1, h2.symm, by change 1 ≤ _; omega, hdst_lt,
              ((heff_s_sb.trans heff1).with_locals_clock _ _).with_locals_clock _ _⟩
          · injection hr with hr'; subst hr'; exact absurd rfl (hnr _)
        · rw [hst] at hse; dsimp only at hse; subst hse
          exact ⟨fun _ h => by simp at h, fun r hr _ => by injection hr with hr'; subst hr'; exact not_resumes_error⟩
      · rw [if_neg hblt, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
        dsimp only at hnt ⊢
        let s' : PanSemStateFiniteExact 64 F :=
          { sb with locals := HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b")) }
        have hs'_loc : s'.locals = s.locals := by
          apply HolFiniteMapExact.ext; funext k
          change (HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b"))).lookup k = s.locals.lookup k
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hk : k = ofString "b"
          · subst hk; simp
          · simp [hk, sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact htail s' ((M11.ByteRegionEffect.refl s Rl).with_locals_clock s'.locals s'.clock) hs'_loc hnt
  · rw [if_neg hn1, if_pos rfl, evaluateHOLFiniteState_skip] at hnt ⊢
    dsimp only at hnt ⊢
    exact htail s (M11.ByteRegionEffect.refl s Rl) rfl hnt

theorem eval_decCall_rlp_encode_bytes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧
      dst0.toNat + rlpHeaderLenPure n0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1) :
    ∃ (len : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      len.toNat ≤ rlpHeaderLenPure n0.toNat + n0.toNat ∧
      dst0.toNat < heapEnd ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word len)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] = some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlk := pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_rlp_encode_bytes)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
    have hent_src : ent.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "src" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases heb : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨reb, seb⟩
    have hnt_eb : reb ≠ some .timeOut := by
      rintro rfl; rw [heb] at hnt; exact hnt rfl
    obtain ⟨hret, hnonret⟩ := eval_rlp_encode_bytes_body_exact ent dst0 src0 n0 Rl
      hcode hAR.1.memaddrs hent_dst hent_src hent_n hin_ivl (by rw [heb]; exact hnt_eb)
    rw [heb] at hret hnonret
    dsimp only at hret hnonret
    simp only [heb] at hnt hres ⊢
    cases reb with
    | none => exact False.elim (not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_eb
      | exception eid ev =>
        exact False.elim (hnonret (.exception eid ev) rfl (fun _ h => by cases h) hres)
      | returned rv =>
        obtain ⟨len, rfl, hlen_le, hdst_lt, heff_eb⟩ := hret rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt hres ⊢
        rw [if_pos hsh] at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word len))
          { seb with locals := s.locals }
        have heff0 : M11.ByteRegionEffect s ent Rl :=
          (M11.ByteRegionEffect.refl s Rl).with_locals_clock ent.locals ent.clock
        have heff_mid : M11.ByteRegionEffect s mid Rl :=
          (heff0.trans heff_eb).with_locals_clock mid.locals mid.clock
        exact ⟨len, mid, hlen_le, hdst_lt, heff_mid.globals, rfl,
          HeapByteEff.of_m11_bre hAR heff_mid, hnt, hres, rfl⟩
      | «break» | «continue» | error =>
        exact False.elim (not_resumes_error hres)
      | finalFfi _ =>
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-! ## 5. `memcpy`, `memzero`, `keccak256`, `st_be64`, and `rlp_finish_list` in `HeapByteEff` -/

theorem eval_call_memcpy_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hsub : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none → HeapByteEff s out.2 Rl gw ∧ out.2.locals = s.locals ∧ out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  have hmc := M11.eval_call_memcpy_bre s dstExp srcExp nExp dst0 src0 n0 Rl
    hcode hAR.1.memaddrs hdst hsrc hn hsub hnt
  dsimp only at hmc ⊢
  refine ⟨fun hn0 => ?_, hmc.2⟩
  obtain ⟨heff, hloc⟩ := hmc.1 hn0
  exact ⟨HeapByteEff.of_m11_bre hAR heff, hloc, heff.globals⟩

private def noExnProg : ProgHOL 64 → Bool
  | .dec _ _ _ b => noExnProg b
  | .seq a b => noExnProg a && noExnProg b
  | .ite _ a b => noExnProg a && noExnProg b
  | .while _ b => noExnProg b
  | .assign _ _ _ | .store _ _ | .storeByte _ _ => true
  | .skip | .break | .continue | .annot _ _ | .return _ => true
  | _ => false

private theorem evaluate_noExnProg {F : Type} (p : ProgHOL 64) (hp : noExnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (eid : MlS) (ev : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.exception eid ev) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | «break» => rw [evaluateHOLFiniteState_break]; simp
  | «continue» => rw [evaluateHOLFiniteState_continue]; simp
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; simp
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | assign _ _ _ =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | dec x sh init b =>
    have hb : noExnProg b = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noExnProg b hb _ eid ev
      · simp
  | seq a b =>
    have hab : noExnProg a = true ∧ noExnProg b = true := by
      simpa [shape, noExnProg, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noExnProg a hab.1 s eid ev
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact evaluate_noExnProg b hab.2 m eid ev
    | some _ => exact ha
  | ite _ a b =>
    have hab : noExnProg a = true ∧ noExnProg b = true := by
      simpa [shape, noExnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noExnProg b hab.2 s eid ev
      · exact evaluate_noExnProg a hab.1 s eid ev
    · simp
  | «while» cond body =>
    have hb : noExnProg body = true := by simpa [shape, noExnProg] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noExnProg body hb (decClockHOLFinite s) eid ev
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid eid ev
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noExnProg (.while cond body) (by simpa [noExnProg] using hb) mid eid ev
            | exception _ _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noExnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

theorem eval_call_memzero_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hsub : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp])
    (out.1 = none →
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
      HeapByteEff s out.2 Rl gw ∧ out.2.locals = s.locals ∧ out.2.globals = s.globals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨ps_z, bd_z, rt_z, hlk_z, hsp_z⟩ := R13Shards.Keccak256.funByteEff_memzero
  have hlook_eq : originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
    lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memzero) rfl
  have hinj := Option.some.inj (hlk_z.symm.trans hlook_eq)
  obtain ⟨rfl, hr_z⟩ := Prod.mk.inj hinj
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr_z
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, nExp] = some [.val (.word dst0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hn]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memzero) dst0 n0 (by decide)
    (by rw [hcode]; exact hlook_eq)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "n", ValueHOL.val (.word n0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide]
    have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_ent : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString "memzero") [.val (.word dst0), .val (.word n0)] =
        some (sourceFnBody Guest.Software.guestFn_memzero, cmap, .one) :=
      pan_two_word_lookup originalRuntimeCode.lookup _ _ _ _ dst0 n0 (by decide) hlook_eq
    have hno_exn : ∀ e v, (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memzero)).1 ≠
        some (.exception e v) :=
      evaluate_noExnProg _ (by decide) ent
    rcases hmz : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_memzero) with ⟨rmz, smz⟩
    have hnt_mz : rmz ≠ some .timeOut := by
      rintro rfl; rw [hmz] at hnt; exact hnt rfl
    simp only [hmz] at hnt ⊢
    cases rmz with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_mz
      | exception eid ev => exact absurd (congrArg Prod.fst hmz) (hno_exn eid ev)
      | returned rv =>
        have hbeff := hsp_z ent [.val (.word dst0), .val (.word n0)] hcode
          (guestInv_callEntry s cmap hAR.1) hl_ent
          (by rw [hmz]; exact hnt_mz) (by rw [hmz]; exact Or.inl ⟨rv, rfl⟩)
        rw [hmz] at hbeff
        have hdom_mz := R13Shards.Keccak256.memzero_body_eff ent dst0 n0 hcode
          (guestInv_callEntry s cmap hAR.1) hent_dst hent_n
          (by rw [hmz]; exact Or.inl ⟨rv, rfl⟩)
        rw [hmz] at hdom_mz
        dsimp only
        split
        · have heff_ent : R13Shards.Keccak256.ByteEff s { smz with locals := s.locals } Rl := by
            have h1 : R13Shards.Keccak256.ByteEff s ent Rl :=
              (R13Shards.Keccak256.ByteEff.refl s Rl).locals_clock ent.locals ent.clock
            have h2 : R13Shards.Keccak256.ByteEff ent smz Rl :=
              hbeff.mono (fun i hi hp => by
                simp [R13Shards.Keccak256.valWordNat] at hi; subst hi
                exact hsub hp)
            exact (h1.trans h2).locals_clock s.locals smz.clock
          exact ⟨fun _ => ⟨hdom_mz.2, HeapByteEff.of_byteEff hAR heff_ent, rfl, heff_ent.globals⟩,
            fun h => False.elim (h rfl)⟩
        · exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem call0_none_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

theorem eval_call_keccak256_heap {F : Type}
    (s : PanSemStateFiniteExact 64 F) (pExp nExp outExp : ExpHOL 64)
    (pw nw outw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word pw)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word nw)))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word outw)))
    (hout_in : ∃ ivl ∈ Rl, ivl.1 ≤ outw.toNat ∧ outw.toNat + 32 ≤ ivl.1 + ivl.2)
    (hpad_in : globN s "keccak_pad" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_pad" ∧ globN s "keccak_pad" + 136 ≤ ivl.1 + ivl.2)
    (hst_in : globN s "keccak_st" ≠ 0 →
      ∃ ivl ∈ Rl, ivl.1 ≤ globN s "keccak_st" ∧ globN s "keccak_st" + 200 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "keccak256") [pExp, nExp, outExp])
    (out.1 = none ∨ Resumes out.1) →
      HeapByteEff s out.2 Rl gw ∧ (out.1 = none → out.2.locals = s.locals ∧ out.2.globals = s.globals) := by
  intro out hor
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [pExp, nExp, outExp] = some [.val (.word pw), .val (.word nw), .val (.word outw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hp, hn, hout]
  have heff := R13Shards.Keccak256.call0_byteEff R13Shards.Keccak256.funByteEff_keccak256
    s [pExp, nExp, outExp] Rl hcode hAR.1
    (fun vs hvs i hi hipos => by
      rw [ha] at hvs; injection hvs with hvs; subst hvs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [R13Shards.Keccak256.globBufIvl_eq_bufferRegion] at hipos ⊢
        by_cases h0 : globN s "keccak_st" = 0
        · simp [bufferRegion, h0] at hipos
        · simp only [bufferRegion, h0, ↓reduceIte]
          exact hst_in h0
      · rw [R13Shards.Keccak256.globBufIvl_eq_bufferRegion] at hipos ⊢
        by_cases h0 : globN s "keccak_pad" = 0
        · simp [bufferRegion, h0] at hipos
        · simp only [bufferRegion, h0, ↓reduceIte]
          exact hpad_in h0
      · simp only [R13Shards.Keccak256.valWordNat, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some]
        exact hout_in)
    hnt hor
  refine ⟨HeapByteEff.of_byteEff hAR heff, fun hn0 => ⟨?_, heff.globals⟩⟩
  exact call0_none_locals s _ _ hn0

theorem eval_decCall_rlp_finish_list {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp pendExp : ExpHOL 64)
    (dst0 pend0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hpend : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pendExp =
      some (.val (.word pend0)))
    (hle : dst0.toNat + 9 ≤ pend0.toNat)
    (_hfit : pend0.toNat ≤ heapEnd)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ pend0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_finish_list") [dstExp, pendExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_finish_list") [dstExp, pendExp] cont)).1) :
    let payload := pend0.toNat - (dst0.toNat + 9)
    let total := rlpHeaderLenPure payload + payload
    ∃ (tw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      tw.toNat = total ∧
      total ≤ pend0.toNat - dst0.toNat ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word tw)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_finish_list") [dstExp, pendExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  intro payload total
  have hhe264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hb_fl : sourceFnBody Guest.Software.guestFn_rlp_finish_list =
      .dec (ofString "payload") .one
        (.op .sub [.var .local (ofString "payload_end"),
          .op .add [.var .local (ofString "dst"), .const 9]])
        (.decCall (ofString "hl") .one (ofString "rlp_list_header_len")
          [.var .local (ofString "payload")]
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
               .op .add [.var .local (ofString "dst"), .const 9],
               .var .local (ofString "payload")])
            (.seq
              (.call (some (none, none)) (ofString "rlp_encode_list_header")
                [.var .local (ofString "dst"), .var .local (ofString "payload")])
              (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]))))) := rfl
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, pendExp] = some [.val (.word dst0), .val (.word pend0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hpend]
  have hlk := pan_two_word_lookup s.code.lookup (ofString "rlp_finish_list")
    (ofString "dst") (ofString "payload_end")
    (sourceFnBody Guest.Software.guestFn_rlp_finish_list) dst0 pend0 (by decide)
    (by rw [hcode]; exact lookup_rlp_finish_list)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "payload_end", ValueHOL.val (.word pend0))
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "payload_end" ≠ ofString "dst" by decide]
    have hent_pend : ent.locals.lookup (ofString "payload_end") = some (.val (.word pend0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- Evaluate body of `rlp_finish_list` on `ent`:
    have hd9_nat : (dst0 + 9).toNat = dst0.toNat + 9 := by
      rw [BitVec.toNat_add]; change (dst0.toNat + 9) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
    let pw : BitVec 64 := pend0 - (dst0 + 9)
    have hpw_nat : pw.toNat = payload := by
      change (pend0 - (dst0 + 9)).toNat = pend0.toNat - (dst0.toNat + 9)
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hd9_nat]; exact hle)), hd9_nat]
    have hnt_body : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list)).1 ≠
        some .timeOut := by
      intro hto; rw [hto] at hnt; exact hnt rfl
    rw [hb_fl, evaluateHOLFiniteState_dec_total] at hnt_body
    have hev_pw : @evalHOLExact 64 F _ ent.toExact
        (fun a => Classical.propDecidable (ent.memaddrs a))
        (.op .sub [.var .local (ofString "payload_end"),
          .op .add [.var .local (ofString "dst"), .const 9]]) =
        some (.val (.word pw)) := by
      simp [evalHOLExact, evalListHOLExact, hent_pend, hent_dst, wordOpHOL, wordOp, valueIsWord, valueWord, pw]
    have hsh_pw : shapeEqHOL .one (shapeOfHOLExact (.val (.word pw) : ValueHOL 64)) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    dsimp only at hnt_body; rw [hev_pw] at hnt_body; dsimp only at hnt_body; rw [if_pos hsh_pw] at hnt_body
    set s1 := setVarHOLFinite (ofString "payload") (.val (.word pw)) ent
    have hAR_s1 : ArenaReady s1 := ⟨guestInv_setVar _ _ _ hAR_ent.1, hAR_ent.2⟩
    have hs1_pw : s1.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
        show ofString "payload" ≠ ofString "dst" by decide]
    obtain ⟨m1, hhl_nat, hhl1, hhl9, hm1_g, hm1_m, hm1_loc, heff_m1, hnt_m1, h_lhl_eq⟩ :=
      eval_decCall_rlp_list_header_len s1 "hl" (.var .local (ofString "payload")) pw _ Rl []
        hcode hAR_s1 hs1_pw hnt_body
    set hlw := BitVec.ofNat 64 (rlpHeaderLenPure pw.toNat)
    have hhl_nat' : hlw.toNat = rlpHeaderLenPure payload := by rw [hhl_nat, hpw_nat]
    have hm1_hl : m1.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm1_pw : m1.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_pw,
        show ofString "hl" ≠ ofString "payload" by decide]
    have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hm1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_dst,
        show ofString "hl" ≠ ofString "dst" by decide]
    have hdhl_nat : (dst0 + hlw).toNat = dst0.toNat + hlw.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m1
    rcases hc_mc : evaluateHOLFiniteState m1
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
         .op .add [.var .local (ofString "dst"), .const 9],
         .var .local (ofString "payload")]) with ⟨rmc, m2⟩
    have hnt_mc : rmc ≠ some .timeOut := by
      rintro rfl; rw [hc_mc] at hnt_m1; exact hnt_m1 rfl
    have hmc := eval_call_memcpy_heap m1
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")])
      (.op .add [.var .local (ofString "dst"), .const 9])
      (.var .local (ofString "payload"))
      (dst0 + hlw) (dst0 + 9) pw Rl [] heff_m1.arena.1.code heff_m1.arena
      (by simp [evalHOLExact, evalListHOLExact, hm1_dst, hm1_hl, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, evalListHOLExact, hm1_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by simp [evalHOLExact, hm1_pw])
      (fun _ => by
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, by rw [hdhl_nat]; omega, by rw [hdhl_nat, hpw_nat]; omega⟩)
      (by rw [hc_mc]; exact hnt_mc)
    dsimp only at hmc; rw [hc_mc] at hmc
    -- Fold body evaluation up to `hc_mc`:
    have hbody_step1 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list) =
        (let o := evaluateHOLFiniteState m1
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
                 .op .add [.var .local (ofString "dst"), .const 9],
                 .var .local (ofString "payload")])
              (.seq
                (.call (some (none, none)) (ofString "rlp_encode_list_header")
                  [.var .local (ofString "dst"), .var .local (ofString "payload")])
                (.return (.op .add [.var .local (ofString "hl"), .var .local (ofString "payload")]))));
         (o.1,
          { o.2 with
            locals := HolFiniteMapExact.resVarEq
              (HolFiniteMapExact.resVarEq o.2.locals (ofString "hl", s1.locals.lookup (ofString "hl")))
              (ofString "payload", ent.locals.lookup (ofString "payload")) })) := by
      rw [hb_fl, evaluateHOLFiniteState_dec_total]
      dsimp only; rw [hev_pw]; dsimp only; rw [if_pos hsh_pw]
      rw [h_lhl_eq]
    cases rmc with
    | some r_mc =>
      exfalso
      have hnr := hmc.2 (by simp)
      rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc] at hres
      dsimp only at hres
      cases r_mc with
      | returned _ => exact hnr (Or.inl ⟨_, rfl⟩)
      | exception eid ev =>
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
        · simp at h
        · injection h with h'; injection h' with e1 e2; subst e1 e2
          exact hnr (Or.inr ⟨eid, ev, rfl, hne⟩)
      | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      | timeOut => exact absurd rfl hnt_mc
      | error | «break» | «continue» => exact not_resumes_error hres
    | none =>
      rw [hc_mc] at hnt_m1; dsimp only at hnt_m1
      obtain ⟨heff_m2, hm2_loc, hm2_g⟩ := hmc.1 rfl
      have hm2_hl : m2.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
        rw [hm2_loc]; exact hm1_hl
      have hm2_pw : m2.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
        rw [hm2_loc]; exact hm1_pw
      have hm2_dst : m2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hm2_loc]; exact hm1_dst
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m1
      rcases hc_lh : evaluateHOLFiniteState m2
        (.call (some (none, none)) (ofString "rlp_encode_list_header")
          [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "payload")]) with ⟨rlh, m3⟩
      have hnt_lh : rlh ≠ some .timeOut := by
        rintro rfl; rw [hc_lh] at hnt_m1; exact hnt_m1 rfl
      have hlh := eval_call_rlp_encode_list_header m2
        (ExpHOL.var VarKind.local (ofString "dst")) (ExpHOL.var VarKind.local (ofString "payload"))
        dst0 pw Rl [] heff_m2.arena.1.code heff_m2.arena
        (by simp [evalHOLExact, hm2_dst])
        (by simp [evalHOLExact, hm2_pw])
        (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            exact ⟨ivl, hivl, h1, by rw [hpw_nat]; have := rlpHeaderLenPure_bounds payload; omega⟩)
        (by rw [hc_lh]; exact hnt_lh)
      dsimp only at hlh; rw [hc_lh] at hlh
      cases rlh with
      | some r_lh =>
        exfalso
        have hnr := hlh.2 (by simp)
        rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc] at hres
        dsimp only at hres
        rw [evaluateHOLFiniteState_seq_line780, hc_lh] at hres
        dsimp only at hres
        cases r_lh with
        | returned _ => exact hnr (Or.inl ⟨_, rfl⟩)
        | exception eid ev =>
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, hne⟩
          · simp at h
          · injection h with h'; injection h' with e1 e2; subst e1 e2
            exact hnr (Or.inr ⟨eid, ev, rfl, hne⟩)
        | finalFfi _ => rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | timeOut => exact absurd rfl hnt_lh
        | error | «break» | «continue» => exact not_resumes_error hres
      | none =>
        obtain ⟨_, heff_m3, hm3_loc⟩ := hlh.1 rfl
        have hm3_hl : m3.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
          rw [hm3_loc]; exact hm2_hl
        have hm3_pw : m3.locals.lookup (ofString "payload") = some (.val (.word pw)) := by
          rw [hm3_loc]; exact hm2_pw
        let tw : BitVec 64 := hlw + pw
        have hhl_bds : rlpHeaderLenPure (pend0.toNat - (dst0.toNat + 9)) ≤ 9 :=
          (rlpHeaderLenPure_bounds (pend0.toNat - (dst0.toNat + 9))).2
        have htw_lt : rlpHeaderLenPure payload + payload < 2 ^ 64 := by
          dsimp [payload]; omega
        have htw_nat : tw.toNat = total := by
          change (hlw + pw).toNat = rlpHeaderLenPure payload + payload
          rw [BitVec.toNat_add, hhl_nat', hpw_nat]
          change (rlpHeaderLenPure payload + payload) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt htw_lt
        have hret_m3 : evaluateHOLFiniteState m3
            (.return (.op .add [ExpHOL.var VarKind.local (ofString "hl"), ExpHOL.var VarKind.local (ofString "payload")])) =
            (some (.returned (.val (.word tw))), m3.emptyLocalsHOLFinite) := by
          rw [evaluateHOLFiniteState_return]
          have hev_tw : @evalHOLExact 64 F _ m3.toExact
              (fun a => Classical.propDecidable (m3.memaddrs a))
              (.op .add [ExpHOL.var VarKind.local (ofString "hl"), ExpHOL.var VarKind.local (ofString "payload")]) =
              some (.val (.word tw)) := by
            simp [evalHOLExact, evalListHOLExact, hm3_hl, hm3_pw, wordOpHOL, wordOp, valueIsWord, valueWord, tw]
          rw [hev_tw]; dsimp only
          have hsz : sizeOfShapeWithContextHOL m3.structs (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz]
        have hbody_done : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_finish_list) =
            (some (.returned (.val (.word tw))),
             { m3.emptyLocalsHOLFinite with
               locals := HolFiniteMapExact.resVarEq
                 (HolFiniteMapExact.resVarEq m3.emptyLocalsHOLFinite.locals (ofString "hl", s1.locals.lookup (ofString "hl")))
                 (ofString "payload", ent.locals.lookup (ofString "payload")) }) := by
          rw [hbody_step1, evaluateHOLFiniteState_seq_line780, hc_mc]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hc_lh]; dsimp only
          rw [hret_m3]
        have hsh_tw : (shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word tw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [hbody_done] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        rw [if_pos hsh_tw] at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word tw)) { m3 with locals := s.locals }
        have heff_s_s1 : HeapByteEff s s1 Rl [] :=
          (HeapByteEff.refl hAR Rl []).locals_clock s1.locals s1.clock
        have heff_mid0 : HeapByteEff s mid Rl [] :=
          (((heff_s_s1.trans heff_m1).trans heff_m2).trans heff_m3).locals_clock mid.locals mid.clock
        have heff_mid : HeapByteEff s mid Rl gw :=
          heff_mid0.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
        have hm3_g : m3.globals = s.globals := by
          apply HolFiniteMapExact.ext_lookup
          intro k
          exact (heff_mid0.globals k (by simp)).symm
        exact ⟨tw, mid, htw_nat, by dsimp [total, payload]; omega, hm3_g, rfl,
          heff_mid, hnt, hres, rfl⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
