import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.StepLemmas

/-! Shared RLP encoding and `memcpy` `ByteRegionEffect` lemmas for `wk_rlp_encode_word`,
`wk_rlp_encode_bytes`, and `wk_sk_make` in micro-shard `m11` (`wave8/contracts-m11`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.M11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

theorem lookup_rlp_write_header :
    originalRuntimeCode.lookup (ofString "rlp_write_header") =
      some ([(ofString "dst", .one), (ofString "base", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_write_header, .one) :=
  lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_write_header) rfl

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

/-! ## 1. Domain bound from a successful `storeByte` or `store` -/

theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    sourceBase ≤ (panByteAlignHOL addr).toNat ∧ addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  rw [sourceBase_val, heapEnd_val]
  omega

theorem word_dom_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    sourceBase ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapEnd ∧ addr.toNat % 8 = 0 := by
  rw [hma, ordinaryDomain_iff] at hdom
  rw [sourceBase_val, heapEnd_val]
  omega

/-! ## 2. Exact evaluation of `rlp_be_len(v)` -/

private theorem lsr8_bound {v n : BitVec 64} (h : v.toNat < 256 ^ (8 - n.toNat)) (hnle : n.toNat ≤ 8)
    (hv : v ≠ 0) :
    n.toNat < 8 ∧ (v >>> (8 : BitVec 64).toNat).toNat < 256 ^ (8 - (n.toNat + 1)) := by
  have hn_lt : n.toNat < 8 := by
    by_contra hge
    have heq : 8 - n.toNat = 0 := by omega
    rw [heq, Nat.pow_zero] at h
    have hv0 : v.toNat = 0 := by omega
    exact hv (BitVec.eq_of_toNat_eq hv0)
  refine ⟨hn_lt, ?_⟩
  have hsh : (v >>> (8 : BitVec 64).toNat).toNat = v.toNat / 256 := by
    change v.toNat >>> 8 = v.toNat / 256
    rw [Nat.shiftRight_eq_div_pow]
  rw [hsh]
  have hpow : 256 ^ (8 - n.toNat) = 256 * 256 ^ (8 - (n.toNat + 1)) := by
    have he : 8 - n.toNat = 1 + (8 - (n.toNat + 1)) := by omega
    rw [he, Nat.pow_add, Nat.pow_one]
  rw [hpow] at h
  exact Nat.div_lt_of_lt_mul h

private def rlpBeLenLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
    (.seq
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))

private theorem eval_rlp_be_len_while {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (vw nw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "v") = some (.val (.word vw)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      nw.toNat ≤ 8 →
      vw.toNat < 256 ^ (8 - nw.toNat) →
      (evaluateHOLFiniteState s rlpBeLenLoop).1 ≠ some .timeOut →
      ∃ ll : BitVec 64,
        (evaluateHOLFiniteState s rlpBeLenLoop).1 = none ∧
        ll.toNat ≤ 8 ∧
        (vw ≠ 0 ∨ 0 < nw.toNat → 0 < ll.toNat) ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2.locals.lookup (ofString "n") = some (.val (.word ll)) ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2 =
          { s with locals := (evaluateHOLFiniteState s rlpBeLenLoop).2.locals,
                   clock := (evaluateHOLFiniteState s rlpBeLenLoop).2.clock } := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s vw nw hclk hv hn hn_le hv_lt hnt
    unfold rlpBeLenLoop at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) =
        some (.val (.word (if vw ≠ 0 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcond] at hnt ⊢
    dsimp only at hnt ⊢
    by_cases hvz : vw = 0
    · rw [if_neg (not_not.mpr hvz)] at hnt ⊢
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨nw, rfl, hn_le, fun h => h.elim (fun hc => absurd hvz hc) id, hn, by cases s; rfl⟩
    · rw [if_pos hvz] at hnt ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        obtain ⟨hn_lt8, hv'_lt⟩ := lsr8_bound hv_lt hn_le hvz
        have hstep : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
              (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))) := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hv_d : (decClockHOLFinite s).locals.lookup (ofString "v") = some (.val (.word vw)) := hv
          have hn_d : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word nw)) := hn
          have hne_vn : ofString "v" ≠ ofString "n" := by decide
          simp [evalHOLExact, evalListHOLExact, hv_d, hn_d, hne_vn, Ne.symm hne_vn,
            isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
            setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            evaluateHOLFiniteState_assign, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hstep] at hnt ⊢
        dsimp only at hnt ⊢
        set mid := setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
          (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))
        have hmid_clk : mid.clock < k := by
          simp [mid, setVarHOLFinite, decClockHOLFinite, hclk]; omega
        have hmid_v : mid.locals.lookup (ofString "v") = some (.val (.word (vw >>> (8 : BitVec 64).toNat))) := by
          have hne : ofString "n" ≠ ofString "v" := by decide
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
        have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word (nw + 1))) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hnw1 : (nw + 1).toNat = nw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (nw.toNat + 1) % 2 ^ 64 = _; omega
        obtain ⟨ll, hnone, hll8, hll_pos, hll_lk, hst_eq⟩ :=
          ih mid.clock hmid_clk mid (vw >>> (8 : BitVec 64).toNat) (nw + 1) rfl hmid_v hmid_n
            (by omega) (by rw [hnw1]; exact hv'_lt) hnt
        unfold rlpBeLenLoop at hnone hll_lk hst_eq
        refine ⟨ll, hnone, hll8, fun _ => hll_pos (Or.inr (by omega)), hll_lk, ?_⟩
        rw [hst_eq]; cases s; rfl

theorem eval_rlp_be_len_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vw : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 ≠
      some .timeOut) :
    ∃ ll : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 =
        some (.returned (.val (.word ll))) ∧
      ll.toNat ≤ 8 ∧
      (vw ≠ 0 → 0 < ll.toNat) ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_be_len =
      .dec (ofString "n") .one (.const 0)
        (.seq
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))))
          (.return (.var .local (ofString "n")))) := rfl
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
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hv]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hv_lt : vw.toNat < 256 ^ (8 - (0 : BitVec 64).toNat) := by
    have h256 : (256 ^ (8 - (0 : BitVec 64).toNat) : Nat) = 2 ^ 64 := by decide
    rw [h256]; exact vw.isLt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hl : evaluateHOLFiniteState s1 rlpBeLenLoop with ⟨rl, sl⟩
  have hnt_l : rl ≠ some .timeOut := by
    rintro rfl
    have hl' : evaluateHOLFiniteState s1
        (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
          (.seq
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))) =
        (some .timeOut, sl) := hl
    rw [hl'] at hnt; exact hnt rfl
  obtain ⟨ll, hnone, hll8, hll_pos, hsl_n, hsl_eq⟩ :=
    eval_rlp_be_len_while s1.clock s1 vw 0 rfl hs1_v hs1_n (by decide) hv_lt
      (by rw [hl]; exact hnt_l)
  rw [hl] at hnone hsl_n hsl_eq
  dsimp only at hnone hsl_n hsl_eq
  subst hnone
  have hl' : evaluateHOLFiniteState s1
      (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
        (.seq
          (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))) =
      (none, sl) := hl
  rw [hl']
  dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev_n : @evalHOLExact 64 F _ sl.toExact
      (fun a => Classical.propDecidable (sl.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word ll)) := by simp [evalHOLExact, hsl_n]
  rw [hev_n]; dsimp only
  have hsz : sizeOfShapeWithContextHOL sl.structs (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  refine ⟨ll, rfl, hll8, fun hnz => hll_pos (Or.inl hnz), ?_⟩
  rw [hsl_eq]; cases s; rfl

theorem eval_decCall_rlp_be_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp : ExpHOL 64) (vw : BitVec 64)
    (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).1 ≠ some .timeOut) :
    ∃ (ll : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      ll.toNat ≤ 8 ∧
      (vw ≠ 0 → 0 < ll.toNat) ∧
      mid.locals = s.locals.update (ofString lname, .val (.word ll)) ∧
      mid = { s with locals := mid.locals, clock := mid.clock } ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [vExp] =
      some [.val (.word vw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_rlp_be_len) vw (by rw [hcode]; exact lookup_rlp_be_len)
  simp only [hargs, hlook] at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hnt
  · simp only [hclk0, ↓reduceIte] at hnt ⊢
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw)))
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word vw)) := by
      simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState
          (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw))))
          (sourceFnBody Guest.Software.guestFn_rlp_be_len) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨ll, hbr, hll8, hll_pos, hbs_eq⟩ :=
      eval_rlp_be_len_body entry vw hent_v (by rw [hb]; exact hnt_b)
    rw [hb] at hbr hbs_eq
    dsimp only at hbr hbs_eq
    subst hbr
    have hb' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw))))
        (sourceFnBody Guest.Software.guestFn_rlp_be_len) =
        (some (.returned (.val (.word ll))), bs) := hb
    simp only [hb'] at hnt ⊢
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word ll)) { bs with locals := s.locals }
    refine ⟨ll, mid, hll8, hll_pos, rfl, ?_, hnt, rfl, rfl⟩
    dsimp only [mid, setVarHOLFinite]
    rw [hbs_eq]
    cases s; rfl

/-! ## 3. `ByteRegionEffect` of `rlp_put_be(dst, v, n)` when `dst.toNat + n.toNat < 2^64` -/

theorem eval_rlp_put_be_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 v0 n0 : BitVec 64)
    (Rl : List Ivl)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hv : s.locals.lookup (ofString "v") = some (.val (.word v0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)
    (∀ rv, out.1 = some (.returned rv) →
      rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_put_be =
      .dec (ofString "i") .one (.var .local (ofString "n"))
        (.seq
          (.while (.cmp .lower (.const 0) (.var .local (ofString "i")))
            (.seq
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
              (.seq
                (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                            (.var .local (ofString "v")))
                (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))))))
          (.return (.const 0))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev_n : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word n0)) := by simp [evalHOLExact, hn]
  have hsh_n : shapeEqHOL .one (shapeOfHOLExact (.val (.word n0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev_n] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh_n] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word n0)) s
  let P (t : PanSemStateFiniteExact 64 F) : Prop :=
    t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
    ∃ iw vw : BitVec 64,
      t.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      t.locals.lookup (ofString "v") = some (.val (.word vw)) ∧
      iw.toNat ≤ n0.toNat
  have hPs1 : P s1 := by
    refine ⟨?_, n0, v0, ?_, ?_, le_refl _⟩
    · have hne : ofString "i" ≠ ofString "dst" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hne : ofString "i" ≠ ofString "v" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hv]
  let wcond : ExpHOL 64 := ExpHOL.cmp .lower (.const 0) (.var .local (ofString "i"))
  let wbody : ProgHOL 64 := ProgHOL.seq
    (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
    (.seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                  (.var .local (ofString "v")))
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))))
  -- Show loop never raises ANY exception (not even `TrapErr`):
  have hloop_no_exn : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k →
      ∀ eid ev, (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.exception eid ev) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk eid ev
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond with _ | cv
      · simp
      · rcases cv with ⟨⟨cw⟩⟩ | _ | _
        · dsimp only
          split
          · split
            · simp
            · have hclk_b := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
              have hd_lt : (decClockHOLFinite t).clock < k := by simp [decClockHOLFinite, hclk]; omega
              -- `wbody` only has `assign .local` and `storeByte`: its `.1` can only be `none` or `some .error`!
              have hwb : (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = none ∨
                  (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = some .error := by
                dsimp only [wbody]
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                split
                · exact Or.inr rfl
                · split
                  · dsimp only
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_storeByte]
                    split
                    · split
                      · split
                        · dsimp only
                          rw [evaluateHOLFiniteState_assign]
                          split
                          · exact Or.inr rfl
                          · split <;> [exact Or.inl rfl; exact Or.inr rfl]
                        · exact Or.inr rfl
                      · exact Or.inr rfl
                    · exact Or.inr rfl
                  · exact Or.inr rfl
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, sb⟩
              rw [hbo] at hwb hclk_b
              rcases hwb with rfl | rfl
              · exact ih sb.clock (lt_of_le_of_lt hclk_b hd_lt) sb rfl eid ev
              · simp
          · simp
        · simp
        · simp
  -- Also use `eval_while_byteRegion` on `P`, except `P` needs `0 < iw.toNat` at body entry!
  -- Wait: `eval_while_byteRegion` passes `t = decClockHOLFinite s` ONLY when `cond` evaluated to non-zero,
  -- wait: `eval_while_byteRegion`'s `hbody` doesn't pass `cond ≠ 0`!
  -- Let's prove a specialized induction on `k` directly in 30 lines! It's MUCH shorter and gives `none` vs `error` directly!
  have hloop : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k → P t →
      (evaluateHOLFiniteState t (.while wcond wbody)).1 = none →
      ByteRegionEffect t (evaluateHOLFiniteState t (.while wcond wbody)).2 Rl := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk ⟨ht_dst, iw, vw, ht_i, ht_v, hiw_le⟩ hrun
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun ⊢
      have hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond =
          some (.val (.word (if (0 : BitVec 64) < iw then 1 else 0))) := by
        simp [wcond, evalHOLFinite, evalHOLExact, ht_i, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc] at hrun ⊢
      dsimp only at hrun ⊢
      by_cases hpos : (0 : BitVec 64) < iw
      · simp only [hpos, ↓reduceIte] at hrun ⊢
        have h10 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h10] at hrun ⊢
        by_cases hk0 : t.clock = 0
        · simp [hk0] at hrun
        · rw [if_neg hk0] at hrun ⊢
          have hiw_pos : 0 < iw.toNat := by
            rw [BitVec.lt_def] at hpos; exact hpos
          have hiw1 : (iw - 1).toNat = iw.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ iw.toNat; omega))]
            rfl
          -- Evaluate first `assign "i" := iw - 1`:
          let t0 := decClockHOLFinite t
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word iw)) := ht_i
          have hasg1 : evaluateHOLFiniteState t0
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0) := by
            rw [evaluateHOLFiniteState_assign]
            simp [evalHOLExact, evalListHOLExact, ht0_i, wordOpHOL, wordOp, valueIsWord, valueWord,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
          let t1 := setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0
          have ht1_dst : t1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            have hne : ofString "i" ≠ ofString "dst" := by decide
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_dst]
          have ht1_i : t1.locals.lookup (ofString "i") = some (.val (.word (iw - 1))) := by
            simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht1_v : t1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
            have hne : ofString "i" ≠ ofString "v" := by decide
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_v]
          have hclk_b := Flapjack.evaluateHOLFiniteState_clock_le t0 wbody
          have hd_lt : t0.clock < k := by simp [t0, decClockHOLFinite, hclk]; omega
          rcases hbo : evaluateHOLFiniteState t0 wbody with ⟨rb, sb⟩
          have hbo_raw : evaluateHOLFiniteState (decClockHOLFinite t) wbody = (rb, sb) := hbo
          simp only [hbo_raw] at hrun ⊢
          rw [hbo] at hclk_b
          -- Decompose `hbo` (`wbody = seq asg1 (seq sb_prog asg2)`):
          have hbo' := hbo
          dsimp only [wbody] at hbo'
          rw [evaluateHOLFiniteState_seq_line780, hasg1] at hbo'
          dsimp only at hbo'
          rw [evaluateHOLFiniteState_seq_line780] at hbo'
          rcases hsb_step : evaluateHOLFiniteState t1
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                          (.var .local (ofString "v"))) with ⟨rsb, t2⟩
          rw [hsb_step] at hbo'
          cases rsb with
          | some r' =>
            dsimp only at hbo'
            injection hbo' with hr_eq _
            subst hr_eq
            exfalso
            have hr_err : r' = .error := by
              rw [evaluateHOLFiniteState_storeByte] at hsb_step
              split at hsb_step
              · split at hsb_step
                · split at hsb_step
                  · simp at hsb_step
                  · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
                · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
              · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
            subst hr_err
            simp at hrun
          | none =>
            dsimp only at hbo'
            obtain ⟨heff_sb, ht2_loc⟩ := ByteRegionEffect.of_storeByte hsb_step (Rl := Rl) (fun addr hdst_ev _ => by
              have haddr_eq : addr = dst0 + (iw - 1) := by
                simp only [evalHOLExact, evalListHOLExact, ht1_dst, ht1_i, wordOpHOL, wordOp,
                  valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte,
                  List.foldr, BitVec.add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
                  HolWordLab.word.injEq] at hdst_ev
                simpa [BitVec.add_zero] using hdst_ev.symm
              subst haddr_eq
              obtain ⟨ivl, hivl, hlo, hhi⟩ := hin_ivl (by omega)
              have hadd_nat : (dst0 + (iw - 1)).toNat = dst0.toNat + (iw.toNat - 1) := by
                rw [BitVec.toNat_add, hiw1]
                exact Nat.mod_eq_of_lt (by omega)
              exact ⟨ivl, hivl, by omega, by omega⟩)
            have ht2_v : t2.locals.lookup (ofString "v") = some (.val (.word vw)) := by
              rw [ht2_loc]; exact ht1_v
            have hasg2 : evaluateHOLFiniteState t2
                (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
                (none, setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) := by
              rw [evaluateHOLFiniteState_assign]
              simp [evalHOLExact, ht2_v, wordShiftHOL, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg2] at hbo'
            injection hbo' with hr_eq hsb_eq
            subst hr_eq hsb_eq
            dsimp only at hrun ⊢
            have hPsb : P (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) := by
              refine ⟨?_, iw - 1, vw >>> (8 : BitVec 64).toNat, ?_, ?_, by omega⟩
              · have hne : ofString "v" ≠ ofString "dst" := by decide
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_loc, ht1_dst]
              · have hne : ofString "v" ≠ ofString "i" := by decide
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_loc, ht1_i]
              · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have heff_t_t1 : ByteRegionEffect t t1 Rl :=
              ByteRegionEffect.refl t Rl |>.with_locals_clock t1.locals t1.clock
            have heff_iter : ByteRegionEffect t (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) Rl :=
              (heff_t_t1.trans heff_sb).with_locals_clock _ t2.clock
            have jih := ih (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2).clock
              (lt_of_le_of_lt hclk_b hd_lt) _ rfl hPsb hrun
            exact heff_iter.trans jih
      · simp only [hpos, ↓reduceIte] at hrun ⊢
        have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
        rw [if_neg h00]
        exact ByteRegionEffect.refl t Rl
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hwl : evaluateHOLFiniteState s1 (.while wcond wbody) with ⟨rwl, swl⟩
  have hno_exn := hloop_no_exn s1.clock s1 rfl
  rw [hwl] at hno_exn
  have hwl_raw : evaluateHOLFiniteState s1
      (.while (.cmp .lower (.const 0) (.var .local (ofString "i")))
        (.seq
          (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                        (.var .local (ofString "v")))
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))))) =
      (rwl, swl) := hwl
  simp only [hwl_raw] at hnt ⊢
  cases rwl with
  | none =>
    dsimp only at hnt ⊢
    have heff_wl := hloop s1.clock s1 rfl hPs1 (by rw [hwl])
    rw [hwl] at heff_wl
    dsimp only at heff_wl
    rw [evaluateHOLFiniteState_return]
    have hev0 : @evalHOLExact 64 F _ swl.toExact
        (fun a => Classical.propDecidable (swl.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
    have hsz : sizeOfShapeWithContextHOL swl.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0]; dsimp only; rw [if_pos hsz]; dsimp only
    refine ⟨fun rv hrv => ?_, fun _ _ h => by simp at h⟩
    injection hrv with hrv'
    injection hrv' with hrv''
    have heff_s_s1 : ByteRegionEffect s s1 Rl :=
      ByteRegionEffect.refl s Rl |>.with_locals_clock s1.locals s1.clock
    exact ⟨hrv''.symm, (heff_s_s1.trans heff_wl).with_locals_clock _ _⟩
  | some r =>
    dsimp only at hnt ⊢
    cases r with
    | timeOut => exact absurd rfl hnt
    | exception eid ev => exact absurd rfl (hno_exn eid ev)
    | returned v =>
      -- `while` never returns `.returned` unless body returns `.returned`, which `wbody` cannot!
      exfalso
      -- Prove `while` with `wbody` never returns `.returned`:
      have hno_ret : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k →
          ∀ val, (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned val) := by
        intro k
        induction k using Nat.strong_induction_on with
        | h k ih =>
          intro t hclk val
          rw [evaluateHOLFiniteState_while_fixClockRewrite]
          rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond with _ | cv
          · simp
          · rcases cv with ⟨⟨cw⟩⟩ | _ | _
            · dsimp only
              split
              · split
                · simp
                · have hclk_b := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
                  have hd_lt : (decClockHOLFinite t).clock < k := by simp [decClockHOLFinite, hclk]; omega
                  have hwb : (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = none ∨
                      (evaluateHOLFiniteState (decClockHOLFinite t) wbody).1 = some .error := by
                    dsimp only [wbody]
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                    split
                    · exact Or.inr rfl
                    · split
                      · dsimp only
                        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_storeByte]
                        split
                        · split
                          · split
                            · dsimp only
                              rw [evaluateHOLFiniteState_assign]
                              split
                              · exact Or.inr rfl
                              · split <;> [exact Or.inl rfl; exact Or.inr rfl]
                            · exact Or.inr rfl
                          · exact Or.inr rfl
                        · exact Or.inr rfl
                      · exact Or.inr rfl
                  rcases hbo : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, sb⟩
                  rw [hbo] at hwb hclk_b
                  rcases hwb with rfl | rfl
                  · exact ih sb.clock (lt_of_le_of_lt hclk_b hd_lt) sb rfl val
                  · simp
              · simp
            · simp
            · simp
      exact hno_ret s1.clock s1 rfl v (by rw [hwl])
    | _ => exact ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem eval_call_rlp_put_be {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp vExp nExp : ExpHOL 64)
    (dst0 v0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word v0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, vExp, nExp] =
      some [.val (.word dst0), .val (.word v0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hv, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "rlp_put_be")
    (ofString "dst") (ofString "v") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_put_be) dst0 v0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_rlp_put_be)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "v", ValueHOL.val (.word v0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "v" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word v0)) := by
      have h1 : ofString "n" ≠ ofString "v" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_put_be) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_rlp_put_be) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨hret, hexn⟩ := eval_rlp_put_be_body entry dst0 v0 n0 Rl hent_dst hent_v hent_n hfit hin_ivl
      (by rw [hb]; exact hnt_b)
    rw [hb] at hret hexn
    dsimp only at hret hexn
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b⟩ := hret rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl⟩,
          fun h => False.elim (h rfl)⟩
      | _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## 4. `ByteRegionEffect` of `memcpy` (body and `call`) -/

private theorem bv_add_small (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

private theorem seq_none_or_err_bre {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c1 c2 : ProgHOL 64} {Rl : List Ivl}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hc1 : (∀ m, evaluateHOLFiniteState s c1 = (none, m) → ByteRegionEffect s m Rl) ∧
           (∀ r, r ≠ none → (evaluateHOLFiniteState s c1).1 = r → r = some .error))
    (hc2 : ∀ m, evaluateHOLFiniteState s c1 = (none, m) → ByteRegionEffect s m Rl →
           (∀ p, evaluateHOLFiniteState m c2 = (none, p) → Q p ∧ ByteRegionEffect m p Rl) ∧
           (∀ r, r ≠ none → (evaluateHOLFiniteState m c2).1 = r → r = some .error)) :
    (∀ p, evaluateHOLFiniteState s (.seq c1 c2) = (none, p) → Q p ∧ ByteRegionEffect s p Rl) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState s (.seq c1 c2)).1 = r → r = some .error) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s c1 with ⟨r1, m⟩
  cases r1 with
  | none =>
    dsimp only
    have he1 := hc1.1 m h1
    obtain ⟨h2n, h2e⟩ := hc2 m h1 he1
    exact ⟨fun p hp => ⟨(h2n p hp).1, he1.trans (h2n p hp).2⟩, h2e⟩
  | some r =>
    dsimp only
    have herr : some r = some .error := hc1.2 (some r) (by simp) (by rw [h1])
    exact ⟨fun _ hp => by simp at hp, fun r' _ hr' => by rw [← hr', herr]⟩

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [he, memLoadHOLExact] at hv
      by_cases hdom : s.memaddrs addr
      · simp only [hdom, ↓reduceIte] at hv
        cases hm : s.memory addr with
        | word w =>
          rw [hm] at hv
          injection hv with hv'
          exact ⟨w, hv'.symm⟩
      · simp [hdom] at hv
    · simp [he] at hv
    · simp [he] at hv

private theorem memcpy_word_store_step {F : Type}
    {st : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst iv _n : BitVec 64} {addrExp rhs : ExpHOL 64} {c : Nat}
    (hma : st.memaddrs = ordinaryDomain)
    (hsub : dst.toNat + iv.toNat + c + 8 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst.toNat + (iv.toNat + c) ∧ dst.toNat + (iv.toNat + c) + 8 ≤ ivl.1 + ivl.2)
    (hrhs_word : ∀ v, @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) rhs = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) addrExp =
      some (.val (.word (dst + (iv + BitVec.ofNat 64 c)))))
    (hprev_dom : (iv.toNat + c > 0 → dst.toNat + iv.toNat + c ≤ 33806089704) ∧ iv.toNat + c < 2 ^ 64) :
    (∀ sm, evaluateHOLFiniteState st (.store addrExp rhs) = (none, sm) →
      ByteRegionEffect st sm Rl ∧ sm.locals = st.locals ∧
      dst.toNat + iv.toNat + c + 8 ≤ 33806089704) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState st (.store addrExp rhs)).1 = r → r = some .error) := by
  have hsum_ivc : (iv + BitVec.ofNat 64 c).toNat = iv.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hc_mod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
    rw [hc_mod]
    exact Nat.mod_eq_of_lt hprev_dom.2
  have haddr_nat : (dst + (iv + BitVec.ofNat 64 c)).toNat = dst.toNat + (iv.toNat + c) := by
    by_cases hz : iv.toNat + c = 0
    · have h0 : iv + BitVec.ofNat 64 c = 0 := BitVec.eq_of_toNat_eq (by rw [hsum_ivc, hz]; rfl)
      have hd0 : dst + (0 : BitVec 64) = dst := BitVec.add_zero dst
      rw [h0, hd0, hz, Nat.add_zero]
    · have hle := hprev_dom.1 (by omega)
      rw [bv_add_small dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
  refine ⟨fun sm hsm => ?_, ?_⟩
  · have hsm' := hsm
    rw [evaluateHOLFiniteState_store, haddr] at hsm'
    dsimp only at hsm'
    rcases hv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) rhs with _ | v
    · simp [hv] at hsm'
    · rw [hv] at hsm'
      obtain ⟨w, rfl⟩ := hrhs_word v hv
      dsimp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hsm'
      by_cases hdom : st.memaddrs (dst + (iv + BitVec.ofNat 64 c))
      · have hd := word_dom_lt_heapEnd hma _ hdom
        rw [heapEnd_val, haddr_nat] at hd
        have hbnd8 : dst.toNat + iv.toNat + c + 8 ≤ 33806089704 := by omega
        obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word hma hsm hrhs_word (fun addr ha _ => by
          rw [haddr] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
          rw [haddr_nat]
          exact hsub hbnd8)
        exact ⟨heff, hloc, hbnd8⟩
      · unfold flattenHOL panMemStoresHOL panMemStoreHOL at hsm'
        simp [hdom] at hsm'
  · intro r hrne hreq
    rw [evaluateHOLFiniteState_store] at hreq
    split at hreq
    · split at hreq
      · split at hreq
        · simp at hreq; exact absurd hreq.symm hrne
        · exact hreq.symm
      · exact hreq.symm
    · exact hreq.symm

private theorem memcpy_byte_store_step {F : Type}
    {st : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst iv _n : BitVec 64} {addrExp rhs : ExpHOL 64} {c : Nat}
    (hma : st.memaddrs = ordinaryDomain)
    (hsub : dst.toNat + iv.toNat + c + 1 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst.toNat + (iv.toNat + c) ∧ dst.toNat + (iv.toNat + c) < ivl.1 + ivl.2)
    (haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) addrExp =
      some (.val (.word (dst + (iv + BitVec.ofNat 64 c)))))
    (hprev_dom : (iv.toNat + c > 0 → dst.toNat + iv.toNat + c ≤ 33806089704) ∧ iv.toNat + c < 2 ^ 64) :
    (∀ sm, evaluateHOLFiniteState st (.storeByte addrExp rhs) = (none, sm) →
      ByteRegionEffect st sm Rl ∧ sm.locals = st.locals ∧
      dst.toNat + iv.toNat + c + 1 ≤ 33806089704) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState st (.storeByte addrExp rhs)).1 = r → r = some .error) := by
  have hsum_ivc : (iv + BitVec.ofNat 64 c).toNat = iv.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hc_mod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
    rw [hc_mod]
    exact Nat.mod_eq_of_lt hprev_dom.2
  have haddr_nat : (dst + (iv + BitVec.ofNat 64 c)).toNat = dst.toNat + (iv.toNat + c) := by
    by_cases hz : iv.toNat + c = 0
    · have h0 : iv + BitVec.ofNat 64 c = 0 := BitVec.eq_of_toNat_eq (by rw [hsum_ivc, hz]; rfl)
      have hd0 : dst + (0 : BitVec 64) = dst := BitVec.add_zero dst
      rw [h0, hd0, hz, Nat.add_zero]
    · have hle := hprev_dom.1 (by omega)
      rw [bv_add_small dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
  refine ⟨fun sm hsm => ?_, ?_⟩
  · have hsm' := hsm
    rw [evaluateHOLFiniteState_storeByte, haddr] at hsm'
    dsimp only at hsm'
    split at hsm'
    · split at hsm'
      · rename_i m' hst
        unfold panMemStoreByteWord8HOL at hst
        dsimp only at hst
        cases hm : st.memory (panByteAlignHOL (dst + (iv + BitVec.ofNat 64 c))) with
        | word cell =>
          by_cases hdom : st.memaddrs (panByteAlignHOL (dst + (iv + BitVec.ofNat 64 c)))
          · have hd := (byteAlign_lt_heapEnd hma _ hdom).2
            rw [heapEnd_val, haddr_nat] at hd
            have hbnd1 : dst.toNat + iv.toNat + c + 1 ≤ 33806089704 := by omega
            obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_storeByte hsm (Rl := Rl) (fun addr ha _ => by
              rw [haddr] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
              rw [haddr_nat]
              exact hsub hbnd1)
            exact ⟨heff, hloc, hbnd1⟩
          · simp [hm, hdom] at hst
      · simp at hsm'
    · simp at hsm'
  · intro r hrne hreq
    rw [evaluateHOLFiniteState_storeByte] at hreq
    split at hreq
    · split at hreq
      · split at hreq
        · simp at hreq; exact absurd hreq.symm hrne
        · exact hreq.symm
      · exact hreq.symm
    · exact hreq.symm

private def MemcpyBreInv {F : Type} (dst n : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.memaddrs = ordinaryDomain ∧
  t.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
  t.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  ∃ iv : BitVec 64,
    t.locals.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat ≤ n.toNat ∧
    iv.toNat ≤ 33806089704 ∧
    (iv.toNat > 0 → dst.toNat + iv.toNat ≤ 33806089704)

private theorem memcpy_loop_runner {F : Type}
    (Rl : List Ivl) (dst n : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F),
      MemcpyBreInv dst n s →
      ∃ cv : BitVec 64,
        @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond =
          some (.val (.word cv)) ∧
        (cv ≠ 0 →
          (∀ sb, evaluateHOLFiniteState (decClockHOLFinite s) body = (none, sb) →
            MemcpyBreInv dst n sb ∧
            ByteRegionEffect (decClockHOLFinite s) sb Rl) ∧
          (∀ r, r ≠ none → (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = r →
            r = some .error)))
    (s0 : PanSemStateFiniteExact 64 F)
    (hinv : MemcpyBreInv dst n s0)
    (hnt : (evaluateHOLFiniteState s0 (.while cond body)).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s0 (.while cond body)).1 = none →
      MemcpyBreInv dst n (evaluateHOLFiniteState s0 (.while cond body)).2 ∧
      ByteRegionEffect s0 (evaluateHOLFiniteState s0 (.while cond body)).2 Rl) ∧
    ((evaluateHOLFiniteState s0 (.while cond body)).1 ≠ none →
      (evaluateHOLFiniteState s0 (.while cond body)).1 = some .error) := by
  suffices hmain : ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k →
      MemcpyBreInv dst n s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s (.while cond body)).1 = none →
        MemcpyBreInv dst n (evaluateHOLFiniteState s (.while cond body)).2 ∧
        ByteRegionEffect s (evaluateHOLFiniteState s (.while cond body)).2 Rl) ∧
      ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
        (evaluateHOLFiniteState s (.while cond body)).1 = some .error) by
    exact hmain s0.clock s0 rfl hinv hnt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt_s
    obtain ⟨cv, hc, hbody_step⟩ := hstep s hPs
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt_s ⊢
    simp only [hc] at hnt_s ⊢
    by_cases hcv : cv = 0
    · subst hcv
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨fun _ => ⟨hPs, ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩
    · rw [if_pos hcv] at hnt_s ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt_s
      · rw [if_neg hk0] at hnt_s ⊢
        obtain ⟨hb_none, hb_err⟩ := hbody_step hcv
        have heff_dec : ByteRegionEffect s (decClockHOLFinite s) Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock s.locals (s.clock - 1)
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        have hd_clk : (decClockHOLFinite s).clock < k := by
          simp [decClockHOLFinite, hclk]; omega
        rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
        simp only [hbo] at hnt_s hb_clk ⊢
        cases rb with
        | none =>
          dsimp only at hnt_s hb_clk ⊢
          obtain ⟨hPsb, heff_b⟩ := hb_none sb hbo
          have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt_s
          exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_b).trans (jih.1 hn).2⟩, jih.2⟩
        | some r =>
          have herr := hb_err (some r) (by simp) (by rw [hbo])
          injection herr with hr; subst hr
          exact ⟨fun h => by simp at h, fun _ => rfl⟩

private theorem eval_add2_di {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d iv : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
      some (.val (.word (d + (iv + BitVec.ofNat 64 0)))) := by
  simp only [evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  rfl

private theorem eval_add3_dic {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d iv : BitVec 64) (c : Nat)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 c)]) =
      some (.val (.word (d + (iv + BitVec.ofNat 64 c)))) := by
  simp only [evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  congr 3
  have hz : BitVec.ofNat 64 c + (0 : BitVec 64) = BitVec.ofNat 64 c := BitVec.add_zero _
  exact congrArg (fun x => d + (iv + x)) hz

private theorem assign_i_bre_step {F : Type} (st : PanSemStateFiniteExact 64 F)
    (dst iv n : BitVec 64) (step : Nat) (Rl : List Ivl)
    (hma : st.memaddrs = ordinaryDomain)
    (hdst : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : st.locals.lookup (ofString "i") = some (.val (.word iv)))
    (_hstep_pos : 0 < step)
    (hle : iv.toNat + step ≤ n.toNat)
    (hdom : dst.toNat + iv.toNat + step ≤ 33806089704) :
    (∀ p, evaluateHOLFiniteState st
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) = (none, p) →
      MemcpyBreInv dst n p ∧ ByteRegionEffect st p Rl) ∧
    (∀ r, r ≠ none →
      (evaluateHOLFiniteState st
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]))).1 = r →
      r = some .error) := by
  have hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]) =
      some (.val (.word (iv + BitVec.ofNat 64 step))) := by
    simp only [evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    congr 3
    have hz : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
    exact congrArg (fun x => iv + x) hz
  have hvld : isValidValueHOLFinite st .local (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi, shapeOfHOLExact, shapeEqHOL]
  have hrun : evaluateHOLFiniteState st
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) st) := by
    rw [evaluateHOLFiniteState_assign, hev]
    dsimp only; rw [if_pos hvld]; rfl
  have hiv_add : (iv + BitVec.ofNat 64 step).toNat = iv.toNat + step := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hs_mod : step % 2 ^ 64 = step := Nat.mod_eq_of_lt (by omega)
    rw [hs_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hrun]
  refine ⟨fun p hp => ?_, fun r hrne hr => absurd hr.symm hrne⟩
  injection hp with _ hp_eq; subst hp_eq
  refine ⟨⟨hma, ?_, ?_, iv + BitVec.ofNat 64 step, ?_, by omega, by omega, fun _ => by omega⟩,
    ByteRegionEffect.refl st Rl |>.with_locals_clock _ st.clock⟩
  · have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  · have hne : ofString "i" ≠ ofString "n" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- Full body evaluation of `memcpy`: when every offset `off < n0.toNat` with `dst0.toNat + off < heapEnd`
lies inside some `ivl ∈ Rl` (`hsub : ∀ k, k < n0.toNat → dst0.toNat + k < 33806089704 → ...`),
every resuming run of `memcpy` produces `ByteRegionEffect s out.2 Rl`, and `memcpy` never raises
an exception. -/
theorem eval_memcpy_body_bre_gen {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hsub_w : ∀ off, off + 8 ≤ n0.toNat → dst0.toNat + off + 8 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off + 8 ≤ ivl.1 + ivl.2)
    (hsub_b : ∀ off, off < n0.toNat → dst0.toNat + off + 1 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off < ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)
    (Resumes out.1 → ByteRegionEffect s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  have hs1_src : s1.locals.lookup (ofString "src") = some (.val (.word src0)) := by
    have hne : ofString "i" ≠ ofString "src" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hsrc]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hinv1 : MemcpyBreInv dst0 n0 s1 :=
    ⟨hma, hs1_dst, hs1_n, 0, hs1_i, Nat.zero_le _, Nat.zero_le _, fun h => by simp at h⟩
  have heff_s_s1 : ByteRegionEffect s s1 Rl :=
    ByteRegionEffect.refl s Rl |>.with_locals_clock s1.locals s1.clock
  -- Helper for `notLower n (i + step)` condition:
  have hcond_nl : ∀ (t : PanSemStateFiniteExact 64 F) (iv : BitVec 64) (step : Nat),
      t.locals.lookup (ofString "n") = some (.val (.word n0)) →
      t.locals.lookup (ofString "i") = some (.val (.word iv)) →
      iv.toNat ≤ 33806089704 → step ≤ 32 →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) =
        some (.val (.word (if iv.toNat + step ≤ n0.toNat then 1 else 0))) := by
    intro t iv step htn hti hiv_le hst_le
    rw [evalHOLFinite_eq_toExact]
    have hz_s : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
    have hadd : (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat = iv.toNat + step := by
      rw [hz_s, BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs_mod : step % 2 ^ 64 = step := Nat.mod_eq_of_lt (by omega)
      rw [hs_mod]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [evalHOLExact, evalListHOLExact, htn, hti, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Bool.not_eq_true', decide_eq_false_iff_not]
    change some (ValueHOL.val (HolWordLab.word (if ¬n0.toNat < (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat then 1 else 0))) = _
    rw [hadd]
    by_cases hle : iv.toNat + step ≤ n0.toNat
    · have hnl : ¬ (n0.toNat < iv.toNat + step) := by omega
      simp [hle, hnl]
    · have hlt : n0.toNat < iv.toNat + step := by omega
      simp [hle, hlt]
  -- Loop 1 (32-byte word loop):
  let lp1 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])
                  (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)])))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))))))
  have hL1 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp1).1 = none →
        MemcpyBreInv dst0 n0 (evaluateHOLFiniteState t0 lp1).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp1).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp1).1 ≠ none → (evaluateHOLFiniteState t0 lp1).1 = some .error) := by
    intro t0 hinv0 hnt1
    refine memcpy_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt1
    refine ⟨if iv.toNat + 32 ≤ n0.toNat then 1 else 0, hcond_nl st iv 32 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle32 : iv.toNat + 32 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have hd0_ma : d0.memaddrs = ordinaryDomain := st_ma
    have hd0_dst : d0.locals.lookup (ofString "dst") = some (.val (.word dst0)) := st_dst
    have hd0_n : d0.locals.lookup (ofString "n") = some (.val (.word n0)) := st_n
    have hd0_i : d0.locals.lookup (ofString "i") = some (.val (.word iv)) := st_i
    have w0 := memcpy_word_store_step (st := d0) (Rl := Rl) (_n := n0) (c := 0)
      (rhs := .load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
      hd0_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_load_one_word d0 _) (eval_add2_di d0 dst0 iv hd0_dst hd0_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1
    obtain ⟨_, hm1_loc, hdom8⟩ := w0.1 m1 hm1
    have hm1_ma : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans hd0_ma
    have hm1_dst : m1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hm1_loc.symm ▸ hd0_dst
    have hm1_i : m1.locals.lookup (ofString "i") = some (.val (.word iv)) := hm1_loc.symm ▸ hd0_i
    have w8 := memcpy_word_store_step (st := m1) (Rl := Rl) (_n := n0) (c := 8)
      (rhs := .load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
      hm1_ma (fun hb => hsub_w (iv.toNat + 8) (by omega) (by omega))
      (eval_load_one_word m1 _) (eval_add3_dic m1 dst0 iv 8 hm1_dst hm1_i)
      ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w8.1 m hm).1, w8.2⟩
    intro m2 hm2 he2
    obtain ⟨_, hm2_loc, hdom16⟩ := w8.1 m2 hm2
    have hm2_ma : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans hm1_ma
    have hm2_dst : m2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hm2_loc.symm ▸ hm1_dst
    have hm2_i : m2.locals.lookup (ofString "i") = some (.val (.word iv)) := hm2_loc.symm ▸ hm1_i
    have w16 := memcpy_word_store_step (st := m2) (Rl := Rl) (_n := n0) (c := 16)
      (rhs := .load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)]))
      hm2_ma (fun hb => hsub_w (iv.toNat + 16) (by omega) (by omega))
      (eval_load_one_word m2 _) (eval_add3_dic m2 dst0 iv 16 hm2_dst hm2_i)
      ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w16.1 m hm).1, w16.2⟩
    intro m3 hm3 he3
    obtain ⟨_, hm3_loc, hdom24⟩ := w16.1 m3 hm3
    have hm3_ma : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans hm2_ma
    have hm3_dst : m3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hm3_loc.symm ▸ hm2_dst
    have hm3_i : m3.locals.lookup (ofString "i") = some (.val (.word iv)) := hm3_loc.symm ▸ hm2_i
    have w24 := memcpy_word_store_step (st := m3) (Rl := Rl) (_n := n0) (c := 24)
      (rhs := .load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)]))
      hm3_ma (fun hb => hsub_w (iv.toNat + 24) (by omega) (by omega))
      (eval_load_one_word m3 _) (eval_add3_dic m3 dst0 iv 24 hm3_dst hm3_i)
      ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w24.1 m hm).1, w24.2⟩
    intro m4 hm4 he4
    obtain ⟨_, hm4_loc, hdom32⟩ := w24.1 m4 hm4
    exact assign_i_bre_step m4 dst0 iv n0 32 Rl (he4.memaddrs.trans hm3_ma)
      (hm4_loc.symm ▸ hm3_dst)
      (by rw [hm4_loc, hm3_loc, hm2_loc, hm1_loc]; exact hd0_n)
      (hm4_loc.symm ▸ hm3_i) (by omega) hle32 (by omega)
  -- Loop 2 (8-byte word loop):
  let lp2 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])) )
  have hL2 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp2).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp2).1 = none →
        MemcpyBreInv dst0 n0 (evaluateHOLFiniteState t0 lp2).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp2).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp2).1 ≠ none → (evaluateHOLFiniteState t0 lp2).1 = some .error) := by
    intro t0 hinv0 hnt2
    refine memcpy_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt2
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have w0 := memcpy_word_store_step (st := d0) (Rl := Rl) (_n := n0) (c := 0)
      (rhs := .load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
      st_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_load_one_word d0 _) (eval_add2_di d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1
    obtain ⟨_, hm1_loc, hdom8⟩ := w0.1 m1 hm1
    exact assign_i_bre_step m1 dst0 iv n0 8 Rl (he1.memaddrs.trans st_ma)
      (hm1_loc.symm ▸ st_dst) (hm1_loc.symm ▸ st_n) (hm1_loc.symm ▸ st_i)
      (by omega) hle8 (by omega)
  -- Loop 3 (8-byte byte loop):
  let lp3 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)])
                          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))))))))))
  have hL3 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp3).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp3).1 = none →
        MemcpyBreInv dst0 n0 (evaluateHOLFiniteState t0 lp3).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp3).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp3).1 ≠ none → (evaluateHOLFiniteState t0 lp3).1 = some .error) := by
    intro t0 hinv0 hnt3
    refine memcpy_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt3
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memcpy_byte_store_step (st := d0) (Rl := Rl) (_n := n0) (c := 0)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    have ma1 : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans st_ma
    have b1 := memcpy_byte_store_step (st := m1) (Rl := Rl) (_n := n0) (c := 1)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))
      ma1 (fun hb => hsub_b (iv.toNat + 1) (by omega) (by omega))
      (eval_add3_dic m1 dst0 iv 1 (l1.symm ▸ st_dst) (l1.symm ▸ st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b1.1 m hm).1, b1.2⟩
    intro m2 hm2 he2; obtain ⟨_, l2, dom2⟩ := b1.1 m2 hm2
    have ma2 : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans ma1
    have b2 := memcpy_byte_store_step (st := m2) (Rl := Rl) (_n := n0) (c := 2)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)]))
      ma2 (fun hb => hsub_b (iv.toNat + 2) (by omega) (by omega))
      (eval_add3_dic m2 dst0 iv 2 (by rw [l2, l1]; exact st_dst) (by rw [l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b2.1 m hm).1, b2.2⟩
    intro m3 hm3 he3; obtain ⟨_, l3, dom3⟩ := b2.1 m3 hm3
    have ma3 : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans ma2
    have b3 := memcpy_byte_store_step (st := m3) (Rl := Rl) (_n := n0) (c := 3)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)]))
      ma3 (fun hb => hsub_b (iv.toNat + 3) (by omega) (by omega))
      (eval_add3_dic m3 dst0 iv 3 (by rw [l3, l2, l1]; exact st_dst) (by rw [l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b3.1 m hm).1, b3.2⟩
    intro m4 hm4 he4; obtain ⟨_, l4, dom4⟩ := b3.1 m4 hm4
    have ma4 : m4.memaddrs = ordinaryDomain := he4.memaddrs.trans ma3
    have b4 := memcpy_byte_store_step (st := m4) (Rl := Rl) (_n := n0) (c := 4)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)]))
      ma4 (fun hb => hsub_b (iv.toNat + 4) (by omega) (by omega))
      (eval_add3_dic m4 dst0 iv 4 (by rw [l4, l3, l2, l1]; exact st_dst) (by rw [l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b4.1 m hm).1, b4.2⟩
    intro m5 hm5 he5; obtain ⟨_, l5, dom5⟩ := b4.1 m5 hm5
    have ma5 : m5.memaddrs = ordinaryDomain := he5.memaddrs.trans ma4
    have b5 := memcpy_byte_store_step (st := m5) (Rl := Rl) (_n := n0) (c := 5)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)]))
      ma5 (fun hb => hsub_b (iv.toNat + 5) (by omega) (by omega))
      (eval_add3_dic m5 dst0 iv 5 (by rw [l5, l4, l3, l2, l1]; exact st_dst) (by rw [l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b5.1 m hm).1, b5.2⟩
    intro m6 hm6 he6; obtain ⟨_, l6, dom6⟩ := b5.1 m6 hm6
    have ma6 : m6.memaddrs = ordinaryDomain := he6.memaddrs.trans ma5
    have b6 := memcpy_byte_store_step (st := m6) (Rl := Rl) (_n := n0) (c := 6)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)]))
      ma6 (fun hb => hsub_b (iv.toNat + 6) (by omega) (by omega))
      (eval_add3_dic m6 dst0 iv 6 (by rw [l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b6.1 m hm).1, b6.2⟩
    intro m7 hm7 he7; obtain ⟨_, l7, dom7⟩ := b6.1 m7 hm7
    have ma7 : m7.memaddrs = ordinaryDomain := he7.memaddrs.trans ma6
    have b7 := memcpy_byte_store_step (st := m7) (Rl := Rl) (_n := n0) (c := 7)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)]))
      ma7 (fun hb => hsub_b (iv.toNat + 7) (by omega) (by omega))
      (eval_add3_dic m7 dst0 iv 7 (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b7.1 m hm).1, b7.2⟩
    intro m8 hm8 he8; obtain ⟨_, l8, dom8⟩ := b7.1 m8 hm8
    exact assign_i_bre_step m8 dst0 iv n0 8 Rl (he8.memaddrs.trans ma7)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_dst)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_n)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_i)
      (by omega) hle8 (by omega)
  -- Loop 4 (1-byte byte loop):
  let lp4 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
  have hL4 : ∀ t0 : PanSemStateFiniteExact 64 F, MemcpyBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp4).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp4).1 = none →
        MemcpyBreInv dst0 n0 (evaluateHOLFiniteState t0 lp4).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp4).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp4).1 ≠ none → (evaluateHOLFiniteState t0 lp4).1 = some .error) := by
    intro t0 hinv0 hnt4
    refine memcpy_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt4
    have hc4 : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iv.toNat < n0.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, st_i, st_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    refine ⟨if iv.toNat < n0.toNat then 1 else 0, hc4, fun hcv => ?_⟩
    have hlt1 : iv.toNat < n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memcpy_byte_store_step (st := d0) (Rl := Rl) (_n := n0) (c := 0)
      (rhs := .loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")]))
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    exact assign_i_bre_step m1 dst0 iv n0 1 Rl (he1.memaddrs.trans st_ma)
      (l1.symm ▸ st_dst) (l1.symm ▸ st_n) (l1.symm ▸ st_i)
      (by omega) (by omega) (by omega)
  -- Sequence `ite` -> `lp3` -> `lp4` -> `return 0`:
  let iteP : ProgHOL 64 := .ite
    (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0)))
    (.seq lp1 lp2)
    .skip
  have hite_spec : ∀ t0 : PanSemStateFiniteExact 64 F,
      MemcpyBreInv dst0 n0 t0 →
      t0.locals.lookup (ofString "src") = some (.val (.word src0)) →
      (evaluateHOLFiniteState t0 iteP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 iteP).1 = none →
        MemcpyBreInv dst0 n0 (evaluateHOLFiniteState t0 iteP).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 iteP).2 Rl) ∧
      ((evaluateHOLFiniteState t0 iteP).1 ≠ none → (evaluateHOLFiniteState t0 iteP).1 = some .error) := by
    intro t0 hinv0 hsrc0 hnt_i
    dsimp only [iteP] at hnt_i ⊢
    rw [evaluateHOLFiniteState_ite] at hnt_i ⊢
    rcases hcond_ev : @evalHOLExact 64 F _ t0.toExact (fun a => Classical.propDecidable (t0.memaddrs a))
        (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0))) with _ | cv
    · simp only [hcond_ev] at hnt_i ⊢
      exact ⟨fun h => by simp at h, fun _ => by simp⟩
    · have hcv_w : ∃ cw : BitVec 64, cv = .val (.word cw) := by
        simp [evalHOLExact, evalListHOLExact, hinv0.2.1, hsrc0, wordOpHOL, wordOp, valueIsWord, valueWord,
          Compiler.Encoders.Asm.wordCmpHOL] at hcond_ev
        exact ⟨_, hcond_ev.symm⟩
      obtain ⟨cw, rfl⟩ := hcv_w
      simp only [hcond_ev] at hnt_i ⊢
      by_cases hcw0 : cw = 0
      · rw [if_pos hcw0, evaluateHOLFiniteState_skip]
        exact ⟨fun _ => ⟨hinv0, ByteRegionEffect.refl t0 Rl⟩, fun h => False.elim (h rfl)⟩
      · rw [if_neg hcw0] at hnt_i ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt_i ⊢
        rcases hr1 : evaluateHOLFiniteState t0 lp1 with ⟨r1, m1⟩
        have hnt1 : r1 ≠ some .timeOut := by rintro rfl; rw [hr1] at hnt_i; exact hnt_i rfl
        have hs1_res := hL1 t0 hinv0 (by rw [hr1]; exact hnt1)
        rw [hr1] at hs1_res
        simp only [hr1] at hnt_i ⊢
        cases r1 with
        | some r => exact ⟨fun h => by simp at h, hs1_res.2⟩
        | none =>
          dsimp only at hnt_i ⊢
          obtain ⟨hm1_inv, he1⟩ := hs1_res.1 rfl
          have hs2_res := hL2 m1 hm1_inv hnt_i
          exact ⟨fun hn => ⟨(hs2_res.1 hn).1, he1.trans (hs2_res.1 hn).2⟩, hs2_res.2⟩
  change (let out := (let res := evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))
    (res.1, { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "i", s.locals.lookup (ofString "i")) }))
    (Resumes out.1 → ByteRegionEffect s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)))
  have hnt' : (evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))).1 ≠
      some .timeOut := hnt
  clear hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
  rcases h_ite : evaluateHOLFiniteState s1 iteP with ⟨r_ite, s2⟩
  simp only [h_ite] at hnt' ⊢
  have hnt_ite : r_ite ≠ some .timeOut := by rintro rfl; exact hnt' rfl
  have hs_ite := hite_spec s1 hinv1 hs1_src (by rw [h_ite]; exact hnt_ite)
  rw [h_ite] at hs_ite
  cases r_ite with
  | some r =>
    dsimp only at hnt' ⊢
    have herr := hs_ite.2 (by simp)
    injection herr with hr_eq; subst hr_eq
    exact ⟨fun hr => False.elim (not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  | none =>
    dsimp only at hnt' ⊢
    obtain ⟨hinv2, heff2⟩ := hs_ite.1 rfl
    rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
    rcases h_l3 : evaluateHOLFiniteState s2 lp3 with ⟨rl3, s3⟩
    simp only [h_l3] at hnt' ⊢
    have hnt_l3 : rl3 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
    have hs_l3 := hL3 s2 hinv2 (by rw [h_l3]; exact hnt_l3)
    rw [h_l3] at hs_l3
    cases rl3 with
    | some r =>
      dsimp only at hnt' ⊢
      have herr := hs_l3.2 (by simp)
      injection herr with hr_eq; subst hr_eq
      exact ⟨fun hr => False.elim (not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
    | none =>
      dsimp only at hnt' ⊢
      obtain ⟨hinv3, heff3⟩ := hs_l3.1 rfl
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      rcases h_l4 : evaluateHOLFiniteState s3 lp4 with ⟨rl4, s4⟩
      simp only [h_l4] at hnt' ⊢
      have hnt_l4 : rl4 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
      have hs_l4 := hL4 s3 hinv3 (by rw [h_l4]; exact hnt_l4)
      rw [h_l4] at hs_l4
      cases rl4 with
      | some r =>
        dsimp only at hnt' ⊢
        have herr := hs_l4.2 (by simp)
        injection herr with hr_eq; subst hr_eq
        exact ⟨fun hr => False.elim (not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
      | none =>
        dsimp only at hnt' ⊢
        obtain ⟨_, heff4⟩ := hs_l4.1 rfl
        rw [evaluateHOLFiniteState_return]
        have hev_r0 : @evalHOLExact 64 F _ s4.toExact
            (fun a => Classical.propDecidable (s4.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev_r0]; dsimp only; rw [if_pos hsz]; dsimp only
        have heff_all : ByteRegionEffect s (emptyLocalsHOLFinite s4) Rl :=
          (((heff_s_s1.trans heff2).trans heff3).trans heff4).with_locals_clock _ _
        refine ⟨fun _ => heff_all.with_locals_clock _ _, fun rv hrv => ?_, fun _ _ h => by simp at h⟩
        injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨hrv''.symm, heff_all.with_locals_clock _ _⟩

theorem eval_memcpy_body_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hsub : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy)
    (Resumes out.1 → ByteRegionEffect s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)) :=
  eval_memcpy_body_bre_gen s dst0 src0 n0 Rl hma hdst hsrc hn
    (fun _ hoff _ => by
      obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
      exact ⟨ivl, hivl, by omega, by omega⟩)
    (fun _ hoff _ => by
      obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
      exact ⟨ivl, hivl, by omega, by omega⟩)
    hnt

theorem eval_call_memcpy_bre_gen {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp =
      some (.val (.word src0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hsub_w : ∀ off, off + 8 ≤ n0.toNat → dst0.toNat + off + 8 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off + 8 ≤ ivl.1 + ivl.2)
    (hsub_b : ∀ off, off < n0.toNat → dst0.toNat + off + 1 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off < ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_memcpy)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "src" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      have h1 : ofString "n" ≠ ofString "src" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memcpy) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨_, hret, hexn⟩ := eval_memcpy_body_bre_gen entry dst0 src0 n0 Rl hma
      hent_dst hent_src hent_n hsub_w hsub_b (by rw [hb]; exact hnt_b)
    rw [hb] at hret hexn
    dsimp only at hret hexn
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b⟩ := hret rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl⟩,
          fun h => False.elim (h rfl)⟩
      | _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem eval_call_memcpy_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
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
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hsrc, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memcpy) dst0 src0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_memcpy)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "src", ValueHOL.val (.word src0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "src" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_src : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
      have h1 : ofString "n" ≠ ofString "src" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memcpy) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨_, hret, hexn⟩ := eval_memcpy_body_bre entry dst0 src0 n0 Rl hma
      hent_dst hent_src hent_n hsub (by rw [hb]; exact hnt_b)
    rw [hb] at hret hexn
    dsimp only at hret hexn
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b⟩ := hret rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl⟩,
          fun h => False.elim (h rfl)⟩
      | _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

end InitECandidate.Solver.Wave8GuestInv.M11
