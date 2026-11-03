import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase

/-! Standalone verified proofs for C08 `WorldKeeps` leaves:
- `«wk_encode_account»`
- `«wk_compute_contract_address»`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! ## 1. Lookups for RLP encoding helpers -/

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

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_encode_account :
    originalRuntimeCode.lookup (ofString "encode_account") =
      some ((sourceFunctionEntry Guest.Software.guestFn_encode_account).2) :=
  lookup_of_guestAst_getElem 294 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_account) rfl

theorem lookup_compute_contract_address :
    originalRuntimeCode.lookup (ofString "compute_contract_address") =
      some ((sourceFunctionEntry Guest.Software.guestFn_compute_contract_address).2) :=
  lookup_of_guestAst_getElem 596 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_contract_address) rfl

theorem seq_nt_or_r16 {F : Type} (cur : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState cur (.seq a b)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState cur (.seq a b)).1 = none ∨
      Resumes (evaluateHOLFiniteState cur (.seq a b)).1) :
    (evaluateHOLFiniteState cur a).1 ≠ some .timeOut ∧
    ((evaluateHOLFiniteState cur a).1 = none ∨ Resumes (evaluateHOLFiniteState cur a).1) := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt hor
  rcases ha : evaluateHOLFiniteState cur a with ⟨ra, ma⟩
  rw [ha] at hnt hor
  refine ⟨fun h => by subst h; simp at hnt, ?_⟩
  cases ra with
  | none => exact Or.inl rfl
  | some _ =>
    right
    rcases hor with h | h
    · simp at h
    · exact h

theorem call0_locals_r16 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rfl
  · simp only [hargs] at hnone ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · rfl
    · simp only [hl] at hnone ⊢
      by_cases hclk : s.clock = 0
      · simp [hclk] at hnone
      · rw [if_neg hclk] at hnone ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        simp only [hb] at hnone ⊢
        cases rb with
        | none => simp at hnone
        | some rb' =>
          cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hok; rw [if_pos hok]
            · simp at hnone
          | _ => simp at hnone

theorem call0_not_resumes_r16 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hf : trapOnlyCallees fname = true) :
    ¬ Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, rs⟩
    · exact not_resumes_error
    · dsimp only
      split
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · have hbody_ok := trapOnlyCallees_good fname hf vals b c rs (by rwa [← hcode])
        have hncr := evaluate_noCatchableRaise trapOnlyCallees trapOnlyCallees_good
          b hbody_ok (callEntryStateHOLFinite s c) hcode
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        rw [hrun] at hncr
        cases rb with
        | none => exact not_resumes_error
        | some rb' =>
          cases rb' with
          | returned _ =>
            dsimp only; split <;> [ (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h); exact not_resumes_error ]
          | exception eid ev =>
            rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
            · simp at h
            · injection h with h'; injection h' with h1 h2; subst h1 h2; exact hncr eid ev hne rfl
          | _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

/-! ## 2. Exact `ByteEff` + return bounds for `rlp_be_len` and `rlp_put_be` -/

private theorem lsr8_bound {v n : BitVec 64} (h : v.toNat < 256 ^ (8 - n.toNat)) (hnle : n.toNat ≤ 8)
    (hv : v ≠ 0) :
    n.toNat < 8 ∧ (v >>> (8 : BitVec 64).toNat).toNat < 256 ^ (8 - (n.toNat + 1)) := by
  have hn_lt : n.toNat < 8 := by
    by_contra hge
    have heq : 8 - n.toNat = 0 := by omega
    rw [heq, Nat.pow_zero] at h
    exact hv (BitVec.eq_of_toNat_eq (by change v.toNat = 0; omega))
  refine ⟨hn_lt, ?_⟩
  have hsh : (v >>> (8 : BitVec 64).toNat).toNat = v.toNat / 256 := by
    change v.toNat >>> 8 = v.toNat / 256; rw [Nat.shiftRight_eq_div_pow]
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

theorem eval_rlp_be_len_while {F : Type} :
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
        let sd := decClockHOLFinite s
        have hsd_v : sd.locals.lookup (ofString "v") = some (.val (.word vw)) := hv
        have hasg1 : evaluateHOLFiniteState sd
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
            (none, setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) sd) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, hsd_v, wordShiftHOL,
            isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
        let s1 := setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) sd
        have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp [s1, sd, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hn, show ofString "v" ≠ ofString "n" by decide]
        have hasg2 : evaluateHOLFiniteState s1
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs1_n,
            wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
            shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
        have hbody : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) := by
          rw [evaluateHOLFiniteState_seq_line780]
          have hasg1' : evaluateHOLFiniteState (decClockHOLFinite s)
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
              (none, s1) := hasg1
          rw [hasg1']; exact hasg2
        simp only [hbody] at hnt ⊢
        let s2 := setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1
        have hnw1 : (nw + 1).toNat = nw.toNat + 1 := BitVec.toNat_add_of_lt (by change nw.toNat + 1 < 2 ^ 64; omega)
        have hs2_clk : s2.clock < k := by simp [s2, s1, sd, setVarHOLFinite, decClockHOLFinite, hclk]; omega
        have hs2_v : s2.locals.lookup (ofString "v") = some (.val (.word (vw >>> (8 : BitVec 64).toNat))) := by
          simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "n" ≠ ofString "v" by decide]
        have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word (nw + 1))) := by
          simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨ll, hr2, hll8, hll_pos, hloc2, heq2⟩ := ih s2.clock hs2_clk s2
          (vw >>> (8 : BitVec 64).toNat) (nw + 1) rfl hs2_v hs2_n (by omega)
          (by rw [hnw1]; exact hv'_lt) hnt
        have hr2' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).1 = none := hr2
        have hloc2' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.locals.lookup (ofString "n") = some (.val (.word ll)) := hloc2
        have heq2' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2 =
            { s2 with locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.locals,
                      clock := (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.clock } := heq2
        change ∃ ll_1,
          (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).1 = none ∧
          ll_1.toNat ≤ 8 ∧
          (vw ≠ 0 ∨ 0 < nw.toNat → 0 < ll_1.toNat) ∧
          (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.locals.lookup (ofString "n") = some (.val (.word ll_1)) ∧
          (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2 =
            { s with locals := (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.locals,
                     clock := (evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word (nw + 1))) s1) rlpBeLenLoop).2.clock }
        refine ⟨ll, hr2', hll8, fun _ => hll_pos (Or.inr (by omega)), hloc2', ?_⟩
        rw [heq2']; simp [s2, s1, sd, setVarHOLFinite, decClockHOLFinite]

theorem eval_rlp_be_len_body {F : Type} (s : PanSemStateFiniteExact 64 F) (vw : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 ≠ some .timeOut) :
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
        (.seq rlpBeLenLoop (.return (.var .local (ofString "n")))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt ⊢
  let s1 := setVarHOLFinite (ofString "n") (.val (.word 0#64)) s
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
      show ofString "n" ≠ ofString "v" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hv_lt : vw.toNat < 256 ^ (8 - (0#64 : BitVec 64).toNat) := by
    have : (256 ^ (8 - (0#64 : BitVec 64).toNat) : Nat) = 2 ^ 64 := rfl
    rw [this]; exact vw.isLt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hl : evaluateHOLFiniteState s1 rlpBeLenLoop with ⟨rl, sl⟩
  have hl' : evaluateHOLFiniteState (setVarHOLFinite (ofString "n") (.val (.word 0#64)) s) rlpBeLenLoop =
      (rl, sl) := hl
  have hnt_l : rl ≠ some .timeOut := by
    rintro rfl; simp [hl'] at hnt
  obtain ⟨ll, hnone, hll8, hll_pos, hsl_n, hsl_eq⟩ :=
    eval_rlp_be_len_while s1.clock s1 vw 0 rfl hs1_v hs1_n (by decide) hv_lt (by rw [hl]; exact hnt_l)
  rw [hl] at hnone hsl_n hsl_eq; dsimp only at hnone hsl_n hsl_eq; subst hnone
  simp only [hl', evaluateHOLFiniteState_return, evalHOLExact, hsl_n, shapeOfHOLExact,
    sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
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
      rintro rfl; simp [entry, hb] at hnt
    obtain ⟨ll, hbr, hll8, hll_pos, hbs_eq⟩ :=
      eval_rlp_be_len_body entry vw hent_v (by rw [hb]; exact hnt_b)
    rw [hb] at hbr hbs_eq; dsimp only at hbr hbs_eq; subst hbr
    have hb' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw))))
        (sourceFnBody Guest.Software.guestFn_rlp_be_len) =
        (some (.returned (.val (.word ll))), bs) := hb
    simp only [hb', shapeOfHOLExact, shapeEqHOL, Bool.and_self, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word ll)) { bs with locals := s.locals }
    refine ⟨ll, mid, hll8, hll_pos, rfl, ?_, hnt, rfl, rfl⟩
    dsimp only [mid, setVarHOLFinite]; rw [hbs_eq]; cases s; rfl

theorem eval_rlp_put_be_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 v0 n0 : BitVec 64)
    (Rl : List Ivl)
    (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hv : s.locals.lookup (ofString "v") = some (.val (.word v0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (_hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)
    ByteEff s out.2 Rl ∧
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
  rw [hb, evaluateHOLFiniteState_dec_total]
  have hev_n : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word n0)) := by simp [evalHOLExact, hn]
  simp only [hev_n, shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
  set s1 := setVarHOLFinite (ofString "i") (.val (.word n0)) s
  let wcond : ExpHOL 64 := ExpHOL.cmp .lower (.const 0) (.var .local (ofString "i"))
  let wbody : ProgHOL 64 := ProgHOL.seq
    (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
    (.seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                  (.var .local (ofString "v")))
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))))
  let P (t : PanSemStateFiniteExact 64 F) : Prop :=
    GuestInv t ∧
    t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
    ∃ iw vw : BitVec 64,
      t.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      t.locals.lookup (ofString "v") = some (.val (.word vw)) ∧
      iw.toNat ≤ n0.toNat
  have hPs1 : P s1 := by
    refine ⟨guestInv_setVar _ _ s hG, ?_, n0, v0, ?_, ?_, le_rfl⟩
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
        show ofString "i" ≠ ofString "dst" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv,
        show ofString "i" ≠ ofString "v" by decide]
  have hloop : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k → P t →
      ByteEff t (evaluateHOLFiniteState t (.while wcond wbody)).2 Rl ∧
      (∀ eid ev, (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.exception eid ev)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk ⟨hGt, ht_dst, iw, vw, ht_i, ht_v, hiw_le⟩
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      have hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond =
          some (.val (.word (if (0 : BitVec 64) < iw then 1 else 0))) := by
        simp [wcond, evalHOLFinite, evalHOLExact, ht_i, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc]; dsimp only
      by_cases hpos : (0 : BitVec 64) < iw
      · simp only [hpos, ↓reduceIte]
        have h10 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h10]
        by_cases hk0 : t.clock = 0
        · simp [hk0]; exact (ByteEff.refl t Rl).locals_clock _ _
        · rw [if_neg hk0]
          have hiw_pos : 0 < iw.toNat := by rw [BitVec.lt_def] at hpos; exact hpos
          have hiw1 : (iw - 1).toNat = iw.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ iw.toNat; omega))]; rfl
          let t0 := decClockHOLFinite t
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word iw)) := ht_i
          have hasg1 : evaluateHOLFiniteState t0
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, ht0_i,
              wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
          let t1 := setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0
          have hasg1' : evaluateHOLFiniteState (decClockHOLFinite t)
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1])) =
              (none, t1) := hasg1
          have hGt1 : GuestInv t1 := guestInv_setVar _ _ t0 (guestInv_congr (s := t) rfl rfl rfl rfl hGt)
          have ht1_dst : t1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              ht_dst, show ofString "i" ≠ ofString "dst" by decide]
          have ht1_i : t1.locals.lookup (ofString "i") = some (.val (.word (iw - 1))) := by
            simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht1_v : t1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              ht_v, show ofString "i" ≠ ofString "v" by decide]
          have hdst_ev : @evalHOLExact 64 F _ t1.toExact (fun a => Classical.propDecidable (t1.memaddrs a))
              (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
              some (.val (.word (dst0 + (iw - 1)))) := by
            simp [evalHOLExact, evalListHOLExact, ht1_dst, ht1_i, wordOpHOL, wordOp, valueIsWord, valueWord]
          have heff_sb := (byteEff_storeByte hGt1
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.var .local (ofString "v")) (fun x hx _ => by
              rw [hdst_ev] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
              obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl (by omega)
              have hadd_nat : (dst0 + (iw - 1)).toNat = dst0.toNat + (iw.toNat - 1) := by
                rw [BitVec.toNat_add, hiw1]; exact Nat.mod_eq_of_lt (by omega)
              exact ⟨ivl, hivl, by omega, by omega⟩)).1
          have hsb_ctrl := evaluate_storeByte_control_frame t1
            (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
            (.var .local (ofString "v"))
          have hclk_b := evaluateHOLFiniteState_clock_le t0 wbody
          have hd_lt : t0.clock < k := by simp [t0, decClockHOLFinite, hclk]; omega
          dsimp only [t0, wbody] at hclk_b ⊢
          rw [evaluateHOLFiniteState_seq_line780, hasg1'] at hclk_b ⊢
          dsimp only at hclk_b ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hclk_b ⊢
          rcases hsb : evaluateHOLFiniteState t1
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                          (.var .local (ofString "v"))) with ⟨rsb, t2⟩
          simp only [hsb] at heff_sb hsb_ctrl hclk_b ⊢
          rcases hsb_ctrl.1 with hrsb | hrsb
          · subst hrsb
            dsimp only at hclk_b ⊢
            have ht2_loc : t2.locals = t1.locals := hsb_ctrl.2.2.1
            have ht2_v : t2.locals.lookup (ofString "v") = some (.val (.word vw)) := by rw [ht2_loc]; exact ht1_v
            have hasg2 : evaluateHOLFiniteState t2
                (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
                (none, setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, ht2_v, wordShiftHOL,
                isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg2] at hclk_b ⊢; dsimp only at hclk_b ⊢
            let t3 := setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2
            have heff_iter : ByteEff t t3 Rl :=
              (((ByteEff.refl t Rl).locals_clock _ _).trans heff_sb).locals_clock _ _
            have hPt3 : P t3 := by
              refine ⟨guestInv_congr heff_iter.code heff_iter.memaddrs heff_iter.shMemaddrs heff_iter.baseAddr hGt,
                ?_, iw - 1, vw >>> (8 : BitVec 64).toNat, ?_, ?_, by omega⟩
              · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht2_loc, ht1_dst,
                  show ofString "v" ≠ ofString "dst" by decide]
              · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht2_loc, ht1_i,
                  show ofString "v" ≠ ofString "i" by decide]
              · simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨jih_eff, jih_ne⟩ := ih t3.clock (lt_of_le_of_lt hclk_b hd_lt) t3 rfl hPt3
            exact ⟨heff_iter.trans jih_eff, jih_ne⟩
          · subst hrsb
            dsimp only
            exact ⟨((ByteEff.refl t Rl).locals_clock _ _).trans heff_sb, by simp⟩
      · simp only [hpos, ↓reduceIte]
        have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
        rw [if_neg h00]
        exact ⟨ByteEff.refl t Rl, by simp⟩
  rw [evaluateHOLFiniteState_seq_line780]
  obtain ⟨heff_l, hne_l⟩ := hloop s1.clock s1 rfl hPs1
  rcases hwl : evaluateHOLFiniteState s1 (.while wcond wbody) with ⟨rwl, swl⟩
  have hwl' : evaluateHOLFiniteState s1
      (.while (.cmp .lower (.const 0) (.var .local (ofString "i")))
        (.seq
          (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                        (.var .local (ofString "v")))
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))))) =
      (rwl, swl) := hwl
  rw [hwl] at heff_l hne_l
  simp only [hwl']
  have heff_s_swl : ByteEff s swl Rl := ((ByteEff.refl s Rl).locals_clock _ _).trans heff_l
  cases rwl with
  | none =>
    dsimp only
    exact ⟨(heff_s_swl.trans (byteEff_return swl _ Rl)).locals_clock _ _,
      by rw [evaluateHOLFiniteState_return]; simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]⟩
  | some r =>
    dsimp only
    exact ⟨heff_s_swl.locals_clock _ _, fun eid ev h => hne_l eid ev h⟩

theorem eval_call_rlp_put_be {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp vExp nExp : ExpHOL 64)
    (dst0 v0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
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
    ByteEff s out.2 Rl ∧
    (out.1 = none → out.2.locals = s.locals) ∧
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
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "dst" by decide, show ofString "v" ≠ ofString "dst" by decide]
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word v0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "n" ≠ ofString "v" by decide]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_rlp_put_be) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      rw [hb] at hnt; exact hnt rfl
    obtain ⟨heff_b, hexn⟩ := eval_rlp_put_be_body entry dst0 v0 n0 Rl (guestInv_callEntry s cmap hG)
      hent_dst hent_v hent_n hfit hin_ivl (by dsimp only [entry]; rw [hb]; exact hnt_b)
    dsimp only [entry] at heff_b hexn; rw [hb] at heff_b hexn; dsimp only at heff_b hexn ⊢
    have heff_s_bs : ByteEff s bs Rl := ((ByteEff.refl s Rl).locals_clock _ _).trans heff_b
    cases br with
    | none => exact ⟨heff_s_bs, fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        dsimp only
        split
        · exact ⟨heff_s_bs.locals_clock _ _, fun _ => rfl, fun h => False.elim (h rfl)⟩
        · exact ⟨heff_s_bs, fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      | _ => exact ⟨heff_s_bs.locals_clock _ _, fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

/-! ## 3. `rlp_write_header`, `rlp_encode_word`, `rlp_encode_bytes`, `rlp_header_len`,
       `rlp_list_header_len`, `rlp_encode_list_header` -/

theorem eval_rlp_write_header_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 base0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hbase : s.locals.lookup (ofString "base") = some (.val (.word base0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1) :
    ∃ h : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 =
        some (.returned (.val (.word h))) ∧
      1 ≤ h.toNat ∧ h.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
      ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
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
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c] at hnt hres ⊢; dsimp only at hnt hres ⊢
  by_cases hn55 : n0.toNat ≤ 55
  · rw [if_pos hn55, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    have hsb_pr := byteEff_storeByte hG (.var .local (ofString "dst"))
      (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])
      (fun x hx _ => by
        simp [evalHOLExact, hdst] at hx; subst hx
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
    have hsb_ctrl := evaluate_storeByte_control_frame s (.var .local (ofString "dst"))
      (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])
    rcases hsb : evaluateHOLFiniteState s
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with ⟨rsb, s1⟩
    simp only [hsb] at hsb_pr hsb_ctrl hres ⊢
    rcases hsb_ctrl.1 with hrsb | hrsb
    · subst hrsb
      obtain ⟨x, hx, _, hhi⟩ := hsb_pr.2 rfl
      simp [evalHOLExact, hdst] at hx; subst hx
      dsimp only at hres ⊢
      rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
        show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
      exact ⟨1, rfl, by decide, by decide, by omega, hsb_pr.1.locals_clock _ _⟩
    · subst hrsb; exact False.elim (not_resumes_error hres)
  · rw [if_neg hn55, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
      eval_decCall_rlp_be_len s "ll" (.var .local (ofString "n")) n0 _ hcode
        (by simp [evalHOLExact, hn]) hnt
    rw [hr_eq] at hres
    rw [hr_eq, hs_eq]
    have hGmid : GuestInv mid := by rw [hmid_eq]; exact guestInv_with_locals_clock s _ _ hG
    have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
    have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "ll" ≠ ofString "dst" by decide]
    have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "ll" ≠ ofString "n" by decide]
    have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
      rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have heff_s_mid : ByteEff s mid Rl := by rw [hmid_eq]; exact (ByteEff.refl s Rl).locals_clock _ _
    rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
    have hsb_pr := byteEff_storeByte hGmid (.var .local (ofString "dst"))
      (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])
      (fun x hx _ => by
        simp [evalHOLExact, hmid_dst] at hx; subst hx
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
        exact ⟨ivl, hivl, h1, by omega⟩)
    have hsb_ctrl := evaluate_storeByte_control_frame mid (.var .local (ofString "dst"))
      (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])
    rcases hsb : evaluateHOLFiniteState mid
        (.storeByte (.var .local (ofString "dst"))
          (.op .add [.var .local (ofString "base"), .const 55, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
    simp only [hsb] at hsb_pr hsb_ctrl hnt_m hres ⊢
    rcases hsb_ctrl.1 with hrsb | hrsb
    · subst hrsb
      obtain ⟨x, hx, _, hhi_dst⟩ := hsb_pr.2 rfl
      simp [evalHOLExact, hmid_dst] at hx; subst hx
      dsimp only at hnt_m hres ⊢
      have hs2_loc : s2.locals = mid.locals := hsb_ctrl.2.2.1
      have hGs2 : GuestInv s2 := guestInv_congr hsb_pr.1.code hsb_pr.1.memaddrs hsb_pr.1.shMemaddrs hsb_pr.1.baseAddr hGmid
      have hs2_code : s2.code = originalRuntimeCode := hsb_pr.1.code.trans hmid_code
      have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hs2_loc]; exact hmid_dst
      have hs2_n : s2.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hs2_loc]; exact hmid_n
      have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by rw [hs2_loc]; exact hmid_ll
      have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 :=
        BitVec.toNat_add_of_lt (by change dst0.toNat + 1 < 2 ^ 64; omega)
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
      rcases hc_put : evaluateHOLFiniteState s2
        (.call (some (none, none)) (ofString "rlp_put_be")
          [.op .add [.var .local (ofString "dst"), .const 1],
           .var .local (ofString "n"), .var .local (ofString "ll")]) with ⟨rc, s3⟩
      have hnt_put : rc ≠ some .timeOut := by rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
      have hput := eval_call_rlp_put_be s2
        (.op .add [.var .local (ofString "dst"), .const 1])
        (.var .local (ofString "n")) (.var .local (ofString "ll"))
        (dst0 + 1) n0 ll Rl hs2_code hGs2
        (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by simp [evalHOLExact, hs2_n])
        (by simp [evalHOLExact, hs2_ll])
        (by rw [hdst1_nat]; have : heapEnd = 33806089704 := heapEnd_val; omega)
        (fun _ => by
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
        (by rw [hc_put]; exact hnt_put)
      dsimp only at hput; rw [hc_put] at hput
      simp only [hc_put] at hres ⊢
      cases rc with
      | some r => exact False.elim (hput.2.2 (by simp) hres)
      | none =>
        dsimp only at hres ⊢
        have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hput.2.1 rfl]; exact hs2_ll
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .add [.const 1, .var .local (ofString "ll")]) = some (.val (.word (1 + ll))) := by
          simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]
        simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
        have h1ll : (1 + ll).toNat = 1 + ll.toNat := BitVec.toNat_add_of_lt (by change 1 + ll.toNat < 2 ^ 64; omega)
        exact ⟨1 + ll, rfl, by omega, by omega, by omega,
          ((((heff_s_mid.trans hsb_pr.1).trans hput.1).locals_clock _ _).locals_clock _ _)⟩
    · subst hrsb; exact False.elim (not_resumes_error hres)

theorem eval_rlp_encode_word_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 w0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w0)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1) :
    ∃ r : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 =
        some (.returned (.val (.word r))) ∧
      1 ≤ r.toNat ∧ r.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
      ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
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
              (.storeByte (.var .local (ofString "dst")) (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"), .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  have hev_c1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
      some (.val (.word (if w0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_c1] at hnt hres ⊢; dsimp only at hnt hres ⊢
  by_cases hwz : w0 = 0
  · rw [if_pos hwz, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    have hsb_pr := byteEff_storeByte hG (.var .local (ofString "dst")) (.const 128) (fun x hx _ => by
      simp [evalHOLExact, hdst] at hx; subst hx
      obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
    have hsb_ctrl := evaluate_storeByte_control_frame s (.var .local (ofString "dst")) (.const 128)
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hsb_pr hsb_ctrl hres ⊢
    rcases hsb_ctrl.1 with hrsb | hrsb
    · subst hrsb
      obtain ⟨x, hx, _, hhi⟩ := hsb_pr.2 rfl; simp [evalHOLExact, hdst] at hx; subst hx
      dsimp only at hres ⊢; rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
      exact ⟨1, rfl, by decide, by decide, by omega, hsb_pr.1.locals_clock _ _⟩
    · subst hrsb; exact False.elim (not_resumes_error hres)
  · rw [if_neg hwz, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
    have hev_c2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
        some (.val (.word (if w0 < 128 then 1 else 0))) := by
      simp [evalHOLExact, hw, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hev_c2] at hnt hres ⊢; dsimp only at hnt hres ⊢
    by_cases hw128 : w0 < 128
    · rw [if_pos hw128, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      have hsb_pr := byteEff_storeByte hG (.var .local (ofString "dst")) (.var .local (ofString "w")) (fun x hx _ => by
        simp [evalHOLExact, hdst] at hx; subst hx
        obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
      have hsb_ctrl := evaluate_storeByte_control_frame s (.var .local (ofString "dst")) (.var .local (ofString "w"))
      rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
      simp only [hsb] at hsb_pr hsb_ctrl hres ⊢
      rcases hsb_ctrl.1 with hrsb | hrsb
      · subst hrsb
        obtain ⟨x, hx, _, hhi⟩ := hsb_pr.2 rfl; simp [evalHOLExact, hdst] at hx; subst hx
        dsimp only at hres ⊢; rw [evaluateHOLFiniteState_return]
        simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
        exact ⟨1, rfl, by decide, by decide, by omega, hsb_pr.1.locals_clock _ _⟩
      · subst hrsb; exact False.elim (not_resumes_error hres)
    · rw [if_neg hw128, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
      dsimp only at hnt hres ⊢
      obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
        eval_decCall_rlp_be_len s "ll" (.var .local (ofString "w")) w0 _ hcode
          (by simp [evalHOLExact, hw]) hnt
      rw [hr_eq] at hres; rw [hr_eq, hs_eq]
      have hGmid : GuestInv mid := by rw [hmid_eq]; exact guestInv_with_locals_clock s _ _ hG
      have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
      have hmid_dst : mid.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "ll" ≠ ofString "dst" by decide]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hw, show ofString "ll" ≠ ofString "w" by decide]
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have heff_s_mid : ByteEff s mid Rl := by rw [hmid_eq]; exact (ByteEff.refl s Rl).locals_clock _ _
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
      have hsb_pr := byteEff_storeByte hGmid (.var .local (ofString "dst"))
        (.op .add [.const 128, .var .local (ofString "ll")]) (fun x hx _ => by
          simp [evalHOLExact, hmid_dst] at hx; subst hx
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
      have hsb_ctrl := evaluate_storeByte_control_frame mid (.var .local (ofString "dst"))
        (.op .add [.const 128, .var .local (ofString "ll")])
      rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst")) (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
      simp only [hsb] at hsb_pr hsb_ctrl hnt_m hres ⊢
      rcases hsb_ctrl.1 with hrsb | hrsb
      · subst hrsb
        obtain ⟨x, hx, _, hhi_dst⟩ := hsb_pr.2 rfl; simp [evalHOLExact, hmid_dst] at hx; subst hx
        dsimp only at hnt_m hres ⊢
        have hs2_loc : s2.locals = mid.locals := hsb_ctrl.2.2.1
        have hGs2 : GuestInv s2 := guestInv_congr hsb_pr.1.code hsb_pr.1.memaddrs hsb_pr.1.shMemaddrs hsb_pr.1.baseAddr hGmid
        have hs2_code : s2.code = originalRuntimeCode := hsb_pr.1.code.trans hmid_code
        have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hs2_loc]; exact hmid_dst
        have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w0)) := by rw [hs2_loc]; exact hmid_w
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by rw [hs2_loc]; exact hmid_ll
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 :=
          BitVec.toNat_add_of_lt (by change dst0.toNat + 1 < 2 ^ 64; omega)
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres ⊢
        rcases hc_put : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .var .local (ofString "w"), .var .local (ofString "ll")]) with ⟨rc, s3⟩
        have hnt_put : rc ≠ some .timeOut := by rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
        have hput := eval_call_rlp_put_be s2
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.var .local (ofString "w")) (.var .local (ofString "ll"))
          (dst0 + 1) w0 ll Rl hs2_code hGs2
          (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by simp [evalHOLExact, hs2_w])
          (by simp [evalHOLExact, hs2_ll])
          (by rw [hdst1_nat]; have : heapEnd = 33806089704 := heapEnd_val; omega)
          (fun _ => by
            obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
            exact ⟨ivl, hivl, by rw [hdst1_nat]; omega, by rw [hdst1_nat]; omega⟩)
          (by rw [hc_put]; exact hnt_put)
        dsimp only at hput; rw [hc_put] at hput
        simp only [hc_put] at hres ⊢
        cases rc with
        | some r => exact False.elim (hput.2.2 (by simp) hres)
        | none =>
          dsimp only at hres ⊢
          have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
            rw [hput.2.1 rfl]; exact hs2_ll
          rw [evaluateHOLFiniteState_return]
          have hev_ret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.op .add [.const 1, .var .local (ofString "ll")]) = some (.val (.word (1 + ll))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret]
          simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
          have h1ll : (1 + ll).toNat = 1 + ll.toNat := BitVec.toNat_add_of_lt (by change 1 + ll.toNat < 2 ^ 64; omega)
          exact ⟨1 + ll, rfl, by omega, by omega, by omega,
            ((((heff_s_mid.trans hsb_pr.1).trans hput.1).locals_clock _ _).locals_clock _ _)⟩
      · subst hrsb; exact False.elim (not_resumes_error hres)

theorem eval_rlp_write_header_short {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 base0 n0 : BitVec 64) (Rl : List Ivl)
    (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (_hbase : s.locals.lookup (ofString "base") = some (.val (.word base0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn55 : n0.toNat ≤ 55)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 1 ≤ ivl.1 + ivl.2)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).1 =
      some (.returned (.val (.word 1))) ∧
    dst0.toNat < heapEnd ∧
    ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_write_header)).2 Rl := by
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
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres ⊢
  have hev_c : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
      some (.val (.word (if n0.toNat ≤ 55 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.le_def]
  rw [hev_c, if_pos hn55] at hres ⊢; dsimp only at hres ⊢
  rw [if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hres ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  have hsb_pr := byteEff_storeByte hG (.var .local (ofString "dst"))
    (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])
    (fun x hx _ => by simp [evalHOLExact, hdst] at hx; subst hx; exact hin_ivl)
  have hsb_ctrl := evaluate_storeByte_control_frame s (.var .local (ofString "dst"))
    (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])
  rcases hsb : evaluateHOLFiniteState s
      (.storeByte (.var .local (ofString "dst"))
        (.op .add [.var .local (ofString "base"), .var .local (ofString "n")])) with ⟨rsb, s1⟩
  simp only [hsb] at hsb_pr hsb_ctrl hres ⊢
  rcases hsb_ctrl.1 with hrsb | hrsb
  · subst hrsb
    obtain ⟨x, hx, _, hhi⟩ := hsb_pr.2 rfl
    simp [evalHOLExact, hdst] at hx; subst hx
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_return]
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
    exact ⟨rfl, by omega, hsb_pr.1.locals_clock _ _⟩
  · subst hrsb; exact False.elim (not_resumes_error hres)

theorem eval_rlp_encode_bytes_bounded {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 src0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn_le : n0.toNat ≤ 55)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + (n0.toNat + 1) ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1) :
    ∃ r : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).1 =
        some (.returned (.val (.word r))) ∧
      1 ≤ r.toNat ∧ r.toNat ≤ n0.toNat + 1 ∧ dst0.toNat < heapEnd ∧
      ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
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
               .var .local (ofString "src"), .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))) := rfl
  let tailP : ProgHOL 64 :=
    .decCall (ofString "h") .one (ofString "rlp_write_header")
      [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")]
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"), .var .local (ofString "n")])
        (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))
  have htail : ∀ (t : PanSemStateFiniteExact 64 F),
      ByteEff s t Rl → t.locals = s.locals →
      (evaluateHOLFiniteState t tailP).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState t tailP).1 →
      ∃ r : BitVec 64,
        (evaluateHOLFiniteState t tailP).1 = some (.returned (.val (.word r))) ∧
        1 ≤ r.toNat ∧ r.toNat ≤ n0.toNat + 1 ∧ dst0.toNat < heapEnd ∧
        ByteEff s (evaluateHOLFiniteState t tailP).2 Rl := by
    intro t heff_t ht_loc hnt_t hres_t
    have ht_code : t.code = originalRuntimeCode := heff_t.code.trans hcode
    have hGt : GuestInv t := guestInv_congr heff_t.code heff_t.memaddrs heff_t.shMemaddrs heff_t.baseAddr hG
    have ht_dst : t.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [ht_loc]; exact hdst
    have ht_src : t.locals.lookup (ofString "src") = some (.val (.word src0)) := by rw [ht_loc]; exact hsrc
    have ht_n : t.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [ht_loc]; exact hn
    dsimp only [tailP] at hnt_t hres_t ⊢
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt_t hres_t ⊢
    have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "dst"), .const 128, .var .local (ofString "n")] =
        some [.val (.word dst0), .val (.word 128), .val (.word n0)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht_dst, ht_n]
    have hlook := pan_three_word_lookup t.code.lookup (ofString "rlp_write_header")
      (ofString "dst") (ofString "base") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_rlp_write_header) dst0 128 n0
      (by decide) (by decide) (by decide) (by rw [ht_code]; exact lookup_rlp_write_header)
    simp only [hargs, hlook] at hnt_t hres_t ⊢
    by_cases hclk0 : t.clock = 0
    · simp [hclk0] at hnt_t
    · simp only [hclk0, ↓reduceIte] at hnt_t hres_t ⊢
      set cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
          (ofString "base", ValueHOL.val (.word (128 : BitVec 64)))).update (ofString "n", ValueHOL.val (.word n0))
      set ent := callEntryStateHOLFinite t cmap
      have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "dst" by decide, show ofString "base" ≠ ofString "dst" by decide]
      have hent_base : ent.locals.lookup (ofString "base") = some (.val (.word (128 : BitVec 64))) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "base" by decide]
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n0)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hGt_ent : GuestInv ent := guestInv_callEntry t cmap hGt
      rcases hwh : evaluateHOLFiniteState ent
          (sourceFnBody Guest.Software.guestFn_rlp_write_header) with ⟨rwh, swh⟩
      have hnt_wh : rwh ≠ some .timeOut := by
        rintro rfl; simp [hwh] at hnt_t
      have hres_wh : Resumes rwh := by
        cases rwh with
        | none => simp [hwh] at hres_t; exact False.elim (not_resumes_error hres_t)
        | some cr =>
          cases cr with
          | returned v => exact Or.inl ⟨v, rfl⟩
          | exception eid ev =>
            simp only [hwh] at hres_t
            rcases hres_t with ⟨_, hc⟩ | ⟨e', v', hc, hne⟩
            · simp at hc
            · simp at hc; obtain ⟨rfl, rfl⟩ := hc; exact Or.inr ⟨eid, ev, rfl, hne⟩
          | _ => simp only [hwh] at hres_t; rcases hres_t with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
      obtain ⟨hrwh, hdst_lt_he, heff_wh⟩ := eval_rlp_write_header_short ent dst0 (128 : BitVec 64) n0 Rl
        hGt_ent hent_dst hent_base hent_n hn_le
        (by obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
        (by rw [hwh]; exact hres_wh)
      rw [hwh] at hrwh heff_wh; dsimp only at hrwh heff_wh; subst hrwh
      have hsh_h : (shapeEqHOL (shapeOfHOLExact (.val (.word (1 : BitVec 64)) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word (1 : BitVec 64)) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      simp only [hwh, hsh_h, ↓reduceIte] at hnt_t hres_t ⊢
      let h : BitVec 64 := 1
      have hh1 : 1 ≤ h.toNat := by decide
      have hh9 : h.toNat ≤ 1 := by decide
      let mid := setVarHOLFinite (ofString "h") (.val (.word h)) { swh with locals := t.locals }
      have heff_s_mid : ByteEff s mid Rl :=
        ((heff_t.locals_clock _ _).trans heff_wh).locals_clock _ _
      have hGmid : GuestInv mid := guestInv_congr heff_s_mid.code heff_s_mid.memaddrs heff_s_mid.shMemaddrs heff_s_mid.baseAddr hG
      have hmid_code : mid.code = originalRuntimeCode := heff_s_mid.code.trans hcode
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
      have h264_val : heapEnd = 33806089704 := by rw [heapEnd_val]
      have hdsth_nat : (dst0 + h).toNat = dst0.toNat + h.toNat :=
        BitVec.toNat_add_of_lt (by change dst0.toNat + h.toNat < 2 ^ 64; omega)
      have hargs_mc : evalListHOLFinite mid (h := fun a => Classical.propDecidable (mid.memaddrs a))
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
           .var .local (ofString "src"), .var .local (ofString "n")] =
          some [.val (.word (dst0 + h)), .val (.word src0), .val (.word n0)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hmid_dst, hmid_h, hmid_src, hmid_n,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      have hnt_t' : (evaluateHOLFiniteState mid
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"), .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).1 ≠ some .timeOut :=
        by intro hc; apply hnt_t; exact hc
      have hres_t' : Resumes (evaluateHOLFiniteState mid
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"), .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).1 := hres_t
      obtain ⟨hnt_mc, hor_mc⟩ := seq_nt_or_r16 mid _ _ hnt_t' (Or.inr hres_t')
      have heff_mc := call0_byteEff funByteEff_memcpy mid _ Rl hmid_code hGmid
        (fun vs hvs iv hiv _ => by
          rw [hargs_mc] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat, hdsth_nat] at hiv; subst hiv
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
          exact ⟨ivl, hivl, by omega, by omega⟩)
        hnt_mc hor_mc
      have hnr_mc := call0_not_resumes_r16 mid (ofString "memcpy")
        [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
         .var .local (ofString "src"), .var .local (ofString "n")] hmid_code (by decide)
      change ∃ r,
        (evaluateHOLFiniteState mid
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
               .var .local (ofString "src"), .var .local (ofString "n")])
            (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).1 =
          some (.returned (.val (.word r))) ∧
        1 ≤ r.toNat ∧ r.toNat ≤ n0.toNat + 1 ∧ dst0.toNat < heapEnd ∧
        ByteEff s
          { (evaluateHOLFiniteState mid
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                   .var .local (ofString "src"), .var .local (ofString "n")])
                (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).2 with
            locals := HolFiniteMapExact.resVarEq
              (evaluateHOLFiniteState mid
                (.seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
                     .var .local (ofString "src"), .var .local (ofString "n")])
                  (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")])))).2.locals
              (ofString "h", t.locals.lookup (ofString "h")) } Rl
      rw [evaluateHOLFiniteState_seq_line780] at hres_t' ⊢
      rcases hmc : evaluateHOLFiniteState mid
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
             .var .local (ofString "src"), .var .local (ofString "n")]) with ⟨rmc, smc⟩
      simp only [hmc] at hres_t' heff_mc hnr_mc ⊢
      cases rmc with
      | some mr => exact False.elim (hnr_mc hres_t')
      | none =>
        dsimp only at hres_t' ⊢
        have hsmc_loc : smc.locals = mid.locals := by
          have := call0_locals_r16 mid _ _ (by rw [hmc]); rwa [hmc] at this
        have hsmc_h : smc.locals.lookup (ofString "h") = some (.val (.word h)) := by rw [hsmc_loc]; exact hmid_h
        have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hsmc_loc]; exact hmid_n
        rw [evaluateHOLFiniteState_return]
        have hev_ret : @evalHOLExact 64 F _ smc.toExact (fun a => Classical.propDecidable (smc.memaddrs a))
            (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
            some (.val (.word (h + n0))) := by
          simp [evalHOLExact, evalListHOLExact, hsmc_h, hsmc_n, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hev_ret]
        simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
        have hhn0 : (h + n0).toNat = h.toNat + n0.toNat :=
          BitVec.toNat_add_of_lt (by change h.toNat + n0.toNat < 2 ^ 64; omega)
        exact ⟨h + n0, rfl, by omega, by omega, hdst_lt_he,
          (((heff_s_mid.trans heff_mc).locals_clock _ _).locals_clock _ _)⟩
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres ⊢
  have hev_n1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 1)) =
      some (.val (.word (if n0 = 1 then 1 else 0))) := by
    simp [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hev_n1] at hnt hres ⊢; dsimp only at hnt hres ⊢
  by_cases hn1 : n0 = 1
  · rw [if_pos hn1, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢; dsimp only at hnt hres ⊢
    rcases hlb : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.var .local (ofString "src"))) with _ | bv
    · simp [hlb] at hres; exact False.elim (not_resumes_error hres)
    · have hbv_w : ∃ b0 : BitVec 64, bv = .val (.word b0) := by
        simp only [evalHOLExact, hsrc, panMemLoadByteHOL] at hlb
        cases s.memory (panByteAlignHOL src0) with
        | word cell =>
          split at hlb
          · simp only [Option.map, Option.some.injEq] at hlb; exact ⟨_, hlb.symm⟩
          · simp at hlb
      obtain ⟨b0, rfl⟩ := hbv_w
      simp only [hlb, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt hres ⊢
      set sb := setVarHOLFinite (ofString "b") (.val (.word b0)) s
      have hGsb : GuestInv sb := guestInv_setVar _ _ s hG
      have hsb_b : sb.locals.lookup (ofString "b") = some (.val (.word b0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hsb_dst : sb.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst,
          show ofString "b" ≠ ofString "dst" by decide]
      rw [evaluateHOLFiniteState_ite] at hnt hres ⊢
      have hev_blt : @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a))
          (.cmp .lower (.var .local (ofString "b")) (.const 128)) =
          some (.val (.word (if b0 < 128 then 1 else 0))) := by
        simp [evalHOLExact, hsb_b, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hev_blt] at hnt hres ⊢; dsimp only at hnt hres ⊢
      by_cases hblt : b0 < 128
      · rw [if_pos hblt, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hnt hres ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
        have hsb_pr := byteEff_storeByte hGsb (.var .local (ofString "dst")) (.var .local (ofString "b")) (fun x hx _ => by
          simp [evalHOLExact, hsb_dst] at hx; subst hx
          obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl; exact ⟨ivl, hivl, h1, by omega⟩)
        have hsb_ctrl := evaluate_storeByte_control_frame sb (.var .local (ofString "dst")) (.var .local (ofString "b"))
        rcases hst : evaluateHOLFiniteState sb (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "b"))) with ⟨rst, s1⟩
        simp only [hst] at hsb_pr hsb_ctrl hres ⊢
        rcases hsb_ctrl.1 with hrst | hrst
        · subst hrst
          obtain ⟨x, hx, _, hhi⟩ := hsb_pr.2 rfl; simp [evalHOLExact, hsb_dst] at hx; subst hx
          dsimp only at hres ⊢; rw [evaluateHOLFiniteState_return]
          simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, show (8 : Nat) ≤ 32 by decide, ↓reduceIte]
          have h264_val : heapEnd = 33806089704 := by rw [heapEnd_val]
          exact ⟨1, rfl, by decide, by change 1 ≤ n0.toNat + 1; omega, by omega,
            ((((ByteEff.refl s Rl).locals_clock _ _).trans hsb_pr.1).locals_clock _ _).locals_clock _ _⟩
        · subst hrst; exact False.elim (not_resumes_error hres)
      · rw [if_neg hblt, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let s' : PanSemStateFiniteExact 64 F :=
          { sb with locals := HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b")) }
        have hs'_loc : s'.locals = s.locals := by
          apply HolFiniteMapExact.ext_lookup; intro k
          change (HolFiniteMapExact.resVarEq sb.locals (ofString "b", s.locals.lookup (ofString "b"))).lookup k = _
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hk : k = ofString "b"
          · subst hk; simp
          · simp [hk, sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        exact htail s' ((ByteEff.refl s Rl).locals_clock _ _) hs'_loc hnt hres
  · rw [if_neg hn1, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    exact htail s (ByteEff.refl s Rl) rfl hnt hres

/-! ## 4. Call-level wrappers and `ByteEff.to_worldStep` -/

theorem ByteEff.to_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (heff : ByteEff s post (R s)) :
    WorldStep R [] stdKeep NoExtra s r post := by
  have hGn : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hWOK.1.1
  have hAn : ArenaReady post := ⟨hGn, by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hWOK.1.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, globalsWord_congr heff.globals h9⟩ <;>
      simpa [globN, heff.globals]⟩
  have hfb : FreshBufsOK s post := by
    refine ⟨fun gn _ => Or.inl (by simp [globN, heff.globals]), ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j _ _ _ h1 _; exact absurd (by simp [globN, heff.globals]) h1.1
  exact worldStep_master [] (by simp) hWOK hAn
    ⟨by simp [globN, heff.globals], by simp [globN, heff.globals]⟩
    (fun _ _ => by rw [heff.globals]) (by decide) hfb
    (fun a hne => ⟨heff.out_dom a hne, Or.inl (heff.cell_frame a hne)⟩)
    (fun b hb64 hne => Or.inl (heff.byte_frame b hb64 hne))
    (fun _ _ _ _ _ _ _ _ => trivial)

theorem eval_decCall_rlp_encode_word_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp wExp : ExpHOL 64)
    (cont : ProgHOL 64) (Rfn : BitVec 64 → List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hin_ivl : ∀ dst0 : BitVec 64, ∃ ivl ∈ Rfn dst0, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 9 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).1) :
    ∃ (dst0 w0 r : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word dst0)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp =
        some (.val (.word w0)) ∧
      1 ≤ r.toNat ∧ r.toNat ≤ 9 ∧ dst0.toNat < heapEnd ∧
      ByteEff s mid (Rfn dst0) ∧
      mid.locals = s.locals.update (ofString lname, .val (.word r)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_word") [dstExp, wExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, wExp] with _ | vals
  · simp [evalListHOLFinite, hargs] at hres; exact False.elim (not_resumes_error hres)
  · simp only [evalListHOLFinite, hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_word") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hres; exact False.elim (not_resumes_error hres)
    · simp only [hl] at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_word")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_word) hl
      have hret := lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_word")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_word) hl
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_word") vals =
          some (body', callee, ret') := by rw [← hcode]; exact hl
      subst hsame; subst hret
      obtain ⟨dst0, w0, rfl, hc_dst, hc_w⟩ := lookupCode_two_words (by decide)
        lookup_rlp_encode_word hl_orig
      simp only [evalListHOLExact, Option.some.injEq, List.cons.injEq] at hargs
      rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | v1
      · simp [hv1] at hargs
      · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) wExp with _ | v2
        · simp [hv1, hv2] at hargs
        · simp only [hv1, hv2, Option.some.injEq, List.cons.injEq, and_true] at hargs
          obtain ⟨rfl, rfl⟩ := hargs
          by_cases hz : s.clock = 0
          · simp [hz] at hnt
          · rw [if_neg hz] at hnt hres ⊢
            set ent := callEntryStateHOLFinite s callee
            rcases hrun : evaluateHOLFiniteState ent
                (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨rb, pb⟩
            have hnt_b : rb ≠ some .timeOut := by rintro rfl; simp [hrun] at hnt
            have hres_b : Resumes rb := by
              cases rb with
              | none => simp [hrun] at hres; exact False.elim (not_resumes_error hres)
              | some cr =>
                cases cr with
                | returned v => exact Or.inl ⟨v, rfl⟩
                | exception eid ev =>
                  simp only [hrun] at hres
                  rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hne⟩
                  · simp at hc
                  · simp at hc; obtain ⟨rfl, rfl⟩ := hc; exact Or.inr ⟨eid, ev, rfl, hne⟩
                | _ => simp only [hrun] at hres; rcases hres with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
            obtain ⟨r, hrb, hr1, hr9, hd_lt, heff_b⟩ := eval_rlp_encode_word_body ent dst0 w0 (Rfn dst0)
              hcode (guestInv_callEntry s callee hG) hc_dst hc_w (hin_ivl dst0)
              (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_b)
            rw [hrun] at hrb heff_b; dsimp only at hrb heff_b; subst hrb
            have hsh_r : (shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one &&
                shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one) = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            rw [hrun] at hnt hres
            dsimp only at hnt hres ⊢
            rw [if_pos hsh_r] at hnt hres ⊢
            let mid := setVarHOLFinite (ofString lname) (.val (.word r)) { pb with locals := s.locals }
            exact ⟨dst0, w0, r, mid, rfl, rfl, hr1, hr9, hd_lt,
              (((ByteEff.refl s _).locals_clock _ _).trans heff_b).locals_clock _ _,
              rfl, hnt, hres, rfl⟩

theorem eval_decCall_rlp_encode_bytes_bounded {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp srcExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hn_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hn_le : n0.toNat ≤ 55)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + (n0.toNat + 1) ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).1) :
    ∃ (r : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      1 ≤ r.toNat ∧ r.toNat ≤ n0.toNat + 1 ∧ dst0.toNat < heapEnd ∧
      ByteEff s mid Rl ∧
      mid.locals = s.locals.update (ofString lname, .val (.word r)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_encode_bytes") [dstExp, srcExp, nExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, nExp] with _ | vals
  · simp [evalListHOLFinite, hargs] at hres; exact False.elim (not_resumes_error hres)
  · simp only [evalListHOLFinite, hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_bytes") vals with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hres; exact False.elim (not_resumes_error hres)
    · simp only [hl] at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_bytes")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_bytes) hl
      have hret := lookupCodeHOLFinite_installed_return s (ofString "rlp_encode_bytes")
        _ _ body' _ ret' vals callee (by rw [hcode]; exact lookup_rlp_encode_bytes) hl
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "rlp_encode_bytes") vals =
          some (body', callee, ret') := by rw [← hcode]; exact hl
      subst hsame; subst hret
      obtain ⟨d', src0, n', hvals_eq, hc_dst, hc_src, hc_n⟩ := lookupCode_three_words
        (by decide) (by decide) (by decide) lookup_rlp_encode_bytes hl_orig
      subst hvals_eq
      rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) srcExp with _ | v2
      · simp [evalListHOLExact, hdst_ev, hv2] at hargs
      · simp only [evalListHOLExact, hdst_ev, hv2, hn_ev, Option.some.injEq, List.cons.injEq, and_true,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        by_cases hz : s.clock = 0
        · simp [hz] at hnt
        · rw [if_neg hz] at hnt hres ⊢
          set ent := callEntryStateHOLFinite s callee
          rcases hrun : evaluateHOLFiniteState ent
              (sourceFnBody Guest.Software.guestFn_rlp_encode_bytes) with ⟨rb, pb⟩
          have hnt_b : rb ≠ some .timeOut := by rintro rfl; simp [hrun] at hnt
          have hres_b : Resumes rb := by
            cases rb with
            | none => simp [hrun] at hres; exact False.elim (not_resumes_error hres)
            | some cr =>
              cases cr with
              | returned v => exact Or.inl ⟨v, rfl⟩
              | exception eid ev =>
                simp only [hrun] at hres
                rcases hres with ⟨_, hc⟩ | ⟨e', v', hc, hne⟩
                · simp at hc
                · simp at hc; obtain ⟨rfl, rfl⟩ := hc; exact Or.inr ⟨eid, ev, rfl, hne⟩
              | _ => simp only [hrun] at hres; rcases hres with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
          obtain ⟨r, hrb, hr1, hr9, hd_lt, heff_b⟩ := eval_rlp_encode_bytes_bounded ent dst0 src0 n0 Rl
            hcode (guestInv_callEntry s callee hG) hc_dst hc_src hc_n hn_le hin_ivl
            (by rw [hrun]; exact hnt_b) (by rw [hrun]; exact hres_b)
          rw [hrun] at hrb heff_b; dsimp only at hrb heff_b; subst hrb
          have hsh_r : (shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one &&
              shapeEqHOL (shapeOfHOLExact (.val (.word r) : ValueHOL 64)) .one) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [hrun] at hnt hres
          dsimp only at hnt hres ⊢
          rw [if_pos hsh_r] at hnt hres ⊢
          let mid := setVarHOLFinite (ofString lname) (.val (.word r)) { pb with locals := s.locals }
          exact ⟨r, mid, hr1, hr9, hd_lt,
            (((ByteEff.refl s _).locals_clock _ _).trans heff_b).locals_clock _ _,
            rfl, hnt, hres, rfl⟩

/-! ## 5. Proof of `wk_encode_account` -/

private def encodeAcctZeroLoop : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
    (.seq
      (.ite (.cmp .notEqual
          (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
          (.const (0#64)))
        .break .skip)
      (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))

private theorem eval_encodeAcctZeroLoop {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (zw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "z") = some (.val (.word zw)) →
      zw.toNat ≤ 32 →
      (evaluateHOLFiniteState s encodeAcctZeroLoop).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s encodeAcctZeroLoop).1 = none →
        ∃ zw' : BitVec 64,
          zw'.toNat ≤ 32 ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoop).2.locals =
            s.locals.update (ofString "z", .val (.word zw')) ∧
          (evaluateHOLFiniteState s encodeAcctZeroLoop).2 =
            { s with locals := (evaluateHOLFiniteState s encodeAcctZeroLoop).2.locals,
                     clock := (evaluateHOLFiniteState s encodeAcctZeroLoop).2.clock }) ∧
      ((evaluateHOLFiniteState s encodeAcctZeroLoop).1 ≠ none →
        ¬ Resumes (evaluateHOLFiniteState s encodeAcctZeroLoop).1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s zw hclk hz hzw_le hnt
    unfold encodeAcctZeroLoop at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "z")) (.const (32#64))) =
        some (.val (.word (if zw.toNat < 32 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hz, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hlt : zw.toNat < 32
    · rw [if_pos hlt, if_pos (by decide : (1 : BitVec 64) ≠ 0)] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        let sd := decClockHOLFinite s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        rcases hev_lb : @evalHOLExact 64 F _ sd.toExact (fun a => Classical.propDecidable (sd.memaddrs a))
            (.cmp .notEqual
              (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
              (.const (0#64))) with _ | cv
        · simp [sd, hev_lb] at hnt ⊢; exact not_resumes_error
        · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp [sd, hev_lb] at hnt ⊢; exact not_resumes_error)
          simp only [sd, hev_lb] at hnt ⊢
          by_cases hcw0 : cw = 0
          · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hnt ⊢; dsimp only at hnt ⊢
            have hsd_z : (decClockHOLFinite s).locals.lookup (ofString "z") = some (.val (.word zw)) := hz
            have hasg : evaluateHOLFiniteState (decClockHOLFinite s)
                (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])) =
                (none, setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hsd_z,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg] at hnt ⊢; dsimp only at hnt ⊢
            let s1 := setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s)
            have hs1_clk : s1.clock < k := by simp [s1, setVarHOLFinite, decClockHOLFinite, hclk]; omega
            have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word (zw + 1#64))) := by
              simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hzw1 : (zw + 1#64).toNat = zw.toNat + 1 :=
              BitVec.toNat_add_of_lt (by change zw.toNat + 1 < 2 ^ 64; omega)
            obtain ⟨ih1, ih2⟩ := ih s1.clock hs1_clk s1 (zw + 1#64) rfl hs1_z (by omega) hnt
            refine ⟨fun hn => ?_, ih2⟩
            obtain ⟨zw', hle', hloc', heq'⟩ := ih1 hn
            have hloc'' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s))
                (.while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
                  (.seq
                    (.ite (.cmp .notEqual
                        (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
                        (.const (0#64)))
                      .break .skip)
                    (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)]))))).2.locals =
                s1.locals.update (ofString "z", .val (.word zw')) := hloc'
            have heq'' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "z") (.val (.word (zw + 1#64))) (decClockHOLFinite s))
                (.while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
                  (.seq
                    (.ite (.cmp .notEqual
                        (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
                        (.const (0#64)))
                      .break .skip)
                    (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)]))))).2 =
                { s1 with locals := (evaluateHOLFiniteState s1 encodeAcctZeroLoop).2.locals,
                          clock := (evaluateHOLFiniteState s1 encodeAcctZeroLoop).2.clock } := heq'
            refine ⟨zw', hle', ?_, ?_⟩
            · rw [hloc'']
              apply HolFiniteMapExact.ext_lookup; intro m
              by_cases hm : m = ofString "z"
              · subst hm; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s1, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hm, Ne.symm hm]
            · rw [heq'']; simp [s1, encodeAcctZeroLoop, setVarHOLFinite, decClockHOLFinite]
          · rw [if_neg hcw0, evaluateHOLFiniteState_break]
            dsimp only
            refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
            apply HolFiniteMapExact.ext_lookup; intro m
            by_cases hm : m = ofString "z"
            · subst hm; simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hz]
            · simp [decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
    · rw [if_neg hlt, if_neg (by decide : ¬ ((0 : BitVec 64) ≠ 0))]
      refine ⟨fun _ => ⟨zw, hzw_le, ?_, by cases s; rfl⟩, fun h => False.elim (h rfl)⟩
      apply HolFiniteMapExact.ext_lookup; intro m
      by_cases hm : m = ofString "z"
      · subst hm; simp [HolFiniteMapExact.lookup_update, FUPDATE, hz]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]

theorem wk_encode_account_impl :
    WorldKeeps WorldOK
      (fun s => [(locN s "out", 110),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      [] stdKeep NoExtra (ofString "encode_account") := by
  refine ⟨_, _, _, lookup_encode_account, fun {F} s hcode hWOK _ hnt hres => ?_⟩
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
  let Rl : List Ivl :=
    [(locN s "out", 110), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]
  refine ByteEff.to_worldStep hWOK ?_
  change ByteEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_encode_account)).2 Rl
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_encode_account,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil, List.map] at hnt hres ⊢
  -- Step 1: `var off = 2`
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt hres ⊢
  let s0 := setVarHOLFinite (ofString "off") (.val (.word (2#64))) s
  have hGs0 : GuestInv s0 := guestInv_setVar _ _ s hWOK.1.1
  have hs0_off : s0.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_other : ∀ m, m ≠ ofString "off" → s0.locals.lookup m = s.locals.lookup m := fun m hm => by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm]
  -- Step 2: `var 1 w = rlp_encode_word(out + off, nonce)`
  obtain ⟨dst1, nonce0, w1, s1, hdst1_ev, _, hw1_lo, hw1_hi, hdst1_lt_he, heff1, hs1_loc, hnt1, hres1, hpost1⟩ :=
    eval_decCall_rlp_encode_word_resumes s0 "w"
      (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
      (.var .local (ofString "nonce")) _
      (fun d => [(d.toNat, 9)]) hcode hGs0
      (fun d => ⟨(d.toNat, 9), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      hnt hres
  -- Extract `out0 : BitVec 64` from `hdst1_ev`:
  have hout_ex : ∃ out0 : BitVec 64, s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      dst1 = out0 + 2 := by
    have hout_s0 := hs0_other (ofString "out") (by decide)
    rcases hout_lk : s.locals.lookup (ofString "out") with _ | ov
    · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off] at hdst1_ev
    · rcases ov with ⟨⟨out0⟩⟩ | _ | _
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, wordOpHOL, wordOp,
          valueIsWord, valueWord] at hdst1_ev
        exact ⟨out0, rfl, hdst1_ev.symm⟩
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
      · simp [evalHOLExact, evalListHOLExact, hout_s0, hout_lk, hs0_off, valueIsWord] at hdst1_ev
  obtain ⟨out0, hs_out, rfl⟩ := hout_ex
  have hout_nat : locN s "out" = out0.toNat := by simp [locN, hs_out]
  -- Notice: could `out0 + 2` wrap `2^64`? Look at the end of `encode_account`: it executes `storeByte out 248`!
  -- Wait: if an earlier step errors, `Resumes` is false! Wait: `encode_account` has NO `raise` and none of its callees (`rlp_encode_word`, `st_be64`, `rlp_encode_bytes`) can raise ANY exception!
  -- Wait: let's check! If `encode_account` resumes, MUST it reach `storeByte out 248`?
  -- YES! Because NO statement in `encode_account` can return early or raise a catchable exception!
  -- Every callee (`rlp_encode_word`, `st_be64`, `rlp_encode_bytes`) is called via `decCall` or `call (some (none, none))` and NEVER raises any exception!
  -- Therefore, if `Resumes` holds at the top of `encode_account`, EVERY step in `encode_account` MUST succeed with `none` until the final `storeByte out 248; storeByte (out + 1) ...; return off`!
  -- And `storeByte out 248` succeeding proves `sourceBase ≤ out0.toNat ∧ out0.toNat + 1 ≤ heapEnd`!
  -- Wait: if `out0.toNat < heapEnd`, then `(out0 + 2).toNat = out0.toNat + 2` WITHOUT WRAPAROUND!
  -- Let's check that! That's SO CLEAN!
  dsimp only [s0] at hpost1
  rw [hpost1]
  -- Helper: `st_be64` and `st_be32` and `bswap64` never raise catchable exceptions:
  have hncr_be : ∀ f, (f == ofString "st_be64" || f == ofString "st_be32" || f == ofString "bswap64") = true →
      ∀ values body callee rs, lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
        noCatchableRaise (fun g => g == ofString "st_be64" || g == ofString "st_be32" || g == ofString "bswap64") body = true := by
    intro f hf values body callee rs hfound
    obtain ⟨params, rs', hinst⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hfound
    simp only [Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with (rfl | rfl) | rfl
    · have hl := lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_st_be64) rfl
      change originalRuntimeCode.lookup (ofString "st_be64") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
    · have hl := lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_st_be32) rfl
      change originalRuntimeCode.lookup (ofString "st_be32") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
    · have hl := lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bswap64) rfl
      change originalRuntimeCode.lookup (ofString "bswap64") = _ at hl
      rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  have call0_be64_not_resumes : ∀ (cur : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64),
      cur.code = originalRuntimeCode →
      ¬ Resumes (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 := by
    intro cur pExp vExp hcc
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] with _ | vals
    · exact not_resumes_error
    · dsimp only
      rcases hl : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") vals with _ | ⟨b, c, rs⟩
      · exact not_resumes_error
      · dsimp only
        split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have hbok := hncr_be (ofString "st_be64") (by decide) vals b c rs (by rwa [← hcc])
          have hncr := evaluate_noCatchableRaise _ hncr_be b hbok (callEntryStateHOLFinite cur c) hcc
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite cur c) b with ⟨rb, pb⟩
          rw [hrun] at hncr
          cases rb with
          | none => exact not_resumes_error
          | some rb' =>
            cases rb' with
            | returned _ => dsimp only; split <;> [ (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h); exact not_resumes_error ]
            | exception eid ev =>
              rintro (⟨_, h⟩ | ⟨e', v', h, hne⟩)
              · simp at h
              · injection h with h'; injection h' with h1 h2; subst h1 h2; exact hncr eid ev hne rfl
            | _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  -- Also extract `phs` (`mpt_hash_scratch`) and `balance` words from `s`:
  obtain ⟨phs, hphs_g⟩ := hWOK.1.2.2.2.2.2.2.2.2.2 "mpt_hash_scratch" (by decide)
  have hphs_nat : globN s "mpt_hash_scratch" = phs.toNat := by
    unfold GlobalWord at hphs_g; simp [globN, hphs_g]
  -- Wait: if `mpt_hash_scratch = 0`, `st_be64(0, ...)` will fail `ordinaryDomain` and NOT resume!
  -- Let's prove `phs ≠ 0` and `phs.toNat + 32 ≤ heapEnd` from the first `st_be64` call succeeding!
  have st_be64_dom_of_none : ∀ (cur : PanSemStateFiniteExact 64 F) (pExp vExp : ExpHOL 64) (pw : BitVec 64),
      cur.code = originalRuntimeCode → GuestInv cur →
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) pExp =
        some (.val (.word pw)) →
      (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).1 = none →
      sourceBase ≤ pw.toNat ∧ ByteEff cur
        (evaluateHOLFiniteState cur (.call (some (none, none)) (ofString "st_be64") [pExp, vExp])).2
        [(pw.toNat, 8)] := by
    intro cur pExp vExp pw hcc hGc hp_ev hnone
    have hlook64 : originalRuntimeCode.lookup (ofString "st_be64") =
        some ([(ofString "p", .one), (ofString "v", .one)],
          sourceFnBody Guest.Software.guestFn_st_be64, .one) :=
      lookup_of_guestAst_getElem 28 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_st_be64) rfl
    have hv_ex : ∃ vw : BitVec 64,
        @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) vExp =
          some (.val (.word vw)) := by
      have hnone' := hnone
      rw [evaluateHOLFiniteState_call] at hnone'
      rcases hv_ev : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) vExp with _ | vv
      · simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev] at hnone'
      · rcases vv with ⟨⟨vw⟩⟩ | flds | ⟨nm, flds⟩
        · exact ⟨vw, rfl⟩
        · have ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
              some [.val (.word pw), .rStruct flds] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
          rw [ha] at hnone'; dsimp only at hnone'
          have hl0 : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") [.val (.word pw), .rStruct flds] = none := by
            apply Option.eq_none_iff_forall_not_mem.2; intro ⟨b, c, r⟩ hm
            have hx := lookupCodeHOLFinite_eq_some cur.code.lookup _ _ b c r hm
            rw [hcc] at hx; simp [lookupCodeHOLExact, hlook64, shapeOfHOLExact, shapeEqHOL] at hx
          rw [hl0] at hnone'; simp at hnone'
        · have ha : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
              some [.val (.word pw), .nStruct nm flds] := by simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
          rw [ha] at hnone'; dsimp only at hnone'
          have hl0 : lookupCodeHOLFinite cur.code.lookup (ofString "st_be64") [.val (.word pw), .nStruct nm flds] = none := by
            apply Option.eq_none_iff_forall_not_mem.2; intro ⟨b, c, r⟩ hm
            have hx := lookupCodeHOLFinite_eq_some cur.code.lookup _ _ b c r hm
            rw [hcc] at hx; simp [lookupCodeHOLExact, hlook64, shapeOfHOLExact, shapeEqHOL] at hx
          rw [hl0] at hnone'; simp at hnone'
    obtain ⟨vw, hv_ev⟩ := hv_ex
    have hargs : evalListHOLFinite cur (h := fun a => Classical.propDecidable (cur.memaddrs a)) [pExp, vExp] =
        some [.val (.word pw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    have heff := call0_byteEff funByteEff_st_be64 cur [pExp, vExp] [(pw.toNat, 8)] hcc hGc
      (fun vs hvs iv hiv _ => by
        rw [hargs] at hvs; injection hvs with hvs; subst hvs
        simp [valWordNat] at hiv; subst hiv
        exact ⟨(pw.toNat, 8), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
      (by rw [hnone]; simp) (Or.inl hnone)
    -- Prove `sourceBase ≤ pw.toNat`: if `pw.toNat < sourceBase`, neither `store pw` nor `storeByte pw` can succeed!
    have hlo : sourceBase ≤ pw.toNat := by
      obtain ⟨_, rv, hrv⟩ := call0_two_word_success cur _ _ _ _ _ _ pw vw (by decide) hcc hlook64 hargs hnone
      let ent := callEntryStateHOLFinite cur
        ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pw))).update (ofString "v", .val (.word vw)))
      have hp_ent : ent.locals.lookup (ofString "p") = some (.val (.word pw)) := by
        simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "v" ≠ ofString "p" by decide]
      have hv_ent : ent.locals.lookup (ofString "v") = some (.val (.word vw)) := by
        simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hGent : GuestInv ent := guestInv_callEntry cur _ hGc
      have hbody64 : sourceFnBody Guest.Software.guestFn_st_be64 =
          .seq (.ite (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0))
              (.decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
                (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
                  (.return (.const 0))))
              .skip)
            (.seq (.call (some (none, none)) (ofString "st_be32")
                [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)])
              (.seq (.call (some (none, none)) (ofString "st_be32")
                  [.op .add [.var .local (ofString "p"), .const 4], .var .local (ofString "v")])
                (.return (.const 0)))) := rfl
      change (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_st_be64)).1 = some (.returned rv) at hrv
      rw [hbody64, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrv
      have hc7 : @evalHOLExact 64 F _ ent.toExact (fun a => Classical.propDecidable (ent.memaddrs a))
          (.cmp .equal (.op .and [.var .local (ofString "p"), .const 7]) (.const 0)) =
          some (.val (.word (if pw &&& 7 = 0 then 1 else 0))) := by
        simp [evalHOLExact, evalListHOLExact, hp_ent, wordOpHOL, wordOp, valueIsWord, valueWord,
          Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc7] at hrv; dsimp only at hrv
      by_cases hp7 : pw &&& 7 = 0
      · rw [if_pos hp7, if_neg (by decide : ¬ ((1 : BitVec 64) = 0))] at hrv
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrv
        have hvbs : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
            [.var .local (ofString "v")] = some [.val (.word vw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hv_ent]
        rw [hvbs] at hrv; dsimp only at hrv
        rcases hlbs : lookupCodeHOLFinite ent.code.lookup (ofString "bswap64") [.val (.word vw)] with _ | ⟨bbs, cbs, rsbs⟩
        · simp [hlbs] at hrv
        · simp only [hlbs] at hrv
          by_cases hclk_ent : ent.clock = 0
          · simp [hclk_ent] at hrv
          · rw [if_neg hclk_ent] at hrv
            set ent_bs := callEntryStateHOLFinite ent cbs
            have hG_pbs_raw := guestInv_evaluate ent_bs bbs (guestInv_callEntry ent cbs hGent)
            rcases hrun_bs : evaluateHOLFiniteState ent_bs bbs with ⟨_ | rbs, pbs⟩
            · simp [hrun_bs] at hrv
            · rw [hrun_bs] at hG_pbs_raw hrv
              dsimp only at hrv
              cases rbs with
              | returned rv_bs =>
                dsimp only at hrv
                by_cases hsh_bs : (shapeEqHOL (shapeOfHOLExact rv_bs) .one && shapeEqHOL (shapeOfHOLExact rv_bs) rsbs) = true
                · rw [if_pos hsh_bs] at hrv
                  rcases rv_bs with ⟨⟨wv⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh_bs)
                  set st_w := setVarHOLFinite (ofString "w") (.val (.word wv)) { pbs with locals := ent.locals }
                  have hGw : GuestInv st_w := guestInv_setVar _ _ _
                    (guestInv_with_locals_clock pbs ent.locals pbs.clock hG_pbs_raw)
                  have hp_w : st_w.locals.lookup (ofString "p") = some (.val (.word pw)) := by
                    simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_ent,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_w : st_w.locals.lookup (ofString "w") = some (.val (.word wv)) := by
                    simp [st_w, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780] at hrv
                  have hcf_st := evaluate_store_control_frame st_w (.var .local (ofString "p")) (.var .local (ofString "w"))
                  rcases hst : evaluateHOLFiniteState st_w
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, mst⟩
                  rw [hst] at hcf_st
                  rcases hcf_st.1 with hrst | hrst
                  · subst hrst
                    obtain ⟨x, hx, hdlo, _, _⟩ := store_one_domain hGw (.var .local (ofString "p")) (.var .local (ofString "w"))
                      (fun v hv => by simp [evalHOLExact, hw_w] at hv; exact ⟨wv, hv.symm⟩)
                      (by rw [hst])
                    simp [evalHOLExact, hp_w] at hx; subst hx; exact hdlo
                  · subst hrst; simp [hst] at hrv
                · rw [if_neg hsh_bs] at hrv; simp at hrv
              | _ => simp at hrv
      · rw [if_neg hp7, if_pos rfl, evaluateHOLFiniteState_skip] at hrv; dsimp only at hrv
        rw [evaluateHOLFiniteState_seq_line780] at hrv
        have hlook32 : originalRuntimeCode.lookup (ofString "st_be32") =
            some ([(ofString "p", .one), (ofString "v", .one)],
              sourceFnBody Guest.Software.guestFn_st_be32, .one) :=
          lookup_of_guestAst_getElem 27 (by rw [guestAst_len]; decide)
            (extractFn Guest.Software.guestFn_st_be32) rfl
        have ha1 : evalListHOLFinite ent (h := fun a => Classical.propDecidable (ent.memaddrs a))
            [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)] =
            some [.val (.word pw), .val (.word (vw >>> 32))] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hp_ent, hv_ent, wordShiftHOL]
        rcases hc1 : evaluateHOLFiniteState ent
            (.call (some (none, none)) (ofString "st_be32")
              [.var .local (ofString "p"), .shift .lsr (.var .local (ofString "v")) (.const 32)]) with ⟨rc1, m1⟩
        rw [hc1] at hrv
        have hor1 : rc1 = none ∨ Resumes rc1 := by
          cases rc1 with
          | none => exact Or.inl rfl
          | some _ => exact Or.inr (Or.inl ⟨rv, hrv⟩)
        have hres1_b := call0_two_word_resumes ent _ _ _ _ _ _ pw (vw >>> 32) (by decide) hcc hlook32 ha1 (by rw [hc1]; exact hor1)
        exact (st_be32_body_eff _ pw (guestInv_callEntry ent _ hGent)
          (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide])
          hres1_b).2.1
    exact ⟨hlo, heff⟩
  -- Also under `WorldOK s`, if `phs ≠ 0`, `("mpt_hash_scratch", 40) ∈ globalBuffers` gives `phs.toNat + 40 ≤ heapLimit ≤ heapEnd`!
  have hphs_bound_if_nz : phs.toNat ≠ 0 → phs.toNat + 40 ≤ heapEnd := by
    intro hnz
    obtain ⟨hGI0, S0, hWT0⟩ := hWOK
    have hF0 := hWT0.2.2.1
    have hmf : (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40) ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.2 ⟨("mpt_hash_scratch", 40), by decide, rfl⟩
    rw [hphs_nat, if_neg hnz] at hmf
    rcases hF0.1 _ hmf with h0 | ⟨hal, _⟩
    · simp at h0
    · exact (ivl_allocated_bound hGI0.2 hal).1
  -- Now step cleanly through the remaining statements of `encode_account`!
  -- Collect raw intervals in `RawRl`:
  let RawRl (off2 off3 off4 : BitVec 64) : List Ivl :=
    [((out0 + 2).toNat, 9),
     ((out0 + off2).toNat, 41),
     ((out0 + off3).toNat, 41),
     ((out0 + off4).toNat, 41),
     (out0.toNat, 2),
     (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]
  -- Step 3: `off = off + w` (`2 + w1`)
  have hs1_code : s1.code = originalRuntimeCode := heff1.code.trans hcode
  have hGs1 : GuestInv s1 := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hGs0
  have hs1_off : s1.locals.lookup (ofString "off") = some (.val (.word (2#64))) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs0_off, show ofString "w" ≠ ofString "off" by decide]
  have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word w1)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
  have hasg_off1 : evaluateHOLFiniteState s1
      (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "off") (.val (.word ((2#64) + w1))) s1) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs1_off, hs1_w,
      wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
  rw [hasg_off1] at hnt1 hres1 ⊢; dsimp only at hnt1 hres1 ⊢
  set off2 := (2#64) + w1
  have hoff2_nat : off2.toNat = 2 + w1.toNat := BitVec.toNat_add_of_lt (by change 2 + w1.toNat < 2 ^ 64; omega)
  set s2 := setVarHOLFinite (ofString "off") (.val (.word off2)) s1
  have hs2_code : s2.code = originalRuntimeCode := hs1_code
  have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
  have hs2_glob : s2.globals = s.globals := heff1.globals
  -- Step 4a..4d: four `st_be64` calls into `mpt_hash_scratch + {0, 8, 16, 24}`:
  rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
  rcases hbe0 : evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "st_be64")
        [.var .global (ofString "mpt_hash_scratch"), .rfield 3 (.var .local (ofString "balance"))]) with ⟨rbe0, s3⟩
  rw [hbe0] at hnt1 hres1
  cases rbe0 with
  | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s2 _ _ hs2_code (by rw [hbe0]; exact hres1))
  | none =>
    dsimp only at hnt1 hres1 ⊢
    have hphs_s2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.var .global (ofString "mpt_hash_scratch")) = some (.val (.word phs)) := by
      change s2.globals.lookup _ = _; rw [hs2_glob]; exact hphs_g
    obtain ⟨hphs_lo, heff_be0⟩ := st_be64_dom_of_none s2
      (.var .global (ofString "mpt_hash_scratch")) (.rfield 3 (.var .local (ofString "balance")))
      phs hs2_code hGs2 hphs_s2 (by rw [hbe0])
    rw [hbe0] at heff_be0; dsimp only at heff_be0
    have hphs_nz : phs.toNat ≠ 0 := by omega
    have hphs_hi : phs.toNat + 40 ≤ heapEnd := hphs_bound_if_nz hphs_nz
    have hs3_loc : s3.locals = s2.locals := by
      have := call0_locals_r16 s2 (ofString "st_be64")
        [.var .global (ofString "mpt_hash_scratch"), .rfield 3 (.var .local (ofString "balance"))]
        (by rw [hbe0])
      rwa [hbe0] at this
    have hs3_code : s3.code = originalRuntimeCode := heff_be0.code.trans hs2_code
    have hGs3 : GuestInv s3 := guestInv_congr heff_be0.code heff_be0.memaddrs heff_be0.shMemaddrs heff_be0.baseAddr hGs2
    have hs3_glob : s3.globals = s.globals := heff_be0.globals.trans hs2_glob
    -- 2nd `st_be64`:
    rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
    rcases hbe1 : evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "st_be64")
          [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)],
           .rfield 2 (.var .local (ofString "balance"))]) with ⟨rbe1, s4⟩
    rw [hbe1] at hnt1 hres1
    cases rbe1 with
    | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s3 _ _ hs3_code (by rw [hbe1]; exact hres1))
    | none =>
      dsimp only at hnt1 hres1 ⊢
      have hphs_s3 : s3.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
        rw [hs3_glob]; exact hphs_g
      obtain ⟨_, heff_be1⟩ := st_be64_dom_of_none s3
        (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)])
        (.rfield 2 (.var .local (ofString "balance")))
        (phs + 8#64) hs3_code hGs3
        (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s3, wordOpHOL, wordOp, valueIsWord, valueWord])
        (by rw [hbe1])
      rw [hbe1] at heff_be1; dsimp only at heff_be1
      have hs4_loc : s4.locals = s2.locals := by
        have := call0_locals_r16 s3 (ofString "st_be64")
          [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (8#64)],
           .rfield 2 (.var .local (ofString "balance"))] (by rw [hbe1])
        rw [hbe1] at this; exact this.trans hs3_loc
      have hs4_code : s4.code = originalRuntimeCode := heff_be1.code.trans hs3_code
      have hGs4 : GuestInv s4 := guestInv_congr heff_be1.code heff_be1.memaddrs heff_be1.shMemaddrs heff_be1.baseAddr hGs3
      have hs4_glob : s4.globals = s.globals := heff_be1.globals.trans hs3_glob
      -- 3rd `st_be64`:
      rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
      rcases hbe2 : evaluateHOLFiniteState s4
          (.call (some (none, none)) (ofString "st_be64")
            [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)],
             .rfield 1 (.var .local (ofString "balance"))]) with ⟨rbe2, s5⟩
      rw [hbe2] at hnt1 hres1
      cases rbe2 with
      | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s4 _ _ hs4_code (by rw [hbe2]; exact hres1))
      | none =>
        dsimp only at hnt1 hres1 ⊢
        have hphs_s4 : s4.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
          rw [hs4_glob]; exact hphs_g
        obtain ⟨_, heff_be2⟩ := st_be64_dom_of_none s4
          (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)])
          (.rfield 1 (.var .local (ofString "balance")))
          (phs + 16#64) hs4_code hGs4
          (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s4, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by rw [hbe2])
        rw [hbe2] at heff_be2; dsimp only at heff_be2
        have hs5_loc : s5.locals = s2.locals := by
          have := call0_locals_r16 s4 (ofString "st_be64")
            [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (16#64)],
             .rfield 1 (.var .local (ofString "balance"))] (by rw [hbe2])
          rw [hbe2] at this; exact this.trans hs4_loc
        have hs5_code : s5.code = originalRuntimeCode := heff_be2.code.trans hs4_code
        have hGs5 : GuestInv s5 := guestInv_congr heff_be2.code heff_be2.memaddrs heff_be2.shMemaddrs heff_be2.baseAddr hGs4
        have hs5_glob : s5.globals = s.globals := heff_be2.globals.trans hs4_glob
        -- 4th `st_be64`:
        rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
        rcases hbe3 : evaluateHOLFiniteState s5
            (.call (some (none, none)) (ofString "st_be64")
              [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)],
               .rfield 0 (.var .local (ofString "balance"))]) with ⟨rbe3, s6⟩
        rw [hbe3] at hnt1 hres1
        cases rbe3 with
        | some _ => dsimp only at hres1; exact False.elim (call0_be64_not_resumes s5 _ _ hs5_code (by rw [hbe3]; exact hres1))
        | none =>
          dsimp only at hnt1 hres1 ⊢
          have hphs_s5 : s5.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word phs)) := by
            rw [hs5_glob]; exact hphs_g
          obtain ⟨_, heff_be3⟩ := st_be64_dom_of_none s5
            (.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)])
            (.rfield 0 (.var .local (ofString "balance")))
            (phs + 24#64) hs5_code hGs5
            (by simp [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hphs_s5, wordOpHOL, wordOp, valueIsWord, valueWord])
            (by rw [hbe3])
          rw [hbe3] at heff_be3; dsimp only at heff_be3
          have hs6_loc : s6.locals = s2.locals := by
            have := call0_locals_r16 s5 (ofString "st_be64")
              [.op .add [.var .global (ofString "mpt_hash_scratch"), .const (24#64)],
               .rfield 0 (.var .local (ofString "balance"))] (by rw [hbe3])
            rw [hbe3] at this; exact this.trans hs5_loc
          have hs6_code : s6.code = originalRuntimeCode := heff_be3.code.trans hs5_code
          have hGs6 : GuestInv s6 := guestInv_congr heff_be3.code heff_be3.memaddrs heff_be3.shMemaddrs heff_be3.baseAddr hGs5
          have hs6_glob : s6.globals = s.globals := heff_be3.globals.trans hs5_glob
          -- Combine all 4 `st_be64` effects into `[bufferRegion s ("mpt_hash_scratch", 40)]`:
          have hphs8 : (phs + 8#64).toNat = phs.toNat + 8 := BitVec.toNat_add_of_lt (by change phs.toNat + 8 < 2 ^ 64; omega)
          have hphs16 : (phs + 16#64).toNat = phs.toNat + 16 := BitVec.toNat_add_of_lt (by change phs.toNat + 16 < 2 ^ 64; omega)
          have hphs24 : (phs + 24#64).toNat = phs.toNat + 24 := BitVec.toNat_add_of_lt (by change phs.toNat + 24 < 2 ^ 64; omega)
          have heff_be_all : ByteEff s2 s6 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] := by
            have h0 : ByteEff s2 s3 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be0.mono (fun iv hiv _ => by
                simp at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h1 : ByteEff s3 s4 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be1.mono (fun iv hiv _ => by
                simp [hphs8] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h2 : ByteEff s4 s5 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be2.mono (fun iv hiv _ => by
                simp [hphs16] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            have h3 : ByteEff s5 s6 [(globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)] :=
              heff_be3.mono (fun iv hiv _ => by
                simp [hphs24] at hiv; subst hiv
                exact ⟨_, List.mem_singleton.2 rfl, by simp [hphs_nat, hphs_nz], by simp [hphs_nat, hphs_nz]⟩)
            exact ((h0.trans h1).trans h2).trans h3
          -- Step 5: `dec "z" 0` + `while (z <+ 32)`
          rw [evaluateHOLFiniteState_dec_total] at hnt1 hres1 ⊢
          simp only [evalHOLExact, shapeEqHOL, shapeOfHOLExact, ↓reduceIte] at hnt1 hres1 ⊢
          set s7 := setVarHOLFinite (ofString "z") (.val (.word (0#64))) s6
          have hs7_z : s7.locals.lookup (ofString "z") = some (.val (.word (0#64))) := by
            simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [evaluateHOLFiniteState_seq_line780] at hnt1 hres1 ⊢
          dsimp only at hnt1 hres1 ⊢
          rcases hzl : evaluateHOLFiniteState s7 encodeAcctZeroLoop with ⟨rzl, s8⟩
          have hzl' : evaluateHOLFiniteState s7
              (.while (.cmp .lower (.var .local (ofString "z")) (.const (32#64)))
                (.seq
                  (.ite (.cmp .notEqual
                      (.loadByte (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")]))
                      (.const (0#64)))
                    .break .skip)
                  (.assign .local (ofString "z") (.op .add [.var .local (ofString "z"), .const (1#64)])))) =
              (rzl, s8) := hzl
          rw [hzl'] at hnt1 hres1 ⊢
          have hnt_zl : rzl ≠ some .timeOut := by rintro rfl; simp at hnt1
          have hzl_spec := eval_encodeAcctZeroLoop s7.clock s7 (0#64) rfl hs7_z (by decide) (by rw [hzl]; exact hnt_zl)
          rw [hzl] at hzl_spec
          cases rzl with
          | some _ => dsimp only at hres1; exact False.elim (hzl_spec.2 (by simp) hres1)
          | none =>
            dsimp only at hnt1 hres1 hzl_spec ⊢
            obtain ⟨zw, hzw_le, hs8_loc, hs8_eq⟩ := hzl_spec.1 rfl
            have hs8_code : s8.code = originalRuntimeCode := by rw [hs8_eq]; exact hs6_code
            have hGs8 : GuestInv s8 := by
              rw [hs8_eq]
              exact guestInv_with_locals_clock s7 _ _ (guestInv_setVar _ _ s6 hGs6)
            have hs8_z : s8.locals.lookup (ofString "z") = some (.val (.word zw)) := by
              rw [hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            have hs8_other : ∀ m, m ≠ ofString "z" → s8.locals.lookup m = s2.locals.lookup m := by
              intro m hm
              rw [hs8_loc]; simp [s7, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm, Ne.symm hm, hs6_loc]
            have hs8_out : s8.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs1_loc,
                show ofString "w" ≠ ofString "out" by decide,
                hs0_other (ofString "out") (by decide), hs_out]
            have hs8_off : s8.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs8_other _ (by decide)]
              simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have h32z_nat : ((32#64) - zw).toNat = 32 - zw.toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hzw_le)]; rfl
            -- Step 6: `var 1 wb = rlp_encode_bytes(out + off, mpt_hash_scratch + z, 32 - z)`
            obtain ⟨wb, s9, hwb_lo, hwb_hi, _, heff_wb, hs9_loc, hnt9, hres9, hpost9⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s8 "wb"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.op .add [.var .global (ofString "mpt_hash_scratch"), .var .local (ofString "z")])
                (.op .sub [.const (32#64), .var .local (ofString "z")])
                (out0 + off2) ((32#64) - zw) _
                [((out0 + off2).toNat, 33)] hs8_code hGs8
                (by simp [evalHOLExact, evalListHOLExact, hs8_out, hs8_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by simp [evalHOLExact, evalListHOLExact, hs8_z, wordOpHOL, wordOp, valueIsWord, valueWord])
                (by omega)
                ⟨((out0 + off2).toNat, 33), List.mem_singleton.2 rfl, le_rfl, by rw [h32z_nat]; omega⟩
                hnt1 hres1
            have hwb_33 : wb.toNat ≤ 33 := by rw [h32z_nat] at hwb_hi; omega
            rw [hpost9]
            -- Step 7: `off = off + wb` (`off3 = off2 + wb`)
            have hs9_code : s9.code = originalRuntimeCode := heff_wb.code.trans hs8_code
            have hGs9 : GuestInv s9 := guestInv_congr heff_wb.code heff_wb.memaddrs heff_wb.shMemaddrs heff_wb.baseAddr hGs8
            have hs9_off : s9.locals.lookup (ofString "off") = some (.val (.word off2)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs8_off, show ofString "wb" ≠ ofString "off" by decide]
            have hs9_wb : s9.locals.lookup (ofString "wb") = some (.val (.word wb)) := by
              rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt9 hres9 ⊢
            have hasg_off2 : evaluateHOLFiniteState s9
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wb")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off2 + wb))) s9) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs9_off, hs9_wb,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off2] at hnt9 hres9 ⊢; dsimp only at hnt9 hres9 ⊢
            set off3 := off2 + wb
            have hoff3_nat : off3.toNat = off2.toNat + wb.toNat :=
              BitVec.toNat_add_of_lt (by change off2.toNat + wb.toNat < 2 ^ 64; omega)
            set s10 := setVarHOLFinite (ofString "off") (.val (.word off3)) s9
            have hs10_code : s10.code = originalRuntimeCode := hs9_code
            have hGs10 : GuestInv s10 := guestInv_setVar _ _ s9 hGs9
            have hs10_out : s10.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs9_loc,
                show ofString "wb" ≠ ofString "out" by decide, hs8_out]
            have hs10_off : s10.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            -- Step 8: `var 1 wsl = rlp_encode_bytes(out + off, storage_root, 32)`
            have h32_lit : (32#64).toNat = 32 := rfl
            obtain ⟨wsl, s11, hwsl_lo, hwsl_hi, _, heff_wsl, hs11_loc, hnt11, hres11, hpost11⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s10 "wsl"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "storage_root")) (.const (32#64))
                (out0 + off3) (32#64) _ [((out0 + off3).toNat, 33)] hs10_code hGs10
                (by simp [evalHOLExact, evalListHOLExact, hs10_out, hs10_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide)
                ⟨((out0 + off3).toNat, 33), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
                hnt9 hres9
            have hwsl_33 : wsl.toNat ≤ 33 := by rw [h32_lit] at hwsl_hi; omega
            rw [hpost11]
            -- Step 9: `off = off + wsl` (`off4 = off3 + wsl`)
            have hs11_code : s11.code = originalRuntimeCode := heff_wsl.code.trans hs10_code
            have hGs11 : GuestInv s11 := guestInv_congr heff_wsl.code heff_wsl.memaddrs heff_wsl.shMemaddrs heff_wsl.baseAddr hGs10
            have hs11_off : s11.locals.lookup (ofString "off") = some (.val (.word off3)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs10_off, show ofString "wsl" ≠ ofString "off" by decide]
            have hs11_wsl : s11.locals.lookup (ofString "wsl") = some (.val (.word wsl)) := by
              rw [hs11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt11 hres11 ⊢
            have hasg_off3 : evaluateHOLFiniteState s11
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wsl")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off3 + wsl))) s11) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs11_off, hs11_wsl,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off3] at hnt11 hres11 ⊢; dsimp only at hnt11 hres11 ⊢
            set off4 := off3 + wsl
            have hoff4_nat : off4.toNat = off3.toNat + wsl.toNat :=
              BitVec.toNat_add_of_lt (by change off3.toNat + wsl.toNat < 2 ^ 64; omega)
            set s12 := setVarHOLFinite (ofString "off") (.val (.word off4)) s11
            have hs12_code : s12.code = originalRuntimeCode := hs11_code
            have hGs12 : GuestInv s12 := guestInv_setVar _ _ s11 hGs11
            have hs12_out : s12.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs11_loc,
                show ofString "wsl" ≠ ofString "out" by decide, hs10_out]
            have hs12_off : s12.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              simp [s12, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            -- Step 10: `var 1 wc = rlp_encode_bytes(out + off, code_hash, 32)`
            obtain ⟨wc, s13, hwc_lo, hwc_hi, _, heff_wc, hs13_loc, hnt13, hres13, hpost13⟩ :=
              eval_decCall_rlp_encode_bytes_bounded s12 "wc"
                (.op .add [.var .local (ofString "out"), .var .local (ofString "off")])
                (.var .local (ofString "code_hash")) (.const (32#64))
                (out0 + off4) (32#64) _ [((out0 + off4).toNat, 33)] hs12_code hGs12
                (by simp [evalHOLExact, evalListHOLExact, hs12_out, hs12_off, wordOpHOL, wordOp, valueIsWord, valueWord])
                rfl (by decide)
                ⟨((out0 + off4).toNat, 33), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩
                hnt11 hres11
            have hwc_33 : wc.toNat ≤ 33 := by rw [h32_lit] at hwc_hi; omega
            rw [hpost13]
            -- Step 11: `off = off + wc` (`off5 = off4 + wc`)
            have hGs13 : GuestInv s13 := guestInv_congr heff_wc.code heff_wc.memaddrs heff_wc.shMemaddrs heff_wc.baseAddr hGs12
            have hs13_off : s13.locals.lookup (ofString "off") = some (.val (.word off4)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs12_off, show ofString "wc" ≠ ofString "off" by decide]
            have hs13_wc : s13.locals.lookup (ofString "wc") = some (.val (.word wc)) := by
              rw [hs13_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hnt13 hres13 ⊢
            have hasg_off4 : evaluateHOLFiniteState s13
                (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"), .var .local (ofString "wc")])) =
                (none, setVarHOLFinite (ofString "off") (.val (.word (off4 + wc))) s13) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hs13_off, hs13_wc,
                wordOpHOL, wordOp, valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg_off4] at hnt13 hres13 ⊢; dsimp only at hnt13 hres13 ⊢
            set off5 := off4 + wc
            set s14 := setVarHOLFinite (ofString "off") (.val (.word off5)) s13
            have hGs14 : GuestInv s14 := guestInv_setVar _ _ s13 hGs13
            have hs14_out : s14.locals.lookup (ofString "out") = some (.val (.word out0)) := by
              simp [s14, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "off" ≠ ofString "out" by decide, hs13_loc,
                show ofString "wc" ≠ ofString "out" by decide, hs12_out]
            -- Step 12: `st8 out, 248` -> THIS PROVES `out0.toNat < heapEnd`!
            rw [evaluateHOLFiniteState_seq_line780] at hnt13 hres13 ⊢
            have hsb_248 := byteEff_storeByte hGs14 (.var .local (ofString "out")) (.const (248#64))
              (fun x hx _ => by
                simp [evalHOLExact, hs14_out] at hx; subst hx
                exact ⟨(out0.toNat, 2), List.mem_singleton.2 rfl, le_rfl, by omega⟩)
            have hcf_248 := evaluate_storeByte_control_frame s14 (.var .local (ofString "out")) (.const (248#64))
            rcases hst248 : evaluateHOLFiniteState s14 (.storeByte (.var .local (ofString "out")) (.const (248#64))) with ⟨r248, s15⟩
            rw [hst248] at hsb_248 hcf_248 hres13
            dsimp only at hsb_248 hcf_248 hres13 ⊢
            rcases hcf_248.1 with hr248 | hr248
            · subst hr248
              dsimp only at hres13 ⊢
              obtain ⟨x, hx, _, hout_hi⟩ := hsb_248.2 rfl
              simp [evalHOLExact, hs14_out] at hx; subst hx
              -- BINGO! `out0.toNat + 1 ≤ heapEnd < 2^64`!
              -- Now NONE of `out0 + 2`, `out0 + off2`, `out0 + off3`, `out0 + off4`, `out0 + 1` can wrap `2^64`!
              have hhe_val : heapEnd = 33806089704 := heapEnd_val
              have ho2 : (out0 + 2#64).toNat = out0.toNat + 2 :=
                BitVec.toNat_add_of_lt (by change out0.toNat + 2 < 2 ^ 64; omega)
              have ho_off2 : (out0 + off2).toNat = out0.toNat + off2.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off2.toNat < 2 ^ 64; omega)
              have ho_off3 : (out0 + off3).toNat = out0.toNat + off3.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off3.toNat < 2 ^ 64; omega)
              have ho_off4 : (out0 + off4).toNat = out0.toNat + off4.toNat :=
                BitVec.toNat_add_of_lt (by change out0.toNat + off4.toNat < 2 ^ 64; omega)
              have ho1 : (out0 + 1#64).toNat = out0.toNat + 1 :=
                BitVec.toNat_add_of_lt (by change out0.toNat + 1 < 2 ^ 64; omega)
              have hGs15 : GuestInv s15 := guestInv_congr hsb_248.1.code hsb_248.1.memaddrs hsb_248.1.shMemaddrs hsb_248.1.baseAddr hGs14
              have hs15_out : s15.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                rw [hcf_248.2.2.1]; exact hs14_out
              -- Step 13: `st8 (out + 1), (off - 2)` + `return off`
              rw [evaluateHOLFiniteState_seq_line780]
              have hsb_len := (byteEff_storeByte (Rl := Rl) hGs15
                (.op .add [.var .local (ofString "out"), .const (1#64)])
                (.op .sub [.var .local (ofString "off"), .const (2#64)])
                (fun x hx _ => by
                  simp [evalHOLExact, evalListHOLExact, hs15_out, wordOpHOL, wordOp, valueIsWord, valueWord] at hx
                  subst hx
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat, ho1]; omega,
                    by dsimp only; rw [hout_nat, ho1]; omega⟩)).1
              rcases hst_len : evaluateHOLFiniteState s15
                  (.storeByte (.op .add [.var .local (ofString "out"), .const (1#64)])
                              (.op .sub [.var .local (ofString "off"), .const (2#64)])) with ⟨rlen, s16⟩
              rw [hst_len] at hsb_len; dsimp only at hsb_len ⊢
              -- Lift every intermediate `ByteEff` into `Rl`:
              have he1 : ByteEff s s1 Rl :=
                ((ByteEff.refl s Rl).locals_clock _ _).trans (heff1.mono (fun iv hiv _ => by
                  have ho2' : (out0 + (2 : BitVec 64)).toNat = out0.toNat + 2 := ho2
                  simp [ho2, ho2'] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩))
              have he2 : ByteEff s1 s6 Rl :=
                ((ByteEff.refl s1 Rl).locals_clock _ _).trans (heff_be_all.mono (fun iv hiv _ => by
                  simp at hiv; subst hiv
                  exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, le_rfl, le_rfl⟩))
              have he3 : ByteEff s6 s8 Rl := by
                rw [hs8_eq]; exact (ByteEff.refl s6 Rl).locals_clock _ _
              have he4 : ByteEff s8 s10 Rl :=
                (heff_wb.mono (fun iv hiv _ => by
                  simp [ho_off2] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he5 : ByteEff s10 s12 Rl :=
                (heff_wsl.mono (fun iv hiv _ => by
                  simp [ho_off3] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he6 : ByteEff s12 s14 Rl :=
                (heff_wc.mono (fun iv hiv _ => by
                  simp [ho_off4] at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat]; omega,
                    by dsimp only; rw [hout_nat]; omega⟩)).locals_clock _ _
              have he7 : ByteEff s14 s15 Rl :=
                hsb_248.1.mono (fun iv hiv _ => by
                  simp at hiv; subst hiv
                  exact ⟨(locN s "out", 110), List.mem_cons_self,
                    by dsimp only; rw [hout_nat],
                    by dsimp only; rw [hout_nat]; omega⟩)
              have he_s_16 : ByteEff s s16 Rl :=
                ((((((he1.trans he2).trans he3).trans he4).trans he5).trans he6).trans he7).trans hsb_len
              cases rlen with
              | some _ =>
                exact (((((he_s_16.locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
              | none =>
                dsimp only
                exact ((((((he_s_16.trans (byteEff_return s16 _ Rl)).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
            · subst hr248; exact False.elim (not_resumes_error hres13)

end InitECandidate.Solver.Wave8GuestInv.R16Rlp

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Rlp

theorem «wk_encode_account» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 110), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
    []
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "encode_account") :=
  wk_encode_account_impl

end InitECandidate.Solver.Wave8GuestInv.R16Shards

