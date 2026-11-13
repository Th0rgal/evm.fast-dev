import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputRet

/-!
# Decode posts with slice-pointer facts (R32)

`WkDecodeHostInputRet` proves return posts for `ssz_split_var_list`,
`decode_bytes_list` and `input_blob` that bound the *length* word of every
slice cell but say nothing about the *pointer* word, and that do not relate the
input blob to `heap_ptr`.  The `wsi` / `hph` / `wph` / `hexec` leaves of
`CertificateR32` all need exactly those missing facts (`WitnessSliceOK`,
`ptr + len ≤ heap_ptr`).

This file replays the three proofs with strengthened posts:

* `ssz_split_var_list_body_returns_slices`, `decode_bytes_list_body_returns_slices`:
  additionally, every slice `j` has pointer word `(p + o) % 2 ^ 64` for some
  offset `o` with `o + len_j ≤ len`, i.e. it lies inside the list `[p, p + len)`.
* `input_blob_body_returns_heap`: additionally the blob is 8-aligned and
  `heap_ptr@entry ≤ p` and `p + len + 8 ≤ heap_ptr@post`.

The proofs are the originals with the loop invariants extended; nothing here is
wired into `Solution.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ### `ssz_split_var_list`: every slice lies inside the list -/

theorem ssz_split_var_list_body_returns_slices {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {wp wlen wlim : BitVec 64} {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlim : entry.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    WorldEff entry post Rl B dhiGw ∧
    ∃ (w_arr w_cnt : BitVec 64),
      rv = .rStruct [.val (.word w_arr), .val (.word w_cnt)] ∧
      w_cnt.toNat ≤ wlim.toNat ∧
      w_cnt.toNat < 2 ^ 30 ∧
      w_arr.toNat % 8 = 0 ∧
      WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) ∧
      ((w_cnt.toNat = 0 ∧ w_arr.toNat = 0 ∧ wlen.toNat = 0) ∨
       (1 ≤ w_cnt.toNat ∧
        sourceBase ≤ w_arr.toNat ∧
        globN entry "heap_ptr" ≤ w_arr.toNat ∧
        w_arr.toNat + 16 * w_cnt.toNat ≤ globN post "heap_ptr" ∧
        globN post "heap_ptr" ≤ heapLimit ∧
        (∀ j : Nat, j < w_cnt.toNat → memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) ∧
        (∀ j : Nat, j < w_cnt.toNat →
          ∃ o : Nat, memW post (w_arr.toNat + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
            o + memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat))) := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_ssz_split_var_list)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_ssz_split_var_list_body heff hnt hcr
    rwa [hrun] at h
  have heff_entry_refl : WorldEff entry entry Rl B dhiGw :=
    WorldEff.refl entry Rl B dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post Rl B dhiGw := by
    have h := worldEff_ssz_split_var_list_body heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_ssz_split_var_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  by_cases hlen0 : wlen = 0#64
  · subst hlen0
    have hite_ret : evaluateHOLFiniteState entry
        (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .const 0#64])) .skip) =
        (some (.returned (.rStruct [.val (.word 0#64), .val (.word 0#64)])), entry.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, hlen, Compiler.Encoders.Asm.wordCmpHOL,
        valueIsWord, valueWord, evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [evaluateHOLFiniteState_seq_line780, hite_ret] at hrun
    dsimp only at hrun
    injection hrun with hrv hpost
    injection hrv with hrv'; injection hrv' with hrv''
    subst hrv''
    refine ⟨heff_s_post, heff_entry_post, 0#64, 0#64, rfl, Nat.zero_le _, by decide, by decide, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
  · have hite0 : evaluateHOLFiniteState entry
        (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0#64))
          (.return (.rstruct [.const 0#64, .const 0#64])) .skip) = (none, entry) := by
      rw [evaluateHOLFiniteState_ite]
      simp [evalHOLExact, evalListHOLExact, toExact, hlen, Compiler.Encoders.Asm.wordCmpHOL,
        valueIsWord, valueWord, hlen0, evaluateHOLFiniteState_skip]
    rw [evaluateHOLFiniteState_seq_line780, hite0] at hrun
    dsimp only at hrun
    obtain ⟨m2, hm2, hrun2⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
    obtain ⟨hm2_eq, _⟩ := ite_ssz_fail_keeps entry m2 heff.code _ _ hm2
    have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm2_eq]; exact hp
    have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm2_eq]; exact hlen
    have hm2_lim : m2.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by rw [hm2_eq]; exact hlim
    have heff_e2 : WorldEff entry m2 Rl B dhiGw := by
      rw [hm2_eq]; exact heff_entry_refl.locals_clock _ _
    obtain ⟨v_first, p3, hv_first, _, hrun3, hp3_eq⟩ := dec_returned_split hrun2
    obtain ⟨w_first, rfl, hfirst_lt⟩ := eval_le32_word_lt m2 _ _ _ _ v_first hv_first
    let m3 := setVarHOLFinite (ofString "first") (.val (.word w_first)) m2
    have hm3_code : m3.code = originalRuntimeCode := by dsimp only [m3]; rw [hm2_eq]; exact heff.code
    obtain ⟨m4, hm4, hrun4⟩ := seq_returned_split (ite_call0_noret_dhi m3 _ _ _) hrun3
    obtain ⟨hm4_eq, hcond21⟩ := ite_ssz_fail_keeps m3 m4 hm3_code _ _ hm4
    have hm3_first : m3.locals.lookup (ofString "first") = some (.val (.word w_first)) := lookup_setVar_eq _ _ _
    have hm3_len : m3.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_len
    have hfirst_bounds : 4 ≤ w_first.toNat ∧ w_first.toNat ≤ wlen.toNat := by
      dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond21
      rw [hm3_first, hm3_len] at hcond21
      simp only [Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
        List.map, List.foldr, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond21
      have hcond21' :
          (if (!0#64 == (if (w_first == 0#64) = true then 1#64 else 0#64) |||
              ((if (!w_first &&& (3#64 &&& ~~~0#64) == 0#64) = true then 1#64 else 0#64) |||
                ((if decide (wlen < w_first) = true then 1#64 else 0#64) ||| 0#64))) = true
            then 1#64 else 0#64) = 0#64 := hcond21
      have hne0 : w_first ≠ 0#64 := by intro hz; subst hz; simp at hcond21'
      have hmod4 : w_first.toNat % 4 = 0 := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hm : (w_first &&& 3#64) == 0#64
        · have hm' : w_first &&& 3#64 = 0#64 := eq_of_beq hm
          have hn := congrArg BitVec.toNat hm'
          rw [BitVec.toNat_and] at hn
          change w_first.toNat &&& (2 ^ 2 - 1) = 0 at hn
          rwa [Nat.and_two_pow_sub_one_eq_mod _ 2] at hn
        · exfalso; simp [hm] at hcond21'; revert hcond21'; split <;> split <;> simp
      have hle_len : w_first.toNat ≤ wlen.toNat := by
        have hand3 : (3#64 &&& ~~~0#64 : BitVec 64) = 3#64 := rfl
        rw [hand3] at hcond21'
        by_cases hlt : wlen < w_first
        · exfalso; simp [hlt] at hcond21'; revert hcond21'; split <;> split <;> simp
        · simp [BitVec.lt_def] at hlt; omega
      have hf_pos : 0 < w_first.toNat := by
        by_cases hp0 : w_first.toNat = 0
        · exact absurd (BitVec.eq_of_toNat_eq hp0) hne0
        · omega
      exact ⟨by omega, hle_len⟩
    have hm4_first : m4.locals.lookup (ofString "first") = some (.val (.word w_first)) := by rw [hm4_eq]; exact hm3_first
    have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm4_eq]; dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_p
    have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm4_eq]; exact hm3_len
    have hm4_lim : m4.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
      rw [hm4_eq]; dsimp only [m3]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm2_lim
    obtain ⟨v_cnt, p5, hv_cnt, _, hrun5, hp5_eq⟩ := dec_returned_split hrun4
    have hv_cnt_eq : v_cnt = .val (.word (w_first >>> 2)) := by
      simp [evalHOLExact, toExact, hm4_first, wordShiftHOL] at hv_cnt; exact hv_cnt.symm
    subst hv_cnt_eq
    let w_cnt := w_first >>> 2
    have hw_cnt_nat : w_cnt.toNat = w_first.toNat / 4 := by
      dsimp only [w_cnt]; change (w_first >>> (2 : Nat)).toNat = w_first.toNat / 4
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hcnt_pos : 1 ≤ w_cnt.toNat := by omega
    have hcnt_lt : w_cnt.toNat < 2 ^ 30 := by omega
    let m5 := setVarHOLFinite (ofString "count") (.val (.word w_cnt)) m4
    have hm5_code : m5.code = originalRuntimeCode := by dsimp only [m5]; rw [hm4_eq]; exact hm3_code
    obtain ⟨m6, hm6, hrun6⟩ := seq_returned_split (ite_call0_noret_dhi m5 _ _ _) hrun5
    obtain ⟨hm6_eq, hcond22⟩ := ite_ssz_fail_keeps m5 m6 hm5_code _ _ hm6
    have hm5_cnt : m5.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := lookup_setVar_eq _ _ _
    have hm5_lim : m5.locals.lookup (ofString "lim") = some (.val (.word wlim)) := by
      dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_lim
    have hcnt_le_lim : w_cnt.toNat ≤ wlim.toNat := by
      simp only [evalHOLExact, evalListHOLExact, toExact, hm5_cnt, hm5_lim,
        Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond22
      by_cases hlt : wlim < w_cnt
      · simp [hlt] at hcond22
      · simp [BitVec.lt_def] at hlt; exact hlt
    have heff_e6 : WorldEff entry m6 Rl B dhiGw := by
      have h4 : m4 = { entry with locals := m4.locals, clock := m4.clock } := by
        rw [hm4_eq]; dsimp only [m3, setVarHOLFinite]; rw [hm2_eq]
      have h6 : m6 = { entry with locals := m6.locals, clock := m6.clock } := by
        rw [hm6_eq]; dsimp only [m5, setVarHOLFinite]; rw [h4]
      rw [h6]; exact heff_entry_refl.locals_clock _ _
    have hm6_cnt : m6.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by rw [hm6_eq]; exact hm5_cnt
    have hm6_first : m6.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_first
    have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_p
    have hm6_len : m6.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      rw [hm6_eq]; dsimp only [m5]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm4_len
    obtain ⟨w_arr, nw, m7, p7, hsz_ev, _, hm7_loc, _, heff_e7, harr_al, harr_sb, harr_lo, harr_add, hhp7_hi, _, hrun7, hp7_eq⟩ :=
      decCall_alloc_returned_split heff_e6 hrun6
    have hnw_eq : nw = w_cnt * 16#64 := by
      simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm6_cnt, valueIsWord, valueWord] at hsz_ev
      exact hsz_ev.symm
    subst hnw_eq
    have hnw_nat : (w_cnt * 16#64).toNat = w_cnt.toNat * 16 := by
      rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hround16 : (w_cnt.toNat * 16 + 7) / 8 * 8 = 16 * w_cnt.toNat := by omega
    rw [hnw_nat, hround16] at harr_add
    have harr_hi : w_arr.toNat + 16 * w_cnt.toNat ≤ heapLimit := by omega
    have hhl_lt : heapLimit < 2 ^ 64 := by decide
    have hm7_cnt : m7.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_cnt, show ofString "arr" ≠ ofString "count" by decide]
    have hm7_first : m7.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_first, show ofString "arr" ≠ ofString "first" by decide]
    have hm7_arr : m7.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hm7_p : m7.locals.lookup (ofString "p") = some (.val (.word wp)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_p, show ofString "arr" ≠ ofString "p" by decide]
    have hm7_len : m7.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
      rw [hm7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm6_len, show ofString "arr" ≠ ofString "len" by decide]
    obtain ⟨vi, p8, hvi, _, hrun8, hp8_eq⟩ := dec_returned_split hrun7
    have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
    subst hvi0
    let m8 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m7
    have hm8_first : m8.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
      dsimp only [m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm7_first
    obtain ⟨vprev, p9, hvprev, _, hrun9, hp9_eq⟩ := dec_returned_split hrun8
    have hvprev_eq : vprev = .val (.word w_first) := by
      dsimp only [evalHOLExact, toExact] at hvprev
      rw [hm8_first] at hvprev
      injection hvprev with h; exact h.symm
    subst hvprev_eq
    let m9 := setVarHOLFinite (ofString "prev") (.val (.word w_first)) m8
    obtain ⟨m10, hm10, hrun10⟩ := seq_returned_split (while_noret_dhi m9 _ _ (fun u =>
      dec_noret_dhi u _ _ _ _ (fun _ =>
        seq_noret_dhi _ (ite_call0_noret_dhi _ _ _ _) (fun sb1 _ =>
          seq_noret_dhi sb1 (ite_noret_dhi sb1 _ _ _ (store_noret_dhi sb1 _ _) (skip_noret_dhi sb1)) (fun sb2 _ =>
            seq_noret_dhi sb2 (store_noret_dhi sb2 _ _) (fun sb3 _ =>
              seq_noret_dhi sb3 (assign_noret_dhi sb3 _ _ _) (fun sb4 _ =>
                assign_noret_dhi sb4 _ _ _))))))) hrun9
    let InvRet : PanSemStateFiniteExact 64 F → Prop := fun t =>
      t.code = originalRuntimeCode ∧
      t.globals = m7.globals ∧
      t.locals.lookup (ofString "arr") = some (.val (.word w_arr)) ∧
      t.locals.lookup (ofString "count") = some (.val (.word w_cnt)) ∧
      t.locals.lookup (ofString "first") = some (.val (.word w_first)) ∧
      t.locals.lookup (ofString "p") = some (.val (.word wp)) ∧
      t.locals.lookup (ofString "len") = some (.val (.word wlen)) ∧
      (∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ w_cnt.toNat ∧
        (∀ j : Nat, j + 1 < wi.toNat → memW t (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) ∧
        ∃ wprev : BitVec 64, t.locals.lookup (ofString "prev") = some (.val (.word wprev)) ∧ wprev.toNat ≤ wlen.toNat ∧
          (∀ j : Nat, j + 1 < wi.toNat →
            ∃ o : Nat, memW t (w_arr.toNat + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
              o + memW t (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) ∧
          (0 < wi.toNat → memW t (w_arr.toNat + 16 * (wi.toNat - 1)) = (wp.toNat + wprev.toNat) % 2 ^ 64))
    have hinv_m9 : InvRet m9 := by
      refine ⟨heff_e7.code, rfl, ?_, ?_, ?_, ?_, ?_, ⟨0#64, ?_, Nat.zero_le _, fun j hj => by simp at hj,
        w_first, lookup_setVar_eq _ _ _, hfirst_bounds.2, fun j hj => by simp at hj,
        fun h => absurd h (by decide)⟩⟩
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_arr
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_cnt
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_first
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_p
      · dsimp only [m9, m8]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        exact hm7_len
      · dsimp only [m9, m8]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
    have hloop_res := while_none_inv_dhi _ _ InvRet (fun _ h => h)
      (fun t _ =>
        dec_nobreak_dhi t _ _ _ _ (fun _ =>
          seq_nobreak_dhi _ (ite_call0_nobreak_dhi _ _ _ _).1 (fun sb1 _ =>
            seq_nobreak_dhi sb1 (ite_nobreak_dhi sb1 _ _ _ (store_nobreak_dhi sb1 _ _).1 (skip_nobreak_dhi sb1).1) (fun sb2 _ =>
              seq_nobreak_dhi sb2 (store_nobreak_dhi sb2 _ _).1 (fun sb3 _ =>
                seq_nobreak_dhi sb3 (assign_nobreak_dhi sb3 _ _ _).1 (fun sb4 _ =>
                  (assign_nobreak_dhi sb4 _ _ _).1))))))
      (fun t0 cw hcond hnz ⟨ht_code, ht_glob, ht_arr, ht_cnt, ht_first, ht_p, ht_len, ⟨wi, ht_i, hwi_le, hj_ok, wprev, ht_prev, hwprev_le, hI1, hI2⟩⟩ hf => ?_)
      m9.clock m9 rfl hinv_m9 (congrArg Prod.fst hm10)
    · rw [hm10] at hloop_res
      dsimp only at hloop_res
      obtain ⟨⟨hm10_code, hm10_glob, hm10_arr, hm10_cnt, _, _, hm10_len, ⟨wi_f, hm10_i, hwi_f_le, hj_f_ok, wprev_f, hm10_prev, hwprev_f_le, hI1_f, hI2_f⟩⟩, hcond_exit⟩ := hloop_res
      have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
      have hwi_eq_cnt : wi_f.toNat = w_cnt.toNat := by
        have hce : @evalHOLFinite 64 F _ m10 (fun a => Classical.propDecidable (m10.memaddrs a))
            (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "count"))) =
            some (.val (.word (if wi_f.toNat < w_cnt.toNat then 1#64 else 0#64))) := by
          rw [evalHOLFinite_eq_toExact]
          simp [evalHOLExact, evalListHOLExact, toExact, hm10_i, hm10_cnt,
            Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small wi_f w_cnt (by omega) (by omega)]
        have hz := hcond_exit _ hce
        by_cases hlt : wi_f.toNat < w_cnt.toNat
        · simp [hlt] at hz
        · omega
      obtain ⟨m11, hst10, hret11⟩ := seq_returned_split (store_noret_dhi m10 _ _) hrun10
      have hsub1 : (w_cnt - 1#64).toNat = w_cnt.toNat - 1 := by
        rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; rfl
      have hmul16 : ((w_cnt - 1#64) * 16#64).toNat = (w_cnt.toNat - 1) * 16 := by
        rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hadd_r : (((w_cnt - 1#64) * 16#64) + 8#64).toNat = (w_cnt.toNat - 1) * 16 + 8 := by
        rw [BitVec.toNat_add_of_lt]; · rw [hmul16]; rfl
        · rw [hmul16]; change (w_cnt.toNat - 1) * 16 + 8 < 2 ^ 64; omega
      have hdst10_ev : @evalHOLExact 64 F _ m10.toExact (fun a => Classical.propDecidable (m10.memaddrs a))
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.op .sub [.var .local (ofString "count"), .const 1#64], .const 16#64],
            .const 8#64]) =
          some (.val (.word (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)))) := by
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hm10_arr, hm10_cnt,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      have hval10_ev : @evalHOLExact 64 F _ m10.toExact (fun a => Classical.propDecidable (m10.memaddrs a))
          (.op .sub [.var .local (ofString "len"), .var .local (ofString "prev")]) =
          some (.val (.word (wlen - wprev_f))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hm10_len, hm10_prev,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨_, _, _, _, hm11_loc, hm11_glob, _, _, hm11_last, hm11_ne⟩ :=
        store_none_evals m10 m11 _ _ hst10 ⟨_, hdst10_ev⟩ (fun v hv => by rw [hval10_ev] at hv; injection hv with h; exact ⟨_, h.symm⟩)
      -- Wait: `store_none_evals` returns `xw` and `vw` existentially; let's just use `store_memW_eq_and_ne` + `store_none_evals`!
      obtain ⟨hm11_last_eq, hm11_ne_eq⟩ := store_memW_eq_and_ne m10 m11 _ _ _ _ hst10 hdst10_ev hval10_ev
      have hx10_nat : (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + 16 * (w_cnt.toNat - 1) + 8 := by
        rw [BitVec.toNat_add_of_lt] <;> omega
      have hlast_le : (wlen - wprev_f).toNat ≤ wlen.toNat := by
        rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hwprev_f_le)]; omega
      rw [evaluateHOLFiniteState_return] at hret11
      simp only [evalHOLExact, evalListHOLExact, toExact, hm11_loc, hm10_arr, hm10_cnt,
        Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
        Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret11
      injection hret11 with hrv_eq hp9_post
      injection hrv_eq with hrv_eq'
      injection hrv_eq' with hrv_eq''
      subst hrv_eq''
      have hpost_mem : post.memory = m11.memory := by
        rw [hp3_eq, hp5_eq, hp7_eq, hp8_eq, hp9_eq]; dsimp only
        rw [← hp9_post]; rfl
      have hpost_glob : post.globals = m7.globals := by
        rw [hp3_eq, hp5_eq, hp7_eq, hp8_eq, hp9_eq]; dsimp only
        rw [← hp9_post]; dsimp only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
        rw [hm11_glob, hm10_glob]
      have hpost_hp : globN post "heap_ptr" = globN m7 "heap_ptr" := by
        unfold globN; rw [hpost_glob]
      have hpost_memW : ∀ a, memW post a = memW m11 a := fun a => by unfold memW; rw [hpost_mem]
      have hwok_post : WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) :=
        wordsOK_preserved_of_worldEff heff_entry_post harr_al (by omega) harr_sb harr_hi
      refine ⟨heff_s_post, heff_entry_post, w_arr, w_cnt, rfl, hcnt_le_lim, hcnt_lt, harr_al, hwok_post,
        Or.inr ⟨hcnt_pos, harr_sb, harr_lo, by rw [hpost_hp]; omega, heff_entry_post.arena.2.2.1, fun j hj => ?_, fun j hj => ?_⟩⟩
      rw [hpost_memW]
      by_cases hj_last : j = w_cnt.toNat - 1
      · subst hj_last
        rw [← hx10_nat, hm11_last_eq]
        exact hlast_le
      · have hj_lt : j + 1 < wi_f.toNat := by omega
        have hne_addr : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat := by
          rw [hx10_nat]; omega
        rw [hm11_ne_eq _ (by omega) hne_addr]
        exact hj_f_ok j hj_lt
      have hne_p : w_arr.toNat + 16 * j ≠ (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat := by
        rw [hx10_nat]; omega
      by_cases hj_last : j = w_cnt.toNat - 1
      · subst hj_last
        have hsub : (wlen - wprev_f).toNat = wlen.toNat - wprev_f.toNat :=
          BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact hwprev_f_le)
        refine ⟨wprev_f.toNat, ?_, ?_⟩
        · rw [hpost_memW, hm11_ne_eq _ (by omega) hne_p, ← hwi_eq_cnt]
          exact hI2_f (by omega)
        · rw [hpost_memW, ← hx10_nat, hm11_last_eq, hsub]; omega
      · obtain ⟨o, ho1, ho2⟩ := hI1_f j (by omega)
        have hne_addr : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((w_cnt - 1#64) * 16#64) + 8#64)).toNat := by
          rw [hx10_nat]; omega
        refine ⟨o, ?_, ?_⟩
        · rw [hpost_memW, hm11_ne_eq _ (by omega) hne_p]; exact ho1
        · rw [hpost_memW, hm11_ne_eq _ (by omega) hne_addr]; exact ho2
    · -- Step of `while` loop body:
      have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
      have ht0_cnt : t0.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := ht_cnt
      have h2_30_63 : (2 : Nat) ^ 30 < 2 ^ 63 := by decide
      have hwi_lt : wi.toNat < w_cnt.toNat := by
        rw [evalHOLFinite_eq_toExact] at hcond
        simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i, ht0_cnt,
          Compiler.Encoders.Asm.wordCmpHOL,
          holAsmSignedLess_small wi w_cnt (by omega) (by omega)] at hcond
        by_cases hlt : wi.toNat < w_cnt.toNat
        · exact hlt
        · simp [hlt] at hcond; exact absurd hcond.symm hnz
      have hhl_lt : heapLimit < 2 ^ 64 := by decide
      obtain ⟨v_o, hv_o, _, hf0, hpost_o⟩ := dec_cont_or_none_split hf
      rw [hpost_o]; clear hf hpost_o
      obtain ⟨w_o, rfl, _⟩ := eval_le32_word_lt (decClockHOLFinite t0) _ _ _ _ v_o hv_o
      let u0 := setVarHOLFinite (ofString "o") (.val (.word w_o)) (decClockHOLFinite t0)
      change (evaluateHOLFiniteState u0 _).1 = _ ∨ _ at hf0
      obtain ⟨u1, hu1_ev, hf1, hpost_1⟩ := seq_cont_or_none_split (ite_call0_nobreak_dhi u0 _ _ _).2 hf0
      rw [hpost_1]; clear hf0 hpost_1
      obtain ⟨hu1_eq, hcond23⟩ := ite_ssz_fail_keeps u0 u1 ht_code _ _ hu1_ev
      have hu0_o : u0.locals.lookup (ofString "o") = some (.val (.word w_o)) := lookup_setVar_eq _ _ _
      have hu0_first : u0.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_first
      have hu0_len : u0.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_len
      have hu0_prev : u0.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_prev
      have ho_bounds : wprev.toNat ≤ w_o.toNat ∧ w_o.toNat ≤ wlen.toNat := by
        dsimp only [evalHOLExact, evalListHOLExact, toExact] at hcond23
        rw [hu0_o, hu0_first, hu0_len, hu0_prev] at hcond23
        simp only [Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all_cons, List.all_nil, Bool.and_self, Option.map_some, ↓reduceIte,
          List.map, List.foldr, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hcond23
        have hcond23' :
            (if (!0#64 == (if decide (w_o < w_first) = true then 1#64 else 0#64) |||
                ((if decide (wlen < w_o) = true then 1#64 else 0#64) |||
                  ((if decide (w_o < wprev) = true then 1#64 else 0#64) ||| 0#64))) = true
              then 1#64 else 0#64) = 0#64 := hcond23
        have h1 : wprev.toNat ≤ w_o.toNat := by
          by_cases hlt : w_o < wprev
          · exfalso; simp [hlt] at hcond23'; revert hcond23'; split <;> split <;> simp
          · simp [BitVec.lt_def] at hlt; exact hlt
        have h2 : w_o.toNat ≤ wlen.toNat := by
          by_cases hlt : wlen < w_o
          · exfalso; simp [hlt] at hcond23'; revert hcond23'; split <;> split <;> simp
          · simp [BitVec.lt_def] at hlt; exact hlt
        exact ⟨h1, h2⟩
      have hu1_arr : u1.locals.lookup (ofString "arr") = some (.val (.word w_arr)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_arr
      have hu1_cnt : u1.locals.lookup (ofString "count") = some (.val (.word w_cnt)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_cnt
      have hu1_first : u1.locals.lookup (ofString "first") = some (.val (.word w_first)) := by
        rw [hu1_eq]; exact hu0_first
      have hu1_p : u1.locals.lookup (ofString "p") = some (.val (.word wp)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_p
      have hu1_len : u1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
        rw [hu1_eq]; exact hu0_len
      have hu1_i : u1.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        rw [hu1_eq]; dsimp only [u0]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact ht_i
      have hu1_o : u1.locals.lookup (ofString "o") = some (.val (.word w_o)) := by
        rw [hu1_eq]; exact hu0_o
      have hu1_prev : u1.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        rw [hu1_eq]; exact hu0_prev
      have hu1_memW : ∀ a, memW u1 a = memW (decClockHOLFinite t0) a := fun a => by
        unfold memW; rw [show u1.memory = u0.memory by rw [hu1_eq]]; rfl
      have hu1_code : u1.code = originalRuntimeCode := by rw [hu1_eq]; exact ht_code
      have hu1_glob : u1.globals = m7.globals := by rw [hu1_eq]; exact ht_glob
      obtain ⟨u2, hu2_ev, hf2, hpost_2⟩ := seq_cont_or_none_split (ite_store_skip_nobreak u1 _ _ _) hf1
      rw [hpost_2]; clear hf1 hpost_2
      have hu2_props : u2.locals = u1.locals ∧ u2.globals = m7.globals ∧ u2.code = originalRuntimeCode ∧
          (∀ j : Nat, j < wi.toNat → memW u2 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) ∧
          (∀ j : Nat, j < wi.toNat →
            ∃ o : Nat, memW u2 (w_arr.toNat + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
              o + memW u2 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) := by
        rw [evaluateHOLFiniteState_ite] at hu2_ev
        simp only [evalHOLExact, evalListHOLExact, toExact, hu1_i,
          Compiler.Encoders.Asm.wordCmpHOL, holAsmSignedLess_small 0#64 wi (by decide) (by omega),
          show (0#64 : BitVec 64).toNat = 0 from rfl] at hu2_ev
        by_cases hpos : 0 < wi.toNat
        · simp only [hpos, ↓reduceIte, show ¬ ((1#64 : BitVec 64) = 0) by decide] at hu2_ev
          have hsub1 : (wi - 1#64).toNat = wi.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; rfl
          have hmul16 : ((wi - 1#64) * 16#64).toNat = (wi.toNat - 1) * 16 := by
            rw [BitVec.toNat_mul, hsub1, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
          have hadd_r : (((wi - 1#64) * 16#64) + 8#64).toNat = (wi.toNat - 1) * 16 + 8 := by
            rw [BitVec.toNat_add_of_lt]; · rw [hmul16]; rfl
            · rw [hmul16]; change (wi.toNat - 1) * 16 + 8 < 2 ^ 64; omega
          have hdst_u1 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
              (.op .add [.var .local (ofString "arr"),
                .panop .mul [.op .sub [.var .local (ofString "i"), .const 1#64], .const 16#64],
                .const 8#64]) =
              some (.val (.word (w_arr + (((wi - 1#64) * 16#64) + 8#64)))) := by
            simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu1_arr, hu1_i,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          have hval_u1 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
              (.op .sub [.var .local (ofString "o"), .var .local (ofString "prev")]) =
              some (.val (.word (w_o - wprev))) := by
            simp [evalHOLExact, evalListHOLExact, toExact, hu1_o, hu1_prev,
              wordOpHOL, wordOp, valueIsWord, valueWord]
          obtain ⟨_, _, _, _, hl2, hg2, hc2, _, _, _⟩ :=
            store_none_evals u1 u2 _ _ hu2_ev ⟨_, hdst_u1⟩ (fun v hv => by rw [hval_u1] at hv; injection hv with h; exact ⟨_, h.symm⟩)
          obtain ⟨hm2_eq', hm2_ne'⟩ := store_memW_eq_and_ne u1 u2 _ _ _ _ hu2_ev hdst_u1 hval_u1
          have hx_nat : (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat = w_arr.toNat + 16 * (wi.toNat - 1) + 8 := by
            rw [BitVec.toNat_add_of_lt] <;> omega
          have hdiff_le : (w_o - wprev).toNat ≤ wlen.toNat := by
            rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact ho_bounds.1)]; omega
          refine ⟨hl2, hg2.trans hu1_glob, hc2.trans hu1_code, fun j hj => ?_, fun j hj => ?_⟩
          by_cases hjl : j = wi.toNat - 1
          · subst hjl; rw [← hx_nat, hm2_eq']; exact hdiff_le
          · have hne_j : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat := by
              rw [hx_nat]; omega
            rw [hm2_ne' _ (by omega) hne_j, hu1_memW]
            exact hj_ok j (by omega)
          have hne_p : w_arr.toNat + 16 * j ≠ (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat := by
            rw [hx_nat]; omega
          by_cases hjl : j = wi.toNat - 1
          · subst hjl
            have hsub : (w_o - wprev).toNat = w_o.toNat - wprev.toNat :=
              BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; exact ho_bounds.1)
            refine ⟨wprev.toNat, ?_, ?_⟩
            · rw [hm2_ne' _ (by omega) hne_p, hu1_memW]; exact hI2 hpos
            · rw [← hx_nat, hm2_eq', hsub]; omega
          · obtain ⟨o, ho1, ho2⟩ := hI1 j (by omega)
            have hne_j : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (((wi - 1#64) * 16#64) + 8#64)).toNat := by
              rw [hx_nat]; omega
            refine ⟨o, ?_, ?_⟩
            · rw [hm2_ne' _ (by omega) hne_p, hu1_memW]; exact ho1
            · rw [hm2_ne' _ (by omega) hne_j, hu1_memW]; exact ho2
        · simp only [hpos, ↓reduceIte, evaluateHOLFiniteState_skip] at hu2_ev
          injection hu2_ev with _ hu2_id
          subst hu2_id
          exact ⟨rfl, hu1_glob, hu1_code, fun j hj => by omega, fun j hj => absurd hj (by omega)⟩
      obtain ⟨hu2_loc, hu2_glob, hu2_code, hj_u2, hP1_u2⟩ := hu2_props
      obtain ⟨u3, hu3_ev, hf3, hpost_3⟩ := seq_cont_or_none_split (store_nobreak_dhi u2 _ _).2 hf2
      rw [hpost_3]; clear hf2 hpost_3
      have hmul16_i : (wi * 16#64).toNat = wi.toNat * 16 := by
        rw [BitVec.toNat_mul, show (16#64 : BitVec 64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
      have hdst_u2 : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
          (.op .add [.var .local (ofString "arr"),
            .panop .mul [.var .local (ofString "i"), .const 16#64]]) =
          some (.val (.word (w_arr + (wi * 16#64)))) := by
        simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, hu2_loc, hu1_arr, hu1_i,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      have hval_u2 : @evalHOLExact 64 F _ u2.toExact (fun a => Classical.propDecidable (u2.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "o")]) =
          some (.val (.word (wp + w_o))) := by
        simp [evalHOLExact, evalListHOLExact, toExact, hu2_loc, hu1_p, hu1_o,
          wordOpHOL, wordOp, valueIsWord, valueWord]
      obtain ⟨_, _, _, _, hu3_loc, hu3_glob, hu3_code, _, _, _⟩ :=
        store_none_evals u2 u3 _ _ hu3_ev ⟨_, hdst_u2⟩ (fun v hv => by rw [hval_u2] at hv; injection hv with h; exact ⟨_, h.symm⟩)
      obtain ⟨hm3_eq, hm3_ne⟩ := store_memW_eq_and_ne u2 u3 _ _ _ _ hu3_ev hdst_u2 hval_u2
      have hx3_nat : (w_arr + (wi * 16#64)).toNat = w_arr.toNat + 16 * wi.toNat := by
        rw [BitVec.toNat_add_of_lt] <;> omega
      have hj_u3 : ∀ j : Nat, j < wi.toNat → memW u3 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat := by
        intro j hj
        have hne3 : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (wi * 16#64)).toNat := by rw [hx3_nat]; omega
        rw [hm3_ne _ (by omega) hne3]
        exact hj_u2 j hj
      obtain ⟨u4, hu4_ev, _, hpost_4⟩ := seq_cont_or_none_split (assign_nobreak_dhi u3 _ _ _).2 hf3
      rw [hpost_4]; clear hf3 hpost_4
      have hu3_prev : u3.locals.lookup (ofString "prev") = some (.val (.word wprev)) := by
        rw [hu3_loc, hu2_loc]; exact hu1_prev
      have hvv_prev : u3.isValidValueHOLFinite .local (ofString "prev") (.val (.word w_o)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          toExact, hu3_prev, shapeOfHOLExact, shapeEqHOL]
      rw [evaluateHOLFiniteState_assign] at hu4_ev
      simp only [evalHOLExact, toExact, hu3_loc, hu2_loc, hu1_o, hvv_prev,
        ↓reduceIte, setKvarHOLFinite] at hu4_ev
      injection hu4_ev with _ hu4_eq; subst hu4_eq
      let u4 := setVarHOLFinite (ofString "prev") (.val (.word w_o)) u3
      have hu4_i : u4.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        dsimp only [u4]; rw [lookup_setVar_ne _ _ _ _ (by decide), hu3_loc, hu2_loc]; exact hu1_i
      have hvv_i : u4.isValidValueHOLFinite .local (ofString "i") (.val (.word (wi + 1#64))) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          toExact, hu4_i, shapeOfHOLExact, shapeEqHOL]
      have hu5_eq : (evaluateHOLFiniteState u4
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))).2 =
          setVarHOLFinite (ofString "i") (.val (.word (wi + 1#64))) u4 := by
        rw [evaluateHOLFiniteState_assign]
        simp [evalHOLExact, evalListHOLExact, toExact, hu4_i, wordOpHOL, wordOp, valueIsWord, valueWord,
          PanSemStateFiniteExact.isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
      rw [hu5_eq]
      let u5 := setVarHOLFinite (ofString "i") (.val (.word (wi + 1#64))) u4
      have hwi_inc : (wi + 1#64).toNat = wi.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      refine ⟨hu3_code.trans hu2_code, hu3_glob.trans hu2_glob, ?_, ?_, ?_, ?_, ?_,
        ⟨wi + 1#64, ?_, by omega, fun j hj => ?_,
        w_o, ?_, ho_bounds.2, fun j hj => ?_, fun _ => ?_⟩⟩
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_arr
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_cnt
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_first
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_p
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        dsimp only [u5, u4]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
        rw [hu3_loc, hu2_loc]; exact hu1_len
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        exact lookup_setVar_eq _ _ _
      · rw [hwi_inc] at hj
        change memW u3 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat
        exact hj_u3 j (by omega)
      · dsimp only; rw [resVarEq_lookup_local, if_neg (by decide)]
        rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
      · rw [hwi_inc] at hj
        obtain ⟨o, ho1, ho2⟩ := hP1_u2 j (by omega)
        have hne_a : w_arr.toNat + 16 * j ≠ (w_arr + (wi * 16#64)).toNat := by rw [hx3_nat]; omega
        have hne_b : w_arr.toNat + 16 * j + 8 ≠ (w_arr + (wi * 16#64)).toNat := by rw [hx3_nat]; omega
        refine ⟨o, ?_, ?_⟩
        · change memW u3 (w_arr.toNat + 16 * j) = (wp.toNat + o) % 2 ^ 64
          rw [hm3_ne _ (by omega) hne_a]; exact ho1
        · change o + memW u3 (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat
          rw [hm3_ne _ (by omega) hne_b]; exact ho2
      · change memW u3 (w_arr.toNat + 16 * ((wi + 1#64).toNat - 1)) = (wp.toNat + w_o.toNat) % 2 ^ 64
        rw [hwi_inc, Nat.add_sub_cancel, ← hx3_nat, hm3_eq, BitVec.toNat_add]

/-! ### `input_blob`: the blob is allocated between the entry and the post `heap_ptr` -/

theorem store_none_globals {F : Type} (cur mid : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64)
    (h : evaluateHOLFiniteState cur (.store dst val) = (none, mid)) : mid.globals = cur.globals := by
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · split at h
    · split at h
      · injection h with _ h2; rw [← h2]
      · exact absurd (congrArg Prod.fst h) (by intro hh; cases hh)
    · exact absurd (congrArg Prod.fst h) (by intro hh; cases hh)
  · exact absurd (congrArg Prod.fst h) (by intro hh; cases hh)

theorem blob_loop_body_globals {F : Type} (t : PanSemStateFiniteExact 64 F)
    (op : OpSize) (nm : MlS) (addr dst val : ExpHOL 64) (nm2 : MlS) (e : ExpHOL 64)
    (hf : (evaluateHOLFiniteState t
            (.seq (.shMemLoad op .local nm addr) (.seq (.store dst val) (.assign .local nm2 e)))).1 = none ∨
          (evaluateHOLFiniteState t
            (.seq (.shMemLoad op .local nm addr) (.seq (.store dst val) (.assign .local nm2 e)))).1 = some .continue) :
    (evaluateHOLFiniteState t
      (.seq (.shMemLoad op .local nm addr) (.seq (.store dst val) (.assign .local nm2 e)))).2.globals = t.globals := by
  obtain ⟨u1, hu1, hf1, hpost_a⟩ := seq_cont_or_none_split (shMemLoad_nobreak_dhi t _ _ _ _).2 hf
  rw [hpost_a]
  obtain ⟨wv, hu1_eq⟩ := shMemLoad_local_none_inv t op nm _ hu1
  have hu1_g : u1.globals = t.globals := by
    have h := congrArg PanSemStateFiniteExact.globals hu1_eq
    exact h
  obtain ⟨u2, hu2, _, hpost_b⟩ := seq_cont_or_none_split (store_nobreak_dhi u1 _ _).2 hf1
  rw [hpost_b]
  have hu2_g : u2.globals = t.globals := (store_none_globals u1 u2 _ _ hu2).trans hu1_g
  rw [evaluateHOLFiniteState_assign]
  split
  · exact hu2_g
  · split
    · exact hu2_g
    · exact hu2_g

theorem input_blob_body_returns_heap {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    WorldEff entry post Rl B dhiGw ∧
    ∃ (wp wlen : BitVec 64),
      rv = .rStruct [.val (.word wp), .val (.word wlen)] ∧
      wlen.toNat ≤ 1073741808 ∧
      sourceBase ≤ wp.toNat ∧
      wp.toNat + wlen.toNat + 8 ≤ heapLimit ∧
      wp.toNat % 8 = 0 ∧
      globN entry "heap_ptr" ≤ wp.toNat ∧
      wp.toNat + wlen.toNat + 8 ≤ globN post "heap_ptr" := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_input_blob)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_input_blob_body heff hnt hcr
    rwa [hrun] at h
  have heff_entry_refl : WorldEff entry entry Rl B dhiGw :=
    WorldEff.refl entry Rl B dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post Rl B dhiGw := by
    have h := worldEff_input_blob_body heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_input_blob, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨vlen0, p0, hvlen0, _, hrun1, hp0_eq⟩ := dec_returned_split hrun
  have hvlen0_eq : vlen0 = .val (.word 0#64) := by simp [evalHOLExact] at hvlen0; exact hvlen0.symm
  subst hvlen0_eq
  let m0 := setVarHOLFinite (ofString "len") (.val (.word 0#64)) entry
  obtain ⟨m1, hm1, hrun2⟩ := seq_returned_split (shMemLoad_noret_dhi m0 _ _ _ _) hrun1
  have heff_m1 : WorldEff s m1 Rl B dhiGw := by
    have h := worldEff_shMemLoad_local (heff.locals_clock m0.locals m0.clock) .opW (ofString "len") (ExpHOL.const 1073741832#64)
    have hm0_eq : ({ entry with locals := m0.locals, clock := m0.clock } : PanSemStateFiniteExact 64 F) = m0 := rfl
    rw [hm0_eq, hm1] at h
    exact h
  have heff_e1 : WorldEff entry m1 Rl B dhiGw := by
    have h := worldEff_shMemLoad_local (heff_entry_refl.locals_clock m0.locals m0.clock) .opW (ofString "len") (ExpHOL.const 1073741832#64)
    have hm0_eq : ({ entry with locals := m0.locals, clock := m0.clock } : PanSemStateFiniteExact 64 F) = m0 := rfl
    rw [hm0_eq, hm1] at h
    exact h
  obtain ⟨wlen, hm1_eq⟩ := shMemLoad_local_none_inv m0 .opW (ofString "len") _ hm1
  have hm1_code : m1.code = originalRuntimeCode := heff_m1.code
  have hm1_len : m1.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm1_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨m2, hm2, hrun3⟩ := seq_returned_split (ite_call0_noret_dhi m1 _ _ _) hrun2
  obtain ⟨hm2_eq, hcond_le⟩ := ite_trap_with_keeps m1 m2 hm1_code _ _ hm2
  have hwlen_le : wlen.toNat ≤ 1073741808 := by
    simp only [evalHOLExact, evalListHOLExact, toExact, hm1_len,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hcond_le
    by_cases hlt : (1073741808#64 : BitVec 64) < wlen
    · simp [hlt] at hcond_le
    · simp [BitVec.lt_def] at hlt; exact hlt
  have heff_m2 : WorldEff s m2 Rl B dhiGw := by rw [hm2_eq]; exact heff_m1
  have heff_e2 : WorldEff entry m2 Rl B dhiGw := by rw [hm2_eq]; exact heff_e1
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm2_eq]; exact hm1_len
  obtain ⟨wp, nw, m3, p3, hsz_ev, _, hm3_loc, _, heff3, hwp_al, hwp_sb, hwp_lo, hwp_add, hhp3_hi, _, hrun4, hp3_eq⟩ :=
    decCall_alloc_returned_split heff_e2 hrun3
  have hnw_eq : nw = wlen + 8#64 := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm2_len, wordOpHOL, wordOp, valueIsWord, valueWord] at hsz_ev
    exact hsz_ev.symm
  subst hnw_eq
  have hnw_nat : (wlen + 8#64).toNat = wlen.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt]; · rfl
    · change wlen.toNat + 8 < 2 ^ 64; omega
  have hwp_hi : wp.toNat + wlen.toNat + 8 ≤ heapLimit := by omega
  obtain ⟨vi, p4, hvi, _, hrun5, hp4_eq⟩ := dec_returned_split hrun4
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m4 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m3
  obtain ⟨vw, p5, hvw, _, hrun6, hp5_eq⟩ := dec_returned_split hrun5
  have hvw0 : vw = .val (.word 0#64) := by simp [evalHOLExact] at hvw; exact hvw.symm
  subst hvw0
  let m5 := setVarHOLFinite (ofString "w") (.val (.word 0#64)) m4
  obtain ⟨m6, hm6, hret⟩ := seq_returned_split (while_noret_dhi m5 _ _ (fun u =>
    seq_noret_dhi u (shMemLoad_noret_dhi u _ _ _ _) (fun u1 _ =>
      seq_noret_dhi u1 (store_noret_dhi u1 _ _) (fun u2 _ =>
        assign_noret_dhi u2 _ _ _)))) hrun6
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m5, m4]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm5_len : m5.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m5, m4]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), hm3_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_len, show ofString "p" ≠ ofString "len" by decide]
  have hm6_p : m6.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    have hk := evaluate_keepLocal (ofString "p") _ (by decide) m5 (Or.inl (congrArg Prod.fst hm6))
    rw [hm6] at hk; rw [hk]; exact hm5_p
  have hm6_len : m6.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    have hk := evaluate_keepLocal (ofString "len") _ (by decide) m5 (Or.inl (congrArg Prod.fst hm6))
    rw [hm6] at hk; rw [hk]; exact hm5_len
  have hloop_g := while_none_inv_dhi _ _ (fun t : PanSemStateFiniteExact 64 F => t.globals = m3.globals)
    (fun _ h => h)
    (fun t _ => seq_nobreak_dhi t (shMemLoad_nobreak_dhi t _ _ _ _).1 (fun u1 _ =>
      seq_nobreak_dhi u1 (store_nobreak_dhi u1 _ _).1 (fun u2 _ => (assign_nobreak_dhi u2 _ _ _).1)))
    (fun t0 _ _ _ ht_g hf => (blob_loop_body_globals _ _ _ _ _ _ _ _ hf).trans ht_g)
    m5.clock m5 rfl rfl (congrArg Prod.fst hm6)
  rw [hm6] at hloop_g
  have hm6_glob : m6.globals = m3.globals := hloop_g.1
  rw [evaluateHOLFiniteState_return] at hret
  simp only [evalHOLExact, evalListHOLExact, toExact, hm6_p, hm6_len,
    Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
    Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret
  injection hret with hrv_eq hpost_eq
  injection hrv_eq with hrv_eq'
  injection hrv_eq' with hrv_eq''
  subst hrv_eq''
  have hpost_glob : post.globals = m3.globals := by
    rw [hp0_eq, hp3_eq, hp4_eq, hp5_eq]; dsimp only
    rw [← hpost_eq]; dsimp only [PanSemStateFiniteExact.emptyLocalsHOLFinite]
    exact hm6_glob
  have hpost_hp : globN post "heap_ptr" = globN m3 "heap_ptr" := by
    unfold globN; rw [hpost_glob]
  exact ⟨heff_s_post, heff_entry_post, wp, wlen, rfl, hwlen_le, hwp_sb, hwp_hi, hwp_al, hwp_lo,
    by rw [hpost_hp]; omega⟩

/-! ### `decode_bytes_list`: the slice facts pass through the length check -/

theorem decode_bytes_list_body_returns_slices {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {wp wlen wlim wmaxb : BitVec 64} {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlim : entry.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (hmaxb : entry.locals.lookup (ofString "maxb") = some (.val (.word wmaxb)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list) =
      (some (.returned rv), post)) :
    WorldEff s post Rl B dhiGw ∧
    WorldEff entry post Rl B dhiGw ∧
    ∃ (w_arr w_cnt : BitVec 64),
      rv = .rStruct [.val (.word w_arr), .val (.word w_cnt)] ∧
      w_cnt.toNat ≤ wlim.toNat ∧
      w_cnt.toNat < 2 ^ 30 ∧
      w_arr.toNat % 8 = 0 ∧
      WordsOK post (w_arr.toNat, 16 * w_cnt.toNat) ∧
      ((w_cnt.toNat = 0 ∧ w_arr.toNat = 0 ∧ wlen.toNat = 0) ∨
       (1 ≤ w_cnt.toNat ∧
        sourceBase ≤ w_arr.toNat ∧
        globN entry "heap_ptr" ≤ w_arr.toNat ∧
        w_arr.toNat + 16 * w_cnt.toNat ≤ globN post "heap_ptr" ∧
        globN post "heap_ptr" ≤ heapLimit ∧
        (∀ j : Nat, j < w_cnt.toNat → memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat) ∧
        (∀ j : Nat, j < w_cnt.toNat →
          ∃ o : Nat, memW post (w_arr.toNat + 16 * j) = (wp.toNat + o) % 2 ^ 64 ∧
            o + memW post (w_arr.toNat + 16 * j + 8) ≤ wlen.toNat))) := by
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post Rl B dhiGw := by
    have h := worldEff_decode_bytes_list_body heff hnt hcr
    rwa [hrun] at h
  have heff_entry_refl : WorldEff entry entry Rl B dhiGw :=
    WorldEff.refl entry Rl B dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post Rl B dhiGw := by
    have h := worldEff_decode_bytes_list_body heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_bytes_list, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨vals, fc, crv, cp, p0, hargs, hl, _, hc, _, _, hrun1, hp0_eq⟩ :=
    decCall_returned_split heff.code lookup_ssz_split_var_list hrun
  obtain ⟨wp', wlen', wlim', hvals_eq, hfc_p, hfc_len, hfc_lim⟩ :=
    lookupCode_three_words_any_dhi (by decide) (by decide) (by decide) lookup_ssz_split_var_list hl
  have hargs_eq : vals = [.val (.word wp), .val (.word wlen), .val (.word wlim)] := by
    rw [evalListHOLFinite_eq_toExact] at hargs
    simp [evalListHOLExact, evalHOLExact, toExact, hp, hlen, hlim] at hargs
    exact hargs.symm
  rw [hargs_eq] at hvals_eq
  injection hvals_eq with h1 htl1
  injection h1 with h1'; injection h1' with hwp_eq; subst hwp_eq
  injection htl1 with h2 htl2
  injection h2 with h2'; injection h2' with hwlen_eq; subst hwlen_eq
  injection htl2 with h3 _
  injection h3 with h3'; injection h3' with hwlim_eq; subst hwlim_eq
  obtain ⟨_, heff_ent_cp, w_arr, w_cnt, rfl, hcnt_lim, hcnt_lt, harr_al, hwok_cp, hcases⟩ :=
    ssz_split_var_list_body_returns_slices (heff_entry_refl.locals_clock fc (entry.clock - 1)) hfc_p hfc_len hfc_lim hc
  let m1 := setVarHOLFinite (ofString "r") (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) { cp with locals := entry.locals }
  obtain ⟨vi, p1, hvi, _, hrun2, hp1_eq⟩ := dec_returned_split hrun1
  have hvi0 : vi = .val (.word 0#64) := by simp [evalHOLExact] at hvi; exact hvi.symm
  subst hvi0
  let m2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m1
  obtain ⟨m3, hm3, hret⟩ := seq_returned_split (while_noret_dhi m2 _ _ (fun u =>
    seq_noret_dhi u (ite_call0_noret_dhi u _ _ _) (fun u1 _ => assign_noret_dhi u1 _ _ _))) hrun2
  have hm2_r : m2.locals.lookup (ofString "r") = some (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) := by
    dsimp only [m2, m1]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm3_r : m3.locals.lookup (ofString "r") = some (.rStruct [.val (.word w_arr), .val (.word w_cnt)]) := by
    have hk := evaluate_keepLocal (ofString "r") _ (by decide) m2 (Or.inl (congrArg Prod.fst hm3))
    rw [hm3] at hk; rw [hk]; exact hm2_r
  have hm2_code : m2.code = originalRuntimeCode := heff_ent_cp.code
  let InvDbl : PanSemStateFiniteExact 64 F → Prop := fun t =>
    t.code = originalRuntimeCode ∧ t.memory = cp.memory ∧ t.globals = cp.globals
  have hloop_ro := while_none_inv_dhi _ _ InvDbl (fun _ h => h)
    (fun t _ => seq_nobreak_dhi t (ite_call0_nobreak_dhi t _ _ _).1 (fun u1 _ => (assign_nobreak_dhi u1 _ _ _).1))
    (fun t0 _ _ _ ⟨ht_c, ht_m, ht_g⟩ hf => ?_)
    m2.clock m2 rfl ⟨hm2_code, rfl, rfl⟩ (congrArg Prod.fst hm3)
  · rw [hm3] at hloop_ro
    obtain ⟨⟨_, hm3_mem, hm3_glob⟩, _⟩ := hloop_ro
    rw [evaluateHOLFiniteState_return] at hret
    simp only [evalHOLExact, evalListHOLExact, toExact, hm3_r,
      Option.map, List.map, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      Flapjack.Pancake.PanLang.sizeOfShapesWithContextHOL, show (2 : Nat) ≤ 32 by decide, ↓reduceIte] at hret
    injection hret with hrv_eq hpost_m3
    cases hrv_eq
    have hpost_mem : post.memory = cp.memory := by
      rw [hp0_eq, hp1_eq]; dsimp only; rw [← hpost_m3]; exact hm3_mem
    have hpost_glob : post.globals = cp.globals := by
      rw [hp0_eq, hp1_eq]; dsimp only; rw [← hpost_m3]; exact hm3_glob
    have hpost_hp : globN post "heap_ptr" = globN cp "heap_ptr" := by unfold globN; rw [hpost_glob]
    have hpost_memW : ∀ a, memW post a = memW cp a := fun a => by unfold memW; rw [hpost_mem]
    refine ⟨heff_s_post, heff_entry_post, w_arr, w_cnt, rfl, hcnt_lim, hcnt_lt, harr_al, ?_, ?_⟩
    · rcases hcases with ⟨hcnt0, harr0, _⟩ | ⟨_, harr_sb, _, harr_hi, hcp_lim, _⟩
      · rw [hcnt0, harr0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
      · exact wordsOK_preserved_of_worldEff heff_entry_post harr_al (by omega) harr_sb (by omega)
    · rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩
      · exact Or.inl ⟨h1, h2, h3⟩
      · refine Or.inr ⟨h1, h2, h3, by rw [hpost_hp]; exact h4, heff_entry_post.arena.2.2.1, fun j hj => ?_, fun j hj => ?_⟩
        · rw [hpost_memW]; exact h6 j hj
        · obtain ⟨o, ho1, ho2⟩ := h7 j hj
          exact ⟨o, by rw [hpost_memW]; exact ho1, by rw [hpost_memW]; exact ho2⟩
  · obtain ⟨u1, hu1, _, hpost_a⟩ := seq_cont_or_none_split (ite_call0_nobreak_dhi (decClockHOLFinite t0) _ _ _).2 hf
    obtain ⟨hu1_eq, _⟩ := ite_ssz_fail_keeps (decClockHOLFinite t0) u1 ht_c _ _ hu1
    subst hu1_eq
    have hasg : InvDbl (evaluateHOLFiniteState (decClockHOLFinite t0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))).2 := by
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨ht_c, ht_m, ht_g⟩
      · split
        · exact ⟨ht_c, ht_m, ht_g⟩
        · exact ⟨ht_c, ht_m, ht_g⟩
    rwa [hpost_a]

end InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
