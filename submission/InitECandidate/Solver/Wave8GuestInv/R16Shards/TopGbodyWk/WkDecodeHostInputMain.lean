import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputReq
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDhiWorldEffTop

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

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

/-! ### Sound Postcondition Predicates for `decode_host_input` -/

def RetInputSound : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    (∀ i ∈ inputCells post w.toNat, i.1 % 8 = 0 ∧
      ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      WordsOK post i) ∧
    IvlsDisj (inputCells post w.toNat) (worldOwned post S' Nd') ∧
    memW post (memW post w.toNat + 40) < 2 ^ 63 ∧
    PayloadAt post (memW post w.toNat) ∧ RequestsAt post (memW post (w.toNat + 32))

def RetInputStrongSound : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    (∀ i ∈ runAttemptCells post w.toNat, i.1 % 8 = 0 ∧
      ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
      WordsOK post i) ∧
    IvlsDisj (runAttemptCells post w.toNat) (worldOwned post S' Nd') ∧
    memW post (memW post w.toNat + 40) < 2 ^ 63 ∧
    PayloadAt post (memW post w.toNat) ∧ RequestsAt post (memW post (w.toNat + 32)) ∧
    memW post (w.toNat + 16) < 2 ^ 32 ∧
    memW post (memW post w.toNat + 56) < 2 ^ 32

/-! ### `decode_stateless_input` Return Postcondition -/

private theorem assign_local_returned_split_eq {F : Type}
    {cur post : PanSemStateFiniteExact 64 F} {nm : MlS} {valExp : ExpHOL 64}
    {cont : ProgHOL 64} {rv : ValueHOL 64}
    (hrun : evaluateHOLFiniteState cur (.seq (.assign .local nm valExp) cont) = (some (.returned rv), post)) :
    ∃ v mid,
      @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp = some v ∧
      mid = { cur with locals := cur.locals.update (nm, v), clock := mid.clock } ∧
      evaluateHOLFiniteState mid cont = (some (.returned rv), post) := by
  obtain ⟨mid, hasg, hk⟩ := seq_returned_split (assign_noret_dhi cur _ _ _) hrun
  rw [evaluateHOLFiniteState_assign] at hasg
  rcases hv : @evalHOLExact 64 F _ cur.toExact (fun a => Classical.propDecidable (cur.memaddrs a)) valExp with _ | v
  · rw [hv] at hasg; simp at hasg
  · rw [hv] at hasg; dsimp only at hasg
    by_cases hvalid : isValidValueHOLFinite cur .local nm v = true
    · rw [if_pos hvalid] at hasg
      injection hasg with _ hmid
      subst hmid
      exact ⟨v, setKvarHOLFinite .local nm v cur, rfl, by cases cur; rfl, hk⟩
    · rw [if_neg hvalid] at hasg; simp at hasg

theorem decode_stateless_input_body_returns {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F}
    {wp0 wlen0 : BitVec 64} {rv : ValueHOL 64}
    (hOK : DhiOffsOK s)
    (heff : WorldEff s entry (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp0)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen0)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input) =
      (some (.returned rv), post)) :
    WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw ∧
    WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw ∧
    ∃ (w_si : BitVec 64),
      rv = .val (.word w_si) ∧
      (∀ i ∈ runAttemptCells post w_si.toNat,
        i.1 % 8 = 0 ∧
        ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i (globN entry "heap_ptr") (globN post "heap_ptr")) ∧
        WordsOK post i) ∧
      Inside (w_si.toNat, 96) (globN entry "heap_ptr") (globN post "heap_ptr") ∧
      Inside (memW post w_si.toNat, 136) (globN entry "heap_ptr") (globN post "heap_ptr") ∧
      Inside (memW post (w_si.toNat + 32), 80) (globN entry "heap_ptr") (globN post "heap_ptr") ∧
      WordsOK post (w_si.toNat, 40) ∧
      memW post (memW post w_si.toNat + 40) < 2 ^ 63 ∧
      PayloadAt post (memW post w_si.toNat) ∧
      RequestsAt post (memW post (w_si.toNat + 32)) ∧
      memW post (w_si.toNat + 16) < 2 ^ 32 ∧
      memW post (memW post w_si.toNat + 56) < 2 ^ 32 := by
  have hhl : heapLimit < 2 ^ 64 := by decide
  have hnt : (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_stateless_input)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_stateless_input_body_ok hOK heff hnt hcr
    rwa [hrun] at h
  have hOK_entry : DhiOffsOK entry := dhiOffsOK_of_worldEff hOK heff
  have heff_entry_refl : WorldEff entry entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl entry (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff.arena heff.code
  have heff_entry_post : WorldEff entry post (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_stateless_input_body_ok hOK_entry heff_entry_refl hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_stateless_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  -- 1. ite (len < 2) ssz_fail
  obtain ⟨m1, hm1_ite, hk1⟩ := seq_returned_split (ite_call0_noret_dhi entry _ _ _) hrun
  obtain ⟨hm1_eq, hlen0_ge2_cond⟩ := ite_ssz_fail_keeps entry m1 heff_entry_refl.code _ _ hm1_ite
  have hlen0_ge2 : 2 ≤ wlen0.toNat := by
    simp only [evalHOLExact, evalListHOLExact, toExact, hlen,
      Compiler.Encoders.Asm.wordCmpHOL, valueIsWord, valueWord] at hlen0_ge2_cond
    by_cases hlt : wlen0 < 2#64
    · simp [hlt] at hlen0_ge2_cond
    · simp [BitVec.lt_def] at hlt; exact hlt
  have heff1 : WorldEff entry m1 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm1_eq]; exact heff_entry_refl
  -- 2. ite (version != 21, 1) ssz_fail
  obtain ⟨m2, hm2_ite, hk2⟩ := seq_returned_split (ite_call0_noret_dhi m1 _ _ _) hk1
  obtain ⟨hm2_eq, _⟩ := ite_ssz_fail_keeps m1 m2 heff1.code _ _ hm2_ite
  have heff2 : WorldEff entry m2 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm2_eq]; exact heff1
  have hm2_p : m2.locals.lookup (ofString "p") = some (.val (.word wp0)) := by
    rw [hm2_eq, hm1_eq]; exact hp
  have hm2_len : m2.locals.lookup (ofString "len") = some (.val (.word wlen0)) := by
    rw [hm2_eq, hm1_eq]; exact hlen
  -- 3. assign p := p + 2; assign len := len - 2
  obtain ⟨vp, m3, hvp_ev, hm3_eq, hk3⟩ :=
    assign_local_returned_split_eq hk2
  have hvp_eq : vp = .val (.word (wp0 + 2#64)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm2_p, wordOpHOL, wordOp, valueIsWord, valueWord] at hvp_ev
    exact hvp_ev.symm
  subst hvp_eq
  have heff3 : WorldEff entry m3 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm3_eq]; exact heff2.locals_clock _ _
  have hm3_len0 : m3.locals.lookup (ofString "len") = some (.val (.word wlen0)) := by
    rw [hm3_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm2_len, show ofString "p" ≠ ofString "len" by decide]
  obtain ⟨vlen, m4, hvlen_ev, hm4_eq, hk4⟩ :=
    assign_local_returned_split_eq hk3
  have hvlen_eq : vlen = .val (.word (wlen0 - 2#64)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm3_len0, wordOpHOL, wordOp, valueIsWord, valueWord] at hvlen_ev
    exact hvlen_ev.symm
  subst hvlen_eq
  have heff4 : WorldEff entry m4 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm4_eq]; exact heff3.locals_clock _ _
  let wp := wp0 + 2#64
  let wlen := wlen0 - 2#64
  have hm4_p : m4.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm4_eq, hm3_eq]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "len" ≠ ofString "p" by decide, wp]
  have hm4_len : m4.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm4_eq]; simp [HolFiniteMapExact.lookup_update, FUPDATE, wlen]
  -- 4. ite (len < 16) ssz_fail
  obtain ⟨m5, hm5_ite, hk5⟩ := seq_returned_split (ite_call0_noret_dhi m4 _ _ _) hk4
  obtain ⟨hm5_eq, _⟩ := ite_ssz_fail_keeps m4 m5 heff4.code _ _ hm5_ite
  have heff5 : WorldEff entry m5 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm5_eq]; exact heff4
  have hm5_p : m5.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm5_eq]; exact hm4_p
  have hm5_len : m5.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm5_eq]; exact hm4_len
  -- 5. store ssz_offs+0 := le32(p), store ssz_offs+8 := le32(p+4), ssz_check_offsets(ssz_offs, 2, 16, len)
  obtain ⟨m6, vw6, hv6_ev, hm6_loc, _, heff6, hm6_eq, hm6_ne, hk6⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff5 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_op_word m5 _ ⟨_, _, rfl⟩) hk5
  obtain ⟨w_le0, hwle0_val, hwle0_lt⟩ := eval_le32_word_lt m5 _ _ _ _ (.val (.word vw6)) hv6_ev
  injection hwle0_val with h1; injection h1 with hw6_eq; subst hw6_eq
  obtain ⟨m7, vw7, hv7_ev, hm7_loc, _, heff7, hm7_eq, hm7_ne, hk7⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff6 8 (by omega) _ _ (Or.inr rfl)
      (eval_op_word m6 _ ⟨_, _, rfl⟩) hk6
  obtain ⟨w_le1, hwle1_val, hwle1_lt⟩ := eval_le32_word_lt m6 _ _ _ _ (.val (.word vw7)) hv7_ev
  injection hwle1_val with h1; injection h1 with hw7_eq; subst hw7_eq
  have hm7_p : m7.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm7_loc, hm6_loc]; exact hm5_p
  have hm7_len : m7.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm7_loc, hm6_loc]; exact hm5_len
  have hlen7_ev : @evalHOLExact 64 F _ m7.toExact (fun a => Classical.propDecidable (m7.memaddrs a))
      (.var .local (ofString "len")) = some (.val (.word wlen)) := by
    simp [evalHOLExact, toExact, hm7_len]
  obtain ⟨m8, hm8_mem, hm8_glob, hm8_loc, heff8, hm7_off0, hm7_bounds, hm7_mono, hk8⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff7 2#64 16#64 (.var .local (ofString "len"))
      (by decide) (by decide) hlen7_ev hk7
  -- 6. dec o_npr := load ssz_offs; dec o_wit := load (ssz_offs + 8)
  have hm8_m7_memW : ∀ a, memW m8 a = memW m7 a := fun a => by unfold memW; rw [hm8_mem]
  obtain ⟨vonpr, post_onpr, hvonpr, _, hk9, hpost_onpr⟩ := dec_returned_split hk8
  obtain ⟨w_onpr, rfl, hwonpr_eq⟩ := load_ssz_offs_const_eval hOK_entry heff8 0 (by decide) (by decide) _ (Or.inl ⟨rfl, rfl⟩) hvonpr
  rw [Nat.add_zero, hm8_m7_memW] at hwonpr_eq
  let m9 := setVarHOLFinite (ofString "o_npr") (.val (.word w_onpr)) m8
  have heff9 : WorldEff entry m9 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff8.locals_clock _ _
  obtain ⟨vowit, post_owit, hvowit, _, hk10, hpost_owit⟩ := dec_returned_split hk9
  obtain ⟨w_owit, rfl, hwowit_eq⟩ := load_ssz_offs_const_eval hOK_entry heff9 8 (by decide) (by decide) _ (Or.inr rfl) hvowit
  have hm9_m8_memW : ∀ a, memW m9 a = memW m8 a := fun _ => rfl
  rw [hm9_m8_memW, hm8_m7_memW] at hwowit_eq
  have howit_lt32 : w_owit.toNat < 2 ^ 32 := by rw [hwowit_eq, hm7_eq]; exact hwle1_lt
  have honpr_chain : w_onpr.toNat = 16 ∧ w_onpr.toNat ≤ w_owit.toNat ∧ w_owit.toNat ≤ wlen.toNat := by
    have h01 := hm7_mono 0 (by decide)
    have hb1 := (hm7_bounds 1 (by decide)).2
    have hn8 : 0 * 8 = 0 ∧ (0 + 1) * 8 = 8 ∧ 1 * 8 = 8 := by decide
    rw [hn8.1, hn8.2.1, Nat.add_zero] at h01
    rw [hn8.2.2] at hb1
    have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
    omega
  let m10 := setVarHOLFinite (ofString "o_wit") (.val (.word w_owit)) m9
  have heff10 : WorldEff entry m10 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff9.locals_clock _ _
  have hm10_p : m10.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m10, m9]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm8_loc]; exact hm7_p
  have hm10_len : m10.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m10, m9]; iterate 2 rw [lookup_setVar_ne _ _ _ _ (by decide)]
    rw [hm8_loc]; exact hm7_len
  have hm10_onpr : m10.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    dsimp only [m10]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm10_owit : m10.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := lookup_setVar_eq _ _ _
  -- 7. decCall si := alloc(96); store (si + 88) ...
  obtain ⟨w_si, nw_si, m11, post_si, hsz_si, hm11_mem, hm11_loc, _, heff11,
    hsi_al, hsi_sb, hsi_lo_m10, hsi_add_m11, hm11_lim, hwok_si_m11, hk11, hpost_si⟩ :=
    decCall_alloc_returned_split heff10 hk10
  have hnw_si : nw_si = 96#64 := by simp [evalHOLExact] at hsz_si; exact hsz_si.symm
  subst hnw_si
  have hsi_hi_m11 : w_si.toNat + 96 = globN m11 "heap_ptr" := by
    simpa [show (96#64 : BitVec 64).toNat = 96 from rfl] using hsi_add_m11
  have hsi_lo : globN entry "heap_ptr" ≤ w_si.toNat := by
    have h1 := heff10.hp_lo; omega
  have hm11_si : m11.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hm11_p : m11.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_p, show ofString "si" ≠ ofString "p" by decide]
  have hm11_len : m11.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_len, show ofString "si" ≠ ofString "len" by decide]
  have hm11_onpr : m11.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_onpr, show ofString "si" ≠ ofString "o_npr" by decide]
  have hm11_owit : m11.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm11_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm10_owit, show ofString "si" ≠ ofString "o_wit" by decide]
  obtain ⟨m12, _, _, hm12_loc, hm12_glob, heff12, _, _, hk12⟩ :=
    seq_store_fresh_returned heff11 (ofString "si") w_si 96 88 hm11_si hsi_lo (by omega) (by omega) _
      (eval_op_word m11 _ ⟨_, _, rfl⟩) hk11
  have hm12_hp : globN m12 "heap_ptr" = globN m11 "heap_ptr" := by unfold globN; rw [hm12_glob]
  have hm12_si : m12.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm12_loc]; exact hm11_si
  have hm12_p : m12.locals.lookup (ofString "p") = some (.val (.word wp)) := by rw [hm12_loc]; exact hm11_p
  have hm12_len : m12.locals.lookup (ofString "len") = some (.val (.word wlen)) := by rw [hm12_loc]; exact hm11_len
  have hm12_onpr : m12.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by rw [hm12_loc]; exact hm11_onpr
  have hm12_owit : m12.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by rw [hm12_loc]; exact hm11_owit
  -- 8. dec np := p + o_npr; dec nlen := o_wit - o_npr; ite (nlen < 44) ssz_fail
  obtain ⟨vnp, post_np, hvnp, _, hk13, hpost_np⟩ := dec_returned_split hk12
  have hvnp_eq : vnp = .val (.word (wp + w_onpr)) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm12_p, hm12_onpr, wordOpHOL, wordOp, valueIsWord, valueWord] at hvnp
    exact hvnp.symm
  subst hvnp_eq
  let w_np := wp + w_onpr
  let m13 := setVarHOLFinite (ofString "np") (.val (.word w_np)) m12
  obtain ⟨vnlen, post_nlen, hvnlen, _, hk14, hpost_nlen⟩ := dec_returned_split hk13
  have hm13_onpr : m13.locals.lookup (ofString "o_npr") = some (.val (.word w_onpr)) := by
    dsimp only [m13]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_onpr
  have hm13_owit : m13.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    dsimp only [m13]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_owit
  have hvnlen_eq : vnlen = .val (.word (w_owit - w_onpr)) := by
    change @evalHOLExact 64 F _ m13.toExact (fun a => Classical.propDecidable (m13.memaddrs a)) _ = _ at hvnlen
    simp [evalHOLExact, evalListHOLExact, toExact, hm13_owit, hm13_onpr, wordOpHOL, wordOp, valueIsWord, valueWord] at hvnlen
    exact hvnlen.symm
  subst hvnlen_eq
  let w_nlen := w_owit - w_onpr
  have hnlen_lt32 : w_nlen.toNat < 2 ^ 32 := by
    have hsub : (w_owit - w_onpr).toNat = w_owit.toNat - w_onpr.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    dsimp only [w_nlen]; omega
  let m14 := setVarHOLFinite (ofString "nlen") (.val (.word w_nlen)) m13
  have heff14 : WorldEff entry m14 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff12.locals_clock _ _
  obtain ⟨m15, hm15_ite, hk15⟩ := seq_returned_split (ite_call0_noret_dhi m14 _ _ _) hk14
  obtain ⟨hm15_eq, _⟩ := ite_ssz_fail_keeps m14 m15 heff14.code _ _ hm15_ite
  have heff15 : WorldEff entry m15 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm15_eq]; exact heff14
  -- 9. dec o_pl, o_vh, o_rq; store into ssz_offs + {0, 8, 16}; ssz_check_offsets(ssz_offs, 3, 44, nlen)
  obtain ⟨vopl, post_opl, hvopl, _, hk16, hpost_opl⟩ := dec_returned_split hk15
  obtain ⟨w_opl, rfl, _⟩ := eval_le32_word_lt m15 _ _ _ _ vopl hvopl
  let m16 := setVarHOLFinite (ofString "o_pl") (.val (.word w_opl)) m15
  obtain ⟨vovh, post_ovh, hvovh, _, hk17, hpost_ovh⟩ := dec_returned_split hk16
  obtain ⟨w_ovh, rfl, hovh_lt⟩ := eval_le32_word_lt m16 _ _ _ _ vovh hvovh
  let m17 := setVarHOLFinite (ofString "o_vh") (.val (.word w_ovh)) m16
  obtain ⟨vorq, post_orq, hvorq, _, hk18, hpost_orq⟩ := dec_returned_split hk17
  obtain ⟨w_orq, rfl, horq_lt⟩ := eval_le32_word_lt m17 _ _ _ _ vorq hvorq
  let m18 := setVarHOLFinite (ofString "o_rq") (.val (.word w_orq)) m17
  have heff18 : WorldEff entry m18 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff15.locals_clock _ _
  have hm18_hp : globN m18 "heap_ptr" = globN m11 "heap_ptr" := by
    change globN m15 "heap_ptr" = globN m11 "heap_ptr"
    rw [hm15_eq]; exact hm12_hp
  have hm15_si : m15.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm15_eq]; dsimp only [m14, m13]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_si
  have hm15_p : m15.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    rw [hm15_eq]; dsimp only [m14, m13]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_p
  have hm15_len : m15.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    rw [hm15_eq]; dsimp only [m14, m13]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]; exact hm12_len
  have hm15_owit : m15.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    rw [hm15_eq]; dsimp only [m14]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm13_owit
  have hm15_np : m15.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    rw [hm15_eq]; dsimp only [m14]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm15_nlen : m15.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm15_eq]; exact lookup_setVar_eq _ _ _
  have hm18_si : m18.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_si
  have hm18_p : m18.locals.lookup (ofString "p") = some (.val (.word wp)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_p
  have hm18_len : m18.locals.lookup (ofString "len") = some (.val (.word wlen)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_len
  have hm18_owit : m18.locals.lookup (ofString "o_wit") = some (.val (.word w_owit)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_owit
  have hm18_np : m18.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_np
  have hm18_nlen : m18.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm15_nlen
  have hm18_opl : m18.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by
    dsimp only [m18, m17, m16]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact lookup_setVar_eq _ _ _
  have hm18_ovh : m18.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    dsimp only [m18, m17]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact lookup_setVar_eq _ _ _
  have hm18_orq : m18.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := lookup_setVar_eq _ _ _
  obtain ⟨m19, vw19, hv19_ev, hm19_loc, hm19_glob, heff19, hm19_eq, hm19_ne, hk19⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff18 0 (by omega) _ _ (Or.inl ⟨rfl, rfl⟩)
      (eval_var_local_word m18 _ w_opl hm18_opl) hk18
  have hvw19 : vw19 = w_opl := by simp [evalHOLExact, toExact, hm18_opl] at hv19_ev; exact hv19_ev.symm
  rw [hvw19] at hm19_eq
  obtain ⟨m20, vw20, hv20_ev, hm20_loc, hm20_glob, heff20, hm20_eq, hm20_ne, hk20⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff19 8 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m19 _ w_ovh (by rw [hm19_loc]; exact hm18_ovh)) hk19
  have hvw20 : vw20 = w_ovh := by
    have h : m19.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by rw [hm19_loc]; exact hm18_ovh
    simp [evalHOLExact, toExact, h] at hv20_ev; exact hv20_ev.symm
  rw [hvw20] at hm20_eq
  obtain ⟨m21, vw21, hv21_ev, hm21_loc, hm21_glob, heff21, hm21_eq, hm21_ne, hk21⟩ :=
    seq_store_ssz_offs_const_returned_ok hOK_entry heff20 16 (by omega) _ _ (Or.inr rfl)
      (eval_var_local_word m20 _ w_orq (by rw [hm20_loc, hm19_loc]; exact hm18_orq)) hk20
  have hvw21 : vw21 = w_orq := by
    have h : m20.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by rw [hm20_loc, hm19_loc]; exact hm18_orq
    simp [evalHOLExact, toExact, h] at hv21_ev; exact hv21_ev.symm
  rw [hvw21] at hm21_eq
  have hm21_nlen : m21.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm21_loc, hm20_loc, hm19_loc]; exact hm18_nlen
  have hnlen21_ev : @evalHOLExact 64 F _ m21.toExact (fun a => Classical.propDecidable (m21.memaddrs a))
      (.var .local (ofString "nlen")) = some (.val (.word w_nlen)) := by
    simp [evalHOLExact, toExact, hm21_nlen]
  obtain ⟨m22, hm22_mem, hm22_glob, hm22_loc, heff22, hm21_off0, hm21_bounds, hm21_mono, hk22⟩ :=
    call0_ssz_check_offsets_returned_ok hOK_entry heff21 3#64 44#64 (.var .local (ofString "nlen"))
      (by decide) (by decide) hnlen21_ev hk21
  have hm22_hp : globN m22 "heap_ptr" = globN m11 "heap_ptr" := by
    unfold globN; rw [hm22_glob, hm21_glob, hm20_glob, hm19_glob]; exact hm18_hp
  have hnpr_chain : w_opl.toNat = 44 ∧ w_opl.toNat ≤ w_ovh.toNat ∧ w_ovh.toNat ≤ w_orq.toNat ∧ w_orq.toNat ≤ w_nlen.toNat := by
    have hhe : heapEnd < 2 ^ 64 := by decide
    have hoff_hi : globN entry "ssz_offs" + 64 ≤ heapEnd := by
      rcases hOK_entry.2 with hg0 | ⟨_, hhi, _, _⟩
      · exfalso
        obtain ⟨mid_s, hst_s, _⟩ := seq_returned_split (store_noret_dhi m18 _ _) hk18
        obtain ⟨sw, hsw_e⟩ := hOK_entry.1.2.2.2.2.2.2.2.2.2 "ssz_offs" (by decide)
        have hsw18 : m18.globals.lookup (ofString "ssz_offs") = some (.val (.word sw)) :=
          (heff18.gw_kept (ofString "ssz_offs") (by decide)).symm.trans hsw_e
        have hsw0 : sw = 0#64 := BitVec.eq_of_toNat_eq (by unfold GlobalWord at hsw_e; simp [globN, hsw_e] at hg0; simp [hg0])
        subst hsw0
        rw [evaluateHOLFiniteState_store] at hst_s
        have hndom : ¬ m18.memaddrs 0#64 := by
          rw [heff18.memaddrs, hOK_entry.1.1.memaddrs, ordinaryDomain_iff]
          have : 0 < sourceBase := by decide
          simp; omega
        simp [evalHOLExact, toExact, hsw18, hm18_opl, flattenHOL, panMemStoresHOL, panMemStoreHOL, hndom] at hst_s
      · exact hhi
    have ha0 : memW m21 (globN entry "ssz_offs") = w_opl.toNat := by
      rw [hm21_ne _ (by omega) (by omega), hm20_ne _ (by omega) (by omega)]; simpa using hm19_eq
    have ha1 : memW m21 (globN entry "ssz_offs" + 8) = w_ovh.toNat := by
      rw [hm21_ne _ (by omega) (by omega), hm20_eq]
    have ha2 : memW m21 (globN entry "ssz_offs" + 16) = w_orq.toNat := hm21_eq
    have hm01 := hm21_mono 0 (by decide)
    have hm12 := hm21_mono 1 (by decide)
    have hb2 := (hm21_bounds 2 (by decide)).2
    have hn8 : 0 * 8 = 0 ∧ (0 + 1) * 8 = 8 ∧ 1 * 8 = 8 ∧ (1 + 1) * 8 = 16 ∧ 2 * 8 = 16 := by decide
    rw [hn8.1, hn8.2.1, Nat.add_zero] at hm01
    rw [hn8.2.2.1, hn8.2.2.2.1] at hm12
    rw [hn8.2.2.2.2] at hb2
    have h44 : (44#64 : BitVec 64).toNat = 44 := rfl
    omega
  have hm22_loc_m18 : m22.locals = m18.locals := by rw [hm22_loc, hm21_loc, hm20_loc, hm19_loc]
  have hm22_si : m22.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm22_loc_m18]; exact hm18_si
  have hm22_np : m22.locals.lookup (ofString "np") = some (.val (.word w_np)) := by rw [hm22_loc_m18]; exact hm18_np
  have hm22_nlen : m22.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by rw [hm22_loc_m18]; exact hm18_nlen
  have hm22_opl : m22.locals.lookup (ofString "o_pl") = some (.val (.word w_opl)) := by rw [hm22_loc_m18]; exact hm18_opl
  have hm22_ovh : m22.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by rw [hm22_loc_m18]; exact hm18_ovh
  have hm22_orq : m22.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by rw [hm22_loc_m18]; exact hm18_orq
  -- 10. decCall pl := decode_payload(np + o_pl, o_vh - o_pl); store (si + 0) pl
  obtain ⟨vals_pl, fc_pl, rv_pl, cp_pl, post_pl, hargs_pl, hl_pl, _, hc_pl, _, _, hk23, hpost_pl⟩ :=
    decCall_returned_split heff22.code lookup_decode_payload hk22
  obtain ⟨wp_pl, wlen_pl, _, hfc_pl_p, hfc_pl_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_payload hl_pl
  obtain ⟨heff_cp_pl, heff_step_pl, w_pl, rfl, hpl_al, hpl_sb, hpl_lo_m22, hpl_hi_cp, hcp_pl_lim,
    hwok_pl_cp, hpl_at_cp, hntx_lt32_cp, hnwd_lt32_cp, htxp_al_cp, hwok_tx_cp, htx_cases_cp⟩ :=
    decode_payload_body_returns hOK_entry (heff22.locals_clock fc_pl (m22.clock - 1)) hfc_pl_p hfc_pl_len hc_pl
  have hpl_lo_si : w_si.toNat + 96 ≤ w_pl.toNat := by
    change globN m22 "heap_ptr" ≤ w_pl.toNat at hpl_lo_m22; omega
  let m23 := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) { cp_pl with locals := m22.locals }
  have heff23 : WorldEff entry m23 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_pl.locals_clock _ _
  have hm23_pl : m23.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := lookup_setVar_eq _ _ _
  have hm23_si : m23.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_si
  obtain ⟨m24, vw24, hv24_ev, hm24_loc, hm24_glob, heff24, hm24_si0, hm24_ne, hk24⟩ :=
    seq_store_fresh_returned heff23 (ofString "si") w_si 96 0 hm23_si hsi_lo (by have := heff_step_pl.hp_lo; change globN m22 "heap_ptr" ≤ _ at this; omega) (by omega) _
      (eval_var_local_word m23 _ w_pl hm23_pl) hk23
  have hvw24 : vw24 = w_pl := by simp [evalHOLExact, toExact, hm23_pl] at hv24_ev; exact hv24_ev.symm
  rw [hvw24, Nat.add_zero] at hm24_si0
  -- 11. decCall nvh := ssz_fixed_list_count(o_rq - o_vh, 32, 2^63 - 1); store si + {8, 16, 24}
  have hm24_ovh : m24.locals.lookup (ofString "o_vh") = some (.val (.word w_ovh)) := by
    rw [hm24_loc]; dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_ovh
  have hm24_orq : m24.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm24_loc]; dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_orq
  have hsub_vh_ev : @evalHOLExact 64 F _ m24.toExact (fun a => Classical.propDecidable (m24.memaddrs a))
      (.op .sub [.var .local (ofString "o_rq"), .var .local (ofString "o_vh")]) =
      some (.val (.word (w_orq - w_ovh))) := by
    simp [evalHOLExact, evalListHOLExact, toExact, hm24_orq, hm24_ovh, wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨w_nvh, m25, post_nvh, _, hmul_nvh, _, hm25_mem, hm25_glob, hm25_loc, heff25, hk25, hpost_nvh⟩ :=
    decCall_ssz_fixed_list_count_returned heff24 (ofString "nvh") _ 32#64 9223372036854775807#64 hsub_vh_ev hk24
  have hnvh_lt32 : w_nvh.toNat < 2 ^ 32 := by
    have hvh_le_rq : w_ovh.toNat ≤ w_orq.toNat := hnpr_chain.2.2.1
    have hsub : (w_orq - w_ovh).toNat = w_orq.toNat - w_ovh.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    rw [show (32#64 : BitVec 64).toNat = 32 from rfl, hsub] at hmul_nvh
    omega
  have hm25_hp : globN m25 "heap_ptr" = globN cp_pl "heap_ptr" := by
    unfold globN; rw [hm25_glob, hm24_glob]; rfl
  have hm25_si : m25.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm25_loc, hm24_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm23_si, show ofString "nvh" ≠ ofString "si" by decide]
  have hm25_nvh : m25.locals.lookup (ofString "nvh") = some (.val (.word w_nvh)) := by
    rw [hm25_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨m26, _, _, hm26_loc, hm26_glob, heff26, _, hm26_ne, hk26⟩ :=
    seq_store_fresh_returned heff25 (ofString "si") w_si 96 8 hm25_si hsi_lo (by omega) (by omega) _
      (eval_op_word m25 _ ⟨_, _, rfl⟩) hk25
  obtain ⟨m27, vw27, hvw27_ev, hm27_loc, hm27_glob, heff27, hm27_si16, hm27_ne, hk27⟩ :=
    seq_store_fresh_returned heff26 (ofString "si") w_si 96 16 (by rw [hm26_loc]; exact hm25_si) hsi_lo
      (by have : globN m26 "heap_ptr" = globN m25 "heap_ptr" := by unfold globN; rw [hm26_glob]
          omega) (by omega) _
      (eval_var_local_word m26 _ w_nvh (by rw [hm26_loc]; exact hm25_nvh)) hk26
  have hvw27 : vw27 = w_nvh := by
    have h26_nvh : m26.locals.lookup (ofString "nvh") = some (.val (.word w_nvh)) := by
      rw [hm26_loc]; exact hm25_nvh
    simp [evalHOLExact, toExact, h26_nvh] at hvw27_ev; exact hvw27_ev.symm
  rw [hvw27] at hm27_si16
  obtain ⟨m28, _, _, hm28_loc, hm28_glob, heff28, _, hm28_ne, hk28⟩ :=
    seq_store_fresh_returned heff27 (ofString "si") w_si 96 24 (by rw [hm27_loc, hm26_loc]; exact hm25_si) hsi_lo
      (by have : globN m27 "heap_ptr" = globN m25 "heap_ptr" := by unfold globN; rw [hm27_glob, hm26_glob]
          omega) (by omega) _
      (eval_op_word m27 _ ⟨_, _, rfl⟩) hk27
  have hm28_hp : globN m28 "heap_ptr" = globN cp_pl "heap_ptr" := by
    unfold globN; rw [hm28_glob, hm27_glob, hm26_glob]; exact hm25_hp
  have hm28_loc_m25 : m28.locals = m25.locals := by rw [hm28_loc, hm27_loc, hm26_loc]
  have hm28_si : m28.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm28_loc_m25]; exact hm25_si
  have hm28_np : m28.locals.lookup (ofString "np") = some (.val (.word w_np)) := by
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "np" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_np
  have hm28_nlen : m28.locals.lookup (ofString "nlen") = some (.val (.word w_nlen)) := by
    rw [hm28_loc_m25, hm25_loc, hm24_loc]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nvh" ≠ ofString "nlen" by decide]
    dsimp only [m23]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm22_nlen
  have hm28_orq : m28.locals.lookup (ofString "o_rq") = some (.val (.word w_orq)) := by
    rw [hm28_loc_m25, hm25_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hm24_orq, show ofString "nvh" ≠ ofString "o_rq" by decide]
  -- 12. decCall rq := decode_requests(np + o_rq, nlen - o_rq); store (si + 32) rq
  obtain ⟨vals_rq, fc_rq, rv_rq, cp_rq, post_rq, hargs_rq, hl_rq, _, hc_rq, _, _, hk29, hpost_rq⟩ :=
    decCall_returned_split heff28.code lookup_decode_requests hk28
  obtain ⟨wp_rq, wlen_rq, hvs_rq, hfc_rq_p, hfc_rq_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_requests hl_rq
  have hargs_rq_eq : vals_rq = [.val (.word (w_np + w_orq)), .val (.word (w_nlen - w_orq))] := by
    rw [evalListHOLFinite_eq_toExact] at hargs_rq
    simp [evalListHOLExact, evalHOLExact, toExact, hm28_np, hm28_nlen, hm28_orq, wordOpHOL, wordOp, valueIsWord, valueWord] at hargs_rq
    exact hargs_rq.symm
  rw [hargs_rq_eq] at hvs_rq
  injection hvs_rq with h1 htl; injection htl with h2 _
  injection h2 with h2'; injection h2' with hlen_rq_eq; subst hlen_rq_eq
  have hlen_rq_lt32 : (w_nlen - w_orq).toNat < 2 ^ 32 := by
    have hsub : (w_nlen - w_orq).toNat = w_nlen.toNat - w_orq.toNat :=
      BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)
    omega
  obtain ⟨heff_cp_rq, heff_step_rq, w_rq, rfl, hrq_al, hrq_sb, hrq_lo_m28, hrq_hi_cp, hcp_rq_lim, hwok_rq_cp, hrq_at_cp⟩ :=
    decode_requests_body_returns hOK_entry (heff28.locals_clock fc_rq (m28.clock - 1)) hfc_rq_p hfc_rq_len hlen_rq_lt32 hc_rq
  have hrq_lo_cp_pl : globN cp_pl "heap_ptr" ≤ w_rq.toNat := by
    change globN m28 "heap_ptr" ≤ w_rq.toNat at hrq_lo_m28; omega
  let m29 := setVarHOLFinite (ofString "rq") (.val (.word w_rq)) { cp_rq with locals := m28.locals }
  have heff29 : WorldEff entry m29 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_rq.locals_clock _ _
  have hm29_rq : m29.locals.lookup (ofString "rq") = some (.val (.word w_rq)) := lookup_setVar_eq _ _ _
  have hm29_si : m29.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m29]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm28_si
  obtain ⟨m30, vw30, hv30_ev, hm30_loc, hm30_glob, heff30, hm30_si32, hm30_ne, hk30⟩ :=
    seq_store_fresh_returned heff29 (ofString "si") w_si 96 32 hm29_si hsi_lo (by omega) (by omega) _
      (eval_var_local_word m29 _ w_rq hm29_rq) hk29
  have hvw30 : vw30 = w_rq := by simp [evalHOLExact, toExact, hm29_rq] at hv30_ev; exact hv30_ev.symm
  rw [hvw30] at hm30_si32
  have hm30_hp : globN m30 "heap_ptr" = globN cp_rq "heap_ptr" := by unfold globN; rw [hm30_glob]; rfl
  -- 13. dec wp := p + o_wit; dec wlen := len - o_wit; ite (wlen < 12) ssz_fail; while (i < 3); ssz_check_offsets; dec w0, w1, w2
  have hm30_si : m30.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm30_loc]; exact hm29_si
  obtain ⟨vwp_w, post_wpw, hvwp_w, _, hk31, hpost_wpw⟩ := dec_returned_split hk30
  let m31 := setVarHOLFinite (ofString "wp") vwp_w m30
  obtain ⟨vwlen_w, post_wlenw, hvwlen_w, _, hk32, hpost_wlenw⟩ := dec_returned_split hk31
  let m32 := setVarHOLFinite (ofString "wlen") vwlen_w m31
  have heff32 : WorldEff entry m32 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff30.locals_clock _ _
  obtain ⟨m33, hm33_ite, hk33⟩ := seq_returned_split (ite_call0_noret_dhi m32 _ _ _) hk32
  obtain ⟨hm33_eq, _⟩ := ite_ssz_fail_keeps m32 m33 heff32.code _ _ hm33_ite
  have heff33 : WorldEff entry m33 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    rw [hm33_eq]; exact heff32
  obtain ⟨vi3, post_i3, hvi3, _, hk34, hpost_i3⟩ := dec_returned_split hk33
  have hvi3_eq : vi3 = .val (.word 0#64) := by simp [evalHOLExact] at hvi3; exact hvi3.symm
  subst hvi3_eq
  let m34 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) m33
  have heff34 : WorldEff entry m34 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff33.locals_clock _ _
  obtain ⟨m35, hm35_w, hk35⟩ := seq_returned_split
    (while_noret_dhi m34 _ _ (fun u =>
      seq_noret_dhi u (store_noret_dhi u _ _) (fun u2 _ => assign_noret_dhi u2 _ _ _))) hk34
  let Inv3 : PanSemStateFiniteExact 64 F → Prop :=
    fun t => ∃ wi : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word wi)) ∧ wi.toNat ≤ 3
  have heff_34_35 : WorldEff m34 m35 (dhiOffsRegions m34) ([] : List (String × Nat)) dhiGw := by
    have hOK_34 := dhiOffsOK_of_worldEff hOK_entry heff34
    have heff34_refl := WorldEff.refl m34 (dhiOffsRegions m34) ([] : List (String × Nat)) dhiGw heff34.arena heff34.code
    exact worldEff_of_none_dhi hm35_w (fun hnt_w hcr_w =>
      worldEff_while_cond_dhi _ Inv3 (fun _ h => h)
        (fun t0 cw hcond hnz heff_t ⟨wi, ht_i, hwi_le⟩ hnt_b hcr_b => by
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word wi)) := ht_i
          have hwi_lt : wi.toNat < 3 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp only [evalHOLExact, evalListHOLExact, toExact, ht0_i,
              Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small wi 3#64 (by omega) (by decide)] at hcond
            by_cases hlt : wi.toNat < 3
            · exact hlt
            · have h3 : (3#64 : BitVec 64).toNat = 3 := rfl
              simp [h3, hlt] at hcond; exact absurd hcond.symm hnz
          have hoff_eq : (wi * 8#64).toNat = wi.toNat * 8 := by
            rw [BitVec.toNat_mul, show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
          refine ⟨?_, fun hf => ?_⟩
          · refine worldEff_seq hnt_b hcr_b
              (fun _ _ => worldEff_store_ssz_offs_dyn_ok hOK_34 heff_t _ _ (wi * 8#64)
                (by simp [evalHOLExact, panOpHOL, evalListHOLExact, toExact, decClockHOLFinite, ht0_i, valueIsWord, valueWord])
                (by omega) (eval_op_word (decClockHOLFinite t0) _ ⟨_, _, rfl⟩))
              (fun tb _ heff_tb _ _ => worldEff_assign_local heff_tb _ _)
          · exact evaluate_incTail_le (ofString "i") 3 (by decide) _ (by decide) (decClockHOLFinite t0) wi ht_i hwi_lt hf)
        m34.clock m34 rfl heff34_refl ⟨0#64, lookup_setVar_eq _ _ _, by decide⟩ hnt_w hcr_w)
  have heff35 : WorldEff entry m35 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have hr := dhiOffsRegions_eq_of_worldEff heff34
    rw [hr] at heff_34_35
    exact heff34.trans_noBuf heff_34_35 (by intro _ h; cases h) dhi_no_gb
  obtain ⟨m36, hm36_chk, hk36⟩ := seq_returned_split (call0_noret_dhi m35 _ _) hk35
  have heff_35_36 : WorldEff m35 m36 (dhiOffsRegions m35) ([] : List (String × Nat)) dhiGw := by
    have heff35_refl := WorldEff.refl m35 (dhiOffsRegions m35) ([] : List (String × Nat)) dhiGw heff35.arena heff35.code
    exact worldEff_of_none_dhi hm36_chk (fun hnt_a hcr_a =>
      worldEff_call0_ro heff35_refl ro_ssz_check_offsets_local _ hnt_a hcr_a)
  have heff36 : WorldEff entry m36 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := by
    have hr := dhiOffsRegions_eq_of_worldEff heff35
    rw [hr] at heff_35_36
    exact heff35.trans_noBuf heff_35_36 (by intro _ h; cases h) dhi_no_gb
  have hm34_si : m34.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m34]; rw [lookup_setVar_ne _ _ _ _ (by decide), hm33_eq]
    dsimp only [m32, m31]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm30_si
  have hm35_si : m35.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    have hk := evaluate_keepLocal (ofString "si") _ (by decide) m34 (Or.inl (congrArg Prod.fst hm35_w))
    rw [hm35_w] at hk; rw [hk]; exact hm34_si
  have hm36_si : m36.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    have hk := evaluate_keepLocal (ofString "si") _ (by decide) m35 (Or.inl (congrArg Prod.fst hm36_chk))
    rw [hm36_chk] at hk; rw [hk]; exact hm35_si
  obtain ⟨vw0, post_w0, _, _, hk37, hpost_w0⟩ := dec_returned_split hk36
  let m37 := setVarHOLFinite (ofString "w0") vw0 m36
  obtain ⟨vw1, post_w1, _, _, hk38, hpost_w1⟩ := dec_returned_split hk37
  let m38 := setVarHOLFinite (ofString "w1") vw1 m37
  obtain ⟨vw2, post_w2, _, _, hk39, hpost_w2⟩ := dec_returned_split hk38
  let m39 := setVarHOLFinite (ofString "w2") vw2 m38
  have heff39 : WorldEff entry m39 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff36.locals_clock _ _
  have hm39_si : m39.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m39, m38, m37]
    rw [lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide), lookup_setVar_ne _ _ _ _ (by decide)]
    exact hm36_si
  have hm30_39_eff : WorldEff m30 m39 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
    have h30_34 : WorldEff m30 m34 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
      have h0 := WorldEff.refl m30 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw heff30.arena heff30.code
      have h32 := h0.locals_clock m32.locals m32.clock
      have h33 : WorldEff m30 m33 (dhiOffsRegions m30) ([] : List (String × Nat)) dhiGw := by
        rw [hm33_eq]; exact h32
      exact h33.locals_clock _ _
    have hr34 : dhiOffsRegions m34 = dhiOffsRegions m30 := dhiOffsRegions_eq_of_worldEff h30_34
    have h30_35 := h30_34.trans_noBuf (by rwa [hr34] at heff_34_35) (by intro _ h; cases h) dhi_no_gb
    have hr35 : dhiOffsRegions m35 = dhiOffsRegions m30 := dhiOffsRegions_eq_of_worldEff h30_35
    have h30_36 := h30_35.trans_noBuf (by rwa [hr35] at heff_35_36) (by intro _ h; cases h) dhi_no_gb
    exact h30_36.locals_clock _ _
  have hm39_hp_ge : globN cp_rq "heap_ptr" ≤ globN m39 "heap_ptr" := by
    have h30_hp : globN m30 "heap_ptr" = globN cp_rq "heap_ptr" := by unfold globN; rw [hm30_glob]; rfl
    have h := hm30_39_eff.hp_lo; omega
  -- 14. decCall st0 := decode_bytes_list(...); store si + 40; store si + 48
  obtain ⟨vals_st0, fc_st0, rv_st0, cp_st0, post_st0, _, hl_st0, _, hc_st0, _, _, hk40, hpost_st0⟩ :=
    decCall_returned_split heff39.code lookup_decode_bytes_list hk39
  obtain ⟨_, _, _, _, _, hst0_p, hst0_len, hst0_lim, hst0_maxb⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_st0
  obtain ⟨heff_cp_st0, heff_step_st0, w_st0a, w_st0b, rfl, _, hst0b_lt30, hst0a_al, _, hst0_cases⟩ :=
    decode_bytes_list_body_returns (heff39.locals_clock fc_st0 (m39.clock - 1)) hst0_p hst0_len hst0_lim hst0_maxb hc_st0
  let m40 := setVarHOLFinite (ofString "st0") (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) { cp_st0 with locals := m39.locals }
  have heff40 : WorldEff entry m40 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_st0.locals_clock _ _
  have hm40_st0 : m40.locals.lookup (ofString "st0") = some (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) := lookup_setVar_eq _ _ _
  have hm40_si : m40.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m40]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm39_si
  have hm40_hp_ge : globN cp_rq "heap_ptr" ≤ globN m40 "heap_ptr" := by
    have h := heff_step_st0.hp_lo; change globN m39 "heap_ptr" ≤ globN cp_st0 "heap_ptr" at h
    change globN cp_rq "heap_ptr" ≤ globN cp_st0 "heap_ptr"; omega
  obtain ⟨m41, vw41, hv41_ev, hm41_loc, hm41_glob, heff41, hm41_si40, hm41_ne, hk41⟩ :=
    seq_store_fresh_returned heff40 (ofString "si") w_si 96 40 hm40_si hsi_lo (by omega) (by omega) _
      (eval_rfield_word m40 0 _ w_st0a w_st0b hm40_st0 (Or.inl rfl)) hk40
  have hvw41 : vw41 = w_st0a := by
    simp [evalHOLExact, toExact, hm40_st0] at hv41_ev; exact hv41_ev.symm
  rw [hvw41] at hm41_si40
  obtain ⟨m42, vw42, hv42_ev, hm42_loc, hm42_glob, heff42, hm42_si48, hm42_ne, hk42⟩ :=
    seq_store_fresh_returned heff41 (ofString "si") w_si 96 48 (by rw [hm41_loc]; exact hm40_si) hsi_lo
      (by have : globN m41 "heap_ptr" = globN m40 "heap_ptr" := by unfold globN; rw [hm41_glob]
          omega) (by omega) _
      (eval_rfield_word m41 1 _ w_st0a w_st0b (by rw [hm41_loc]; exact hm40_st0) (Or.inr rfl)) hk41
  have hvw42 : vw42 = w_st0b := by
    have h : m41.locals.lookup (ofString "st0") = some (.rStruct [.val (.word w_st0a), .val (.word w_st0b)]) := by
      rw [hm41_loc]; exact hm40_st0
    simp [evalHOLExact, toExact, h] at hv42_ev; exact hv42_ev.symm
  rw [hvw42] at hm42_si48
  have hm42_hp : globN m42 "heap_ptr" = globN cp_st0 "heap_ptr" := by unfold globN; rw [hm42_glob, hm41_glob]; rfl
  have hm42_si : m42.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm42_loc, hm41_loc]; exact hm40_si
  -- 15. decCall cd := decode_bytes_list(...); store si + 56; store si + 64
  obtain ⟨vals_cd, fc_cd, rv_cd, cp_cd, post_cd, _, hl_cd, _, hc_cd, _, _, hk43, hpost_cd⟩ :=
    decCall_returned_split heff42.code lookup_decode_bytes_list hk42
  obtain ⟨_, _, _, _, _, hcd_p, hcd_len, hcd_lim, hcd_maxb⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_cd
  obtain ⟨heff_cp_cd, heff_step_cd, w_cda, w_cdb, rfl, _, hcdb_lt30, hcda_al, _, hcd_cases⟩ :=
    decode_bytes_list_body_returns (heff42.locals_clock fc_cd (m42.clock - 1)) hcd_p hcd_len hcd_lim hcd_maxb hc_cd
  let m43 := setVarHOLFinite (ofString "cd") (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) { cp_cd with locals := m42.locals }
  have heff43 : WorldEff entry m43 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_cd.locals_clock _ _
  have hm43_cd : m43.locals.lookup (ofString "cd") = some (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) := lookup_setVar_eq _ _ _
  have hm43_si : m43.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m43]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm42_si
  have hm43_hp_ge : globN cp_st0 "heap_ptr" ≤ globN m43 "heap_ptr" := by
    have h := heff_step_cd.hp_lo; change globN m42 "heap_ptr" ≤ globN cp_cd "heap_ptr" at h
    change globN cp_st0 "heap_ptr" ≤ globN cp_cd "heap_ptr"; omega
  obtain ⟨m44, vw44, hv44_ev, hm44_loc, hm44_glob, heff44, hm44_si56, hm44_ne, hk44⟩ :=
    seq_store_fresh_returned heff43 (ofString "si") w_si 96 56 hm43_si hsi_lo (by omega) (by omega) _
      (eval_rfield_word m43 0 _ w_cda w_cdb hm43_cd (Or.inl rfl)) hk43
  have hvw44 : vw44 = w_cda := by
    simp [evalHOLExact, toExact, hm43_cd] at hv44_ev; exact hv44_ev.symm
  rw [hvw44] at hm44_si56
  obtain ⟨m45, vw45, hv45_ev, hm45_loc, hm45_glob, heff45, hm45_si64, hm45_ne, hk45⟩ :=
    seq_store_fresh_returned heff44 (ofString "si") w_si 96 64 (by rw [hm44_loc]; exact hm43_si) hsi_lo
      (by have : globN m44 "heap_ptr" = globN m43 "heap_ptr" := by unfold globN; rw [hm44_glob]
          omega) (by omega) _
      (eval_rfield_word m44 1 _ w_cda w_cdb (by rw [hm44_loc]; exact hm43_cd) (Or.inr rfl)) hk44
  have hvw45 : vw45 = w_cdb := by
    have h : m44.locals.lookup (ofString "cd") = some (.rStruct [.val (.word w_cda), .val (.word w_cdb)]) := by
      rw [hm44_loc]; exact hm43_cd
    simp [evalHOLExact, toExact, h] at hv45_ev; exact hv45_ev.symm
  rw [hvw45] at hm45_si64
  have hm45_hp : globN m45 "heap_ptr" = globN cp_cd "heap_ptr" := by unfold globN; rw [hm45_glob, hm44_glob]; rfl
  have hm45_si : m45.locals.lookup (ofString "si") = some (.val (.word w_si)) := by rw [hm45_loc, hm44_loc]; exact hm43_si
  -- 16. decCall hd := decode_bytes_list(...); store si + 72; store si + 80; return si
  obtain ⟨vals_hd, fc_hd, rv_hd, cp_hd, post_hd, _, hl_hd, _, hc_hd, _, _, hk46, hpost_hd⟩ :=
    decCall_returned_split heff45.code lookup_decode_bytes_list hk45
  obtain ⟨_, _, _, _, _, hhd_p, hhd_len, hhd_lim, hhd_maxb⟩ :=
    lookupCode_four_words_any_dhi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      lookup_decode_bytes_list hl_hd
  obtain ⟨heff_cp_hd, heff_step_hd, w_hda, w_hdb, rfl, _, hhdb_lt30, hhda_al, _, hhd_cases⟩ :=
    decode_bytes_list_body_returns (heff45.locals_clock fc_hd (m45.clock - 1)) hhd_p hhd_len hhd_lim hhd_maxb hc_hd
  let m46 := setVarHOLFinite (ofString "hd") (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) { cp_hd with locals := m45.locals }
  have heff46 : WorldEff entry m46 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw := heff_cp_hd.locals_clock _ _
  have hm46_hd : m46.locals.lookup (ofString "hd") = some (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) := lookup_setVar_eq _ _ _
  have hm46_si : m46.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    dsimp only [m46]; rw [lookup_setVar_ne _ _ _ _ (by decide)]; exact hm45_si
  have hm46_hp_ge : globN cp_cd "heap_ptr" ≤ globN m46 "heap_ptr" := by
    have h := heff_step_hd.hp_lo; change globN m45 "heap_ptr" ≤ globN cp_hd "heap_ptr" at h
    change globN cp_cd "heap_ptr" ≤ globN cp_hd "heap_ptr"; omega
  obtain ⟨m47, vw47, hv47_ev, hm47_loc, hm47_glob, heff47, hm47_si72, hm47_ne, hk47⟩ :=
    seq_store_fresh_returned heff46 (ofString "si") w_si 96 72 hm46_si hsi_lo (by omega) (by omega) _
      (eval_rfield_word m46 0 _ w_hda w_hdb hm46_hd (Or.inl rfl)) hk46
  have hvw47 : vw47 = w_hda := by
    simp [evalHOLExact, toExact, hm46_hd] at hv47_ev; exact hv47_ev.symm
  rw [hvw47] at hm47_si72
  obtain ⟨m48, vw48, hv48_ev, hm48_loc, hm48_glob, heff48, hm48_si80, hm48_ne, hk48⟩ :=
    seq_store_fresh_returned heff47 (ofString "si") w_si 96 80 (by rw [hm47_loc]; exact hm46_si) hsi_lo
      (by have : globN m47 "heap_ptr" = globN m46 "heap_ptr" := by unfold globN; rw [hm47_glob]
          omega) (by omega) _
      (eval_rfield_word m47 1 _ w_hda w_hdb (by rw [hm47_loc]; exact hm46_hd) (Or.inr rfl)) hk47
  have hvw48 : vw48 = w_hdb := by
    have h : m47.locals.lookup (ofString "hd") = some (.rStruct [.val (.word w_hda), .val (.word w_hdb)]) := by
      rw [hm47_loc]; exact hm46_hd
    simp [evalHOLExact, toExact, h] at hv48_ev; exact hv48_ev.symm
  rw [hvw48] at hm48_si80
  have hm48_si : m48.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    rw [hm48_loc, hm47_loc]; exact hm46_si
  rw [evaluateHOLFiniteState_return] at hk48
  simp [evalHOLExact, toExact, hm48_si, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hk48
  obtain ⟨hrv_eq, hm48_post⟩ := hk48
  have hpost_mem : post.memory = m48.memory := by
    rw [hpost_onpr, hpost_owit, hpost_si, hpost_np, hpost_nlen, hpost_opl, hpost_ovh, hpost_orq,
        hpost_pl, hpost_nvh, hpost_rq, hpost_wpw, hpost_wlenw, hpost_i3, hpost_w0, hpost_w1, hpost_w2,
        hpost_st0, hpost_cd, hpost_hd, ← hm48_post]
    rfl
  have hpost_glob : post.globals = cp_hd.globals := by
    rw [hpost_onpr, hpost_owit, hpost_si, hpost_np, hpost_nlen, hpost_opl, hpost_ovh, hpost_orq,
        hpost_pl, hpost_nvh, hpost_rq, hpost_wpw, hpost_wlenw, hpost_i3, hpost_w0, hpost_w1, hpost_w2,
        hpost_st0, hpost_cd, hpost_hd, ← hm48_post]
    change m48.globals = cp_hd.globals
    rw [hm48_glob, hm47_glob]; rfl
  have hpost_hp : globN post "heap_ptr" = globN cp_hd "heap_ptr" := by unfold globN; rw [hpost_glob]
  have hpost_memW : ∀ a, memW post a = memW m48 a := fun a => by unfold memW; rw [hpost_mem]
  have hm45_46_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_cd "heap_ptr" → memW m46 a = memW m45 a :=
    fun a hal hlo hhi => by
      change memW cp_hd a = memW m45 a
      have hr := dhiOffsRegions_eq_of_worldEff heff45
      have hstep : WorldEff m45 cp_hd (dhiOffsRegions m45) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact (WorldEff.refl m45 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff45.arena heff45.code).trans_noBuf
          ((WorldEff.refl m45 _ _ _ heff45.arena heff45.code).locals_clock fc_hd (m45.clock - 1) |>.trans_noBuf
            heff_step_hd (by intro _ h; cases h) dhi_no_gb)
          (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff45 hstep hal hlo (by rw [hm45_hp]; exact hhi)
  have hm42_43_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_st0 "heap_ptr" → memW m43 a = memW m42 a :=
    fun a hal hlo hhi => by
      change memW cp_cd a = memW m42 a
      have hr := dhiOffsRegions_eq_of_worldEff heff42
      have hstep : WorldEff m42 cp_cd (dhiOffsRegions m42) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact ((WorldEff.refl m42 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff42.arena heff42.code).locals_clock
          fc_cd (m42.clock - 1)).trans_noBuf heff_step_cd (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff42 hstep hal hlo (by rw [hm42_hp]; exact hhi)
  have hm39_40_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN m39 "heap_ptr" → memW m40 a = memW m39 a :=
    fun a hal hlo hhi => by
      change memW cp_st0 a = memW m39 a
      have hr := dhiOffsRegions_eq_of_worldEff heff39
      have hstep : WorldEff m39 cp_st0 (dhiOffsRegions m39) ([] : List (String × Nat)) dhiGw := by
        rw [hr]
        exact ((WorldEff.refl m39 (dhiOffsRegions entry) ([] : List (String × Nat)) dhiGw heff39.arena heff39.code).locals_clock
          fc_st0 (m39.clock - 1)).trans_noBuf heff_step_st0 (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff39 hstep hal hlo hhi
  have hm30_39_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_rq "heap_ptr" → memW m39 a = memW m30 a :=
    fun a hal hlo hhi =>
      worldEff_dhi_keeps_heap_memW_ok hOK_entry heff30 hm30_39_eff hal hlo (by rw [hm30_hp]; exact hhi)
  have hm28_29_keep : ∀ a, a % 8 = 0 → globN entry "heap_ptr" ≤ a → a + 8 ≤ globN cp_pl "heap_ptr" → memW m29 a = memW m28 a :=
    fun a hal hlo hhi => by
      change memW cp_rq a = memW m28 a
      have hstep : WorldEff m28 cp_rq (dhiOffsRegions m28) ([] : List (String × Nat)) dhiGw :=
        ((WorldEff.refl m28 (dhiOffsRegions m28) ([] : List (String × Nat)) dhiGw heff28.arena heff28.code).locals_clock
          fc_rq (m28.clock - 1)).trans_noBuf heff_step_rq (by intro _ h; cases h) dhi_no_gb
      exact worldEff_dhi_keeps_heap_memW_ok hOK_entry heff28 hstep hal hlo (by rw [hm28_hp]; exact hhi)
  -- Exact memW post at si + {0, 32, 40, 48, 56, 64, 72, 80}:
  have hsi_lt_cp_pl : w_si.toNat + 96 ≤ globN cp_pl "heap_ptr" := by omega
  have hcp_pl_le_rq : globN cp_pl "heap_ptr" ≤ globN cp_rq "heap_ptr" := by omega
  have hcp_rq_le_st0 : globN cp_rq "heap_ptr" ≤ globN cp_st0 "heap_ptr" := by
    change globN cp_rq "heap_ptr" ≤ globN m40 "heap_ptr"; exact hm40_hp_ge
  have hcp_st0_le_cd : globN cp_st0 "heap_ptr" ≤ globN cp_cd "heap_ptr" := by
    change globN cp_st0 "heap_ptr" ≤ globN m43 "heap_ptr"; exact hm43_hp_ge
  have hcp_cd_le_hd : globN cp_cd "heap_ptr" ≤ globN cp_hd "heap_ptr" := by
    change globN cp_cd "heap_ptr" ≤ globN m46 "heap_ptr"; exact hm46_hp_ge
  have hpost_si80 : memW post (w_si.toNat + 80) = w_hdb.toNat := by
    rw [hpost_memW, hm48_si80]
  have hpost_si72 : memW post (w_si.toNat + 72) = w_hda.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_si72]
  have hpost_si64 : memW post (w_si.toNat + 64) = w_cdb.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_si64]
  have hpost_si56 : memW post (w_si.toNat + 56) = w_cda.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_si56]
  have hpost_si48 : memW post (w_si.toNat + 48) = w_st0b.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_si48]
  have hpost_si40 : memW post (w_si.toNat + 40) = w_st0a.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_si40]
  have hpost_si32 : memW post (w_si.toNat + 32) = w_rq.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ (by omega) (by omega) (by omega), hm30_39_keep _ (by omega) (by omega) (by omega), hm30_si32]
  have hpost_si0 : memW post w_si.toNat = w_pl.toNat := by
    have hm25_24 : ∀ a, memW m25 a = memW m24 a := fun a => by unfold memW; rw [hm25_mem]
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ (by omega) (by omega) (by omega), hm30_39_keep _ (by omega) (by omega) (by omega), hm30_ne _ (by omega) (by omega),
        hm28_29_keep _ (by omega) (by omega) (by omega), hm28_ne _ (by omega) (by omega), hm27_ne _ (by omega) (by omega),
        hm26_ne _ (by omega) (by omega), hm25_24, hm24_si0]
  have hpost_si16 : memW post (w_si.toNat + 16) = w_nvh.toNat := by
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ (by omega) (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ (by omega) (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ (by omega) (by omega) (by omega), hm30_39_keep _ (by omega) (by omega) (by omega), hm30_ne _ (by omega) (by omega),
        hm28_29_keep _ (by omega) (by omega) (by omega), hm28_ne _ (by omega) (by omega), hm27_si16]
  -- Preservation of all words in [w_si + 96, globN cp_rq "heap_ptr") from m30 to post:
  have hkeep_after_rq : ∀ a, a % 8 = 0 → w_si.toNat + 96 ≤ a → a + 8 ≤ globN cp_rq "heap_ptr" → memW post a = memW m30 a := by
    intro a hal ha_lo ha_hi
    rw [hpost_memW, hm48_ne _ (by omega) (by omega), hm47_ne _ (by omega) (by omega),
        hm45_46_keep _ hal (by omega) (by omega), hm45_ne _ (by omega) (by omega), hm44_ne _ (by omega) (by omega),
        hm42_43_keep _ hal (by omega) (by omega), hm42_ne _ (by omega) (by omega), hm41_ne _ (by omega) (by omega),
        hm39_40_keep _ hal (by omega) (by omega), hm30_39_keep _ hal (by omega) ha_hi]
  -- Preservation of all words in [w_si + 96, globN cp_pl "heap_ptr") from cp_pl to post:
  have hkeep_after_pl : ∀ a, a % 8 = 0 → w_si.toNat + 96 ≤ a → a + 8 ≤ globN cp_pl "heap_ptr" → memW post a = memW cp_pl a := by
    intro a hal ha_lo ha_hi
    have hm25_24 : ∀ x, memW m25 x = memW m24 x := fun x => by unfold memW; rw [hm25_mem]
    rw [hkeep_after_rq a hal ha_lo (by omega), hm30_ne _ (by omega) (by omega),
        hm28_29_keep _ hal (by omega) ha_hi, hm28_ne _ (by omega) (by omega), hm27_ne _ (by omega) (by omega),
        hm26_ne _ (by omega) (by omega), hm25_24, hm24_ne _ (by omega) (by omega)]
    rfl
  have hwok_si96 : WordsOK post (w_si.toNat, 96) :=
    wordsOK_preserved_of_worldEff heff_entry_post hsi_al (by omega) hsi_sb (by have := heff_entry_post.arena.2.2.1; omega)
  have hwok_si40 : WordsOK post (w_si.toNat, 40) :=
    ⟨hsi_al, by omega, fun k hk => hwok_si96.2.2 k (by omega)⟩
  have hwok_pl_post : WordsOK post (w_pl.toNat, 136) :=
    wordsOK_preserved_of_worldEff heff_entry_post hpl_al (by omega) hpl_sb (by have := heff_entry_post.arena.2.2.1; omega)
  have hwok_rq_post : WordsOK post (w_rq.toNat, 80) :=
    wordsOK_preserved_of_worldEff heff_entry_post hrq_al (by omega) hrq_sb (by have := heff_entry_post.arena.2.2.1; omega)
  have hpl_24_eq : memW post (w_pl.toNat + 24) = memW cp_pl (w_pl.toNat + 24) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  have hpl_32_eq : memW post (w_pl.toNat + 32) = memW cp_pl (w_pl.toNat + 32) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  have hpl_40_eq : memW post (w_pl.toNat + 40) = memW cp_pl (w_pl.toNat + 40) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  have hpl_56_eq : memW post (w_pl.toNat + 56) = memW cp_pl (w_pl.toNat + 56) :=
    hkeep_after_pl _ (by omega) (by omega) (by omega)
  have hpl_at_post : PayloadAt post w_pl.toNat := by
    refine ⟨hwok_pl_post, by rw [hpl_24_eq]; exact hpl_at_cp.2.1, by rw [hpl_40_eq]; exact hpl_at_cp.2.2.1, ?_⟩
    intro j hj
    rw [hpl_40_eq] at hj
    rw [hpl_32_eq]
    rcases htx_cases_cp with ⟨hc0, _⟩ | ⟨_, _, _, htx_hi_cp, hpl_tx_lo⟩
    · omega
    · rw [hkeep_after_pl _ (by omega) (by omega) (by omega)]
      exact hpl_at_cp.2.2.2 j hj
  have hrq_at_post : RequestsAt post w_rq.toNat := by
    refine ⟨hwok_rq_post, ?_⟩
    intro j hj
    rw [hkeep_after_rq _ (by omega) (by omega) (by omega), hm30_ne _ (by omega) (by omega)]
    exact hrq_at_cp.2 j hj
  have hwok_tx_post : WordsOK post (memW post (w_pl.toNat + 32), 16 * memW post (w_pl.toNat + 40)) := by
    rw [hpl_32_eq, hpl_40_eq]
    rcases htx_cases_cp with ⟨hc0, ha0⟩ | ⟨_, htx_sb, _, htx_hi_cp, _⟩
    · rw [hc0, ha0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post htxp_al_cp (by omega) htx_sb
        (by have := heff_entry_post.arena.2.2.1; omega)
  have hwok_st0_post : WordsOK post (w_st0a.toNat, 16 * w_st0b.toNat) := by
    rcases hst0_cases with ⟨hc0, ha0, _⟩ | ⟨_, hsb, _, hhi, _, _⟩
    · rw [hc0, ha0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post hst0a_al (by omega) hsb
        (by have := heff_entry_post.arena.2.2.1; omega)
  have hwok_cd_post : WordsOK post (w_cda.toNat, 16 * w_cdb.toNat) := by
    rcases hcd_cases with ⟨hc0, ha0, _⟩ | ⟨_, hsb, _, hhi, _, _⟩
    · rw [hc0, ha0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post hcda_al (by omega) hsb
        (by have := heff_entry_post.arena.2.2.1; omega)
  have hwok_hd_post : WordsOK post (w_hda.toNat, 16 * w_hdb.toNat) := by
    rcases hhd_cases with ⟨hc0, ha0, _⟩ | ⟨_, hsb, _, hhi, _, _⟩
    · rw [hc0, ha0]; exact ⟨rfl, rfl, fun k hk => by simp at hk⟩
    · exact wordsOK_preserved_of_worldEff heff_entry_post hhda_al (by omega) hsb
        (by have := heff_entry_post.arena.2.2.1; omega)
  have hsi_ins : Inside (w_si.toNat, 96) (globN entry "heap_ptr") (globN post "heap_ptr") :=
    ⟨hsi_lo, by omega⟩
  have hpl_ins : Inside (memW post w_si.toNat, 136) (globN entry "heap_ptr") (globN post "heap_ptr") := by
    rw [hpost_si0]; exact ⟨by omega, by omega⟩
  have hrq_ins : Inside (memW post (w_si.toNat + 32), 80) (globN entry "heap_ptr") (globN post "heap_ptr") := by
    rw [hpost_si32]; exact ⟨by omega, by omega⟩
  refine ⟨heff_s_post, heff_entry_post, w_si, hrv_eq.symm, ?_, hsi_ins, hpl_ins, hrq_ins, hwok_si40,
    by rw [hpost_si0, hpl_40_eq]; omega,
    by rw [hpost_si0]; exact hpl_at_post,
    by rw [hpost_si32]; exact hrq_at_post,
    by rw [hpost_si16]; exact hnvh_lt32,
    by rw [hpost_si0, hpl_56_eq]; exact hnwd_lt32_cp⟩
  intro c hc
  simp only [runAttemptCells, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hsi_al, Or.inr hsi_ins, hwok_si96⟩
  · rw [hpost_si0]; exact ⟨hpl_al, Or.inr ⟨by omega, by omega⟩, hwok_pl_post⟩
  · rw [hpost_si32]; exact ⟨hrq_al, Or.inr ⟨by omega, by omega⟩, hwok_rq_post⟩
  · rw [hpost_si0]
    refine ⟨by rw [hpl_32_eq]; exact htxp_al_cp, ?_, hwok_tx_post⟩
    rw [hpl_32_eq, hpl_40_eq]
    rcases htx_cases_cp with ⟨hc0, ha0⟩ | ⟨_, _, htx_lo, htx_hi, _⟩
    · exact Or.inl ⟨ha0, by simp [hc0]⟩
    · exact Or.inr ⟨by change globN entry "heap_ptr" ≤ _; omega, by omega⟩
  · rw [hpost_si40, hpost_si48]
    refine ⟨hst0a_al, ?_, hwok_st0_post⟩
    rcases hst0_cases with ⟨hc0, ha0, _⟩ | ⟨_, _, hlo, hhi, _, _⟩
    · exact Or.inl ⟨ha0, by simp [hc0]⟩
    · exact Or.inr ⟨by change globN m39 "heap_ptr" ≤ _ at hlo; omega, by omega⟩
  · rw [hpost_si56, hpost_si64]
    refine ⟨hcda_al, ?_, hwok_cd_post⟩
    rcases hcd_cases with ⟨hc0, ha0, _⟩ | ⟨_, _, hlo, hhi, _, _⟩
    · exact Or.inl ⟨ha0, by simp [hc0]⟩
    · exact Or.inr ⟨by change globN m42 "heap_ptr" ≤ _ at hlo; omega, by omega⟩
  · rw [hpost_si72, hpost_si80]
    refine ⟨hhda_al, ?_, hwok_hd_post⟩
    rcases hhd_cases with ⟨hc0, ha0, _⟩ | ⟨_, _, hlo, hhi, _, _⟩
    · exact Or.inl ⟨ha0, by simp [hc0]⟩
    · exact Or.inr ⟨by change globN m45 "heap_ptr" ≤ _ at hlo; omega, by omega⟩

/-! ### `decode_host_input` Return Postcondition & `WorldKeeps` Theorems -/

theorem decode_host_input_body_returns {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {rv : ValueHOL 64}
    (hWOK : WorldOK s)
    (heff : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw)
    (hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned rv), post)) :
    WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw ∧
    ∃ (w_si : BitVec 64),
      rv = .val (.word w_si) ∧
      (∀ i ∈ runAttemptCells post w_si.toNat,
        i.1 % 8 = 0 ∧
        ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i (globN s "heap_ptr") (globN post "heap_ptr")) ∧
        WordsOK post i) ∧
      Inside (w_si.toNat, 96) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      Inside (memW post w_si.toNat, 136) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      Inside (memW post (w_si.toNat + 32), 80) (globN s "heap_ptr") (globN post "heap_ptr") ∧
      WordsOK post (w_si.toNat, 40) ∧
      memW post (memW post w_si.toNat + 40) < 2 ^ 63 ∧
      PayloadAt post (memW post w_si.toNat) ∧
      RequestsAt post (memW post (w_si.toNat + 32)) ∧
      memW post (w_si.toNat + 16) < 2 ^ 32 ∧
      memW post (memW post w_si.toNat + 56) < 2 ^ 32 := by
  have hOK := dhiOffsOK_of_worldOK hWOK
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hcr : ContOrRes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).1 := by
    rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rv, rfl⟩)))
  have heff_s_post : WorldEff s post (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := by
    have h := worldEff_decode_host_input_body hWOK heff hnt hcr
    rwa [hrun] at h
  dsimp only [Guest.Software.guestFn_decode_host_input, sourceFnBody, sourceFunctionEntry,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  obtain ⟨m1, hm1_pre, hk1⟩ := seq_returned_split (call0_noret_dhi s _ _) hrun
  have heff1 : WorldEff s m1 (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_of_none_dhi hm1_pre (fun hnt_a hcr_a =>
      worldEff_call0_eff heff _ _ _ _ _ lookup_precheck_host_ssz_header
        (fun callee _ _ _ hnt_c hres_c => worldEff_precheck_host_ssz_header_body hWOK (heff.locals_clock callee _) hnt_c (contOrRes_of_resumes_dhi hres_c))
        hnt_a hcr_a)
  obtain ⟨vals_inp, fc_inp, rv_inp, cp_inp, post_inp, _, _, _, hc_inp, _, _, hk2, hpost_inp⟩ :=
    decCall_returned_split heff1.code lookup_input_blob hk1
  obtain ⟨heff_cp_inp, wp_inp, wlen_inp, rfl, _, _, _⟩ :=
    input_blob_body_returns (heff1.locals_clock fc_inp (m1.clock - 1)) hc_inp
  let m2 := setVarHOLFinite (ofString "inp") (.rStruct [.val (.word wp_inp), .val (.word wlen_inp)]) { cp_inp with locals := m1.locals }
  have heff2 : WorldEff s m2 (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw := heff_cp_inp.locals_clock _ _
  obtain ⟨vals_dsi, fc_dsi, cp_dsi, hargs_dsi, hl_dsi, _, hc_dsi, _, hpost_dsi⟩ :=
    tailCall_returned_split heff2.code lookup_decode_stateless_input hk2
  obtain ⟨wp_d, wlen_d, _, hfc_d_p, hfc_d_len⟩ :=
    lookupCode_two_words_any_dhi (by decide) lookup_decode_stateless_input hl_dsi
  obtain ⟨heff_s_cp, heff_step_dsi, w_si, rfl, hcells_cp, hsi_ins, hpl_ins, hrq_ins, hwok_si40, hntx_lt, hpl_at, hrq_at, hnvh_dsi, hnwd_dsi⟩ :=
    decode_stateless_input_body_returns hOK (heff2.locals_clock fc_dsi (m2.clock - 1)) hfc_d_p hfc_d_len hc_dsi
  have hpost_mem : post.memory = cp_dsi.memory := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_glob : post.globals = cp_dsi.globals := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_ma : post.memaddrs = cp_dsi.memaddrs := by
    rw [hpost_inp, hpost_dsi]; rfl
  have hpost_hp : globN post "heap_ptr" = globN cp_dsi "heap_ptr" := by unfold globN; rw [hpost_glob]
  have hpost_memW : ∀ a, memW post a = memW cp_dsi a := fun a => by unfold memW; rw [hpost_mem]
  have hs_le_m2 : globN s "heap_ptr" ≤ globN m2 "heap_ptr" := heff2.hp_lo
  have hwordAt_eq : ∀ a, WordAt post a ↔ WordAt cp_dsi a := fun a => by
    unfold WordAt; rw [hpost_ma, hpost_mem]
  have hwok_eq : ∀ iv, WordsOK post iv ↔ WordsOK cp_dsi iv := fun iv => by
    simp only [WordsOK, hwordAt_eq]
  have hcells_eq : runAttemptCells post w_si.toNat = runAttemptCells cp_dsi w_si.toNat := by
    simp only [runAttemptCells, hpost_memW]
  refine ⟨heff_s_post, w_si, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    rw [hcells_eq] at hc
    obtain ⟨hal, hins, hwok⟩ := hcells_cp c hc
    refine ⟨hal, ?_, (hwok_eq c).2 hwok⟩
    rcases hins with h00 | ⟨hlo, hhi⟩
    · exact Or.inl h00
    · change globN m2 "heap_ptr" ≤ c.1 at hlo
      rw [hpost_hp]
      exact Or.inr ⟨by omega, hhi⟩
  · obtain ⟨hlo, hhi⟩ := hsi_ins
    change globN m2 "heap_ptr" ≤ w_si.toNat at hlo
    rw [hpost_hp]; exact ⟨by omega, hhi⟩
  · obtain ⟨hlo, hhi⟩ := hpl_ins
    change globN m2 "heap_ptr" ≤ _ at hlo
    rw [hpost_memW, hpost_hp]; exact ⟨by omega, hhi⟩
  · obtain ⟨hlo, hhi⟩ := hrq_ins
    change globN m2 "heap_ptr" ≤ _ at hlo
    rw [hpost_memW, hpost_hp]; exact ⟨by omega, hhi⟩
  · exact (hwok_eq _).2 hwok_si40
  · simpa only [hpost_memW] using hntx_lt
  · rw [hpost_memW]
    exact ⟨(hwok_eq _).2 hpl_at.1,
           by simpa only [hpost_memW] using hpl_at.2.1,
           by simpa only [hpost_memW] using hpl_at.2.2.1,
           fun j hj => by
             rw [hpost_memW] at hj
             simpa only [hpost_memW] using hpl_at.2.2.2 j hj⟩
  · rw [hpost_memW]
    exact ⟨(hwok_eq _).2 hrq_at.1, fun j hj => by simpa only [hpost_memW] using hrq_at.2 j hj⟩
  · simpa only [hpost_memW] using hnvh_dsi
  · simpa only [hpost_memW] using hnwd_dsi

theorem wk_decode_host_input_sound :
    WorldKeeps WorldOK
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetInputSound (ofString "decode_host_input") := by
  refine ⟨_, _, _, lookup_decode_host_input, ?_⟩
  intro F s hc hWOK hl hnt hres
  have heff0 : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc
  have heff : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
      (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_decode_host_input_body hWOK heff0 hnt (contOrRes_of_resumes_dhi hres)
  refine R16Shards.WorldEff.to_worldStep_Q (R := dhiOffsRegions)
    hWOK (by intro _ h; cases h) (by decide) heff ?_
  intro S Nd hWT hDisjR _ _ hne_eq hfp_eq v hrv
  have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned v), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2) :=
    Prod.ext hrv rfl
  obtain ⟨heff_post, w_si, rfl, hcells, hsi_ins, hpl_ins, hrq_ins, hwok_si40, hntx_lt, hpl_at, hrq_at, _, _⟩ :=
    decode_host_input_body_returns hWOK heff0 hrun
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
  have hinp_mem : ∀ c ∈ inputCells post w_si.toNat,
      c.1 % 8 = 0 ∧ ((c.1 = 0 ∧ c.2 = 0) ∨ Inside c (globN s "heap_ptr") (globN post "heap_ptr")) ∧ WordsOK post c := by
    intro c hc_in
    simp only [inputCells, List.mem_cons, List.mem_nil_iff, or_false] at hc_in
    rcases hc_in with rfl | rfl | rfl | rfl
    · have hc96 := hcells (w_si.toNat, 96) (by simp [runAttemptCells])
      have hhi96 : w_si.toNat + 96 ≤ globN post "heap_ptr" := hsi_ins.2
      exact ⟨hc96.1, Or.inr ⟨hsi_ins.1, by dsimp only; omega⟩, hwok_si40⟩
    · exact hcells (memW post w_si.toNat, 136) (by simp [runAttemptCells, post])
    · exact hcells (memW post (w_si.toNat + 32), 80) (by simp [runAttemptCells, post])
    · exact hcells (memW post (memW post w_si.toNat + 32), 16 * memW post (memW post w_si.toNat + 40))
        (by simp [runAttemptCells, post])
  have hdisj : IvlsDisj (inputCells post w_si.toNat) (worldOwned post S Nd) :=
    disj_worldOwned_of_zero_or_fresh_dhi hWOK.1 heff_post hWT hDisjR hne_eq hfp_eq
      (fun c hc_in => by
        rcases (hinp_mem c hc_in).2.1 with ⟨_, h0⟩ | hins
        · exact Or.inl h0
        · exact Or.inr hins)
  exact ⟨w_si, rfl, hinp_mem, hdisj, hntx_lt, hpl_at, hrq_at⟩

theorem wk_decode_host_input_strong_sound :
    WorldKeeps WorldOK
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetInputStrongSound (ofString "decode_host_input") := by
  refine ⟨_, _, _, lookup_decode_host_input, ?_⟩
  intro F s hc hWOK hl hnt hres
  have heff0 : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc
  have heff : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
      (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_decode_host_input_body hWOK heff0 hnt (contOrRes_of_resumes_dhi hres)
  refine R16Shards.WorldEff.to_worldStep_Q (R := dhiOffsRegions)
    hWOK (by intro _ h; cases h) (by decide) heff ?_
  intro S Nd hWT hDisjR _ _ hne_eq hfp_eq v hrv
  have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned v), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2) :=
    Prod.ext hrv rfl
  obtain ⟨heff_post, w_si, rfl, hcells, _, _, _, _, hntx_lt, hpl_at, hrq_at, hnvh, hnwd⟩ :=
    decode_host_input_body_returns hWOK heff0 hrun
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
  have hdisj : IvlsDisj (runAttemptCells post w_si.toNat) (worldOwned post S Nd) :=
    disj_worldOwned_of_zero_or_fresh_dhi hWOK.1 heff_post hWT hDisjR hne_eq hfp_eq
      (fun c hc_in => by
        rcases (hcells c hc_in).2.1 with ⟨_, h0⟩ | hins
        · exact Or.inl h0
        · exact Or.inr hins)
  exact ⟨w_si, rfl, hcells, hdisj, hntx_lt, hpl_at, hrq_at, hnvh, hnwd⟩

/-- Conditional bridge to exact `RetInput` whenever the decoded transaction list is non-empty
    (`0 < memW post (memW post w.toNat + 40)`). When `ntx = 0`, `ssz_split_var_list` returns `(0, 0)`
    without calling `alloc`, so the 4th cell `(0, 0)` of `inputCells` has `0 < sourceBase ≤ globN s "heap_ptr"`. -/
def RetInputIfNonempty : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post S' Nd' =>
    (∀ v (w : BitVec 64), r = some (.returned v) → v = .val (.word w) →
      0 < memW post (memW post w.toNat + 40)) →
    RetInput s r post S' Nd'

theorem wk_decode_host_input_of_nonempty :
    WorldKeeps WorldOK
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]),
       ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetInputIfNonempty (ofString "decode_host_input") := by
  refine ⟨_, _, _, lookup_decode_host_input, ?_⟩
  intro F s hc hWOK hl hnt hres
  have heff0 : WorldEff s s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    WorldEff.refl s (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw hWOK.1 hc
  have heff : WorldEff s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
      (dhiOffsRegions s) ([] : List (String × Nat)) dhiGw :=
    worldEff_decode_host_input_body hWOK heff0 hnt (contOrRes_of_resumes_dhi hres)
  refine R16Shards.WorldEff.to_worldStep_Q (R := dhiOffsRegions)
    hWOK (by intro _ h; cases h) (by decide) heff ?_
  intro S Nd hWT hDisjR _ _ hne_eq hfp_eq hne_tx v hrv
  have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input) =
      (some (.returned v), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2) :=
    Prod.ext hrv rfl
  obtain ⟨heff_post, w_si, rfl, hcells, hsi_ins, hpl_ins, hrq_ins, hwok_si40, hntx_lt, hpl_at, hrq_at, _, _⟩ :=
    decode_host_input_body_returns hWOK heff0 hrun
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_decode_host_input)).2
  have hpos_tx : 0 < memW post (memW post w_si.toNat + 40) := hne_tx _ w_si hrv rfl
  have hinp_mem : ∀ c ∈ inputCells post w_si.toNat,
      c.1 % 8 = 0 ∧ Inside c (globN s "heap_ptr") (globN post "heap_ptr") ∧ WordsOK post c := by
    intro c hc_in
    simp only [inputCells, List.mem_cons, List.mem_nil_iff, or_false] at hc_in
    rcases hc_in with rfl | rfl | rfl | rfl
    · have hc96 := hcells (w_si.toNat, 96) (by simp [runAttemptCells])
      have hhi96 : w_si.toNat + 96 ≤ globN post "heap_ptr" := hsi_ins.2
      exact ⟨hc96.1, ⟨hsi_ins.1, by dsimp only; omega⟩, hwok_si40⟩
    · exact ⟨(hcells (memW post w_si.toNat, 136) (by simp [runAttemptCells, post])).1, hpl_ins, hpl_at.1⟩
    · exact ⟨(hcells (memW post (w_si.toNat + 32), 80) (by simp [runAttemptCells, post])).1, hrq_ins, hrq_at.1⟩
    · have h4 := hcells (memW post (memW post w_si.toNat + 32), 16 * memW post (memW post w_si.toNat + 40))
        (by simp [runAttemptCells, post])
      rcases h4.2.1 with ⟨_, hsz0⟩ | hins
      · dsimp only at hsz0; omega
      · exact ⟨h4.1, hins, h4.2.2⟩
  have hdisj : IvlsDisj (inputCells post w_si.toNat) (worldOwned post S Nd) :=
    disj_worldOwned_of_zero_or_fresh_dhi hWOK.1 heff_post hWT hDisjR hne_eq hfp_eq
      (fun c hc_in => Or.inr (hinp_mem c hc_in).2.1)
  exact ⟨w_si, rfl, hinp_mem, hdisj, hntx_lt, hpl_at, hrq_at⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
