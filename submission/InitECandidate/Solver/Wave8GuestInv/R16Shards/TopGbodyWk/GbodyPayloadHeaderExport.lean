import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyPayloadHeader
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockRlpLength
import InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover.HeaderHash

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R13PayloadStateInit
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover

private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

private theorem heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

private theorem ivlUnhit_of_heapByteEff_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    {h len : Nat} (hh_ins : Inside (h, len) sourceBase (globN s0 "heap_ptr"))
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1) :
    IvlUnhit s0 st (h, len) := by
  intro a ha8 hhit
  obtain ⟨ha_lo, ha_hi⟩ := hhit
  dsimp only at ha_lo ha_hi
  obtain ⟨hh_lo, hh_hi⟩ := hh_ins
  dsimp only at hh_lo hh_hi
  by_contra hne
  have hsep : heapLimit = scratchStart := rfl
  have hhp8 : globN s0 "heap_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.1
  have hfp8 : globN s0 "frame_mem_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.1
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hfp_lo : scratchStart ≤ globN s0 "frame_mem_ptr" := hAR0.2.2.2.1
  rcases heff.cell_frame a hne with ⟨i, hi, hipos, hc1, hc2⟩ | ⟨_, g1, _⟩ | ⟨_, f1, _⟩
  · have := hRl_ge i hi hipos
    omega
  · unfold freeGap at g1
    dsimp only at g1
    omega
  · unfold heapFree at f1
    dsimp only at f1
    omega

theorem wk_block_rlp_length_hdr :
    WorldKeeps (fun s => WorldOK s ∧ HeaderAtStrong s (locN s "hdr")) (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "block_rlp_length") := by
  refine ⟨_, _, _, lookup_block_rlp_length, fun {F} s hcode ⟨hW, hHdr⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨hw, w_pl, _, hhdr_lk, _⟩ :=
    R13Shards.Keccak256.lookupCode_two_words (by decide) lookup_block_rlp_length hl_args
  have hhdr_locN : locN s "hdr" = hw.toNat := by simp [locN, hhdr_lk]
  have hH : HeaderAtStrong s hw.toNat := by rwa [hhdr_locN] at hHdr
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).2
      (([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun _ => []) (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  have hb : sourceFnBody Guest.Software.guestFn_block_rlp_length =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "he") (.comb [.one, .one]) (ofString "encode_header")
          [.var .local (ofString "hdr")]
          (.seq
            (.call (some (none, none)) (ofString "heap_release")
              [.var .local (ofString "mark")])
            ph_blockRlpTail)) := rfl
  rw [hb] at hnt hres ⊢
  set Rall : List Ivl := ([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)
  obtain ⟨mark, s1, _, hmark_nat, _, _, hs1_loc, heff01_nil, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ ([] : List Ivl) ["heap_ptr"] hcode hAR hnt
  have heff01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  rw [heq1] at hres
  dsimp only at hres
  refine heapByteEff_of_eq_resVar heq1 ?_
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_hdr : s1.locals.lookup (ofString "hdr") = some (.val (.word hw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hhdr_lk,
      show ofString "mark" ≠ ofString "hdr" by decide]
  have hH_s1 : HeaderAtStrong s1 hw.toNat := by
    have hu : IvlUnhit s s1 (hw.toNat, 248) :=
      ivlUnhit_of_heapByteEff_below_hp hAR heff01_nil hH.2 (fun _ h => by cases h)
    exact headerAtStrong_of_ivlUnhit hAR.1 heff01.arena.1 heff01.hp_le
      (by have := hH.2.2; have := hAR.2.2.1; omega) hu hH
  obtain ⟨startw, totalw, s2, hs2_loc, heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_encode_header s1 "he" (.var .local (ofString "hdr")) hw _ Rall ["heap_ptr"]
      heff01.arena.1.code heff01.arena (by simp) hs1_hdr hH_s1 hnt1 hres
  refine heapByteEff_of_eq_resVar heq2 ?_
  have heff02 : HeapByteEff s s2 Rall ["heap_ptr"] := heff01.trans heff12
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "he" ≠ ofString "mark" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2
    (.call (some (none, none)) (ofString "heap_release")
      [.var .local (ofString "mark")]) with ⟨r3, s3⟩
  have hnt_c3 : r3 ≠ some .timeOut := by
    rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
  have h3 := eval_call_heap_release s2 (.var .local (ofString "mark")) mark
    Rall ["heap_ptr"] heff02.arena.1.code heff02 (by simp) hs2_mark
    (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc3]; exact hnt_c3)
  dsimp only at h3
  rw [hc3] at h3
  obtain ⟨rfl, _, _, _, heff03⟩ := h3
  refine heapByteEff_of_seq_none hc3 ?_
  have hlf4 := ph_frame_blockRlpTail s3 heff03.arena.1.code
  exact heff03.trans (HeapByteEff.of_locFrame heff03.arena hlf4 Rall ["heap_ptr"])

def PH_BL_POST : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_BH s ∧
    ∀ w_pl : BitVec 64, s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) →
      0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44

theorem ph_bl_post_guestInv {F : Type} {s : PanSemStateFiniteExact 64 F} :
    PH_BL_POST s → GuestInv s := by
  intro h; exact ph_bh_guestInv h.1

theorem ph_block_rlp_length_returned_bound {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w_hdr w_pl : BitVec 64) (rv : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hhdr : s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)))
    (hpl : s.locals.lookup (ofString "pl") = some (.val (.word w_pl)))
    (hH : HeaderAtStrong s w_hdr.toNat)
    (hpl_in : Inside (w_pl.toNat, 136) sourceBase (globN s "heap_ptr"))
    (hpl8 : w_pl.toNat % 8 = 0)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 =
      some (.returned rv)) :
    0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44 := by
  have hb : sourceFnBody Guest.Software.guestFn_block_rlp_length =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "he") (.comb [.one, .one]) (ofString "encode_header")
          [.var .local (ofString "hdr")]
          (.seq
            (.call (some (none, none)) (ofString "heap_release")
              [.var .local (ofString "mark")])
            ph_blockRlpTail)) := rfl
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 ≠
      some .timeOut := by rw [hret]; simp
  have hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_block_rlp_length)).1 :=
    Or.inl ⟨rv, hret⟩
  rw [hb] at hret hnt hres
  set Rall : List Ivl := ([] : List Ivl) ++ ([] : List (String × Nat)).map (bufferRegion s)
  obtain ⟨mark, s1, _, hmark_nat, _, _, hs1_loc, heff01_nil, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ ([] : List Ivl) ["heap_ptr"] hcode hAR hnt
  have heff01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  rw [heq1] at hret hres
  dsimp only at hret hres
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_hdr : s1.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hhdr,
      show ofString "mark" ≠ ofString "hdr" by decide]
  have hs1_pl : s1.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hpl,
      show ofString "mark" ≠ ofString "pl" by decide]
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hH_s1 : HeaderAtStrong s1 w_hdr.toNat := by
    have hu : IvlUnhit s s1 (w_hdr.toNat, 248) :=
      ivlUnhit_of_heapByteEff_below_hp hAR heff01_nil hH.2 (fun _ h => by cases h)
    exact headerAtStrong_of_ivlUnhit hAR.1 heff01.arena.1 heff01.hp_le
      (by have := hH.2.2; have := hAR.2.2.1; omega) hu hH
  obtain ⟨startw, totalw, s2, hs2_loc, heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_encode_header s1 "he" (.var .local (ofString "hdr")) w_hdr _ Rall ["heap_ptr"]
      heff01.arena.1.code heff01.arena (by simp) hs1_hdr hH_s1 hnt1 hres
  rw [heq2] at hret
  dsimp only at hret
  have heff02 : HeapByteEff s s2 Rall ["heap_ptr"] := heff01.trans heff12
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "he" ≠ ofString "mark" by decide]
  have hs2_pl : s2.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_pl,
      show ofString "he" ≠ ofString "pl" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2
    (.call (some (none, none)) (ofString "heap_release")
      [.var .local (ofString "mark")]) with ⟨r3, s3⟩
  have hnt_c3 : r3 ≠ some .timeOut := by
    rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
  have h3 := eval_call_heap_release s2 (.var .local (ofString "mark")) mark
    Rall ["heap_ptr"] heff02.arena.1.code heff02 (by simp) hs2_mark
    (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.1)
    (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc3]; exact hnt_c3)
  dsimp only at h3
  rw [hc3] at h3 hret
  obtain ⟨rfl, hs3_loc, _, _, heff03⟩ := h3
  dsimp only at hret hs3_loc heff03
  have hs3_pl : s3.locals.lookup (ofString "pl") = some (.val (.word w_pl)) := by
    rw [hs3_loc]; exact hs2_pl
  intro hn_pos
  have hu_pl : IvlUnhit s s3 (w_pl.toNat, 136) :=
    ivlUnhit_of_heapByteEff_below_hp hAR heff03 hpl_in (by intro _ h; simp [Rall] at h)
  have hpl_hi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hpl_in.2 hAR.2.2.1
  have hmem_eq : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 136 →
      memW s3 (w_pl + BitVec.ofNat 64 off).toNat = memW s (w_pl + BitVec.ofNat 64 off).toNat := by
    intro off hoff8 hoff_hi
    have hnat : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hnat]
    exact memW_eq_of_ivlUnhit hu_pl (by omega) (by omega) ⟨by omega, by omega⟩
  have hm48 := hmem_eq 48 (by omega) (by omega)
  have hm56 := hmem_eq 56 (by omega) (by omega)
  have htail := ph_blockRlpTail_returned_bound s3 w_pl rv heff03.arena.1.code heff03.arena.1 hs3_pl hret
    (by simpa only [hm56] using hn_pos)
  simpa only [hm48, hm56] using htail

theorem ph_block_rlp_length_resume :
    DecCallResumeOn PH_BH PH_BL_POST (ofString "bl") (ofString "block_rlp_length")
      [.var .local (ofString "h"), .var .local (ofString "pl")] := by
  intro F s values body callee ret rv post hcode hP hargs hl hret
  obtain ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    hd_ht, hd_hw, hd_tw, hd_hr, hd_hb, hlsi, hlpl, hlh, hltxr, hlwr, hlrh, hlbh,
    hpl_eq, h136⟩ := hP
  have heh : evalAt s (.var .local (ofString "h")) = some (.val (.word w_h)) := by
    simpa [evalAt, evalHOLExact] using hlh
  have hep : evalAt s (.var .local (ofString "pl")) = some (.val (.word w_pl)) := by
    simpa [evalAt, evalHOLExact] using hlpl
  have hpc := callee_param_two s (ofString "block_rlp_length") (ofString "hdr")
    (ofString "pl") .one .one _ _ (by rw [hcode]; exact lookup_block_rlp_length)
    _ _ _ _ values body callee ret heh hep hargs hl
  have hl0 : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "block_rlp_length") values =
      some (body, callee, ret) := by rwa [hcode] at hl
  have hbody : body = sourceFnBody Guest.Software.guestFn_block_rlp_length := by
    obtain ⟨p', r', hc⟩ := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hl0
    rw [lookup_block_rlp_length] at hc
    injection hc with hc1
    injection hc1 with _ hc2
    injection hc2 with hb _
    exact hb.symm
  subst body
  let entry := callEntryStateHOLFinite s callee
  have hIAe : InputAtWith entry S Nd w_si.toNat :=
    (inputAtWith_with_locals s callee (s.clock - 1) S Nd w_si.toNat).2 hIA
  have hBse : AllBlocksGood entry S Nd
      [(w_h.toNat, 248), (w_txr.toNat, 32), (w_wr.toNat, 32), (w_rh.toNat, 32), (w_bh.toNat, 32)] :=
    (allBlocksGood_with_locals s callee (s.clock - 1) S Nd _).2 hBs
  have hH : HeaderAtStrong entry w_h.toNat :=
    ⟨⟨(hBse _ (by simp)).2.2.2.1, h136⟩, (hBse _ (by simp)).2.2.1⟩
  have hWe : WorldOK entry := ⟨hIAe.1, S, (worldTyped_iff_with entry S).2 ⟨Nd, hIAe.2.1⟩⟩
  have hguard : WorldOK entry ∧ HeaderAtStrong entry (locN entry "hdr") := by
    refine ⟨hWe, ?_⟩
    simpa [entry, locN, callEntryStateHOLFinite, hpc.2.1] using hH
  have hws := FunSpec.at_lookup wk_block_rlp_length_hdr s hcode values _ callee ret hl hguard
    (by rw [hret]; simp)
  rw [hret] at hws
  dsimp only at hws
  have hstep := hws (Or.inl ⟨rv, rfl⟩)
  obtain ⟨S', Nd', hIAp, hBsp, hu_bs, hu_ic, _⟩ :=
    WorldStep_preserves_inputAndBlocks hIAe hBse hstep
      (by intro j hj; cases hj) (by intro j hj; cases hj)
      (by intro c hc j hj; cases hj) (by intro b hb j hj; cases hj)
  have hic := inputCells_eq_of_unhit hIAe hu_ic
  have hplmem : (w_pl.toNat, 136) ∈ inputCells entry w_si.toNat := by
    change (w_pl.toNat, 136) ∈ inputCells s w_si.toNat
    rw [hpl_eq]; simp [inputCells]
  have hplgood := hIAe.2.2.1 _ hplmem
  have hbound := ph_block_rlp_length_returned_bound entry w_h w_pl rv hIAe.1.1.code hIAe.1
    hpc.2.1 hpc.2.2 hH hplgood.1 hplgood.2.1 (by rw [hret])
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hpl_hi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hplgood.1.2 hIAe.1.2.2.1
  have hpl8 : w_pl.toNat % 8 = 0 := hplgood.2.1
  have hm : ∀ off : Nat, off % 8 = 0 → off + 8 ≤ 136 →
      memW post (w_pl + BitVec.ofNat 64 off).toNat =
        memW entry (w_pl + BitVec.ofNat 64 off).toNat := by
    intro off ho hf
    have hn : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [hn]
    exact memW_eq_of_ivlUnhit (hu_ic _ hplmem) (by omega) (by omega) ⟨by omega, by omega⟩
  have hh := hBse (w_h.toNat, 248) (by simp)
  have h136eq : memW post (w_h.toNat + 136) = memW entry (w_h.toNat + 136) :=
    memW_eq_of_ivlUnhit (hu_bs (w_h.toNat, 248) (by simp)) (by have := hh.1; omega)
      (by have := hh.2.2.1.2; have := hIAe.1.2.2.1; omega) ⟨by omega, by omega⟩
  constructor
  · refine ⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S', Nd',
      (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIAp,
      (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBsp,
      ?_, hd_ht, hd_hw, hd_tw, hd_hr, hd_hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change IvlsDisj (inputCells post w_si.toNat) _
      rw [hic.2.2]; exact hd_ic
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "si" by decide, hlsi]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "pl" by decide, hlpl]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "h" by decide, hlh]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "txr" by decide, hltxr]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "wr" by decide, hlwr]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "rh" by decide, hlrh]
    · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "bh" by decide, hlbh]
    · exact hpl_eq.trans hic.1.symm
    · change memW post (w_h.toNat + 136) ≤ 32
      rw [h136eq]; exact h136
  · intro wp hwp hn
    have hwp' : wp = w_pl := by
      simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "bl" ≠ ofString "pl" by decide, hlpl] using hwp.symm
    subst wp
    change 0 < (BitVec.ofNat 64 (memW post (w_pl + 56#64).toNat)).toInt at hn
    change memW post (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW post (w_pl + 56#64).toNat ≤ heapEnd + 44
    rw [hm 48 (by omega) (by omega), hm 56 (by omega) (by omega)]
    exact hbound (by simpa only [hm 56 (by omega) (by omega)] using hn)

theorem ph_block_rlp_length_entry :
    CallEntryOn PH_BH GuestInv (ofString "block_rlp_length")
      [.var .local (ofString "h"), .var .local (ofString "pl")] :=
  callEntryOn_of_imp localsFree_guestInv (fun _ h => ph_bh_guestInv h) _ _

theorem ph_bl_check_post :
    Hoare PH_BL_POST
      (.ite (.cmp .lower (.const 8388608#64) (.var .local (ofString "bl")))
        (.raise (ofString "BlockErr") (.const 7#64)) .skip)
      (fun r t => r = none → PH_BL_POST t) :=
  Hoare.ite_raise_skip _ _ _

theorem ph_payload_word_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {w_si w_pl : BitVec 64}
    (hIA : InputAtWith s S Nd w_si.toNat)
    (hpl : w_pl.toNat = memW s w_si.toNat)
    (hu : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s post c)
    (off : Nat) (ho : off % 8 = 0) (hf : off + 8 ≤ 136) :
    memW post (w_pl + BitVec.ofNat 64 off).toNat =
      memW s (w_pl + BitVec.ofNat 64 off).toNat := by
  have hc : (w_pl.toNat, 136) ∈ inputCells s w_si.toNat := by
    rw [hpl]; simp [inputCells]
  have hg := hIA.2.2.1 _ hc
  have hhi : w_pl.toNat + 136 ≤ heapLimit := Nat.le_trans hg.1.2 hIA.1.2.2.1
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hn : (w_pl + BitVec.ofNat 64 off).toNat = w_pl.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [hn]
  exact memW_eq_of_ivlUnhit (hu _ hc) (by have := hg.2.1; omega)
    (by omega) ⟨by omega, by omega⟩

theorem ph_withdrawal_bounds_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {w_si w_pl : BitVec 64}
    (hIA : InputAtWith s S Nd w_si.toNat)
    (hpl : w_pl.toNat = memW s w_si.toNat)
    (hu : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s post c)
    (hb : 0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
        44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44) :
    0 < (BitVec.ofNat 64 (memW post (w_pl + 56#64).toNat)).toInt →
      memW post (w_pl + 48#64).toNat < heapEnd ∧
        44 * memW post (w_pl + 56#64).toNat ≤ heapEnd + 44 := by
  rw [ph_payload_word_unhit hIA hpl hu 48 (by omega) (by omega),
    ph_payload_word_unhit hIA hpl hu 56 (by omega) (by omega)]
  exact hb

theorem ph_withdrawal_active_lt {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_i w_nwd : BitVec 64}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hn : s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)))
    (hc : CondTrue (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nwd"))) s) :
    w_i.toInt < w_nwd.toInt := by
  obtain ⟨w, he, hw⟩ := hc
  have ha : LoopActive (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nwd"))) s :=
    ⟨w, by rwa [evalHOLFinite_eq_toExact], hw⟩
  obtain ⟨wi, wn, hli, hln, hlt⟩ := loopActive_cmp_less_locals ha
  rw [hi] at hli
  rw [hn] at hln
  cases hli
  cases hln
  exact hlt

def PH_WR_POST_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PH_WR_POST s ∧
    ∀ w_pl : BitVec 64, s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) →
      0 < (BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat)).toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧
      44 * memW s (w_pl + 56#64).toNat ≤ heapEnd + 44

def PH_NWD_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd : BitVec 64, ∃ S Nd : List Nat,
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_WDS0_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_LOOP_B : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds w_i : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    0 ≤ w_i.toInt ∧
    (0 < w_i.toNat → 44 * (w_i.toNat - 1) < heapEnd) ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

def PH_LOOP_EB : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_pl w_wr w_nwd w_wds w_i e0 e1 : BitVec 64, ∃ S Nd : List Nat,
    let alloc_sz := (w_nwd * 16#64 + 16#64).toNat
    InputAtWith s S Nd w_si.toNat ∧
    AllBlocksGood s S Nd [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    IvlsDisj (inputCells s w_si.toNat) [(w_wr.toNat, 32), (w_wds.toNat, alloc_sz)] ∧
    Disj (w_wr.toNat, 32) (w_wds.toNat, alloc_sz) ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wr") = some (.val (.word w_wr)) ∧
    s.locals.lookup (ofString "nwd") = some (.val (.word w_nwd)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    s.locals.lookup (ofString "e") = some (.rStruct [.val (.word e0), .val (.word e1)]) ∧
    s.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    0 ≤ w_i.toInt ∧
    w_i.toInt < w_nwd.toInt ∧
    44 * w_i.toNat < heapEnd ∧
    (0 < w_nwd.toInt →
      memW s (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44)

theorem ph_loop_b_loop {F : Type} {s : PanSemStateFiniteExact 64 F} :
    PH_LOOP_B s → PH_LOOP s := by
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, _⟩
  exact ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib⟩

theorem ph_loop_b_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) :
    PH_LOOP_B s → PH_LOOP_B (decClockHOLFinite s) := by
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩
  exact ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd,
    (inputAtWith_with_locals s s.locals (s.clock - 1) S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s s.locals (s.clock - 1) S Nd _).2 hBs,
    hd_ic, hd, hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩

theorem ph_loop_b_localsOnly :
    LocalsOnly ["si", "pl", "wr", "nwd", "i"] PH_LOOP_B := by
  intro F s locals k hl
  rintro ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hib, hnwd⟩
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd,
    (inputAtWith_with_locals s locals k S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s locals k S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, hi0, hib, hnwd⟩
  · simpa [hl "si" (by simp)] using hlsi
  · simpa [hl "pl" (by simp)] using hlpl
  · simpa [hl "wr" (by simp)] using hlwr
  · simpa [hl "nwd" (by simp)] using hlnwd
  · simpa [hl "i" (by simp)] using hli

theorem ph_build_mpt_txr_b
    (wmpt : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed")) :
    Hoare PH_BL_POST
      (.call (some (none, none)) (ofString "build_mpt_indexed")
        [.load .one (.op .add [.var .local (ofString "pl"), .const 32#64]),
         .load .one (.op .add [.var .local (ofString "pl"), .const 40#64]),
         .var .local (ofString "txr")])
      (fun r t => r = none → PH_WR_POST_B t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  refine ⟨(ph_build_mpt_txr wmpt).run state hcode hP.1 (by rw [hr]; simp) hr, ?_⟩
  set e1 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 32#64])
  set e2 : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "pl"), .const 40#64])
  set e3 : ExpHOL 64 := .var .local (ofString "txr")
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "build_mpt_indexed") [e1, e2, e3]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨⟨w_si, w_pl, w_h, w_txr, w_wr, w_rh, w_bh, S, Nd, hIA, hBs, hd_ic,
    _, _, _, _, _, _, hlpl, _, hltxr, _, _, _, hpl_eq, _⟩, hbound0⟩ := hP
  have hb0 := hbound0 w_pl hlpl
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    have hargs' : evalListHOLExact state.toExact [e1, e2, e3] = some values := by
      rwa [evalListHOLFinite_eq_toExact] at hargs
    rcases he1 : evalAt state e1 with _ | v1
    · simp [evalListHOLExact, he1] at hargs'
    · rcases he2 : evalAt state e2 with _ | v2
      · simp [evalListHOLExact, he1, he2] at hargs'
      · have he3 : evalAt state e3 = some (.val (.word w_txr)) := by
          simpa [e3, evalAt, evalHOLExact] using hltxr
        rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "build_mpt_indexed") values
          with _ | ⟨body, callee, ret⟩
        · rw [hl] at hcall; simp at hcall
        · rw [hl] at hcall; dsimp only at hcall
          split_ifs at hcall with hz
          · simp at hcall
          · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body
              with ⟨bres, post⟩
            rw [hb] at hcall
            cases bres with
            | none => simp at hcall
            | some br =>
              cases br with
              | returned v =>
                dsimp only at hcall
                split_ifs at hcall with hsh
                · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
                  have hpc := callee_param_three state (ofString "build_mpt_indexed")
                    (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
                    (by rw [hcode]; exact lookup_build_mpt_indexed_fn)
                    e1 e2 e3 v1 v2 (.val (.word w_txr)) values body callee ret he1 he2 he3 hargs hl
                  set entry := callEntryStateHOLFinite state callee
                  have hout : locN entry "out" = w_txr.toNat := by
                    simp [entry, locN, callEntryStateHOLFinite, hpc.2.2]
                  have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
                  have hstep := FunSpec.at_lookup wmpt state hcode values body callee ret hl
                    (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
                  rw [hb] at hstep; dsimp only at hstep
                  have hws := hstep (Or.inl ⟨v, rfl⟩)
                  have hIA_entry : InputAtWith entry S Nd w_si.toNat :=
                    (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
                  have htxr_good := hBs (w_txr.toNat, 32) (by simp)
                  have hRz : ∀ j ∈ [(locN entry "out", 32),
                      bufferRegion entry ("keccak_pad", 136),
                      bufferRegion entry ("keccak_st", 200),
                      bufferRegion entry ("mpt_hash_scratch", 40),
                      bufferRegion entry ("mpt_key_scratch", 16)], j.2 = 0 → j.1 % 8 = 0 := by
                    intro j hj
                    rcases List.mem_cons.1 hj with rfl | hj1
                    · intro _; rw [hout]; exact htxr_good.1
                    · rcases List.mem_cons.1 hj1 with rfl | hj2
                      · exact bufferRegion_zero_aligned entry "keccak_pad" 136 (by decide)
                      · rcases List.mem_cons.1 hj2 with rfl | hj3
                        · exact bufferRegion_zero_aligned entry "keccak_st" 200 (by decide)
                        · rcases List.mem_cons.1 hj3 with rfl | hj4
                          · exact bufferRegion_zero_aligned entry "mpt_hash_scratch" 40 (by decide)
                          · simp only [List.mem_singleton] at hj4; subst hj4
                            exact bufferRegion_zero_aligned entry "mpt_key_scratch" 16 (by decide)
                  obtain ⟨_, _, _, _, _, hu_ic2, _⟩ :=
                    WorldStep_preserves_inputAndBlocks hIA_entry (allBlocksGood_nil entry S Nd) hws hRz
                      (fun j hj k hk => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact htxr_good.2.2.2.2 k (worldTypedIvls_sub_worldOwned _ _ _ k hk)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl k hk
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact bufferRegion_disj_le hIA_entry.2.1 ("keccak_st", 200) (by decide) (by decide) 200 le_rfl k hk
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_hash_scratch", 40) (by decide) (by decide) 40 le_rfl k hk
                              · simp only [List.mem_singleton] at hj4; subst hj4
                                exact bufferRegion_disj_le hIA_entry.2.1 ("mpt_key_scratch", 16) (by decide) (by decide) 16 le_rfl k hk)
                      (fun c hc j hj => by
                        rcases List.mem_cons.1 hj with rfl | hj1
                        · rw [hout]; exact hd_ic c hc (w_txr.toNat, 32) (by simp)
                        · rcases List.mem_cons.1 hj1 with rfl | hj2
                          · exact hIA_entry.2.2.2.1 c hc _
                              (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_pad", 136)) (by decide))
                          · rcases List.mem_cons.1 hj2 with rfl | hj3
                            · exact hIA_entry.2.2.2.1 c hc _
                                (bufferRegion_mem_worldOwned entry S Nd (gn := ("keccak_st", 200)) (by decide))
                            · rcases List.mem_cons.1 hj3 with rfl | hj4
                              · exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_hash_scratch", 40)) (by decide))
                              · simp only [List.mem_singleton] at hj4; subst hj4
                                exact hIA_entry.2.2.2.1 c hc _
                                  (bufferRegion_mem_worldOwned entry S Nd (gn := ("mpt_key_scratch", 16)) (by decide)))
                      (fun _ hb _ _ => by cases hb)
                  intro wp hwp
                  dsimp only
                  rw [← hpost_eq] at hwp ⊢
                  have hwp' : wp = w_pl := by simpa [hlpl] using hwp.symm
                  subst wp
                  exact ph_withdrawal_bounds_unhit hIA hpl_eq hu_ic2 hb0
                · simp at hcall
              | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_dec_nwd_post_b {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_NWD_B body K) :
    TerminatingProgBoundedOn PH_WR_POST_B
      (.dec (ofString "nwd") .one
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64])) body) K := by
  refine dec_eval_on (P := PH_WR_POST_B) (Q := PH_NWD_B) _ _ _ ?_ hbody
  intro F s v ⟨⟨w_si, w_pl, w_wr, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hpl_eq⟩, hbound⟩ hev
  obtain ⟨a, w_nwd, ha, rfl, hmem, _⟩ := evalAt_load_one_word hIA.1.1 hev
  have ha_eq := evalAt_add_local_const (off := 56) hlpl ha
  subst ha_eq
  have hbv : BitVec.ofNat 64 (memW s (w_pl + 56#64).toNat) = w_nwd := by
    rw [← hmem, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨w_si, w_pl, w_wr, w_nwd, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd [(w_wr.toNat, 32)]).2 hBs,
    hd_ic, ?_, ?_, ?_, ?_, hpl_eq, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nwd" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · intro hn
    have hb := hbound w_pl hlpl (by rwa [hbv])
    rwa [← hmem] at hb

theorem ph_alloc_wd_rlp_slices_b
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    Hoare PH_NWD_B
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]])
      (fun r t => r = none → PH_WDS0_B t) := by
  classical
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  obtain ⟨w_si, w_pl, w_wr, w_nwd, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hlnwd, hpl_eq, hnwdb⟩ := hP
  have hbase := (ph_alloc_wd_rlp_slices wal rtal).run state hcode
    ⟨w_si, w_pl, w_wr, w_nwd, S, Nd, hIA, hBs, hd_ic, hlsi, hlpl, hlwr, hlnwd, hpl_eq⟩
    (by rw [hr]; simp) hr
  set e_sz : ExpHOL 64 :=
    .op .add [.panop .mul [.var .local (ofString "nwd"), .const 16#64], .const 16#64]
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, ofString "wd_rlp_slices"), none)) (ofString "alloc") [e_sz])
    with ⟨cres, cpost⟩
  have hbase0 : PH_WDS0 cpost := by rw [hcall] at hbase; exact hbase
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
  set w_sz : BitVec 64 := w_nwd * 16#64 + 16#64
  have he_sz : evalAt state e_sz = some (.val (.word w_sz)) := by
    simp [e_sz, w_sz, evalAt, evalHOLExact, evalListHOLExact, hlnwd, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp]
  have hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [e_sz] =
      some [.val (.word w_sz)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp only [evalListHOLExact]
    unfold evalAt at he_sz
    rw [he_sz]
  rw [evaluateHOLFiniteState_call, hargs] at hcall
  dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") [.val (.word w_sz)]
    with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, post⟩
      rw [hb] at hcall
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned value =>
          dsimp only at hcall
          split_ifs at hcall with hsh hv
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hstep := FunSpec.at_lookup wal state hcode [.val (.word w_sz)] body callee ret hl
              (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
            rw [hb] at hstep; dsimp only at hstep
            have hws := hstep (Or.inl ⟨value, rfl⟩)
            have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
              (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
            obtain ⟨_, _, _, _, _, hu_ic, _⟩ :=
              WorldStep_preserves_inputAndBlocks hIA_entry (allBlocksGood_nil _ S Nd) hws
                (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
                (fun _ _ _ hj => by simp at hj) (fun _ hb' _ _ => by cases hb')
            have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
            obtain ⟨w_si', w_pl', w_wr', w_nwd', w_wds, S', Nd',
              hIA', hBs', hd_ic', hd', hlsi', hlpl', hlwr', hlnwd', hgwds', hpl_eq'⟩ := hbase0
            have hpl_same : w_pl' = w_pl := by
              rw [← hpost_eq] at hlpl'
              simpa [setKvarHOLFinite, setGlobalHOLFinite, hlpl] using hlpl'.symm
            have hnwd_same : w_nwd' = w_nwd := by
              rw [← hpost_eq] at hlnwd'
              simpa [setKvarHOLFinite, setGlobalHOLFinite, hlnwd] using hlnwd'.symm
            subst w_pl' w_nwd'
            dsimp only
            refine ⟨w_si', w_pl, w_wr', w_nwd, w_wds, S', Nd',
              hIA', hBs', hd_ic', hd', hlsi', hlpl', hlwr', hlnwd', hgwds', hpl_eq', ?_⟩
            intro hn
            rw [← hpost_eq]
            change memW post (w_pl + 48#64).toNat < heapEnd ∧ 44 * w_nwd.toNat ≤ heapEnd + 44
            rw [hm48]
            exact hnwdb hn
          · simp at hcall
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

theorem ph_dec_i_b {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn PH_LOOP_B body K) :
    TerminatingProgBoundedOn PH_WDS0_B
      (.dec (ofString "i") .one (.const 0#64) body) K := by
  refine dec_eval_on (P := PH_WDS0_B) (Q := PH_LOOP_B) _ _ _ ?_ hbody
  intro F s v hP hev
  have hv : v = .val (.word 0#64) := by
    simp only [evalAt, evalHOLExact, Option.some.injEq] at hev
    exact hev.symm
  subst hv
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hgwds, hpl_eq, hnwdb⟩ := hP
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, 0#64, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, by decide, fun hp => absurd hp (by decide), hnwdb⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "si" by decide, hlsi]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "pl" by decide, hlpl]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "wr" by decide, hlwr]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, hlnwd]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem ph_withdrawal_store0_b :
    Hoare PH_LOOP_EB (ph_withdrawal_store 0) (fun r t => r = none → PH_LOOP_EB t) := by
  unfold ph_withdrawal_store
  simp only [↓reduceIte]
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds, hpl_eq, hi0, hilt, hi44, hnwdb⟩ := hP
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbounds := ph_slice_offset_bounds w_nwd w_i hi0 hilt (hnwdb hn0).2
  have hfit0 : 16 * w_i.toNat + 8 ≤ (w_nwd * 16#64 + 16#64).toNat :=
    Nat.le_trans (by omega) hbounds.2.2
  obtain ⟨w1, w2, hw1, hw2, hx_eq⟩ := evalAt_add2_words hx
  have hw1_eq : w1 = w_wds := by
    simpa [evalAt, evalHOLExact, hgwds] using hw1.symm
  subst w1
  obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 16) hw2
  have hwi_eq : wi' = w_i := by
    simpa [evalAt, evalHOLExact, hli] using hwi'.symm
  subst wi'
  cases hmul_eq
  have hv_eq : v = .val (.word e0) := by
    simpa [evalAt, evalHOLExact, hle] using hv.symm
  subst v
  have hx_off : x = w_wds + BitVec.ofNat 64 (16 * w_i.toNat) := by
    rw [hx_eq, ← hbounds.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htr := store_in_tracked_block
    (base := w_wds.toNat) (sz := (w_nwd * 16#64 + 16#64).toNat) (off := 16 * w_i.toNat)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_off (by simpa [flattenHOL] using hfit0) hst
  have hu_ic : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s { s with memory := mem' } c :=
    fun c hc => htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc _ (by simp))
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd,
    htr.1, htr.2.1, ?_, hd, hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds,
    by rw [hic.1]; exact hpl_eq, hi0, hilt, hi44, ?_⟩
  · rw [hic.2.2]; exact hd_ic
  · intro hp
    rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_store1_b :
    Hoare PH_LOOP_EB (ph_withdrawal_store 1) (fun r t => r = none → PH_LOOP_EB t) := by
  unfold ph_withdrawal_store
  simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
  refine Hoare_store_fall (fun s x v mem' hP hx hv hst => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds, hpl_eq, hi0, hilt, hi44, hnwdb⟩ := hP
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbounds := ph_slice_offset_bounds w_nwd w_i hi0 hilt (hnwdb hn0).2
  obtain ⟨w1, w2, w3, hw1, hw2, hw3, hx_eq⟩ := evalAt_add3_words hx
  have hw1_eq : w1 = w_wds := by
    simpa [evalAt, evalHOLExact, hgwds] using hw1.symm
  subst w1
  obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 16) hw2
  have hwi_eq : wi' = w_i := by
    simpa [evalAt, evalHOLExact, hli] using hwi'.symm
  subst wi'
  cases hmul_eq
  have hw3_eq : w3 = 8#64 := by
    simpa [evalAt, evalHOLExact] using hw3.symm
  subst w3
  have hv_eq : v = .val (.word e1) := by
    simpa [evalAt, evalHOLExact, hle] using hv.symm
  subst v
  have hx_off : x = w_wds + BitVec.ofNat 64 (16 * w_i.toNat + 8) := by
    rw [hx_eq, ← hbounds.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htr := store_in_tracked_block
    (base := w_wds.toNat) (sz := (w_nwd * 16#64 + 16#64).toNat) (off := 16 * w_i.toNat + 8)
    hIA hBs (by simp)
    (fun c hc b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hd_ic c hc _ (by simp))
    rfl (by omega) hx_off (by simpa [flattenHOL] using hbounds.2.2) hst
  have hu_ic : ∀ c ∈ inputCells s w_si.toNat, IvlUnhit s { s with memory := mem' } c :=
    fun c hc => htr.2.2 c (fun _ => (hIA.2.2.1 c hc).2.1) (hd_ic c hc _ (by simp))
  have hic := inputCells_eq_of_unhit hIA hu_ic
  have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S, Nd,
    htr.1, htr.2.1, ?_, hd, hlsi, hlpl, hlwr, hlnwd, hli, hle, hgwds,
    by rw [hic.1]; exact hpl_eq, hi0, hilt, hi44, ?_⟩
  · rw [hic.2.2]; exact hd_ic
  · intro hp
    rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_inc_b :
    Hoare PH_LOOP_EB ph_withdrawal_increment (fun r t => r = none → PH_LOOP_B t) := by
  unfold ph_withdrawal_increment
  refine Hoare.assign_fall (fun s v hP hv => ?_)
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, _, _, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, _, hgwds, hpl_eq, hi0, _, hi44, hnwdb⟩ := hP
  have hv_eq : v = .val (.word (w_i + 1#64)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hli, valueIsWord, valueWord,
      wordOpHOL, wordOp] using hv.symm
  subst v
  have he : heapEnd < 2 ^ 40 := by decide
  have hi_lt63 : w_i.toNat + 1 < 2 ^ 63 := by omega
  have hnext_nat : (w_i + 1#64).toNat = w_i.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : (1 : Nat) % 2 ^ 64 = 1 := by decide
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  have hnext_int : 0 ≤ (w_i + 1#64).toInt := by
    rw [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]
    have hnot : ¬ decide ((w_i + 1#64).toNat ≥ 2 ^ 63) = true := by
      rw [decide_eq_true_eq, hnext_nat]; omega
    rw [if_neg hnot]
    exact Int.natCast_nonneg _
  refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i + 1#64, S, Nd,
    (inputAtWith_with_locals s _ s.clock S Nd w_si.toNat).2 hIA,
    (allBlocksGood_with_locals s _ s.clock S Nd _).2 hBs,
    hd_ic, hd, ?_, ?_, ?_, ?_, ?_, hgwds, hpl_eq, hnext_int, ?_, hnwdb⟩
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "si" by decide, hlsi]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "pl" by decide, hlpl]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "wr" by decide, hlwr]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nwd" by decide, hlnwd]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · intro _
    rw [hnext_nat]
    simpa using hi44

theorem hoare_decCall_fall_shaped {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        arguments = some values →
      lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) shape = true →
      R (setVarHOLFinite name value { post with locals := state.locals }))
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · rename_i hcond
              set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed :=
                hres s values body' callee ret' v bpost hcode hP hargs hl hb
                  ((Bool.and_eq_true _ _).mp hcond).1
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem ph_encode_withdrawal_resume_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      (PH_LOOP_B state ∧
        CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) state) →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        ph_withdrawal_args = some values →
      lookupCodeHOLFinite state.code.lookup (ofString "encode_withdrawal_rlp") values =
        some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one, .one]) = true →
      PH_LOOP_EB (setVarHOLFinite (ofString "e") value { post with locals := state.locals }) := by
  intro F state values body callee returnShape value post hcode ⟨hP, hcond⟩ hargs hl hb hsh
  obtain ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, S, Nd, hIA, hBs, hd_ic, hd,
    hlsi, hlpl, hlwr, hlnwd, hli, hgwds, hpl_eq, hi0, hprev, hnwdb⟩ := hP
  have hilt := ph_withdrawal_active_lt hli hlnwd hcond
  have hn0 : 0 < w_nwd.toInt := by omega
  have hbase_lt : memW state (w_pl + 48#64).toNat < heapEnd := (hnwdb hn0).1
  unfold ph_withdrawal_args at hargs
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  set e_arg : ExpHOL 64 :=
    .op .add
      [.load .one (.op .add [.var .local (ofString "pl"), .const 48#64]),
       .panop .mul [.var .local (ofString "i"), .const 44#64]]
  rcases he_arg : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) e_arg with _ | v_arg
  · rw [he_arg] at hargs; simp at hargs
  · rw [he_arg] at hargs
    have hv_list : values = [v_arg] := by simpa using hargs.symm
    subst values
    have hl_fn : state.code.lookup (ofString "encode_withdrawal_rlp") =
        some ([(ofString "wd", .one)],
          sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp, .comb [.one, .one]) := by
      rw [hcode]
      exact lookup_encode_withdrawal_rlp_fn
    have hargs_fin : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) [e_arg] = some [v_arg] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, he_arg]
    obtain ⟨hsh_arg, hcallee_wd⟩ := callee_param_one_exp state (ofString "encode_withdrawal_rlp")
      (ofString "wd") .one _ (.comb [.one, .one]) hl_fn e_arg v_arg [v_arg]
      body callee returnShape he_arg hargs_fin hl
    have hsh_arg_eq := (shapeEqHOL_eq_true _ _).1 hsh_arg
    rcases v_arg with ⟨⟨w_arg⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact] at hsh_arg_eq
    obtain ⟨w_base, w_mul, hw_base, hw_mul, harg_eq⟩ := evalAt_add2_words (s := state) he_arg
    obtain ⟨a48, w_base', ha48, hw_base_val, hmem48, _⟩ := evalAt_load_one_word hIA.1.1 hw_base
    have ha48_eq := evalAt_add_local_const (off := 48) hlpl ha48
    subst a48
    have hw_base_eq : w_base' = w_base := by simpa using hw_base_val.symm
    subst w_base'
    obtain ⟨wi', hwi', hmul_eq⟩ := evalAt_panOp_mul_const (c := 44) hw_mul
    have hwi_eq : wi' = w_i := by simpa [evalAt, evalHOLExact, hli] using hwi'.symm
    subst wi'
    cases hmul_eq
    have hW_state : WorldOK state := ⟨hIA.1, S, (worldTyped_iff_with state S).2 ⟨Nd, hIA.2.1⟩⟩
    have hstep := FunSpec.at_lookup wenc state hcode [.val (.word w_arg)] body callee returnShape hl
      (localsFree_worldOK state callee (state.clock - 1) hW_state) (by rw [hb]; simp)
    rw [hb] at hstep; dsimp only at hstep
    have hws := hstep (Or.inl ⟨value, rfl⟩)
    have hdom0 := FunSpec.at_lookup denc state hcode [.val (.word w_arg)] body callee returnShape hl
      (localsFree_guestInv state callee (state.clock - 1) hIA.1.1) (by rw [hb]; simp)
    rw [hb] at hdom0; dsimp only at hdom0
    have hloc_wd : locN (callEntryStateHOLFinite state callee) "wd" = w_arg.toNat := by
      simp [callEntryStateHOLFinite, locN, hcallee_wd]
    have hinside : Inside (w_arg.toNat, 1) sourceBase heapEnd := by
      have hd1 := hdom0 (Or.inl ⟨value, rfl⟩) (by decide)
      simpa [hloc_wd] using hd1
    have hprog := ph_withdrawal_domain_progress w_base w_i
      (fun hp => ⟨by rw [hmem48]; exact hbase_lt, hprev hp⟩)
      (by rwa [← harg_eq])
    have hIA_entry : InputAtWith (callEntryStateHOLFinite state callee) S Nd w_si.toNat :=
      (inputAtWith_with_locals state callee (state.clock - 1) S Nd w_si.toNat).2 hIA
    have hBs_entry : AllBlocksGood (callEntryStateHOLFinite state callee) S Nd
        [(w_wr.toNat, 32), (w_wds.toNat, (w_nwd * 16#64 + 16#64).toNat)] :=
      (allBlocksGood_with_locals state callee (state.clock - 1) S Nd _).2 hBs
    obtain ⟨S', Nd', hIA_post, hBs_post, _, hu_ic, _⟩ :=
      WorldStep_preserves_inputAndBlocks hIA_entry hBs_entry hws
        (fun _ hj => by simp at hj) (fun _ hj => by simp at hj)
        (fun _ _ _ hj => by simp at hj) (fun _ _ _ hj => by simp at hj)
    have hic := inputCells_eq_of_unhit hIA_entry hu_ic
    have hm48 := ph_payload_word_unhit hIA hpl_eq hu_ic 48 (by omega) (by omega)
    have hgwds_post : post.globals.lookup (ofString "wd_rlp_slices") = some (.val (.word w_wds)) := by
      have hg_eq := hws.2.2.1 (ofString "wd_rlp_slices")
        (by simp [show ofString "wd_rlp_slices" ≠ ofString "heap_ptr" by decide])
      simpa [callEntryStateHOLFinite, hgwds] using hg_eq.symm
    have hsh_eq := (shapeEqHOL_eq_true _ _).1 hsh
    cases value with
    | val _ => simp [shapeOfHOLExact] at hsh_eq
    | nStruct _ _ => simp [shapeOfHOLExact] at hsh_eq
    | rStruct vs =>
      simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh_eq
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh_eq
      rcases hsh_eq with ⟨hv0, hv1⟩
      cases v0 with
      | rStruct _ => simp [shapeOfHOLExact] at hv0
      | nStruct _ _ => simp [shapeOfHOLExact] at hv0
      | val wl0 =>
        cases wl0 with
        | word e0 =>
          cases v1 with
          | rStruct _ => simp [shapeOfHOLExact] at hv1
          | nStruct _ _ => simp [shapeOfHOLExact] at hv1
          | val wl1 =>
            cases wl1 with
            | word e1 =>
              refine ⟨w_si, w_pl, w_wr, w_nwd, w_wds, w_i, e0, e1, S', Nd',
                (inputAtWith_with_locals post _ post.clock S' Nd' w_si.toNat).2 hIA_post,
                (allBlocksGood_with_locals post _ post.clock S' Nd' _).2 hBs_post,
                ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, hgwds_post, ?_, hi0, hilt, hprog.2, ?_⟩
              · change IvlsDisj (inputCells post w_si.toNat) _
                rw [hic.2.2]; exact hd_ic
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "si" by decide, hlsi]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "pl" by decide, hlpl]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "wr" by decide, hlwr]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "nwd" by decide, hlnwd]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
                  show ofString "e" ≠ ofString "i" by decide, hli]
              · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              · change w_pl.toNat = memW post w_si.toNat
                rw [hic.1]; exact hpl_eq
              · intro hp
                change memW post (w_pl + 48#64).toNat < heapEnd ∧ _
                rw [hm48]; exact hnwdb hp

theorem ph_withdrawal_body_hoare_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare
      (fun s => PH_LOOP_B s ∧
        CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nwd"))) s)
      ph_withdrawal_body
      (fun r t => r = none → PH_LOOP_B t) := by
  unfold ph_withdrawal_body
  exact hoare_decCall_fall_shaped
    (fun n hn => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn; rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide)
    ph_loop_b_localsOnly
    (ph_encode_withdrawal_resume_b wenc denc)
    (Hoare.seq_fall ph_withdrawal_store0_b
      (Hoare.seq_fall ph_withdrawal_store1_b ph_withdrawal_inc_b))

theorem ph_withdrawal_loop_hoare_b
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare PH_LOOP_B ph_withdrawal_loop (fun r t => r = none → PH_LOOP_B t) :=
  Hoare.while_preserve_ncb ph_loop_b_decClock rfl (ph_withdrawal_body_hoare_b wenc denc)

private theorem ph_h_false_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_H false s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_oh_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_OH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_tmp_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_TMP s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_txr_guestInv (b : Bool) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_TXR b s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_wr_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_WR s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_rh_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_RH s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_s0_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_S0 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_nwd_b_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_NWD_B s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hIA, _⟩ := h; exact hIA.1.1

private theorem ph_bl_post_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PH_BL_POST s) : WorldOK s := by
  obtain ⟨⟨_, _, _, _, _, _, _, S, Nd, hIA, _⟩, _⟩ := h
  exact ⟨hIA.1, S, (worldTyped_iff_with s S).2 ⟨Nd, hIA.2.1⟩⟩

private theorem ph_store_h0_one :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 0#64]) (.const 1#64))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 0 _ (by omega) (by omega) (by simp) (Or.inl rfl)

private theorem ph_store_h8_raw0 :
    Hoare (PH_H false)
      (.store (.op .add [.var .local (ofString "h"), .const 8#64])
        (.op .add [.var .local (ofString "raw"), .const 0#64]))
      (fun r t => r = none → PH_H false t) :=
  ph_h_store_simple false 8 _ (by omega) (by omega) (by simp) (Or.inr (Or.inl ⟨_, _, rfl⟩))

private theorem ph_withdrawal_loop_bound_b
    (henc : TerminatingFunBoundedOn GuestInv (ofString "encode_withdrawal_rlp") K.«encode_withdrawal_rlp») :
    TerminatingProgBoundedOn PH_LOOP_B ph_withdrawal_loop
      ((2 ^ 64 + 1) * ((K.«encode_withdrawal_rlp» + 1) + 1)) := by
  intro F s hc hP hnt
  exact ph_withdrawal_loop_bound henc s hc (ph_loop_guestInv (ph_loop_b_loop hP)) hnt

private theorem ph_withdrawal_loop_hoare_loop
    (wenc : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "encode_withdrawal_rlp"))
    (denc : ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp")) :
    Hoare PH_LOOP_B ph_withdrawal_loop (fun r t => r = none → PH_LOOP t) :=
  ⟨fun s hc hP hnt hr =>
    ph_loop_b_loop ((ph_withdrawal_loop_hoare_b wenc denc).run s hc hP hnt hr)⟩

theorem «gbody_payload_header» : GBody.«payload_header» := by
  intro hal hbl hmpt hcrh heer henc hkec hmz wal rtal _wbl wmpt wenc denc wkec wmz _zvmz
  refine ⟨_, _, _, R13PayloadStateInit.lookup_payload_header, ?_⟩
  apply ph_entry_dec_pl_raw
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_payload_header,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hal _ _ _
      (callEntryOn_of_imp localsFree_guestInv ph_s0_guestInv _ _)
      (ph_alloc_h wal rtal)
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.call_on hmz _ _
          (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _))
        (ph_memzero_h wmz)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
          ph_store_h0_one
          (TerminatingProgBoundedOn.seq_hoare
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            ph_store_h8_raw0
            (TerminatingProgBoundedOn.decCall_on hal _ _ _
              (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _)
              (ph_alloc_oh wal rtal)
              (TerminatingProgBoundedOn.decCall_on hal _ _ _
                (callEntryOn_of_imp localsFree_guestInv ph_oh_guestInv _ _)
                (ph_alloc_tmp wal rtal)
                (TerminatingProgBoundedOn.seq_hoare
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_storeByte s _ _))
                  ph_storeByte_tmp
                  (TerminatingProgBoundedOn.seq_hoare_trans
                    (TerminatingProgBoundedOn.call_on hkec _ _
                      (callEntryOn_of_imp localsFree_guestInv ph_tmp_guestInv _ _))
                    (ph_keccak_oh wkec)
                    (TerminatingProgBoundedOn.seq_hoare_trans
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                      ph_store_h16_oh
                      (TerminatingProgBoundedOn.seq_hoare
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        ph_store_h24_raw32
                        (TerminatingProgBoundedOn.seq_hoare
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          ph_store_h32_raw52
                          (TerminatingProgBoundedOn.decCall_on hal _ _ _
                            (callEntryOn_of_imp localsFree_guestInv ph_h_false_guestInv _ _)
                            (ph_alloc_txr wal rtal)
                            (TerminatingProgBoundedOn.seq_hoare
                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                              ph_store_h40_txr
                              (TerminatingProgBoundedOn.seq_hoare
                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                ph_store_h48_raw84
                                (TerminatingProgBoundedOn.seq_hoare
                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                  ph_store_h56_raw116
                                  (TerminatingProgBoundedOn.seq_hoare
                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                    ph_store_h64_zero
                                    (TerminatingProgBoundedOn.seq_hoare
                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                      ph_store_h96_pl80
                                      (TerminatingProgBoundedOn.seq_hoare
                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                        ph_store_h104_pl88
                                        (TerminatingProgBoundedOn.seq_hoare
                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                          ph_store_h112_pl96
                                          (TerminatingProgBoundedOn.seq_hoare
                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                            ph_store_h120_pl104
                                            (TerminatingProgBoundedOn.seq_hoare
                                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                              ph_store_h128_pl16
                                              (TerminatingProgBoundedOn.seq_hoare_trans
                                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                ph_store_h136_pl24
                                                (TerminatingProgBoundedOn.seq_hoare
                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                  ph_store_h144_raw372
                                                  (TerminatingProgBoundedOn.decCall_on hal _ _ _
                                                    (callEntryOn_of_imp localsFree_guestInv (ph_txr_guestInv true) _ _)
                                                    (ph_alloc_z8d wal rtal)
                                                    (TerminatingProgBoundedOn.seq_hoare_trans
                                                      (TerminatingProgBoundedOn.call_on hmz _ _
                                                        (callEntryOn_of_imp localsFree_guestInv (fun _ h => ph_z8d_guestInv h) _ _))
                                                      (ph_memzero_z8d wmz)
                                                      (TerminatingProgBoundedOn.seq_hoare_trans
                                                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                        ph_store_h152_z8
                                                        (ph_dec_bf _
                                                          (TerminatingProgBoundedOn.seq_hoare_trans
                                                            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                            ph_store_h160_bf
                                                            (TerminatingProgBoundedOn.decCall_on hal _ _ _
                                                              (callEntryOn_of_imp localsFree_guestInv (ph_txr_guestInv true) _ _)
                                                              (ph_alloc_wr wal rtal)
                                                              (TerminatingProgBoundedOn.seq_hoare
                                                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                ph_store_h192_wr
                                                                (TerminatingProgBoundedOn.seq_hoare
                                                                  (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                  ph_store_h200_pl112
                                                                  (TerminatingProgBoundedOn.seq_hoare
                                                                    (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                    ph_store_h208_pl120
                                                                    (TerminatingProgBoundedOn.seq_hoare
                                                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                      ph_store_h216_si24
                                                                      (TerminatingProgBoundedOn.decCall_on hal _ _ _
                                                                        (callEntryOn_of_imp localsFree_guestInv ph_wr_guestInv _ _)
                                                                        (ph_alloc_rh wal rtal)
                                                                        (TerminatingProgBoundedOn.seq_hoare
                                                                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                          ph_store_h224_rh
                                                                          (TerminatingProgBoundedOn.decCall_on hal _ _ _
                                                                            (callEntryOn_of_imp localsFree_guestInv ph_rh_guestInv _ _)
                                                                            (ph_alloc_bh wal rtal)
                                                                            (TerminatingProgBoundedOn.seq_hoare
                                                                              (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                              ph_store_h232_bh
                                                                              (TerminatingProgBoundedOn.seq_hoare
                                                                                (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                                                                                ph_store_h240_pl128
                                                                                (TerminatingProgBoundedOn.decCall_on hbl _ _ _
                                                                                  ph_block_rlp_length_entry
                                                                                  ph_block_rlp_length_resume
                                                                                  (TerminatingProgBoundedOn.seq_hoare
                                                                                    (TerminatingProgBoundedOn.ite_on
                                                                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_raise s _ _))
                                                                                      (TerminatingProgBoundedOn.of_clock (fun s => clock_skip s)))
                                                                                    ph_bl_check_post
                                                                                    (TerminatingProgBoundedOn.seq_hoare_trans
                                                                                      (TerminatingProgBoundedOn.call_on hmpt _ _
                                                                                        (callEntryOn_of_imp localsFree_worldOK ph_bl_post_worldOK _ _))
                                                                                      (ph_build_mpt_txr_b wmpt)
                                                                                      (ph_dec_nwd_post_b
                                                                                        (TerminatingProgBoundedOn.seq_hoare_trans
                                                                                          (TerminatingProgBoundedOn.call_on hal _ _
                                                                                            (callEntryOn_of_imp localsFree_guestInv ph_nwd_b_guestInv _ _))
                                                                                          (ph_alloc_wd_rlp_slices_b wal rtal)
                                                                                          (ph_dec_i_b
                                                                                            (TerminatingProgBoundedOn.seq_hoare_trans
                                                                                              (ph_withdrawal_loop_bound_b henc)
                                                                                              (ph_withdrawal_loop_hoare_loop wenc denc)
                                                                                              (ph_second_mpt_tail hmpt
                                                                                                (ph_guestInv_tail heer hcrh hkec _ _ _ _)))))))))))))))))))))))))))))))))))))))))))))))
    ?_
  unfold K.«payload_header»
  try simp only [show ∀ a b : Nat, Nat.max a b = max a b from fun _ _ => rfl]
  omega

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
