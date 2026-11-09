import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.MptSetRootKeepsExt
import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalkWip
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkCacheGetRoot
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
def bmiWkGw : List String := ["heap_ptr", "scratch_ptr"]
theorem bmiWkGw_map : bmiWkGw.map ofString = ["heap_ptr", "scratch_ptr"].map ofString := rfl
theorem bmiWkGw_no_gb : ∀ gs ∈ globalBuffers, ofString gs.1 ∉ ["heap_ptr", "scratch_ptr"].map ofString := by
  decide
theorem bmiWk_we_of_heapByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Sub Rl : List Ivl}
    (h : HeapByteEff s post Sub (bmiWkGw : List String))
    (hc : post.code = originalRuntimeCode)
    (hes : post.eshapes = s.eshapes)
    (hRl : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    R16Shards.WorldEff s post Rl [] (bmiWkGw : List String) := by
  refine ⟨h.arena, hc, h.memaddrs, h.be, hes, h.hp_le, h.fp_eq, h.sp_le, h.globals,
    freshBufsOK_of_no_globalBuf_writes h.globals bmiWkGw_no_gb, h.out_dom, ?_, ?_⟩
  · intro a hne
    rcases h.cell_frame a hne with ⟨ivl, hivl, hcp⟩ | hfg | hhf
    · obtain ⟨h0, hc1, hc2⟩ := hcp
      rcases hRl ivl hivl h0 with ⟨j, hj, hj1, hj2⟩ | hg | hh
      · refine Or.inl ⟨j, hj, ?_, ?_⟩
        · omega
        · simp only [CellHits] at ⊢
          omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        simp only [Fast_C08WkShard03.CellHitsPos, CellHits, freeGap] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [Fast_C08WkShard03.CellHitsPos, CellHits, heapFree] at ⊢
        omega
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))
  · intro b hb64 hne
    rcases h.byte_frame b hb64 hne with ⟨ivl, hivl, hiv⟩ | hfg | hhf
    · obtain ⟨h1, h2⟩ := hiv
      rcases hRl ivl hivl (by omega) with ⟨j, hj, hj1, hj2⟩ | hg | hh
      · refine Or.inl ⟨j, hj, ?_⟩
        simp only [InIvl] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        simp only [InIvl, freeGap] at ⊢
        omega
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [InIvl, heapFree] at ⊢
        omega
    · exact Or.inr (Or.inr (Or.inl hfg))
    · exact Or.inr (Or.inr (Or.inr hhf))
theorem bmiWk_we_trans_heapByteEff {F : Type} {s0 t mid : PanSemStateFiniteExact 64 F}
    {Sub Rl : List Ivl}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hb : HeapByteEff t mid Sub (bmiWkGw : List String))
    (hc : mid.code = originalRuntimeCode)
    (hes : mid.eshapes = t.eshapes)
    (hRl : ∀ iv ∈ Sub, 0 < iv.2 →
      (∃ j ∈ Rl, j.1 ≤ iv.1 ∧ iv.1 + iv.2 ≤ j.1 + j.2) ∨
      (globN t "frame_mem_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ globN t "scratch_ptr") ∨
      (globN t "heap_ptr" ≤ iv.1 ∧ iv.1 + iv.2 ≤ heapLimit)) :
    R16Shards.WorldEff s0 mid Rl [] (bmiWkGw : List String) := by
  have hstep := bmiWk_we_of_heapByteEff hb hc hes hRl
  exact R16Shards.WorldEff.trans h hstep (fun gs hgs => absurd hgs (by simp))
    (freshBufsOK_of_no_globalBuf_writes
      (fun k hk => (h.gw_kept k hk).trans (hstep.gw_kept k hk)) bmiWkGw_no_gb)
def bmiWkKeccakR (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
   bufferRegion s ("mpt_hash_scratch", 40)]
def bmiWkMptRm (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  (locN s "m", globN s "heap_ptr" - locN s "m") :: bmiWkKeccakR s
theorem bmiWkKeccakR_eq_mptSetR_sc {F : Type} (s : PanSemStateFiniteExact 64 F) :
    bmiWkKeccakR s = mptSetR_sc s := rfl
theorem bmiWk_we_callee_mpt {F : Type} {s0 t post : PanSemStateFiniteExact 64 F}
    {Rm : PanSemStateFiniteExact 64 F → List Ivl}
    {Wown : List Ivl} {Rl : List Ivl}
    (h : R16Shards.WorldEff s0 t Rl [] (bmiWkGw : List String))
    (hRl : ∀ i ∈ Rm t, 0 < i.2 → ∃ j ∈ Rl, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hRlW : ∀ j ∈ Wown, j ∈ Rl)
    (hAp : ArenaReady post)
    (hhp : globN t "heap_ptr" ≤ globN post "heap_ptr")
    (hspc : globN post "scratch_ptr" ≤ globN t "scratch_ptr")
    (hcell : ∀ a : BitVec 64, post.memory a ≠ t.memory a →
      (∃ i ∈ Rm t, 0 < i.2 ∧ i.1 < a.toNat + 8 ∧ a.toNat < i.1 + i.2) ∨
      (∃ j ∈ Wown, 0 < j.2 ∧ j.1 < a.toNat + 8 ∧ a.toNat < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" < a.toNat + 8 ∧ a.toNat < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" < a.toNat + 8 ∧ a.toNat < heapLimit))
    (hbyte : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB t b →
      (∃ i ∈ Rm t, 0 < i.2 ∧ i.1 ≤ b ∧ b < i.1 + i.2) ∨
      (∃ j ∈ Wown, 0 < j.2 ∧ j.1 ≤ b ∧ b < j.1 + j.2) ∨
      (0 < globN t "scratch_ptr" - globN t "frame_mem_ptr" ∧
        globN t "frame_mem_ptr" ≤ b ∧ b < globN t "scratch_ptr") ∨
      (0 < heapLimit - globN t "heap_ptr" ∧
        globN t "heap_ptr" ≤ b ∧ b < heapLimit))
    (hgw : ∀ k : MlS, k ∉ [ofString "heap_ptr", ofString "scratch_ptr"] →
      t.globals.lookup k = post.globals.lookup k)
    (hc : post.code = originalRuntimeCode)
    (hmd : post.memaddrs = t.memaddrs ∧ post.be = t.be ∧ post.eshapes = t.eshapes)
    (hout : ∀ a : BitVec 64, post.memory a ≠ t.memory a → t.memaddrs a) :
    R16Shards.WorldEff s0 post Rl [] (bmiWkGw : List String) := by
  obtain ⟨hmd_ma, hmd_be, hmd_es⟩ := hmd
  have hfmp_t : globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr" := h.fmp_eq
  have hfmp_p : globN post "frame_mem_ptr" = globN t "frame_mem_ptr" :=
    globN_eq_of_lookup (hgw (ofString "frame_mem_ptr") (by decide))
  have hsp_t : globN t "scratch_ptr" ≤ globN s0 "scratch_ptr" := h.sp_hi
  have hhp_t : globN s0 "heap_ptr" ≤ globN t "heap_ptr" := h.hp_lo
  have hgw_c : GlobalsKept (bmiWkGw : List String) s0 post := by
    intro k hk
    rw [bmiWkGw_map] at hk
    have h1 : k ∉ [ofString "heap_ptr", ofString "scratch_ptr"] := by
      intro hm
      exact hk (by simpa using hm)
    exact (h.gw_kept k hk).trans (hgw k h1)
  refine ⟨hAp, hc, hmd_ma.trans h.memaddrs, hmd_be.trans h.be, hmd_es.trans h.eshapes,
    le_trans hhp_t hhp, hfmp_p.trans hfmp_t, le_trans hspc hsp_t, hgw_c,
    freshBufsOK_of_no_globalBuf_writes hgw_c bmiWkGw_no_gb, fun a hne => ?_, ?_, ?_⟩
  · by_cases hct : post.memory a = t.memory a
    · rw [hct] at hne; exact h.out_dom a hne
    · exact h.memaddrs ▸ hout a hct
  · intro a hne
    by_cases hct : post.memory a = t.memory a
    · rw [hct] at hne; exact h.cell_frame a hne
    · rcases hcell a hct with ⟨i, hi, h0, hc1, hc2⟩ | ⟨j, hj, hj0, hj1, hj2⟩ | hfg |
        ⟨h0, hc1, hc2⟩
      · obtain ⟨j', hj', hj0', hj1', hj2'⟩ := hRl i hi h0
        exact Or.inl ⟨j', hj', hj0', ⟨by omega, by omega⟩⟩
      · exact Or.inl ⟨j, hRlW j hj, hj0, hj1, hj2⟩
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
        all_goals (dsimp only [freeGap]; omega)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))
        all_goals dsimp only [Fast_C08WkShard03.CellHitsPos, CellHits, heapFree]
        all_goals omega
  · intro b hb64 hne
    by_cases hct : memB post b = memB t b
    · rw [hct] at hne; exact h.byte_frame b hb64 hne
    · rcases hbyte b hb64 hct with ⟨i, hi, h0, h1, h2⟩ | ⟨j, hj, hj0, hj1, hj2⟩ | hfg |
        ⟨h0, h1, h2⟩
      · obtain ⟨j', hj', hj0', hj1', hj2'⟩ := hRl i hi h0
        exact Or.inl ⟨j', hj', ⟨by omega, by omega⟩⟩
      · exact Or.inl ⟨j, hRlW j hj, hj1, hj2⟩
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
        all_goals (dsimp only [freeGap]; omega)
      · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
        all_goals dsimp only [InIvl, heapFree]
        all_goals omega
def BmiWkInv (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat) (mark : Nat)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady t ∧
  locN t "mark" = mark ∧ locN t "m" = mark ∧
  (∃ w : BitVec 64, t.locals.lookup (ofString "m") = some (.val (.word w))) ∧
  (∃ w : BitVec 64, t.locals.lookup (ofString "slice_arr") = some (.val (.word w))) ∧
  locN t "n" = locN s0 "n" ∧ locN t "slice_arr" = locN s0 "slice_arr" ∧
    locN t "out" = locN s0 "out" ∧
  mark ≤ globN t "heap_ptr" ∧
  globN t "heap_ptr" ≤ heapLimit ∧
  globN t "keccak_pad" = globN s0 "keccak_pad" ∧
    globN t "keccak_st" = globN s0 "keccak_st" ∧
  globN t "frame_mem_ptr" = globN s0 "frame_mem_ptr" ∧
  globN t "mpt_hash_scratch" = globN s0 "mpt_hash_scratch" ∧
  globN t "scratch_ptr" ≤ globN s0 "scratch_ptr" ∧
  (∃ S Nd Nm,
    WorldTypedWith t S Nd ∧
    MptObjInWith t S Nm mark ∧ NodeHeapValuePtrOK t Nm ∧
    IvlsDisj ((mark, 16) :: nodeExtents t Nm) (nodeExtents t Nd) ∧
    IvlsDisj (bmiWkRti s0) (worldTypedIvls t S Nd ++ mptObjIvls t Nm mark) ∧
    IvlsDisj [(locN s0 "slice_arr", 16 * locN s0 "n")]
      (worldOwned t S Nd ++ mptObjIvls t Nm mark) ∧
    (∀ o ∈ nodeExtents t Nm, mark ≤ o.1 ∧ o.1 + o.2 ≤ globN t "heap_ptr") ∧
    (∀ o ∈ worldOwned t S Nd, o = (0, 0) ∨
      (∃ j ∈ worldOwned s0 S0 Nd0, j.1 ≤ o.1 ∧ o.1 + o.2 ≤ j.1 + j.2) ∨
      (mark ≤ o.1 ∧ o.1 + o.2 ≤ globN t "heap_ptr")) ∧
    (∀ o ∈ worldOwned t S Nd, o = (0, 0) ∨
      Inside o sourceBase mark ∨ Inside o (globN t "scratch_ptr") scratchEnd) ∧
    (∀ r ∈ R10Shards.P26_P28.stdKeep, globN s0 r.1 ≠ 0 → ∀ k ∈ r.2,
      (∀ i ∈ bmiWkRti s0, ¬ CellHits (globN s0 r.1 + k) i) →
      memW t (globN s0 r.1 + k) = memW s0 (globN s0 r.1 + k)) ∧
    (∀ i, i < locN s0 "n" →
      memW t (locN s0 "slice_arr" + 16 * i) = memW s0 (locN s0 "slice_arr" + 16 * i) ∧
      memW t (locN s0 "slice_arr" + 16 * i + 8) = memW s0 (locN s0 "slice_arr" + 16 * i + 8))) ∧
  locN s0 "slice_arr" + 16 * locN s0 "n" ≤ mark ∧
  (∀ iv ∈ bmiWkRti s0, iv.2 = 0 ∨ Allocated s0 iv) ∧
  globN t "mpt_key_scratch" = globN s0 "mpt_key_scratch" ∧
  globN t "mpt_key_scratch" ≠ 0 ∧
  (Inside (locN s0 "slice_arr", 16 * locN s0 "n") sourceBase (globN t "heap_ptr") ∧
    WordsOK t (locN s0 "slice_arr", 16 * locN s0 "n")) ∧
  IvlsDisj [(locN s0 "slice_arr", 16 * locN s0 "n")]
    (bmiWkRti s0 ++ worldOwned s0 S0 Nd0) ∧
  (∀ i, i < locN s0 "n" → memW s0 (locN s0 "slice_arr" + 16 * i) + 8 ≤ mark) ∧
  (∀ i, i < locN s0 "n" → ∀ iv ∈ keccakBufIvls s0, 0 < iv.2 →
    ¬ InIvl (memW s0 (locN s0 "slice_arr" + 16 * i)) iv) ∧
  mark + 16 ≤ globN t "heap_ptr"
theorem bmiWk_fixedObjects_zero_len_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ j ∈ fixedObjects s, j.2 = 0 → j = (0, 0) := by
  intro j hj hz
  unfold fixedObjects at hj
  rcases List.mem_append.1 hj with hf1 | hbal
  · rcases List.mem_append.1 hf1 with hf2 | hbo
    · rcases List.mem_append.1 hf2 with hbuf | hjr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hbuf
        by_cases h0 : globN s p.1 = 0
        · simp [h0]
        · simp only [h0, ↓reduceIte] at hz
          have hpos : ∀ q ∈ globalBuffers, 0 < q.2 := by decide
          exact absurd hz (Nat.ne_of_gt (hpos p hp))
      · simp only [List.mem_singleton] at hjr
        subst hjr; dsimp at hz
        have hc : globN s "journal_cap" = 0 := by omega
        simp [hc]
    · have hobj : ∀ (bo p len : Nat),
          (if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)).2 = 0 →
          (if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) = (0, 0) := by
        intro bo p len h
        split_ifs at h ⊢ with hc
        · rfl
        · dsimp at h; exact absurd (Or.inr (Or.inr h)) hc
      have hblst : ∀ (bo l : Nat), ∀ x ∈ (if bo = 0 ∨ l = 0 then [(0, 0), (0, 0)]
          else [(if bo = 0 ∨ l = 0 ∨ 24 = 0 then (0, 0) else (l, 24)),
                (if bo = 0 ∨ memW s l = 0 ∨ 8 * memW s (l + 16) = 0 then (0, 0)
                 else (memW s l, 8 * memW s (l + 16)))]),
          x.2 = 0 → x = (0, 0) := by
        intro bo l x hx hxz
        by_cases hc : bo = 0 ∨ l = 0
        · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> rfl
        · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hobj _ _ _ hxz
          · exact hobj _ _ _ hxz
      unfold blockOutObjects at hbo
      rcases List.mem_append.1 hbo with hbo12 | h72
      · rcases List.mem_append.1 hbo12 with hbo1 | h40
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hbo1
          rcases hbo1 with rfl | rfl | rfl <;> exact hobj _ _ _ hz
        · exact hblst _ _ j h40 hz
      · exact hblst _ _ j h72 hz
  · have hlst : ∀ (l esz : Nat), ∀ x ∈ lstObjects s l esz, x.2 = 0 → x = (0, 0) := by
      intro l esz x hx hxz
      unfold lstObjects at hx
      by_cases hl0 : l = 0
      · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · simp only [hl0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · dsimp at hxz; omega
        · dsimp at hxz; simp [hxz]
    unfold balObjects at hbal
    obtain ⟨ad, _, hj_ad⟩ := List.mem_flatMap.1 hbal
    rcases List.mem_cons.1 hj_ad with rfl | hj_rest
    · dsimp at hz; omega
    · rcases List.mem_append.1 hj_rest with hj123 | hj_stor
      · rcases List.mem_append.1 hj123 with hj12 | hj32
        · rcases List.mem_append.1 hj12 with hj16 | hj24
          · exact hlst _ _ j hj16 hz
          · exact hlst _ _ j hj24 hz
        · exact hlst _ _ j hj32 hz
      · obtain ⟨l, _, hj_l⟩ := List.mem_flatMap.1 hj_stor
        exact hlst _ _ j hj_l hz
theorem bmiWk_worldOwned_zero_or_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) :
    ∀ o ∈ worldOwned s S Nd, o = (0, 0) ∨ Inside o sourceBase (globN s "heap_ptr") ∨
      Inside o (globN s "scratch_ptr") scratchEnd := by
  obtain ⟨hT, _, hF, hTr⟩ := hW
  intro j hj
  unfold worldOwned at hj
  rcases List.mem_append.1 hj with h1 | hnd
  · rcases List.mem_append.1 h1 with htab | hfix
    · obtain ⟨u, hu, hj_fp⟩ := List.mem_flatMap.1 htab
      rcases ((hT.2.1 u hu).2 j hj_fp).1 with hhp | hsc
      · exact Or.inr (Or.inl hhp)
      · exact Or.inr (Or.inr hsc)
    · rcases hF.1 j hfix with hz | ⟨hal, _⟩
      · exact Or.inl (bmiWk_fixedObjects_zero_len_eq s j hfix hz)
      · rcases hal with hhp | hsc
        · exact Or.inr (Or.inl hhp)
        · exact Or.inr (Or.inr hsc)
  · obtain ⟨n, hn, hj_n⟩ := List.mem_flatMap.1 hnd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_n
    rcases hj_n with rfl | rfl
    · rcases (hTr.1.1 n hn).2.1 with hhp | hsc
      · exact Or.inr (Or.inl hhp)
      · exact Or.inr (Or.inr hsc)
    · unfold nodePath
      split_ifs with hp
      · rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 hp.1 with h0 | ⟨_, hal, _⟩
        · exact absurd h0 hp.2
        · rcases hal with hhp | hsc
          · exact Or.inr (Or.inl hhp)
          · exact Or.inr (Or.inr hsc)
      · exact Or.inl rfl
end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
