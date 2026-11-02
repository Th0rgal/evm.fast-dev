import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetLoops

/-! Semantic specs for `htab_grow`, `htab_new_node`, `htab_new_leaf`, and `htab_new_internal`. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Arithmetic, Disjointness, and Arena Helpers -/

theorem nodup_len_le_range {l : List Nat} {n : Nat} (hnd : l.Nodup)
    (hr : ∀ x ∈ l, 1 ≤ x ∧ x < n) : l.length ≤ n - 1 := by
  have hsub : l.toFinset ⊆ Finset.Ico 1 n := by
    intro x hx
    simp only [List.mem_toFinset] at hx
    simp only [Finset.mem_Ico]
    exact hr x hx
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico] at this
  exact this

/-- Every `HtabBlocks` table has `hdr s t 10 < 10^9`, `hdr s t 1 ≤ 64`, `hdr s t 1 % 8 = 0`, `8 ≤ hdr s t 1`. -/
theorem htabBlocks_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hB : HtabBlocks s t) :
    hdr s t 10 < 1000000000 ∧ 8 ≤ hdr s t 1 ∧ hdr s t 1 ≤ 64 ∧ hdr s t 1 % 8 = 0 ∧
    sourceBase ≤ t ∧ t + 88 ≤ heapEnd ∧ t % 8 = 0 := by
  have hhdr_in := (hB.1 (t, 88) (by simp [htabFootprint]))
  have hnd_in := (hB.1 (hdr s t 5, (hdr s t 10 + 1) * 32) (by simp [htabFootprint])).1
  have hk1 := hB.2.2.1
  have hk60 : hdr s t 0 ≤ 60 := hB.2.2.2.1
  have hst := hB.2.2.2.2.1
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := rfl
  unfold Inside WordsOK at hhdr_in
  unfold Inside at hnd_in
  refine ⟨by omega, by omega, by omega, by omega, hhdr_in.1.1, hhdr_in.1.2, hhdr_in.2.1⟩

/-- Every `ArenaReady` state has a `BitVec 64` word bound to `"heap_ptr"` in `globals` with `toNat = globN s "heap_ptr"`. -/
theorem arenaReady_heap_word {F : Type} {s : PanSemStateFiniteExact 64 F} (hA : ArenaReady s) :
    ∃ hp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      sourceBase ≤ hp.toNat ∧ hp.toNat ≤ cMax.toNat ∧ hp.toNat % 8 = 0 := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhl : heapLimit = cMax.toNat := rfl
  have hok := hA.2
  have hge : sourceBase ≤ globN s "heap_ptr" := hok.1
  cases hg : s.globals.lookup (ofString "heap_ptr") with
  | none => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
            omega
  | some val =>
    cases val with
    | val wl =>
      cases wl with
      | word hp =>
        have hgn : globN s "heap_ptr" = hp.toNat := by unfold globN; rw [hg]
        refine ⟨hp, rfl, hgn.symm, by omega, ?_, ?_⟩
        · have := hok.2.1; rw [hgn, hhl] at this; exact this
        · have := hok.2.2.2.2.2.1; rw [hgn] at this; exact this
    | rStruct _ => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
                   omega
    | nStruct _ _ => have hz : globN s "heap_ptr" = 0 := by unfold globN; rw [hg]
                     omega

/-- Updating `"heap_ptr"` to an aligned `q` with `hp ≤ q ≤ cMax` preserves `ArenaReady` and advances `globN _ "heap_ptr"` to `q.toNat`. -/
theorem arenaReady_upd_heap {F : Type} {s : PanSemStateFiniteExact 64 F}
    {q : BitVec 64} (hA : ArenaReady s)
    (hq_lo : globN s "heap_ptr" ≤ q.toNat) (hq_hi : q.toNat ≤ cMax.toNat) (hq_al : q.toNat % 8 = 0) :
    let s' := { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) }
    ArenaReady s' ∧ globN s' "heap_ptr" = q.toNat ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = s'.globals.lookup k) := by
  intro s'
  have hG : GuestInv s' := guestInv_congr (s := s) rfl rfl rfl rfl hA.1
  have hhp : globN s' "heap_ptr" = q.toNat := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE]
  have hfm : globN s' "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN s' "scratch_ptr" = globN s "scratch_ptr" := by
    simp [s', globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hhl : heapLimit = cMax.toNat := rfl
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8⟩ := hA.2
  refine ⟨⟨hG, ?_⟩, hhp, ?_⟩
  · unfold ArenaOK
    rw [hhp, hfm, hsp, hhl]
    exact ⟨le_trans h1 hq_lo, hq_hi, h3, h4, h5, hq_al, h7, h8⟩
  · intro k hk
    have hne : ofString "heap_ptr" ≠ k := by
      rintro rfl; exact hk (by simp)
    simp [s', HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-- An `Allocated` interval with positive length does not overlap `[lo, hi)` when `globN s "heap_ptr" ≤ lo`, `lo < hi`, and `hi ≤ heapLimit`. -/
theorem disj_fresh_of_allocated {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} {lo hi : Nat} (hA : ArenaReady s) (hal : Allocated s i)
    (hlo : globN s "heap_ptr" ≤ lo) (hhi : hi ≤ heapLimit) :
    i.2 = 0 ∨ hi ≤ lo ∨ lo + (hi - lo) ≤ i.1 ∨ i.1 + i.2 ≤ lo := by
  have hok := hA.2
  have hss : heapLimit = scratchStart := rfl
  by_cases hlen : hi ≤ lo
  · exact Or.inr (Or.inl hlen)
  · rcases hal with ⟨_, hi2⟩ | ⟨hi1, _⟩
    · exact Or.inr (Or.inr (Or.inr (by omega)))
    · have : scratchStart ≤ i.1 := by have := hok.2.2.1; have := hok.2.2.2.1; omega
      exact Or.inr (Or.inr (Or.inl (by omega)))

/-- Compatibility wrapper returning `Disj (lo, hi - lo) i`. -/
theorem disj_fresh_ivl {F : Type} {s : PanSemStateFiniteExact 64 F}
    {i : Ivl} {lo hi : Nat} (hA : ArenaReady s) (hal : Allocated s i)
    (hlo : globN s "heap_ptr" ≤ lo) (hhi : hi ≤ heapLimit) :
    Disj (lo, hi - lo) i := by
  rcases disj_fresh_of_allocated hA hal hlo hhi with hz | hle | h1 | h2
  · exact Or.inr (Or.inl hz)
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h2))

/-- If `FrameOutside s1 s2 [iv] (0, 0)` holds and `iv.2 = 0 ∨ a + 8 ≤ iv.1 ∨ iv.1 + iv.2 ≤ a` where `a < 2^64`,
then `memW s2 a = memW s1 a`. -/
theorem memW_eq_of_frame_disj {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {iv : Ivl} {a : Nat}
    (hfr : FrameOutside s1 s2 [iv] (0, 0))
    (ha_lt : a < 2 ^ 64)
    (hsep : a + 8 ≤ iv.1 ∨ iv.1 + iv.2 ≤ a) :
    memW s2 a = memW s1 a := by
  have hcell : s2.memory (BitVec.ofNat 64 a) = s1.memory (BitVec.ofNat 64 a) := by
    apply hfr (BitVec.ofNat 64 a)
    · intro j hj hhit
      rw [List.mem_singleton.mp hj] at hhit
      have hba : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt]
      have h1 : iv.1 < a + 8 := by have := hhit.1; omega
      have h2 : a < iv.1 + iv.2 := by have := hhit.2; omega
      rcases hsep with hle | hle
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hle)
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h2 hle)
    · intro hhit
      have h2 : (BitVec.ofNat 64 a).toNat < (0, 0).1 + (0, 0).2 := hhit.2
      dsimp only at h2
      omega
  unfold memW
  rw [hcell]

/-- Under `MemCopyRel s1 s2 dst src len len`, when `dst % 8 = 0`, `src % 8 = 0`, `off + 8 ≤ len`, `off % 8 = 0`,
`memW s2 (dst.toNat + off) = memW s1 (src.toNat + off)`. -/
theorem memW_copied_of_memCopyRel {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    {dst src : BitVec 64} {len off : Nat}
    (hrel : MemCopyRel s1 s2 dst src len len)
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0) (hoff8 : off % 8 = 0)
    (hoff_le : off + 8 ≤ len)
    (hd_nw : dst.toNat + len < 2 ^ 64) (hs_nw : src.toNat + len < 2 ^ 64) :
    memW s2 (dst.toNat + off) = memW s1 (src.toNat + off) := by
  have hbe : s2.be = s1.be := hrel.2.2.2.2.1
  apply (memW_eq_iff_memB hbe (by omega) (by omega) (by omega) (by omega)).mpr
  intro r hr
  have hc := hrel.2.2.2.2.2.2.2.1 (off + r) (by omega)
  have hd_eq : (dst + BitVec.ofNat 64 (off + r)).toNat = (dst.toNat + off) + r := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hs_eq : (src + BitVec.ofNat 64 (off + r)).toNat = (src.toNat + off) + r := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [← hd_eq, ← hs_eq]
  exact hc

/-- `Ret.decCall_alloc`: specialized `decCall1` for `alloc(arg)` from an `ArenaReady` state. -/
theorem Ret.decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : MlS} {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (nv : BitVec 64) (harg : evalAt s arg = some (.val (.word nv)))
    (hk : ∀ (hp q : BitVec 64) (s' : PanSemStateFiniteExact 64 F),
      hp.toNat = globN s "heap_ptr" →
      hp.toNat % 8 = 0 →
      hp.toNat + nv.toNat ≤ q.toNat →
      q.toNat ≤ cMax.toNat →
      q.toNat % 8 = 0 →
      ArenaReady s' →
      globN s' "heap_ptr" = q.toNat →
      s'.memory = s.memory →
      s'.be = s.be →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = s'.globals.lookup k) →
      s'.locals = s.locals →
      Ret (setVarHOLFinite x (.val (.word hp)) s') cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one (ofString "alloc") [arg] cont) Φ := by
  obtain ⟨hp, hhp_g, hhp_nat, _, hhp_hi, hhp_al⟩ := arenaReady_heap_word hA
  refine Ret.decCall1 hA.1.code lookup_alloc_fn nv harg ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
  have hrun_spec := alloc_body_run entry hp nv hA.1.code hhp_hi hhp_g
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hrun_spec
  obtain ⟨hw_eq, hq_lo, hq_hi, hq_al, hpost_eq⟩ := hrun_spec
  dsimp only at hpost_eq
  injection hw_eq with hw1; injection hw1 with hw2
  have hw_eq_hp : w = hp := hw2
  subst hw_eq_hp
  let q := (w + (nv + 7)) &&& ((0 : BitVec 64) - 8)
  have hq_lo' : w.toNat + nv.toNat ≤ q.toNat := hq_lo
  have hhp_le_q : globN s "heap_ptr" ≤ q.toNat := by omega
  obtain ⟨hA', hgn', hg_keep⟩ := arenaReady_upd_heap hA hhp_le_q hq_hi hq_al
  let s_res := { post with locals := s.locals }
  have hs_res_eq : s_res = { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := post.clock } := by
    dsimp only [s_res]
    rw [hpost_eq]
    cases s; rfl
  have hA_res : ArenaReady s_res := by
    rw [hs_res_eq]
    exact (arenaReady_locals { s with globals := s.globals.update (ofString "heap_ptr", .val (.word q)) } s.locals post.clock).mpr hA'
  exact hk w q s_res hhp_nat hhp_al hq_lo hq_hi hq_al hA_res
    (by rw [hs_res_eq]; exact hgn')
    (by rw [hs_res_eq])
    (by rw [hs_res_eq])
    (fun k hk' => by rw [hs_res_eq]; exact hg_keep k hk')
    rfl

/-- `Ret.seq_memcpy_disj`: `call memcpy(ed, es, en); cont` when `(dst, n)` and `(src, n)` are disjoint. -/
theorem Ret.seq_memcpy_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hs_nw : src.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hdisj : Disj (dst.toNat, n.toNat) (src.toNat, n.toNat))
    (hed : evalAt s ed = some (.val (.word dst)))
    (hes : evalAt s es = some (.val (.word src)))
    (hen : evalAt s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      ArenaReady s' →
      MemCopyRel s s' dst src n.toNat n.toNat →
      s'.locals = s.locals →
      Ret s' cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Φ := by
  refine Ret.seq_call3 hA.1.code
    (by decide) (by decide) (by decide) lookup_memcpy_fn dst src n hed hes hen ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := memcpy_body_spec entry dst src n hd_nw hs_nw hn_small hdisj
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "src" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨_, hrel⟩ := hspec
  let s_res := { post with locals := s.locals }
  have hrel_s : MemCopyRel s s_res dst src n.toNat n.toNat := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hrel
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩
  have hG_res : GuestInv s_res :=
    guestInv_congr hrel_s.1 hrel_s.2.1 hrel_s.2.2.1 hrel_s.2.2.2.1 hA.1
  have hA_res : ArenaReady s_res := by
    refine ⟨hG_res, ?_⟩
    have hg : s_res.globals = s.globals := hrel_s.2.2.2.2.2.1
    unfold ArenaOK globN
    rw [hg]
    exact hA.2
  exact hk s_res hA_res hrel_s rfl

/-- `Ret.seq_memcpy_frame`: `call memcpy(ed, es, en); cont` without `Disj` (frame-only). -/
theorem Ret.seq_memcpy_frame {F : Type} {s : PanSemStateFiniteExact 64 F}
    {ed es en : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hA : ArenaReady s)
    (dst src n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hed : evalAt s ed = some (.val (.word dst)))
    (hes : evalAt s es = some (.val (.word src)))
    (hen : evalAt s en = some (.val (.word n)))
    (hk : ∀ s' : PanSemStateFiniteExact 64 F,
      ArenaReady s' →
      MemCopyFrame s s' dst n.toNat →
      s'.locals = s.locals →
      Ret s' cont Φ) :
    Ret s (.seq (.call (some (none, none)) (ofString "memcpy") [ed, es, en]) cont) Φ := by
  refine Ret.seq_call3 hA.1.code
    (by decide) (by decide) (by decide) lookup_memcpy_fn dst src n hed hes hen ?_
  intro w post hrun
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst))).update
      (ofString "src", .val (.word src))).update (ofString "n", .val (.word n)))
  have hspec := memcpy_body_frame entry dst n hd_nw hn_small
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide])
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨_, hrel⟩ := hspec
  let s_res := { post with locals := s.locals }
  have hrel_s : MemCopyFrame s s_res dst n.toNat := by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hrel
    exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
  have hG_res : GuestInv s_res :=
    guestInv_congr hrel_s.1 hrel_s.2.1 hrel_s.2.2.1 hrel_s.2.2.2.1 hA.1
  have hA_res : ArenaReady s_res := by
    refine ⟨hG_res, ?_⟩
    have hg : s_res.globals = s.globals := hrel_s.2.2.2.2.2.1
    unfold ArenaOK globN
    rw [hg]
    exact hA.2
  exact hk s_res hA_res hrel_s rfl

/-! ## 2. `htab_grow` Postcondition -/

theorem htab_grow_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hB0 : HtabBlocks s0 tw.toNat)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_grow)
      (fun v post =>
        let t := tw.toNat
        let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
        v = .val (.word 0#64) ∧
        ArenaReady post ∧
        HtabBlocks post t ∧
        hdr post t 0 = hdr s0 t 0 ∧
        hdr post t 1 = hdr s0 t 1 ∧
        hdr post t 3 = hdr s0 t 3 ∧
        hdr post t 7 = hdr s0 t 7 ∧
        hdr post t 8 = hdr s0 t 8 ∧
        hdr post t 9 = hdr s0 t 9 ∧
        hdr post t 10 = 2 * hdr s0 t 10 ∧
        (∀ n, n < hdr s0 t 10 + 1 → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF post (hdr post t 5) n off = nodeF s0 (hdr s0 t 5) n off) ∧
        (∀ i, i < hdr s0 t 10 + 1 →
          memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
        globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
        (∀ i ∈ htabFootprint post t, Allocated post i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
        FrameOutside s0 post [(t, 88)] fresh ∧
        (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = post.globals.lookup k)) := by
  set t := tw.toNat
  obtain ⟨hncap_lt, hst_ge8, hst_le64, hst_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnc2 : 2 ≤ hdr s0 t 10 := hB0.2.2.2.2.2.1
  have hnx1 : 1 ≤ hdr s0 t 8 := hB0.2.2.2.2.2.2.1
  have hnx_le : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hhe : heapEnd = 33806089704 := rfl
  have hcMax_val : cMax.toNat = 2952790016 := rfl
  have hhl_val : heapLimit = 2952790016 := rfl
  have hkeys_in0 := (hB0.1 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) (by simp [htabFootprint]))
  have hnodes_in0 := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint]))
  have horder_in0 := (hB0.1 (hdr s0 t 6, (hdr s0 t 10 + 1) * 8) (by simp [htabFootprint]))
  have hhdr_al0 : Allocated s0 (t, 88) := hal0 (t, 88) (by simp [htabFootprint])
  have hkeys_al0 : Allocated s0 (hdr s0 t 4, (hdr s0 t 10 + 1) * hdr s0 t 1) := hal0 _ (by simp [htabFootprint])
  have hnodes_al0 : Allocated s0 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) := hal0 _ (by simp [htabFootprint])
  have horder_al0 : Allocated s0 (hdr s0 t 6, (hdr s0 t 10 + 1) * 8) := hal0 _ (by simp [htabFootprint])
  obtain ⟨hdom_t0, hm_t0⟩ := word_of_hdr s0 tw 0 (by omega) hB0
  obtain ⟨hdom_t1, hm_t1⟩ := word_of_hdr s0 tw 1 (by omega) hB0
  obtain ⟨hdom_t2, hm_t2⟩ := word_of_hdr s0 tw 2 (by omega) hB0
  obtain ⟨hdom_t3, hm_t3⟩ := word_of_hdr s0 tw 3 (by omega) hB0
  obtain ⟨hdom_t4, hm_t4⟩ := word_of_hdr s0 tw 4 (by omega) hB0
  obtain ⟨hdom_t5, hm_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom_t6, hm_t6⟩ := word_of_hdr s0 tw 6 (by omega) hB0
  obtain ⟨hdom_t7, hm_t7⟩ := word_of_hdr s0 tw 7 (by omega) hB0
  obtain ⟨hdom_t8, hm_t8⟩ := word_of_hdr s0 tw 8 (by omega) hB0
  obtain ⟨hdom_t9, hm_t9⟩ := word_of_hdr s0 tw 9 (by omega) hB0
  obtain ⟨hdom_t10, hm_t10⟩ := word_of_hdr s0 tw 10 (by omega) hB0
  set nodecap := hdr s0 t 10
  set ncap := 2 * nodecap
  set stride := hdr s0 t 1
  set old_keys := hdr s0 t 4
  set old_nodes := hdr s0 t 5
  set old_order := hdr s0 t 6
  have hw_nc0 : (BitVec.ofNat 64 nodecap).toNat = nodecap := by rw [BitVec.toNat_ofNat]; omega
  have hw_st : (BitVec.ofNat 64 stride).toNat = stride := by rw [BitVec.toNat_ofNat]; omega
  have hw_nc : (BitVec.ofNat 64 nodecap * 2#64).toNat = ncap := by
    rw [BitVec.toNat_mul, hw_nc0, show (2#64).toNat = 2 from rfl]; omega
  have hw_nc_eq : BitVec.ofNat 64 nodecap * 2#64 = BitVec.ofNat 64 ncap := by
    apply BitVec.eq_of_toNat_eq; rw [hw_nc, BitVec.toNat_ofNat]; omega
  htab_unfold Guest.Software.guestFn_htab_grow
  -- 1. dec nodecap := load(t + 80)
  apply Ret.dec; intro v_nc0 hv_nc0
  obtain ⟨_, rfl⟩ := ev_field_load s0 (ofString "t") tw 80 ht v_nc0 hv_nc0
  have hm80 : s0.memory (tw + 80) = .word (BitVec.ofNat 64 nodecap) := hm_t10
  rw [hm80]
  -- 2. dec ncap := nodecap * 2
  apply Ret.dec; intro v_nc hv_nc
  have hv_nc_eq : v_nc = .val (.word (BitVec.ofNat 64 ncap)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, panOpHOL, valueIsWord, valueWord, hw_nc_eq] at hv_nc
    exact hv_nc.symm
  subst hv_nc_eq
  -- 3. dec stride := load(t + 8)
  apply Ret.dec; intro v_st hv_st
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 8
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "ncap" ≠ ofString "t" by decide, show ofString "nodecap" ≠ ofString "t" by decide]) v_st hv_st
  have hm8 : s0.memory (tw + 8) = .word (BitVec.ofNat 64 stride) := hm_t1
  simp only [setVarHOLFinite] at *
  rw [hm8]
  let L0_3 : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((s0.locals.update (ofString "nodecap", .val (.word (BitVec.ofNat 64 nodecap)))).update
      (ofString "ncap", .val (.word (BitVec.ofNat 64 ncap)))).update
      (ofString "stride", .val (.word (BitVec.ofNat 64 stride)))
  let s0_3 : PanSemStateFiniteExact 64 F := { s0 with locals := L0_3 }
  have hb_mul1 : (ncap + 1) * stride < 2 ^ 64 := by
    have : 2 * nodecap + 1 ≤ 2000000000 := by omega
    have : (2 * nodecap + 1) * stride ≤ 2000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64
    dsimp only [ncap]; omega
  have hb_mul2 : (nodecap + 1) * stride < 2 ^ 64 := by
    have : (nodecap + 1) * stride ≤ 1000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64
    omega
  have hb_mul3 : (ncap + 1) * 32 < 2 ^ 64 := by dsimp only [ncap]; omega
  have hb_mul4 : (nodecap + 1) * 32 < 2 ^ 64 := by omega
  have hb_mul5 : (ncap + 1) * 8 < 2 ^ 64 := by dsimp only [ncap]; omega
  have hb_mul6 : (nodecap + 1) * 8 < 2 ^ 64 := by omega
  -- 4. decCall keys := alloc((ncap + 1) * stride)
  have harg_k : evalAt s0_3 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * stride)))) := by
    have h1 : s0_3.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      simp [s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "stride" ≠ ofString "ncap" by decide]
    have h2 : s0_3.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
      simp [s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE]
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, h1, h2,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    have hst_lt : stride < 2 ^ 64 := by omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt, Nat.mod_eq_of_lt hst_lt]
  refine Ret.decCall_alloc (s := s0_3) ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩
    (BitVec.ofNat 64 ((ncap + 1) * stride)) harg_k ?_
  intro kptr q1 s1 hkptr_nat hkptr_al hq1_lo hq1_hi hq1_al hA1 hgn1 hmem1 hbe1 hg1 hloc1
  have hkptr_s0 : kptr.toNat = globN s0 "heap_ptr" := hkptr_nat
  have hsz_k : (BitVec.ofNat 64 ((ncap + 1) * stride)).toNat = (ncap + 1) * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul1]
  rw [hsz_k] at hq1_lo
  -- 5. call memcpy(keys, load(t + 32), (nodecap + 1) * stride)
  set s1k := setVarHOLFinite (ofString "keys") (.val (.word kptr)) s1
  have hA1k : ArenaReady s1k := ⟨guestInv_congr (s := s1) rfl rfl rfl rfl hA1.1, hA1.2⟩
  have hsz_ok : (BitVec.ofNat 64 ((nodecap + 1) * stride)).toNat = (nodecap + 1) * stride := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul2]
  have he_kd : evalAt s1k (.var .local (ofString "keys")) = some (.val (.word kptr)) := by
    simp [s1k, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht_s1k : s1k.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "keys" ≠ ofString "t" by decide, show ofString "stride" ≠ ofString "t" by decide,
      show ofString "ncap" ≠ ofString "t" by decide, show ofString "nodecap" ≠ ofString "t" by decide]
  have hnc0_s1k : s1k.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "nodecap" by decide, show ofString "stride" ≠ ofString "nodecap" by decide,
      show ofString "ncap" ≠ ofString "nodecap" by decide]
  have hnc_s1k : s1k.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "ncap" by decide, show ofString "stride" ≠ ofString "ncap" by decide]
  have hst_s1k : s1k.locals.lookup (ofString "stride") = some (.val (.word (BitVec.ofNat 64 stride))) := by
    simp [s1k, setVarHOLFinite, hloc1, s0_3, L0_3, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "keys" ≠ ofString "stride" by decide]
  have he_ks : evalAt s1k (.load .one (.op .add [.var .local (ofString "t"), .const 32#64])) =
      some (.val (.word (BitVec.ofNat 64 old_keys))) := by
    have hdom32 : s1k.memaddrs (tw + 32#64) := by
      have : s1k.memaddrs = s0.memaddrs := hA1.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t4
    have hm32 : s1k.memory (tw + 32#64) = .word (BitVec.ofNat 64 old_keys) := by
      change s1.memory (tw + 32#64) = _; rw [hmem1]; exact hm_t4
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s1k,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom32, hm32]
  have he_kn : evalAt s1k (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .var .local (ofString "stride")]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * stride)))) := by
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc0_s1k, hst_s1k,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc0_lt : nodecap < 2 ^ 64 := by omega
    have hnc01_lt : nodecap + 1 < 2 ^ 64 := by omega
    have hst_lt : stride < 2 ^ 64 := by omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, show (1#64).toNat = 1 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc0_lt, Nat.mod_eq_of_lt hnc01_lt, Nat.mod_eq_of_lt hst_lt]
  have hle_ok_k : (nodecap + 1) * stride ≤ (ncap + 1) * stride := Nat.mul_le_mul_right stride (by dsimp only [ncap]; omega)
  refine Ret.seq_memcpy_frame hA1k kptr (BitVec.ofNat 64 old_keys) (BitVec.ofNat 64 ((nodecap + 1) * stride))
    (by rw [hsz_ok]; omega)
    (by rw [hsz_ok]; have : (nodecap + 1) * stride ≤ 1000000000 * 64 := Nat.mul_le_mul (by omega) hst_le64; omega)
    he_kd he_ks he_kn ?_
  intro s2 hA2 hmcf_k hloc2
  -- 6. store(t + 32, keys)
  have ht_s2 : s2.locals.lookup (ofString "t") = some (.val (.word tw)) := by rw [hloc2]; exact ht_s1k
  have hk_s2 : s2.locals.lookup (ofString "keys") = some (.val (.word kptr)) := by
    rw [hloc2]; simp [s1k, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 32#64) kptr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s2, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hk_s2]) ?_
  intro _
  set s3 := { s2 with memory := updW s2.memory (tw + 32#64) kptr }
  have hA3 : ArenaReady s3 := ⟨guestInv_congr (s := s2) rfl rfl rfl rfl hA2.1, hA2.2⟩
  -- 7. decCall nodes := alloc((ncap + 1) * 32)
  have harg_nd : evalAt s3 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 32#64]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * 32)))) := by
    have hnc_s3 : s3.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_s3,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (32#64).toNat = 32 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt]
  refine Ret.decCall_alloc hA3 (BitVec.ofNat 64 ((ncap + 1) * 32)) harg_nd ?_
  intro nptr q2 s4 hnptr_nat hnptr_al hq2_lo hq2_hi hq2_al hA4 hgn4 hmem4 hbe4 hg4 hloc4
  have hgn3 : globN s3 "heap_ptr" = q1.toNat := by
    change globN s2 "heap_ptr" = _
    have hg2 : s2.globals = s1k.globals := hmcf_k.2.2.2.2.2.1
    unfold globN at hgn1 ⊢; rw [hg2]; exact hgn1
  rw [hgn3] at hnptr_nat
  have hsz_nd : (BitVec.ofNat 64 ((ncap + 1) * 32)).toNat = (ncap + 1) * 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul3]
  rw [hsz_nd] at hq2_lo
  -- Frame of s3 relative to s0: only `(t, 88)` (at `t+32`) and `(kptr, (nodecap+1)*stride)` changed!
  have hfr_s0_s3 : FrameOutside s0 s3 [(t, 88)] (globN s0 "heap_ptr", q1.toNat - globN s0 "heap_ptr") := by
    have hfr_s0_s2 : FrameOutside s0 s2 [(t, 88)] (globN s0 "heap_ptr", q1.toNat - globN s0 "heap_ptr") := by
      intro x hxk hxf
      have hm2_1 : s2.memory x = s1k.memory x := by
        apply hmcf_k.2.2.2.2.2.2 x
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          apply hxf
          exact cellHits_of_inside hhit ⟨by omega, by omega⟩
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; exact congrFun hmem1 x
    have htw32 : (tw + 32#64).toNat = t + 32 := by
      rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl]; omega
    exact frameOutside_trans_same hfr_s0_s2
      (frameOutside_updW s2 (tw + 32#64) kptr [(t, 88)] _
        (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- Check that `load(t + 40)` in `s4` still reads `old_nodes`, and `old_nodes` words are untouched!
  set s4n := setVarHOLFinite (ofString "nodes") (.val (.word nptr)) s4
  have hA4n : ArenaReady s4n := ⟨guestInv_congr (s := s4) rfl rfl rfl rfl hA4.1, hA4.2⟩
  have hsz_ond : (BitVec.ofNat 64 ((nodecap + 1) * 32)).toNat = (nodecap + 1) * 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul4]
  have hw_ond : (BitVec.ofNat 64 old_nodes).toNat = old_nodes := by
    rw [BitVec.toNat_ofNat]; unfold Inside at hnodes_in0; omega
  have hdisj_nd : Disj (nptr.toNat, (nodecap + 1) * 32) (old_nodes, (nodecap + 1) * 32) := by
    have hd := disj_fresh_ivl hA0 hnodes_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
    dsimp only [ncap] at hq2_lo
    unfold Disj at hd ⊢; omega
  have he_nd_d : evalAt s4n (.var .local (ofString "nodes")) = some (.val (.word nptr)) := by
    simp [s4n, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have he_nd_s : evalAt s4n (.load .one (.op .add [.var .local (ofString "t"), .const 40#64])) =
      some (.val (.word (BitVec.ofNat 64 old_nodes))) := by
    have ht_s4n : s4n.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s4n, setVarHOLFinite, hloc4, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "t" by decide]
      exact ht_s2
    have hdom40 : s4n.memaddrs (tw + 40#64) := by
      have : s4n.memaddrs = s0.memaddrs := hA4.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t5
    have hne40_32 : tw + 40#64 ≠ tw + 32#64 := by
      intro he; have := congrArg BitVec.toNat he
      rw [BitVec.toNat_add, BitVec.toNat_add, show (40#64).toNat = 40 from rfl, show (32#64).toNat = 32 from rfl] at this
      omega
    have hm40 : s4n.memory (tw + 40#64) = .word (BitVec.ofNat 64 old_nodes) := by
      change s4.memory (tw + 40#64) = _; rw [hmem4]
      simp only [s3, updW, hne40_32, ↓reduceIte]
      have hm2_1 : s2.memory (tw + 40#64) = s1k.memory (tw + 40#64) := by
        apply hmcf_k.2.2.2.2.2.2 (tw + 40#64)
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
          have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
          rw [htw40] at hhit
          obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; change s1.memory _ = _; rw [hmem1]; exact hm_t5
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s4n,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom40, hm40]
  have he_nd_n : evalAt s4n (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 32#64]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * 32)))) := by
    have hnc_l : s4n.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc0_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (32#64).toNat = 32 from rfl, hz0, Nat.add_zero]
    omega
  -- 8. call memcpy(nodes, load(t + 40), (nodecap + 1) * 32)
  refine Ret.seq_memcpy_disj hA4n nptr (BitVec.ofNat 64 old_nodes) (BitVec.ofNat 64 ((nodecap + 1) * 32))
    (by rw [hsz_ond]; dsimp only [ncap] at hq2_lo; omega)
    (by rw [hw_ond, hsz_ond]; unfold Inside at hnodes_in0; omega)
    (by rw [hsz_ond]; omega)
    (by rw [hw_ond, hsz_ond]; exact hdisj_nd)
    he_nd_d he_nd_s he_nd_n ?_
  intro s5 hA5 hrel_nd hloc5
  -- 9. store(t + 40, nodes)
  have ht_s5 : s5.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hloc5]; simp [s4n, setVarHOLFinite, hloc4, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "t" by decide]; exact ht_s2
  have hnd_s5 : s5.locals.lookup (ofString "nodes") = some (.val (.word nptr)) := by
    rw [hloc5]; simp [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 40#64) nptr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s5, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hnd_s5]) ?_
  intro _
  set s6 := { s5 with memory := updW s5.memory (tw + 40#64) nptr }
  have hA6 : ArenaReady s6 := ⟨guestInv_congr (s := s5) rfl rfl rfl rfl hA5.1, hA5.2⟩
  -- 10. decCall order := alloc((ncap + 1) * 8)
  have harg_ord : evalAt s6 (.panop .mul [.op .add [.var .local (ofString "ncap"), .const 1#64], .const 8#64]) =
      some (.val (.word (BitVec.ofNat 64 ((ncap + 1) * 8)))) := by
    have hnc_s6 : s6.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
      change s5.locals.lookup _ = _; rw [hloc5]
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "ncap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_s6,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    have hnc_lt : ncap < 2 ^ 64 := by dsimp only [ncap]; omega
    have hnc1_lt : ncap + 1 < 2 ^ 64 := by dsimp only [ncap]; omega
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (8#64).toNat = 8 from rfl, hz0, Nat.add_zero]
    have h1m : 1 % 2 ^ 64 = 1 := rfl
    rw [h1m, Nat.mod_eq_of_lt hnc_lt, Nat.mod_eq_of_lt hnc1_lt]
  refine Ret.decCall_alloc hA6 (BitVec.ofNat 64 ((ncap + 1) * 8)) harg_ord ?_
  intro optr q3 s7 hoptr_nat hoptr_al hq3_lo hq3_hi hq3_al hA7 hgn7 hmem7 hbe7 hg7 hloc7
  have hgn6 : globN s6 "heap_ptr" = q2.toNat := by
    change globN s5 "heap_ptr" = _
    have hg5 : s5.globals = s4n.globals := hrel_nd.2.2.2.2.2.1
    unfold globN at hgn4 ⊢; rw [hg5]; exact hgn4
  rw [hgn6] at hoptr_nat
  have hsz_ord : (BitVec.ofNat 64 ((ncap + 1) * 8)).toNat = (ncap + 1) * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul5]
  rw [hsz_ord] at hq3_lo
  have hfr_s0_s6 : FrameOutside s0 s6 [(t, 88)] (globN s0 "heap_ptr", q2.toNat - globN s0 "heap_ptr") := by
    have hfr_s0_s5 : FrameOutside s0 s5 [(t, 88)] (globN s0 "heap_ptr", q2.toNat - globN s0 "heap_ptr") := by
      intro x hxk hxf
      have hm5_4 : s5.memory x = s4n.memory x := by
        apply hrel_nd.2.2.2.2.2.2.1 x
        · intro i hi hhit
          rw [List.mem_singleton.mp hi, hsz_ond] at hhit
          dsimp only [ncap] at hq2_lo
          exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
        · intro ⟨_, h2⟩; omega
      rw [hm5_4]; change s4.memory x = _; rw [hmem4]
      apply hfr_s0_s3 x hxk
      intro hhit; exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
    have htw40 : (tw + 40#64).toNat = t + 40 := by
      rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    exact frameOutside_trans_same hfr_s0_s5
      (frameOutside_updW s5 (tw + 40#64) nptr [(t, 88)] _
        (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- 11. call memcpy(order, load(t + 48), (nodecap + 1) * 8)
  set s7o := setVarHOLFinite (ofString "order") (.val (.word optr)) s7
  have hA7o : ArenaReady s7o := ⟨guestInv_congr (s := s7) rfl rfl rfl rfl hA7.1, hA7.2⟩
  have hsz_oord : (BitVec.ofNat 64 ((nodecap + 1) * 8)).toNat = (nodecap + 1) * 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_mul6]
  have hw_oord : (BitVec.ofNat 64 old_order).toNat = old_order := by
    rw [BitVec.toNat_ofNat]; unfold Inside at horder_in0; omega
  have hdisj_ord : Disj (optr.toNat, (nodecap + 1) * 8) (old_order, (nodecap + 1) * 8) := by
    have hd := disj_fresh_ivl hA0 horder_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
    dsimp only [ncap] at hq3_lo
    unfold Disj at hd ⊢; omega
  have he_ord_d : evalAt s7o (.var .local (ofString "order")) = some (.val (.word optr)) := by
    simp [s7o, evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have he_ord_s : evalAt s7o (.load .one (.op .add [.var .local (ofString "t"), .const 48#64])) =
      some (.val (.word (BitVec.ofNat 64 old_order))) := by
    have ht_s7o : s7o.locals.lookup (ofString "t") = some (.val (.word tw)) := by
      simp [s7o, setVarHOLFinite, hloc7, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "order" ≠ ofString "t" by decide]
      exact ht_s5
    have hdom48 : s7o.memaddrs (tw + 48#64) := by
      have : s7o.memaddrs = s0.memaddrs := hA7.1.memaddrs.trans hA0.1.memaddrs.symm
      rw [this]; exact hdom_t6
    have hm48 : s7o.memory (tw + 48#64) = .word (BitVec.ofNat 64 old_order) := by
      change s7.memory (tw + 48#64) = _; rw [hmem7]
      have hne48_40 : tw + 48#64 ≠ tw + 40#64 := by
        intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_add, BitVec.toNat_add, show (48#64).toNat = 48 from rfl, show (40#64).toNat = 40 from rfl] at this; omega
      have hne48_32 : tw + 48#64 ≠ tw + 32#64 := by
        intro he; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_add, BitVec.toNat_add, show (48#64).toNat = 48 from rfl, show (32#64).toNat = 32 from rfl] at this; omega
      simp only [s6, updW, hne48_40, ↓reduceIte]
      have hm5_4 : s5.memory (tw + 48#64) = s4n.memory (tw + 48#64) := by
        apply hrel_nd.2.2.2.2.2.2.1 (tw + 48#64)
        · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
          have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
          rw [htw48] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; dsimp only [ncap] at hq2_lo; omega
        · intro ⟨_, h2⟩; omega
      rw [hm5_4]; change s4.memory _ = _; rw [hmem4]
      simp only [s3, updW, hne48_32, ↓reduceIte]
      have hm2_1 : s2.memory (tw + 48#64) = s1k.memory (tw + 48#64) := by
        apply hmcf_k.2.2.2.2.2.2 (tw + 48#64)
        · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ok] at hhit
          have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
          have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
          rw [htw48] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
        · intro ⟨_, h2⟩; omega
      rw [hm2_1]; change s1.memory _ = _; rw [hmem1]; exact hm_t6
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s7o,
      valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact, hdom48, hm48]
  have he_ord_n : evalAt s7o (.panop .mul [.op .add [.var .local (ofString "nodecap"), .const 1#64], .const 8#64]) =
      some (.val (.word (BitVec.ofNat 64 ((nodecap + 1) * 8)))) := by
    have hnc_l : s7o.locals.lookup (ofString "nodecap") = some (.val (.word (BitVec.ofNat 64 nodecap))) := by
      simp only [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "order" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc7]; change s5.locals.lookup _ = _; rw [hloc5]
      simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nodes" ≠ ofString "nodecap" by decide, ↓reduceIte]
      rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc0_s1k
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hnc_l,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (1#64).toNat = 1 from rfl, show (8#64).toNat = 8 from rfl, hz0, Nat.add_zero]
    omega
  refine Ret.seq_memcpy_disj hA7o optr (BitVec.ofNat 64 old_order) (BitVec.ofNat 64 ((nodecap + 1) * 8))
    (by rw [hsz_oord]; dsimp only [ncap] at hq3_lo; omega)
    (by rw [hw_oord, hsz_oord]; unfold Inside at horder_in0; omega)
    (by rw [hsz_oord]; omega)
    (by rw [hw_oord, hsz_oord]; exact hdisj_ord)
    he_ord_d he_ord_s he_ord_n ?_
  intro s8 hA8 hrel_ord hloc8
  -- 12. store(t + 48, order)
  have ht_s8 : s8.locals.lookup (ofString "t") = some (.val (.word tw)) := by
    rw [hloc8]; simp [s7o, setVarHOLFinite, hloc7, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "order" ≠ ofString "t" by decide]; exact ht_s5
  have hord_s8 : s8.locals.lookup (ofString "order") = some (.val (.word optr)) := by
    rw [hloc8]; simp [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine Ret.seq_storeW (tw + 48#64) optr
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hord_s8]) ?_
  intro _
  set s9 := { s8 with memory := updW s8.memory (tw + 48#64) optr }
  -- 13. store(t + 16, load(t + 16) * 2)
  have hdom16_s9 : s9.memaddrs (tw + 16#64) := by
    have : s9.memaddrs = s0.memaddrs := hA8.1.memaddrs.trans hA0.1.memaddrs.symm
    rw [this]; exact hdom_t2
  rcases hm16_s9 : s9.memory (tw + 16#64) with ⟨capw⟩
  refine Ret.seq_storeW (tw + 16#64) (capw * 2#64)
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s9.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s9.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, memLoadHOLExact, hdom16_s9, hm16_s9]) ?_
  intro _
  set s10 := { s9 with memory := updW s9.memory (tw + 16#64) (capw * 2#64) }
  -- 14. store(t + 80, ncap)
  have hnc_s10 : s10.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 ncap))) := by
    change s8.locals.lookup _ = _; rw [hloc8]
    simp only [s7o, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "order" ≠ ofString "ncap" by decide, ↓reduceIte]
    rw [hloc7]; change s5.locals.lookup _ = _; rw [hloc5]
    simp only [s4n, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nodes" ≠ ofString "ncap" by decide, ↓reduceIte]
    rw [hloc4]; change s2.locals.lookup _ = _; rw [hloc2]; exact hnc_s1k
  refine Ret.seq_storeW (tw + 80#64) (BitVec.ofNat 64 ncap)
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
          show s10.locals.lookup (ofString "t") = some (.val (.word tw)) from ht_s8, valueIsWord, valueWord, wordOpHOL, wordOp])
    (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hnc_s10]) ?_
  intro _
  set s11 := { s10 with memory := updW s10.memory (tw + 80#64) (BitVec.ofNat 64 ncap) }
  -- 15. return 0
  apply Ret.ret
  intro val hval
  have hval0 : val = .val (.word 0#64) := by simp [evalAt, evalHOLExact] at hval; exact hval.symm
  subst hval0
  -- Note: the final post-state `pEnd` has the same `memory`, `globals`, `code`, `memaddrs`, `shMemaddrs`, `baseAddr`, `be` as `s11`!
  -- Let's prove our postconditions on `s11` first, and since every conjunct is independent of `locals` and `clock`, transfer immediately!
  have hA11 : ArenaReady s11 := ⟨guestInv_congr (s := s8) rfl rfl rfl rfl hA8.1, hA8.2⟩
  have hgn11 : globN s11 "heap_ptr" = q3.toNat := by
    change globN s8 "heap_ptr" = _
    have hg8 : s8.globals = s7o.globals := hrel_ord.2.2.2.2.2.1
    unfold globN at hgn7 ⊢; rw [hg8]; exact hgn7
  have hncap_eq : ncap = 2 * nodecap := rfl
  have hgn1 : globN s1 "heap_ptr" = q1.toNat := hgn1
  have hgn4 : globN s4 "heap_ptr" = q2.toNat := hgn4
  have hgn7 : globN s7 "heap_ptr" = q3.toNat := hgn7
  have hg_all : ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = s11.globals.lookup k := by
    intro k hk'
    have e1 := hg1 k hk'
    have e2 : s1k.globals.lookup k = s2.globals.lookup k := congrArg (fun g => g.lookup k) hmcf_k.2.2.2.2.2.1.symm
    have e4 := hg4 k hk'
    have e5 : s4n.globals.lookup k = s5.globals.lookup k := congrArg (fun g => g.lookup k) hrel_nd.2.2.2.2.2.1.symm
    have e7 := hg7 k hk'
    have e8 : s7o.globals.lookup k = s8.globals.lookup k := congrArg (fun g => g.lookup k) hrel_ord.2.2.2.2.2.1.symm
    exact e1.trans (e2.trans (e4.trans (e5.trans (e7.trans e8))))
  -- Frame of s11 relative to s0:
  have hfr_s0_s8 : FrameOutside s0 s8 [(t, 88)] (globN s0 "heap_ptr", q3.toNat - globN s0 "heap_ptr") := by
    intro x hxk hxf
    have hm8_7 : s8.memory x = s7o.memory x := by
      apply hrel_ord.2.2.2.2.2.2.1 x
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change s7.memory x = _; rw [hmem7]
    apply hfr_s0_s6 x hxk
    intro hhit; exact hxf (cellHits_of_inside hhit ⟨by omega, by omega⟩)
  have htw48 : (tw + 48#64).toNat = t + 48 := by rw [BitVec.toNat_add, show (48#64).toNat = 48 from rfl]; omega
  have htw16 : (tw + 16#64).toNat = t + 16 := by rw [BitVec.toNat_add, show (16#64).toNat = 16 from rfl]; omega
  have htw80 : (tw + 80#64).toNat = t + 80 := by rw [BitVec.toNat_add, show (80#64).toNat = 80 from rfl]; omega
  have hfr_s0_s9 := frameOutside_trans_same hfr_s0_s8
    (frameOutside_updW s8 (tw + 48#64) optr [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  have hfr_s0_s10 := frameOutside_trans_same hfr_s0_s9
    (frameOutside_updW s9 (tw + 16#64) (capw * 2#64) [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  have hfr_s0_s11 := frameOutside_trans_same hfr_s0_s10
    (frameOutside_updW s10 (tw + 80#64) (BitVec.ofNat 64 ncap) [(t, 88)] _
      (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
  -- Helper: header word `tw + 8*k` for `k ∉ {2, 4, 5, 6, 10}` is untouched across all steps!
  have hdr_unchanged : ∀ k : Nat, k < 11 → k ≠ 2 → k ≠ 4 → k ≠ 5 → k ≠ 6 → k ≠ 10 →
      hdr s11 t k = hdr s0 t k := by
    intro k hklt hk2 hk4 hk5 hk6 hk10
    have haddr_eq : BitVec.ofNat 64 (t + 8 * k) = tw + BitVec.ofNat 64 (8 * k) := ofNat_add_toNat tw (8 * k)
    have hne : ∀ j : Nat, j < 11 → j ≠ k → BitVec.ofNat 64 (t + 8 * k) ≠ tw + BitVec.ofNat 64 (8 * j) := by
      intro j hjlt hjk heq
      rw [← ofNat_add_toNat tw (8 * j)] at heq
      have := ofNat64_eq_of_lt (by omega) (by omega) heq
      omega
    have hne10 := hne 10 (by omega) (Ne.symm hk10)
    have hne2 := hne 2 (by omega) (Ne.symm hk2)
    have hne6 := hne 6 (by omega) (Ne.symm hk6)
    have hne5 := hne 5 (by omega) (Ne.symm hk5)
    have hne4 := hne 4 (by omega) (Ne.symm hk4)
    unfold hdr memW
    have hm11_8 : s11.memory (BitVec.ofNat 64 (t + 8 * k)) = s8.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s11, s10, s9, updW]
      rw [if_neg hne10, if_neg hne2, if_neg hne6]
    have hm8_7 : s8.memory (BitVec.ofNat 64 (t + 8 * k)) = s7o.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    have hm6_5 : s6.memory (BitVec.ofNat 64 (t + 8 * k)) = s5.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s6, updW]; rw [if_neg hne5]
    have hm5_4 : s5.memory (BitVec.ofNat 64 (t + 8 * k)) = s4n.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hrel_nd.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    have hm3_2 : s3.memory (BitVec.ofNat 64 (t + 8 * k)) = s2.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      simp only [s3, updW]; rw [if_neg hne4]
    have hm2_1 : s2.memory (BitVec.ofNat 64 (t + 8 * k)) = s1k.memory (BitVec.ofNat 64 (t + 8 * k)) := by
      apply hmcf_k.2.2.2.2.2.2
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ok] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
        have hb : (BitVec.ofNat 64 (t + 8 * k)).toNat = t + 8 * k := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm11_8, hm8_7]
    change (match s7.memory _ with | .word w => w.toNat) = _
    rw [hmem7, hm6_5, hm5_4]
    change (match s4.memory _ with | .word w => w.toNat) = _
    rw [hmem4, hm3_2, hm2_1]
    change (match s1.memory _ with | .word w => w.toNat) = _
    rw [hmem1]
  have hh0 : hdr s11 t 0 = hdr s0 t 0 := hdr_unchanged 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh1 : hdr s11 t 1 = stride := hdr_unchanged 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh3 : hdr s11 t 3 = hdr s0 t 3 := hdr_unchanged 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh7 : hdr s11 t 7 = hdr s0 t 7 := hdr_unchanged 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh8 : hdr s11 t 8 = hdr s0 t 8 := hdr_unchanged 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh9 : hdr s11 t 9 = hdr s0 t 9 := hdr_unchanged 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hh10 : hdr s11 t 10 = ncap := by
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 10)]
    have : tw + BitVec.ofNat 64 (8 * 10) = tw + 80#64 := rfl
    rw [this]; simp only [s11, updW, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hh6 : hdr s11 t 6 = optr.toNat := by
    have hne10 : tw + 48#64 ≠ tw + 80#64 := by
      intro he; have := congrArg BitVec.toNat he; rw [htw48, htw80] at this; omega
    have hne2 : tw + 48#64 ≠ tw + 16#64 := by
      intro he; have := congrArg BitVec.toNat he; rw [htw48, htw16] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 6)]
    have : tw + BitVec.ofNat 64 (8 * 6) = tw + 48#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, ↓reduceIte]
  have hh5 : hdr s11 t 5 = nptr.toNat := by
    have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    have hne10 : tw + 40#64 ≠ tw + 80#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw80] at this; omega
    have hne2 : tw + 40#64 ≠ tw + 16#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw16] at this; omega
    have hne6 : tw + 40#64 ≠ tw + 48#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw40, htw48] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 5)]
    have : tw + BitVec.ofNat 64 (8 * 5) = tw + 40#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, hne6, ↓reduceIte]
    have hm8_7 : s8.memory (tw + 40#64) = s7o.memory (tw + 40#64) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        rw [htw40] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7]
    simp [s6, updW]
  have hh4 : hdr s11 t 4 = kptr.toNat := by
    have htw32 : (tw + 32#64).toNat = t + 32 := by rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl]; omega
    have htw40 : (tw + 40#64).toNat = t + 40 := by rw [BitVec.toNat_add, show (40#64).toNat = 40 from rfl]; omega
    have hne10 : tw + 32#64 ≠ tw + 80#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw80] at this; omega
    have hne2 : tw + 32#64 ≠ tw + 16#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw16] at this; omega
    have hne6 : tw + 32#64 ≠ tw + 48#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw48] at this; omega
    have hne5 : tw + 32#64 ≠ tw + 40#64 := by intro he; have := congrArg BitVec.toNat he; rw [htw32, htw40] at this; omega
    unfold hdr memW
    rw [ofNat_add_toNat tw (8 * 4)]
    have : tw + BitVec.ofNat 64 (8 * 4) = tw + 32#64 := rfl
    rw [this]; simp only [s11, s10, s9, updW, hne10, hne2, hne6, ↓reduceIte]
    have hm8_7 : s8.memory (tw + 32#64) = s7o.memory (tw + 32#64) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
        rw [htw32] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7]
    simp only [s6, updW, hne5, ↓reduceIte]
    have hm5_4 : s5.memory (tw + 32#64) = s4n.memory (tw + 32#64) := by
      apply hrel_nd.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_ond] at hhit
        have hd := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
        rw [htw32] at hhit; obtain ⟨h1, h2⟩ := hhit; unfold Disj at hd; omega
      · intro ⟨_, h2⟩; omega
    rw [hm5_4]; change (match s4.memory _ with | .word w => w.toNat) = _; rw [hmem4]
    simp [s3, updW]
  -- Copied node fields: for `n < nodecap + 1`, `nodeF s11 nptr.toNat n off = nodeF s0 old_nodes n off`!
  have hnodes_copied : ∀ n, n < nodecap + 1 → ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF s11 nptr.toNat n off = nodeF s0 old_nodes n off := by
    intro n hn_lt off hoff
    unfold nodeF
    set a := nptr.toNat + 32 * n + off
    have ha_al : a % 8 = 0 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [a] <;> omega
    have ha_hi : a + 8 ≤ nptr.toNat + (nodecap + 1) * 32 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [a] <;> omega
    -- `a` is in `[nptr, q2)`, disjoint from `(t, 88)` and `[optr, q3)`!
    have hd_hdr := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
    have hm11_8 : s11.memory (BitVec.ofNat 64 a) = s8.memory (BitVec.ofNat 64 a) := by
      have hne : ∀ off_t : BitVec 64, off_t.toNat < 88 → BitVec.ofNat 64 a ≠ tw + off_t := by
        intro off_t hoff_t heq
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp only [s11, s10, s9, updW, hne 80#64 (by decide), hne 16#64 (by decide), hne 48#64 (by decide), ↓reduceIte]
    have hm8_7 : s8.memory (BitVec.ofNat 64 a) = s7o.memory (BitVec.ofNat 64 a) := by
      apply hrel_ord.2.2.2.2.2.2.1
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hsz_oord] at hhit
        have hb : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
        rw [hb] at hhit; obtain ⟨h1, h2⟩ := hhit; omega
      · intro ⟨_, h2⟩; omega
    have hm6_5 : s6.memory (BitVec.ofNat 64 a) = s5.memory (BitVec.ofNat 64 a) := by
      have hne40 : BitVec.ofNat 64 a ≠ tw + 40#64 := by
        intro heq; have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, show (40#64).toNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp [s6, updW, hne40]
    have hm11_5 : memW s11 a = memW s5 a := by
      unfold memW; rw [hm11_8, hm8_7]; change (match s7.memory _ with | .word w => w.toNat) = _; rw [hmem7, hm6_5]
    rw [hm11_5]
    -- Now use `memW_copied_of_memCopyRel` on `hrel_nd : MemCopyRel s4n s5 nptr (BitVec.ofNat 64 old_nodes) ((nodecap+1)*32) ((nodecap+1)*32)`!
    have hsz_eq : (BitVec.ofNat 64 ((nodecap + 1) * 32)).toNat = (nodecap + 1) * 32 := hsz_ond
    have hrel_nd' : MemCopyRel s4n s5 nptr (BitVec.ofNat 64 old_nodes) ((nodecap + 1) * 32) ((nodecap + 1) * 32) := by
      rw [← hsz_eq]; exact hrel_nd
    have ha_eq : a = nptr.toNat + (32 * n + off) := by dsimp [a]; omega
    have hcp := memW_copied_of_memCopyRel (off := 32 * n + off) hrel_nd' hnptr_al
      (by rw [hw_ond]; exact hnodes_in0.2.1)
      (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
      (by dsimp only [ncap] at hq2_lo; omega) (by rw [hw_ond]; unfold Inside at hnodes_in0; omega)
    rw [ha_eq, hcp, hw_ond]
    -- Finally, `memW s4n (old_nodes + (32 * n + off)) = memW s0 (old_nodes + 32 * n + off)` by `hfr_s0_s3`!
    have hb_eq : old_nodes + (32 * n + off) = old_nodes + 32 * n + off := by omega
    rw [hb_eq]
    change memW s4 (old_nodes + 32 * n + off) = _
    unfold memW; rw [hmem4]
    have hm3_0 : s3.memory (BitVec.ofNat 64 (old_nodes + 32 * n + off)) = s0.memory (BitVec.ofNat 64 (old_nodes + 32 * n + off)) := by
      have hb_nat : (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat = old_nodes + 32 * n + off := by
        rw [BitVec.toNat_ofNat]; unfold Inside at hnodes_in0
        rcases hoff with rfl | rfl | rfl | rfl <;> omega
      apply hfr_s0_s3
      · intro i hi hhit; rw [List.mem_singleton.mp hi, hb_nat] at hhit
        have hpair := hB0.2.1; simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
        have hd_tn : Disj (t, 88) (old_nodes, (nodecap + 1) * 32) := hpair.1 _ (Or.inr (Or.inl rfl))
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_tn
        rcases hoff with rfl | rfl | rfl | rfl <;> omega
      · intro hhit
        have c1 : globN s0 "heap_ptr" < (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat + 8 := hhit.1
        have c2 : (BitVec.ofNat 64 (old_nodes + 32 * n + off)).toNat < globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") := hhit.2
        have c1' : globN s0 "heap_ptr" < old_nodes + 32 * n + off + 8 := hb_nat ▸ c1
        have c2' : old_nodes + 32 * n + off < globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") := hb_nat ▸ c2
        have hd_fn := disj_fresh_of_allocated hA0 hnodes_al0 (lo := globN s0 "heap_ptr") (hi := q1.toNat) le_rfl (by omega)
        have hpos_q1 : globN s0 "heap_ptr" < q1.toNat := by
          have : 0 < (ncap + 1) * stride := Nat.mul_pos (by dsimp [ncap]; omega) (by omega)
          omega
        rcases hd_fn with hz | hle_bad | hle | hle
        · change (hdr s0 t 10 + 1) * 32 = 0 at hz; omega
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hpos_q1 hle_bad)
        · change globN s0 "heap_ptr" + (q1.toNat - globN s0 "heap_ptr") ≤ hdr s0 t 5 at hle
          have hsub : hdr s0 t 5 ≤ old_nodes + 32 * n + off := by
            change old_nodes ≤ (old_nodes + 32 * n) + off
            exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le c2' (Nat.le_trans hle hsub))
        · change hdr s0 t 5 + (hdr s0 t 10 + 1) * 32 ≤ globN s0 "heap_ptr" at hle
          have hsub : old_nodes + 32 * n + off + 8 ≤ hdr s0 t 5 + (hdr s0 t 10 + 1) * 32 := by
            change hdr s0 t 5 + 32 * n + off + 8 ≤ hdr s0 t 5 + (nodecap + 1) * 32
            rcases hoff with rfl | rfl | rfl | rfl <;> omega
          exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le c1' (Nat.le_trans hsub hle))
    rw [hm3_0]
  -- Copied order words: for `i < nodecap + 1`, `memW s11 (optr.toNat + 8 * i) = memW s0 (old_order + 8 * i)`!
  have horder_copied : ∀ i, i < nodecap + 1 →
      memW s11 (optr.toNat + 8 * i) = memW s0 (old_order + 8 * i) := by
    intro i hi_lt
    set a := optr.toNat + 8 * i
    have hd_hdr := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
    have hm11_8 : s11.memory (BitVec.ofNat 64 a) = s8.memory (BitVec.ofNat 64 a) := by
      have hne : ∀ off_t : BitVec 64, off_t.toNat < 88 → BitVec.ofNat 64 a ≠ tw + off_t := by
        intro off_t hoff_t heq
        have := congrArg BitVec.toNat heq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at this
        unfold Disj at hd_hdr; omega
      simp only [s11, s10, s9, updW, hne 80#64 (by decide), hne 16#64 (by decide), hne 48#64 (by decide), ↓reduceIte]
    have hm11_8w : memW s11 a = memW s8 a := by unfold memW; rw [hm11_8]
    rw [hm11_8w]
    have hrel_ord' : MemCopyRel s7o s8 optr (BitVec.ofNat 64 old_order) ((nodecap + 1) * 8) ((nodecap + 1) * 8) := by
      rw [← hsz_oord]; exact hrel_ord
    have hcp := memW_copied_of_memCopyRel (off := 8 * i) hrel_ord' hoptr_al
      (by rw [hw_oord]; exact horder_in0.2.1)
      (by omega) (by omega) (by omega) (by rw [hw_oord]; unfold Inside at horder_in0; omega)
    rw [show a = optr.toNat + 8 * i from rfl, hcp, hw_oord]
    change memW s7 (old_order + 8 * i) = _
    unfold memW; rw [hmem7]
    have hm6_0 : s6.memory (BitVec.ofNat 64 (old_order + 8 * i)) = s0.memory (BitVec.ofNat 64 (old_order + 8 * i)) := by
      have hb_nat : (BitVec.ofNat 64 (old_order + 8 * i)).toNat = old_order + 8 * i := by
        rw [BitVec.toNat_ofNat]; unfold Inside at horder_in0; omega
      apply hfr_s0_s6
      · intro iv hiv hhit; rw [List.mem_singleton.mp hiv, hb_nat] at hhit
        have hpair := hB0.2.1; simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
        have hd_to : Disj (t, 88) (old_order, (nodecap + 1) * 8) := hpair.1 _ (Or.inr (Or.inr (Or.inl rfl)))
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_to; omega
      · intro hhit; rw [hb_nat] at hhit
        have hd_fo := disj_fresh_ivl hA0 horder_al0 (lo := globN s0 "heap_ptr") (hi := q2.toNat) (by omega) (by omega)
        obtain ⟨c1, c2⟩ := hhit; unfold Disj at hd_fo; omega
    rw [hm6_0]
  -- `HtabBlocks s11 t`:
  have hsb_val : sourceBase = 2701131776 := rfl
  have hhp0_lo : sourceBase ≤ globN s0 "heap_ptr" := hA0.2.1
  have hB11 : HtabBlocks s11 t := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro iv hiv
      simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl | rfl
      · exact ⟨⟨ht_lo, ht_hi⟩, wordsOK_block s11 hA11.1.memaddrs t 88 ht_al (by omega) ht_lo ht_hi⟩
      · have hmul_le : (ncap + 1) * stride ≤ q1.toNat - kptr.toNat := by omega
        exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs kptr.toNat ((ncap + 1) * stride) hkptr_al (Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right (Nat.dvd_iff_mod_eq_zero.mpr hst_al) _)) (by omega) (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs nptr.toNat ((ncap + 1) * 32) hnptr_al (by omega) (by omega) (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, wordsOK_block s11 hA11.1.memaddrs optr.toNat ((ncap + 1) * 8) hoptr_al (by omega) (by omega) (by omega)⟩
    · simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true]
      have hd_tk := disj_fresh_ivl hA0 hhdr_al0 (lo := kptr.toNat) (hi := q1.toNat) (by omega) (by omega)
      have hd_tn := disj_fresh_ivl hA0 hhdr_al0 (lo := nptr.toNat) (hi := q2.toNat) (by omega) (by omega)
      have hd_to := disj_fresh_ivl hA0 hhdr_al0 (lo := optr.toNat) (hi := q3.toNat) (by omega) (by omega)
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, fun _ h => False.elim h⟩
      · unfold Disj at hd_tk ⊢; omega
      · unfold Disj at hd_tn ⊢; omega
      · unfold Disj at hd_to ⊢; omega
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
    · rw [hh0]; exact hB0.2.2.1
    · rw [hh0]; exact hB0.2.2.2.1
    · rw [hh1, hh0]; exact hB0.2.2.2.2.1
    · rw [hh10]; omega
    · rw [hh8]; exact hnx1
    · rw [hh8, hh10]; omega
  -- Footprint allocation + provenance in `s11`:
  have hfp11 : ∀ iv ∈ htabFootprint s11 t, Allocated s11 iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (q3.toNat - globN s0 "heap_ptr"))) := by
    have hgrows : AllocatorGrows s0 s11 := by
      refine ⟨by rw [hgn11]; omega, ?_⟩
      have hsp := hg_all (ofString "scratch_ptr") (by simp [show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide])
      unfold globN; rw [← hsp]
    intro iv hiv
    simp only [htabFootprint, hh4, hh5, hh6, hh10, hh1, List.mem_cons, List.not_mem_nil, or_false] at hiv
    rcases hiv with rfl | rfl | rfl | rfl
    · exact ⟨hgrows.allocated hhdr_al0, Or.inl ⟨(t, 88), by simp [htabFootprint], le_rfl, le_rfl⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
    · exact ⟨Or.inl ⟨by omega, by rw [hgn11]; omega⟩, Or.inr ⟨by omega, by omega⟩⟩
  -- Now package for the final state (same `memory`/`globals`/metadata as `s11`)!
  refine ⟨rfl, ⟨guestInv_congr (s := s11) rfl rfl rfl rfl hA11.1, hA11.2⟩,
    hB11, hh0, hh1, hh3, hh7, hh8, hh9, hh10, ?_, ?_, ?_, ?_, ?_, hg_all⟩
  · intro n hn off hoff
    change nodeF s11 (hdr s11 t 5) n off = nodeF s0 old_nodes n off
    rw [hh5]; exact hnodes_copied n hn off hoff
  · intro i hi
    change memW s11 (hdr s11 t 6 + 8 * i) = memW s0 (old_order + 8 * i)
    rw [hh6]; exact horder_copied i hi
  · change globN s0 "heap_ptr" ≤ globN s11 "heap_ptr"; rw [hgn11]; omega
  · change ∀ iv ∈ htabFootprint s11 t, Allocated s11 iv ∧
      ((∃ j ∈ htabFootprint s0 t, Inside iv j.1 (j.1 + j.2)) ∨
        Inside iv (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s11 "heap_ptr" - globN s0 "heap_ptr")))
    rw [hgn11]; exact hfp11
  · change FrameOutside s0 s11 [(t, 88)] (globN s0 "heap_ptr", globN s11 "heap_ptr" - globN s0 "heap_ptr")
    rw [hgn11]; exact hfr_s0_s11

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
