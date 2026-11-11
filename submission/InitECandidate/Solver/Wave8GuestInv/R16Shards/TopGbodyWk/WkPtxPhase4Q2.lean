import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase (stdKeep)
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

/-! # Phase 4Q2: the g8 stable-logs tail (instructions after `lst_new`)

This file continues `WkPtxPhase4Q`.  After the `lst_new` allocation
(`p4Q8_stableLogs_alloc`), the program stores the count into the fresh
header (`stable_logs + 8 := nl`), loads the backing pointer into
`stable_lp` (`stable_logs + 0`), resets `i := 0`, copies the original log
pointers into the fresh backing array (loop 38), pushes the new list onto
the receipts list at `bo + 72` (`lst_push`) and stores the list pointer
into the returned slot (`rl := stable_logs`).

The file provides the forward-evaluation helpers, the geometry thread for
the original (out-record) logs list, and the chain-from-bundle conversion
shared by the count store and the copy loop. -/

/-! ## Forward-evaluation helpers -/

/-- A single-word store at an in-domain address produces exactly the
`pmcUpdW` memory. -/
theorem p4Q8_store_word_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x w : BitVec 64} (hdom : s.memaddrs x) :
    @panMemStoresHOL 64 _ x (flattenHOL (.val (.word w))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory
      = some (pmcUpdW s.memory x w) := by
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  rfl

/-- The destination expression `local + const k` evaluates to the word at
`w_base.toNat + k` (no wraparound). -/
theorem p4Q8_eval_var_add_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {lname : String} {w_base : BitVec 64} {k : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word w_base)))
    (hk64 : w_base.toNat + k < 2 ^ 64) :
    evalAt s (.op .add [.var .local (ofString lname), .const (BitVec.ofNat 64 k)]) =
      some (.val (.word (BitVec.ofNat 64 (w_base.toNat + k)))) := by
  have hk : k < 2 ^ 64 := by omega
  have hdst_eq : w_base + (BitVec.ofNat 64 k + (0 : BitVec 64)) =
      BitVec.ofNat 64 (w_base.toNat + k) := by
    apply BitVec.eq_of_toNat_eq
    have hz0 : ((0 : BitVec 64)).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk64]
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hlk, valueIsWord, valueWord,
    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    hdst_eq]

/-- The destination expression `local + 8 * i` (the loop-38 store
destination) evaluates to the word `w_base + iw * 8`. -/
theorem p4Q8_eval_var_add_mul {F : Type} {s : PanSemStateFiniteExact 64 F}
    {lname iname : String} {w_base iw : BitVec 64}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word w_base)))
    (hik : s.locals.lookup (ofString iname) = some (.val (.word iw))) :
    evalAt s (.op .add [.var .local (ofString lname),
        (.panop .mul [.var .local (ofString iname), (.const 0x0000000000000008#64)])]) =
      some (.val (.word (w_base + iw * 0x0000000000000008#64))) := by
  have hz : iw * 0x0000000000000008#64 + (0 : BitVec 64) =
      iw * 0x0000000000000008#64 := BitVec.add_zero _
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hlk, hik, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, hz]

/-- The loop-38 source load `lp + 8 * i` evaluates forward from the
in-domain word cell. -/
theorem p4Q8_eval_load_lp {F : Type}
    {s : PanSemStateFiniteExact 64 F} {lp_w iw v : BitVec 64}
    (hlp : s.locals.lookup (ofString "lp") = some (.val (.word lp_w)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hdom : s.memaddrs (lp_w + iw * 0x0000000000000008#64))
    (hcell : s.memory (lp_w + iw * 0x0000000000000008#64) = .word v) :
    evalAt s (.load .one (.op .add [.var .local (ofString "lp"),
        (.panop .mul [.var .local (ofString "i"), (.const 0x0000000000000008#64)])])) =
      some (.val (.word v)) := by
  have hz : iw * 0x0000000000000008#64 + (0 : BitVec 64) =
      iw * 0x0000000000000008#64 := BitVec.add_zero _
  simp only [evalAt, evalHOLExact, evalListHOLExact, toExact, hlp, hi, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map, Bool.and_self,
    ↓reduceIte, List.foldr, memLoadHOLExact, isWfShapeExactHOL, hz, hdom, hcell]

/-! ## The geometry thread for the original logs list -/

/-- A region of the original (out-record) logs list: it was allocated
before the stable-logs blocks, so it lies strictly below the fresh
frontier `lw`, or on the scratch side (above `heapLimit = scratchStart`). -/
def p4Q8OldGeo (lw : Nat) (i : Ivl) : Prop :=
  Inside i sourceBase lw ∨ Inside i scratchStart scratchEnd

/-- A geo region is disjoint from a fresh block that starts at `lw`. -/
theorem p4Q8OldGeo_disj {lw base sz : Nat} {i : Ivl}
    (hgeo : p4Q8OldGeo lw i) (hbase : lw ≤ base)
    (hin : base + sz ≤ heapLimit) :
    Disj i (base, sz) := by
  rcases hgeo with h | h
  · unfold Inside at h
    obtain ⟨h1, h2⟩ := h
    refine Or.inr (Or.inr ?_)
    dsimp only
    omega
  · unfold Inside at h
    obtain ⟨h1, h2⟩ := h
    have hlim : heapLimit = scratchStart := rfl
    refine Or.inr (Or.inr ?_)
    dsimp only
    omega

/-- A store cell inside a geo region does not hit a fresh block. -/
theorem p4Q8OldGeo_noHit {lw base sz k : Nat} {i : Ivl}
    (hgeo : p4Q8OldGeo lw i)
    (hkin : i.1 ≤ k ∧ k + 8 ≤ i.1 + i.2)
    (hbase : lw ≤ base)
    (hin : base + sz ≤ heapLimit) :
    ¬ CellHits k (base, sz) := by
  rcases hgeo with h | h
  · unfold Inside at h
    obtain ⟨h1, h2⟩ := h
    intro hcc
    unfold CellHits at hcc
    obtain ⟨c1, c2⟩ := hcc
    dsimp only at c1 c2
    omega
  · unfold Inside at h
    obtain ⟨h1, h2⟩ := h
    have hlim : heapLimit = scratchStart := rfl
    intro hcc
    unfold CellHits at hcc
    obtain ⟨c1, c2⟩ := hcc
    dsimp only at c1 c2
    omega

/-- The chain at the `lst_new` exit state follows from the witness bundle
forwarded by `WkPtxPhase4C.p4Run_decCall_lst_new`. -/
theorem p4Q8Chain_of_bundle {F : Type}
    {entry s_pmc mid : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    (hbundle : ∀ S0 Nd0 : List Nat, WorldTypedWith entry S0 Nd0 →
      IvlsDisj (ptxRegions entry) (worldTypedIvls entry S0 Nd0) →
      ∃ S_pmc' Nd_pmc' S_new Nd_new : List Nat,
        WorldTypedWith s_pmc S_pmc' Nd_pmc' ∧
        (∀ t' ∈ S0, t' ∈ S_new) ∧
        WorldTypedWith mid S_new Nd_new ∧
        OwnedGrows s_pmc mid (worldOwned s_pmc S_pmc' Nd_pmc') (worldOwned mid S_new Nd_new) ∧
        OwnedGrows entry mid (worldOwned entry S0 Nd0) (worldOwned mid S_new Nd_new) ∧
        FrameOutside entry mid (worldOwned entry S0 Nd0 ++ ptxRegions entry ++ [freeGap entry])
          (heapFree entry) ∧
        (∀ o ∈ worldOwned mid S_new Nd_new, Disj (w_out.toNat, 96) o) ∧
        IvlsDisj [(lw.toNat, 24), (lw.toNat + 24, 8 * capw.toNat)]
          (worldOwned mid S_new Nd_new) ∧
        PmcLogsLiveOwned mid S_new Nd_new (memW mid (w_out.toNat + 16)) ∧
        PmcLogsLiveOwned mid S_new Nd_new lw.toNat) :
    p4Q8Chain entry s_pmc w_out lw capw mid := by
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S_pmc', Nd_pmc', S_new, Nd_new, hWTp, hsub, hWTt, hOGp, hOGe, hFO, hout, hfresh,
    hlist, -⟩ := hbundle S0 Nd0 hWT0 hD0
  exact ⟨S_new, Nd_new, S_pmc', Nd_pmc', hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩

/-! ## The chain across empty-region WorldSteps -/

/-- The chain survives a WorldStep at the empty region family: the `lst_push`
callee of the final push and the single-cell slot store both expose
`R = fun _ => []`, so every disjunctive freshness premise of the store
transport is vacuous.  Only the geometry of the out-record and of the fresh
stable-logs blocks against the post-state's new-heap gap is needed. -/
theorem p4Q8Chain_worldStep {F : Type}
    {entry s_pmc t post : PanSemStateFiniteExact 64 F} {w_out lw capw : BitVec 64}
    {gw : List String} {r : Option (PanSemResultExact 64)}
    (h : p4Q8Chain entry s_pmc w_out lw capw t)
    (hW : WorldOK t)
    (hhp_pmc : globN s_pmc "heap_ptr" ≤ globN t "heap_ptr")
    (hhp_ent : globN entry "heap_ptr" ≤ globN t "heap_ptr")
    (hfp_ent : globN entry "frame_mem_ptr" ≤ globN t "frame_mem_ptr")
    (hsp_ent : globN t "scratch_ptr" ≤ globN entry "scratch_ptr")
    (hAR_ent : ArenaReady entry)
    (hw_out8 : w_out.toNat % 8 = 0)
    (hout_inside : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr"))
    (hhp_lw : lw.toNat + 24 + 8 * capw.toNat ≤ globN t "heap_ptr")
    (hlogs_list : LogsListOK t (memW t (w_out.toNat + 16)))
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra t r post)
    (hgw : gw = [] ∨ gw = ["heap_ptr"]) :
    p4Q8Chain entry s_pmc w_out lw capw post := by
  have hsp_eq : globN post "scratch_ptr" = globN t "scratch_ptr" := by
    rcases hgw with rfl | rfl
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by simp))
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "scratch_ptr") (by decide))
  have hsys : globN post "vm_system_address" = globN t "vm_system_address" := by
    rcases hgw with rfl | rfl
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "vm_system_address") (by simp))
    · exact globN_eq_of_lookup (hstep.2.2.1 (ofString "vm_system_address") (by decide))
  have hAs : ArenaOK t := hW.1.2
  have hAp : ArenaOK post := hstep.1.2
  have hgS : GuestInv t := hW.1.1
  have hgrow : AllocatorGrows t post := ⟨hstep.2.1, le_of_eq hsp_eq⟩
  have hwout96 : w_out.toNat + 96 ≤ globN t "heap_ptr" := hout_inside.2
  intro S0 Nd0 hWT0 hD0
  obtain ⟨S, N, Sp, Np, hsub, hWTt, hWTp, hOGp, hOGe, hFO, hout, hfresh, hlist⟩ :=
    h S0 Nd0 hWT0 hD0
  have hR_disj : IvlsDisj ((fun _ => []) t) (worldTypedIvls t S N) := by
    intro o ho
    cases ho
  obtain ⟨S', N', hsub', hWT', hOG', hFO', -⟩ :=
    hstep.2.2.2.2 S N hWTt hR_disj
  have hold0 : ∀ j ∈ worldOwned t S N, j.2 = 0 → j.1 % 8 = 0 :=
    R13Shards.worldOwned_zero_aligned hWTt
  have hR0 : ∀ j ∈ ((fun _ => []) t : List Ivl), j.2 = 0 → j.1 % 8 = 0 := by
    intro j hj
    cases hj
  have hout_u : R13Shards.IvlUnhit t post (w_out.toNat, 96) :=
    (R13Shards.heap_ivl_survives_step hAs hstep.2.1 hold0 hR0 hOG' hFO'
      (b := (w_out.toNat, 96)) hw_out8 (by norm_num) hout_inside hout
      (by intro j hj; cases hj)).2.2
  have hout_hi : w_out.toNat + 96 ≤ 2 ^ 64 :=
    (R13Shards.ivl_allocated_bound hAs (Or.inl hout_inside)).2
  have hout_cell : memW post (w_out.toNat + 16) = memW t (w_out.toNat + 16) :=
    R13Shards.memW_eq_of_ivlUnhit hout_u (by omega) hout_hi ⟨by omega, by omega⟩
  refine ⟨S', N', Sp, Np, fun t' ht' => hsub' t' (hsub t' ht'), hWT', hWTp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ptx_ownedGrows_trans hhp_pmc hstep.2.1 hOGp hOG'
  · exact ptx_ownedGrows_trans hhp_ent hstep.2.1 hOGe hOG'
  · exact ptx_frameOutside_trans hAR_ent ⟨hgS, hAs⟩ hhp_ent hfp_ent hsp_ent hOGe
      (by intro i hi; cases hi) hFO hFO'
  · intro o ho
    rcases hOG' o ho with rfl | ⟨j, hj, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact disj_of_inside_right hin (hout j hj)
    · obtain ⟨h1, h2⟩ := hin
      refine Or.inr (Or.inr (Or.inl ?_))
      show w_out.toNat + 96 ≤ o.1
      omega
  · intro i hi j hj
    rcases hOG' j hj with rfl | ⟨k, hk, hin⟩ | hin
    · exact Or.inr (Or.inl rfl)
    · exact disj_of_inside_right hin (hfresh i hi k hk)
    · obtain ⟨h1, h2⟩ := hin
      rcases List.mem_cons.1 hi with rfl | hi'
      · refine Or.inr (Or.inr (Or.inl ?_))
        show lw.toNat + 24 ≤ j.1
        omega
      · rcases List.mem_cons.1 hi' with rfl | hi''
        · refine Or.inr (Or.inr (Or.inl ?_))
          show lw.toNat + 24 + 8 * capw.toNat ≤ j.1
          omega
        · cases hi''
  · rw [hout_cell]
    by_cases hnz : memW t (w_out.toNat + 16) = 0
    · rw [hnz]; exact pmcLogsLiveOwned_zero _ _ _
    · exact PtxP34.logsLiveOwned_survives hAs hAp hgS hgrow hlogs_list hlist hsys hold0 hR0
        hOG' hFO' (by intro j hj; cases hj) (by intro j hj; cases hj)
        (by intro i hi j hj; cases hj)

/-! ## Geometry of the original logs list -/

/-- An allocated region of a state whose heap frontier is `lw` is a geo
region: below `lw`, or on the scratch side. -/
theorem p4Q8OldGeo_of_alloc {F : Type} {t : PanSemStateFiniteExact 64 F} {lw : Nat} {i : Ivl}
    (hAs : ArenaOK t) (hlw : globN t "heap_ptr" = lw) (ha : Allocated t i) :
    p4Q8OldGeo lw i := by
  rcases ha with h | h
  · refine Or.inl ⟨h.1, ?_⟩
    rw [hlw] at h
    exact h.2
  · have hsc : scratchStart ≤ globN t "scratch_ptr" :=
      Nat.le_trans hAs.2.2.1 hAs.2.2.2.1
    exact Or.inr ⟨Nat.le_trans hsc h.1, h.2⟩

/-- A cell inside a geo region survives a fresh-block store. -/
theorem p4Q8MemW_store_of_geo {F : Type}
    {t : PanSemStateFiniteExact 64 F} {base sz lw k : Nat} {i : Ivl}
    {mem' : BitVec 64 → HolWordLab 64}
    (hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = t.memory a)
    (hgeo : p4Q8OldGeo lw i)
    (hkin : i.1 ≤ k ∧ k + 8 ≤ i.1 + i.2)
    (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit)
    (hk64 : k < 2 ^ 64) :
    memW {t with memory := mem'} k = memW t k := by
  have hk' : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  unfold memW
  dsimp only
  rw [hcell (BitVec.ofNat 64 k) (by
    show ¬ CellHits (BitVec.ofNat 64 k).toNat (base, sz)
    rw [hk']
    exact p4Q8OldGeo_noHit hgeo hkin hbase hin)]

/-! ## Transporting the original logs facts across fresh-block stores -/

/-- A word cell inside a geo region survives a fresh-block store. -/
theorem p4Q8WordAt_store_of_geo {F : Type}
    {t : PanSemStateFiniteExact 64 F} {base sz lw k : Nat} {i : Ivl}
    {mem' : BitVec 64 → HolWordLab 64}
    (hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = t.memory a)
    (h : WordAt t k)
    (hgeo : p4Q8OldGeo lw i)
    (hkin : i.1 ≤ k ∧ k + 8 ≤ i.1 + i.2)
    (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit)
    (hk64 : k < 2 ^ 64) :
    WordAt {t with memory := mem'} k := by
  obtain ⟨w, hd, hv⟩ := h
  refine ⟨w, hd, ?_⟩
  show mem' (BitVec.ofNat 64 k) = HolWordLab.word w
  rw [hcell (BitVec.ofNat 64 k) (by
    show ¬ CellHits (BitVec.ofNat 64 k).toNat (base, sz)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
    exact p4Q8OldGeo_noHit hgeo hkin hbase hin)]
  exact hv

/-- A log entry's facts survive a fresh-block store: only the five record
cells are read, and the record lies strictly below the fresh blocks. -/
theorem p4Q8LogEntryOK_store {F : Type}
    {t : PanSemStateFiniteExact 64 F} {base sz lw log : Nat}
    {mem' : BitVec 64 → HolWordLab 64}
    (hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = t.memory a)
    (h : LogEntryOK t log)
    (hgeo : p4Q8OldGeo lw (log, 40))
    (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit)
    (hk64 : log + 40 ≤ 2 ^ 64) :
    LogEntryOK {t with memory := mem'} log := by
  obtain ⟨hwords, hin40, hc16, hc32, hia, hit, hid⟩ := h
  have hgp : globN {t with memory := mem'} "heap_ptr" = globN t "heap_ptr" := rfl
  have h0 : memW {t with memory := mem'} log = memW t log :=
    p4Q8MemW_store_of_geo hcell hgeo ⟨by omega, by omega⟩ hbase hin (by omega)
  have h8 : memW {t with memory := mem'} (log + 8) = memW t (log + 8) :=
    p4Q8MemW_store_of_geo hcell hgeo ⟨by omega, by omega⟩ hbase hin (by omega)
  have h16 : memW {t with memory := mem'} (log + 16) = memW t (log + 16) :=
    p4Q8MemW_store_of_geo hcell hgeo ⟨by omega, by omega⟩ hbase hin (by omega)
  have h24 : memW {t with memory := mem'} (log + 24) = memW t (log + 24) :=
    p4Q8MemW_store_of_geo hcell hgeo ⟨by omega, by omega⟩ hbase hin (by omega)
  have h32 : memW {t with memory := mem'} (log + 32) = memW t (log + 32) :=
    p4Q8MemW_store_of_geo hcell hgeo ⟨by omega, by omega⟩ hbase hin (by omega)
  refine ⟨⟨hwords.1, hwords.2.1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact p4Q8WordAt_store_of_geo hcell (hwords.2.2 k hk) hgeo
      ⟨by omega, by omega⟩ hbase hin (by omega)
  · rw [hgp]; exact hin40
  · rw [h16]; exact hc16
  · rw [h32]; exact hc32
  · rw [h0, hgp]; exact hia
  · rw [h8, h16, hgp]; exact hit
  · rw [h24, h32, hgp]; exact hid

/-- The original out-record logs list survives a fresh-block store: the
header cells, the array cells and every log record lie strictly below the
fresh blocks. -/
theorem p4Q8LogsListOK_store {F : Type}
    {t : PanSemStateFiniteExact 64 F} {base sz lw logs : Nat}
    {mem' : BitVec 64 → HolWordLab 64}
    (hcell : ∀ a : BitVec 64, ¬ CellHits a.toNat (base, sz) → mem' a = t.memory a)
    (hnz : logs ≠ 0)
    (h : LogsListOK t logs)
    (hhdr : p4Q8OldGeo lw (logs, 24))
    (harr : p4Q8OldGeo lw (memW t logs, 8 * memW t (logs + 8)))
    (hent : ∀ i, i < memW t (logs + 8) →
      p4Q8OldGeo lw (memW t (memW t logs + 8 * i), 40))
    (hbase : lw ≤ base) (hin : base + sz ≤ heapLimit)
    (hh64 : logs + 24 ≤ 2 ^ 64)
    (harr64 : memW t logs + 8 * memW t (logs + 8) ≤ 2 ^ 64)
    (hent64 : ∀ i, i < memW t (logs + 8) →
      memW t (memW t logs + 8 * i) + 40 ≤ 2 ^ 64) :
    LogsListOK {t with memory := mem'} logs := by
  rcases h with rfl | ⟨hw, ha, hc8, hc16, he⟩
  · exact absurd rfl hnz
  have hL : memW {t with memory := mem'} logs = memW t logs :=
    p4Q8MemW_store_of_geo hcell hhdr ⟨by omega, by omega⟩ hbase hin (by omega)
  have h8 : memW {t with memory := mem'} (logs + 8) = memW t (logs + 8) :=
    p4Q8MemW_store_of_geo hcell hhdr ⟨by omega, by omega⟩ hbase hin (by omega)
  have h16 : memW {t with memory := mem'} (logs + 16) = memW t (logs + 16) :=
    p4Q8MemW_store_of_geo hcell hhdr ⟨by omega, by omega⟩ hbase hin (by omega)
  have hc : ∀ i, i < memW t (logs + 8) →
      memW {t with memory := mem'} (memW t logs + 8 * i) =
        memW t (memW t logs + 8 * i) := by
    intro i hi
    exact p4Q8MemW_store_of_geo hcell harr ⟨by omega, by omega⟩ hbase hin (by omega)
  refine Or.inr ⟨⟨hw.1, hw.2.1, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact p4Q8WordAt_store_of_geo hcell (hw.2.2 k hk) hhdr
      ⟨by omega, by omega⟩ hbase hin (by omega)
  · exact ha
  · rw [h8]; exact hc8
  · rw [h8, h16]; exact hc16
  · rw [h8]
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact p4Q8WordAt_store_of_geo hcell (he i hi).1 harr
        ⟨by omega, by omega⟩ hbase hin (by omega)
    · rw [hL, hc i hi]
      exact p4Q8LogEntryOK_store hcell (he i hi).2 (hent i hi) hbase hin (hent64 i hi)

/-! ## Store domain -/

/-- An aligned address below `heapEnd` is in the ordinary store domain of
any guest-invariant state. -/
theorem p4Q8_dom_of_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) {a : Nat} (hal : a % 8 = 0) (hlo : sourceBase ≤ a)
    (hhi : a < heapEnd) :
    s.memaddrs (BitVec.ofNat 64 a) := by
  rw [hG.memaddrs]
  exact InitECandidate.Solver.Wave8GuestInv.R13.ordinaryDomain_of_nat a hlo hhi hal

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
