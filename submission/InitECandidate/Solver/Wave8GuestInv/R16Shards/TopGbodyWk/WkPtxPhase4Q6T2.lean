import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Q6T1

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

/-! # Phase 4Q6T2: cell and transport lemmas for the final receipt push

The `bo + 72` (receipt list) counterparts of the loop-31 `bo + 40` cell
lemmas: the callee's write-set misses the tx/receipt slice cells, the slot
store misses the receipt-list header and the slice cells, the slot store is
a typed block-out array store, and it misses every kept record cell.  Also
the generic transport of the `ptxGlobals`/`ptxKeep` invariants and of the
`out` block across an empty-region `stdKeep` step. -/

theorem p4Q8T_memW_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memW s a < 2 ^ 64 := by
  unfold memW
  split
  exact BitVec.isLt _

/-- The entry-relative globals/records invariants survive an empty-region
`stdKeep` step that only writes `ptxGlobals` globals. -/
theorem p4Q8T_keep_step {F : Type}
    {entry t post : PanSemStateFiniteExact 64 F} {gw : List String}
    {r : Option (PanSemResultExact 64)}
    (hg : GlobalsKept ptxGlobals entry t)
    (hr : RecordsKept ptxRegions ptxKeep entry t)
    (hgw : ∀ g ∈ gw, g ∈ ptxGlobals)
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra t r post) :
    GlobalsKept ptxGlobals entry post ∧ RecordsKept ptxRegions ptxKeep entry post := by
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkg : k ∉ gw.map ofString := by
      intro hm
      obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hm
      exact hk (List.mem_map.2 ⟨g, hgw g hg', rfl⟩)
    exact (hg k hk).trans (hstep.2.2.1 k hkg)
  · intro rec hrec hn off hoff hno
    obtain ⟨offs, hkr, hko⟩ := ptxKeepSub_stdKeep rec hrec
    have heq : globN t rec.1 = globN entry rec.1 := by
      have hni : ofString rec.1 ∉ ptxGlobals.map ofString := by
        simp only [ptxKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
        rcases hrec with rfl | rfl | rfl | rfl
        · decide
        · decide
        · simp at hoff
        · decide
      exact globN_eq_of_lookup (hg (ofString rec.1) hni)
    have hks := hstep.2.2.2.1 (rec.1, offs) hkr (by rw [heq]; exact hn)
      off (hko off hoff) (fun i hi => by cases hi)
    rw [heq] at hks
    exact hks.trans (hr rec hrec hn off hoff hno)

/-- `TxEnv` from the entry-relative globals/records invariants. -/
theorem p4Q8T_txEnv {F : Type} {entry t : PanSemStateFiniteExact 64 F}
    (hready : TxReadyStrong entry)
    (hg : GlobalsKept ptxGlobals entry t)
    (hr : RecordsKept ptxRegions ptxKeep entry t)
    (hidx_local : t.locals.lookup (ofString "index") = entry.locals.lookup (ofString "index")) :
    TxEnv t := by
  obtain ⟨⟨_, hbo_nz_e, hbo24_nz_e, hbo32_nz_e, hidx_lt_e⟩, hjcap_e, hbo40_nz_e, hbo72_nz_e,
    S_e, Nd_e, hWT_e, _⟩ := hready
  have hbo24 := ptx_entry_bo_field_eq (off := 24) hWT_e hg hr hbo_nz_e (by simp) (by omega)
  have hbo32 := ptx_entry_bo_field_eq (off := 32) hWT_e hg hr hbo_nz_e (by simp) (by omega)
  have hbo40 := ptx_entry_bo_field_eq (off := 40) hWT_e hg hr hbo_nz_e (by simp) (by omega)
  have hbo72 := ptx_entry_bo_field_eq (off := 72) hWT_e hg hr hbo_nz_e (by simp) (by omega)
  have hbo80 := ptx_entry_bo_field_eq (off := 80) hWT_e hg hr hbo_nz_e (by simp) (by omega)
  have hbo_s : globN t "bo" = globN entry "bo" :=
    globN_eq_of_lookup (hg (ofString "bo") (by decide))
  have hidx : locN t "index" = locN entry "index" := by simp only [locN, hidx_local]
  exact ⟨by rw [hbo_s]; exact hbo_nz_e, by rw [hbo24]; exact hbo24_nz_e,
    by rw [hbo32]; exact hbo32_nz_e, by rw [hbo40]; exact hbo40_nz_e,
    by rw [hbo72]; exact hbo72_nz_e, by rw [hidx, hbo80]; exact hidx_lt_e,
    by rw [globN_eq_of_lookup (hg (ofString "journal_cap") (by decide))]; exact hjcap_e⟩

/-- The bo+72 backing array is a block-out object with positive capacity. -/
theorem p4Q8T_arrFacts {F : Type} {s : PanSemStateFiniteExact 64 F} {l : Nat}
    (hE : TxEnv s) {S : List Nat} (hT : TablesTyped s S)
    (hl : l = memW s (globN s "bo" + 72))
    (hdata_nz : memW s l ≠ 0) :
    (memW s l, 8 * memW s (l + 16)) ∈ blockOutObjects s ∧ 1 ≤ memW s (l + 16) := by
  obtain ⟨_, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hT
  have hcap : 1 ≤ memW s (l + 16) := by rw [hl]; exact hc72
  have hlen_nz : 8 * memW s (l + 16) ≠ 0 := by omega
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hget6 : (blockOutObjects s)[6] = (memW s l, 8 * memW s (l + 16)) := by
    simp [hbo_eq, ← hl, hE.bo_nz, hdata_nz, hlen_nz]
  exact ⟨hget6 ▸ List.getElem_mem (by rw [hbo_len]; decide), hcap⟩

/-- The receipt-list push callee (write-set: the `bo + 72` list header and
the free heap) preserves every tx/receipt slice cell up to the current
index. -/
theorem p4Q8T_calleeSlices {F : Type}
    {entry u post : PanSemStateFiniteExact 64 F} {w_l : BitVec 64}
    (hAR : ArenaReady u) (hE : TxEnv u) {S Nd : List Nat} (hW : WorldTypedWith u S Nd)
    (hidx : locN u "index" = locN entry "index")
    (hl72 : w_l.toNat = memW u (globN u "bo" + 72))
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (w_l.toNat, 24) →
      ¬ CellHits a.toNat (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) →
      post.memory a = u.memory a) :
    ∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      memW post (memW u (globN u "bo" + off) + 16 * i + 8) =
        memW u (memW u (globN u "bo" + off) + 16 * i + 8) := by
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects u).length = 7 := by rw [hbo_eq]; rfl
  have hlen_nz : 16 * memW u (globN u "bo" + 80) + 16 ≠ 0 := by omega
  have hget0 : (blockOutObjects u)[0] =
      (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo24, hlen_nz]
  have hget1 : (blockOutObjects u)[1] =
      (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) := by
    simp [hbo_eq]
  have hget5 : (blockOutObjects u)[5] = (w_l.toNat, 24) := by
    rw [hl72]; simp [hbo_eq]
  obtain ⟨-, hbo_pw, -, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  have hpair := List.pairwise_iff_getElem.1 hbo_pw
  have he0_mem : (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := hget0 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he1_mem : (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16) ∈
      blockOutObjects u := hget1 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have hd05 : Disj (memW u (globN u "bo" + 24), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    have h := hpair 0 5 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget0, hget5] at h
    exact h
  have hd15 : Disj (memW u (globN u "bo" + 32), 16 * memW u (globN u "bo" + 80) + 16)
      (w_l.toNat, 24) := by
    have h := hpair 1 5 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget5] at h
    exact h
  have hcontain : ∀ e : Ivl, e ∈ blockOutObjects u → e.2 ≠ 0 →
      Allocated u e ∧ e.1 % 8 = 0 ∧ e.2 % 8 = 0 ∧ e.1 + e.2 ≤ 2 ^ 64 := by
    intro e he_mem he_nz
    have he_fix : e ∈ fixedObjects u := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      exact he_mem
    obtain ⟨halloc, hwords⟩ := (hW.2.2.1.1 e he_fix).resolve_left he_nz
    exact ⟨halloc, hwords.1, hwords.2.1, (ivl_allocated_bound hAR.2 halloc).2⟩
  have hsep : heapLimit ≤ scratchStart := by decide
  have hidx_lt : locN u "index" < memW u (globN u "bo" + 80) := hE.idx_lt
  have hcell : ∀ c : Ivl, Allocated u c → c.1 % 8 = 0 → c.2 % 8 = 0 →
      Disj c (w_l.toNat, 24) →
      ∀ k : Nat, k % 8 = 0 → c.1 ≤ k → k + 8 ≤ c.1 + c.2 → k < 2 ^ 64 →
      memW post k = memW u k := by
    intro c halloc hc8 hc2 hd k hk8 hk1 hk2 hk64
    have hj0 : (w_l.toNat, 24).2 = 0 → (w_l.toNat, 24).1 % 8 = 0 := by simp
    have hhit : CellHits k c := ⟨by omega, by omega⟩
    have hm1 : ¬ CellHits k (w_l.toNat, 24) :=
      not_cellHits_of_disj hc8 hc2 hk8 hj0 hhit hd
    have hm2 : ¬ CellHits k (InitECandidate.Solver.Wave8Contracts.M08.heapFree u) := by
      intro ⟨hc1, hc2⟩
      simp only [InitECandidate.Solver.Wave8Contracts.M08.heapFree] at hc1 hc2
      unfold Allocated at halloc
      unfold Inside at halloc
      rcases halloc with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · omega
      · have h1 := hAR.2.2.1; have h2 := hAR.2.2.2.1; have h3 := hAR.2.2.2.2.1
        omega
    exact p4Loop31_memW_of_miss hmem hk64 hm1 hm2
  intro off hoff i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
  rcases hoff with rfl | rfl
  · obtain ⟨halloc0, halign0, hlen0, hhi0⟩ := hcontain _ he0_mem hlen_nz
    have hb8 : memW u (globN u "bo" + 24) % 8 = 0 := halign0
    have hb_hi : memW u (globN u "bo" + 24) + (16 * memW u (globN u "bo" + 80) + 16)
        ≤ 2 ^ 64 := hhi0
    have hk8 : (memW u (globN u "bo" + 24) + 16 * i + 8) % 8 = 0 := by omega
    have hk1 : memW u (globN u "bo" + 24) ≤ memW u (globN u "bo" + 24) + 16 * i + 8 := by omega
    have hk2 : memW u (globN u "bo" + 24) + 16 * i + 8 + 8
        ≤ memW u (globN u "bo" + 24) + 16 * memW u (globN u "bo" + 80) + 16 := by omega
    have hk64 : memW u (globN u "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
    exact hcell _ halloc0 hb8 hlen0 hd05 _ hk8 hk1 hk2 hk64
  · obtain ⟨halloc1, halign1, hlen1, hhi1⟩ := hcontain _ he1_mem hlen_nz
    have hb8 : memW u (globN u "bo" + 32) % 8 = 0 := halign1
    have hb_hi : memW u (globN u "bo" + 32) + (16 * memW u (globN u "bo" + 80) + 16)
        ≤ 2 ^ 64 := hhi1
    have hk8 : (memW u (globN u "bo" + 32) + 16 * i + 8) % 8 = 0 := by omega
    have hk1 : memW u (globN u "bo" + 32) ≤ memW u (globN u "bo" + 32) + 16 * i + 8 := by omega
    have hk2 : memW u (globN u "bo" + 32) + 16 * i + 8 + 8
        ≤ memW u (globN u "bo" + 32) + 16 * memW u (globN u "bo" + 80) + 16 := by omega
    have hk64 : memW u (globN u "bo" + 32) + 16 * i + 8 < 2 ^ 64 := by omega
    exact hcell _ halloc1 hb8 hlen1 hd15 _ hk8 hk1 hk2 hk64

/-- The slot store into the bo+72 backing array misses the receipt-list
header cells and every tx/receipt slice cell up to the current index. -/
theorem p4Q8T_storeMisses {F : Type}
    {entry s : PanSemStateFiniteExact 64 F} {w : BitVec 64} {l : Nat}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hl : l = memW s (globN s "bo" + 72))
    (hdata_nz : memW s l ≠ 0)
    (hientry : locN entry "index" < memW s (globN s "bo" + 80))
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16))) :
    (BitVec.ofNat 64 l ≠ w ∧ BitVec.ofNat 64 (l + 8) ≠ w) ∧
    (∀ off ∈ ([24, 32] : List Nat), ∀ i ≤ locN entry "index",
      BitVec.ofNat 64 (memW s (globN s "bo" + off) + 16 * i + 8) ≠ w) := by
  obtain ⟨harr_mem, hcap⟩ := p4Q8T_arrFacts hE hW.1 hl hdata_nz
  have hlen8_nz : 8 * memW s (l + 16) ≠ 0 := by omega
  obtain ⟨hc40, hc72, hbo_eq⟩ := blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have hlen_nz : 16 * memW s (globN s "bo" + 80) + 16 ≠ 0 := by omega
  have hget0 : (blockOutObjects s)[0] =
      (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq, hE.bo_nz, hE.bo24, hlen_nz]
  have hget1 : (blockOutObjects s)[1] =
      (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) := by
    simp [hbo_eq]
  have hget5 : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by
    simp [hbo_eq]
  have hget6 : (blockOutObjects s)[6] = (memW s l, 8 * memW s (l + 16)) := by
    simp [hbo_eq, ← hl, hE.bo_nz, hdata_nz, hlen8_nz]
  obtain ⟨-, hbo_pw, -, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  have hpair := List.pairwise_iff_getElem.1 hbo_pw
  have hd06 : Disj (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 0 6 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget0, hget6] at h
    exact h
  have hd16 : Disj (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 1 6 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget1, hget6] at h
    exact h
  have hd56 : Disj (memW s (globN s "bo" + 72), 24)
      (memW s l, 8 * memW s (l + 16)) := by
    have h := hpair 5 6 (by rw [hbo_len]; decide) (by rw [hbo_len]; decide) (by decide)
    rw [hget5, hget6] at h
    exact h
  have hbound : ∀ e : Ivl, e ∈ blockOutObjects s → e.2 ≠ 0 → e.1 + e.2 ≤ 2 ^ 64 := by
    intro e he_mem he_nz
    have he_fix : e ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append_left
      apply List.mem_append_right
      exact he_mem
    obtain ⟨halloc, -⟩ := (hW.2.2.1.1 e he_fix).resolve_left he_nz
    exact (ivl_allocated_bound hA.2 halloc).2
  have he0_mem : (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget0 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he1_mem : (memW s (globN s "bo" + 32), 16 * memW s (globN s "bo" + 80) + 16) ∈
      blockOutObjects s := hget1 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he5_mem : (memW s (globN s "bo" + 72), 24) ∈ blockOutObjects s :=
    hget5 ▸ List.getElem_mem (by rw [hbo_len]; decide)
  have he5_nz : (memW s (globN s "bo" + 72), 24).2 ≠ 0 := by simp
  have he0_hi : memW s (globN s "bo" + 24) + (16 * memW s (globN s "bo" + 80) + 16)
      ≤ 2 ^ 64 := hbound _ he0_mem hlen_nz
  have he1_hi : memW s (globN s "bo" + 32) + (16 * memW s (globN s "bo" + 80) + 16)
      ≤ 2 ^ 64 := hbound _ he1_mem hlen_nz
  have he5_hi : memW s (globN s "bo" + 72) + 24 ≤ 2 ^ 64 := hbound _ he5_mem he5_nz
  have hcell_miss : ∀ c : Ivl, Disj c (w.toNat, 8) → ∀ k : Nat,
      c.1 ≤ k → k + 8 ≤ c.1 + c.2 → k < 2 ^ 64 →
      BitVec.ofNat 64 k ≠ w := by
    intro c hd k hk1 hk2 hk64 heq
    have htonat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  have hdisj_w : ∀ c : Ivl, Disj c (memW s l, 8 * memW s (l + 16)) →
      Disj c (w.toNat, 8) := fun c hd => disj_of_inside_right hin hd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hk1a : memW s (globN s "bo" + 72) ≤ l := by omega
    have hk2a : l + 8 ≤ memW s (globN s "bo" + 72) + 24 := by omega
    have hk64a : l < 2 ^ 64 := by omega
    exact hcell_miss _ (hdisj_w _ hd56) _ hk1a hk2a hk64a
  · have hk1b : memW s (globN s "bo" + 72) ≤ l + 8 := by omega
    have hk2b : l + 8 + 8 ≤ memW s (globN s "bo" + 72) + 24 := by omega
    have hk64b : l + 8 < 2 ^ 64 := by omega
    exact hcell_miss _ (hdisj_w _ hd56) _ hk1b hk2b hk64b
  · intro off hoff i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl
    · have hk1 : memW s (globN s "bo" + 24) ≤ memW s (globN s "bo" + 24) + 16 * i + 8 := by omega
      have hk2 : memW s (globN s "bo" + 24) + 16 * i + 8 + 8
          ≤ memW s (globN s "bo" + 24) + 16 * memW s (globN s "bo" + 80) + 16 := by omega
      have hk64 : memW s (globN s "bo" + 24) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hd06) _ hk1 hk2 hk64
    · have hk1 : memW s (globN s "bo" + 32) ≤ memW s (globN s "bo" + 32) + 16 * i + 8 := by omega
      have hk2 : memW s (globN s "bo" + 32) + 16 * i + 8 + 8
          ≤ memW s (globN s "bo" + 32) + 16 * memW s (globN s "bo" + 80) + 16 := by omega
      have hk64 : memW s (globN s "bo" + 32) + 16 * i + 8 < 2 ^ 64 := by omega
      exact hcell_miss _ (hdisj_w _ hd16) _ hk1 hk2 hk64

/-- The `hty` core of the final slot store: the single-cell store inside the
bo+72 backing array preserves typing, the owned set and the `TxEnv`, and
the stored cell lies inside an owned object (the backing array itself). -/
theorem p4Q8T_hty {F : Type} {s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64} {l : Nat}
    (hAR : ArenaReady s) (hE : TxEnv s)
    (hl : l = memW s (globN s "bo" + 72))
    (hdata_nz : memW s l ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16)))
    (hx : s.memaddrs w)
    (hm : ∀ a, a ≠ w → mem' a = s.memory a) :
    ∀ S Nd, WorldTypedWith s S Nd →
      (WorldTypedWith {s with memory := mem'} S Nd ∧
        worldOwned {s with memory := mem'} S Nd = worldOwned s S Nd ∧
        TxEnv {s with memory := mem'}) ∧
      (∃ o ∈ worldOwned s S Nd, Inside (w.toNat, 8) o.1 (o.1 + o.2)) := by
  intro S Nd hWT
  obtain ⟨harr_mem, -⟩ := p4Q8T_arrFacts hE hWT.1 hl hdata_nz
  have harr_fix : (memW s l, 8 * memW s (l + 16)) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_mem
  have harr_own : (memW s l, 8 * memW s (l + 16)) ∈ worldOwned s S Nd := by
    unfold worldOwned
    apply List.mem_append_left
    apply List.mem_append_right
    exact harr_fix
  refine ⟨?_, ⟨(memW s l, 8 * memW s (l + 16)), harr_own, hin⟩⟩
  rw [hl] at hdata_nz hin
  exact store_bo_array_world (idx := 6)
    (arr := (memW s (memW s (globN s "bo" + 72)),
      8 * memW s (memW s (globN s "bo" + 72) + 16)))
    hAR hE hWT (Or.inr (Or.inr ⟨rfl, hdata_nz, rfl⟩)) hx hin hm

/-- The `hrec` core of the final slot store: every `stdKeep` record cell
(ws, bs, ts, bo) misses the stored slot address. -/
theorem p4Q8T_hrecStd {F : Type} {s : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {mem' : RiscV.Word 64 → HolWordLab 64}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {l : Nat} (hl : l = memW s (globN s "bo" + 72))
    (hdata_nz : memW s l ≠ 0)
    (hin : Inside (w.toNat, 8) (memW s l) (memW s l + 8 * memW s (l + 16)))
    (hm : ∀ a, a ≠ w → mem' a = s.memory a) :
    ∀ r ∈ stdKeep, globN s r.1 ≠ 0 → ∀ k ∈ r.2,
      memW {s with memory := mem'} (globN s r.1 + k) = memW s (globN s r.1 + k) := by
  obtain ⟨-, -, hgb_rest, -, -⟩ := fixedObjects_disj_parts hW.2.2.1
  obtain ⟨harr_mem, -⟩ := p4Q8T_arrFacts hE hW.1 hl hdata_nz
  have hrec_disj : ∀ (g : String) (sz : Nat), (g, sz) ∈ globalBuffers →
      globN s g ≠ 0 → Disj (globN s g, sz) (memW s l, 8 * memW s (l + 16)) := by
    intro g sz hgb hgnz
    have hmem : (memW s l, 8 * memW s (l + 16)) ∈
        [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap")] ++ blockOutObjects s ++ balObjects s := by
      apply List.mem_append_left
      apply List.mem_append_right
      exact harr_mem
    exact hgb_rest _ (List.mem_map.2 ⟨(g, sz), hgb, by simp [hgnz]⟩) _ hmem
  have hcell_miss : ∀ (g : String) (sz : Nat), (g, sz) ∈ typedRecords →
      globN s g ≠ 0 → ∀ k, k + 8 ≤ sz → BitVec.ofNat 64 (globN s g + k) ≠ w := by
    intro g sz htr hgnz k hk8
    have hd : Disj (globN s g, sz) (w.toNat, 8) :=
      disj_of_inside_right hin (hrec_disj g sz (typedRecord_mem_globalBuffers htr) hgnz)
    have hg_fix : (globN s g, sz) ∈ fixedObjects s := by
      simpa [hgnz] using typedRecord_mem_fixedObjects s (r := (g, sz)) htr
    have hsz_nz : (g, sz).2 ≠ 0 := by simp; omega
    obtain ⟨halloc, -⟩ := (hW.2.2.1.1 _ hg_fix).resolve_left hsz_nz
    have hg_hi := (ivl_allocated_bound hA.2 halloc).2
    intro heq
    have htonat := congrArg BitVec.toNat heq
    have hk_lt : globN s g + k < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    rcases hd with h0 | h0 | h1 | h1 <;> omega
  intro r hr hgnz k hk
  simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hne : BitVec.ofNat 64 (globN s r.1 + k) ≠ w := by
    rcases hr with rfl | rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 40 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "ws" 40 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 80 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "bs" 80 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 72 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "ts" 72 (by decide) hgnz k hk8
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      have hk8 : k + 8 ≤ 88 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact hcell_miss "bo" 88 (by decide) hgnz k hk8
  exact p4Loop31_memW_of_storeMiss hm hne

/-- The `out` block is untouched by an empty-region `stdKeep` step from a
state carrying the extended chain. -/
theorem p4Q8T_out_unhit {F : Type}
    {entry s_pmc t post : PanSemStateFiniteExact 64 F} {w_out lw : BitVec 64}
    {gw : List String} {r : Option (PanSemResultExact 64)} {S_e Nd_e : List Nat}
    (hX : p4Q8ChainX entry s_pmc w_out lw t)
    (hWT_e : WorldTypedWith entry S_e Nd_e)
    (hD_e : IvlsDisj (ptxRegions entry) (worldTypedIvls entry S_e Nd_e))
    (hA : ArenaOK t)
    (hw8 : w_out.toNat % 8 = 0)
    (hin : Inside (w_out.toNat, 96) sourceBase (globN t "heap_ptr"))
    (hstep : WorldStep (fun _ => []) gw stdKeep NoExtra t r post) :
    R13Shards.IvlUnhit t post (w_out.toNat, 96) := by
  obtain ⟨S, N, Sp, Np, _, hWT, _, _, _, _, hout, _⟩ := hX S_e Nd_e hWT_e hD_e
  obtain ⟨S', N', _, _, hOG, hFO, _⟩ := hstep.2.2.2.2 S N hWT (by intro i hi; cases hi)
  exact (R13Shards.heap_ivl_survives_step hA hstep.2.1
    (R13Shards.worldOwned_zero_aligned hWT) (by intro j hj; cases hj) hOG hFO
    (b := (w_out.toNat, 96)) hw8 (by norm_num) hin hout (by intro j hj; cases hj)).2.2

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
