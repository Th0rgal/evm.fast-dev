import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.StepLemmas

/-! EVM-frame invariant (`EvmInv`, `EvmStep`, `EvmKeeps`, `EvmAvoids`) congruence lemmas for
micro-shard `m23` (R11). Also exports `evmStep_of_head_64_184` for `ek_charge_gas`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M23

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim EVM contract definitions (R11) -/

def KeepsOn (P W : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (fname : MlS) : Prop :=
  FunSpec P (fun _ r post => Resumes r → W post) fname

def EvmInvAt {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat) : Prop :=
  WorldTyped s S ∧
    let ch := evmChain s
    ch ≠ [] ∧ ch.length ≤ Wave8GuestInv.maxChain ∧ (∃ ec ∈ ch.getLast?, memW s (ec.2 + 16) = 0) ∧
    (∀ ec ∈ ch, FrameWF s S ec) ∧ (∀ ec ∈ ch.tail, FrameRoom s ec) ∧ RetWindowsOK s ch ∧
    ((ch.map (frameObjects s)).flatten).Pairwise Disj ∧
    (∀ ec ∈ ch, ∀ o ∈ frameObjects s ec,
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j) ∧
    AvoidsTries s S (ch.map (frameObjects s)).flatten ∧
    MarksOK s S ch ∧
    RolesOK s S (worldRoleSlots s ++ frameRoleSlots s ch) (journalRoleSlots s) ∧
    (ch.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum + 1 < 2 ^ 64

def EvmAvoids (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧ ∃ Nd, TriesTypedWith s S Nd ∧
    IvlsDisj (R s) (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten)

def EvmStep (gw : List String) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post => EvmInv post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧ GlobalsKept gw s post ∧
    evmChain post = evmChain s

def EvmKeeps (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpec P (fun s r post => Resumes r → EvmStep gw s post) fname

/-! ## 2. Frame-object bounds and cell equality from `ByteRegionEffect` -/

theorem frameScratch_in_frameObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {ec o : Ivl}
    (ho : o ∈ frameScratch s ec) : o ∈ frameObjects s ec := by
  unfold frameScratch at ho
  unfold frameObjects
  apply List.mem_append_left
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
  rcases ho with rfl | rfl | rfl | rfl <;> simp

theorem frameWF_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hA : ArenaOK s) (hFW : FrameWF s S ec) :
    ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64 ∧ memW s (ec.1 + 88) + 24 ≤ 2 ^ 64 ∧
    (∀ o ∈ frameObjects s ec, o.2 = 0 ∨ o.1 + o.2 ≤ 2 ^ 64) := by
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in, hll_ok, _⟩ := hFW
  have he1 := (hscr (ec.1, 280) (by simp)).1
  have he2 := (hscr (ec.2, 104) (by simp)).1
  have he88 := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
  have hstk := (hscr (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
  have hse : scratchEnd ≤ 2 ^ 64 := by rw [scratchEnd_val]; norm_num
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  have hfm_le : globN s "frame_mem_ptr" ≤ 2 ^ 64 := by
    have := hA.2.2.2.1; have := hA.2.2.2.2.1; omega
  have hhp_le : globN s "heap_ptr" ≤ 2 ^ 64 := le_trans hA.2.1 hhl
  refine ⟨le_trans he1.2 hse, le_trans he2.2 hse, le_trans he88.2 hse, fun o ho => ?_⟩
  unfold frameObjects at ho
  rcases List.mem_append.1 ho with ho7 | holog
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
    rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (le_trans he1.2 hse)
    · exact Or.inr (le_trans he2.2 hse)
    · exact Or.inr (le_trans hstk.2 hse)
    · exact Or.inr (le_trans hmem_in.2 hfm_le)
    · exact Or.inr (le_trans he88.2 hse)
    · rcases hlogs_in with h | h
      · exact Or.inr (le_trans h.2 hhp_le)
      · exact Or.inr (le_trans h.2 hse)
    · rcases hret_in with ⟨hz, _⟩ | ⟨h, _⟩
      · unfold frameRet; simp [hz]
      · exact Or.inr (le_trans h.2 hhp_le)
  · unfold frameLogObjects at holog
    dsimp only at holog
    obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx_mem
    rcases hll_ok with hz | ⟨_, _, _, _, hent⟩
    · exfalso
      have hlo := he88.1
      dsimp only at hlo
      have hss : 0 < scratchStart := by rw [scratchStart_val]; decide
      have := hA.2.2.1; have := hA.2.2.2.1
      omega
    · have hle := (hent idx hidx_mem).2
      have ho_rec : o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
        (List.mem_filter.1 ho_own).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
      rcases ho_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (le_trans hle.2.1.2 hhp_le)
      · exact Or.inr (le_trans hle.2.2.2.2.1.2 hhp_le)
      · exact Or.inr (le_trans hle.2.2.2.2.2.1.2 hhp_le)
      · exact Or.inr (le_trans hle.2.2.2.2.2.2.2 hhp_le)

private theorem memW_eq_of_frameDisj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma_s : s.memaddrs = ordinaryDomain)
    {Rl : List Ivl} (heff : ByteRegionEffect s post Rl)
    {base sz k : Nat} (hbnd : base + sz ≤ 2 ^ 64) (hb8 : base % 8 = 0) (hk8 : k % 8 = 0)
    (hk : k + 8 ≤ sz)
    (hdj : ∀ x ∈ Rl, Disj x (base, sz)) :
    memW post (base + k) = memW s (base + k) := by
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  unfold memW
  by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (base + k))
  · have hdom' := (ordinaryDomain_iff _).mp hdom
    have ha_ord : (BitVec.ofNat 64 (base + k)).toNat % 8 = 0 ∧
        sourceBase ≤ (BitVec.ofNat 64 (base + k)).toNat ∧
        (BitVec.ofNat 64 (base + k)).toNat < heapEnd := by
      rw [sourceBase_val, heapEnd_val]; omega
    rcases hp_m : post.memory (BitVec.ofNat 64 (base + k)) with ⟨wp⟩
    rcases hs_m : s.memory (BitVec.ofNat 64 (base + k)) with ⟨ws⟩
    dsimp only
    have hb_eq : ∀ idx < 8, memB post (base + k + idx) = memB s (base + k + idx) := by
      intro idx hidx
      apply heff.byte_frame (base + k + idx) (by omega)
      intro x hx hbx
      obtain ⟨_, _⟩ := hbx
      rcases hdj x hx with h0 | h0 | h | h
      · omega
      · dsimp only at h0; omega
      · dsimp only at h; omega
      · dsimp only at h; omega
    have hbyte_val : ∀ idx < 8,
        (panGetByteHOL (BitVec.ofNat 64 (base + k + idx)) wp s.be).toNat =
        (panGetByteHOL (BitVec.ofNat 64 (base + k + idx)) ws s.be).toNat := by
      intro idx hidx
      have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (base + k + idx)) = BitVec.ofNat 64 (base + k) := by
        apply BitVec.eq_of_toNat_eq
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt ha]
        omega
      have hbk := hb_eq idx hidx
      unfold memB at hbk
      rw [hal_eq, hp_m, hs_m, heff.be] at hbk
      exact hbk
    have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
        w.toNat / 256 ^ idx % 256 =
        (panGetByteHOL (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))) w s.be).toNat := by
      intro w idx hidx
      unfold panGetByteHOL
      change w.toNat / 256 ^ idx % 256 =
        (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
      have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))).toNat % 8
          else (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
        have hmod_lt : (BitVec.ofNat 64 (base + k + (if s.be then 7 - idx else idx))).toNat =
            base + k + (if s.be then 7 - idx else idx) :=
          Nat.mod_eq_of_lt (by cases s.be <;> simp <;> omega)
        rw [hmod_lt]
        cases s.be <;> simp <;> omega
      rw [hexp, UInt8.toNat_ofNat']
      have h256 : (2 ^ 8 : Nat) = 256 := by decide
      rw [h256, Nat.mod_mod]
    have hpow_eq : ∀ idx : Nat, idx < 8 → wp.toNat / 256 ^ idx % 256 = ws.toNat / 256 ^ idx % 256 := by
      intro idx hidx
      rw [hshift wp idx hidx, hshift ws idx hidx]
      exact hbyte_val (if s.be then 7 - idx else idx) (by cases s.be <;> simp <;> omega)
    have hdecomp : ∀ n : Nat, n < 2 ^ 64 →
        n = (n / 256 ^ 0 % 256) +
            (n / 256 ^ 1 % 256) * 256 ^ 1 +
            (n / 256 ^ 2 % 256) * 256 ^ 2 +
            (n / 256 ^ 3 % 256) * 256 ^ 3 +
            (n / 256 ^ 4 % 256) * 256 ^ 4 +
            (n / 256 ^ 5 % 256) * 256 ^ 5 +
            (n / 256 ^ 6 % 256) * 256 ^ 6 +
            (n / 256 ^ 7 % 256) * 256 ^ 7 := by
      intro n hn; omega
    rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
    rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
        hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]
  · rw [heff.out_dom _ (by rwa [hma_s])]

private theorem wordAt_congr_of_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {a : Nat} :
    WordAt post a ↔ WordAt s a := by
  unfold WordAt
  rw [hma]
  constructor
  · rintro ⟨_, hdom, _⟩
    cases hs : s.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases hp : post.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩

private theorem wordsOK_congr_of_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {i : Ivl} :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun _ => imp_congr_right fun _ =>
    wordAt_congr_of_dom hma))

private theorem logRecord_in_frameObjects {F : Type} {s : PanSemStateFiniteExact 64 F} {ec : Ivl}
    {i : Nat} (hi : i < memW s (memW s (ec.1 + 88) + 8)) :
    (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
  unfold frameObjects
  apply List.mem_append_right
  unfold frameLogObjects
  dsimp only
  apply List.mem_flatMap.2
  refine ⟨i, List.mem_range.2 hi, ?_⟩
  unfold logOwnedIvls logRecordIvls
  exact List.mem_filter.2 ⟨by simp, by simp⟩

private theorem logsList_and_objects_congr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hFW : FrameWF s S ec)
    (hdom : post.memaddrs = s.memaddrs)
    (hglob : ∀ nm, globN post nm = globN s nm)
    (he88 : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (h88_eq : ∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i))
    (hlog_rec_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
      ∀ off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off)) :
    frameLogObjects post ec = frameLogObjects s ec ∧
    LogsListOK post (memW post (ec.1 + 88)) := by
  set logs := memW s (ec.1 + 88)
  have hl0 : memW post logs = memW s logs := by simpa [logs] using h88_eq 0 (by omega) (by omega)
  have hl8 : memW post (logs + 8) = memW s (logs + 8) := h88_eq 8 (by omega) (by omega)
  have hl16 : memW post (logs + 16) = memW s (logs + 16) := h88_eq 16 (by omega) (by omega)
  have hlogOwned_eq : ∀ i, i < memW s (logs + 8) →
      logOwnedIvls post (memW post (memW post logs + 8 * i)) =
        logOwnedIvls s (memW s (memW s logs + 8 * i)) := by
    intro i hi
    rw [hl0, harr_eq i hi]
    set lg := memW s (memW s logs + 8 * i)
    have r0 : memW post lg = memW s lg := by simpa [lg] using hlog_rec_eq i hi 0 (by omega) (by omega)
    have r8 : memW post (lg + 8) = memW s (lg + 8) := hlog_rec_eq i hi 8 (by omega) (by omega)
    have r16 : memW post (lg + 16) = memW s (lg + 16) := hlog_rec_eq i hi 16 (by omega) (by omega)
    have r24 : memW post (lg + 24) = memW s (lg + 24) := hlog_rec_eq i hi 24 (by omega) (by omega)
    have r32 : memW post (lg + 32) = memW s (lg + 32) := hlog_rec_eq i hi 32 (by omega) (by omega)
    unfold logOwnedIvls logRecordIvls
    rw [r0, r8, r16, r24, r32, hglob "vm_system_address"]
  refine ⟨?_, ?_⟩
  · unfold frameLogObjects
    dsimp only
    rw [he88, hl8]
    apply List.flatMap_congr
    intro i hi
    rw [List.mem_range] at hi
    exact hlogOwned_eq i hi
  · rw [he88]
    rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
    · exact Or.inl hz
    · right
      have hal_post : Allocated post (logs, 24) := by
        unfold Allocated at hal_l ⊢; simp only [hglob]; exact hal_l
      refine ⟨(wordsOK_congr_of_dom hdom).2 hw_l, hal_post, by rw [hl8]; exact hlt28,
        by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
      rw [hl8] at hi
      rw [hl0]
      obtain ⟨hwa, hle⟩ := hent i hi
      refine ⟨(wordAt_congr_of_dom hdom).2 hwa, ?_⟩
      rw [harr_eq i hi]
      set lg := memW s (memW s logs + 8 * i)
      have r0 : memW post lg = memW s lg := by simpa [lg] using hlog_rec_eq i hi 0 (by omega) (by omega)
      have r8 : memW post (lg + 8) = memW s (lg + 8) := hlog_rec_eq i hi 8 (by omega) (by omega)
      have r16 : memW post (lg + 16) = memW s (lg + 16) := hlog_rec_eq i hi 16 (by omega) (by omega)
      have r24 : memW post (lg + 24) = memW s (lg + 24) := hlog_rec_eq i hi 24 (by omega) (by omega)
      have r32 : memW post (lg + 32) = memW s (lg + 32) := hlog_rec_eq i hi 32 (by omega) (by omega)
      unfold LogEntryOK at hle ⊢
      rw [r0, r8, r16, r24, r32, hglob "heap_ptr"]
      exact ⟨(wordsOK_congr_of_dom hdom).2 hle.1, hle.2⟩

private theorem worldTableRefs_eq_of_cell {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaOK s) (hWT : WorldTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hglob_eq : ∀ nm, globN post nm = globN s nm) :
    worldTableRefs post S = worldTableRefs s S := by
  unfold worldTableRefs recordSlots
  rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
      show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
        simp only [globalTableRoots, List.map, hglob_eq],
      balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
      hglob_eq "journal_n", hglob_eq "journal"]
  have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
      (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 40 := by
        simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
  have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
      (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 80 := by
        simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
  have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
      (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
    split
    · rfl
    · rename_i hnz
      apply List.map_congr_left; intro k hk
      have hk_le : k + 8 ≤ 72 := by
        simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      exact memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
  have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
      (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
    by_cases hnz : globN s "bs" = 0
    · simp [hnz]
    · rw [memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
      by_cases hmS : memW s (globN s "bs" + 32) ∈ S
      · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
      · simp [hnz, hmS]
  have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
      (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
    by_cases hnz : globN s "ts" = 0
    · simp [hnz]
    · rw [memW_typedRec_eq hAs hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
      by_cases hmS : memW s (globN s "ts" + 32) ∈ S
      · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
      · simp [hnz, hmS]
  have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
      (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
    apply List.flatMap_congr; intro ad had
    have had_mem := balRecord_ivl_mem had
    rcases fixedObject_le_2pow64 hAs hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
    · dsimp only at h0; omega
    · dsimp only at had_bnd
      have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
      rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
          memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
  have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
      (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
    apply List.map_congr_left; intro k hk
    rw [List.mem_range] at hk
    have hjc_ne : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
    rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
    · exact absurd h0 hjc_ne
    · have hbnd := allocated_le_2pow64 hAs hal
      dsimp only at hbnd
      have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
      exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd) hjc_ne)
        ⟨by dsimp only; omega, by dsimp only; omega⟩
  dsimp only
  rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]

/-! ### Intersection of two `TriesTypedWith` witnesses -/

theorem triesTypedWith_inter {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd1 Nd2 : List Nat}
    (h1 : TriesTypedWith s S Nd1) (h2 : TriesTypedWith s S Nd2) :
    let Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
    TriesTypedWith s S Nd ∧
    (∀ x ∈ nodeExtents s Nd, x ∈ nodeExtents s Nd1 ∧ x ∈ nodeExtents s Nd2) := by
  dsimp only
  set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hmem_iff : ∀ n, n ∈ Nd ↔ n ∈ Nd1 ∧ n ∈ Nd2 := by
    intro n; simp [Nd, List.mem_filter]
  have hroot_iff : ∀ v, RootIn Nd1 v → RootIn Nd2 v → RootIn Nd v := by
    intro v r1 r2
    rcases r1 with rfl | hm1
    · exact Or.inl rfl
    · rcases r2 with rfl | hm2
      · exact Or.inl rfl
      · exact Or.inr ((hmem_iff v).2 ⟨hm1, hm2⟩)
  have hne_sub : ∀ x ∈ nodeExtents s Nd, x ∈ nodeExtents s Nd1 ∧ x ∈ nodeExtents s Nd2 := by
    intro x hx
    unfold nodeExtents at hx ⊢
    obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hx
    obtain ⟨hn1, hn2⟩ := (hmem_iff n).1 hn
    exact ⟨List.mem_flatMap.2 ⟨n, hn1, hnx⟩, List.mem_flatMap.2 ⟨n, hn2, hnx⟩⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hne_sub⟩
  · intro n hn
    obtain ⟨hn1, hn2⟩ := (hmem_iff n).1 hn
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := h1.1.1 n hn1
    obtain ⟨_, _, _, _, d5, d6, _⟩ := h2.1.1 n hn2
    refine ⟨c1, c2, c3, c4, fun hk2 => hroot_iff _ (c5 hk2) (d5 hk2),
      fun hk3 i hi => hroot_iff _ (c6 hk3 i hi) (d6 hk3 i hi), ?_, c8, c9, c10⟩
    intro h12
    rcases c7 h12 with hz | ⟨hnib, hal, hin, hdj⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hnib, hal, hin, fun m hm => hdj m ((hmem_iff m).1 hm).1⟩
  · intro n hn m hm hne
    exact h1.1.2 n ((hmem_iff n).1 hn).1 m ((hmem_iff m).1 hm).1 hne
  · intro o ho
    exact h1.2.1 o (hne_sub o ho).1
  · intro hws
    obtain ⟨r1_24, r1_32⟩ := h1.2.2 hws
    obtain ⟨r2_24, r2_32⟩ := h2.2.2 hws
    exact ⟨hroot_iff _ r1_24 r2_24, fun htS i hi => hroot_iff _ (r1_32 htS i hi) (r2_32 htS i hi)⟩

/-- Monotonicity of `SameTypedCells` wrt `Nd`: if `∀ n ∈ Ndi, n ∈ Nd` and `nodeIvl`/`nodePath`
for `n ∈ Ndi` are in `nodeExtents s Nd`, then `SameTypedCells s post S Nd` implies
`SameTypedCells s post S Ndi`! -/
private theorem sameTypedCells_sub_nd {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd Ndi : List Nat}
    (hsub : ∀ n ∈ Ndi, n ∈ Nd)
    (hcell : SameTypedCells s post S Nd) :
    SameTypedCells s post S Ndi := by
  have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd := by
    intro i hi
    unfold worldTypedIvls at hi ⊢
    rcases List.mem_append.1 hi with hpre | hne
    · exact List.mem_append_left _ hpre
    · apply List.mem_append_right
      unfold nodeExtents at hne ⊢
      obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
      exact List.mem_flatMap.2 ⟨n, hsub n hn, hnx⟩
  refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1, ?_, ?_⟩
  · intro a ha ha8 ⟨i, hi, h1, h2⟩
    exact hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩
  · intro b hb ⟨i, hi, h1, h2⟩
    exact hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩

private theorem msgOwned_congr {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {m : Nat}
    (hAs : ArenaReady s) (hApost : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hdom : post.memaddrs = s.memaddrs)
    (hglob : ∀ nm, globN post nm = globN s nm)
    (hWT_base : TablesTyped s S ∧ JournalTyped s S ∧ FixedTyped s)
    (hFT_post : FixedTyped post)
    (hfeq : fixedObjects post = fixedObjects s)
    (hTr : TriesTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hfp_eq : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hchain_eq : evmChain post = evmChain s)
    (hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec)
    (hmsg : MsgOwned s S m) :
    MsgOwned post S m := by
  obtain ⟨hal, hw, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := hmsg
  obtain ⟨hTr_int, hsub_int⟩ := triesTypedWith_inter hTr hTr_m
  set Ndi := Nd.filter (fun n => decide (n ∈ Nd_m))
  have hsub_nd : ∀ n ∈ Ndi, n ∈ Nd := fun n hn => (List.mem_filter.1 hn).1
  have hcell_i : SameTypedCells s post S Ndi := sameTypedCells_sub_nd hsub_nd hcell
  have hWT_i : WorldTypedWith s S Ndi := ⟨hWT_base.1, hWT_base.2.1, hWT_base.2.2, hTr_int⟩
  obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc hg hcell_i hWT_i
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hne_i_eq := nodeExtents_eq hTr_int.1 hcell_i
  have hal_post : Allocated post (m, 176) := by
    unfold Allocated at hal ⊢; simp only [hglob]; exact hal
  refine ⟨hal_post, (wordsOK_congr_of_dom hdom).2 hw, ?_, ?_, ?_, Ndi, hWT_i_post.2.2.2, ?_⟩
  · intro t ht i hi
    rw [hfp_eq t ht] at hi
    exact hdt t ht i hi
  · rw [hfeq]; exact hdf
  · rw [hchain_eq]
    intro ec hec o ho
    rw [hfo_eq ec hec] at ho
    exact hdfo ec hec o ho
  · intro o ho j hj
    rw [hne_i_eq] at hj
    exact hdj_m o ho j (hsub_int j hj).2

/-! ## 3. `ByteRegionEffect.to_evmStep_nil_with` and `ByteRegionEffect.to_evmStep_avoids` -/

theorem ByteRegionEffect.to_evmStep_nil_with {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {S Nd : List Nat}
    (hAs : ArenaReady s) (hInv : EvmInvAt s S) (hTr : TriesTypedWith s S Nd)
    (hAT_Nd : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd, Disj o j)
    (hdj : IvlsDisj Rl (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten))
    (heff : ByteRegionEffect s post Rl) :
    EvmStep [] s post := by
  have hWT : WorldTypedWith s S Nd := ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr⟩
  have hdj_w : IvlsDisj Rl (worldTypedIvls s S Nd) :=
    fun x hx i hi => hdj x hx i (List.mem_append_left _ hi)
  have hdj_f : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, ∀ x ∈ Rl, Disj x o := by
    intro ec hec o ho x hx
    apply hdj x hx o
    apply List.mem_append_right
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩
  have heff' : ByteRegionEffect s post (Rl ++ []) := by simpa using heff
  have hWS : WorldStep (fun {F} _ => Rl) [] stdKeep NoExtra s none post :=
    ByteRegionEffect.to_worldStep (R := fun {F} _ => Rl) (extra := fun {F} _ => []) (r := none)
      ⟨hAs, S, hInv.1⟩ (fun _ h => by simp at h) heff'
  obtain ⟨hApost, hh, hG, _, _⟩ := hWS
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hcell : SameTypedCells s post S Nd :=
    ByteRegionEffect.sameTypedCells hAs.1.memaddrs hWT hdj_w (fun _ h => by simp at h) heff'
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  obtain ⟨_, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 hFW
    have he1_8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have he2_8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have he88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    refine ⟨fun k hk hk8 => memW_eq_of_frameDisj hAs.1.memaddrs heff hb1 he1_8 hk8 hk
              (hdj_f ec hec (ec.1, 280) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_frameDisj hAs.1.memaddrs heff hb2 he2_8 hk8 hk
              (hdj_f ec hec (ec.2, 104) (by simp [frameObjects])),
            fun k hk hk8 => memW_eq_of_frameDisj hAs.1.memaddrs heff hb88 he88_8 hk8 hk
              (hdj_f ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]))⟩
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec' hec'
        apply hsub ec'
        simp only [evmChainFrom, hne16, ↓reduceIte, List.mem_cons]
        exact Or.inr hec'
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux (Wave8GuestInv.maxChain + 1) (globN s "ev") (globN s "cur_cont") (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    refine logsList_and_objects_congr hFW heff.memaddrs hglob_eq
      (he_eq 88 (by omega) (by omega)) h88_eq ?_ ?_
    · intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
          hFW.2.2.2.2.2.2.2.2.2.2.2.1
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      exact memW_eq_of_frameDisj hAs.1.memaddrs heff hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega)
        (hdj_f ec hec (frameLogs s ec) hfl_in)
    · intro i hi off hoff hoff8
      have hlr_in := logRecord_in_frameObjects (s := s) (ec := ec) hi
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have hss : 0 < scratchStart := by rw [scratchStart_val]; decide
          have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; have := he88_in.1
          dsimp only at this
          omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_frameDisj hAs.1.memaddrs heff hlr_b hlr_8 hoff8 hoff
        (hdj_f ec hec _ hlr_in)
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega)]
      exact msgOwned_congr hAs hApost hh hsc (fun g _ => hglob_eq g) heff.memaddrs hglob_eq
        ⟨hWT.1, hWT.2.1, hWT.2.2.1⟩ hFT_post hfeq hTr hcell hfp_eq_all hchain_eq hframeObjects_eq c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 16 (by omega) (by omega),
        he_eq 32 (by omega) (by omega), he_eq 136 (by omega) (by omega),
        he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    rw [he_eq 88 (by omega) (by omega)] at hlo_ok
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_, hlo_ok, hmsg_ok⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
  · intro ec hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by omega), (hrec_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega), (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfeq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [hfp_eq_all t ht] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr.1 hcell] at hj
    exact hAT_Nd o ho j hj
  · have hworldRefs_eq := worldTableRefs_eq_of_cell hAs.2 hWT hcell hglob_eq
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k % 8 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_le.1 hk_le.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]
      exact m8 t ht
  · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
    rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]
    exact ⟨haS, hkl⟩
  · have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec hec
      rw [(hrec_eq ec hec).1 64 (by omega) (by omega), (hrec_eq ec hec).1 192 (by omega) (by omega)]
    rw [hmap_gas]
    exact hGas

theorem ByteRegionEffect.to_evmStep_avoids {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F}
    (hAv : EvmAvoids R s)
    (heff : ByteRegionEffect s post (R s)) :
    EvmStep [] s post := by
  obtain ⟨hAs, S, hInv, Nd1, hTr1, hdj1⟩ := hAv
  obtain ⟨Nd2, hTr2, hAT2⟩ := hInv.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hTr_int, hsub_int⟩ := triesTypedWith_inter hTr1 hTr2
  refine ByteRegionEffect.to_evmStep_nil_with hAs hInv hTr_int ?_ ?_ heff
  · intro o ho j hj
    exact hAT2 o ho j (hsub_int j hj).2
  · intro x hx i hi
    apply hdj1 x hx i
    rcases List.mem_append.1 hi with hi_w | hi_f
    · apply List.mem_append_left
      unfold worldTypedIvls at hi_w ⊢
      rcases List.mem_append.1 hi_w with hi_pre | hi_ne
      · exact List.mem_append_left _ hi_pre
      · exact List.mem_append_right _ (hsub_int i hi_ne).1
    · exact List.mem_append_right _ hi_f

/-! ## 4. General head-frame word-update lemma (`16` for `stack_pop`, `64`/`184` for `charge_gas`) -/

/-- General lemma for updating only offsets `{16, 64, 184}` of the head frame `e0 = globN s "ev"`
(with `memW post (e0 + 16) ≤ memW s (e0 + 16)` and `memW post (e0 + 64) ≤ memW s (e0 + 64)`,
leaving globals, endianness, domains, and all other memory cells unchanged):
preserves `EvmInv`, `heap_ptr`, globals, and `evmChain`! -/
theorem evmStep_of_head_16_64_184 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
      x ≠ BitVec.ofNat 64 (globN s "ev" + 64) →
      x ≠ BitVec.ofNat 64 (globN s "ev" + 184) →
      post.memory x = s.memory x)
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16))
    (hgas_le : memW post (globN s "ev" + 64) ≤ memW s (globN s "ev" + 64)) :
    EvmStep [] s post := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_eq_cons : ∃ tail, evmChain s = (e0, c0) :: tail := by
    unfold evmChain
    exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_eq_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_align : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have ha16_nat : (BitVec.ofNat 64 (e0 + 16)).toNat = e0 + 16 := Nat.mod_eq_of_lt (by omega)
  have ha64_nat : (BitVec.ofNat 64 (e0 + 64)).toNat = e0 + 64 := Nat.mod_eq_of_lt (by omega)
  have ha184_nat : (BitVec.ofNat 64 (e0 + 184)).toNat = e0 + 184 := Nat.mod_eq_of_lt (by omega)
  have hdom_slot : ∀ k ∈ ([16, 64, 184] : List Nat), s.memaddrs (BitVec.ofNat 64 (e0 + k)) := by
    intro k hk
    have hdiv : k / 8 < 280 / 8 ∧ 8 * (k / 8) = k := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (k / 8) hdiv.1
    simpa [hdiv.2] using hdom
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  -- `ByteRegionEffect s post [(e0, 280)]`:
  have heff : ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_out a
      · rintro rfl; exact hna (hdom_slot 16 (by simp))
      · rintro rfl; exact hna (hdom_slot 64 (by simp))
      · rintro rfl; exact hna (hdom_slot 184 (by simp))
    · intro a ha
      apply hmem_out a
      · rintro rfl; exact ha (e0, 280) (by simp) ⟨by rw [ha16_nat]; omega, by rw [ha16_nat]; omega⟩
      · rintro rfl; exact ha (e0, 280) (by simp) ⟨by rw [ha64_nat]; omega, by rw [ha64_nat]; omega⟩
      · rintro rfl; exact ha (e0, 280) (by simp) ⟨by rw [ha184_nat]; omega, by rw [ha184_nat]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      · intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha16_nat] at this
        exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha64_nat] at this
        exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      · intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha184_nat] at this
        exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [hglob]
  -- `(e0, 280)` is disjoint from every non-empty interval in `worldTypedIvls s S Nd_at`:
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (e0, 280) i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; simp
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · have hfl : (e0, 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
        rw [List.mem_flatten]
        exact ⟨frameObjects s (e0, c0), List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩
      exact Or.inr (hAT_at _ hfl i h6)
  have hcell : SameTypedCells s post S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [(e0, 280)]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
      (by simpa using heff)
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [hglob])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  -- Word equality outside `{e0+16, e0+64, e0+184}`:
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 → a ≠ e0 + 16 → a ≠ e0 + 64 → a ≠ e0 + 184 →
      memW post a = memW s a := by
    intro a ha h1 h2 h3
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    · intro heq; have := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, ha16_nat] at this; exact h1 this
    · intro heq; have := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, ha64_nat] at this; exact h2 this
    · intro heq; have := congrArg BitVec.toNat heq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, ha184_nat] at this; exact h3 this
  -- Pairwise disjointness of `frameObjects`: `(e0, 280)` is index 0 of frame 0, so it is `Disj` from:
  -- * every object at index `≥ 1` of frame 0 (including `(c0, 104)`, `(memW s (e0+88), 24)`, `frameLogs`, and every `(lg, 40)` in `frameLogObjects`)!
  -- * EVERY object in `frameObjects s ec` for `ec ∈ chTail`!
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_tail_fo : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    change ((e0, 280) :: ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0))).Pairwise Disj at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_cons, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_tail_fo _ (by simp), hhead_disj_tail_fo _ (by simp),
        hhead_disj_tail_fo _ (by simp), fun i hi => hhead_disj_tail_fo _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ (logRecord_in_frameObjects hi)⟩
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ≠ 16 → k ≠ 64 → k ≠ 184 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => memW_eq_of_frameDisj hAs.1.memaddrs heff hb_c hc8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => memW_eq_of_frameDisj hAs.1.memaddrs heff hb_88 h88_8 hk8 hk
        (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hk16 hk64 hk184
    apply hmemW_ne (ec.1 + k) (by omega)
    all_goals
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · dsimp only; omega
      · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
        rcases hd with h0 | h0 | h1 | h2
        · dsimp only at h0; omega
        · dsimp only at h0; omega
        · dsimp only at h1 ⊢; omega
        · dsimp only at h2 ⊢; omega
  have htail_all_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    exact memW_eq_of_frameDisj hAs.1.memaddrs heff hb_e he8 hk8 hk
      (fun x hx => by simp at hx; subst hx; exact hd)
  -- `evmChain post = evmChain s`:
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_other_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec' hec'
        apply hsub ec'
        simp only [evmChainFrom, hne16, ↓reduceIte, List.mem_cons]
        exact Or.inr hec'
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux (Wave8GuestInv.maxChain + 1) (globN s "ev") (globN s "cur_cont") (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    refine logsList_and_objects_congr hFW hdom_eq hglob_eq
      (he_eq 88 (by omega) (by omega) (by omega) (by omega)) h88_eq ?_ ?_
    · intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_frameDisj hAs.1.memaddrs heff hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    · intro i hi off hoff hoff8
      have hlr_in := logRecord_in_frameObjects (s := s) (ec := ec) hi
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have hss : 0 < scratchStart := by rw [scratchStart_val]; decide
          have := hAs.2.2.2.1; have := hAs.2.2.2.2.1; have := he88_in.1
          dsimp only at this
          omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_frameDisj hAs.1.memaddrs heff hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega) (by omega),
        he_eq 40 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have he16_le : memW post (ec.1 + 16) ≤ memW s (ec.1 + 16) := by
      have hec' := hec
      rw [hch_cons, List.mem_cons] at hec'
      rcases hec' with rfl | htail
      · exact hsp_le
      · rw [htail_all_eq ec htail 16 (by omega) (by omega)]
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega) (by omega) (by omega)]
      exact msgOwned_congr hAs hApost hh hsc (fun g _ => hglob_eq g) hdom_eq hglob_eq
        ⟨hWT.1, hWT.2.1, hWT.2.2.1⟩ hFT_post hfeq hTr_at hcell hfp_eq_all hchain_eq hframeObjects_eq c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega) (by omega),
        he_eq 40 (by omega) (by omega) (by omega) (by omega),
        he_eq 32 (by omega) (by omega) (by omega) (by omega),
        he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)] at hlo_ok
    refine ⟨?_, c2, (wordsOK_congr_of_dom hdom_eq).2 c3, c4, le_trans he16_le c5, c6, c7,
      c8, c9, c10, c11, c12, c13, (wordsOK_congr_of_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, (wordsOK_congr_of_dom hdom_eq).2 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_of_dom hdom_eq).2 hw⟩
  · intro ec hec
    have hec_tail : ec ∈ chTail := by rw [hch_cons, List.tail_cons] at hec; exact hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [htail_all_eq ec hec_tail 16 (by omega) (by omega),
        htail_all_eq ec hec_tail 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_other_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_other_eq _ hi1).1 40 (by omega) (by omega) (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfeq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [hfp_eq_all t ht] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    exact hAT_at o ho j hj
  · have hworldRefs_eq := worldTableRefs_eq_of_cell hAs.2 hWT hcell hglob_eq
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k ≠ 16 ∧ k ≠ 64 ∧ k ≠ 184 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
      rw [(hrec_other_eq _ hj_mem).1 k hk_le.1 hk_le.2.1 hk_le.2.2.1 hk_le.2.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega) (by omega) (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_other_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]
      exact m8 t ht
  · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
    rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]
    exact ⟨haS, hkl⟩
  · have hsum_le : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      rw [hch_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have h192_0 := (hrec_other_eq (e0, c0) hhead_mem).1 192 (by omega) (by omega) (by omega) (by omega)
      have htail_map : (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
          (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
        apply List.map_congr_left; intro ec htail
        rw [htail_all_eq ec htail 64 (by omega) (by omega),
            htail_all_eq ec htail 192 (by omega) (by omega)]
      dsimp only at h192_0 ⊢
      rw [h192_0, htail_map]
      exact Nat.add_le_add_right (Nat.add_le_add_right hgas_le _) _
    omega

/-- Specialization to `off = 16` (`stack_pop`). -/
theorem evmStep_of_head_sp_dec {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {ev sp1 : BitVec 64}
    (hInv : EvmInv s)
    (hev : s.globals.lookup (ofString "ev") = some (.val (.word ev)))
    (hsp_pos : 0 < memW s (globN s "ev" + 16))
    (hsp1 : sp1.toNat = memW s (globN s "ev" + 16) - 1)
    (hpost : post = { s with
      memory := fun a => if a = ev + 16 then .word sp1 else s.memory a,
      locals := post.locals,
      clock := post.clock }) :
    EvmStep [] s post := by
  have hev_nat : ev.toNat = globN s "ev" := by simp [globN, hev]
  have hb1 : globN s "ev" + 280 ≤ 2 ^ 64 := by
    obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
    exact (frameWF_bounds hAs.2 (hFW_all (globN s "ev", globN s "cur_cont") (by simp [evmChain, evmChainFrom]))).1
  have hev16_eq : ev + 16 = BitVec.ofNat 64 (globN s "ev" + 16) := by
    apply BitVec.eq_of_toNat_eq
    have : (16 : BitVec 64).toNat = 16 := rfl
    rw [BitVec.toNat_add, hev_nat, this, BitVec.toNat_ofNat]
  have hne_16_64 : BitVec.ofNat 64 (globN s "ev" + 64) ≠ ev + 16 := by
    rw [hev16_eq]; intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hGp : GuestInv post := by
    rw [hpost]; exact guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1
  apply evmStep_of_head_16_64_184 hInv hGp (by rw [hpost]) (by rw [hpost])
  · intro x hx1 _ _
    rw [hpost]; dsimp only
    rw [if_neg (hev16_eq.symm ▸ hx1)]
  · have hm_post : memW post (globN s "ev" + 16) = sp1.toNat := by
      unfold memW; rw [hpost]; dsimp only; rw [if_pos hev16_eq.symm]
    rw [hm_post, hsp1]
    omega
  · unfold memW
    rw [hpost]; dsimp only
    rw [if_neg hne_16_64]

end InitECandidate.Solver.Wave8Contracts.M23
