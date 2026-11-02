import InitECandidate.Solver.Wave8GuestInv.Deliveries.M22.StepLemmas

/-! EVM-frame invariant (`EvmInv`, `EvmStep`, `EvmKeeps`, `EvmAvoids`) congruence lemmas for
micro-shard `m22` (`wave8/contracts-m22`).
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M22

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim EVM contract definitions from `Contracts.lean` (rev9 `8a79d9f28`) -/

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
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
  rcases ho with rfl | rfl | rfl | rfl <;> simp

theorem frameWF_bounds {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hA : ArenaOK s) (hFW : FrameWF s S ec) :
    ec.1 + 280 ≤ 2 ^ 64 ∧ ec.2 + 104 ≤ 2 ^ 64 ∧ memW s (ec.1 + 88) + 24 ≤ 2 ^ 64 ∧
    (∀ o ∈ frameObjects s ec, o.2 = 0 ∨ o.1 + o.2 ≤ 2 ^ 64) := by
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, _, _, hlogs_in, _, hret_in⟩ := hFW
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
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private theorem memW_eq_of_frameDisj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (heff : ByteRegionEffect s post Rl)
    {base sz k : Nat} (hbnd : base + sz ≤ 2 ^ 64) (hk : k + 8 ≤ sz)
    (hdj : ∀ x ∈ Rl, Disj x (base, sz)) :
    memW post (base + k) = memW s (base + k) := by
  unfold memW
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  rw [heff.cell_frame (BitVec.ofNat 64 (base + k)) (fun x hx => by
    rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) (by dsimp only; omega) (by dsimp only; omega)
      (Disj.symm (hdj x hx)))]

private theorem wordsOK_congr_of_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {i : Ivl} :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK WordAt
  rw [hma]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun k => imp_congr_right fun _ => ?_))
  constructor
  · rintro ⟨_, hdom, _⟩
    cases hs : s.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases hp : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with
    | word w => exact ⟨w, hdom, rfl⟩

/-- If `heff : ByteRegionEffect s post Rl` avoids every interval of
`worldTypedIvls s S Nd ++ (evmChain s).flatMap (frameObjects s)` AND `AvoidsTries` holds on `Nd`
(in particular when `Rl = []` we pick `Nd := Nd_at` from `hInv`'s `AvoidsTries`), then
`EvmStep [] s post` holds! -/
theorem ByteRegionEffect.to_evmStep_nil_with {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {S Nd : List Nat}
    (hAs : ArenaReady s) (hInv : EvmInvAt s S) (hTr : TriesTypedWith s S Nd)
    (hAT_Nd : ∀ o ∈ ((evmChain s).map (frameObjects s)).flatten, ∀ j ∈ nodeExtents s Nd, Disj o j)
    (hdj : ∀ x ∈ Rl, ∀ o ∈ worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten,
      o.2 = 0 ∨ Disj x o)
    (heff : ByteRegionEffect s post Rl) :
    EvmStep [] s post := by
  have hWT : WorldTypedWith s S Nd := ⟨hInv.1.1, hInv.1.2.1, hInv.1.2.2.1, hTr⟩
  have hdj_w : ∀ x ∈ Rl, ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i :=
    fun x hx i hi => hdj x hx i (List.mem_append_left _ hi)
  have hdj_f : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.2 ≠ 0 → ∀ x ∈ Rl, Disj x o := by
    intro ec hec o ho honz x hx
    rcases hdj x hx o (List.mem_append_right _ (List.mem_flatten.2
      ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩)) with h0 | hd
    · exact absurd h0 honz
    · exact hd
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hApost : ArenaReady post := by
    refine ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1, ?_⟩
    unfold ArenaOK; simp only [hglob_eq]; exact hAs.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  have hbfr : ByteFrameOutside s post ([] ++ Rl ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx => ha x (List.mem_append_left [freeGap s] (by simpa using hx)))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx; rw [hbit]
      exact not_cellHits_of_disj_aligned (i := (a, 8)) (by omega) (by omega)
        (hdja x (List.mem_append_left [freeGap s] (by simpa using hx)))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx => hno x (List.mem_append_left [freeGap s] (by simpa using hx)))
  have hcell : SameTypedCells s post S Nd :=
    sameTypedCells_of_byteFrame hAs hWT (fun _ h => by simp at h) hdj_w hbfr
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd, hWT_post.2.2.2⟩
  -- 2. Show every frame `ec ∈ evmChain s` has identical record/continuation/logs-header words in `post`!
  obtain ⟨_, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb1, hb2, hb88, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    refine ⟨fun k hk => memW_eq_of_frameDisj heff hb1 hk (hdj_f ec hec (ec.1, 280) (by simp [frameObjects]) (by simp)),
            fun k hk => memW_eq_of_frameDisj heff hb2 hk (hdj_f ec hec (ec.2, 104) (by simp [frameObjects]) (by simp)),
            fun k hk => memW_eq_of_frameDisj heff hb88 hk (hdj_f ec hec (memW s (ec.1 + 88), 24) (by simp [frameObjects]) (by simp))⟩
  -- 3. `evmChain post = evmChain s` by induction on fuel along suffixes of `evmChainFrom`!
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
      have hc16 := hc_eq 16 (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega)
      have hc8 := hc_eq 8 (by omega)
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
  -- 4. `frameLogs`, `frameRet`, `frameObjects`, `frameScratch`, `frameRoleSlots` equality on `evmChain s`
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega), show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega), he_eq 144 (by omega)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 24 (by omega), he_eq 40 (by omega),
        he_eq 88 (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega), he_eq 168 (by omega), he_eq 176 (by omega)]
  -- 5. Assemble `EvmInv post`!
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hFW_all ec hec
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega), he_eq 24 (by omega),
        he_eq 40 (by omega), he_eq 16 (by omega), he_eq 32 (by omega), he_eq 136 (by omega),
        he_eq 168 (by omega), he_eq 176 (by omega),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega), he_eq 144 (by omega), hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
  · intro ec hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega), (hrec_eq ec hec_mem).1 232 (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega), (hrec_eq _ hi0).2.1 72 (by omega),
        (hrec_eq _ hi1).1 40 (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfeq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr.1 hcell] at hj
    exact hAT_Nd o ho j hj
  · -- `MarksOK post S (evmChain s)`:
    have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
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
          have hk_le : k + 8 ≤ 40 := by simp [wsTableSlots] at hk; subst hk; omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 80 := by
            simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 72 := by
            simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk
        rw [List.mem_range] at hk
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · have := hWT.2.1.1; omega
        · have hbnd := allocated_le_2pow64 hAs.2 hal
          dsimp only at hbnd
          have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd))
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> omega
      rw [(hrec_eq _ hj_mem).1 k hk_le]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem]
      exact m5 j hj hij
    · intro t ht
      rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1, hdelEx_iff i t]
      exact m8 t ht
  · -- `RolesOK post S (worldRoleSlots post ++ frameRoleSlots post (evmChain s)) (journalRoleSlots post)`:
    have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
    rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]
    exact ⟨haS, hkl⟩
  ·     -- Gas sum `< 2^64`:
    have hmap_gas : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec hec
      rw [(hrec_eq ec hec).1 64 (by omega), (hrec_eq ec hec).1 192 (by omega)]
    rw [hmap_gas]
    exact hGas

/-- General single-word update inside the head frame `(globN s "ev", globN s "cur_cont")` at a field
offset `off` that does NOT affect `frameObjects`, `evmChain`, `frameRoleSlots`, `RetWindowsOK`,
`MarksOK`, or gas (`off = 16`, stack height)! -/
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
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  have hev_nat : ev.toNat = globN s "ev" := by simp [globN, hev]
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm, evmChainFrom]
    exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have hev16_nat : (ev + 16).toNat = globN s "ev" + 16 := by
    simp only [BitVec.toNat_add, hev_nat]
    have : (16 : BitVec 64).toNat = 16 := rfl
    rw [this]; omega
  have hev_align : (globN s "ev") % 8 = 0 :=
    (hhead_FW.1 (globN s "ev", 280) (by simp)).2.1
  -- Show `(globN s "ev", 280)` is disjoint from every `worldTypedIvls s S Nd_at`:
  have hrec_fo : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (globN s "ev", 280) i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; simp
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · have hfl : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
        rw [List.mem_flatten]
        exact ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
          List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩
      exact Or.inr (hAT_at _ hfl i h6)
  -- `ByteRegionEffect s post [(globN s "ev" + 16, 8)]`:
  have hdom16 : s.memaddrs (ev + 16) := by
    have hw := (hhead_FW.1 (globN s "ev", 280) (by simp)).2.2.2 2 (by omega)
    obtain ⟨_, hdom, _⟩ := hw
    have heq_bv : BitVec.ofNat 64 (globN s "ev" + 8 * 2) = ev + 16 := by
      apply BitVec.eq_of_toNat_eq
      rw [hev16_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rwa [← heq_bv]
  have heff : ByteRegionEffect s post [(globN s "ev" + 16, 8)] := by
    rw [hpost]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro a hna; dsimp only
      have hne : a ≠ ev + 16 := by rintro rfl; exact hna hdom16
      rw [if_neg hne]
    · intro a ha; dsimp only
      have hne : a ≠ ev + 16 := by
        rintro rfl
        exact ha (globN s "ev" + 16, 8) (by simp) ⟨by rw [hev16_nat]; omega, by rw [hev16_nat]; omega⟩
      rw [if_neg hne]
    · intro b hb hno
      unfold memB; dsimp only
      have hne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ ev + 16 := by
        intro heq
        have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
          rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
        rw [heq, hev16_nat] at hal_b
        exact hno (globN s "ev" + 16, 8) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
      rw [if_neg hne]
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by rw [hpost]; rfl
  have hApost : ArenaReady post := by
    refine ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1, ?_⟩
    unfold ArenaOK; simp only [hglob_eq]; exact hAs.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun name _ => by rw [hpost]
  -- `SameTypedCells s post S Nd_at`:
  have hdj_16_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (globN s "ev" + 16, 8) i := by
    intro i hi
    rcases hrec_disj_wti i hi with h0 | hdj
    · exact Or.inl h0
    · right
      rcases hdj with h1 | h2
      · exact Or.inl (by dsimp only at h1 ⊢; omega)
      · exact Or.inr (by dsimp only at h2 ⊢; omega)
  have hbfr : ByteFrameOutside s post ([] ++ [(globN s "ev" + 16, 8)] ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx => ha x (by simp at hx; subst hx; simp))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx; rw [hbit]
      exact not_cellHits_of_disj_aligned (i := (a, 8)) (by omega) (by omega)
        (hdja x (by simp at hx; subst hx; simp))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx => hno x (by simp at hx; subst hx; simp))
  have hcell : SameTypedCells s post S Nd_at :=
    sameTypedCells_of_byteFrame hAs hWT (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hdj_16_wti) hbfr
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  -- Helper: any word `a < 2^64` with `a ≠ globN s "ev" + 16` and `a % 8 = 0` has `memW post a = memW s a`!
  have hmemW_ne16 : ∀ a : Nat, a < 2 ^ 64 → a ≠ globN s "ev" + 16 → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hpost]; dsimp only
    have hbv_ne : BitVec.ofNat 64 a ≠ ev + 16 := by
      intro heq
      have h1 : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      rw [heq, hev16_nat] at h1
      exact hne h1.symm
    rw [if_neg hbv_ne]
  have hmemW_16 : memW post (globN s "ev" + 16) = sp1.toNat := by
    unfold memW; rw [hpost]; dsimp only
    have hbv_eq : BitVec.ofNat 64 (globN s "ev" + 16) = ev + 16 := by
      apply BitVec.eq_of_toNat_eq
      rw [hev16_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos hbv_eq]
  -- Pairwise disjointness of `(evmChain s).flatMap (frameObjects s)` implies:
  -- 1) For EVERY `ec ∈ evmChain s`, `(ec.2, 104)` and `(memW s (ec.1 + 88), 24)` are disjoint from `(globN s "ev", 280)`!
  --    Because `(globN s "ev", 280)` is index 0 of frame 0, while `(ec.2, 104)` is index 1 and logs header is index 4!
  -- 2) For every `ec ∈ (evmChain s).tail`, `(ec.1, 280)` is in a LATER frame, so disjoint from `(globN s "ev", 280)`!
  have hch_eq_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm, evmChainFrom]
    exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_eq_cons
  have hpw_head_tail :
      (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_other : ∀ o ∈ [((globN s "ev", globN s "cur_cont").2, 104),
      (memW s (globN s "ev" + 88), 24)], Disj (globN s "ev", 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    simp only [List.pairwise_cons] at hpw0
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact hpw0.1 _ (by simp)
    · exact hpw0.1 _ (by simp)
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ≠ 16 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    have hdisj_c : Disj (globN s "ev", 280) (ec.2, 104) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hhead_disj_other _ (by simp)
      · exact hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail _ (by simp [frameObjects])
    have hdisj_88 : Disj (globN s "ev", 280) (memW s (ec.1 + 88), 24) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hhead_disj_other _ (by simp)
      · exact hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail _ (by simp [frameObjects])
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hkne
      apply hmemW_ne16 (ec.1 + k) (by omega)
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · dsimp only; omega
      · have hd := hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
        rcases hd with h1 | h2
        · dsimp only at h1 ⊢; omega
        · dsimp only at h2 ⊢; omega
    · intro k hk
      apply hmemW_ne16 (ec.2 + k) (by omega)
      rcases hdisj_c with h1 | h2
      · dsimp only at h1 ⊢; omega
      · dsimp only at h2 ⊢; omega
    · intro k hk
      apply hmemW_ne16 (memW s (ec.1 + 88) + k) (by omega)
      rcases hdisj_88 with h1 | h2
      · dsimp only at h1 ⊢; omega
      · dsimp only at h2 ⊢; omega
  have htail_16_eq : ∀ ec ∈ chTail, memW post (ec.1 + 16) = memW s (ec.1 + 16) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_of_mem _ htail
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    have hd := hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    apply hmemW_ne16 (ec.1 + 16) (by omega)
    rcases hd with h1 | h2
    · dsimp only at h1 ⊢; omega
    · dsimp only at h2 ⊢; omega
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
      have hc16 := hc_eq 16 (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega)
      have hc8 := hc_eq 8 (by omega)
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
    rw [he_eq 88 (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 24 (by omega) (by omega), he_eq 40 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega), he_eq 88 (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega), he_eq 176 (by omega) (by omega)]
  -- Assemble `EvmStep [] s post`:
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hFW_all ec hec
    have he16_le : memW post (ec.1 + 16) ≤ memW s (ec.1 + 16) := by
      by_cases heq_ev : ec.1 = globN s "ev"
      · rw [heq_ev, hmemW_16, hsp1]; omega
      · obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
        have he8 : ec.1 % 8 = 0 := (c1 (ec.1, 280) (by simp)).2.1
        rw [hmemW_ne16 (ec.1 + 16) (by omega) (by omega)]
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega), he_eq 232 (by omega) (by omega),
        he_eq 88 (by omega) (by omega), he_eq 24 (by omega) (by omega),
        he_eq 40 (by omega) (by omega), he_eq 32 (by omega) (by omega),
        he_eq 136 (by omega) (by omega), he_eq 168 (by omega) (by omega),
        he_eq 176 (by omega) (by omega),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega) (by omega), he_eq 144 (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, le_trans he16_le c5, c6, c7,
      c8, c9, c10, c11, c12, c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
  · intro ec hec
    have hec_tail : ec ∈ chTail := by rw [hch_cons, List.tail_cons] at hec; exact hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [htail_16_eq ec hec_tail, (hrec_other_eq ec hec_mem).1 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega), (hrec_other_eq _ hi0).2.1 72 (by omega),
        (hrec_other_eq _ hi1).1 40 (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfeq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    exact hAT_at o ho j hj
  · -- `MarksOK`:
    have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
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
          have hk_le : k + 8 ≤ 40 := by simp [wsTableSlots] at hk; subst hk; omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 80 := by
            simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 72 := by
            simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk
        rw [List.mem_range] at hk
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · have := hWT.2.1.1; omega
        · have hbnd := allocated_le_2pow64 hAs.2 hal
          dsimp only at hbnd
          have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at))
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_le : k + 8 ≤ 280 ∧ k ≠ 16 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      rw [(hrec_other_eq _ hj_mem).1 k hk_le.1 hk_le.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega)
    have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem]
      exact m5 j hj hij
    · intro t ht
      rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1, hdelEx_iff i t]
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
      rw [(hrec_other_eq ec hec).1 64 (by omega) (by omega),
          (hrec_other_eq ec hec).1 192 (by omega) (by omega)]
    rw [hmap_gas]
    exact hGas

/-- General head-frame gas/status update inside `(globN s "ev", 280)` via
`ByteRegionEffect s post [(globN s "ev", 280)]`: if `memW post (globN s "ev" + k) = memW s (globN s "ev" + k)`
for all `k + 8 ≤ 280` outside `{64, 72, 160, 184, 192}` and
`memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤ memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)`,
then `EvmStep [] s post` holds. -/
theorem evmStep_of_head_gas_status_update {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (heff : ByteRegionEffect s post [(globN s "ev", 280)])
    (hkeep_ev : ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      k ∉ ([64, 72, 160, 184, 192] : List Nat) →
      memW post (globN s "ev" + k) = memW s (globN s "ev" + k))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmStep [] s post := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm, evmChainFrom]
    exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have hrec_fo : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (globN s "ev", 280) i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; simp
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · have hfl : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
        rw [List.mem_flatten]
        exact ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
          List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩
      exact Or.inr (hAT_at _ hfl i h6)
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hApost : ArenaReady post := by
    refine ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1, ?_⟩
    unfold ArenaOK; simp only [hglob_eq]; exact hAs.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun name _ => by rw [heff.globals]
  have hbfr : ByteFrameOutside s post ([] ++ [(globN s "ev", 280)] ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx => ha x (by simp at hx; subst hx; simp))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx; rw [hbit]
      exact not_cellHits_of_disj_aligned (i := (a, 8)) (by omega) (by omega)
        (hdja x (by simp at hx; subst hx; simp))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx => hno x (by simp at hx; subst hx; simp))
  have hcell : SameTypedCells s post S Nd_at :=
    sameTypedCells_of_byteFrame hAs hWT (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti) hbfr
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hch_eq_cons : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm, evmChainFrom]
    exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_eq_cons
  have hpw_head_tail :
      (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_other : ∀ o ∈ [((globN s "ev", globN s "cur_cont").2, 104),
      (memW s (globN s "ev" + 88), 24)], Disj (globN s "ev", 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    simp only [List.pairwise_cons] at hpw0
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact hpw0.1 _ (by simp)
    · exact hpw0.1 _ (by simp)
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ∉ ([64, 72, 160, 184, 192] : List Nat) →
        memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    have hdisj_c : Disj (globN s "ev", 280) (ec.2, 104) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hhead_disj_other _ (by simp)
      · exact hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail _ (by simp [frameObjects])
    have hdisj_88 : Disj (globN s "ev", 280) (memW s (ec.1 + 88), 24) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hhead_disj_other _ (by simp)
      · exact hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail _ (by simp [frameObjects])
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hk8 hknot
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hkeep_ev k hk hk8 hknot
      · have hd := hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
        exact memW_eq_of_frameDisj heff hb_e hk (fun x hx => by simp at hx; subst hx; exact hd)
    · intro k hk
      exact memW_eq_of_frameDisj heff hb_c hk (fun x hx => by simp at hx; subst hx; exact hdisj_c)
    · intro k hk
      exact memW_eq_of_frameDisj heff hb_88 hk (fun x hx => by simp at hx; subst hx; exact hdisj_88)
  have htail_gas_eq : ∀ ec ∈ chTail,
      memW post (ec.1 + 64) = memW s (ec.1 + 64) ∧
      memW post (ec.1 + 192) = memW s (ec.1 + 192) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_of_mem _ htail
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    have hd := hpw_head_tail.2 (globN s "ev", 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    exact ⟨memW_eq_of_frameDisj heff hb_e (by omega) (fun x hx => by simp at hx; subst hx; exact hd),
           memW_eq_of_frameDisj heff hb_e (by omega) (fun x hx => by simp at hx; subst hx; exact hd)⟩
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
      have hc16 := hc_eq 16 (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega)
      have hc8 := hc_eq 8 (by omega)
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
    rw [he_eq 88 (by omega) (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by decide), he_eq 144 (by omega) (by omega) (by decide)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega) (by decide), he_eq 232 (by omega) (by omega) (by decide),
        he_eq 24 (by omega) (by omega) (by decide), he_eq 40 (by omega) (by omega) (by decide),
        he_eq 88 (by omega) (by omega) (by decide), hframeLogs_eq ec hec, hframeRet_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by decide), he_eq 232 (by omega) (by omega) (by decide),
        he_eq 88 (by omega) (by omega) (by decide)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by decide),
        he_eq 168 (by omega) (by omega) (by decide),
        he_eq 176 (by omega) (by omega) (by decide)]
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := hFW_all ec hec
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega) (by decide), he_eq 232 (by omega) (by omega) (by decide),
        he_eq 88 (by omega) (by omega) (by decide), he_eq 24 (by omega) (by omega) (by decide),
        he_eq 40 (by omega) (by omega) (by decide), he_eq 16 (by omega) (by omega) (by decide),
        he_eq 32 (by omega) (by omega) (by decide),
        he_eq 136 (by omega) (by omega) (by decide), he_eq 168 (by omega) (by omega) (by decide),
        he_eq 176 (by omega) (by omega) (by decide),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by decide), he_eq 144 (by omega) (by omega) (by decide),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, c5, c6, c7,
      c8, c9, c10, c11, c12, c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_of_dom heff.memaddrs).2 hw⟩
  · intro ec hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_other_eq ec hec_mem).1 16 (by omega) (by omega) (by decide),
        (hrec_other_eq ec hec_mem).1 232 (by omega) (by omega) (by decide)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega), (hrec_other_eq _ hi0).2.1 72 (by omega),
        (hrec_other_eq _ hi1).1 40 (by omega) (by omega) (by decide)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfeq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    exact hAT_at o ho j hj
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
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
          have hk_le : k + 8 ≤ 40 := by simp [wsTableSlots] at hk; subst hk; omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz hk_le
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 80 := by
            simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz hk_le
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split
        · rfl
        · rename_i hnz
          apply List.map_congr_left; intro k hk
          have hk_le : k + 8 ≤ 72 := by
            simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
          exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz hk_le
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk
        rw [List.mem_range] at hk
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · have := hWT.2.1.1; omega
        · have hbnd := allocated_le_2pow64 hAs.2 hal
          dsimp only at hbnd
          have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at))
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧ k ∉ ([64, 72, 160, 184, 192] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by decide⟩
      rw [(hrec_other_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega)
    have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega) (by omega) (by decide)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by decide)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem]
      exact m5 j hj hij
    · intro t ht
      rw [htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1, hdelEx_iff i t]
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
  · -- Gas sum `< 2^64`:
    have hsum_le : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      rw [hch_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have htail_map : (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
          (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
        apply List.map_congr_left; intro ec htail
        obtain ⟨h64, h192⟩ := htail_gas_eq ec htail
        rw [h64, h192]
      rw [htail_map]
      exact Nat.add_le_add_right hgas_le _
    exact lt_of_le_of_lt (Nat.add_le_add_right hsum_le 1) hGas

end InitECandidate.Solver.Wave8Contracts.M22
