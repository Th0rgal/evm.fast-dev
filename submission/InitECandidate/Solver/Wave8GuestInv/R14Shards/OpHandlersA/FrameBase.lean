import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Walk

/-! # Frame & buffer preservation base lemmas for `R14-OpHandlersSpec-A` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8Contracts.M23

/-- Offsets of `(ev, 280)` never read by `EvmInv`, `evmChain`, or `evmR`. -/
def nonStructFrameOffs : List Nat :=
  [0, 72, 96, 104, 120, 128, 152, 160, 184, 200, 240, 248, 256]

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun x => if x = a then .word w else m x

theorem memW_updW_same {F : Type} (t : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    memW { t with memory := updW t.memory (BitVec.ofNat 64 a) w } a = w.toNat := by
  unfold memW updW; simp

theorem memW_updW_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (a b : Nat) (w : BitVec 64)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : b ≠ a) :
    memW { t with memory := updW t.memory (BitVec.ofNat 64 a) w } b = memW t b := by
  unfold memW updW
  have hbv : BitVec.ofNat 64 b ≠ BitVec.ofNat 64 a := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] at this
    exact hne this
  simp [hbv]

theorem store_global_off_word {F : Type} {t post : PanSemStateFiniteExact 64 F}
    {gname : String} {gbase off : Nat} {gw : BitVec 64} {valExp : ExpHOL 64}
    (hg_lk : t.globals.lookup (ofString gname) = some (.val (.word gw)))
    (hg_nat : gw.toNat = gbase)
    (hbnd : gbase + off < 2 ^ 64)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) ∧
      post = { t with memory := updW t.memory (BitVec.ofNat 64 (gbase + off)) w } := by
  have hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (gbase + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hg_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hg_nat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega), Nat.mod_eq_of_lt hbnd]
  rw [evaluateHOLFiniteState_store, hdst] at hrun
  revert hrun
  cases hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp with
  | none => simp
  | some v =>
    obtain ⟨w, rfl⟩ := hval v hv
    dsimp only
    split
    · rename_i m' hst
      unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
      by_cases hdom : t.memaddrs (BitVec.ofNat 64 (gbase + off))
      · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
        subst hst
        intro hrun; injection hrun with _ hpost
        exact ⟨w, rfl, hpost.symm⟩
      · simp [hdom] at hst
    · simp

theorem wordAt_congr_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {a : Nat} :
    WordAt post a ↔ WordAt s a := by
  unfold WordAt; rw [hma]
  constructor
  · rintro ⟨_, hdom, _⟩
    cases hs : s.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩
  · rintro ⟨_, hdom, _⟩
    cases hp : post.memory (BitVec.ofNat 64 a) with
    | word w => exact ⟨w, hdom, rfl⟩

theorem wordsOK_congr_dom {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hma : post.memaddrs = s.memaddrs) {i : Ivl} :
    WordsOK post i ↔ WordsOK s i := by
  unfold WordsOK
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun _ => imp_congr_right fun _ =>
    wordAt_congr_dom hma))

theorem memW_eq_of_disj_eff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (heff : ByteRegionEffect s post Rl)
    (hRl8 : ∀ x ∈ Rl, x.1 % 8 = 0)
    {base sz k : Nat} (hbnd : base + sz ≤ 2 ^ 64) (hb8 : base % 8 = 0) (hk8 : k % 8 = 0)
    (hk : k + 8 ≤ sz) (hdj : ∀ x ∈ Rl, Disj x (base, sz)) :
    memW post (base + k) = memW s (base + k) := by
  unfold memW
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
  intro x hx
  rw [hbit]
  exact not_cellHits_of_disj_aligned (i := (base, sz)) (by omega) (hRl8 x hx)
    (by dsimp only; omega) (by dsimp only; omega) (R11Shards.Disj.symm (hdj x hx))

theorem evmR_eq_of_chain_and_words {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hch : evmChain post = evmChain s)
    (hw : ∀ ec ∈ evmChain s,
      memW post (ec.1 + 64) = memW s (ec.1 + 64) ∧
      memW post (ec.1 + 192) = memW s (ec.1 + 192)) :
    evmR post = evmR s := by
  unfold evmR; rw [hch]
  congr 1
  apply List.map_congr_left
  intro ec hec
  obtain ⟨h64, h192⟩ := hw ec hec
  rw [h64, h192]

/-- Updating any subset of `nonStructFrameOffs` of `globN s "ev"` preserves `EvmInv`,
`evmChain`, and `evmR` (exact equality). -/
theorem evmInv_of_head_nonstruct {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x) :
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ nonStructFrameOffs,
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ s.memaddrs (BitVec.ofNat 64 (e0 + off)) := by
    intro off hoff
    have hdiv : off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off := by
      revert off hoff; decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (off / 8) hdiv.2.2.1
    exact ⟨hdiv.1, hdiv.2.1, by simpa [hdiv.2.2.2] using hdom⟩
  have heff : ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_out a
      intro off hoff rfl
      exact hna (hoff_props off hoff).2.2
    · intro a ha
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      exact ha (e0, 280) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro off hoff heq
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      have := congrArg BitVec.toNat heq
      rw [hal_b, htn] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hRl8_e0 : ∀ x ∈ ([(e0, 280)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact he0_8
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
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
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩) i h6)
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
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ nonStructFrameOffs, a ≠ e0 + off) → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro off hoff heq
    have hp := hoff_props off hoff
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)] at this
    exact hne off hoff this
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_rest : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_rest _ (by simp), hhead_disj_rest _ (by simp),
        hhead_disj_rest _ (by simp), fun i hi => hhead_disj_rest _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ∉ nonStructFrameOffs → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_c hc8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_88 h88_8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hknot
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have : k = off := by dsimp only at heq; omega
      exact hknot (this ▸ hoff)
    · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
      rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
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
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by decide), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by decide)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by decide),
       (hrec_eq ec hec).1 192 (by omega) (by decide)⟩)
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by decide)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
        (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono hh hsc hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        by rw [hchain_eq]; intro ec' hec' o ho; rw [hframeObjects_eq ec' hec'] at ho; exact hdfo ec' hec' o ho,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
      exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
        he_eq 40 (by omega) (by decide), he_eq 16 (by omega) (by decide),
        he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
        he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by decide), he_eq 144 (by omega) (by decide),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    rw [he_eq 88 (by omega) (by decide)] at hlo_ok
    refine ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
      c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
    rcases c15 with h0 | ⟨hin, hw⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by decide),
        (hrec_eq ec hec_mem).1 232 (by omega) (by decide)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by decide)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho; rw [hfeq]
    exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho).1 t ht i hi,
      (hFO_disj ec hec o ho).2⟩
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
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
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
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k ∉ nonStructFrameOffs := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by decide)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by decide)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
    rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [hsum_eq]; exact hGas

/-- Untyped global buffer writes (`u256_ws`, `sk_buf`, `keccak_pad`, `keccak_st`, `mpt_nib_scratch`)
preserve `EvmInv`, `evmChain`, and `evmR`. -/
def untypedGlobalBufIvls {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [("u256_ws", 640), ("sk_buf", 64), ("keccak_pad", 136), ("keccak_st", 200), ("mpt_nib_scratch", 64)].map
    fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)

private theorem globalBuffers_idx_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) {i1 i2 : Nat}
    (h1 : i1 < globalBuffers.length) (h2 : i2 < globalBuffers.length) (hne : i1 ≠ i2) :
    let g1 := globalBuffers[i1]
    let g2 := globalBuffers[i2]
    Disj (globN s g1.1, if globN s g1.1 = 0 then 0 else g1.2)
         (globN s g2.1, if globN s g2.1 = 0 then 0 else g2.2) := by
  have hpw := hF.2
  unfold fixedObjects at hpw
  have hpw1 := (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hpw).1).1).1
  have hlen : (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)).length =
      globalBuffers.length := List.length_map _
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := List.pairwise_iff_getElem.1 hpw1 i1 i2 (by rw [hlen]; exact h1) (by rw [hlen]; exact h2) hlt
    simpa [List.getElem_map] using this
  · have := List.pairwise_iff_getElem.1 hpw1 i2 i1 (by rw [hlen]; exact h2) (by rw [hlen]; exact h1) hgt
    exact R11Shards.Disj.symm (by simpa [List.getElem_map] using this)

theorem evmStepR_of_untypedGlobalBufs {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (heff : ByteRegionEffect s post (untypedGlobalBufIvls s)) :
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hInvAt.2.2.2.2.2.2.2.2.2.1
  have hF := hW.2.2.1
  have hpw := hF.2
  unfold fixedObjects at hpw
  obtain ⟨hpw_123, _, hrel_bal⟩ := List.pairwise_append.1 hpw
  obtain ⟨hpw_12, _, hrel_bo⟩ := List.pairwise_append.1 hpw_123
  obtain ⟨_, _, hrel_jrn⟩ := List.pairwise_append.1 hpw_12
  have hub_in_gb : ∀ x ∈ untypedGlobalBufIvls s,
      (∃ idx : Nat, ∃ hidx : idx < globalBuffers.length,
        idx ∈ ([43, 38, 23, 25, 28] : List Nat) ∧
        x = (globN s globalBuffers[idx].1, if globN s globalBuffers[idx].1 = 0 then 0 else globalBuffers[idx].2)) ∧
      x ∈ globalBuffers.map (fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    intro x hx
    unfold untypedGlobalBufIvls at hx
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · refine ⟨⟨43, by decide, by simp, rfl⟩, List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩⟩
    · refine ⟨⟨38, by decide, by simp, rfl⟩, List.mem_map.2 ⟨("sk_buf", 64), by decide, rfl⟩⟩
    · refine ⟨⟨23, by decide, by simp, rfl⟩, List.mem_map.2 ⟨("keccak_pad", 136), by decide, rfl⟩⟩
    · refine ⟨⟨25, by decide, by simp, rfl⟩, List.mem_map.2 ⟨("keccak_st", 200), by decide, rfl⟩⟩
    · refine ⟨⟨28, by decide, by simp, rfl⟩, List.mem_map.2 ⟨("mpt_nib_scratch", 64), by decide, rfl⟩⟩
  have htr_idx : ∀ r ∈ typedRecords,
      ∃ idx2 : Nat, ∃ hidx2 : idx2 < globalBuffers.length,
        idx2 ∈ ([46, 11, 42, 10] : List Nat) ∧ r = globalBuffers[idx2] := by
    intro r hr
    simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨46, by decide, by simp, rfl⟩
    · exact ⟨11, by decide, by simp, rfl⟩
    · exact ⟨42, by decide, by simp, rfl⟩
    · exact ⟨10, by decide, by simp, rfl⟩
  have hRl8_ub : ∀ x ∈ untypedGlobalBufIvls s, x.1 % 8 = 0 := by
    intro x hx
    obtain ⟨_, hx_map⟩ := hub_in_gb x hx
    have hx_fix : x ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx_map))
    rcases hF.1 x hx_fix with h0 | ⟨_, hw⟩
    · obtain ⟨gn, hgn_m, rfl⟩ := List.mem_map.1 hx_map
      have hpos : 0 < gn.2 := by clear * - hgn_m; revert gn hgn_m; decide
      dsimp only at h0 ⊢
      by_cases hz : globN s gn.1 = 0
      · simp [hz]
      · simp [hz] at h0; omega
    · exact hw.1
  have hdj_all : IvlsDisj (untypedGlobalBufIvls s)
      (worldTypedIvls s S Nd_at ++ ((evmChain s).map (frameObjects s)).flatten) := by
    intro x hx j hj
    obtain ⟨⟨idx1, hidx1, hmem1, hxeq⟩, hx_map⟩ := hub_in_gb x hx
    have hx_fix : x ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx_map))
    rcases List.mem_append.1 hj with hj_w | hj_f
    · unfold worldTypedIvls at hj_w
      simp only [List.mem_append] at hj_w
      rcases hj_w with ((((h1 | h2) | h3) | h4) | h5) | h6
      · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
        exact R11Shards.Disj.symm (((hW.1.2.1 t ht).2 j hfp).2 x hx_fix)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
        obtain ⟨idx2, hidx2, hmem2, rfl⟩ := htr_idx r hr
        have hne : idx1 ≠ idx2 := by
          clear * - hmem1 hmem2
          revert idx1 idx2 hmem1 hmem2; decide
        rw [hxeq]
        exact globalBuffers_idx_disj hF hidx1 hidx2 hne
      · simp only [List.mem_singleton] at h3; subst h3
        exact hrel_jrn x hx_map _ (List.mem_singleton.2 rfl)
      · exact hrel_bo x (List.mem_append_left _ hx_map) j h4
      · exact hrel_bal x (List.mem_append_left _ (List.mem_append_left _ hx_map)) j h5
      · exact R11Shards.Disj.symm ((hTr_at.2.1 j h6).2 x hx_fix)
    · obtain ⟨fo, hfo_map, hj_fo⟩ := List.mem_flatten.1 hj_f
      obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
      exact R11Shards.Disj.symm ((hInvAt.2.2.2.2.2.2.2.2.1 ec hec j hj_fo).2 x hx_fix)
  have hstep := ByteRegionEffect.to_evmStep_nil_with hAs hInvAt hTr_at hAT_at hdj_all heff
  have hR : evmR post = evmR s := by
    refine evmR_eq_of_chain_and_words hstep.2.2.2 (fun ec hec => ?_)
    have hFW := hInvAt.2.2.2.2.1 ec hec
    obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    have hdj_ec : ∀ x ∈ untypedGlobalBufIvls s, Disj x (ec.1, 280) := fun x hx =>
      hdj_all x hx (ec.1, 280) (List.mem_append_right _ (List.mem_flatten.2
        ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩))
    exact ⟨memW_eq_of_disj_eff heff hRl8_ub hb1 he8 (by omega) (by omega) hdj_ec,
           memW_eq_of_disj_eff heff hRl8_ub hb1 he8 (by omega) (by omega) hdj_ec⟩
  exact ⟨hstep.1, heff.globals, hstep.2.2.2, hR⟩

end InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
