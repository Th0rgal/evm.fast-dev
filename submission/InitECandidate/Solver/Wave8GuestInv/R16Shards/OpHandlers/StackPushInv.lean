import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

/-! # `ScratchByteEff` and `EvmInv` preservation across head-frame stack growth/push -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

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
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. `ScratchByteEff`: `ByteRegionEffect` where `scratch_ptr` may shrink -/

structure ScratchByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  glob_other : ∀ g : String, g ≠ "scratch_ptr" → post.globals.lookup (ofString g) = s.globals.lookup (ofString g)
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

theorem ScratchByteEff.of_bre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ByteRegionEffect s post Rl) : ScratchByteEff s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, fun _ _ => by rw [h.globals],
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ScratchByteEff.of_m11_bre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : M11.ByteRegionEffect s post Rl) : ScratchByteEff s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, fun _ _ => by rw [h.globals],
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ScratchByteEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ScratchByteEff s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ScratchByteEff.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : ScratchByteEff s post Rl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ScratchByteEff s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.glob_other,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ScratchByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ScratchByteEff a b Rl) (h2 : ScratchByteEff b c Rl) :
    ScratchByteEff a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, fun g hg => (h2.glob_other g hg).trans (h1.glob_other g hg), ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx; rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno; rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

theorem ScratchByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ScratchByteEff s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ScratchByteEff s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.glob_other, h.out_dom, ?_, ?_⟩
  · intro a ha; apply h.cell_frame a; intro i hi ⟨hc1, hc2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno; apply h.byte_frame b hb; intro i hi ⟨hb1, hb2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

theorem ScratchByteEff.to_bre_dummy {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ScratchByteEff s post Rl) :
    ByteRegionEffect s { post with globals := s.globals } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, rfl,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ScratchByteEff.of_store_struct4 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval4 : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w0 w1 w2 w3 : BitVec 64, v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)])
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      addr.toNat + 32 ≤ 2 ^ 64 ∧ ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 32 ≤ i.1 + i.2) :
    ScratchByteEff s post Rl ∧ post.locals = s.locals ∧ post.globals = s.globals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | v
      · simp
      · obtain ⟨w0, w1, w2, w3, rfl⟩ := hval4 v hv
        dsimp only
        split
        · rename_i m' hst
          obtain ⟨hbnd32, i, hi, hi1, hi2⟩ := hin addr hdst
          have hbw : Flapjack.Compiler.Backend.StackRemove.bytesInWord 64 = (8 : BitVec 64) := rfl
          simp only [flattenHOL, List.flatMap, panMemStoresHOL, panMemStoreHOL, hbw] at hst
          by_cases hd0 : s.memaddrs addr
          · simp only [hd0, ↓reduceIte] at hst
            by_cases hd1 : s.memaddrs (addr + 8)
            · simp only [hd1, ↓reduceIte] at hst
              by_cases hd2 : s.memaddrs (addr + 8 + 8)
              · simp only [hd2, ↓reduceIte] at hst
                by_cases hd3 : s.memaddrs (addr + 8 + 8 + 8)
                · simp only [hd3, ↓reduceIte, Option.some.injEq] at hst
                  subst hst
                  intro hrun; injection hrun with _ hpost; subst hpost
                  have ha8 : addr.toNat % 8 = 0 := by
                    have hdom' := hma_ord ▸ hd0
                    rw [ordinaryDomain_iff] at hdom'; exact hdom'.2.2
                  have ha8_nat : (addr + 8).toNat = addr.toNat + 8 := by
                    have : (8 : BitVec 64).toNat = 8 := rfl
                    rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
                  have ha16_nat : (addr + 8 + 8).toNat = addr.toNat + 16 := by
                    have : (8 : BitVec 64).toNat = 8 := rfl
                    rw [BitVec.toNat_add, ha8_nat, this, Nat.mod_eq_of_lt (by omega)]
                  have ha24_nat : (addr + 8 + 8 + 8).toNat = addr.toNat + 24 := by
                    have : (8 : BitVec 64).toNat = 8 := rfl
                    rw [BitVec.toNat_add, ha16_nat, this, Nat.mod_eq_of_lt (by omega)]
                  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_⟩, rfl, rfl⟩
                  · intro a hna; dsimp only
                    have hne3 : a ≠ addr + 8 + 8 + 8 := by rintro rfl; exact hna hd3
                    have hne2 : a ≠ addr + 8 + 8 := by rintro rfl; exact hna hd2
                    have hne1 : a ≠ addr + 8 := by rintro rfl; exact hna hd1
                    have hne0 : a ≠ addr := by rintro rfl; exact hna hd0
                    simp [hne3, hne2, hne1, hne0]
                  · intro a hna; dsimp only
                    have hne3 : a ≠ addr + 8 + 8 + 8 := by
                      rintro rfl; exact hna i hi ⟨by rw [ha24_nat]; omega, by rw [ha24_nat]; omega⟩
                    have hne2 : a ≠ addr + 8 + 8 := by
                      rintro rfl; exact hna i hi ⟨by rw [ha16_nat]; omega, by rw [ha16_nat]; omega⟩
                    have hne1 : a ≠ addr + 8 := by
                      rintro rfl; exact hna i hi ⟨by rw [ha8_nat]; omega, by rw [ha8_nat]; omega⟩
                    have hne0 : a ≠ addr := by
                      rintro rfl; exact hna i hi ⟨by omega, by omega⟩
                    simp [hne3, hne2, hne1, hne0]
                  · intro b hb hno
                    unfold memB; dsimp only
                    have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
                    have hne3 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8 + 8 + 8 := by
                      intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha24_nat] at this
                      exact hno i hi ⟨by omega, by omega⟩
                    have hne2 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8 + 8 := by
                      intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha16_nat] at this
                      exact hno i hi ⟨by omega, by omega⟩
                    have hne1 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr + 8 := by
                      intro heq; have := congrArg BitVec.toNat heq; rw [hal_b, ha8_nat] at this
                      exact hno i hi ⟨by omega, by omega⟩
                    have hne0 : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
                      intro heq; have := congrArg BitVec.toNat heq; rw [hal_b] at this
                      exact hno i hi ⟨by omega, by omega⟩
                    simp [hne3, hne2, hne1, hne0]
                · simp [hd3] at hst
              · simp [hd2] at hst
            · simp [hd1] at hst
          · simp [hd0] at hst
        · simp
    · simp
    · simp

/-! ## 2. `EvmInv`, `evmChain`, and `evmR` preservation across head-frame stack push / growth -/

theorem globN_eq_of_lookup_eq {F : Type} {s post : PanSemStateFiniteExact 64 F} {g : String}
    (h : post.globals.lookup (ofString g) = s.globals.lookup (ofString g)) :
    globN post g = globN s g := by
  unfold globN; rw [h]

theorem allocated_mono_scr {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    {i : Ivl} (hal : Allocated s i) : Allocated post i := by
  rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, le_trans h2 hh⟩
  · exact Or.inr ⟨le_trans hsc h1, h2⟩

theorem wordsOK_of_allocated_scr {F : Type} {post : PanSemStateFiniteExact 64 F}
    (hApost : ArenaReady post) {i : Ivl} (hal : Allocated post i)
    (hi8 : i.1 % 8 = 0) (hisz8 : i.2 % 8 = 0) : WordsOK post i := by
  have hsb_le_ss : sourceBase ≤ scratchStart := by decide
  have hse_le_he : scratchEnd ≤ heapEnd := by decide
  have hhp_le_he : globN post "heap_ptr" ≤ heapEnd :=
    le_trans hApost.2.2.1 (by rw [R11Shards.heapLimit_val, R11Shards.heapEnd_val]; decide)
  rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Wave8Contracts.M26.wordsOK_of_guestInv post hApost.1 i.1 i.2 hi8 hisz8 h1 (le_trans h2 hhp_le_he)
  · have hsc_ge : sourceBase ≤ globN post "scratch_ptr" :=
      le_trans hsb_le_ss (le_trans hApost.2.2.2.1 hApost.2.2.2.2.1)
    exact Wave8Contracts.M26.wordsOK_of_guestInv post hApost.1 i.1 i.2 hi8 hisz8
      (le_trans hsc_ge h1) (le_trans h2 hse_le_he)

theorem evmInv_of_head_stack_push {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {freshIvl : Ivl}
    (hInv : EvmInv s)
    (hApost : ArenaReady post)
    (hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (heff : ScratchByteEff s post [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
    (hfresh : freshIvl.2 = 0 ∨
      (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
        Inside freshIvl (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (he0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (hnew_stk :
      (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
        memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
      (freshIvl.2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = freshIvl))
    (hcap_bounds :
      1 ≤ memW post (globN s "ev" + 232) ∧
      memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
      memW post (globN s "ev" + 232) ≤ 1024) :
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set oldStk : Ivl := (memW s (e0 + 8), 32 * memW s (e0 + 232))
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have holdStk_8 : oldStk.1 % 8 = 0 := (hhead_FW.1 oldStk (by simp [oldStk])).2.1
  have hRl_list : ∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), x.1 % 8 = 0 ∨ x.2 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh with h0 | ⟨h8, _⟩
      · exact Or.inr h0
      · exact Or.inl h8
    · exact Or.inl he0_8
    · exact Or.inl holdStk_8
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob_eq : ∀ g, g ≠ "scratch_ptr" → globN post g = globN s g :=
    fun g hg => globN_eq_of_lookup_eq (heff.glob_other g hg)
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq "heap_ptr" (by decide)]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0), ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem o ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have hfresh_disj_alloc : ∀ i : Ivl, Allocated s i → Disj freshIvl i := by
    intro i hal
    rcases hfresh with hf0 | ⟨_, _, hfin⟩
    · exact Or.inl hf0
    · rcases hal with ⟨_, hhi⟩ | ⟨hlo, _⟩
      · have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1; have h3 := hApost.2.2.2.1
        rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
        obtain ⟨hfin1, _⟩ := hfin
        obtain ⟨_, hhi2⟩ := hhi
        exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · obtain ⟨_, hfin2⟩ := hfin
        obtain ⟨hlo1, _⟩ := hlo
        exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
  have hwrite_disj_wti : ∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl),
      ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases worldTypedIvls_allocated hWT i hi with hi0 | hal
      · exact Or.inl hi0
      · exact Or.inr (hfresh_disj_alloc i hal)
    · exact hfo_disj_wti (e0, 280) (by simp [frameObjects]) i hi
    · exact hfo_disj_wti oldStk (by simp [frameObjects, oldStk]) i hi
  have hcellG : SameTypedCells s { post with globals := s.globals } S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [freshIvl, (e0, 280), oldStk])
      hAs.1.memaddrs hWT (fun _ h => by simp at h) hwrite_disj_wti (by simpa using heff.to_bre_dummy)
  have hcell : SameTypedCells s post S Nd_at := hcellG
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ h2 _ => (heff.glob_other name h2).symm)
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc_le hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : g ≠ "scratch_ptr" := by clear * - hg; revert g hg; decide
    exact hglob_eq g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    rcases hRl_list x hx with hx8 | hx0
    · exact not_cellHits_of_disj_aligned (i := (base, sz)) (by omega) hx8
        (by dsimp only; omega) (by dsimp only; omega) (R11Shards.Disj.symm (hdj x hx))
    · intro ⟨_, hc2⟩; rw [hx0] at hc2; omega
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj freshIvl o := by
    intro ec hec o ho
    rcases hfresh with hf0 | ⟨_, _, hfin⟩
    · exact Or.inl hf0
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have hFW := hFW_all ec hec
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1; have h3 := hApost.2.2.2.1
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      have hsb_hl : globN s "heap_ptr" ≤ 2952790016 := h1
      unfold frameObjects at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨_, hin2⟩ := hFW.2.1
          have hfp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hglob_eq "frame_mem_ptr" (by decide)
          rw [hfp_eq] at h3
          exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, hin2⟩ | ⟨hin1, _⟩
          · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
          · exact Or.inr (Or.inr (Or.inl (by dsimp only; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨⟨_, hin2⟩, _⟩
          · unfold frameRet; simp [hz]; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (by dsimp only; omega)))
      · unfold frameLogObjects at holog; dsimp only at holog
        obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
        rw [List.mem_range] at hidx_mem
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          dsimp only at hin1; omega
        · have hle := (hent idx hidx_mem).2
          have ho_rec := (List.mem_filter.1 ho_own).1
          simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
          rcases ho_rec with rfl | rfl | rfl | rfl
          · obtain ⟨_, hin2⟩ := hle.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  have hdisj_write_nonstk : ∀ ec ∈ evmChain s,
      (∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x (ec.2, 104)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x (memW s (ec.1 + 88), 24)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x (frameLogs s ec)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        ∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl),
          Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    have hlog_in : ∀ i < memW s (memW s (ec.1 + 88) + 8),
        (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
      intro i hi; unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
        by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hmem_head : (e0, c0) ∈ evmChain s := hhead_mem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldStk]))
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp2.1 _ (by simp)
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp2.1 _ (by simp)
      · intro i hi x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hli := hlog_in i hi
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by unfold frameObjects; exact List.mem_append_right _ hli)
        · exact hp0.1 _ (by simp [hli])
        · exact hp2.1 _ (by simp [hli])
    · have hmem_ec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
      have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x o2 := by
        intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo ec hmem_ec o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects, oldStk]) ec htail o2 ho2
      exact ⟨hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             fun i hi => hall _ (by unfold frameObjects; exact List.mem_append_right _ (hlog_in i hi))⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    apply hmemW_disj hb_e he8 hk8 hk
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfresh_disj_fo ec hec (ec.1, 280) (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects, oldStk]) ec htail _ (by simp [frameObjects])
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ≠ 8 → k ≠ 16 → k ≠ 232 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_write_nonstk ec hec
    refine ⟨?_,
      fun k hk hk8 => hmemW_disj hb_c hc8 hk8 hk hd_c,
      fun k hk hk8 => hmemW_disj hb_88 h88_8 hk8 hk hd_88⟩
    intro k hk hk8 hk_8 hk_16 hk_232
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact he0_other k hk hk8 hk_8 hk_16 hk_232
    · exact htail_rec_eq ec htail k hk hk8
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
    unfold evmChain
    rw [hglob_eq "ev" (by decide), hglob_eq "cur_cont" (by decide)]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_write_nonstk ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 := h88_eq 8 (by omega) (by omega)
    have hl16 := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (ec.1 + 88) + 8 * i) := by
      intro i _; unreachable!
    -- Wait: let's state `harr_eq` with the exact parenthesization `memW s (memW s (ec.1 + 88)) + 8 * i`!
    clear harr_eq
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post ((memW s (memW s (ec.1 + 88))) + 8 * i) = memW s ((memW s (memW s (ec.1 + 88))) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact hmemW_disj hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega) hd_fl
    have hlr_eq : ∀ i (_hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) =
          memW s ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact hmemW_disj hlr_b hlr_8 hoff8 hoff (hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega) (by omega) (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address" (by decide)]
    · rw [he_eq 88 (by omega) (by omega) (by omega) (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono_scr hh hsc_le hal_l,
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
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr" (by decide)]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    unfold frameObjects
    rw [htail_rec_eq ec htail 8 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega),
        htail_rec_eq ec htail 24 (by omega) (by omega),
        htail_rec_eq ec htail 40 (by omega) (by omega),
        htail_rec_eq ec htail 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have htail_fs_eq : ∀ ec ∈ chTail, frameScratch post ec = frameScratch s ec := by
    intro ec htail
    unfold frameScratch
    rw [htail_rec_eq ec htail 8 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega),
        htail_rec_eq ec htail 88 (by omega) (by omega)]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ (ec = (e0, c0) ∧ freshIvl.2 ≠ 0 ∧ o = freshIvl) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · rcases hnew_stk with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
      · left
        have heq_fo : frameObjects post (e0, c0) = frameObjects s (e0, c0) := by
          unfold frameObjects
          rw [h8_eq, h232_eq,
              he0_other 24 (by omega) (by omega) (by omega) (by omega) (by omega),
              he0_other 40 (by omega) (by omega) (by omega) (by omega) (by omega),
              he0_other 88 (by omega) (by omega) (by omega) (by omega) (by omega),
              hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1]
        rwa [← heq_fo]
      · unfold frameObjects at ho
        rw [hstk_eq,
            he0_other 24 (by omega) (by omega) (by omega) (by omega) (by omega),
            he0_other 40 (by omega) (by omega) (by omega) (by omega) (by omega),
            he0_other 88 (by omega) (by omega) (by omega) (by omega) (by omega),
            hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1] at ho
        rcases List.mem_append.1 ho with ho7 | holog
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
          rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inr ⟨rfl, hnz, rfl⟩
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
          · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ holog)
    · left; rwa [htail_fo_eq ec htail] at ho
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega) (by omega) (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega) (by omega) (by omega) (by omega)⟩)
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
      rw [he_eq 112 (by omega) (by omega) (by omega) (by omega) (by omega)]
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
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell_i
        ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono_scr hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        ?_,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      · rw [hchain_eq]; intro ec' hec' o ho
        rcases hfo_post_cases ec' hec' o ho with ho_old | ⟨_, _, rfl⟩
        · exact hdfo ec' hec' o ho_old
        · exact R11Shards.Disj.symm (hfresh_disj_alloc (memW s (ec.1 + 112), 176) hal_m)
      · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
    have inside_scr_mono : ∀ {i : Ivl}, Inside i (globN s "scratch_ptr") scratchEnd →
        Inside i (globN post "scratch_ptr") scratchEnd :=
      fun ⟨h1, h2⟩ => ⟨le_trans hsc_le h1, h2⟩
    unfold FrameWF; dsimp only
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 40 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 32 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 136 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "frame_mem_ptr" (by decide),
        hglob_eq "heap_ptr" (by decide),
        hglob_eq "evm_empty" (by decide)]
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega) (by omega)] at hlo_ok
    have hfl_in_post : Inside (frameLogs s ec) sourceBase (globN s "heap_ptr") ∨
        Inside (frameLogs s ec) (globN post "scratch_ptr") scratchEnd := by
      rcases c13 with h | h
      · exact Or.inl h
      · exact Or.inr (inside_scr_mono h)
    have hret_in_post : (memW s (ec.1 + 216) = 0 ∧ memW s (ec.1 + 144) = globN s "evm_empty") ∨
        Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK post (frameRet s ec) := by
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨?_, c2, (wordsOK_congr_dom hdom_eq).2 c3, hcap_bounds.1, hcap_bounds.2.1, hcap_bounds.2.2,
        c7, c8, c9, c10, c11, c12, hfl_in_post, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨inside_scr_mono (c1 _ (by simp)).1, (wordsOK_congr_dom hdom_eq).2 (c1 _ (by simp)).2⟩
      · exact ⟨inside_scr_mono (c1 _ (by simp)).1, (wordsOK_congr_dom hdom_eq).2 (c1 _ (by simp)).2⟩
      · rcases hnew_stk with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
        · rw [h8_eq, h232_eq]
          exact ⟨inside_scr_mono (c1 _ (by simp)).1, (wordsOK_congr_dom hdom_eq).2 (c1 _ (by simp)).2⟩
        · rw [hstk_eq]
          rcases hfresh with hf0 | ⟨hf8, hfsz8, hfin⟩
          · exact absurd hf0 hnz
          · have hhi_se : freshIvl.1 + freshIvl.2 ≤ scratchEnd := le_trans hfin.2 hAs.2.2.2.2.1
            have hal_f : Allocated post freshIvl := Or.inr ⟨hfin.1, hhi_se⟩
            exact ⟨⟨hfin.1, hhi_se⟩, wordsOK_of_allocated_scr hApost hal_f hf8 hfsz8⟩
      · exact ⟨inside_scr_mono (c1 _ (by simp)).1, (wordsOK_congr_dom hdom_eq).2 (c1 _ (by simp)).2⟩
    · rw [htail_rec_eq ec htail 8 (by omega) (by omega),
          htail_rec_eq ec htail 16 (by omega) (by omega),
          htail_rec_eq ec htail 232 (by omega) (by omega)]
      refine ⟨fun i hi => ⟨inside_scr_mono (c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        hfl_in_post, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
  · intro ec hec
    have htail : ec ∈ chTail := by rw [hch_eq, List.tail_cons] at hec; exact hec
    unfold FrameRoom
    rw [htail_rec_eq ec htail 16 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hRW i hi
  · have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
      List.map_congr_left htail_fo_eq
    rcases hnew_stk with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
    · have hhead_fo_eq : frameObjects post (e0, c0) = frameObjects s (e0, c0) := by
        unfold frameObjects
        rw [h8_eq, h232_eq,
             he0_other 24 (by omega) (by omega) (by omega) (by omega) (by omega),
             he0_other 40 (by omega) (by omega) (by omega) (by omega) (by omega),
             he0_other 88 (by omega) (by omega) (by omega) (by omega) (by omega),
             hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1]
      rw [hch_eq, List.map_cons, hhead_fo_eq, htail_map_eq]
      rw [hch_eq, List.map_cons] at hFO_pw; exact hFO_pw
    · rw [hch_eq, List.map_cons, List.flatten_cons, htail_map_eq, List.pairwise_append]
      have hFO_pw' := hFO_pw
      rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw'
      refine ⟨?_, hFO_pw'.2.1, ?_⟩
      · unfold frameObjects
        rw [hstk_eq,
            he0_other 24 (by omega) (by omega) (by omega) (by omega) (by omega),
            he0_other 40 (by omega) (by omega) (by omega) (by omega) (by omega),
            he0_other 88 (by omega) (by omega) (by omega) (by omega) (by omega),
            hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1]
        change ((e0, 280) :: (c0, 104) :: freshIvl ::
          ((memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
            frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0))).Pairwise Disj
        refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, hp2.2⟩⟩⟩
        · intro o ho; simp only [List.mem_cons] at ho
          rcases ho with rfl | rfl | ho_rest
          · exact hp0.1 _ (by simp)
          · exact R11Shards.Disj.symm (hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects]))
          · exact hp0.1 _ (by simp [ho_rest])
        · intro o ho; simp only [List.mem_cons] at ho
          rcases ho with rfl | ho_rest
          · exact R11Shards.Disj.symm (hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects]))
          · exact hp1.1 _ (by simp [ho_rest])
        · intro o ho
          have ho_in : o ∈ frameObjects s (e0, c0) := by
            unfold frameObjects
            simp only [List.mem_cons] at ho
            rcases ho with rfl | rfl | rfl | rfl | ho_log
            · simp
            · simp
            · simp
            · simp
            · exact List.mem_append_right _ ho_log
          exact hfresh_disj_fo _ hhead_mem o ho_in
      · intro o1 ho1 o2 ho2
        obtain ⟨l2, hl2, ho2_in⟩ := List.mem_flatten.1 ho2
        obtain ⟨ec2, hec2, rfl⟩ := List.mem_map.1 hl2
        have hec2_mem : ec2 ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ hec2
        rcases hfo_post_cases _ hhead_mem o1 ho1 with ho1_old | ⟨_, _, rfl⟩
        · exact hFO_pw'.2.2 o1 ho1_old o2 ho2
        · exact hfresh_disj_fo ec2 hec2_mem o2 ho2_in
  · intro ec hec o ho
    rw [hfeq]
    rcases hfo_post_cases ec hec o ho with ho_old | ⟨_, _, rfl⟩
    · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
        (hFO_disj ec hec o ho_old).2⟩
    · refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [hfp_eq_all t ht] at hi
        exact hfresh_disj_alloc i ((hWT.1.2.1 t ht).2 i hi).1
      · rcases hWT.2.2.1.1 j hj with hj0 | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hj0)
        · exact hfresh_disj_alloc j hal_j
  · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | ⟨_, _, rfl⟩
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · rcases worldTypedIvls_allocated hWT j (mem_worldTypedIvls_nodeExtents hj) with hj0 | hal_j
      · exact Or.inr (Or.inl hj0)
      · exact hfresh_disj_alloc j hal_j
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_eq "ws" (by decide), hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map, hglob_eq _ (by decide)],
          balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts" (by decide)),
          hglob_eq "journal_n" (by decide), hglob_eq "journal" (by decide)]
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
      rw [hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧ k ≠ 8 ∧ k ≠ 16 ∧ k ≠ 232 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2.1 hk_ok.2.2.2.1 hk_ok.2.2.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega) (by omega) (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega) (by omega) (by omega)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, ?_, m7, ?_, m9⟩
    · intro j hj hij
      have hj_tail : (evmChain s)[j] ∈ chTail := by
        rcases j with _ | j'
        · omega
        · simp [hch_eq]
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [htail_fs_eq _ hj_tail, htail_fo_eq _ hj_tail, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · rcases i with _ | i'
      · have hi0_eq : ((evmChain s)[0]'(by omega)) = (e0, c0) := by simp [hch_eq]
        rw [hi0_eq] at m6 ⊢
        intro o ho
        unfold frameScratch at ho
        rw [he0_other 88 (by omega) (by omega) (by omega) (by omega) (by omega)] at ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl
        · exact m6 _ (by simp [frameScratch])
        · exact m6 _ (by simp [frameScratch])
        · rcases hnew_stk with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
          · rw [h8_eq, h232_eq]; exact m6 _ (by simp [frameScratch])
          · rw [hstk_eq]
            rcases hfresh with hf0 | ⟨_, _, _, hfin2⟩
            · exact absurd hf0 hnz
            · have he0_m : e0 + 280 ≤ memW s (c0 + 48) := m6 (e0, 280) (by simp [frameScratch])
              obtain ⟨he0_scr, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).1
              dsimp only at he0_m he0_scr ⊢
              omega
        · exact m6 _ (by simp [frameScratch])
      · have hi_tail : ((evmChain s)[i' + 1]'(by omega)) ∈ chTail := by simp [hch_eq]
        rw [htail_fs_eq _ hi_tail]; exact m6
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
