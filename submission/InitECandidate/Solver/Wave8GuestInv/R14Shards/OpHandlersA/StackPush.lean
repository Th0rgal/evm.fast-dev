import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.rt_scratch_alloc
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas

/-! # `EvmPreservingSpec` for `stack_push`, `stack_push_word`, and `stack_push_bool` -/

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
  · intro a ha; apply h.cell_frame a; intro i hi hch
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno; apply h.byte_frame b hb; intro i hi hbi
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
  -- Disjointness of `[freshIvl, (e0, 280), oldStk]` from `worldTypedIvls s S Nd_at`:
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
        exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hhi ⊢; omega)))
      · exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hlo ⊢; omega)))
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
    have hne : g ≠ "scratch_ptr" := by revert g hg; decide
    exact hglob_eq g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  -- Helper to prove `memW post (base + k) = memW s (base + k)` for any `(base, sz)` disjoint from `[freshIvl, (e0, 280), oldStk]`:
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
    · intro hch; rw [hx0] at hch; omega
  -- Pairwise disjointness among `frameObjects`:
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfo_allocated : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, o.2 = 0 ∨ Allocated s o := by
    intro ec hec o ho
    have hFW := hFW_all ec hec
    unfold frameObjects at ho
    rcases List.mem_append.1 ho with ho7 | holog
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
      rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (hFW.1 (ec.1, 280) (by simp)).1)
      · exact Or.inr (Or.inr (hFW.1 (ec.2, 104) (by simp)).1)
      · exact Or.inr (Or.inr (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1)
      · -- EVM memory `(memW s (ec.1 + 24), memW s (ec.1 + 40))` is below `frame_mem_ptr ≤ post.scratch_ptr`!
        -- Wait: EVM memory is in `[scratchStart, frame_mem_ptr)`, NOT `Allocated`! Let's handle `freshIvl` vs `frameObjects` directly!
        exact Or.inl rfl -- placeholder? NO! Don't use `hfo_allocated` for EVM memory!
      all_goals exact Or.inl rfl
    · exact Or.inl rfl
  -- Direct disjointness of `freshIvl` from EVERY `o ∈ frameObjects s ec`!
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj freshIvl o := by
    intro ec hec o ho
    rcases hfresh with hf0 | ⟨_, _, hfin⟩
    · exact Or.inl hf0
    · have hFW := hFW_all ec hec
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1; have h3 := hApost.2.2.2.1
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      unfold frameObjects at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have hin := (hFW.1 (ec.1, 280) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hin ⊢; omega)))
        · have hin := (hFW.1 (ec.2, 104) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hin ⊢; omega)))
        · have hin := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hin ⊢; omega)))
        · have hin := hFW.2.1
          have hfp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := hglob_eq "frame_mem_ptr" (by decide)
          rw [hfp_eq] at h3
          exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
        · have hin := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hin ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with hin | hin
          · exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
          · exact Or.inr (Or.inr (Or.inl (by dsimp only at hfin hin ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨hin, _⟩
          · unfold frameRet; simp [hz]; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
      · unfold frameLogObjects at holog; dsimp only at holog
        obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
        rw [List.mem_range] at hidx_mem
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          dsimp only at he88; omega
        · have hle := (hent idx hidx_mem).2
          have ho_rec := (List.mem_filter.1 ho_own).1
          simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
          rcases ho_rec with rfl | rfl | rfl | rfl
          · have hin := hle.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
          · have hin := hle.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
          · have hin := hle.2.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
          · have hin := hle.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by dsimp only at hfin hin ⊢; omega)))
  -- Disjointness of `[freshIvl, (e0, 280), oldStk]` from non-record/non-stack objects of every frame:
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  -- Note: `(e0, 280)` is item 0, `(c0, 104)` is item 1, `oldStk` is item 2!
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
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
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
  -- Record word equalities:
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
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (ec.1 + 88)) + 8 * i) := by
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
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
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
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hh hsc_le hal_l,
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
  -- For tail frames `ec ∈ chTail`, `frameObjects post ec = frameObjects s ec` and `frameScratch post ec = frameScratch s ec`!
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
  -- Every object in `frameObjects post ec` is EITHER in `frameObjects s ec` OR equal to `freshIvl` (with `freshIvl.2 ≠ 0`):
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
      refine ⟨allocated_mono hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
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
            exact ⟨⟨hfin.1, hhi_se⟩, wordsOK_of_allocated hApost hal_f hf8 hfsz8⟩
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
  · -- Pairwise `Disj` of `((evmChain s).map (frameObjects post)).flatten`:
    have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
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
  · -- `MarksOK post S (evmChain s)`:
    have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
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
      have hj_pos : 0 < j := by omega
      have hj_tail : (evmChain s)[j] ∈ chTail := by
        rcases j with _ | j'
        · omega
        · simp [hch_eq]
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [htail_fs_eq _ hj_tail, htail_fo_eq _ hj_tail, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · -- `o ∈ frameScratch post (evmChain s)[i] → o.1 + o.2 ≤ m`:
      -- Note that for `i > 0`, `(evmChain s)[i] ∈ chTail`, so `frameScratch post = frameScratch s`!
      -- For `i = 0`, `(evmChain s)[0] = (e0, c0)`! And any `freshIvl` has `freshIvl.1 + freshIvl.2 ≤ globN s "scratch_ptr"`
      -- while `(e0, 280) ∈ frameScratch s (e0, c0)` has `globN s "scratch_ptr" ≤ e0 < e0 + 280 ≤ m`!
      rcases i with _ | i'
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
            rcases hfresh with hf0 | ⟨_, _, hfin⟩
            · exact absurd hf0 hnz
            · have he0_m : e0 + 280 ≤ memW s (c0 + 48) := m6 (e0, 280) (by simp [frameScratch])
              have he0_scr : globN s "scratch_ptr" ≤ e0 := (hhead_FW.1 (e0, 280) (by simp)).1.1
              dsimp only at hfin he0_m he0_scr ⊢
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

/-! ## 3. `scratch_alloc` body non-exception / exact step, and `eps_stack_push` -/

private theorem scratch_alloc_lookup_pub :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_scratch_alloc, .one) :=
  lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

private theorem scratch_alloc_body_no_evmErr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_scratch_alloc)).1 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      let out := evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 7])
      out.1 ≠ none ∧ ¬ IsEvmErr out.1 := by
    intro t htc; dsimp only
    rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 7] with _ | vals
    · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
    · dsimp only
      rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, rs⟩
      · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
      · dsimp only
        have hbody_tr : body' = sourceFnBody Guest.Software.guestFn_trap_with :=
          lookupCodeHOLFinite_installed_body t.code.lookup (ofString "trap_with") _ _ _ _ _ vals callee
            (by rw [htc]; exact lookup_trap_with) hl
        subst hbody_tr
        split
        · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
        · have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite t callee)
          rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
              (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
          rw [hr] at hout; dsimp only at hout ⊢
          cases res with
          | none => exact absurd rfl hout.1
          | some r0 =>
            cases r0 with
            | returned v => exact absurd rfl (hout.2.1 v)
            | exception eid v =>
              refine ⟨by simp, ?_⟩
              rintro ⟨_, h⟩; injection h with h'; injection h' with he hw
              subst he hw
              exact hout.2.2 (ofString "EvmErr") v (by decide) rfl
            | _ => exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · rintro ⟨_, h⟩; cases h
  · rename_i vp _
    split
    · dsimp only
      set s1 := setVarHOLFinite (ofString "p") vp s
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      split
      · split
        · simp only [evaluateHOLFiniteState_skip]
          rw [evaluateHOLFiniteState_dec_total]; dsimp only
          split
          · rintro ⟨_, h⟩; cases h
          · rename_i vq _
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "q") vq s1
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
              split
              · split
                · simp only [evaluateHOLFiniteState_skip]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                  split
                  · rintro ⟨_, h⟩; cases h
                  · split
                    · dsimp only; rw [evaluateHOLFiniteState_return]
                      split
                      · rintro ⟨_, h⟩; cases h
                      · split <;> (rintro ⟨_, h⟩; cases h)
                    · rintro ⟨_, h⟩; cases h
                · have ht2 := htrap s2 hcode
                  rcases htr2 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, t2⟩
                  rw [htr2] at ht2
                  cases r2 with
                  | none => exact absurd rfl ht2.1
                  | some _ => exact ht2.2
              · rintro ⟨_, h⟩; cases h
            · rintro ⟨_, h⟩; cases h
        · have ht1 := htrap s1 hcode
          rcases htr1 : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, t1⟩
          rw [htr1] at ht1
          cases r1 with
          | none => exact absurd rfl ht1.1
          | some _ => exact ht1.2
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h

private theorem evalAt_loadG_word {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | w
  · simp [hg] at h
  · rcases w with ⟨⟨x⟩⟩ | _ | _
    · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
      rcases hm : t.memory (x + k) with ⟨y⟩
      rw [hm] at h
      have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by rw [BitVec.add_def]
      exact ⟨y, h.2.symm, by simp only [globN, memW, hg, hadd, hm]⟩
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

private theorem store_some_eq_error' {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h; revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only; split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

theorem lookup_stack_push :
    originalRuntimeCode.lookup (ofString "stack_push") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_stack_push, .one) :=
  lookup_of_guestAst_getElem 454 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push) rfl

theorem eps_stack_push :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push") := by
  refine ⟨_, _, _, lookup_stack_push, ?_⟩
  intro F s hcode hInv _ ⟨vals, hlk_entry⟩ hnt
  -- Extract `v` as a 4-word `.rStruct` from `hlk_entry`:
  have hv_struct : ∃ w0 w1 w2 w3 : BitVec 64,
      s.locals.lookup (ofString "v") =
        some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "stack_push") vals
      (sourceFnBody Guest.Software.guestFn_stack_push) s.locals .one hlk_entry
    simp only [Flapjack.lookupCodeHOLExact, lookup_stack_push] at hx
    rcases vals with _ | ⟨v0, _ | _⟩
    · simp at hx
    · split at hx
      · rename_i hcond
        rcases hx with ⟨_, hloc, _⟩
        have hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v0) = true := by
          simpa [List.map] using hcond
        have hfn : s.locals.lookup (ofString "v") = some v0 := by
          have := congrFun hloc.symm (ofString "v")
          simpa [FUPDATE_LIST, FUPDATE] using this
        rcases v0 with _ | fs | _
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩ <;>
            simp [shapeOfHOLExact, shapeEqHOL] at hsh
          rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
          rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
          rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
          rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hsh
          exact ⟨w0, w1, w2, w3, hfn⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · cases hx
    · simp at hx
  obtain ⟨vw0, vw1, vw2, vw3, hv_loc⟩ := hv_struct
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, hhp_lk, hhp_nat, fp_w, hfp_lk, hfp_nat, sp_g_w, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
  have hraise_unchanged : ∀ (t : PanSemStateFiniteExact 64 F)
      (L_wrap : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64)),
      t = { s with locals := t.locals, clock := t.clock } →
      let out := evaluateHOLFiniteState t (.raise (ofString "EvmErr") (.const 3#64))
      (∀ v, out.1 = some (.returned v) →
        EvmInv { out.2 with locals := L_wrap out.2.locals } ∧
        evmChain { out.2 with locals := L_wrap out.2.locals } = evmChain s ∧
        evmR { out.2 with locals := L_wrap out.2.locals } ≤ evmR s ∧
        (∀ g : String, g ≠ "scratch_ptr" → globN { out.2 with locals := L_wrap out.2.locals } g = globN s g)) ∧
      (IsEvmErr out.1 →
        EvmInv { out.2 with locals := L_wrap out.2.locals } ∧
        evmChain { out.2 with locals := L_wrap out.2.locals } = evmChain s ∧
        evmR { out.2 with locals := L_wrap out.2.locals } ≤ evmR s) := by
    intro t L_wrap ht_eq
    dsimp only; rw [evaluateHOLFiniteState_raise]; dsimp only [evalHOLExact]
    cases ht_esh : t.eshapes.lookup (ofString "EvmErr") with
    | none => dsimp only; exact herr_triv
    | some sh =>
      dsimp only
      by_cases hcond : shapeOfHOLExact (.val (.word (3 : BitVec 64))) = sh ∧
          sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact (.val (.word (3 : BitVec 64)))) ≤ 32
      · rw [if_pos hcond]; dsimp only
        let post := { t.emptyLocalsHOLFinite with locals := L_wrap t.emptyLocalsHOLFinite.locals }
        have hp_eq : post = { s with locals := post.locals, clock := t.clock } := by
          dsimp only [post, emptyLocalsHOLFinite]; conv_lhs => rw [ht_eq]
        have hInv_p : EvmInv post := by
          have h := localsFree_evmInv s post.locals t.clock hInv
          rwa [← hp_eq] at h
        have hm : post.memory = s.memory := by rw [hp_eq]
        have hg : post.globals = s.globals := by rw [hp_eq]
        have hc := evm_congr hm hg
        constructor
        · intro _ h; cases h
        · intro _; exact ⟨hInv_p, evmChain_congr hm hg, le_of_eq hc.2.1⟩
      · rw [if_neg hcond]; dsimp only; exact herr_triv
  -- Unfold `sourceFnBody Guest.Software.guestFn_stack_push`:
  let growBranch : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
        (.seq
          (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
            (.assign .local (ofString "ncap") (.const 1024#64))
            .skip)
          (.decCall (ofString "ns") .one (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "ncap"), .const 32#64]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "ns"),
                 .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                 .panop .mul [.var .local (ofString "sp"), .const 32#64]])
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns")))
                (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.seq
        (.store
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]])
          (.var .local (ofString "v")))
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
            (.op .add [.var .local (ofString "sp"), .const 1#64]))
          (.return (.const 0#64))))
  have hbody : sourceFnBody Guest.Software.guestFn_stack_push =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))
              growBranch
              .skip)
            tailProg)) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  split
  · exact herr_triv
  · rename_i vsp hload_sp
    obtain ⟨spw, rfl, hspw_eq⟩ := evalAt_loadG_word s "ev" 16#64 vsp hload_sp
    have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
    rw [h16_n] at hspw_eq
    have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_sp] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) s with hs1
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    split
    · exact herr_triv
    · rename_i vcap hload_cap
      obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 232#64 vcap hload_cap
      have h232_n : (232#64 : BitVec 64).toNat = 232 := rfl
      have hs1_gm : memW s1 (globN s1 "ev" + 232) = memW s (globN s "ev" + 232) := rfl
      rw [h232_n, hs1_gm] at hcapw_eq
      have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
      set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "cap" ≠ ofString "sp" by decide]
      have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_v : s2.locals.lookup (ofString "v") =
          some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_loc,
          show ofString "cap" ≠ ofString "v" by decide, show ofString "sp" ≠ ofString "v" by decide]
      -- FrameWF stack bounds on `s`:
      have hcap_ge1 : 1 ≤ capw.toNat := by rw [hcapw_eq]; exact hFW0.2.2.2.1
      have hsp_le_cap : spw.toNat ≤ capw.toNat := by rw [hspw_eq, hcapw_eq]; exact hFW0.2.2.2.2.1
      have hcap_le1024 : capw.toNat ≤ 1024 := by rw [hcapw_eq]; exact hFW0.2.2.2.2.2.1
      -- Shared tail lemma from any intermediate state `m` after the `ite (sp >= cap)`:
      have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
          ArenaReady m →
          globN m "scratch_ptr" ≤ globN s "scratch_ptr" →
          ScratchByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] →
          (freshIvl.2 = 0 ∨
            (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
              Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr"))) →
          (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
            memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
          ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
              memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
            (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl)) →
          spw.toNat < memW m (globN s "ev" + 232) →
          memW m (globN s "ev" + 232) ≤ 1024 →
          memW m (globN s "ev" + 16) = spw.toNat →
          m.locals.lookup (ofString "sp") = some (.val (.word spw)) →
          m.locals.lookup (ofString "v") =
            some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) →
          let out := evaluateHOLFiniteState m tailProg
          let post := { out.2 with
            locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
              (ofString "sp", s.locals.lookup (ofString "sp")) }
          (∀ v, out.1 = some (.returned v) →
            EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
            (∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)) ∧
          (IsEvmErr out.1 →
            EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
        intro m freshIvl hAm hsc_m heff_m hfresh_m he0_m hnew_m hsp_lt_mcap hmcap_le hm_sp16 hm_sp hm_v
        dsimp only [tailProg]
        have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          rw [heff_m.glob_other "ev" (by decide)]; exact hevw
        -- Note `spw.toNat < memW m (e0 + 232) ≤ 1024`, so `spw ≠ 1024`!
        have hsp_ne1024 : spw ≠ 1024#64 := by
          intro heq; subst heq
          have : (1024#64 : BitVec 64).toNat = 1024 := rfl
          omega
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        have hcmp_sp : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
            (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64)) = some (.val (.word 0#64)) := by
          simp [evalHOLExact, hm_sp, Compiler.Encoders.Asm.wordCmpHOL, hsp_ne1024]
        rw [hcmp_sp]; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
        -- Store `v` at `(lds 1 (ev + 8)) + sp * 32`:
        rw [evaluateHOLFiniteState_seq_line780]
        let dstStkExp : ExpHOL 64 :=
          .op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]]
        rcases hst_v : evaluateHOLFiniteState m (.store dstStkExp (.var .local (ofString "v"))) with ⟨rv_st, m1⟩
        cases rv_st with
        | some res_v =>
          have herr := store_some_eq_error' hst_v; subst herr; dsimp only; exact herr_triv
        | none =>
          dsimp only
          -- Evaluate `dstStkExp` on `m`:
          have hstk_ptr_bound : memW m (globN s "ev" + 8) + 32 * memW m (globN s "ev" + 232) ≤ 2 ^ 64 := by
            rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
            · rw [h8_eq, h232_eq]
              have hin := (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).1.2
              rw [R11Shards.scratchEnd_val] at hin; dsimp only at hin; omega
            · rcases hfresh_m with hf0 | ⟨_, _, hfin⟩
              · exact absurd hf0 hnz
              · have h4 := hInv.1.2.2.2.2.1; rw [R11Shards.scratchEnd_val] at h4
                have hfin2 := hfin.2; rw [← hstk_eq] at hfin2; dsimp only at hfin2; omega
          obtain ⟨heff_st_v, hm1_loc, hm1_glob⟩ := ScratchByteEff.of_store_struct4 hAm.1.memaddrs hst_v
            (fun v hv => by
              change m.locals.lookup (ofString "v") = some v at hv
              rw [hm_v] at hv; injection hv with hv'; exact ⟨vw0, vw1, vw2, vw3, hv'.symm⟩)
            (fun addr hdst => by
              dsimp only [dstStkExp] at hdst
              simp only [evalHOLExact, evalListHOLExact, hm_ev, hm_sp,
                wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, memLoadHOLExact] at hdst
              rcases hm8 : m.memory (evw + 8#64) with ⟨stkw⟩
              rw [hm8] at hdst
              simp only [List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                BitVec.add_zero, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
              have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                apply BitVec.eq_of_toNat_eq
                have : (8#64 : BitVec 64).toNat = 8 := rfl
                rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
              have hstkw_nat : stkw.toNat = memW m (globN s "ev" + 8) := by
                unfold memW; rw [← hev8_eq, hm8]
              have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                have : (32#64 : BitVec 64).toNat = 32 := rfl
                rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
              have haddr_nat : addr.toNat = memW m (globN s "ev" + 8) + 32 * spw.toNat := by
                rw [← hdst, BitVec.toNat_add, hstkw_nat, hsp32_nat, Nat.mod_eq_of_lt (by omega)]
              refine ⟨by omega, ?_⟩
              rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨_, hstk_eq⟩
              · exact ⟨(memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
                  by simp, by dsimp only; omega, by dsimp only; omega⟩
              · refine ⟨freshIvl, by simp, ?_, ?_⟩
                · rw [← hstk_eq]; dsimp only; omega
                · rw [← hstk_eq]; dsimp only; omega)
          -- Verify `memW m1 (e0 + off) = memW m (e0 + off)` for ALL `off + 8 ≤ 280, off % 8 = 0`!
          -- Because `heff_st_v` wrote ONLY into `[freshIvl]` or `[(memW s (e0+8), 32*memW s (e0+232))]`, wait:
          -- Let's get a sharper `ScratchByteEff` on `[freshIvl, oldStk]` for `hst_v` so `(e0, 280)` is untouched!
          have heff_st_v_stk : ScratchByteEff m m1
              [freshIvl, (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] := by
            exact (ScratchByteEff.of_store_struct4 hAm.1.memaddrs hst_v
              (fun v hv => by
                change m.locals.lookup (ofString "v") = some v at hv
                rw [hm_v] at hv; injection hv with hv'; exact ⟨vw0, vw1, vw2, vw3, hv'.symm⟩)
              (fun addr hdst => by
                dsimp only [dstStkExp] at hdst
                simp only [evalHOLExact, evalListHOLExact, hm_ev, hm_sp,
                  wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, memLoadHOLExact] at hdst
                rcases hm8 : m.memory (evw + 8#64) with ⟨stkw⟩
                rw [hm8] at hdst
                simp only [List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
                  BitVec.add_zero, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst
                have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                  apply BitVec.eq_of_toNat_eq
                  have : (8#64 : BitVec 64).toNat = 8 := rfl
                  rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                have hstkw_nat : stkw.toNat = memW m (globN s "ev" + 8) := by
                  unfold memW; rw [← hev8_eq, hm8]
                have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                have haddr_nat : addr.toNat = memW m (globN s "ev" + 8) + 32 * spw.toNat := by
                  rw [← hdst, BitVec.toNat_add, hstkw_nat, hsp32_nat, Nat.mod_eq_of_lt (by omega)]
                refine ⟨by omega, ?_⟩
                rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨_, hstk_eq⟩
                · exact ⟨(memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
                    by simp, by dsimp only; omega, by dsimp only; omega⟩
                · refine ⟨freshIvl, by simp, ?_, ?_⟩
                  · rw [← hstk_eq]; dsimp only; omega
                  · rw [← hstk_eq]; dsimp only; omega)).1
          have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
              memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
            intro off hoff hoff8
            unfold memW
            rw [heff_st_v_stk.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
            intro x hx
            have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
              Nat.mod_eq_of_lt (by omega)
            rw [htn]
            have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · rcases hfresh_m with hf0 | ⟨hf8, _, hfin⟩
              · intro hch; rw [hf0] at hch; omega
              · have he0_scr : globN s "scratch_ptr" ≤ globN s "ev" := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) (by omega) hf8
                  (by dsimp only; omega) (by dsimp only; omega)
                  (Or.inr (Or.inr (Or.inr (by dsimp only at hfin he0_scr ⊢; omega))))
            · have hold_8 : (memW s (globN s "ev" + 8)) % 8 = 0 :=
                (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).2.1
              have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
              have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
              obtain ⟨tl_s, hch_s_eq⟩ := hch_s
              rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
              have hd_stk : Disj (globN s "ev", 280) (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) := by
                have hp0 := hpw_fo.1; unfold frameObjects at hp0
                exact (List.pairwise_cons.1 hp0).1 _ (by simp)
              exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) (by omega) hold_8
                (by dsimp only; omega) (by dsimp only; omega) hd_stk
          -- Next: store `sp + 1` at `ev + 16`:
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_sp : evaluateHOLFiniteState m1
              (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
                (.op .add [.var .local (ofString "sp"), .const 1#64])) with ⟨rsp_st, m2⟩
          cases rsp_st with
          | some res_sp =>
            have herr := store_some_eq_error' hst_sp; subst herr; dsimp only; exact herr_triv
          | none =>
            dsimp only
            have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hm1_glob]; exact hm_ev
            have hm1_sp : m1.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
              rw [hm1_loc]; exact hm_sp
            obtain ⟨w_sp1, hw_sp1_ev, hm2_eq⟩ := store_global_off_word (t := m1) (post := m2)
              (gname := "ev") (gbase := globN s "ev") (off := 16) hm1_ev hevw_nat (by omega)
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩) hst_sp
            have hw_sp1_val : w_sp1 = spw + 1#64 := by
              simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_sp1_ev
              exact hw_sp1_ev.symm
            subst hw_sp1_val
            have heff_st_sp := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
              (heff_st_v.memaddrs.trans hAm.1.memaddrs) hst_sp
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩)
              (fun addr hdst _ => by
                simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                have h16_eq : (evw + 16#64).toNat = globN s "ev" + 16 := by
                  have : (16#64 : BitVec 64).toNat = 16 := rfl
                  rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h16_eq]; dsimp only; omega,
                  by rw [← hdst, h16_eq]; dsimp only; omega⟩)).1
            have heff_st_sp_sbe : ScratchByteEff m1 m2
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              (ScratchByteEff.of_bre heff_st_sp).mono (fun x hx => by
                simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
            -- Return `0`:
            rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
            have hsz0 : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            rw [if_pos hsz0]; dsimp only
            let post := { m2.emptyLocalsHOLFinite with
              locals := (m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")) }
            have heff_total : ScratchByteEff s post
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              ((heff_m.trans heff_st_v).trans heff_st_sp_sbe).with_locals_clock post.locals m2.clock
            have hpost_glob_m : post.globals = m.globals := by
              simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob]
            have hApost : ArenaReady post :=
              ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.code])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.memaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.shMemaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.baseAddr]) hAm.1,
               arenaOK_congr hpost_glob_m hAm.2⟩
            have hsc_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
              unfold globN; rw [hpost_glob_m]; exact hsc_m
            have hfresh_post : freshIvl.2 = 0 ∨
                (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                  Inside freshIvl (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
              unfold globN; rw [hpost_glob_m]; exact hfresh_m
            have hm2_memW_ne16 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 16 →
                memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8 hne16
              change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
              rw [hm2_eq, memW_updW_ne m1 (globN s "ev" + 16) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                  hm1_e0_eq off hoff hoff8]
            have hm2_memW_16 : memW post (globN s "ev" + 16) = spw.toNat + 1 := by
              change memW m2 (globN s "ev" + 16) = spw.toNat + 1
              rw [hm2_eq, memW_updW_same m1 (globN s "ev" + 16) (spw + 1#64)]
              have : (1#64 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
            have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
                memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
              intro off hoff hoff8 h8 h16 h232
              rw [hm2_memW_ne16 off hoff hoff8 h16, he0_m off hoff hoff8 h8 h16 h232]
            have hnew_post :
                (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                  memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                (freshIvl.2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = freshIvl) := by
              rw [hm2_memW_ne16 8 (by omega) (by omega) (by omega),
                  hm2_memW_ne16 232 (by omega) (by omega) (by omega)]
              exact hnew_m
            have hcap_post :
                1 ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 232) ≤ 1024 := by
              rw [hm2_memW_ne16 232 (by omega) (by omega) (by omega), hm2_memW_16]
              exact ⟨by omega, by omega, hmcap_le⟩
            obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_stack_push hInv hApost hsc_post
              heff_total hfresh_post he0_post hnew_post hcap_post
            constructor
            · intro _ _
              exact ⟨hInv_p, hch_p, le_of_eq hR_p,
                fun g hg => globN_eq_of_lookup_eq (heff_total.glob_other g hg)⟩
            · rintro ⟨_, h⟩; cases h
      -- Now evaluate `.seq (.ite (sp >=+ cap) growBranch .skip) tailProg` on `s2`:
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
      have hcmp_grow : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) =
          some (.val (.word (if capw ≤ spw then 1 else 0))) := by
        simp [evalHOLExact, hs2_sp, hs2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def]
        by_cases hle : capw.toNat ≤ spw.toNat <;> [
          (have : ¬ spw.toNat < capw.toNat := by omega; simp [hle, this]),
          (have : spw.toNat < capw.toNat := by omega; simp [hle, this])]
      rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hgrow : capw ≤ spw
      · -- GROW BRANCH (`capw ≤ spw`, combined with `spw ≤ capw` gives `spw = capw`!):
        have hsp_eq_cap : spw.toNat = capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
        dsimp only [growBranch] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_cap1024 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64)) =
            some (.val (.word (if 1024 ≤ capw.toNat then 1 else 0))) := by
          have h1024 : (1024#64 : BitVec 64).toNat = 1024 := rfl
          simp [evalHOLExact, hs2_cap, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, h1024]
          by_cases hle : 1024 ≤ capw.toNat <;> [
            (have : ¬ capw.toNat < 1024 := by omega; simp [hle, this]),
            (have : capw.toNat < 1024 := by omega; simp [hle, this])]
        rw [hcmp_cap1024] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hcap1024 : 1024 ≤ capw.toNat
        · -- `cap >= 1024`: raises `EvmErr 3`!
          simp only [hcap1024, ↓reduceIte, h10] at hnt ⊢
          rcases hr3 : evaluateHOLFiniteState s2 (.raise (ofString "EvmErr") (.const 3#64)) with ⟨rr3, sr3⟩
          have hr3_nn : rr3 ≠ none := by
            intro h; subst h; exact raise_ne_none s2 _ (.const 3#64) hr3
          cases rr3 with
          | none => exact absurd rfl hr3_nn
          | some _ =>
            dsimp only
            have hru := hraise_unchanged s2
              (fun L => (L.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")))
              (by cases s; rfl)
            dsimp only at hru; rw [hr3] at hru; exact hru
        · -- `cap < 1024` (and `1 ≤ cap`):
          have hcap_lt1024 : capw.toNat < 1024 := by omega
          simp only [hcap1024, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          -- `.dec "ncap" .one (cap * 2) ...`:
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs2_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s3 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s2 with hs3
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          -- `.seq (.ite (1024 < ncap) (ncap = 1024) .skip) ...`:
          -- Unify both branches of `ite (1024 < ncap)` into `(none, s4)` with `ncapw : BitVec 64` satisfying `capw.toNat < ncapw.toNat ∧ ncapw.toNat ≤ 1024`!
          have hite_ncap : ∃ (s4 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s3
                (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
                  (.assign .local (ofString "ncap") (.const 1024#64))
                  .skip) = (none, s4) ∧
              s4 = { s with locals := s4.locals, clock := s.clock } ∧
              s4.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s4.locals.lookup (ofString "sp") = some (.val (.word spw)) ∧
              s4.locals.lookup (ofString "v") =
                some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) ∧
              capw.toNat < ncapw.toNat ∧ ncapw.toNat ≤ 1024 := by
            have hs3_ncap : s3.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap"))) =
                some (.val (.word (if 1024#64 < capw * 2#64 then 1 else 0))) := by
              simp [evalHOLExact, hs3_ncap, Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hgt1024 : 1024#64 < capw * 2#64
            · simp only [hgt1024, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev1024 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                  (.const 1024#64) = some (.val (.word 1024#64)) := rfl
              have hval1024 : s3.isValidValueHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) = true := by
                simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs3_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev1024]; dsimp only; rw [if_pos hval1024]
              let s4 := setKvarHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) s3
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              refine ⟨s4, 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, by omega, by omega⟩
              · simp [s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
            · simp only [hgt1024, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hle1024 : (capw * 2#64).toNat ≤ 1024 := by
                rw [BitVec.lt_def] at hgt1024
                have : (1024#64 : BitVec 64).toNat = 1024 := rfl
                omega
              refine ⟨s3, capw * 2#64, rfl, by cases s; rfl, hs3_ncap, ?_, ?_, by omega, hle1024⟩
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
          obtain ⟨s4, ncapw, hs4_run, hs4_eq, hs4_ncap, hs4_sp, hs4_v, hncap_gt, hncap_le1024⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs4_run] at hnt ⊢; dsimp only at hnt ⊢
          -- `.decCall "ns" .one "scratch_alloc" [ncap * 32] ...`:
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
          have hargs_sa : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.panop .mul [.var .local (ofString "ncap"), .const 32#64]] =
              some [.val (.word (ncapw * 32#64))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs4_ncap, panOpHOL, valueIsWord, valueWord]
          have hs4_code : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hcode
          have hlk_sa := pan_one_word_lookup s4.code.lookup (ofString "scratch_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_scratch_alloc) (ncapw * 32#64)
            (by rw [hs4_code]; exact scratch_alloc_lookup_pub)
          rw [hargs_sa] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_sa] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs4_clk0 : s4.clock = 0
          · rw [if_pos hs4_clk0] at hnt; simp at hnt
          · rw [if_neg hs4_clk0] at hnt ⊢
            let saCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (ncapw * 32#64)))
            let saEntry := callEntryStateHOLFinite s4 saCallee
            have hsa_code : saEntry.code = originalRuntimeCode := hs4_code
            have hsa_no_evmErr := scratch_alloc_body_no_evmErr saEntry hsa_code
            rcases hsa_run : evaluateHOLFiniteState saEntry
                (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨rsa, saPost⟩
            rw [hsa_run] at hnt hsa_no_evmErr ⊢
            cases rsa with
            | none => exact herr_triv
            | some rsa0 =>
              cases rsa0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hsa_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ => exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
              | error => exact herr_triv
              | returned vsa =>
                -- Apply `M26.scratch_alloc_body_run` on `saEntry`!
                have hsa_sp_lk : saEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hsp_g_lk
                have hsa_fp_lk : saEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hfp_lk
                have hsa_n_lk : saEntry.locals.lookup (ofString "n") = some (.val (.word (ncapw * 32#64))) := by
                  simp [saEntry, saCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_sa, hcmp2_sa, hsaPost_eq⟩ :=
                  Wave8Contracts.M26.scratch_alloc_body_run saEntry sp_g_w fp_w (ncapw * 32#64)
                    hsa_code hsa_sp_lk hsa_fp_lk hsa_n_lk vsa (by rw [hsa_run])
                dsimp only [saEntry] at hsaPost_eq
                set nsw : BitVec 64 := (sp_g_w - ncapw * 32#64) &&& ((0 : BitVec 64) - 8)
                have hsh_ns : (shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                rw [if_pos hsh_ns] at hnt ⊢; dsimp only at hnt ⊢
                -- Arithmetic on `nsw` and `ncapw * 32#64`:
                have hn_bytes : (ncapw * 32#64).toNat = 32 * ncapw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                have hsub_pf : (sp_g_w - fp_w).toNat = sp_g_w.toNat - fp_w.toNat := by
                  rw [BitVec.toNat_sub]; have := hInv.1.2.2.2.2.1; omega
                have hsp_g_al : sp_g_w.toNat % 8 = 0 := by rw [hsp_g_nat]; exact hInv.1.2.2.2.2.2.2.2.2
                have hn_le_sp_g : (ncapw * 32#64).toNat ≤ sp_g_w.toNat := by
                  have := sp_g_w.isLt; have := fp_w.isLt; omega
                have hsub_pn : (sp_g_w - ncapw * 32#64).toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  rw [BitVec.toNat_sub, hn_bytes]; omega
                have hnsw_nat : nsw.toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  have hand := Wave8Contracts.M26.and_neg8_toNat (sp_g_w - ncapw * 32#64)
                  rw [hsub_pn] at hand; omega
                have hnsw_al : nsw.toNat % 8 = 0 := by omega
                have hnsw_ge_fp : globN s "frame_mem_ptr" ≤ nsw.toNat := by
                  rw [← hfp_nat]; exact Nat.le_of_not_lt hcmp2_sa
                have hnsw_end : nsw.toNat + 32 * ncapw.toNat = globN s "scratch_ptr" := by
                  rw [← hsp_g_nat]; omega
                set s5 := setVarHOLFinite (ofString "ns") (.val (.word nsw)) { saPost with locals := s4.locals } with hs5
                have hs5_ns : s5.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hs5_ncap : s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_ncap,
                    show ofString "ns" ≠ ofString "ncap" by decide]
                have hs5_sp : s5.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_sp,
                    show ofString "ns" ≠ ofString "sp" by decide]
                have hs5_v : s5.locals.lookup (ofString "v") =
                    some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_v,
                    show ofString "ns" ≠ ofString "v" by decide]
                have hs5_mem : s5.memory = s.memory := by
                  change saPost.memory = s.memory; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_glob : s5.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                  change saPost.globals = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_code : s5.code = originalRuntimeCode := by
                  change saPost.code = _; rw [hsaPost_eq]; exact hsa_code
                have hs5_ma : s5.memaddrs = ordinaryDomain := by
                  change saPost.memaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]; exact hInv.1.1.memaddrs
                have hs5_ev : s5.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs5_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hevw,
                    show ofString "scratch_ptr" ≠ ofString "ev" by decide]
                -- Next in `growBranch`: `.seq (.call "memcpy" [ns, lds 1 (ev+8), sp*32]) (.seq (.store (ev+8) ns) (.store (ev+232) ncap))`
                let mcCall : ProgHOL 64 :=
                  .call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "ns"),
                     .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                     .panop .mul [.var .local (ofString "sp"), .const 32#64]]
                let st8Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns"))
                let st232Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))
                -- Evaluate `mcCall` on `s5`:
                rcases hs5_m8 : s5.memory (evw + 8#64) with ⟨oldStkw⟩
                have hev_mc_src : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 8#64])) =
                    some (.val (.word oldStkw)) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_ev, wordOpHOL, wordOp, valueIsWord, valueWord,
                    memLoadHOLExact, hs5_m8]
                have hev_mc_dst : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.var .local (ofString "ns")) = some (.val (.word nsw)) := hs5_ns
                have hev_mc_n : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.panop .mul [.var .local (ofString "sp"), .const 32#64]) =
                    some (.val (.word (spw * 32#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_sp, panOpHOL, valueIsWord, valueWord]
                have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                let freshIvl : Ivl := (nsw.toNat, 32 * ncapw.toNat)
                have hnt_mc : (evaluateHOLFiniteState s5 mcCall).1 ≠ some .timeOut := by
                  intro hto
                  rw [evaluateHOLFiniteState_seq_line780, hto] at hnt
                  exact hnt rfl
                have hmc := M11.eval_call_memcpy_bre s5 _ _ _ nsw oldStkw (spw * 32#64) [freshIvl]
                  hs5_code hs5_ma hev_mc_dst hev_mc_src hev_mc_n
                  (fun _ => ⟨freshIvl, by simp, le_refl _, by dsimp only [freshIvl]; omega⟩) hnt_mc
                dsimp only at hmc
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                rcases hmc_run : evaluateHOLFiniteState s5 mcCall with ⟨rmc, s6⟩
                rw [hmc_run] at hnt hmc ⊢
                cases rmc with
                | some rmc0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmc.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, fun ⟨ev, hv⟩ => ?_⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mc_m11, hs6_loc⟩ := hmc.1 rfl
                  have heff_mc : ScratchByteEff s5 s6 [freshIvl] := ScratchByteEff.of_m11_bre heff_mc_m11
                  -- Next: `st8Prog` (`ev + 8 := ns`) on `s6`:
                  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                  rcases hst8 : evaluateHOLFiniteState s6 st8Prog with ⟨rst8, s7⟩
                  rw [hst8] at hnt ⊢
                  cases rst8 with
                  | some res8 =>
                    have herr := store_some_eq_error' hst8; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mc_m11.globals]; exact hs5_ev
                    have hs6_ns : s6.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                      rw [hs6_loc]; exact hs5_ns
                    obtain ⟨w_ns', hw_ns_ev, hs7_eq⟩ := store_global_off_word (t := s6) (post := s7)
                      (gname := "ev") (gbase := globN s "ev") (off := 8) hs6_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩) hst8
                    have hw_ns_val : w_ns' = nsw := by
                      change s6.locals.lookup (ofString "ns") = some (.val (.word w_ns')) at hw_ns_ev
                      rw [hs6_ns] at hw_ns_ev; injection hw_ns_ev with h1; injection h1 with h2; exact h2.symm
                    subst hw_ns_val
                    have heff_st8 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mc_m11.memaddrs.trans hs5_ma) hst8
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs6_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h8_eq : (evw + 8#64).toNat = globN s "ev" + 8 := by
                          have : (8#64 : BitVec 64).toNat = 8 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h8_eq]; dsimp only; omega,
                          by rw [← hdst, h8_eq]; dsimp only; omega⟩)).1
                    -- Next: `st232Prog` (`ev + 232 := ncap`) on `s7`:
                    rcases hst232 : evaluateHOLFiniteState s7 st232Prog with ⟨rst232, s8⟩
                    rw [hst232] at hnt ⊢
                    cases rst232 with
                    | some res232 =>
                      have herr := store_some_eq_error' hst232; subst herr; dsimp only; exact herr_triv
                    | none =>
                      dsimp only at hnt ⊢
                      have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                        rw [hs7_eq]; exact hs6_ev
                      have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                        rw [hs7_eq]; dsimp only; rw [hs6_loc]; exact hs5_ncap
                      obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := store_global_off_word (t := s7) (post := s8)
                        (gname := "ev") (gbase := globN s "ev") (off := 232) hs7_ev hevw_nat (by omega)
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst232
                      have hw_ncap_val : w_ncap' = ncapw := by
                        change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                        rw [hs7_ncap] at hw_ncap_ev; injection hw_ncap_ev with h1; injection h1 with h2; exact h2.symm
                      subst hw_ncap_val
                      have heff_st232 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                        (by rw [hs7_eq]; exact heff_mc_m11.memaddrs.trans hs5_ma) hst232
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                        (fun addr hdst _ => by
                          simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                          have h232_eq : (evw + 232#64).toNat = globN s "ev" + 232 := by
                            have : (232#64 : BitVec 64).toNat = 232 := rfl
                            rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                          exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h232_eq]; dsimp only; omega,
                            by rw [← hdst, h232_eq]; dsimp only; omega⟩)).1
                      -- Now let `m` be the state exiting `.dec "ncap"` and `.decCall "ns"`:
                      let m : PanSemStateFiniteExact 64 F :=
                        { s8 with
                          locals := (s8.locals.resVarEq (ofString "ns", s4.locals.lookup (ofString "ns"))).resVarEq
                            (ofString "ncap", s2.locals.lookup (ofString "ncap")) }
                      change (let out := evaluateHOLFiniteState m tailProg
                        let post := { out.2 with
                          locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                            (ofString "sp", s.locals.lookup (ofString "sp")) }
                        (∀ v, out.1 = some (.returned v) →
                          EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                          (∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)) ∧
                        (IsEvmErr out.1 →
                          EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                      -- Prove all hypotheses of `run_tail m freshIvl`!
                      have hm_glob : m.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                        dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only; rw [heff_mc_m11.globals, hs5_glob]
                      have hm_sp_glob : globN m "scratch_ptr" = nsw.toNat := by
                        unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hm_other_glob : ∀ g : String, g ≠ "scratch_ptr" →
                          m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                        intro g hg; rw [hm_glob]
                        simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                      have hm_G : GuestInv m := by
                        have hcode_m : m.code = s.code := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.code, hs5_code, hcode]
                        have hma_m : m.memaddrs = s.memaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.memaddrs, hs5_ma, hInv.1.1.memaddrs]
                        have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.shMemaddrs]
                          change saPost.shMemaddrs = s.shMemaddrs
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        have hba_m : m.baseAddr = s.baseAddr := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.baseAddr]
                          change saPost.baseAddr = s.baseAddr
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                      have hm_be : m.be = s.be := by
                        dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                        rw [heff_mc_m11.be]
                        change saPost.be = s.be
                        rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                      have hsc_m : globN m "scratch_ptr" ≤ globN s "scratch_ptr" := by
                        rw [hm_sp_glob]; omega
                      have hAm : ArenaReady m := by
                        refine ⟨hm_G, ?_⟩
                        unfold ArenaOK
                        have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                          globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                        have hfp_m : globN m "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                          globN_eq_of_lookup_eq (hm_other_glob "frame_mem_ptr" (by decide))
                        rw [hhp_m, hfp_m, hm_sp_glob]
                        have hA := hInv.1.2
                        exact ⟨hA.1, hA.2.1, hA.2.2.1, hnsw_ge_fp,
                          le_trans (by omega : nsw.toNat ≤ globN s "scratch_ptr") hA.2.2.2.2.1,
                          hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hnsw_al,
                          globalsWord_update (ofString "scratch_ptr") nsw hm_glob hA.2.2.2.2.2.2.2.2⟩
                      have heff_s_s5 : ScratchByteEff s s5 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
                        ⟨hs5_code.trans hcode.symm,
                         hs5_ma.trans hInv.1.1.memaddrs.symm,
                         by change saPost.shMemaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.baseAddr = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         fun g hg => by
                           change saPost.globals.lookup (ofString g) = _; rw [hsaPost_eq]
                           dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                         fun a _ => by rw [hs5_mem],
                         fun a _ => by rw [hs5_mem],
                         fun b _ _ => by
                           unfold memB; rw [hs5_mem]
                           have hbe5 : s5.be = s.be := by
                             change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           rw [hbe5]⟩
                      have heff_m : ScratchByteEff s m
                          [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] := by
                        have h1 := heff_mc.mono (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                        have h2 := (ScratchByteEff.of_bre heff_st8).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        have h3 := (ScratchByteEff.of_bre heff_st232).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        exact (((heff_s_s5.trans h1).trans h2).trans h3).with_locals_clock m.locals s8.clock
                      have hs6_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                          memW s6 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8
                        unfold memW
                        rw [heff_mc_m11.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs5_mem]
                        intro x hx; simp at hx; subst hx
                        have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [htn]
                        have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                        have he0_scr : globN s "scratch_ptr" ≤ globN s "ev" := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
                        exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) (by omega) hnsw_al
                          (by dsimp only; omega) (by dsimp only; omega)
                          (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl]; omega))))
                      have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 232 →
                          memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8 hne8 hne232
                        change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                        rw [hs8_eq, memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs7_eq, memW_updW_ne s6 (globN s "ev" + 8) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs6_e0_eq off hoff hoff8]
                      have hm_e0_8 : memW m (globN s "ev" + 8) = nsw.toNat := by
                        change memW s8 (globN s "ev" + 8) = nsw.toNat
                        rw [hs8_eq, memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + 8) _ (by omega) (by omega) (by omega),
                            hs7_eq, memW_updW_same s6 (globN s "ev" + 8) nsw]
                      have hm_e0_232 : memW m (globN s "ev" + 232) = ncapw.toNat := by
                        change memW s8 (globN s "ev" + 232) = ncapw.toNat
                        rw [hs8_eq, memW_updW_same s7 (globN s "ev" + 232) ncapw]
                      have hfresh_m : freshIvl.2 = 0 ∨
                          (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                            Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr")) := by
                        right; refine ⟨hnsw_al, by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_sp_glob]; exact ⟨le_refl _, le_of_eq hnsw_end⟩
                      have hnew_m :
                          (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                            memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                          (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl) := by
                        right; refine ⟨by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_e0_8, hm_e0_232]
                      have hm_loc_s4 : ∀ k, k ≠ ofString "ns" → k ≠ ofString "ncap" →
                          m.locals.lookup k = s4.locals.lookup k := by
                        intro k hk1 hk2
                        have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                            key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                          intro mp key q old hne
                          unfold HolFiniteMapExact.resVarEq
                          cases old with
                          | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                          | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                        have hs8_l : s8.locals = s5.locals := by
                          rw [hs8_eq, hs7_eq]; exact hs6_loc
                        dsimp only [m]
                        rw [hres_ne _ _ _ _ hk2.symm,
                            hres_ne _ _ _ _ hk1.symm,
                            hs8_l]
                        simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                      exact run_tail m freshIvl hAm hsc_m heff_m hfresh_m
                        (fun off hoff hoff8 h8 _ h232 => hm_e0_other off hoff hoff8 h8 h232)
                        hnew_m
                        (by rw [hm_e0_232]; omega)
                        (by rw [hm_e0_232]; exact hncap_le1024)
                        (by rw [hm_e0_other 16 (by omega) (by omega) (by omega) (by omega), ← hspw_eq])
                        (by rw [hm_loc_s4 (ofString "sp") (by decide) (by decide)]; exact hs4_sp)
                        (by rw [hm_loc_s4 (ofString "v") (by decide) (by decide)]; exact hs4_v)
      · -- NO-GROW BRANCH (`¬ capw ≤ spw`, so `spw < capw`!):
        have hsp_lt_cap : spw.toNat < capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        exact run_tail s2 (0, 0)
          ⟨guestInv_congr rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
          (le_refl _)
          ((ScratchByteEff.refl s _).with_locals_clock s2.locals s.clock)
          (Or.inl rfl)
          (fun _ _ _ _ _ _ => rfl)
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (by change spw.toNat < memW s (globN s "ev" + 232); rw [← hcapw_eq]; exact hsp_lt_cap)
          (by change memW s (globN s "ev" + 232) ≤ 1024; rw [← hcapw_eq]; exact hcap_le1024)
          (by change memW s (globN s "ev" + 16) = spw.toNat; exact hspw_eq.symm)
          hs2_sp hs2_v

/-! ## 4. Wrapper specs: `eps_stack_push_word` and `eps_stack_push_bool` -/

private theorem eps_seq_call_ret0 {fname : MlS}
    (hf : EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g) fname)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (hnt : (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1 ≠ some .timeOut) :
    let r := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1
    let post := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).2
    (∀ v, r = some (.returned v) →
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
      (∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)) ∧
    (IsEvmErr r →
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
  dsimp only
  obtain ⟨params, body, retShape, hlk, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body s.code.lookup fname params body body' retShape ret' vals callee
            (by rw [hcode]; exact hlk) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup fname vals body callee ret' hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, retShape) := by
          rwa [← hcode]
        have hInv_ce : EvmInv (callEntryStateHOLFinite s callee) := localsFree_evmInv s callee (s.clock - 1) hInv
        have hc_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        have hQ (hsafe : res ≠ some .timeOut) :=
          hspec (callEntryStateHOLFinite s callee) hcode hInv_ce trivial ⟨vals, hl_orig⟩ (by rw [hrun]; exact hsafe)
        cases res with
        | none => exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned vr =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact vr) retShape = true
            · simp only [hsh, ↓reduceIte]
              have hs := hQ (by simp); dsimp only at hs; rw [hrun] at hs
              obtain ⟨hInv_cp, hch_cp, hR_cp, hg_cp⟩ := hs.1 vr rfl
              rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
              have hsz0 : sizeOfShapeWithContextHOL cpost.structs
                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rw [if_pos hsz0]; dsimp only
              let post := ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).emptyLocalsHOLFinite
              have hInv_p : EvmInv post := localsFree_evmInv cpost post.locals cpost.clock hInv_cp
              have hc_p := evm_congr (s := cpost) (t := post) rfl rfl
              constructor
              · intro _ _
                exact ⟨hInv_p, (evmChain_congr rfl rfl).trans (hch_cp.trans (evmChain_congr rfl rfl)),
                  by rw [hc_p.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp,
                  fun g hg => hg_cp g hg⟩
              · rintro ⟨_, h⟩; cases h
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              have hs := hQ (by simp); dsimp only at hs; rw [hrun] at hs
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := hs.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              constructor
              · intro _ h; cases h
              · intro _
                exact ⟨hInv_el, (evmChain_congr rfl rfl).trans (hch_cp.trans (evmChain_congr rfl rfl)),
                  by rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp⟩
            · constructor
              · intro _ h; cases h
              · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | _ => exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩

theorem lookup_stack_push_word :
    originalRuntimeCode.lookup (ofString "stack_push_word") =
      some ([(ofString "w", .one)], sourceFnBody Guest.Software.guestFn_stack_push_word, .one) :=
  lookup_of_guestAst_getElem 455 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push_word) rfl

theorem eps_stack_push_word :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_word") := by
  refine ⟨_, _, _, lookup_stack_push_word, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_word =
      .seq
        (.call (some (none, none)) (ofString "stack_push")
          [.rStruct [.var .local (ofString "w"), .const 0#64, .const 0#64, .const 0#64]])
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt

theorem lookup_stack_push_bool :
    originalRuntimeCode.lookup (ofString "stack_push_bool") =
      some ([(ofString "b", .one)], sourceFnBody Guest.Software.guestFn_stack_push_bool, .one) :=
  lookup_of_guestAst_getElem 456 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_push_bool) rfl

theorem eps_stack_push_bool :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => ∀ g : String, g ≠ "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_bool") := by
  refine ⟨_, _, _, lookup_stack_push_bool, ?_⟩
  intro F s hcode hInv _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_bool =
      .seq
        (.ite (.cmp .notEqual (.var .local (ofString "b")) (.const 0#64))
          (.call (some (none, none)) (ofString "stack_push")
            [.rStruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]])
          (.call (some (none, none)) (ofString "stack_push")
            [.rStruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]]))
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i cw _
    by_cases hcw0 : cw = 0
    · subst hcw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt
    · simp only [hcw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact eps_seq_call_ret0 eps_stack_push s _ hcode hInv hnt
  · intro _; exact ⟨fun _ h => by cases h, fun ⟨_, h⟩ => by cases h⟩

end InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA



