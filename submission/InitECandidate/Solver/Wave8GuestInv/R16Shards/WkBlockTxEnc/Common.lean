import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Exec
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M18.Common
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256

/-! Shared composable `HeapByteEff` & `WorldStep` infrastructure for `R16e-WkBlockTxEnc`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

abbrev CellHitsPos := R13Shards.Keccak256.CellHitsPos

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) :=
  R13Shards.Keccak256.not_resumes_error

theorem sourceBase_val : sourceBase = 2701131776 := rfl
theorem heapLimit_val : heapLimit = 2952790016 := rfl
theorem scratchStart_val : scratchStart = 2952790016 := rfl
theorem scratchEnd_val : scratchEnd = 2965299200 := rfl
theorem heapEnd_val : heapEnd = 33806089704 := by decide

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd :=
  R13Shards.Keccak256.ordinaryDomain_iff x

theorem global_heap_ptr_word {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" := by
  have hpos : 0 < globN s "heap_ptr" := by
    have := hA.1; rw [sourceBase_val] at this; omega
  unfold globN at hpos ⊢
  rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
  · simp [hg] at hpos
  · rcases gv with ⟨⟨hp⟩⟩ | _ | _
    · exact ⟨hp, rfl, by simp [hg]⟩
    · simp [hg] at hpos
    · simp [hg] at hpos

theorem arenaReady_update_heap_ptr {F : Type} {s post : PanSemStateFiniteExact 64 F} {q : BitVec 64}
    (hG : GuestInv post) (hA : ArenaOK s)
    (hg : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hq_lo : sourceBase ≤ q.toNat) (hq_hi : q.toNat ≤ heapLimit) (hq8 : q.toNat % 8 = 0) :
    ArenaReady post := by
  have hhp : globN post "heap_ptr" = q.toNat := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hfp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsWord_update (ofString "heap_ptr") q hg hA.2.2.2.2.2.2.2.2⟩
  · rw [hhp]; exact hq_lo
  · rw [hhp]; exact hq_hi
  · rw [hfp]; exact hA.2.2.1
  · rw [hfp, hsp]; exact hA.2.2.2.1
  · rw [hsp]; exact hA.2.2.2.2.1
  · rw [hhp]; exact hq8
  · rw [hfp]; exact hA.2.2.2.2.2.2.1
  · rw [hsp]; exact hA.2.2.2.2.2.2.2.1

theorem arenaReady_update_scratch_ptr {F : Type} {s post : PanSemStateFiniteExact 64 F} {q : BitVec 64}
    (hG : GuestInv post) (hA : ArenaOK s)
    (hg : post.globals = s.globals.update (ofString "scratch_ptr", .val (.word q)))
    (hq_lo : globN s "frame_mem_ptr" ≤ q.toNat) (hq_hi : q.toNat ≤ scratchEnd) (hq8 : q.toNat % 8 = 0) :
    ArenaReady post := by
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide]
  have hfp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "scratch_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN post "scratch_ptr" = q.toNat := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    globalsWord_update (ofString "scratch_ptr") q hg hA.2.2.2.2.2.2.2.2⟩
  · rw [hhp]; exact hA.1
  · rw [hhp]; exact hA.2.1
  · rw [hfp]; exact hA.2.2.1
  · rw [hfp, hsp]; exact hq_lo
  · rw [hsp]; exact hq_hi
  · rw [hhp]; exact hA.2.2.2.2.2.1
  · rw [hfp]; exact hA.2.2.2.2.2.2.1
  · rw [hsp]; exact hq8

/-! ## 1. `HeapByteEff` relation & combinators -/

structure HeapByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (Rl : List Ivl) (gw : List String) : Prop where
  arena      : ArenaReady post
  hp_le      : globN s "heap_ptr" ≤ globN post "heap_ptr"
  fp_eq      : globN post "frame_mem_ptr" = globN s "frame_mem_ptr"
  sp_le      : globN post "scratch_ptr" ≤ globN s "scratch_ptr"
  be         : post.be = s.be
  globals    : GlobalsKept gw s post
  out_dom    : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, post.memory a ≠ s.memory a →
                 (∃ i ∈ Rl, CellHitsPos a.toNat i) ∨
                 CellHitsPos a.toNat (freeGap s) ∨
                 CellHitsPos a.toNat (heapFree s)
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b →
                 (∃ i ∈ Rl, InIvl b i) ∨
                 InIvl b (freeGap s) ∨
                 InIvl b (heapFree s)

theorem HeapByteEff.refl {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s) (Rl : List Ivl) (gw : List String) :
    HeapByteEff s s Rl gw :=
  ⟨hAR, le_rfl, rfl, le_rfl, rfl, fun _ _ => rfl,
   fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

theorem HeapByteEff.locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h : HeapByteEff s post Rl gw) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    HeapByteEff s { post with locals := L, clock := k } Rl gw :=
  ⟨localsFree_arenaReady post L k h.arena, h.hp_le, h.fp_eq, h.sp_le, h.be, h.globals,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem HeapByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (h1 : HeapByteEff a b Rl gw) (h2 : HeapByteEff b c Rl gw) :
    HeapByteEff a c Rl gw := by
  have hfg_sub : ∀ x, CellHitsPos x (freeGap b) → CellHitsPos x (freeGap a) := by
    rintro x ⟨hpos, hc1, hc2⟩
    unfold freeGap at hpos hc1 hc2 ⊢
    rw [h1.fp_eq] at hpos hc1 hc2
    have := h1.sp_le
    exact ⟨by dsimp only at *; omega, by dsimp only at *; omega, by dsimp only at *; omega⟩
  have hfg_in : ∀ x, InIvl x (freeGap b) → InIvl x (freeGap a) := by
    rintro x ⟨hx1, hx2⟩
    unfold freeGap at hx1 hx2 ⊢
    rw [h1.fp_eq] at hx1 hx2
    have := h1.sp_le
    exact ⟨by dsimp only at *; omega, by dsimp only at *; omega⟩
  have hhf_sub : ∀ x, CellHitsPos x (heapFree b) → CellHitsPos x (heapFree a) := by
    rintro x ⟨hpos, hc1, hc2⟩
    unfold heapFree at hpos hc1 hc2 ⊢
    have := h1.hp_le
    exact ⟨by dsimp only at *; omega, by dsimp only at *; omega, by dsimp only at *; omega⟩
  have hhf_in : ∀ x, InIvl x (heapFree b) → InIvl x (heapFree a) := by
    rintro x ⟨hx1, hx2⟩
    unfold heapFree at hx1 hx2 ⊢
    have := h1.hp_le
    exact ⟨by dsimp only at *; omega, by dsimp only at *; omega⟩
  refine ⟨h2.arena, le_trans h1.hp_le h2.hp_le, h2.fp_eq.trans h1.fp_eq,
    le_trans h2.sp_le h1.sp_le, h2.be.trans h1.be,
    fun k hk => (h1.globals k hk).trans (h2.globals k hk), ?_, ?_, ?_⟩
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.out_dom x hne
    · rw [h1.arena.1.memaddrs.symm]; rw [← h2.arena.1.memaddrs]
      have hmb : b.memaddrs x := h2.out_dom x hcb
      rwa [h2.arena.1.memaddrs]
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.cell_frame x hne
    · rcases h2.cell_frame x hcb with hr | hfg | hhf
      · exact Or.inl hr
      · exact Or.inr (Or.inl (hfg_sub _ hfg))
      · exact Or.inr (Or.inr (hhf_sub _ hhf))
  · intro x hx hne
    by_cases hcb : memB c x = memB b x
    · rw [hcb] at hne; exact h1.byte_frame x hx hne
    · rcases h2.byte_frame x hx hcb with hr | hfg | hhf
      · exact Or.inl hr
      · exact Or.inr (Or.inl (hfg_in _ hfg))
      · exact Or.inr (Or.inr (hhf_in _ hhf))

theorem HeapByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R1 R2 : List Ivl} {gw1 gw2 : List String}
    (h : HeapByteEff s post R1 gw1)
    (hR : ∀ i ∈ R1, 0 < i.2 →
      (∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "frame_mem_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ globN s "scratch_ptr") ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit))
    (hgw : ∀ g ∈ gw1, g ∈ gw2) :
    HeapByteEff s post R2 gw2 := by
  refine ⟨h.arena, h.hp_le, h.fp_eq, h.sp_le, h.be, ?_, h.out_dom, ?_, ?_⟩
  · intro k hk
    apply h.globals k
    intro hm
    obtain ⟨nm, hnm, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨nm, hgw nm hnm, rfl⟩)
  · intro a hne
    rcases h.cell_frame a hne with ⟨i, hi, hipos, hc1, hc2⟩ | hfg | hhf
    · rcases hR i hi hipos with ⟨j, hj, h1, h2⟩ | ⟨hf1, hf2⟩ | ⟨hh1, hh2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)
    · exact Or.inr (Or.inl hfg)
    · exact Or.inr (Or.inr hhf)
  · intro b hb hne
    rcases h.byte_frame b hb hne with ⟨i, hi, hb1, hb2⟩ | hfg | hhf
    · rcases hR i hi (by omega) with ⟨j, hj, h1, h2⟩ | ⟨hf1, hf2⟩ | ⟨hh1, hh2⟩
      · exact Or.inl ⟨j, hj, by omega, by omega⟩
      · exact Or.inr (Or.inl ⟨by dsimp [freeGap]; omega, by dsimp [freeGap]; omega⟩)
      · exact Or.inr (Or.inr ⟨by dsimp [heapFree]; omega, by dsimp [heapFree]; omega⟩)
    · exact Or.inr (Or.inl hfg)
    · exact Or.inr (Or.inr hhf)

theorem HeapByteEff.of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAR : ArenaReady s) (hlf : M13.LocFrame s post) (Rl : List Ivl) (gw : List String) :
    HeapByteEff s post Rl gw := by
  have hg := hlf.globals
  have hm := hlf.memory
  refine ⟨hlf.arenaReady hAR, by simp [globN, hg], by simp [globN, hg], by simp [globN, hg],
    hlf.be, fun _ _ => hg.symm,
    fun _ h => absurd hm h, fun _ h => absurd hm h, fun b _ h => absurd ?_ h⟩
  unfold memB; rw [hm, hlf.be]

theorem HeapByteEff.of_byteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : R13Shards.Keccak256.ByteEff s post Rl) :
    HeapByteEff s post Rl gw := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun _ _ => heff.globals.symm, heff.out_dom,
    fun a hne => Or.inl (heff.cell_frame a hne),
    fun b hb hne => Or.inl (heff.byte_frame b hb hne)⟩

theorem HeapByteEff.of_m13_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : M13.ByteRegionEffect s post Rl) :
    HeapByteEff s post Rl gw := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun _ _ => heff.globals.symm, ?_, ?_, ?_⟩
  · intro a hne; by_contra hna; exact hne (heff.out_dom a hna)
  · intro a hne; left
    by_contra hno
    apply hne; apply heff.cell_frame a
    intro i hi hch
    exact hno ⟨i, hi, by obtain ⟨_, _⟩ := hch; omega, hch⟩
  · intro b hb hne; left
    by_contra hno
    apply hne; apply heff.byte_frame b hb
    intro i hi hin; exact hno ⟨i, hi, hin⟩

theorem HeapByteEff.of_m11_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (heff : M11.ByteRegionEffect s post Rl) :
    HeapByteEff s post Rl gw := by
  have hG : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAR.1
  have hA : ArenaOK post := arenaOK_congr heff.globals hAR.2
  have hg_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  refine ⟨⟨hG, hA⟩, by rw [hg_eq], hg_eq _, by rw [hg_eq], heff.be,
    fun _ _ => heff.globals.symm, ?_, ?_, ?_⟩
  · intro a hne; by_contra hna; exact hne (heff.out_dom a hna)
  · intro a hne; left
    by_contra hno
    apply hne; apply heff.cell_frame a
    intro i hi hch
    exact hno ⟨i, hi, by obtain ⟨_, _⟩ := hch; omega, hch⟩
  · intro b hb hne; left
    by_contra hno
    apply hne; apply heff.byte_frame b hb
    intro i hi hin; exact hno ⟨i, hi, hin⟩

/-! ## 2. Master `HeapByteEff.to_worldStep` -/

theorem mem_eq_of_bytes_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hbe : post.be = s.be) (a : BitVec 64) (ha_dom : ordinaryDomain a)
    (hb : ∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) :
    post.memory a = s.memory a := by
  have ha_ord := (ordinaryDomain_iff a).1 ha_dom
  have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
  have hhe_8 : heapEnd % 8 = 0 := by rw [heapEnd_val]; decide
  have ha_hi : a.toNat + 8 ≤ 2 ^ 64 := by omega
  rcases hp_m : post.memory a with ⟨wp⟩
  rcases hs_m : s.memory a with ⟨ws⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  have hbyte_val : ∀ k : Nat, k < 8 →
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) wp s.be).toNat =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + k)) ws s.be).toNat := by
    intro k hk
    have hal_eq : panByteAlignHOL (BitVec.ofNat 64 (a.toNat + k)) = a := by
      apply BitVec.eq_of_toNat_eq
      rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hbk := hb k hk
    unfold memB at hbk
    rw [hal_eq, hp_m, hs_m, hbe] at hbk
    exact hbk
  have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
      w.toNat / 256 ^ idx % 256 =
      (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
    intro w idx _
    unfold panGetByteHOL
    change w.toNat / 256 ^ idx % 256 =
      (UInt8.ofNat (w.toNat / 256 ^ (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) % 256)).toNat
    have hexp : (if s.be then 8 - 1 - (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8
        else (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat % 8) = idx := by
      have hmod_lt : (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))).toNat =
          a.toNat + (if s.be then 7 - idx else idx) :=
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
      n = (n / 256 ^ 0 % 256) + (n / 256 ^ 1 % 256) * 256 ^ 1 +
          (n / 256 ^ 2 % 256) * 256 ^ 2 + (n / 256 ^ 3 % 256) * 256 ^ 3 +
          (n / 256 ^ 4 % 256) * 256 ^ 4 + (n / 256 ^ 5 % 256) * 256 ^ 5 +
          (n / 256 ^ 6 % 256) * 256 ^ 6 + (n / 256 ^ 7 % 256) * 256 ^ 7 := by
    intro n _; omega
  rw [hdecomp wp.toNat wp.isLt, hdecomp ws.toNat ws.isLt]
  rw [hpow_eq 0 (by omega), hpow_eq 1 (by omega), hpow_eq 2 (by omega), hpow_eq 3 (by omega),
      hpow_eq 4 (by omega), hpow_eq 5 (by omega), hpow_eq 6 (by omega), hpow_eq 7 (by omega)]

theorem allocated_not_in_free {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : i.2 = 0 ∨ Allocated s i) {b : Nat} (hb : InIvl b i) :
    ¬ InIvl b (freeGap s) ∧ ¬ InIvl b (heapFree s) := by
  have hsep : heapLimit = scratchStart := rfl
  obtain ⟨hb1, hb2⟩ := hb
  rcases hal with hi0 | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · omega
  · refine ⟨fun ⟨g1, _⟩ => ?_, fun ⟨f1, _⟩ => ?_⟩
    · dsimp [freeGap] at g1; have := hA.2.1; have := hA.2.2.1; omega
    · dsimp [heapFree] at f1; omega
  · refine ⟨fun ⟨_, g2⟩ => ?_, fun ⟨_, f2⟩ => ?_⟩
    · dsimp [freeGap] at g2; have := hA.2.2.2.1; omega
    · dsimp [heapFree] at f2; have := hA.1; have := hA.2.2.1; have := hA.2.2.2.1; omega

theorem HeapByteEff.to_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (B : List (String × Nat))
    (hB_ok : ∀ gs ∈ B, gs ∈ globalBuffers ∧ gs.1 ∉ typedRecords.map Prod.fst)
    (hgw_ok : ∀ g ∈ gw, g = "heap_ptr" ∨ g = "scratch_ptr")
    (hW : WorldOK s)
    (heff : HeapByteEff s post (R s ++ B.map (bufferRegion s)) gw)
    (hQ : ∀ S Nd, WorldTypedWith s S Nd → WorldTypedWith post S Nd →
      worldOwned post S Nd = worldOwned s S Nd → Q s r post S Nd) :
    WorldStep R gw M13.stdKeep Q s r post := by
  have hAs : ArenaReady s := hW.1
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hWT0⟩ := (worldTyped_iff_with s S0).1 hWT0_ex
  have hnonheap : ∀ name : String,
      ofString name ≠ ofString "heap_ptr" →
      ofString name ≠ ofString "scratch_ptr" →
      ofString name ≠ ofString "frame_mem_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name) := by
    intro name h1 h2 _
    apply heff.globals
    intro hm
    obtain ⟨g, hg, heq⟩ := List.mem_map.1 hm
    rcases hgw_ok g hg with rfl | rfl
    · exact h1 heq.symm
    · exact h2 heq.symm
  have hRK : RecordsKept R M13.stdKeep s post := by
    intro rec hrec hgnz k hk hnoR
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [M13.stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hkle⟩ := hsz_ex
    have hfix0 := M13.typedRec_in_fixedObjects s htr
    have hsz : (if globN s rec.1 = 0 then 0 else sz) = sz := if_neg hgnz
    rcases hWT0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, hw0⟩
    · dsimp only at h0; rw [hsz] at h0; omega
    · have hb := M13.allocated_le_2pow64 hAs.2 hal0
      dsimp only at hb; rw [hsz] at hb
      have ha64 : globN s rec.1 + k < 2 ^ 64 := by omega
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha64
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (globN s rec.1 + k))
      · rw [mem_eq_of_bytes_eq heff.be _ hdom]
        intro idx hidx
        rw [hbit]
        by_contra hne_b
        have hin_rec : InIvl (globN s rec.1 + k + idx) (globN s rec.1, sz) := ⟨by omega, by omega⟩
        have hal_rec : Allocated s (globN s rec.1, sz) := by
          simpa [hsz] using hal0
        have hnfree := allocated_not_in_free hAs.2 (Or.inr hal_rec) hin_rec
        rcases heff.byte_frame (globN s rec.1 + k + idx) (by omega) hne_b with ⟨x, hx, hbx⟩ | hfg | hhf
        · rcases List.mem_append.1 hx with hxR | hxB
          · exact hnoR x hxR ⟨by obtain ⟨_, _⟩ := hbx; omega, by obtain ⟨_, _⟩ := hbx; omega⟩
          · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hxB
            have hwti := M13.mem_worldTypedIvls_typedRec (s := s) (S := S0) (Nd := Nd0) htr
            rw [hsz] at hwti
            have hdj := bufferRegion_disj hWT0 gs (hB_ok gs hgs).1 (hB_ok gs hgs).2 _ hwti
            obtain ⟨_, _⟩ := hbx
            rcases hdj with d | d | d | d <;> (dsimp only at *; omega)
        · exact hnfree.1 hfg
        · exact hnfree.2 hhf
      · by_contra hne_w
        have hne_m : post.memory (BitVec.ofNat 64 (globN s rec.1 + k)) ≠
            s.memory (BitVec.ofNat 64 (globN s rec.1 + k)) := fun heq => hne_w (by rw [heq])
        exact hdom (hAs.1.memaddrs ▸ heff.out_dom _ hne_m)
  refine ⟨heff.arena, heff.hp_le, heff.globals, hRK, fun S Nd hWT hdisj => ?_⟩
  have hbyte_wti : ∀ b : Nat, b < 2 ^ 64 →
      (∃ i ∈ worldTypedIvls s S Nd, i.1 ≤ b ∧ b < i.1 + i.2) →
      memB post b = memB s b := by
    intro b hb ⟨i, hi, hb1, hb2⟩
    by_contra hne_b
    have hal_i := M13.worldTypedIvls_allocated hWT hi
    have hnfree := allocated_not_in_free hAs.2 hal_i ⟨hb1, hb2⟩
    rcases heff.byte_frame b hb hne_b with ⟨x, hx, hbx⟩ | hfg | hhf
    · rcases List.mem_append.1 hx with hxR | hxB
      · have hdj := hdisj x hxR i hi
        obtain ⟨_, _⟩ := hbx
        rcases hdj with d | d | d | d <;> omega
      · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hxB
        have hdj := bufferRegion_disj hWT gs (hB_ok gs hgs).1 (hB_ok gs hgs).2 i hi
        obtain ⟨_, _⟩ := hbx
        rcases hdj with d | d | d | d <;> omega
    · exact hnfree.1 hfg
    · exact hnfree.2 hhf
  have hcell : M13.SameTypedCells s post S Nd := by
    refine ⟨heff.be, heff.arena.1.memaddrs.trans hAs.1.memaddrs.symm, hAs.1.memaddrs, ?_, ?_, hbyte_wti⟩
    · intro a hna
      by_contra hne
      exact hna (hAs.1.memaddrs ▸ heff.out_dom a hne)
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply mem_eq_of_bytes_eq heff.be _ hdom
        intro k hk
        rw [hbit]
        exact hbyte_wti (a + k) (by omega) ⟨i, hi, by omega, by omega⟩
      · by_contra hne
        exact hdom (hAs.1.memaddrs ▸ heff.out_dom _ hne)
  have hfeq := M13.fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name h1 h2 h3 => (hnonheap name h1 h2 h3).symm)
  have hFT_post := M13.fixedTyped_of_eq heff.arena hWT.2.2.1 heff.hp_le heff.sp_le hfeq
  have hcore_eq : ∀ g ∈ M13.coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" ∧ ofString g ≠ ofString "scratch_ptr" ∧
        ofString g ≠ ofString "frame_mem_ptr" := by revert g hg; decide
    exact (M13.globN_eq_of_lookup_eq (hnonheap g hne.1 hne.2.1 hne.2.2)).symm
  obtain ⟨hWT_post, hOG⟩ := M13.worldTypedWith_congr_w1 hAs heff.arena heff.hp_le heff.sp_le
    hcore_eq hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hwo_eq : worldOwned post S Nd = worldOwned s S Nd := by
    unfold worldOwned
    rw [hfeq, M13.nodeExtents_eq hWT.2.2.2.1 hcell]
    congr 2
    apply List.flatMap_congr
    intro t ht
    exact M13.htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  refine ⟨S, Nd, fun _ ht => ht, hWT_post, hOG, ?_, hQ S Nd hWT hWT_post hwo_eq⟩
  intro a hkeep hhf
  by_contra hne
  rcases heff.cell_frame a hne with ⟨x, hx, _, hhit⟩ | ⟨_, hfg⟩ | ⟨_, hchf⟩
  · rcases List.mem_append.1 hx with hxR | hxB
    · exact hkeep x (List.mem_append_left [freeGap s] (List.mem_append_right _ hxR)) hhit
    · obtain ⟨gs, hgs, rfl⟩ := List.mem_map.1 hxB
      have hfo : bufferRegion s gs ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨gs, (hB_ok gs hgs).1, rfl⟩
      have hwo : bufferRegion s gs ∈ worldOwned s S Nd := by
        unfold worldOwned; exact List.mem_append_left _ (List.mem_append_right _ hfo)
      exact hkeep _ (List.mem_append_left [freeGap s] (List.mem_append_left _ hwo)) hhit
  · exact hkeep (freeGap s) (List.mem_append_right _ List.mem_cons_self) hfg
  · exact hhf hchf

/-! ## 3. `heap_mark`, `heap_release`, `alloc`, and `trap_with` combinators -/

theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_heap_mark :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_heap_release :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

theorem evaluate_call_trap_with_no_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    ¬ Resumes (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 := by
  have hs := Wave8Contracts.M18.call_trap_with_trapped state [.const codeVal] hcode
  rcases hrun : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal]) with ⟨r, st⟩
  rw [hrun] at hs
  rcases hs with _ | ⟨_, _, _, hnr⟩
  · rw [evaluateHOLFiniteState_call] at hrun
    have hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) [.const codeVal] =
        some [.val (.word codeVal)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
    have hlk := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
      (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
    rw [hargs] at hrun; dsimp only at hrun; rw [hlk] at hrun; dsimp only at hrun
    split at hrun
    · injection hrun with hr _; subst hr; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · have hout := evaluate_trap_with_body_outcomes
        (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
        (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨rb, sb⟩
      rw [hb] at hout hrun
      cases rb with
      | none => exact absurd rfl hout.1
      | some r' =>
        cases r' with
        | returned rv => exact absurd rfl (hout.2.1 rv)
        | exception eid ev =>
          dsimp only at hrun
          injection hrun with hr _; subst hr
          rintro (⟨_, h⟩ | ⟨e, w, h, hne⟩)
          · simp at h
          · injection h with h'; injection h' with he hw; subst he hw
            exact hout.2.2 eid ev hne rfl
        | _ =>
          dsimp only at hrun; injection hrun with hr _; subst hr
          rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  · exact hnr

theorem evaluate_alloc_body_resumes {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hres : Resumes (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ rv, (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned rv) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hres ⊢; rw [hp_eval] at hres ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hres ⊢; rw [if_pos hsh_p] at hres ⊢; dsimp only at hres ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hres
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_res := evaluate_call_trap_with_no_resumes pState 1 hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_res hres
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact False.elim (hno_res hres)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hres ⊢; dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_dec_total] at hres ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hres ⊢; rw [hq_eval] at hres ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hres ⊢; rw [if_pos hsh_q] at hres ⊢; dsimp only at hres ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hres
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_res := evaluate_call_trap_with_no_resumes qState 1 hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_res hres
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact False.elim (hno_res hres)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]; dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLFinite,
          lookupKvarHOLFinite, hp_g, shapeOfHOLExact, shapeEqHOL,
          setKvarHOLFinite, setGlobalHOLFinite, evaluateHOLFiniteState_return]
      rw [heval_end]
      exact ⟨.val (.word p), rfl⟩

/-- `decCall lname .one "alloc" [nExp] cont` under `Resumes`: extracts `n : BitVec 64`,
advances `heap_ptr` from `hp` to `q = round8(hp + n) ≤ heapLimit`, and steps to `mid`
with `HeapByteEff s mid Rl gw` (whenever `"heap_ptr" ∈ gw`). -/
theorem eval_decCall_alloc_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (nExp : ExpHOL 64)
    (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)).1) :
    ∃ (hp n q : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
        some (.val (.word n)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      hp.toNat % 8 = 0 ∧
      q.toNat = (hp.toNat + n.toNat + 7) / 8 * 8 ∧
      hp.toNat + n.toNat ≤ q.toNat ∧
      q.toNat ≤ heapLimit ∧
      q.toNat % 8 = 0 ∧
      globN mid "heap_ptr" = q.toNat ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hp)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "alloc") [nExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  obtain ⟨hp, hhp, hhp_nat⟩ := global_heap_ptr_word s hAR.2
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hnv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp with _ | nv
  · simp [evalListHOLFinite, evalListHOLExact, hnv] at hres
    exact False.elim (not_resumes_error hres)
  · have hnw_ex : ∃ nw : BitVec 64, nv = .val (.word nw) := by
      rcases nv with ⟨⟨nw⟩⟩ | fields | ⟨nm, fields⟩
      · exact ⟨nw, rfl⟩
      · have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
            some [.rStruct fields] := by simp [evalListHOLFinite, evalListHOLExact, hnv]
        have hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.rStruct fields] = none := by
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
          · rfl
          · rename_i hraw; rw [hcode] at hraw
            simp [lookupCodeHOLExact, lookup_alloc, shapeOfHOLExact, shapeEqHOL] at hraw
        rw [ha] at hres; dsimp only at hres; rw [hlk] at hres
        exact False.elim (not_resumes_error hres)
      · have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
            some [.nStruct nm fields] := by simp [evalListHOLFinite, evalListHOLExact, hnv]
        have hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.nStruct nm fields] = none := by
          unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
          · rfl
          · rename_i hraw; rw [hcode] at hraw
            simp [lookupCodeHOLExact, lookup_alloc, shapeOfHOLExact, shapeEqHOL] at hraw
        rw [ha] at hres; dsimp only at hres; rw [hlk] at hres
        exact False.elim (not_resumes_error hres)
    obtain ⟨n, rfl⟩ := hnw_ex
    have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [nExp] =
        some [.val (.word n)] := by simp [evalListHOLFinite, evalListHOLExact, hnv]
    have hlk := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) n (by rw [hcode]; exact lookup_alloc)
    simp only [ha, hlk] at hnt hres ⊢
    by_cases hcz : s.clock = 0
    · simp [hcz] at hnt
    · simp only [hcz, ↓reduceIte] at hnt hres ⊢
      let cmap := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word n))
      let ent := callEntryStateHOLFinite s cmap
      have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rcases hal : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
      have hres_ent : Resumes ra := by
        cases ra with
        | none => simp [ent, cmap, hal] at hres; exact False.elim (not_resumes_error hres)
        | some r =>
          cases r with
          | returned rv => exact Or.inl ⟨rv, rfl⟩
          | exception eid ev =>
            simp only [ent, cmap, hal] at hres
            rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
            · simp at h
            · injection h with h'; injection h' with he1 he2; subst he1 he2
              exact Or.inr ⟨eid, ev, rfl, hne⟩
          | timeOut => simp [ent, cmap, hal] at hnt
          | finalFfi _ =>
            simp only [ent, cmap, hal] at hres
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | _ => simp [ent, cmap, hal] at hres; exact False.elim (not_resumes_error hres)
      obtain ⟨rv, hrv⟩ := evaluate_alloc_body_resumes ent hp n hcode hhp hent_n (by rw [hal]; exact hres_ent)
      have hp_le_cmax : hp.toNat ≤ cMax.toNat := by
        have : cMax.toNat = heapLimit := rfl
        rw [this, hhp_nat]; exact hAR.2.2.1
      have hgen := M13.evaluate_alloc_body_general ent hp n hcode hp_le_cmax hhp hent_n rv hrv
      rw [hal] at hrv hgen
      dsimp only at hgen
      obtain ⟨rfl, hg_sa, hm_sa, hpq, hqc, hq8⟩ := hgen
      have hra : ra = some (.returned (.val (.word hp))) := hrv
      subst hra
      set q : BitVec 64 := (hp + (n + 7)) &&& ((0 : BitVec 64) - 8)
      have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
          shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      change (let bodyOutput := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc); _) = _
      change (let bodyOutput := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc); _).1 ≠ _ at hnt
      change Resumes (let bodyOutput := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_alloc); _).1 at hres
      rw [hal] at hnt hres ⊢
      dsimp only at hnt hres ⊢
      rw [if_pos hsh] at hnt hres ⊢
      let mid := setVarHOLFinite (ofString lname) (.val (.word hp)) { sa with locals := s.locals }
      have hgb := M13.evaluateHOLFiniteState_guestInv_be ent (sourceFnBody Guest.Software.guestFn_alloc)
        (guestInv_callEntry s cmap hAR.1)
      rw [hal] at hgb
      have hG_mid : GuestInv mid :=
        guestInv_setVar _ _ _ (guestInv_with_locals_clock sa s.locals sa.clock hgb.1)
      have hq_hi : q.toNat ≤ heapLimit := hqc
      have hq_lo : sourceBase ≤ q.toNat := by
        have := hAR.2.1; rw [← hhp_nat] at this; omega
      have hAR_mid : ArenaReady mid :=
        arenaReady_update_heap_ptr hG_mid hAR.2 hg_sa hq_lo hq_hi hq8
      have hq_nat : q.toNat = (hp.toNat + n.toNat + 7) / 8 * 8 := by
        have hhl264 : heapLimit < 2 ^ 64 := by decide
        have hn_lt : hp.toNat + n.toNat + 7 < 2 ^ 64 := by omega
        have h1 : (n + 7).toNat = n.toNat + 7 := by
          rw [BitVec.toNat_add]; change (n.toNat + 7) % 2 ^ 64 = _; exact Nat.mod_eq_of_lt (by omega)
        have h2 : (hp + (n + 7)).toNat = hp.toNat + n.toNat + 7 := by
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt hn_lt]
        have h3 := and_neg8_toNat (hp + (n + 7))
        change q.toNat = _ at h3
        rw [h3, h2]
      have hmid_hp : globN mid "heap_ptr" = q.toNat := by
        change globN sa "heap_ptr" = q.toNat
        unfold globN; rw [hg_sa]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_fp : globN mid "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        change globN sa "frame_mem_ptr" = globN s "frame_mem_ptr"
        unfold globN; rw [hg_sa]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
      have hmid_sp : globN mid "scratch_ptr" = globN s "scratch_ptr" := by
        change globN sa "scratch_ptr" = globN s "scratch_ptr"
        unfold globN; rw [hg_sa]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
      have heff_mid : HeapByteEff s mid Rl gw := by
        refine ⟨hAR_mid, by rw [← hhp_nat, hmid_hp]; omega, hmid_fp, by rw [hmid_sp], hgb.2, ?_,
          fun _ h => absurd hm_sa h, fun _ h => absurd hm_sa h,
          fun b _ h => absurd (by unfold memB; change _ = _; rw [hm_sa, hgb.2]) h⟩
        intro k hk
        have hne : k ≠ ofString "heap_ptr" := fun heq =>
          hk (List.mem_map.2 ⟨"heap_ptr", hgw, heq.symm⟩)
        change s.globals.lookup k = sa.globals.lookup k
        rw [hg_sa]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
      exact ⟨hp, n, q, mid, hnv, hhp_nat, by rw [hhp_nat]; exact hAR.2.2.2.2.2.1,
        hq_nat, hpq, hq_hi, hq8, hmid_hp, hg_sa, hm_sa, rfl, heff_mid, hnt, hres, rfl⟩

/-- `decCall lname .one "heap_mark" [] cont` binds `lname = hp` (`hp.toNat = globN s "heap_ptr"`). -/
theorem eval_decCall_heap_mark {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (cont : ProgHOL 64)
    (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)).1 ≠ some .timeOut) :
    ∃ (hp : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      mid.globals = s.globals ∧
      mid.memory = s.memory ∧
      mid.locals = s.locals.update (ofString lname, .val (.word hp)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "heap_mark") [] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  obtain ⟨hp, hhp, hhp_nat⟩ := global_heap_ptr_word s hAR.2
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  have hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "heap_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_heap_mark, HolFiniteMapExact.empty, .one) := by
    have hraw : lookupCodeHOLExact s.code.lookup (ofString "heap_mark") [] =
        some (sourceFnBody Guest.Software.guestFn_heap_mark, FEMPTY, .one) := by
      rw [hcode]; simp [lookupCodeHOLExact, lookup_heap_mark]; rfl
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite; split
    · rename_i hm; rw [hraw] at hm; simp at hm
    · rename_i b l r hf
      have hinj := Option.some.inj (hf.symm.trans hraw)
      obtain ⟨rfl, hr⟩ := Prod.mk.inj hinj
      obtain ⟨hl_eq, rfl⟩ := Prod.mk.inj hr
      subst hl_eq; rfl
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set ent := s.callEntryStateHOLFinite HolFiniteMapExact.empty
    have hm_eval : evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_heap_mark) =
        (some (.returned (.val (.word hp))), ent.emptyLocalsHOLFinite) := by
      have hb : sourceFnBody Guest.Software.guestFn_heap_mark =
          .return (.var .global (ofString "heap_ptr")) := rfl
      rw [hb, evaluateHOLFiniteState_return]
      have hev : @evalHOLExact 64 F _ ent.toExact
          (fun a => Classical.propDecidable (ent.memaddrs a)) (.var .global (ofString "heap_ptr")) =
          some (.val (.word hp)) := hhp
      rw [hev]; simp [shapeOfHOLExact]
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word hp) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [hm_eval] at hnt ⊢
    dsimp only at hnt ⊢
    rw [if_pos hsh] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word hp))
      { ent.emptyLocalsHOLFinite with locals := s.locals }
    have hlf : M13.LocFrame s mid := by cases s; rfl
    exact ⟨hp, mid, hhp, hhp_nat, rfl, rfl, rfl,
      HeapByteEff.of_locFrame hAR hlf Rl gw, hnt, rfl⟩

/-- `call (some (none, none)) "heap_release" [mExp]` sets `heap_ptr := mw` when `mw` is aligned and
`sourceBase ≤ mw.toNat ≤ heapLimit`, composing cleanly with a prior `HeapByteEff s0 s Rl gw`
whose initial `heap_ptr` is `≤ mw.toNat`! -/
theorem eval_call_heap_release {F : Type}
    {s0 : PanSemStateFiniteExact 64 F} (s : PanSemStateFiniteExact 64 F)
    (mExp : ExpHOL 64) (mw : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode)
    (heff0 : HeapByteEff s0 s Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hm_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) mExp =
      some (.val (.word mw)))
    (hm_lo : globN s0 "heap_ptr" ≤ mw.toNat)
    (hm_lo_sb : sourceBase ≤ mw.toNat)
    (hm_hi : mw.toNat ≤ heapLimit)
    (hm8 : mw.toNat % 8 = 0)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "heap_release") [mExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s (.call (some (none, none)) (ofString "heap_release") [mExp])
    out.1 = none ∧ out.2.locals = s.locals ∧
    out.2.globals = s.globals.update (ofString "heap_ptr", .val (.word mw)) ∧
    out.2.memory = s.memory ∧
    HeapByteEff s0 out.2 Rl gw := by
  intro out; dsimp only [out]
  obtain ⟨hp_cur, hhp_cur, _⟩ := global_heap_ptr_word s heff0.arena.2
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [mExp] =
      some [.val (.word mw)] := by simp [evalListHOLFinite, evalListHOLExact, hm_ev]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "heap_release") (ofString "m")
    (sourceFnBody Guest.Software.guestFn_heap_release) mw (by rw [hcode]; exact lookup_heap_release)
  simp only [ha, hlk] at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    let cmap := HolFiniteMapExact.empty.update (ofString "m", ValueHOL.val (.word mw))
    set ent := s.callEntryStateHOLFinite cmap
    have hent_m : ent.locals.lookup (ofString "m") = some (.val (.word mw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbody_eval : evaluateHOLFiniteState ent
        (sourceFnBody Guest.Software.guestFn_heap_release) =
        (some (.returned (.val (.word 0#64))),
          emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw)) ent)) := by
      have hb : sourceFnBody Guest.Software.guestFn_heap_release =
          .seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "m")))
            (.return (.const 0#64)) := rfl
      rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ ent.toExact
          (fun a => Classical.propDecidable (ent.memaddrs a)) (.var .local (ofString "m")) =
          some (.val (.word mw)) := hent_m
      have hg_ent : ent.globals.lookup (ofString "heap_ptr") = some (.val (.word hp_cur)) := hhp_cur
      rw [hev]
      dsimp only
      have hvalid : ent.isValidValueHOLFinite .global (ofString "heap_ptr") (.val (.word mw)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hg_ent, shapeOfHOLExact, shapeEqHOL]
      rw [hvalid]
      simp only [↓reduceIte, setKvarHOLFinite, setGlobalHOLFinite, evaluateHOLFiniteState_return]
      have hc0 : @evalHOLExact 64 F _
          (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw)) ent).toExact
          (fun a => Classical.propDecidable (ent.memaddrs a)) (.const 0#64) =
          some (.val (.word 0#64)) := rfl
      dsimp only [setGlobalHOLFinite] at hc0 ⊢
      rw [hc0]; simp [shapeOfHOLExact]
    have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word 0#64) : ValueHOL 64)) .one = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    rw [hbody_eval]
    dsimp only
    rw [if_pos hsh0]
    set post : PanSemStateFiniteExact 64 F :=
      { (emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mw)) ent)) with
        locals := s.locals }
    have hG_post : GuestInv post :=
      guestInv_congr (s := s) (t := post) rfl rfl rfl rfl heff0.arena.1
    have hg_post : post.globals = s.globals.update (ofString "heap_ptr", .val (.word mw)) := rfl
    have hAR_post : ArenaReady post :=
      arenaReady_update_heap_ptr hG_post heff0.arena.2 hg_post hm_lo_sb hm_hi hm8
    have hhp_post : globN post "heap_ptr" = mw.toNat := by
      unfold globN; rw [hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hfp_post : globN post "frame_mem_ptr" = globN s0 "frame_mem_ptr" := by
      have : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        unfold globN; rw [hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
      exact this.trans heff0.fp_eq
    have hsp_post : globN post "scratch_ptr" ≤ globN s0 "scratch_ptr" := by
      have : globN post "scratch_ptr" = globN s "scratch_ptr" := by
        unfold globN; rw [hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
      rw [this]; exact heff0.sp_le
    refine ⟨rfl, rfl, rfl, rfl, hAR_post, by rw [hhp_post]; exact hm_lo, hfp_post, hsp_post,
      heff0.be, ?_, heff0.out_dom, heff0.cell_frame, heff0.byte_frame⟩
    intro k hk
    have hne : k ≠ ofString "heap_ptr" := fun heq =>
      hk (List.mem_map.2 ⟨"heap_ptr", hgw, heq.symm⟩)
    rw [hg_post]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
    exact heff0.globals k hk

end InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
