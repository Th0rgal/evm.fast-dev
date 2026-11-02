import InitECandidate.Solver.Wave8GuestInv.R10Shards.EvmBase

/-! Byte/word region effects and R11 `EvmStep` / `FrameWF` / `frameLogObjects` / `MsgOwned` /
`MarksOK` preservation lemmas for EVM frame contracts. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas

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
open InitECandidate.Solver.Wave8GuestInv.EvmBase

/-! ## 1. `ByteRegionEffect` -/

structure ByteRegionEffect {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, i.2 ≠ 0 → ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

theorem ByteRegionEffect.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ByteRegionEffect.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : ByteRegionEffect s post Rl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteRegionEffect s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteRegionEffect.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteRegionEffect a b Rl) (h2 : ByteRegionEffect b c Rl) :
    ByteRegionEffect a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, h2.globals.trans h1.globals, ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx
    rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno
    rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

theorem ByteRegionEffect.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ByteRegionEffect s post R1)
    (hsub : ∀ i ∈ R1, i.2 = 0 ∨ ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteRegionEffect s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.out_dom, ?_, ?_⟩
  · intro a ha
    apply h.cell_frame a
    intro i hi hi0 ⟨hc1, hc2⟩
    rcases hsub i hi with h0 | ⟨j, hj, h1, h2⟩
    · exact hi0 h0
    · exact ha j hj (by omega) ⟨by omega, by omega⟩
  · intro b hb hno
    apply h.byte_frame b hb
    intro i hi ⟨hb1, hb2⟩
    rcases hsub i hi with h0 | ⟨j, hj, h1, h2⟩
    · rw [h0] at hb2; omega
    · exact hno j hj ⟨by omega, by omega⟩

private theorem pow_div_low (x y z K J : Nat) (_hy : y < 256) (_hz : z < 2 ^ K) (hJK : J + 8 ≤ K) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
  have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
  have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
    have hk_eq : K = (K - J - 8) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
    have hk_eq : K + 8 = (K - J) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
      z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
    rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
    omega
  rw [h1, Nat.add_mul_div_right _ _ hpJ]
  omega

private theorem pow_div_high (x y z K J : Nat) (_hy : y < 256) (_hz : z < 2 ^ K) (hKJ : K + 8 ≤ J) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
      (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
  have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
    have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
    have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
      rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
    omega
  have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
    have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
    conv_lhs => rw [hj_eq]
    rw [Nat.pow_add]
  have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
  have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
  rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
    Nat.mul_div_cancel _ hpK8]

theorem panGetByte_panSetByte_ne (addr' addr : BitVec 64) (b : UInt8) (cell : BitVec 64) (be : Bool)
    (hal : panByteAlignHOL addr' = panByteAlignHOL addr) (hne : addr' ≠ addr) :
    panGetByteHOL addr' (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be) be =
      panGetByteHOL addr' cell be := by
  have hb8 : b.toNat < 256 := b.toNat_lt_size
  have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
  have h256_pow : ∀ a : BitVec 64,
      (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
    intro a
    rw [pow256_eq_two_pow_mul]
    cases be <;> simp [byteBitIndex]
  have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
    intro hmeq
    apply hne
    apply BitVec.eq_of_toNat_eq
    have ha1 := panByteAlign_toNat64 addr'
    have ha2 := panByteAlign_toNat64 addr
    rw [hal] at ha1
    omega
  have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
      byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
    have hm1 : addr'.toNat % 8 < 8 := by omega
    have hm2 : addr.toNat % 8 < 8 := by omega
    cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
  simp only [panGetByteHOL]
  apply congrArg UInt8.ofNat
  change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
    cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
  rw [hset_nat, h256_pow addr']
  rcases hidx_sep with hlow | hhigh
  · rw [pow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
    have hc_eq : 2 ^ byteBitIndex addr be =
        (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hk_eq : byteBitIndex addr be =
          (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
      conv_lhs => rw [hk_eq]
      rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
    have hcell_eq : cell.toNat =
        cell.toNat % 2 ^ byteBitIndex addr be +
        (((cell.toNat / 2 ^ byteBitIndex addr be) *
          2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
      rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
      have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
          (((cell.toNat / 2 ^ byteBitIndex addr be) *
            2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
            2 ^ byteBitIndex addr' be := by
        rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [hmul] at hdm
      omega
    conv_rhs => rw [hcell_eq]
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    omega
  · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh]
    have hdJ : 2 ^ byteBitIndex addr' be =
        2 ^ (byteBitIndex addr be + 8) * 2 ^ (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by
      have hj_eq : byteBitIndex addr' be =
          (byteBitIndex addr be + 8) + (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by omega
      conv_lhs => rw [hj_eq]
      rw [Nat.pow_add]
    have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
    rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]

theorem ByteRegionEffect.of_storeByte {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hrun : evaluateHOLFiniteState s (.storeByte dst val) = (none, post))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat < i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_storeByte] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | vv
      · simp
      · rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only
          split
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            rcases hm : s.memory (panByteAlignHOL addr) with ⟨cell⟩
            have hm' : (s.6 (panByteAlignHOL addr)).1 = cell := by
              change (s.memory (panByteAlignHOL addr)).1 = cell; rw [hm]
            dsimp only at hst
            rw [hm'] at hst
            split at hst
            · rename_i hdom
              injection hst with hm'
              subst hm'
              intro hrun
              injection hrun with _ hpost
              subst hpost
              obtain ⟨i, hi, h1, h2⟩ := hin addr hdst hdom
              have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
              refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
              · intro a hna
                dsimp only
                have hne : a ≠ panByteAlignHOL addr := by rintro rfl; exact hna hdom
                rw [if_neg hne]
              · intro a hna
                dsimp only
                have hne : a ≠ panByteAlignHOL addr := by
                  rintro rfl
                  exact hna i hi (by omega) ⟨by rw [hal]; omega, by rw [hal]; omega⟩
                rw [if_neg hne]
              · intro b hb hno
                unfold memB
                dsimp only
                by_cases hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = panByteAlignHOL addr
                · rw [if_pos hal_eq]
                  have hm_rhs : (s.6 (panByteAlignHOL (BitVec.ofNat 64 b))).1 = cell := by
                    rw [hal_eq]; exact hm'
                  rw [hm_rhs]
                  dsimp only
                  have hne : BitVec.ofNat 64 b ≠ addr := by
                    intro heq
                    have hbt : (BitVec.ofNat 64 b).toNat = b := Nat.mod_eq_of_lt hb
                    rw [heq] at hbt
                    subst hbt
                    exact hno i hi ⟨h1, h2⟩
                  let byte8 : UInt8 := UInt8.ofNat (BitVec.ofNat 8 v.toNat).toNat
                  have hbyte8 : byte8.toNat = (BitVec.ofNat 8 v.toNat).toNat := by
                    have hlt : (BitVec.ofNat 8 v.toNat).toNat < 256 := (BitVec.ofNat 8 v.toNat).isLt
                    simp [byte8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
                  rw [← hbyte8, panGetByte_panSetByte_ne _ _ byte8 cell s.be hal_eq hne]
                · rw [if_neg hal_eq]
            · cases hst
          · simp
        · simp
        · simp
    · simp
    · simp

theorem ByteRegionEffect.of_store_word {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval_word : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) :
    ByteRegionEffect s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with
    _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with
        _ | v
      · simp
      · obtain ⟨w, rfl⟩ := hval_word v hv
        dsimp only
        split
        · rename_i m' hst
          unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
          by_cases hdom : s.memaddrs addr
          · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
            subst hst
            intro hrun
            injection hrun with _ hpost
            subst hpost
            obtain ⟨i, hi, h1, h2⟩ := hin addr hdst hdom
            have ha8 : addr.toNat % 8 = 0 := by
              have hdom' := hma_ord ▸ hdom
              rw [ordinaryDomain_iff] at hdom'; exact hdom'.2.2
            refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
            · intro a hna
              dsimp only
              have hne : a ≠ addr := by rintro rfl; exact hna hdom
              rw [if_neg hne]
            · intro a hna
              dsimp only
              have hne : a ≠ addr := by
                rintro rfl
                exact hna i hi (by omega) ⟨by omega, by omega⟩
              rw [if_neg hne]
            · intro b hb hno
              unfold memB
              dsimp only
              have hne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
                intro heq
                have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                  rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
                rw [heq] at hal_b
                exact hno i hi ⟨by omega, by omega⟩
              rw [if_neg hne]
          · simp [hdom] at hst
        · simp
    · simp
    · simp

/-! ## 2. Frame-object bounds, `frameLogObjects`, `LogsListOK`, `MsgOwned` under R11 -/

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
  obtain ⟨hscr, hmem_in, _, _, _, _, _, _, _, _, hlogs_cap1, _, hlogs_in, _, hret_in, hlogs_ok, _⟩ := hFW
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
    obtain ⟨idx, hidx, hmem_lo⟩ := List.mem_flatMap.1 holog
    rw [List.mem_range] at hidx
    have hmem_rec : o ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
      (List.mem_filter.1 hmem_lo).1
    rcases hlogs_ok with hz88 | ⟨_, _, _, _, hentry⟩
    · exfalso
      have hs0 := he88.1
      rw [hz88] at hs0
      have hsc := hA.2.2.1; have hgap := hA.2.2.2.1
      rw [scratchStart_val] at hsc; dsimp only at hs0; omega
    · obtain ⟨_, _, hl40, _, _, hl20, hltop, hldat⟩ := hentry idx hidx
      unfold logRecordIvls at hmem_rec
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_rec
      rcases hmem_rec with rfl | rfl | rfl | rfl
      · exact Or.inr (le_trans hl40.2 hhp_le)
      · exact Or.inr (le_trans hl20.2 hhp_le)
      · exact Or.inr (le_trans hltop.2 hhp_le)
      · exact Or.inr (le_trans hldat.2 hhp_le)

theorem memW_eq_of_frameDisj {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (heff : ByteRegionEffect s post Rl)
    {base sz k : Nat} (hbnd : base + sz ≤ 2 ^ 64) (hk : k + 8 ≤ sz)
    (hdj : ∀ x ∈ Rl, Disj x (base, sz)) :
    memW post (base + k) = memW s (base + k) := by
  unfold memW
  have ha : base + k < 2 ^ 64 := by omega
  have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
  rw [heff.cell_frame (BitVec.ofNat 64 (base + k)) (fun x hx hx0 => by
    rw [hbit]
    exact not_cellHits_of_disj_aligned hx0 (i := (base, sz)) (by dsimp only; omega)
      (by dsimp only; omega) (Disj.flip (hdj x hx)))]

/-- Under `FrameWF s S ec` and `ByteRegionEffect s post Rl` avoiding every nonzero interval of
`frameObjects s ec` (except possibly fields of `(ec.1, 280)` outside offset `88` and `112`) and
avoiding `(globN s "vm_system_address", if globN s "vm_system_address" = 0 then 0 else 24)`,
`frameLogObjects post ec = frameLogObjects s ec` and `LogsListOK post (memW post (ec.1 + 88))` holds! -/
theorem frameLogObjects_and_logsOK_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {S : List Nat} {ec : Ivl}
    (hA : ArenaOK s) (hFW : FrameWF s S ec)
    (heff : ByteRegionEffect s post Rl)
    (he88_eq : memW post (ec.1 + 88) = memW s (ec.1 + 88))
    (h88_eq : ∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hdj_logs : frameLogs s ec = (0, 0) ∨ (frameLogs s ec).2 = 0 ∨ ∀ x ∈ Rl, Disj x (frameLogs s ec))
    (hdj_logObjs : ∀ o ∈ frameLogObjects s ec, o.2 ≠ 0 → ∀ x ∈ Rl, Disj x o) :
    frameLogObjects post ec = frameLogObjects s ec ∧
    LogsListOK post (memW post (ec.1 + 88)) := by
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hse : scratchEnd ≤ 2 ^ 64 := by rw [scratchEnd_val]; norm_num
  have hhl : heapLimit ≤ 2 ^ 64 := by rw [heapLimit_val]; norm_num
  have hhp_le : globN s "heap_ptr" ≤ 2 ^ 64 := le_trans hA.2.1 hhl
  obtain ⟨hscr, _, _, _, _, _, _, _, _, _, hlogs_cap1, hlogs_len_le, hlogs_in, _, _, hlogs_ok, _⟩ := hFW
  have he88_scr := (hscr (memW s (ec.1 + 88), 24) (by simp)).1
  have h88_nz : memW s (ec.1 + 88) ≠ 0 := by
    intro hz; rw [hz] at he88_scr
    have hsc := hA.2.2.1; have hgap := hA.2.2.2.1
    rw [scratchStart_val] at hsc; unfold Inside at he88_scr; dsimp only at he88_scr; omega
  rcases hlogs_ok with hz | ⟨hw24, hal24, hlen28, hlen_cap, hentries⟩
  · exact absurd hz h88_nz
  have hlogs_bnd : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
    rcases hlogs_in with h | h
    · exact le_trans h.2 hhp_le
    · exact le_trans h.2 hse
  -- Each live entry pointer `memW s (memW s logs + 8 * idx)` for `idx < memW s (logs + 8)` is unchanged:
  have hptr_eq : ∀ idx, idx < memW s (memW s (ec.1 + 88) + 8) →
      memW post (memW s (memW s (ec.1 + 88)) + 8 * idx) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * idx) := by
    intro idx hidx
    have hsz_pos : 8 * idx + 8 ≤ (frameLogs s ec).2 := by
      unfold frameLogs; dsimp only; omega
    have hdj_fl : ∀ x ∈ Rl, Disj x (frameLogs s ec) := by
      rcases hdj_logs with h0 | h0 | hdj
      · rw [h0] at hsz_pos; dsimp only at hsz_pos; omega
      · omega
      · exact hdj
    exact memW_eq_of_frameDisj heff hlogs_bnd hsz_pos hdj_fl
  -- Each live log record `(log, 40)` has `(log, 40) ∈ frameLogObjects s ec` (since size `40 ≠ 20`),
  -- so all 5 words of `log` (`+0, +8, +16, +24, +32`) are unchanged!
  have hlog_words_eq : ∀ idx, idx < memW s (memW s (ec.1 + 88) + 8) →
      let log := memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)
      memW post log = memW s log ∧
      memW post (log + 8) = memW s (log + 8) ∧
      memW post (log + 16) = memW s (log + 16) ∧
      memW post (log + 24) = memW s (log + 24) ∧
      memW post (log + 32) = memW s (log + 32) := by
    intro idx hidx log
    have hle_ok := (hentries idx hidx).2
    have hlog_bnd : log + 40 ≤ 2 ^ 64 := le_trans hle_ok.2.1.2 hhp_le
    have hlog_in_flo : (log, 40) ∈ frameLogObjects s ec := by
      unfold frameLogObjects
      refine List.mem_flatMap.2 ⟨idx, List.mem_range.2 hidx, ?_⟩
      unfold logOwnedIvls
      refine List.mem_filter.2 ⟨by simp [logRecordIvls, log], ?_⟩
      simp
    have hdj40 := hdj_logObjs (log, 40) hlog_in_flo (by simp)
    have e0 := memW_eq_of_frameDisj heff hlog_bnd (k := 0) (by omega) hdj40
    rw [Nat.add_zero] at e0
    exact ⟨e0,
      memW_eq_of_frameDisj heff hlog_bnd (k := 8) (by omega) hdj40,
      memW_eq_of_frameDisj heff hlog_bnd (k := 16) (by omega) hdj40,
      memW_eq_of_frameDisj heff hlog_bnd (k := 24) (by omega) hdj40,
      memW_eq_of_frameDisj heff hlog_bnd (k := 32) (by omega) hdj40⟩
  have hflo_eq : frameLogObjects post ec = frameLogObjects s ec := by
    unfold frameLogObjects
    dsimp only
    rw [he88_eq, h88_eq 8 (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) from
          by simpa using h88_eq 0 (by omega)]
    apply List.flatMap_congr
    intro idx hidx
    rw [List.mem_range] at hidx
    rw [hptr_eq idx hidx]
    obtain ⟨e0, e8, e16, e24, e32⟩ := hlog_words_eq idx hidx
    unfold logOwnedIvls logRecordIvls
    simp only [e0, e8, e16, e24, e32, hglob_eq "vm_system_address"]
  refine ⟨hflo_eq, ?_⟩
  rw [he88_eq]
  right
  have he88_0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) :=
    by simpa using h88_eq 0 (by omega)
  have he88_8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
    h88_eq 8 (by omega)
  have he88_16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
    h88_eq 16 (by omega)
  refine ⟨(wordsOK_congr_of_dom heff.memaddrs).2 hw24,
    by unfold Allocated; rw [hglob_eq "heap_ptr", hglob_eq "scratch_ptr"]; exact hal24,
    by rw [he88_8]; exact hlen28,
    by rw [he88_8, he88_16]; exact hlen_cap,
    fun idx hidx => ?_⟩
  rw [he88_8] at hidx
  rw [he88_0]
  obtain ⟨⟨_, hdom_ptr, _⟩, hle_ok⟩ := hentries idx hidx
  have hw_ptr : WordAt post (memW s (memW s (ec.1 + 88)) + 8 * idx) := by
    rcases hp : post.memory (BitVec.ofNat 64 (memW s (memW s (ec.1 + 88)) + 8 * idx)) with ⟨w⟩
    exact ⟨w, by rw [heff.memaddrs]; exact hdom_ptr, hp⟩
  rw [hptr_eq idx hidx]
  obtain ⟨e0, e8, e16, e24, e32⟩ := hlog_words_eq idx hidx
  obtain ⟨hw40, hin40, hnt4, hd32, hin20, hintop, hindat⟩ := hle_ok
  refine ⟨hw_ptr, (wordsOK_congr_of_dom heff.memaddrs).2 hw40, ?_⟩
  rw [e0, e8, e16, e24, e32, hglob_eq "heap_ptr"]
  exact ⟨hin40, hnt4, hd32, hin20, hintop, hindat⟩

/-- Intersection of two `TriesTypedWith` witnesses: `Nd1.filter (· ∈ Nd2)` is ALSO a
`TriesTypedWith s S` node heap, and its `nodeExtents` is a subset of BOTH `nodeExtents s Nd1`
and `nodeExtents s Nd2`! -/
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
    obtain ⟨_, _, _, _, d5, d6, _, _, _, _⟩ := h2.1.1 n hn2
    refine ⟨c1, c2, c3, c4, fun hk2 => hroot_iff _ (c5 hk2) (d5 hk2),
      fun hk3 i hi => hroot_iff _ (c6 hk3 i hi) (d6 hk3 i hi), fun h12 => ?_, c8, c9, c10⟩
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

/-- `MsgOwned` congruence when `SameTypedCells s post S Nd` holds for some `Nd` with
`TriesTypedWith s S Nd`, `post` preserves `evmChain`, `frameObjects` on `evmChain`, and `fixedObjects`,
and `AllocatorGrows s post`: intersecting `MsgOwned`'s `AvoidsTries` witness `Nd_m` with `Nd`
gives `Nd_int ⊆ Nd` (so `SameTypedCells s post S Nd_int` holds!) and `Nd_int ⊆ Nd_m` (so `(m, 176)`
is disjoint from `nodeExtents post Nd_int`)! -/
theorem msgOwned_congr {F : Type} {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {m : Nat}
    (hAs : ArenaOK s) (hT : TablesTyped s S) (hTr : TriesTypedWith s S Nd)
    (hcell : SameTypedCells s post S Nd)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hglob_ws : globN post "ws" = globN s "ws")
    (hF : FixedTyped s) (_hFT_post : FixedTyped post) (hfeq : fixedObjects post = fixedObjects s)
    (_hT_post : TablesTyped post S)
    (hchain_eq : evmChain post = evmChain s)
    (hfo_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec)
    (hM : MsgOwned s S m) :
    MsgOwned post S m := by
  obtain ⟨hal, hw, hd_tab, hd_fix, hd_fo, Nd_m, hTr_m, hdj_m⟩ := hM
  obtain ⟨hTr_int, hsub_int⟩ := triesTypedWith_inter hTr hTr_m
  -- Since `nodeExtents s Nd_int ⊆ nodeExtents s Nd`, `SameTypedCells s post S Nd` implies
  -- `SameTypedCells s post S Nd_int`!
  let Nd_int := Nd.filter (fun n => decide (n ∈ Nd_m))
  have hcell_int : SameTypedCells s post S Nd_int := by
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcell
    refine ⟨c1, c2, c3, c4, fun a ha ⟨i, hi, h1, h2⟩ => c5 a ha ⟨i, ?_, h1, h2⟩,
      fun b hb ⟨i, hi, h1, h2⟩ => c6 b hb ⟨i, ?_, h1, h2⟩⟩
    · unfold worldTypedIvls at hi ⊢
      rcases List.mem_append.1 hi with hpre | hne
      · exact List.mem_append_left _ hpre
      · exact List.mem_append_right _ (hsub_int i hne).1
    · unfold worldTypedIvls at hi ⊢
      rcases List.mem_append.1 hi with hpre | hne
      · exact List.mem_append_left _ hpre
      · exact List.mem_append_right _ (hsub_int i hne).1
  have hNH_int_post : NodeHeap post Nd_int := nodeHeap_congr hTr_int.1 hcell_int hh hsc
  have hne_int_eq : nodeExtents post Nd_int = nodeExtents s Nd_int := nodeExtents_eq hTr_int.1 hcell_int
  have hTr_int_post : TriesTypedWith post S Nd_int := by
    refine ⟨hNH_int_post, ?_, ?_⟩
    · rw [hne_int_eq, hfeq]
      intro o ho
      refine ⟨fun t ht i hi => ?_, (hTr_int.2.1 o ho).2⟩
      rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
      exact (hTr_int.2.1 o ho).1 t ht i hi
    · rw [hglob_ws]
      intro hws_nz
      have e24 := memW_typedRec_eq hAs hF hcell (sz := 40) (k := 24) (by decide) hws_nz (by omega)
      have e32 := memW_typedRec_eq hAs hF hcell (sz := 40) (k := 32) (by decide) hws_nz (by omega)
      rw [e24, e32]
      obtain ⟨hr24, hr32⟩ := hTr_int.2.2 hws_nz
      refine ⟨hr24, fun htS i hi => ?_⟩
      have hW32 := (hT.2.1 _ htS).1
      have hcnt32 := htabCount_le_ncap hW32
      have htb32 := (hW32.1 (memW s (globN s "ws" + 32), 88) (by simp [htabFootprint])).1
      rw [htab_hdr_eq hcell htS htb32 3 (by omega)] at hi
      rw [htab_hdr_eq hcell htS htb32 5 (by omega), htab_hdr_eq hcell htS htb32 6 (by omega)]
      have hfp3 : (hdr s (memW s (globN s "ws" + 32)) 6, (hdr s (memW s (globN s "ws" + 32)) 10 + 1) * 8) ∈
          htabFootprint s (memW s (globN s "ws" + 32)) := by simp [htabFootprint]
      have hob := (hW32.1 _ hfp3).1
      have h264 : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; norm_num
      have ho_eq : memW post (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) =
          memW s (hdr s (memW s (globN s "ws" + 32)) 6 + 8 * i) :=
        memW_eq_of_cellHits hcell (by have := le_trans hob.2 h264; omega)
          (mem_worldTypedIvls_htab htS hfp3) ⟨by dsimp only; omega, by dsimp only; omega⟩
      rw [ho_eq, nodeF_eq_of_lt hcell htS hW32 (htabOrder_entry_le_ncap hW32 hi) (by omega)]
      exact hr32 htS i hi
  refine ⟨allocated_mono hh hsc hal, (wordsOK_congr_of_dom hcell.2.1).2 hw, ?_, ?_, ?_, ?_⟩
  · intro t ht i hi
    rw [htabFootprint_eq hcell ht (hT.2.1 t ht).1] at hi
    exact hd_tab t ht i hi
  · rw [hfeq]; exact hd_fix
  · rw [hchain_eq]
    intro ec hec o ho
    rw [hfo_eq ec hec] at ho
    exact hd_fo ec hec o ho
  · refine ⟨Nd_int, hTr_int_post, fun o ho j hj => ?_⟩
    simp only [List.mem_singleton] at ho
    subst ho
    rw [hne_int_eq] at hj
    exact hdj_m (m, 176) (List.mem_singleton.2 rfl) j (hsub_int j hj).2

/-! ## 3. R11 `EvmStep` congruence theorems -/

/-- R11 `ByteRegionEffect.to_evmStep_nil_with`: if `heff : ByteRegionEffect s post Rl` avoids
every nonzero interval of `worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten`
and `AvoidsTries` holds on `Nd`, then `EvmStep [] s post` holds! -/
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
    · intro a ha _; exact heff.cell_frame a (fun x hx _ => ha x (List.mem_append_left [freeGap s] (by simpa using hx)))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx hx0; rw [hbit]
      exact not_cellHits_of_disj_aligned hx0 (i := (a, 8)) (by dsimp only; omega) (by dsimp only; omega)
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
  have hflo_and_logsOK : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    refine frameLogObjects_and_logsOK_eq hAs.2 (hFW_all ec hec) heff (he_eq 88 (by omega)) h88_eq ?_ ?_
    · by_cases hfl0 : (frameLogs s ec).2 = 0
      · exact Or.inr (Or.inl hfl0)
      · exact Or.inr (Or.inr (hdj_f ec hec (frameLogs s ec) (by simp [frameObjects]) hfl0))
    · intro o ho honz
      exact hdj_f ec hec o (by unfold frameObjects; exact List.mem_append_right _ ho) honz
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 24 (by omega), he_eq 40 (by omega),
        he_eq 88 (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec, (hflo_and_logsOK ec hec).1]
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
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlogOK_post := (hflo_and_logsOK ec hec).2
    have hmsg_post : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega)]
      exact msgOwned_congr hAs.2 hWT.1 hTr hcell hh hsc (hglob_eq "ws") hWT.2.2.1 hFT_post hfeq
        hWT_post.1 hchain_eq hframeObjects_eq c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega), he_eq 232 (by omega), he_eq 88 (by omega), he_eq 24 (by omega),
        he_eq 40 (by omega), he_eq 16 (by omega), he_eq 32 (by omega), he_eq 136 (by omega),
        he_eq 168 (by omega), he_eq 176 (by omega),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec, he_eq 216 (by omega), he_eq 144 (by omega), hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_, by rwa [he_eq 88 (by omega)] at hlogOK_post,
      hmsg_post⟩
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
          have hk_le : k + 8 ≤ 40 := by
            simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl <;> omega
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
        have hjcz : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjcz
        · have hbnd := allocated_le_2pow64 hAs.2 hal
          dsimp only at hbnd
          have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
          simp only [hjcz, ↓reduceIte] at hwti
          have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
          exact memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
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
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega)]
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
      rw [(hrec_eq ec hec).1 64 (by omega), (hrec_eq ec hec).1 192 (by omega)]
    rw [hmap_gas]
    exact hGas

/-- Under `EvmAvoids R s`, ANY `ByteRegionEffect s post (R s)` immediately yields `EvmStep [] s post`! -/
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
    refine Or.inr (hdj1 x hx i ?_)
    rcases List.mem_append.1 hi with hi_w | hi_f
    · apply List.mem_append_left
      unfold worldTypedIvls at hi_w ⊢
      rcases List.mem_append.1 hi_w with hi_pre | hi_ne
      · exact List.mem_append_left _ hi_pre
      · exact List.mem_append_right _ (hsub_int i hi_ne).1
    · exact List.mem_append_right _ hi_f

/-- General head-frame & continuation update inside `[(globN s "ev", 280), (globN s "cur_cont", 104)]`
via `ByteRegionEffect`: if
- `memW post (globN s "ev" + k) = memW s (globN s "ev" + k)` for all `k + 8 ≤ 280` outside
  `{0, 16, 64, 72, 104, 120, 128, 160, 184, 192}`,
- `memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16)` (stack height does not exceed old height),
- `memW post (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k)` for all `k + 8 ≤ 104`
  outside `{32}`,
- and `memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
    memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)`,
then `EvmStep [] s post` holds AND `evmR post ≤ evmR s`! -/
theorem evmStep_of_head_frame_cont_update {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (heff : ByteRegionEffect s post [(globN s "ev", 280), (globN s "cur_cont", 104)])
    (hkeep_ev : ∀ k, k + 8 ≤ 280 → k % 8 = 0 →
      k ∉ ([0, 16, 64, 72, 104, 120, 128, 160, 184, 192] : List Nat) →
      memW post (globN s "ev" + k) = memW s (globN s "ev" + k))
    (hsp_le : memW post (globN s "ev" + 16) ≤ memW s (globN s "ev" + 16))
    (hkeep_cont : ∀ k, k + 8 ≤ 104 → k % 8 = 0 → k ≠ 32 →
      memW post (globN s "cur_cont" + k) = memW s (globN s "cur_cont" + k))
    (hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmStep [] s post ∧ evmR post ≤ evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  let headEc : Ivl := (globN s "ev", globN s "cur_cont")
  have hch_eq_cons : ∃ tail, evmChain s = headEc :: tail := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_eq_cons
  have hhead_mem : headEc ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  have hrec_fo : (globN s "ev", 280) ∈ frameObjects s headEc := by simp [frameObjects, headEc]
  have hcont_fo : (globN s "cur_cont", 104) ∈ frameObjects s headEc := by simp [frameObjects, headEc]
  have hfo_disj_wti : ∀ x ∈ [(globN s "ev", 280), (globN s "cur_cont", 104)],
      ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi
    have hx_fo : x ∈ frameObjects s headEc := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hrec_fo
      · exact hcont_fo
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hx_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hx_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; simp
      exact Or.inr ((hFO_disj _ hhead_mem _ hx_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hx_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hx_fo).2 _ (bal_in_fixedObjects h5))
    · have hfl : x ∈ ((evmChain s).map (frameObjects s)).flatten := by
        rw [List.mem_flatten]
        exact ⟨frameObjects s headEc, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hx_fo⟩
      exact Or.inr (hAT_at _ hfl i h6)
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hApost : ArenaReady post := by
    refine ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1, ?_⟩
    unfold ArenaOK; simp only [hglob_eq]; exact hAs.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  have hbfr : ByteFrameOutside s post ([] ++ [(globN s "ev", 280), (globN s "cur_cont", 104)] ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx _ => ha x (List.mem_append_left [freeGap s] (by simpa using hx)))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx hx0; rw [hbit]
      exact not_cellHits_of_disj_aligned hx0 (i := (a, 8)) (by dsimp only; omega) (by dsimp only; omega)
        (hdja x (List.mem_append_left [freeGap s] (by simpa using hx)))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx => hno x (List.mem_append_left [freeGap s] (by simpa using hx)))
  have hcell : SameTypedCells s post S Nd_at :=
    sameTypedCells_of_byteFrame hAs hWT (fun _ h => by simp at h) hfo_disj_wti hbfr
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  -- Pairwise disjointness of `frameObjects s headEc` against its own other elements and against `chTail`:
  have hpw_head_tail :
      (frameObjects s headEc).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s headEc, ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  -- Both `(globN s "ev", 280)` and `(globN s "cur_cont", 104)` are disjoint from:
  -- 1) index 4 `(memW s (headEc.1 + 88), 24)`, index 5 `frameLogs s headEc`, and `frameLogObjects s headEc`;
  -- 2) ALL `o2 ∈ frameObjects s ec` for `ec ∈ chTail`!
  have hhead_disj_rest : ∀ x ∈ [(globN s "ev", 280), (globN s "cur_cont", 104)],
      ∀ o ∈ [(memW s (headEc.1 + 88), 24), frameLogs s headEc] ++ frameLogObjects s headEc,
      Disj x o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    rw [List.cons_append, List.cons_append, List.pairwise_cons] at hpw0
    have hpw1 := hpw0.2
    rw [List.pairwise_cons] at hpw1
    intro x hx o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have ho_in_tail : o ∈ [(memW s (headEc.1 + 8), 32 * memW s (headEc.1 + 232)),
        (memW s (headEc.1 + 24), memW s (headEc.1 + 40)), (memW s (headEc.1 + 88), 24),
        frameLogs s headEc, frameRet s headEc] ++ frameLogObjects s headEc := by
      rcases List.mem_append.1 ho with ho2 | hflo
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho2
        rcases ho2 with rfl | rfl <;> simp
      · exact List.mem_append_right _ hflo
    rcases hx with rfl | rfl
    · exact hpw0.1 o (List.mem_cons_of_mem _ ho_in_tail)
    · exact hpw1.1 o ho_in_tail
  have htail_disj : ∀ ec ∈ chTail, ∀ o ∈ frameObjects s ec,
      ∀ x ∈ [(globN s "ev", 280), (globN s "cur_cont", 104)], Disj x o := by
    intro ec htail o ho x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpw_head_tail.2 _ hrec_fo ec htail o ho
    · exact hpw_head_tail.2 _ hcont_fo ec htail o ho
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 →
        k ∉ ([0, 16, 64, 72, 104, 120, 128, 160, 184, 192] : List Nat) →
        memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → k ≠ 32 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk hk8 hknot
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hkeep_ev k hk hk8 hknot
      · exact memW_eq_of_frameDisj heff hb_e hk (htail_disj ec htail (ec.1, 280) (by simp [frameObjects]))
    · intro k hk hk8 hkne
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hkeep_cont k hk hk8 hkne
      · exact memW_eq_of_frameDisj heff hb_c hk (htail_disj ec htail (ec.2, 104) (by simp [frameObjects]))
    · intro k hk
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact memW_eq_of_frameDisj heff hb_88 hk (fun x hx => hhead_disj_rest x hx _ (by simp))
      · exact memW_eq_of_frameDisj heff hb_88 hk (htail_disj ec htail (memW s (ec.1 + 88), 24) (by simp [frameObjects]))
  have htail_16_gas_eq : ∀ ec ∈ chTail,
      memW post (ec.1 + 16) = memW s (ec.1 + 16) ∧
      memW post (ec.1 + 64) = memW s (ec.1 + 64) ∧
      memW post (ec.1 + 192) = memW s (ec.1 + 192) := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_cons]; exact List.mem_cons_of_mem _ htail
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 (hFW_all ec hec)
    have hdj := htail_disj ec htail (ec.1, 280) (by simp [frameObjects])
    exact ⟨memW_eq_of_frameDisj heff hb_e (by omega) hdj,
           memW_eq_of_frameDisj heff hb_e (by omega) hdj,
           memW_eq_of_frameDisj heff hb_e (by omega) hdj⟩
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
      have hc16 := hc_eq 16 (by omega) (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega) (by omega)
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
  have hflo_and_logsOK : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    refine frameLogObjects_and_logsOK_eq hAs.2 (hFW_all ec hec) heff
      (he_eq 88 (by omega) (by omega) (by decide)) h88_eq ?_ ?_
    · rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact Or.inr (Or.inr (fun x hx => hhead_disj_rest x hx _ (by simp)))
      · exact Or.inr (Or.inr (htail_disj ec htail (frameLogs s ec) (by simp [frameObjects])))
    · intro o ho _
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact fun x hx => hhead_disj_rest x hx o (List.mem_append_right _ ho)
      · exact htail_disj ec htail o (by unfold frameObjects; exact List.mem_append_right _ ho)
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega) (by decide), he_eq 232 (by omega) (by omega) (by decide),
        he_eq 24 (by omega) (by omega) (by decide), he_eq 40 (by omega) (by omega) (by decide),
        he_eq 88 (by omega) (by omega) (by decide), hframeLogs_eq ec hec, hframeRet_eq ec hec,
        (hflo_and_logsOK ec hec).1]
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
  have hsum_gas_le : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
      ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
    rw [hch_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have htail_map : (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
        (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left; intro ec htail
      obtain ⟨_, h64, h192⟩ := htail_16_gas_eq ec htail
      rw [h64, h192]
    rw [htail_map]
    exact Nat.add_le_add_right hgas_le _
  have hevmR_le : evmR post ≤ evmR s := by
    unfold evmR; rw [hchain_eq]; exact hsum_gas_le
  refine ⟨⟨⟨hApost, S, hW_post, ?_⟩, hh, hG, hchain_eq⟩, hevmR_le⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    lt_of_le_of_lt (Nat.add_le_add_right hsum_gas_le 1) hGas⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega) (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have he16_le : memW post (ec.1 + 16) ≤ memW s (ec.1 + 16) := by
      have hec' := hec
      rw [hch_cons, List.mem_cons] at hec'
      rcases hec' with rfl | htail
      · exact hsp_le
      · rw [(htail_16_gas_eq ec htail).1]
    have hlogOK_post := (hflo_and_logsOK ec hec).2
    have hmsg_post : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega) (by decide)]
      exact msgOwned_congr hAs.2 hWT.1 hTr_at hcell hh hsc (hglob_eq "ws") hWT.2.2.1 hFT_post hfeq
        hWT_post.1 hchain_eq hframeObjects_eq c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega) (by decide), he_eq 232 (by omega) (by omega) (by decide),
        he_eq 88 (by omega) (by omega) (by decide), he_eq 24 (by omega) (by omega) (by decide),
        he_eq 40 (by omega) (by omega) (by decide), he_eq 32 (by omega) (by omega) (by decide),
        he_eq 136 (by omega) (by omega) (by decide), he_eq 168 (by omega) (by omega) (by decide),
        he_eq 176 (by omega) (by omega) (by decide),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by decide), he_eq 144 (by omega) (by omega) (by decide),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, (wordsOK_congr_of_dom heff.memaddrs).2 c3, c4, le_trans he16_le c5, c6, c7,
      c8, c9, c10, c11, c12, c13, (wordsOK_congr_of_dom heff.memaddrs).2 c14, ?_,
      by rwa [he_eq 88 (by omega) (by omega) (by decide)] at hlogOK_post, hmsg_post⟩
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
    rw [(htail_16_gas_eq ec hec_tail).1, (hrec_other_eq ec hec_mem).1 232 (by omega) (by omega) (by decide)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega) (by omega) (by omega),
        (hrec_other_eq _ hi0).2.1 72 (by omega) (by omega) (by omega),
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
          have hk_le : k + 8 ≤ 40 := by
            simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl <;> omega
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
        have hjcz : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjcz
        · have hbnd := allocated_le_2pow64 hAs.2 hal
          dsimp only at hbnd
          have hwti := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd_at)
          simp only [hjcz, ↓reduceIte] at hwti
          have hlt : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by have := hWT.2.1.1; omega
          exact memW_eq_of_cellHits hcell (by omega) hwti ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧
          k ∉ ([0, 16, 64, 72, 104, 120, 128, 160, 184, 192] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by decide⟩
      rw [(hrec_other_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega) (by omega) (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega) (by omega) (by omega)
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
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_other_eq _ hj_mem).1 112 (by omega) (by omega) (by decide)]
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

/-- `ByteRegionEffect.to_worldStep`: if `heff : ByteRegionEffect s post (R s)` on a `WorldOK`
state `s`, then `WorldStep R [] stdKeep NoExtra s r post` holds! -/
theorem ByteRegionEffect.to_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s)
    (heff : ByteRegionEffect s post (R s)) :
    WorldStep R [] stdKeep NoExtra s r post := by
  have hAs : ArenaReady s := hWOK.1
  obtain ⟨S0, hWT0⟩ := hWOK.2
  have hF0 : FixedTyped s := hWT0.2.2.1
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hApost : ArenaReady post := by
    refine ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1, ?_⟩
    unfold ArenaOK; simp only [hglob_eq]; exact hAs.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  have hK : RecordsKept R stdKeep s post := by
    intro rec hrec hnz k hk hno
    have hrec_sz : ∃ sz, (rec.1, sz) ∈ typedRecords ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨80, by decide, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨72, by decide, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      · refine ⟨88, by decide, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨sz, htr, hk_le⟩ := hrec_sz
    have hfix := typedRec_in_fixedObjects s htr
    rcases fixedObject_le_2pow64 hAs.2 hF0 hfix with h0 | hbnd
    · simp only [hnz, ↓reduceIte] at h0; omega
    · simp only [hnz, ↓reduceIte] at hbnd
      have ha_lt : globN s rec.1 + k < 2 ^ 64 := by omega
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha_lt
      unfold memW
      rw [heff.cell_frame _ (fun i hi _ => by rw [hbit]; exact hno i hi)]
  refine ⟨hApost, hh, hG, hK, fun S Nd hWT hdj => ?_⟩
  have hbfr : ByteFrameOutside s post (R s ++ ([] : List Ivl) ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hAs.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna; apply heff.out_dom a; rwa [hAs.1.memaddrs]
    · intro a ha _; exact heff.cell_frame a (fun x hx _ =>
        ha x (List.mem_append_left [freeGap s] (List.mem_append_left [] hx)))
    · intro a ha hdja _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx hx0; rw [hbit]
      exact not_cellHits_of_disj_aligned hx0 (i := (a, 8)) (by dsimp only; omega) (by dsimp only; omega)
        (hdja x (List.mem_append_left [freeGap s] (List.mem_append_left [] hx)))
    · intro b hb hno _
      exact heff.byte_frame b hb (fun x hx =>
        hno x (List.mem_append_left [freeGap s] (List.mem_append_left [] hx)))
  have hcell : SameTypedCells s post S Nd :=
    sameTypedCells_of_byteFrame hAs hWT hdj (fun _ h => by simp at h) hbfr
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, hOG⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, ?_, trivial⟩
  intro a ha _
  exact heff.cell_frame a (fun x hx _ =>
    ha x (List.mem_append_left [freeGap s] (List.mem_append_right _ hx)))

end InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas

