import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.WorldLemmas

/-! Composable frame/store/loop/world-step primitives for shard `m11` (`wave8/contracts-m11`):
1. `ByteRegionEffect Rl`: byte-accurate and cell-accurate memory write frame inside `Rl`,
   lifting directly to `WorldStep` on `WorldOK` states (supporting both `R s` output buffers
   and owned global scratch buffers like `sk_buf`).
2. `eval_while_byteRegion`: loop combinator for `ByteRegionEffect`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.M11

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `ByteRegionEffect`: byte-accurate and cell-accurate write frame -/

structure ByteRegionEffect {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
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
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteRegionEffect s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.out_dom, ?_, ?_⟩
  · intro a ha
    apply h.cell_frame a
    intro i hi hch
    obtain ⟨hc1, hc2⟩ := hch
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno
    apply h.byte_frame b hb
    intro i hi hbi
    obtain ⟨hb1, hb2⟩ := hbi
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

/-! ### `panGetByteHOL` / `panSetByteHOL` disjoint-byte preservation -/

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

private theorem pow_div_high (x y z K J : Nat) (hy : y < 256) (hz : z < 2 ^ K) (hKJ : K + 8 ≤ J) :
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
            dsimp only at hst
            cases hm : s.memory (panByteAlignHOL addr) with
            | word cell =>
              have hcell : (s.memory (panByteAlignHOL addr)).1 = cell := by rw [hm]
              rw [hcell] at hst
              by_cases hdom : s.memaddrs (panByteAlignHOL addr)
              · simp only [hdom, ↓reduceIte, Option.some.injEq] at hst
                subst hst
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
                    exact hna i hi ⟨by rw [hal]; omega, by rw [hal]; omega⟩
                  rw [if_neg hne]
                · intro b hb hno
                  unfold memB
                  dsimp only
                  by_cases hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = panByteAlignHOL addr
                  · rw [if_pos hal_eq]
                    have hrhs : (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 = cell := by
                      rw [hal_eq, hcell]
                    change (panGetByteHOL (BitVec.ofNat 64 b)
                        (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 v.toNat).toNat) cell s.be) s.be).toNat =
                      (panGetByteHOL (BitVec.ofNat 64 b) (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 s.be).toNat
                    rw [hrhs]
                    have hne : BitVec.ofNat 64 b ≠ addr := by
                      intro heq
                      have hbt : (BitVec.ofNat 64 b).toNat = b := Nat.mod_eq_of_lt hb
                      rw [heq] at hbt
                      subst hbt
                      exact hno i hi ⟨h1, h2⟩
                    let byte8 : UInt8 := UInt8.ofNat (BitVec.ofNat 8 v.toNat).toNat
                    have hbyte8 : byte8.toNat = (BitVec.ofNat 8 v.toNat).toNat := by
                      simp [byte8]
                    rw [← hbyte8, panGetByte_panSetByte_ne _ _ byte8 cell s.be hal_eq hne]
                  · rw [if_neg hal_eq]
              · simp [hdom] at hst
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
          unfold flattenHOL at hst
          unfold panMemStoresHOL at hst
          unfold panMemStoreHOL at hst
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
                exact hna i hi ⟨by omega, by omega⟩
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

/-! ## 2. Lifting `ByteRegionEffect` to `WorldStep` -/

theorem untypedGlobalBuf_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) {g : String} {sz : Nat}
    (hgb : (g, sz) ∈ globalBuffers)
    (huntyped : g ∉ ["ws", "bs", "ts", "bo"]) :
    ∀ i ∈ worldTypedIvls s S Nd,
      i.2 = 0 ∨ Disj (globN s g, if globN s g = 0 then 0 else sz) i := by
  by_cases hg0 : globN s g = 0
  · intro i _; simp [hg0]; exact Or.inr (Or.inl rfl)
  · obtain ⟨hT, hJ, hF, hTr⟩ := hWT
    have hsz : (if globN s g = 0 then 0 else sz) = sz := if_neg hg0
    rw [hsz]
    have hmem_fix : (globN s g, sz) ∈ fixedObjects s := by
      have : (globN s g, if globN s g = 0 then 0 else sz) ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      rwa [hsz] at this
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr (Disj.symm (((hT.2.1 t ht).2 i hfp).2 _ hmem_fix))
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      by_cases hr0 : globN s r.1 = 0
      · simp [hr0]
      · right
        have hne_name : g ≠ r.1 := by
          intro heq; subst heq
          apply huntyped
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [Prod.mk.injEq] at h; simp [h.1])
        obtain ⟨idx1, hidx1, heq1⟩ := List.mem_iff_getElem.1 hgb
        have hr_gb : r ∈ globalBuffers := by
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [h]; decide)
        obtain ⟨idx2, hidx2, heq2⟩ := List.mem_iff_getElem.1 hr_gb
        have hidx_ne : idx1 ≠ idx2 := by
          intro h; subst h; rw [heq1] at heq2
          exact hne_name (congrArg Prod.fst heq2)
        have hpw_gb : ((globalBuffers.map fun gn =>
            (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2))).Pairwise Disj := by
          have hpw := hF.2
          unfold fixedObjects at hpw
          exact (List.pairwise_append.1 (List.pairwise_append.1 (List.pairwise_append.1 hpw).1).1).1
        have hget := List.pairwise_iff_getElem.1 hpw_gb
        rcases Nat.lt_or_gt_of_ne hidx_ne with hlt | hgt
        · have hd := hget idx1 idx2 (by simp; exact hidx1) (by simp; exact hidx2) hlt
          simp only [List.getElem_map, heq1, heq2, hsz] at hd
          exact hd
        · have hd := hget idx2 idx1 (by simp; exact hidx2) (by simp; exact hidx1) hgt
          simp only [List.getElem_map, heq1, heq2, hsz] at hd
          exact Disj.symm hd
    · simp only [List.mem_singleton] at h3
      subst h3
      have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl))
    · have hpw13 := (List.pairwise_append.1 hF.2).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++ [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] := by
        apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4)
    · have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
          [(if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s := by
        apply List.mem_append_left; apply List.mem_append_left
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hF.2).2.2 _ hm1 _ h5)
    · exact Or.inr (Disj.symm ((hTr.2.1 i h6).2 _ hmem_fix))

theorem ByteRegionEffect.to_worldStep {F : Type}
    {R extra : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hW : WorldOK s)
    (hextra_fix : ∀ x ∈ extra s, x ∈ fixedObjects s ∧
      ∀ S Nd, WorldTypedWith s S Nd → ∀ i ∈ worldTypedIvls s S Nd, i.2 = 0 ∨ Disj x i)
    (heff : ByteRegionEffect s post (R s ++ extra s)) :
    WorldStep R [] stdKeep NoExtra s r post := by
  have hinv_post : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hW.1.1
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, heff.globals]
  have hA_post : ArenaReady post := by
    refine ⟨hinv_post, ?_⟩
    unfold ArenaOK
    simp only [hglob_eq]
    exact hW.1.2
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hG : GlobalsKept [] s post := fun _ _ => by rw [heff.globals]
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hTr0⟩ := hWT0_ex.2.2.2
  have hWT0 : WorldTypedWith s S0 Nd0 := ⟨hWT0_ex.1, hWT0_ex.2.1, hWT0_ex.2.2.1, hTr0⟩
  have hmem_eq_bytes : ∀ a : BitVec 64, ordinaryDomain a →
      (∀ k : Nat, k < 8 → memB post (a.toNat + k) = memB s (a.toNat + k)) →
      post.memory a = s.memory a := by
    intro a ha_dom hb
    have hdom' := (ordinaryDomain_iff a).mp ha_dom
    have ha_ord : a.toNat % 8 = 0 ∧ sourceBase ≤ a.toNat ∧ a.toNat < heapEnd := by
      rw [sourceBase_val, heapEnd_val]; omega
    have hhe_lt : heapEnd ≤ 2 ^ 64 := by rw [heapEnd_val]; decide
    have hhe_8 : heapEnd % 8 = 0 := by decide
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
      rw [hal_eq, hp_m, hs_m, heff.be] at hbk
      exact hbk
    have hshift : ∀ (w : BitVec 64) (idx : Nat), idx < 8 →
        w.toNat / 256 ^ idx % 256 =
        (panGetByteHOL (BitVec.ofNat 64 (a.toNat + (if s.be then 7 - idx else idx))) w s.be).toNat := by
      intro w idx hidx
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
  have hRK : RecordsKept R stdKeep s post := by
    intro rec hrec hgnz k hk hnoR
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ typedRecords ∧ k % 8 = 0 ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hk8, hkle⟩ := hsz_ex
    have hfix0 := typedRec_in_fixedObjects s htr
    have hsz : (if globN s rec.1 = 0 then 0 else sz) = sz := if_neg hgnz
    rcases hWT0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, hw0⟩
    · dsimp only at h0; rw [hsz] at h0; omega
    · have hb := allocated_le_2pow64 hW.1.2 hal0
      dsimp only at hb; rw [hsz] at hb
      have hg8 : (globN s rec.1) % 8 = 0 := hw0.1
      have ha64 : globN s rec.1 + k < 2 ^ 64 := by omega
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha64
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 (globN s rec.1 + k))
      · rw [hmem_eq_bytes _ hdom]
        intro idx hidx
        rw [hbit]
        apply heff.byte_frame (globN s rec.1 + k + idx) (by omega)
        intro x hx hbx
        rcases List.mem_append.1 hx with hxR | hxE
        · apply hnoR x hxR
          obtain ⟨_, _⟩ := hbx
          exact ⟨by omega, by omega⟩
        · have hwti := mem_worldTypedIvls_typedRec (s := s) (S := S0) (Nd := Nd0) htr
          rw [hsz] at hwti
          rcases (hextra_fix x hxE).2 S0 Nd0 hWT0 _ hwti with h0 | hdj
          · dsimp only at h0; omega
          · obtain ⟨_, _⟩ := hbx
            rcases hdj with h0 | h0 | h | h
            · omega
            · dsimp only at h0; omega
            · dsimp only at h; omega
            · dsimp only at h; omega
      · rw [heff.out_dom]
        rwa [hW.1.1.memaddrs]
  refine ⟨hA_post, hh, hG, hRK, fun S Nd hWT hdisj => ?_⟩
  have hcell : SameTypedCells s post S Nd := by
    refine ⟨heff.be, heff.memaddrs, hW.1.1.memaddrs, ?_, ?_, ?_⟩
    · intro a hna
      apply heff.out_dom a
      rwa [hW.1.1.memaddrs]
    · intro a ha ha8 ⟨i, hi, ha1, ha2⟩
      by_cases hdom : ordinaryDomain (BitVec.ofNat 64 a)
      · have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
        apply hmem_eq_bytes _ hdom
        intro k hk
        rw [hbit]
        apply heff.byte_frame (a + k) (by omega)
        intro x hx hbx
        rcases List.mem_append.1 hx with hxR | hxE
        · have hdj := hdisj x hxR i hi
          obtain ⟨_, _⟩ := hbx
          rcases hdj with h0 | h0 | h | h <;> omega
        · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
          · omega
          · obtain ⟨_, _⟩ := hbx
            rcases hdj with h0 | h0 | h | h <;> omega
      · apply heff.out_dom
        rwa [hW.1.1.memaddrs]
    · intro b hb ⟨i, hi, hb1, hb2⟩
      apply heff.byte_frame b hb
      intro x hx hbx
      rcases List.mem_append.1 hx with hxR | hxE
      · have hdj := hdisj x hxR i hi
        obtain ⟨_, _⟩ := hbx
        rcases hdj with h0 | h0 | h | h <;> omega
      · rcases (hextra_fix x hxE).2 S Nd hWT i hi with hi0 | hdj
        · omega
        · obtain ⟨_, _⟩ := hbx
          rcases hdj with h0 | h0 | h | h <;> omega
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hW.1.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [heff.globals])
  have hFT_post := fixedTyped_of_eq hA_post hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, hOG⟩ := worldTypedWith_congr_w1 hW.1 hA_post hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  refine ⟨S, Nd, fun _ h => h, hWT_post, hOG, ?_, trivial⟩
  intro a ha _
  apply heff.cell_frame a
  intro x hx
  rcases List.mem_append.1 hx with hxR | hxE
  · exact ha x (List.mem_append_left [freeGap s] (List.mem_append_right (worldOwned s S Nd) hxR))
  · have hx_wo : x ∈ worldOwned s S Nd := by
      unfold worldOwned
      exact List.mem_append_left _ (List.mem_append_right _ (hextra_fix x hxE).1)
    exact ha x (List.mem_append_left [freeGap s] (List.mem_append_left (R s) hx_wo))

/-! ## 3. Loop combinator for `ByteRegionEffect` -/

theorem eval_while_byteRegion {F : Type}
    (cond : ExpHOL 64) (body : ProgHOL 64) (Rl : List Ivl)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hP_dec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t, P t →
      (evaluateHOLFiniteState t body).1 ≠ some .timeOut →
        (((evaluateHOLFiniteState t body).1 = none ∨
          (evaluateHOLFiniteState t body).1 = some .continue) →
            P (evaluateHOLFiniteState t body).2 ∧
            ByteRegionEffect t (evaluateHOLFiniteState t body).2 Rl) ∧
        ((evaluateHOLFiniteState t body).1 = some .break →
          ByteRegionEffect t (evaluateHOLFiniteState t body).2 Rl) ∧
        (∀ r, (evaluateHOLFiniteState t body).1 = some r →
          r ≠ .continue → r ≠ .break → r ≠ .timeOut →
          (∀ v, r ≠ .returned v) ∧ (∀ e v, e ≠ ofString "TrapErr" → r ≠ .exception e v))) :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k → P s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
        ((evaluateHOLFiniteState s (.while cond body)).1 = none →
          ByteRegionEffect s (evaluateHOLFiniteState s (.while cond body)).2 Rl) ∧
        ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
          ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    rcases hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
      _ | cv
    · simp only [hc] at hnt ⊢
      exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · simp only [hc] at hnt ⊢
      rcases cv with ⟨⟨w⟩⟩ | _ | _
      · dsimp only at hnt ⊢
        by_cases hw : w = 0
        · subst hw
          exact ⟨fun _ => ByteRegionEffect.refl s Rl, fun h => False.elim (h rfl)⟩
        · rw [if_pos hw] at hnt ⊢
          by_cases hk0 : s.clock = 0
          · simp [hk0] at hnt
          · rw [if_neg hk0] at hnt ⊢
            have hPd : P (decClockHOLFinite s) := hP_dec s hPs
            have heff_dec : ByteRegionEffect s (decClockHOLFinite s) Rl :=
              ByteRegionEffect.refl s Rl |>.with_locals_clock s.locals (s.clock - 1)
            have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            have hd_clk : (decClockHOLFinite s).clock < k := by
              simp [decClockHOLFinite, hclk]; omega
            rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
            simp only [hbo] at hnt hb_clk ⊢
            have hnt_b : rb ≠ some .timeOut := by
              rintro rfl; exact hnt rfl
            have hb_spec := hbody (decClockHOLFinite s) hPd (by rw [hbo]; exact hnt_b)
            rw [hbo] at hb_spec
            dsimp only at hb_spec
            cases rb with
            | none =>
              obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inl rfl)
              have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
              exact ⟨fun hn => (heff_dec.trans heff_b).trans (jih.1 hn), jih.2⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hPsb, heff_b⟩ := hb_spec.1 (Or.inr rfl)
                have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt
                exact ⟨fun hn => (heff_dec.trans heff_b).trans (jih.1 hn), jih.2⟩
              | «break» =>
                exact ⟨fun _ => heff_dec.trans (hb_spec.2.1 rfl), fun h => absurd rfl h⟩
              | timeOut => exact absurd rfl hnt_b
              | returned v =>
                obtain ⟨hnr, _⟩ := hb_spec.2.2 (.returned v) rfl (by simp) (by simp) (by simp)
                exact absurd rfl (hnr v)
              | exception e v =>
                refine ⟨fun h => by simp at h, fun _ hres => ?_⟩
                obtain ⟨_, hne⟩ := hb_spec.2.2 (.exception e v) rfl (by simp) (by simp) (by simp)
                rcases hres with ⟨_, h⟩ | ⟨e', v', h, he⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2
                  subst h1 h2
                  exact hne e v he rfl
              | error =>
                exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
              | finalFfi ev =>
                exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · exact ⟨fun h => by simp at h, fun _ hres => by rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

end InitECandidate.Solver.Wave8GuestInv.M11
