import InitECandidate.Solver.Wave8GuestInv.Deliveries.M22.WorldLemmas

/-! Composable frame/store/alloc/world-step primitives for shard `m22` (`wave8/contracts-m22`):
1. `ByteRegionEffect Rl`: exact byte-granular and cell-granular memory write frame inside `Rl`,
   which lifts directly to `WorldStep` on `WorldOK` states (supporting both `R s` output buffers
   and owned global scratch buffers like `keccak_st`/`keccak_pad`).
2. `eval_while_byteRegion`: loop combinator for `ByteRegionEffect`.
3. `eval_alloc_exact`: exact characterization of `alloc(n)` on `ArenaReady` states, including
   alignment, bounds, and `FreshBlock` / `RetAvoids` properties.
-/

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
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `ByteRegionEffect`: byte-accurate and cell-accurate write frame -/

/-- `post` agrees with `s` on metadata, endianness, and globals, leaves cells outside `s.memaddrs`
unchanged, leaves cells not meeting `Rl` (`CellHits`) unchanged, and leaves bytes (`memB`) outside
`Rl` (`InIvl`) unchanged. -/
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

/-- Single `storeByte` step: if `evaluateHOLFiniteState s (.storeByte dst val) = (none, post)` and
`dst` evaluates inside some `i ∈ Rl`, then `ByteRegionEffect s post Rl ∧ post.locals = s.locals`. -/
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
                  exact hna i hi ⟨by rw [hal]; omega, by rw [hal]; omega⟩
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

/-- Single word `store` step: if `evaluateHOLFiniteState s (.store dst val) = (none, post)` with
a one-word `val`, and `[addr.toNat, addr.toNat + 8) ⊆ [i.1, i.1 + i.2)` for some `i ∈ Rl` when
`s.memaddrs addr` holds (note `s.memaddrs = ordinaryDomain` implies `addr.toNat % 8 = 0`), then
`ByteRegionEffect s post Rl ∧ post.locals = s.locals`. -/
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

/-- A content-free global buffer in `globalBuffers` (not one of `ws`, `bs`, `ts`, `bo`) is in
`fixedObjects s` and pairwise disjoint from all `worldTypedIvls s S Nd`! -/
theorem untypedGlobalBuf_disj_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) {g : String} {sz : Nat}
    (hgb : (g, sz) ∈ globalBuffers)
    (huntyped : g ∉ ["ws", "bs", "ts", "bo"]) :
    ∀ i ∈ worldTypedIvls s S Nd,
      i.2 = 0 ∨ Disj (globN s g, if globN s g = 0 then 0 else sz) i := by
  by_cases hg0 : globN s g = 0
  · intro i _; simp [hg0]; exact Or.inr (Or.inl (by omega))
  · obtain ⟨hT, hJ, hF, hTr⟩ := hWT
    have hsz : (if globN s g = 0 then 0 else sz) = sz := if_neg hg0
    rw [hsz]
    -- Find the exact index of `(g, sz)` in `globalBuffers` so `Pairwise Disj` separates it from
    -- distinct entries in `fixedObjects`!
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
        -- Both `(g, sz)` and `r` are in `globalBuffers` with `g ≠ r.1`!
        have hne_name : g ≠ r.1 := by
          intro heq; subst heq
          apply huntyped
          simp only [typedRecords, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with h | h | h | h <;> (rw [Prod.mk.injEq] at h; simp [h.1])
        have hnodup_gb : (globalBuffers.map Prod.fst).Nodup := by decide
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
      -- `(globN s g, sz)` is in the 1st segment of `fixedObjects s`; journal is in the 2nd!
      have hpw12 := (List.pairwise_append.1 (List.pairwise_append.1 hF.2).1).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw12).2.2 _ hm1 _ (List.mem_singleton.2 rfl))
    · have hpw13 := (List.pairwise_append.1 hF.2).1
      have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++ [(globN s "journal", 32 * globN s "journal_cap")] := by
        apply List.mem_append_left; rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hpw13).2.2 _ hm1 _ h4)
    · have hm1 : (globN s g, sz) ∈ (globalBuffers.map fun gn =>
          (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) ++
          [(globN s "journal", 32 * globN s "journal_cap")] ++ blockOutObjects s := by
        apply List.mem_append_left; apply List.mem_append_left
        rw [← hsz]; exact List.mem_map.2 ⟨(g, sz), hgb, rfl⟩
      exact Or.inr ((List.pairwise_append.1 hF.2).2.2 _ hm1 _ h5)
    · exact Or.inr (Disj.symm ((hTr.2.1 i h6).2 _ hmem_fix))

/-- Any `ByteRegionEffect s post (R s ++ extra s)` where every `x ∈ extra s` is a content-free
global buffer `(globN s g, if globN s g = 0 then 0 else sz)` (so `x ∈ fixedObjects s ⊆ worldOwned s S Nd`
and `x` avoids `worldTypedIvls s S Nd`) lifts directly to `WorldStep R [] stdKeep NoExtra s r post`! -/
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
  have hG : GlobalsKept [] s post := fun name _ => by rw [heff.globals]
  -- RecordsKept: note `ws`, `bs`, `ts`, `bo` are in `worldTypedIvls s S0 Nd0`, hence disjoint from `extra s`!
  obtain ⟨S0, hWT0_ex⟩ := hW.2
  obtain ⟨Nd0, hTr0⟩ := hWT0_ex.2.2.2
  have hWT0 : WorldTypedWith s S0 Nd0 := ⟨hWT0_ex.1, hWT0_ex.2.1, hWT0_ex.2.2.1, hTr0⟩
  have hRK : RecordsKept R stdKeep s post := by
    intro rec hrec hgnz k hk hnoR
    have hsz_ex : ∃ sz : Nat, (rec.1, sz) ∈ typedRecords ∧ k + 8 ≤ sz := by
      simp only [stdKeep, List.mem_cons, List.not_mem_nil, or_false] at hrec
      rcases hrec with rfl | rfl | rfl | rfl
      · refine ⟨40, by decide, ?_⟩; simp at hk; omega
      · refine ⟨80, by decide, ?_⟩; simp at hk; omega
      · refine ⟨72, by decide, ?_⟩; simp at hk; omega
      · refine ⟨88, by decide, ?_⟩; simp at hk; omega
    obtain ⟨sz, htr, hkle⟩ := hsz_ex
    have hfix0 := typedRec_in_fixedObjects s htr
    have hsz : (if globN s rec.1 = 0 then 0 else sz) = sz := if_neg hgnz
    rcases hWT0.2.2.1.1 _ hfix0 with h0 | ⟨hal0, _⟩
    · dsimp only at h0; rw [hsz] at h0; omega
    · have hb := allocated_le_2pow64 hW.1.2 hal0
      dsimp only at hb; rw [hsz] at hb
      have ha64 : globN s rec.1 + k < 2 ^ 64 := by omega
      unfold memW
      have hbit : (BitVec.ofNat 64 (globN s rec.1 + k)).toNat = globN s rec.1 + k :=
        Nat.mod_eq_of_lt ha64
      rw [heff.cell_frame (BitVec.ofNat 64 (globN s rec.1 + k)) (fun x hx => by
        rw [hbit]
        rcases List.mem_append.1 hx with hxR | hxE
        · exact hnoR x hxR
        · have hwti := mem_worldTypedIvls_typedRec (s := s) (S := S0) (Nd := Nd0) htr
          rw [hsz] at hwti
          rcases (hextra_fix x hxE).2 S0 Nd0 hWT0 _ hwti with h0 | hdj
          · dsimp only at h0; omega
          · exact not_cellHits_of_disj_aligned (i := (globN s rec.1, sz))
              (by dsimp only; omega) (by dsimp only; omega) (Disj.symm hdj))]
  refine ⟨hA_post, hh, hG, hRK, fun S Nd hWT hdisj => ?_⟩
  have hbfr : ByteFrameOutside s post (R s ++ extra s ++ [freeGap s]) (heapFree s) := by
    refine ⟨heff.be, heff.memaddrs, hW.1.1.memaddrs, ?_, ?_, ?_, ?_⟩
    · intro a hna
      apply heff.out_dom a
      rwa [hW.1.1.memaddrs]
    · intro a ha _
      apply heff.cell_frame a
      intro x hx
      exact ha x (List.mem_append_left [freeGap s] hx)
    · intro a ha hdj _
      have hbit : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      apply heff.cell_frame (BitVec.ofNat 64 a)
      intro x hx
      rw [hbit]
      exact not_cellHits_of_disj_aligned (i := (a, 8)) (by omega) (by omega)
        (hdj x (List.mem_append_left [freeGap s] hx))
    · intro b hb hno _
      apply heff.byte_frame b hb
      intro x hx
      exact hno x (List.mem_append_left [freeGap s] hx)
  have hcell : SameTypedCells s post S Nd :=
    sameTypedCells_of_byteFrame hW.1 hWT hdisj (fun x hx => (hextra_fix x hx).2 S Nd hWT) hbfr
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


end InitECandidate.Solver.Wave8Contracts.M22
