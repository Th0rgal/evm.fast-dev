import InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28_Core

/-! Composable execution effect (`InitEff`) and primitive callees (`alloc`, `memzero`, `memcpy`,
`st_le64`, `st_be32`, `st_be64`, `addr_from_words`, `keccak256`, `sha256_pair`, `heap_mark`,
`heap_release`) for Shards P26 + P27 + P28. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

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

/-! ## 1. Byte store & word store primitives -/

def memWordAt (mem : BitVec 64 → HolWordLab 64) (addr : BitVec 64) : BitVec 64 :=
  match mem addr with
  | .word w => w

def memByteAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (addr : BitVec 64) : UInt8 :=
  panGetByteHOL addr (memWordAt mem (panByteAlignHOL addr)) be

theorem memB_eq_memByteAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memB s a = (memByteAt s.memory s.be (BitVec.ofNat 64 a)).toNat := by
  unfold memB memByteAt memWordAt
  cases s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w => rfl

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
    rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]; omega
  rw [h1, Nat.add_mul_div_right _ _ hpJ]; omega

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
    conv_lhs => rw [hj_eq]; rw [Nat.pow_add]
  have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
  have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
  rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
    Nat.mul_div_cancel _ hpK8]

theorem panMemStoreByte_other_byte {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {bw : BitVec 8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr bw = some mem')
    {addr' : BitVec 64} (hne : addr' ≠ addr) :
    (match mem' (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) =
    (match mem (panByteAlignHOL addr') with | .word v => (panGetByteHOL addr' v be).toNat) := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
      · simp only [hal, ↓reduceIte, hcell, panGetByteHOL]
        let b : UInt8 := UInt8.ofNat bw.toNat
        have hb8 : b.toNat < 256 := b.toNat_lt_size
        have hbw_eq : bw.toNat = b.toNat := by
          have := bw.isLt
          simp [b, UInt8.toNat_ofNat', Nat.mod_eq_of_lt this]
        rw [hbw_eq]
        have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
        have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
            ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
              cell.toNat / 2 ^ J := by
          intro J hKJ
          have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
            have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
            conv_lhs => rw [hj_eq]; rw [Nat.pow_add]
          have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
          rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
        have h256_pow : ∀ a : BitVec 64,
            (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
          intro a
          have : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by
            rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
          rw [this]; cases be <;> simp [byteBitIndex, Nat.mul_comm 8]
        have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
          intro hmeq; apply hne; apply BitVec.eq_of_toNat_eq
          have ha1 := panByteAlign_toNat64 addr'
          have ha2 := panByteAlign_toNat64 addr
          rw [hal] at ha1; omega
        have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
            byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
          have hm1 : addr'.toNat % 8 < 8 := by omega
          have hm2 : addr.toNat % 8 < 8 := by omega
          cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
        have heq_mod : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
          cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 := by
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
              rw [hmul] at hdm; omega
            conv_rhs => rw [hcell_eq]
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]; omega
          · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
              hcell_high _ hhigh]
        simpa [UInt8.toNat_ofNat'] using heq_mod
      · simp only [hal, ↓reduceIte]
    · cases hst

/-! ## 2. `ByteEff`: pure memory-region write effect (no global changes) -/

structure ByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  eshapes    : post.eshapes = s.eshapes
  out_dom    : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, post.memory a ≠ s.memory a → ∃ i ∈ Rl, CellHitsPos a.toNat i
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b → ∃ i ∈ Rl, InIvl b i

theorem ByteEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd rfl h,
   fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

theorem ByteEff.locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ByteEff s post Rl) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteEff s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteEff a b Rl) (h2 : ByteEff b c Rl) : ByteEff a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, h2.globals.trans h1.globals, h2.eshapes.trans h1.eshapes, ?_, ?_, ?_⟩
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.out_dom x hne
    · rw [← h1.memaddrs]; exact h2.out_dom x hcb
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.cell_frame x hne
    · exact h2.cell_frame x hcb
  · intro x hx hne
    by_cases hcb : memB c x = memB b x
    · rw [hcb] at hne; exact h1.byte_frame x hx hne
    · exact h2.byte_frame x hx hcb

theorem ByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ByteEff s post R1)
    (hsub : ∀ i ∈ R1, 0 < i.2 → ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteEff s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes, h.out_dom, ?_, ?_⟩
  · intro a hne
    obtain ⟨i, hi, hipos, hc1, hc2⟩ := h.cell_frame a hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi hipos
    exact ⟨j, hj, by omega, by omega, by omega⟩
  · intro b hb hne
    obtain ⟨i, hi, hb1, hb2⟩ := h.byte_frame b hb hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi (by omega)
    exact ⟨j, hj, by omega, by omega⟩

theorem byteEff_store_one {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs x →
      ∃ i ∈ Rl, i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.store dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0) := by
  rw [evaluateHOLFiniteState_store]
  split
  · rename_i x hx
    split
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
          subst hmem
          have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          obtain ⟨ivl, hivl, hi1, hi2⟩ := hin x hx hdom
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
            fun _ => ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩⟩
          · intro a hne; by_cases hax : a = x
            · subst hax; exact hdom
            · simp [hax] at hne
          · intro a hne; by_cases hax : a = x
            · subst hax; exact ⟨ivl, hivl, by omega, by omega, by omega⟩
            · simp [hax] at hne
          · intro b hb hne
            by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = x
            · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
              rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc_nat
              exact ⟨ivl, hivl, by omega, by omega⟩
            · unfold memB at hne; simp [hal] at hne
        · simp [hdom] at hmem
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

theorem byteEff_storeByte {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs (panByteAlignHOL x) →
      ∃ i ∈ Rl, InIvl x.toNat i) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd) := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · rename_i x hx
    split
    · rename_i vw hvw
      split
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        obtain ⟨ivl, hivl, hin_x⟩ := hin x hx hdom
        have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
          intro a hne
          have hm' := hmem
          unfold panMemStoreByteWord8HOL at hm'
          cases s.memory (panByteAlignHOL x) with
          | word cell =>
            dsimp only at hm'; rw [if_pos hdom] at hm'
            injection hm' with hm_eq; subst hm_eq; simp [hne]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
          fun _ => ⟨x, hx, by omega, by omega⟩⟩
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax; exact hdom
          · exact False.elim (hne (hmem_cell a hax))
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax
            obtain ⟨hx1, hx2⟩ := hin_x
            exact ⟨ivl, hivl, by omega, by rw [hal_nat]; omega, by rw [hal_nat]; omega⟩
          · exact False.elim (hne (hmem_cell a hax))
        · intro b hb hne
          by_cases hbx : BitVec.ofNat 64 b = x
          · have hb_eq : b = x.toNat := by
              have := congrArg BitVec.toNat hbx
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
            rw [hb_eq]; exact ⟨ivl, hivl, hin_x⟩
          · have hob := @panMemStoreByte_other_byte s.memory s.memaddrs
              (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x
              (BitVec.ofNat 8 vw.toNat) mem' hmem (BitVec.ofNat 64 b) hbx
            exact False.elim (hne hob)
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

/-! ## 3. `memzero`, `memcpy`, `st_le32`, `st_le64`, `st_be32`, `st_be64`, `addr_from_words` -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def noBreakOrCont : ProgHOL 64 → Bool
  | .seq a b => noBreakOrCont a && noBreakOrCont b
  | .ite _ a b => noBreakOrCont a && noBreakOrCont b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreakOrCont {F : Type} (p : ProgHOL 64) (hp : noBreakOrCont p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreakOrCont] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreakOrCont a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreakOrCont b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreakOrCont b hab.2 s
      · exact evaluate_noBreakOrCont a hab.1 s
    · simp
  | _ => simp [shape, noBreakOrCont] at hp

private def CopyInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(dst0.toNat, n0.toNat)] ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word (x + y))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp]

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word (x + y + c))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp,
    BitVec.add_assoc]

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [he, memLoadHOLExact] at hv
      split at hv
      · cases hm : s.memory addr with
        | word w =>
          rw [hm] at hv
          split at hv
          · injection hv with h; exact ⟨w, h.symm⟩
          · cases hv
      · cases hv
    · simp [he] at hv
    · simp [he] at hv

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (dst0 + iw).toNat = dst0.toNat + iw.toNat ∧
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  rw [sourceBase_val, heapEnd_val] at hprev hcur ⊢
  have hdlt := dst0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢; rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat := BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat := BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, rfl, by omega, hdlo, by omega⟩

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he; exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge; simp [hge] at he; exact hw he.symm

private theorem while_copyInv {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnbc : noBreakOrCont body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      CopyInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : CopyInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    CopyInv s0 dst0 n0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nbc := evaluate_noBreakOrCont body hnbc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nbc
          cases r1 with
          | none =>
            have hmid : CopyInv s0 dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nbc.2
            | «break» => exact absurd rfl nbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem assign_i_copyInv {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(dst0.toNat, n0.toNat)])
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    CopyInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]; dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, heff.locals_clock _ s.clock, ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem seq_store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (st b : ProgHOL 64)
    (hloc : (evaluateHOLFiniteState s st).2.locals = s.locals)
    (h : (evaluateHOLFiniteState s (.seq st b)).1 = none) :
    (evaluateHOLFiniteState s st).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).1 = none ∧
    (evaluateHOLFiniteState s (.seq st b)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).2 ∧
    (evaluateHOLFiniteState s st).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s st with ⟨r, m⟩
  rw [hr] at h hloc
  cases r with
  | none => exact ⟨rfl, h, rfl, hloc⟩
  | some _ => simp at h

theorem store_one_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hnone : (evaluateHOLFiniteState s (.store dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0 := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split at hnone
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          exact ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩
        · simp [hdom] at hmem
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem storeByte_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · split at hnone
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        exact ⟨x, hx, by omega, by omega⟩
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem byteEff_store_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hoff : off + 8 ≤ len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_store_one hG dstExp valExp hval (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

theorem byteEff_storeByte_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hoff : off < len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_storeByte hG dstExp valExp (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

private theorem step_copy_loop32 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 v8 v16 v24 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs8, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_store_control_frame s1 _ _).2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs16, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_store_control_frame s2 _ _).2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs24, _, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_store_control_frame s3 _ _).2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  have hd_s1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi_s1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd_s2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd_s1
  have hi_s2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi_s1
  have hd_s3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd_s2
  have hi_s3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi_s2
  have hd_s4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd_s3
  have hi_s4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi_s3
  have hn_s4 : s4.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hl4, hl3, hl2, hl1]; exact hn
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  obtain ⟨x8, hx8, _, hd8_hi, _⟩ := store_one_domain hG1 _ v8 (hv8 s1) hs8
  obtain ⟨x16, hx16, _, hd16_hi, _⟩ := store_one_domain hG2 _ v16 (hv16 s2) hs16
  obtain ⟨x24, hx24, _, hd24_hi, _⟩ := store_one_domain hG3 _ v24 (hv24 s3) hs24
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex8 := eval_add3_locals s1 _ _ dst0 iw 8 hd_s1 hi_s1
  have ex16 := eval_add3_locals s2 _ _ dst0 iw 16 hd_s2 hi_s2
  have ex24 := eval_add3_locals s3 _ _ dst0 iw 24 hd_s3 hi_s3
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex8] at hx8; injection hx8 with hx8; injection hx8 with hx8; injection hx8 with hx8; subst hx8
  rw [ex16] at hx16; injection hx16 with hx16; injection hx16 with hx16; injection hx16 with hx16; subst hx16
  rw [ex24] at hx24; injection hx24 with hx24; injection hx24 with hx24; injection hx24 with hx24; subst hx24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    rw [a8] at hd8_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    rw [a16] at hd16_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    rw [a24] at hd24_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 32 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hin32 : 0 < 32 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 32 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 32 (by omega) hin32 (hv0 sd) (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff2 := byteEff_store_at hG1 _ v8 (dst0 + iw) 8 32 (by omega) hin32 (hv8 s1) (by omega) ex8
  have eff3 := byteEff_store_at hG2 _ v16 (dst0 + iw) 16 32 (by omega) hin32 (hv16 s2) (by omega) ex16
  have eff4 := byteEff_store_at hG3 _ v24 (dst0 + iw) 24 32 (by omega) hin32 (hv24 s3) (by omega) ex24
  have hmeta4 : s4.code = originalRuntimeCode := hG4.code
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_copyInv hmeta4 hG4 (heffd.trans (eff1.trans (eff2.trans (eff3.trans eff4))))
    hd_s4 hn_s4 hi_s4 hle_ik hdlo hdhi

private theorem step_copy_loop8w {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 8 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (hv0 sd) (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff1)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem step_copy_loop8b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs1, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_storeByte_control_frame s1 _ _).2.2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs2, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_storeByte_control_frame s2 _ _).2.2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs3, hr4, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_storeByte_control_frame s3 _ _).2.2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  obtain ⟨hs4, hr5, heq5, hl5⟩ := seq_store_none s4 _ _ (evaluate_storeByte_control_frame s4 _ _).2.2.1 hr4
  let s5 := (evaluateHOLFiniteState s4 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)).2
  have hG5 : GuestInv s5 := guestInv_evaluate s4 _ hG4
  obtain ⟨hs5, hr6, heq6, hl6⟩ := seq_store_none s5 _ _ (evaluate_storeByte_control_frame s5 _ _).2.2.1 hr5
  let s6 := (evaluateHOLFiniteState s5 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)).2
  have hG6 : GuestInv s6 := guestInv_evaluate s5 _ hG5
  obtain ⟨hs6, hr7, heq7, hl7⟩ := seq_store_none s6 _ _ (evaluate_storeByte_control_frame s6 _ _).2.2.1 hr6
  let s7 := (evaluateHOLFiniteState s6 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)).2
  have hG7 : GuestInv s7 := guestInv_evaluate s6 _ hG6
  obtain ⟨hs7, _, heq8, hl8⟩ := seq_store_none s7 _ _ (evaluate_storeByte_control_frame s7 _ _).2.2.1 hr7
  let s8 := (evaluateHOLFiniteState s7 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)).2
  have hG8 : GuestInv s8 := guestInv_evaluate s7 _ hG7
  have hd1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd1
  have hi2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi1
  have hd3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd2
  have hi3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi2
  have hd4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd3
  have hi4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi3
  have hd5 : s5.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl5]; exact hd4
  have hi5 : s5.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl5]; exact hi4
  have hd6 : s6.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl6]; exact hd5
  have hi6 : s6.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl6]; exact hi5
  have hd7 : s7.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl7]; exact hd6
  have hi7 : s7.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl7]; exact hi6
  have hd8 : s8.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl8]; exact hd7
  have hi8 : s8.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl8]; exact hi7
  have hn8 : s8.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hn
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex1 := eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1
  have ex2 := eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2
  have ex3 := eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3
  have ex4 := eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4
  have ex5 := eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5
  have ex6 := eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6
  have ex7 := eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  obtain ⟨x1, hx1, _, hd1_hi⟩ := storeByte_domain hG1 _ b1 hs1
  obtain ⟨x2, hx2, _, hd2_hi⟩ := storeByte_domain hG2 _ b2 hs2
  obtain ⟨x3, hx3, _, hd3_hi⟩ := storeByte_domain hG3 _ b3 hs3
  obtain ⟨x4, hx4, _, hd4_hi⟩ := storeByte_domain hG4 _ b4 hs4
  obtain ⟨x5, hx5, _, hd5_hi⟩ := storeByte_domain hG5 _ b5 hs5
  obtain ⟨x6, hx6, _, hd6_hi⟩ := storeByte_domain hG6 _ b6 hs6
  obtain ⟨x7, hx7, _, hd7_hi⟩ := storeByte_domain hG7 _ b7 hs7
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex1] at hx1; injection hx1 with hx1; injection hx1 with hx1; injection hx1 with hx1; subst hx1
  rw [ex2] at hx2; injection hx2 with hx2; injection hx2 with hx2; injection hx2 with hx2; subst hx2
  rw [ex3] at hx3; injection hx3 with hx3; injection hx3 with hx3; injection hx3 with hx3; subst hx3
  rw [ex4] at hx4; injection hx4 with hx4; injection hx4 with hx4; injection hx4 with hx4; subst hx4
  rw [ex5] at hx5; injection hx5 with hx5; injection hx5 with hx5; injection hx5 with hx5; subst hx5
  rw [ex6] at hx6; injection hx6 with hx6; injection hx6 with hx6; injection hx6 with hx6; subst hx6
  rw [ex7] at hx7; injection hx7 with hx7; injection hx7 with hx7; injection hx7 with hx7; subst hx7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 := by
    rw [a1] at hd1_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 := by
    rw [a2] at hd2_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 := by
    rw [a3] at hd3_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 := by
    rw [a4] at hd4_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 := by
    rw [a5] at hd5_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 := by
    rw [a6] at hd6_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    rw [a7] at hd7_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 8 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hin8 : 0 < 8 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 8 (by omega) hin8 (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff1 := byteEff_storeByte_at hG1 _ b1 (dst0 + iw) 1 8 (by omega) hin8 (by omega) ex1
  have eff2 := byteEff_storeByte_at hG2 _ b2 (dst0 + iw) 2 8 (by omega) hin8 (by omega) ex2
  have eff3 := byteEff_storeByte_at hG3 _ b3 (dst0 + iw) 3 8 (by omega) hin8 (by omega) ex3
  have eff4 := byteEff_storeByte_at hG4 _ b4 (dst0 + iw) 4 8 (by omega) hin8 (by omega) ex4
  have eff5 := byteEff_storeByte_at hG5 _ b5 (dst0 + iw) 5 8 (by omega) hin8 (by omega) ex5
  have eff6 := byteEff_storeByte_at hG6 _ b6 (dst0 + iw) 6 8 (by omega) hin8 (by omega) ex6
  have eff7 := byteEff_storeByte_at hG7 _ b7 (dst0 + iw) 7 8 (by omega) hin8 (by omega) ex7
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_copyInv hG8.code hG8
    (heffd.trans (eff0.trans (eff1.trans (eff2.trans (eff3.trans (eff4.trans (eff5.trans (eff6.trans eff7))))))))
    hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_copy_loop1b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  have hnl : ¬ (n0 < iw + 1) := by
    rw [BitVec.lt_def]
    have := n0.isLt
    have : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
    omega
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 1 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff0)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem copy_body_eff {F : Type}
    (alignCond v0 v8 v16 v24 b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0))) :
    let w32 := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    let w8w := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    let w8b := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    let w1b := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    let fullBody := ProgHOL.dec (ofString "i") .one (.const 0)
      (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
    Resumes (evaluateHOLFiniteState s0 fullBody).1 →
      ByteEff s0 (evaluateHOLFiniteState s0 fullBody).2 [(dst0.toNat, n0.toNat)] ∧
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  intro w32 w8w w8b w1b fullBody hres
  have hdec : evaluateHOLFiniteState s0 fullBody =
      let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
      let r := evaluateHOLFiniteState si (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
      (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "i", s0.locals.lookup (ofString "i")) }) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact, shapeEqHOL, shapeOfHOLExact]
  rw [hdec] at hres ⊢
  dsimp only at hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
  have hinv_si : CopyInv s0 dst0 n0 si := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, 0, ?_, by simp, fun h => by simp at h⟩
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "i" ≠ ofString "dst" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases h1 : evaluateHOLFiniteState si (.ite alignCond (.seq w32 w8w) .skip) with ⟨r1, m1⟩
  rw [h1] at hres
  cases r1 with
  | some _ =>
    exfalso; exact evaluate_noReturnOrRaise (.ite alignCond (.seq w32 w8w) .skip) rfl si (by rw [h1]; exact hres)
  | none =>
    have hinv_m1 : CopyInv s0 dst0 n0 m1 := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with _ hm1; subst hm1; exact hinv_si
        · rw [evaluateHOLFiniteState_seq_line780] at h1
          rcases hw32 : evaluateHOLFiniteState si w32 with ⟨rw32, mw32⟩
          rw [hw32] at h1
          cases rw32 with
          | some _ => simp at h1
          | none =>
            have hinv_32 := (while_copyInv _ _ rfl (step_copy_loop32 v0 v8 v16 v24 hv0 hv8 hv16 hv24)
              si.clock si mw32 le_rfl hinv_si hw32).1
            exact (while_copyInv _ _ rfl (step_copy_loop8w v0 hv0)
              mw32.clock mw32 m1 le_rfl hinv_32 h1).1
      · simp at h1
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    rcases h2 : evaluateHOLFiniteState m1 w8b with ⟨r2, m2⟩
    rw [h2] at hres
    cases r2 with
    | some _ =>
      exfalso; exact evaluate_noReturnOrRaise w8b rfl m1 (by rw [h2]; exact hres)
    | none =>
      have hinv_m2 := (while_copyInv _ _ rfl (step_copy_loop8b b0 b1 b2 b3 b4 b5 b6 b7)
        m1.clock m1 m2 le_rfl hinv_m1 h2).1
      dsimp only at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases h3 : evaluateHOLFiniteState m2 w1b with ⟨r3, m3⟩
      rw [h3] at hres
      cases r3 with
      | some _ =>
        exfalso; exact evaluate_noReturnOrRaise w1b rfl m2 (by rw [h3]; exact hres)
      | none =>
        obtain ⟨hinv_m3, hfalse3⟩ := while_copyInv _ _ rfl (step_copy_loop1b b0)
          m2.clock m2 m3 le_rfl hinv_m2 h3
        dsimp only at hres ⊢
        obtain ⟨_, _, heff3, _, hn3, iw3, hi3, hle3, hdom3⟩ := hinv_m3
        have heq_in : iw3.toNat = n0.toNat := by
          simp only [evalHOLExact, hi3, hn3, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hfalse3
          by_cases hlt3 : iw3.toNat < n0.toNat
          · simp [hlt3] at hfalse3
          · omega
        have hret_eff : ByteEff s0 (evaluateHOLFiniteState m3 (.return (.const 0))).2 [(dst0.toNat, n0.toNat)] := by
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact, shapeOfHOLExact]
          split
          · exact heff3.locals_clock _ m3.clock
          · exact heff3
        exact ⟨hret_eff.locals_clock _ _, fun hpos => by rw [← heq_in] at hpos ⊢; exact hdom3 hpos⟩

theorem memzero_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  have hc0 : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := fun _ _ h => by injection h with h'; exact ⟨0, h'.symm⟩
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hc0 hc0 hc0 s0 dst0 n0 hc hG hdst hn hres

theorem memcpy_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    s0 dst0 n0 hc hG hdst hn hres

/-! ## 4. Composable `ByteEff` statement combinators & helper callees -/

theorem byteEff_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl}
    (ha : ByteEff s (evaluateHOLFiniteState s a).2 Rl)
    (hb : ∀ m, evaluateHOLFiniteState s a = (none, m) → ByteEff m (evaluateHOLFiniteState m b).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.seq a b)).2 Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact ha.trans (hb m hr)
  | some _ => exact ha

theorem byteEff_ite {F : Type} {s : PanSemStateFiniteExact 64 F} (cond : ExpHOL 64)
    {yes no : ProgHOL 64} {Rl : List Ivl}
    (hy : ByteEff s (evaluateHOLFiniteState s yes).2 Rl)
    (hn : ByteEff s (evaluateHOLFiniteState s no).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.ite cond yes no)).2 Rl := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · exact ByteEff.refl s Rl

theorem byteEff_dec {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ val,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      ByteEff (setVarHOLFinite name val s) (evaluateHOLFiniteState (setVarHOLFinite name val s) body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.dec name sh init body)).2 Rl := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ByteEff.refl s Rl
  · rename_i val hval
    split
    · exact ((ByteEff.refl s Rl).locals_clock _ s.clock).trans (hb val hval) |>.locals_clock _ _
    · exact ByteEff.refl s Rl

theorem byteEff_assign_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.assign .local name e)).2 Rl := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.return e)).2 Rl := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_skip {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s .skip).2 Rl := by
  rw [evaluateHOLFiniteState_skip]; exact ByteEff.refl s Rl

theorem byteEff_while {F : Type} (cond : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → GuestInv t →
      ByteEff t (evaluateHOLFiniteState t body).2 Rl)
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (hG : GuestInv s) :
    ByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact (ByteEff.refl s Rl).locals_clock _ s.clock
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have ih1 := hb (decClockHOLFinite s) hc hGd
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
        rw [hbr] at ih1 rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
        have heff1 : ByteEff s mid Rl := ((ByteEff.refl s Rl).locals_clock _ _).trans ih1
        have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
        cases r1 with
        | none => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
        | some res =>
          cases res with
          | «continue» => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
          | _ => exact heff1
    · exact ByteEff.refl s Rl
  · exact ByteEff.refl s Rl
termination_by s.clock

/-- Call wrapper for a `ByteEff` callee that only takes effect when `Resumes` holds
(or unconditionally on any non-timeout outcome). -/
def FunByteEff (fname : MlS)
    (argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)),
      entry.code = originalRuntimeCode → GuestInv entry →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, retShape) →
      (evaluateHOLFiniteState entry body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry body).1 →
      ByteEff entry (evaluateHOLFiniteState entry body).2 (argR vals entry.globals)

theorem call0_byteEff {F : Type} {fname : MlS}
    {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hsub : ∀ vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals s.globals, 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ByteEff.refl s Rl
  · simp only [hargs] at hnt hor ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ByteEff.refl s Rl
    · simp only [hl] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hor ⊢
        let entry := callEntryStateHOLFinite s callee
        have hGe : GuestInv entry := guestInv_callEntry s callee hG
        have hl_e : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hor ⊢
        have hntb : res ≠ some .timeOut := by intro h; subst h; simp at hnt
        have runSpec (hr : Resumes res) : ByteEff s post Rl := by
          have hb := hspec entry vals hc hGe hl_e (by dsimp only [entry]; rw [hrun]; exact hntb)
            (by dsimp only [entry]; rw [hrun]; exact hr)
          dsimp only [entry] at hb; rw [hrun] at hb
          exact (((ByteEff.refl s _).locals_clock _ _).trans hb).mono (hsub vals hargs)
        cases res with
        | none =>
          exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hor ⊢
            split
            · exact (runSpec (Or.inl ⟨v, rfl⟩)).locals_clock _ _
            · rename_i hbad
              rw [if_neg hbad] at hor
              exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | exception eid ev =>
            have hnot_trap : eid ≠ ofString "TrapErr" := by
              rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · simp at h
              · simp at h; obtain ⟨rfl, _⟩ := h; exact hne
            exact (runSpec (Or.inr ⟨eid, ev, rfl, hnot_trap⟩)).locals_clock _ _
          | _ =>
            exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
