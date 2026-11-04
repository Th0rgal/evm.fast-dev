import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.HeapPotential

/-! Self-contained byte-region write-frame and RLP/account-encoding return-bound helpers
for `P3_BuildMptIndexed` and `P3_ComputeStateRoot`. Imports only `ContractParts.C07` and
`HeapPotential`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.ByteFrame

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. `ByteRegionEffect` and `storeByte` / `store` frame primitives -/

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
    intro i hi ⟨hc1, hc2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno
    apply h.byte_frame b hb
    intro i hi ⟨hb1, hb2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    decide
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]; omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢; omega

theorem panByteAlign_toNat64 (a : BitVec 64) :
    (panByteAlignHOL a).toNat = a.toNat / 8 * 8 := by
  have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
  change (BitVec.ofNat 64 (a.toNat / 2 ^ ((64 : Nat) / 8).log2 *
    2 ^ ((64 : Nat) / 8).log2)).toNat = a.toNat / 8 * 8
  rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self _ 8) a.isLt)]

theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    sourceBase ≤ (panByteAlignHOL addr).toNat ∧ addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 33806089704 := by decide
  omega

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
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
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

theorem panGetByte_panSetByte_ne (addr' addr : BitVec 64) (b : UInt8) (cell : BitVec 64) (be : Bool)
    (hal : panByteAlignHOL addr' = panByteAlignHOL addr) (hne : addr' ≠ addr) :
    panGetByteHOL addr' (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be) be =
      panGetByteHOL addr' cell be := by
  have hb8 : b.toNat < 256 := b.toNat_lt_size
  have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
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
      rw [hmul] at hdm; omega
    conv_rhs => rw [hcell_eq]
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]; omega
  · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh]
    have hdJ : 2 ^ byteBitIndex addr' be =
        2 ^ (byteBitIndex addr be + 8) * 2 ^ (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by
      have hj_eq : byteBitIndex addr' be =
          (byteBitIndex addr be + 8) + (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by omega
      conv_lhs => rw [hj_eq]; rw [Nat.pow_add]
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
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
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
                      rw [heq] at hbt; subst hbt
                      exact hno i hi ⟨h1, h2⟩
                    let byte8 : UInt8 := UInt8.ofNat (BitVec.ofNat 8 v.toNat).toNat
                    have hbyte8 : byte8.toNat = (BitVec.ofNat 8 v.toNat).toNat := by simp [byte8]
                    rw [← hbyte8, panGetByte_panSetByte_ne _ _ byte8 cell s.be hal_eq hne]
                  · rw [if_neg hal_eq]
              · simp [hdom] at hst
          · simp
        · simp
        · simp
    · simp
    · simp

/-! ## 2. Exact `ByteRegionEffect` + return bound (`≤ 9`) of `rlp_encode_word` -/

theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

theorem lookup_rlp_put_be :
    originalRuntimeCode.lookup (ofString "rlp_put_be") =
      some ([(ofString "dst", .one), (ofString "v", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_put_be, .one) :=
  lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_be) rfl

theorem lookup_rlp_encode_word :
    originalRuntimeCode.lookup (ofString "rlp_encode_word") =
      some ([(ofString "dst", .one), (ofString "w", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_encode_word, .one) :=
  lookup_of_guestAst_getElem 123 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_encode_word) rfl

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem lsr8_bound {v n : BitVec 64} (h : v.toNat < 256 ^ (8 - n.toNat)) (hnle : n.toNat ≤ 8)
    (hv : v ≠ 0) :
    n.toNat < 8 ∧ (v >>> (8 : BitVec 64).toNat).toNat < 256 ^ (8 - (n.toNat + 1)) := by
  have hn_lt : n.toNat < 8 := by
    by_contra hge
    have heq : 8 - n.toNat = 0 := by omega
    rw [heq, Nat.pow_zero] at h
    exact hv (BitVec.eq_of_toNat_eq (by change v.toNat = 0; omega))
  refine ⟨hn_lt, ?_⟩
  have hsh : (v >>> (8 : BitVec 64).toNat).toNat = v.toNat / 256 := by
    change v.toNat >>> 8 = v.toNat / 256; rw [Nat.shiftRight_eq_div_pow]
  rw [hsh]
  have hpow : 256 ^ (8 - n.toNat) = 256 * 256 ^ (8 - (n.toNat + 1)) := by
    have he : 8 - n.toNat = 1 + (8 - (n.toNat + 1)) := by omega
    rw [he, Nat.pow_add, Nat.pow_one]
  rw [hpow] at h
  exact Nat.div_lt_of_lt_mul h

private def rlpBeLenLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
    (.seq
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))

private theorem eval_rlp_be_len_while {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (vw nw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "v") = some (.val (.word vw)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      nw.toNat ≤ 8 →
      vw.toNat < 256 ^ (8 - nw.toNat) →
      (evaluateHOLFiniteState s rlpBeLenLoop).1 ≠ some .timeOut →
      ∃ ll : BitVec 64,
        (evaluateHOLFiniteState s rlpBeLenLoop).1 = none ∧
        ll.toNat ≤ 8 ∧
        (vw ≠ 0 ∨ 0 < nw.toNat → 0 < ll.toNat) ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2.locals.lookup (ofString "n") = some (.val (.word ll)) ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2 =
          { s with locals := (evaluateHOLFiniteState s rlpBeLenLoop).2.locals,
                   clock := (evaluateHOLFiniteState s rlpBeLenLoop).2.clock } := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s vw nw hclk hv hn hn_le hv_lt hnt
    unfold rlpBeLenLoop at hnt ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) =
        some (.val (.word (if vw ≠ 0 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hv, wordCmpHOL]
    rw [hcond] at hnt ⊢; dsimp only at hnt ⊢
    by_cases hvz : vw = 0
    · rw [if_neg (not_not.mpr hvz)] at hnt ⊢
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨nw, rfl, hn_le, fun h => h.elim (fun hc => absurd hvz hc) id, hn, by cases s; rfl⟩
    · rw [if_pos hvz] at hnt ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnt ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt
      · rw [if_neg hk0] at hnt ⊢
        obtain ⟨hn_lt8, hv'_lt⟩ := lsr8_bound hv_lt hn_le hvz
        have hstep : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
              (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))) := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hv_d : (decClockHOLFinite s).locals.lookup (ofString "v") = some (.val (.word vw)) := hv
          have hn_d : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word nw)) := hn
          have hne_vn : ofString "v" ≠ ofString "n" := by decide
          simp [evalHOLExact, evalListHOLExact, hv_d, hn_d, hne_vn, Ne.symm hne_vn,
            isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
            setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            evaluateHOLFiniteState_assign, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hstep] at hnt ⊢; dsimp only at hnt ⊢
        set mid := setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
          (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))
        have hmid_clk : mid.clock < k := by simp [mid, setVarHOLFinite, decClockHOLFinite, hclk]; omega
        have hmid_v : mid.locals.lookup (ofString "v") = some (.val (.word (vw >>> (8 : BitVec 64).toNat))) := by
          have hne : ofString "n" ≠ ofString "v" := by decide
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
        have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word (nw + 1))) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hnw1 : (nw + 1).toNat = nw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (nw.toNat + 1) % 2 ^ 64 = _; omega
        obtain ⟨ll, hnone, hll8, hll_pos, hll_lk, hst_eq⟩ :=
          ih mid.clock hmid_clk mid (vw >>> (8 : BitVec 64).toNat) (nw + 1) rfl hmid_v hmid_n
            (by omega) (by rw [hnw1]; exact hv'_lt) hnt
        unfold rlpBeLenLoop at hnone hll_lk hst_eq
        refine ⟨ll, hnone, hll8, fun _ => hll_pos (Or.inr (by omega)), hll_lk, ?_⟩
        rw [hst_eq]; cases s; rfl

theorem eval_rlp_be_len_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vw : BitVec 64)
    (hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 ≠
      some .timeOut) :
    ∃ ll : BitVec 64,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 =
        some (.returned (.val (.word ll))) ∧
      ll.toNat ≤ 8 ∧
      (vw ≠ 0 → 0 < ll.toNat) ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_be_len =
      .dec (ofString "n") .one (.const 0)
        (.seq
          (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))))
          (.return (.var .local (ofString "n")))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "n") (.val (.word 0)) s
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    have hne : ofString "n" ≠ ofString "v" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hv]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hv_lt : vw.toNat < 256 ^ (8 - (0 : BitVec 64).toNat) := by
    have h256 : (256 ^ (8 - (0 : BitVec 64).toNat) : Nat) = 2 ^ 64 := by decide
    rw [h256]; exact vw.isLt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hl : evaluateHOLFiniteState s1 rlpBeLenLoop with ⟨rl, sl⟩
  have hnt_l : rl ≠ some .timeOut := by
    rintro rfl
    have hl' : evaluateHOLFiniteState s1
        (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
          (.seq
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
            (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))) =
        (some .timeOut, sl) := hl
    rw [hl'] at hnt; exact hnt rfl
  obtain ⟨ll, hnone, hll8, hll_pos, hsl_n, hsl_eq⟩ :=
    eval_rlp_be_len_while s1.clock s1 vw 0 rfl hs1_v hs1_n (by decide) hv_lt
      (by rw [hl]; exact hnt_l)
  rw [hl] at hnone hsl_n hsl_eq
  dsimp only at hnone hsl_n hsl_eq
  subst hnone
  have hl' : evaluateHOLFiniteState s1
      (.while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
        (.seq
          (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
          (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))) =
      (none, sl) := hl
  rw [hl']; dsimp only
  rw [evaluateHOLFiniteState_return]
  have hev_n : @evalHOLExact 64 F _ sl.toExact
      (fun a => Classical.propDecidable (sl.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word ll)) := by simp [evalHOLExact, hsl_n]
  rw [hev_n]; dsimp only
  have hsz : sizeOfShapeWithContextHOL sl.structs (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]; dsimp only
  refine ⟨ll, rfl, hll8, fun hnz => hll_pos (Or.inl hnz), ?_⟩
  rw [hsl_eq]; cases s; rfl

theorem eval_decCall_rlp_be_len {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp : ExpHOL 64) (vw : BitVec 64)
    (cont : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word vw)))
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).1 ≠ some .timeOut) :
    ∃ (ll : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      ll.toNat ≤ 8 ∧
      (vw ≠ 0 → 0 < ll.toNat) ∧
      mid.locals = s.locals.update (ofString lname, .val (.word ll)) ∧
      mid = { s with locals := mid.locals, clock := mid.clock } ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).1 =
        (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "rlp_be_len") [vExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
            (ofString lname, s.locals.lookup (ofString lname)) } := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [vExp] =
      some [.val (.word vw)] := by
    simp [evalListHOLFinite, evalListHOLExact, hev]
  have hlook := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_rlp_be_len) vw (by rw [hcode]; exact lookup_rlp_be_len)
  simp only [hargs, hlook] at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · simp [hclk0] at hnt
  · simp only [hclk0, ↓reduceIte] at hnt ⊢
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw)))
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word vw)) := by
      simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState
          (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw))))
          (sourceFnBody Guest.Software.guestFn_rlp_be_len) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨ll, hbr, hll8, hll_pos, hbs_eq⟩ :=
      eval_rlp_be_len_body entry vw hent_v (by rw [hb]; exact hnt_b)
    rw [hb] at hbr hbs_eq; dsimp only at hbr hbs_eq; subst hbr
    have hb' : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word vw))))
        (sourceFnBody Guest.Software.guestFn_rlp_be_len) =
        (some (.returned (.val (.word ll))), bs) := hb
    simp only [hb'] at hnt ⊢
    have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
        shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
      simp [shapeOfHOLExact, shapeEqHOL]
    simp only [hsh, ↓reduceIte] at hnt ⊢
    let mid := setVarHOLFinite (ofString lname) (.val (.word ll)) { bs with locals := s.locals }
    refine ⟨ll, mid, hll8, hll_pos, rfl, ?_, hnt, rfl, rfl⟩
    dsimp only [mid, setVarHOLFinite]; rw [hbs_eq]; cases s; rfl

theorem eval_rlp_put_be_body {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 v0 n0 : BitVec 64)
    (Rl : List Ivl)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hv : s.locals.lookup (ofString "v") = some (.val (.word v0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_put_be)
    (∀ rv, out.1 = some (.returned rv) →
      rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)) := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_put_be =
      .dec (ofString "i") .one (.var .local (ofString "n"))
        (.seq
          (.while (.cmp .lower (.const 0) (.var .local (ofString "i")))
            (.seq
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
              (.seq
                (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                            (.var .local (ofString "v")))
                (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))))))
          (.return (.const 0))) := rfl
  dsimp only
  rw [hb, evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev_n : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local (ofString "n")) =
      some (.val (.word n0)) := by simp [evalHOLExact, hn]
  have hsh_n : shapeEqHOL .one (shapeOfHOLExact (.val (.word n0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev_n] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh_n] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word n0)) s
  let P (t : PanSemStateFiniteExact 64 F) : Prop :=
    t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
    ∃ iw vw : BitVec 64,
      t.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      t.locals.lookup (ofString "v") = some (.val (.word vw)) ∧
      iw.toNat ≤ n0.toNat
  have hPs1 : P s1 := by
    refine ⟨?_, n0, v0, ?_, ?_, le_refl _⟩
    · have hne : ofString "i" ≠ ofString "dst" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · have hne : ofString "i" ≠ ofString "v" := by decide
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hv]
  let wcond : ExpHOL 64 := ExpHOL.cmp .lower (.const 0) (.var .local (ofString "i"))
  let wbody : ProgHOL 64 := ProgHOL.seq
    (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
    (.seq
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                  (.var .local (ofString "v")))
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))))
  have hwb_outcome : ∀ (t : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState t wbody).1 = none ∨ (evaluateHOLFiniteState t wbody).1 = some .error := by
    intro t; dsimp only [wbody]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
    split
    · exact Or.inr rfl
    · split
      · dsimp only
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_storeByte]
        split
        · split
          · split
            · dsimp only
              rw [evaluateHOLFiniteState_assign]
              split
              · exact Or.inr rfl
              · split <;> [exact Or.inl rfl; exact Or.inr rfl]
            · exact Or.inr rfl
          · exact Or.inr rfl
        · exact Or.inr rfl
      · exact Or.inr rfl
  have hloop_no_exn : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k →
      (∀ eid ev, (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.exception eid ev)) ∧
      (∀ val, (evaluateHOLFiniteState t (.while wcond wbody)).1 ≠ some (.returned val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond with _ | cv
      · simp
      · rcases cv with ⟨⟨cw⟩⟩ | _ | _
        · dsimp only
          split
          · split
            · simp
            · have hclk_b := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite t) wbody
              have hd_lt : (decClockHOLFinite t).clock < k := by simp [decClockHOLFinite, hclk]; omega
              have hwb := hwb_outcome (decClockHOLFinite t)
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite t) wbody with ⟨rb, sb⟩
              rw [hbo] at hwb hclk_b
              rcases hwb with rfl | rfl
              · exact ih sb.clock (lt_of_le_of_lt hclk_b hd_lt) sb rfl
              · simp
          · simp
        · simp
        · simp
  have hloop : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k → P t →
      (evaluateHOLFiniteState t (.while wcond wbody)).1 = none →
      ByteRegionEffect t (evaluateHOLFiniteState t (.while wcond wbody)).2 Rl := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk ⟨ht_dst, iw, vw, ht_i, ht_v, hiw_le⟩ hrun
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun ⊢
      have hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) wcond =
          some (.val (.word (if (0 : BitVec 64) < iw then 1 else 0))) := by
        simp [wcond, evalHOLFinite, evalHOLExact, ht_i, wordCmpHOL]
      rw [hc] at hrun ⊢; dsimp only at hrun ⊢
      by_cases hpos : (0 : BitVec 64) < iw
      · simp only [hpos, ↓reduceIte] at hrun ⊢
        have h10 : (1 : BitVec 64) ≠ 0 := by decide
        rw [if_pos h10] at hrun ⊢
        by_cases hk0 : t.clock = 0
        · simp [hk0] at hrun
        · rw [if_neg hk0] at hrun ⊢
          have hiw_pos : 0 < iw.toNat := by rw [BitVec.lt_def] at hpos; exact hpos
          have hiw1 : (iw - 1).toNat = iw.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 1 ≤ iw.toNat; omega))]; rfl
          let t0 := decClockHOLFinite t
          have ht0_i : t0.locals.lookup (ofString "i") = some (.val (.word iw)) := ht_i
          have hasg1 : evaluateHOLFiniteState t0
              (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0) := by
            rw [evaluateHOLFiniteState_assign]
            simp [evalHOLExact, evalListHOLExact, ht0_i, wordOpHOL, wordOp, valueIsWord, valueWord,
              isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
          let t1 := setVarHOLFinite (ofString "i") (.val (.word (iw - 1))) t0
          have ht1_dst : t1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
            have hne : ofString "i" ≠ ofString "dst" := by decide
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_dst]
          have ht1_i : t1.locals.lookup (ofString "i") = some (.val (.word (iw - 1))) := by
            simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have ht1_v : t1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
            have hne : ofString "i" ≠ ofString "v" := by decide
            simp [t1, t0, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht_v]
          have hclk_b := Flapjack.evaluateHOLFiniteState_clock_le t0 wbody
          have hd_lt : t0.clock < k := by simp [t0, decClockHOLFinite, hclk]; omega
          rcases hbo : evaluateHOLFiniteState t0 wbody with ⟨rb, sb⟩
          have hbo_raw : evaluateHOLFiniteState (decClockHOLFinite t) wbody = (rb, sb) := hbo
          simp only [hbo_raw] at hrun ⊢
          rw [hbo] at hclk_b
          have hbo' := hbo
          dsimp only [wbody] at hbo'
          rw [evaluateHOLFiniteState_seq_line780, hasg1] at hbo'
          dsimp only at hbo'
          rw [evaluateHOLFiniteState_seq_line780] at hbo'
          rcases hsb_step : evaluateHOLFiniteState t1
              (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                          (.var .local (ofString "v"))) with ⟨rsb, t2⟩
          rw [hsb_step] at hbo'
          cases rsb with
          | some r' =>
            dsimp only at hbo'
            injection hbo' with hr_eq _
            subst hr_eq
            exfalso
            have hr_err : r' = .error := by
              rw [evaluateHOLFiniteState_storeByte] at hsb_step
              split at hsb_step
              · split at hsb_step
                · split at hsb_step
                  · simp at hsb_step
                  · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
                · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
              · injection hsb_step with h1 _; injection h1 with h2; exact h2.symm
            subst hr_err; simp at hrun
          | none =>
            dsimp only at hbo'
            obtain ⟨heff_sb, ht2_loc⟩ := ByteRegionEffect.of_storeByte hsb_step (Rl := Rl) (fun addr hdst_ev _ => by
              have haddr_eq : addr = dst0 + (iw - 1) := by
                simp only [evalHOLExact, evalListHOLExact, ht1_dst, ht1_i, wordOpHOL, wordOp,
                  valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte,
                  List.foldr, BitVec.add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
                  HolWordLab.word.injEq] at hdst_ev
                simpa [BitVec.add_zero] using hdst_ev.symm
              subst haddr_eq
              obtain ⟨ivl, hivl, hlo, hhi⟩ := hin_ivl (by omega)
              have hadd_nat : (dst0 + (iw - 1)).toNat = dst0.toNat + (iw.toNat - 1) := by
                rw [BitVec.toNat_add, hiw1]; exact Nat.mod_eq_of_lt (by omega)
              exact ⟨ivl, hivl, by omega, by omega⟩)
            have ht2_v : t2.locals.lookup (ofString "v") = some (.val (.word vw)) := by
              rw [ht2_loc]; exact ht1_v
            have hasg2 : evaluateHOLFiniteState t2
                (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8))) =
                (none, setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) := by
              rw [evaluateHOLFiniteState_assign]
              simp [evalHOLExact, ht2_v, wordShiftHOL, isValidValueHOLExact, lookupKvarHOLExact,
                shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
            rw [hasg2] at hbo'
            injection hbo' with hr_eq hsb_eq
            subst hr_eq hsb_eq
            dsimp only at hrun ⊢
            have hPsb : P (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) := by
              refine ⟨?_, iw - 1, vw >>> (8 : BitVec 64).toNat, ?_, ?_, by omega⟩
              · have hne : ofString "v" ≠ ofString "dst" := by decide
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_loc, ht1_dst]
              · have hne : ofString "v" ≠ ofString "i" := by decide
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht2_loc, ht1_i]
              · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have heff_t_t1 : ByteRegionEffect t t1 Rl :=
              ByteRegionEffect.refl t Rl |>.with_locals_clock t1.locals t1.clock
            have heff_iter : ByteRegionEffect t (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2) Rl :=
              (heff_t_t1.trans heff_sb).with_locals_clock _ t2.clock
            have jih := ih (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) t2).clock
              (lt_of_le_of_lt hclk_b hd_lt) _ rfl hPsb hrun
            exact heff_iter.trans jih
      · simp only [hpos, ↓reduceIte] at hrun ⊢
        have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
        rw [if_neg h00]
        exact ByteRegionEffect.refl t Rl
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hwl : evaluateHOLFiniteState s1 (.while wcond wbody) with ⟨rwl, swl⟩
  have hno_exn := hloop_no_exn s1.clock s1 rfl
  rw [hwl] at hno_exn
  have hwl_raw : evaluateHOLFiniteState s1
      (.while (.cmp .lower (.const 0) (.var .local (ofString "i")))
        (.seq
          (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1]))
          (.seq
            (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
                        (.var .local (ofString "v")))
            (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))))) =
      (rwl, swl) := hwl
  simp only [hwl_raw] at hnt ⊢
  cases rwl with
  | none =>
    dsimp only at hnt ⊢
    have heff_wl := hloop s1.clock s1 rfl hPs1 (by rw [hwl])
    rw [hwl] at heff_wl; dsimp only at heff_wl
    rw [evaluateHOLFiniteState_return]
    have hev0 : @evalHOLExact 64 F _ swl.toExact
        (fun a => Classical.propDecidable (swl.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
    have hsz : sizeOfShapeWithContextHOL swl.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0]; dsimp only; rw [if_pos hsz]; dsimp only
    refine ⟨fun rv hrv => ?_, fun _ _ h => by simp at h⟩
    injection hrv with hrv'; injection hrv' with hrv''
    have heff_s_s1 : ByteRegionEffect s s1 Rl :=
      ByteRegionEffect.refl s Rl |>.with_locals_clock s1.locals s1.clock
    exact ⟨hrv''.symm, (heff_s_s1.trans heff_wl).with_locals_clock _ _⟩
  | some r =>
    dsimp only at hnt ⊢
    cases r with
    | timeOut => exact absurd rfl hnt
    | exception eid ev => exact absurd rfl (hno_exn.1 eid ev)
    | returned v => exact absurd rfl (hno_exn.2 v)
    | _ => exact ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem eval_call_rlp_put_be {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp vExp nExp : ExpHOL 64)
    (dst0 v0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.val (.word v0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hfit : dst0.toNat + n0.toNat ≤ 2 ^ 64)
    (hin_ivl : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "rlp_put_be") [dstExp, vExp, nExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, vExp, nExp] =
      some [.val (.word dst0), .val (.word v0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hv, hn]
  have hlook := pan_three_word_lookup s.code.lookup (ofString "rlp_put_be")
    (ofString "dst") (ofString "v") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_rlp_put_be) dst0 v0 n0
    (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_rlp_put_be)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "v", ValueHOL.val (.word v0))).update (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      have h2 : ofString "v" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_v : entry.locals.lookup (ofString "v") = some (.val (.word v0)) := by
      have h1 : ofString "n" ≠ ofString "v" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_put_be) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_rlp_put_be) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨hret, hexn⟩ := eval_rlp_put_be_body entry dst0 v0 n0 Rl hent_dst hent_v hent_n hfit hin_ivl
      (by rw [hb]; exact hnt_b)
    rw [hb] at hret hexn; dsimp only at hret hexn
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b⟩ := hret rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl⟩,
          fun h => False.elim (h rfl)⟩
      | _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

private theorem storeByte_local_dst_inv {F : Type}
    (t : PanSemStateFiniteExact 64 F) (val : ExpHOL 64)
    (hma : t.memaddrs = ordinaryDomain)
    (hnone : (evaluateHOLFiniteState t (.storeByte (.var .local (ofString "dst")) val)).1 = none) :
    ∃ dst0 : BitVec 64,
      t.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      dst0.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  rcases hd : t.locals.lookup (ofString "dst") with _ | dv
  · simp [evalHOLExact, hd] at hnone
  · rcases dv with ⟨⟨dst0⟩⟩ | _ | _
    · simp only [evalHOLExact, hd] at hnone
      split at hnone
      · split at hnone
        · rename_i m' hst
          unfold panMemStoreByteWord8HOL at hst
          dsimp only at hst
          cases hm : t.memory (panByteAlignHOL dst0) with
          | word cell =>
            by_cases hdom : t.memaddrs (panByteAlignHOL dst0)
            · exact ⟨dst0, rfl, (byteAlign_lt_heapEnd hma dst0 hdom).2⟩
            · simp [hm, hdom] at hst
        · simp at hnone
      · simp at hnone
    · simp [evalHOLExact, hd] at hnone
    · simp [evalHOLExact, hd] at hnone

private theorem storeByte_only_none_or_error {F : Type}
    (t : PanSemStateFiniteExact 64 F) (dst val : ExpHOL 64) :
    (evaluateHOLFiniteState t (.storeByte dst val)).1 = none ∨
      (evaluateHOLFiniteState t (.storeByte dst val)).1 = some .error := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

/-- When `rlp_encode_word` returns `retVal` normally from a `GuestInv` state,
it returns a word `kw ≤ 9` and has `ByteRegionEffect s post [(locN s "dst", 9)]`. -/
theorem rlp_encode_word_returned_bre {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (retVal : ValueHOL 64)
    (hcode : s.code = originalRuntimeCode)
    (hG : GuestInv s)
    (hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word) =
      (some (.returned retVal), post)) :
    ∃ kw : BitVec 64, retVal = .val (.word kw) ∧ kw.toNat ≤ 9 ∧
      ByteRegionEffect s post [(locN s "dst", 9)] := by
  let Rl : List Ivl := [(locN s "dst", 9)]
  have hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 ≠
      some .timeOut := by rw [hrun]; simp
  have hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 := by
    rw [hrun]; exact Or.inl ⟨retVal, rfl⟩
  have hb : sourceFnBody Guest.Software.guestFn_rlp_encode_word =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "w")) (.const 0))
          (.seq (.storeByte (.var .local (ofString "dst")) (.const 128)) (.return (.const 1)))
          .skip)
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "w")) (.const 128))
            (.seq (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) (.return (.const 1)))
            .skip)
          (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "w")]
            (.seq
              (.storeByte (.var .local (ofString "dst")) (.op .add [.const 128, .var .local (ofString "ll")]))
              (.seq
                (.call (some (none, none)) (ofString "rlp_put_be")
                  [.op .add [.var .local (ofString "dst"), .const 1],
                   .var .local (ofString "w"),
                   .var .local (ofString "ll")])
                (.return (.op .add [.const 1, .var .local (ofString "ll")])))))) := rfl
  have hrun0 := hrun
  rw [hb] at hnt hres hrun0
  have hw_ex : ∃ w0 : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w0)) := by
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hres
    rcases hw : s.locals.lookup (ofString "w") with _ | wv
    · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
    · rcases wv with ⟨⟨w0⟩⟩ | _ | _
      · exact ⟨w0, rfl⟩
      · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
      · simp [evalHOLExact, hw] at hres; exact False.elim (not_resumes_error hres)
  obtain ⟨w0, hw0⟩ := hw_ex
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres hrun0
  have hev_c1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "w")) (.const 0)) =
      some (.val (.word (if w0 = 0 then 1 else 0))) := by
    simp [evalHOLExact, hw0, wordCmpHOL]
  rw [hev_c1] at hnt hres hrun0; dsimp only at hnt hres hrun0
  by_cases hwz : w0 = 0
  · rw [if_pos hwz] at hnt hres hrun0
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10, evaluateHOLFiniteState_seq_line780] at hres hrun0
    rcases hsb : evaluateHOLFiniteState s (.storeByte (.var .local (ofString "dst")) (.const 128)) with ⟨rsb, s1⟩
    simp only [hsb] at hres hrun0
    rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.const 128) with hsn | hse
    · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hres hrun0
      obtain ⟨dst0, hdst0, _⟩ := storeByte_local_dst_inv s (.const 128) hG.memaddrs (by rw [hsb])
      have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hdst0]
      obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
        simp only [evalHOLExact, hdst0, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
        subst hdst_ev
        exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
      rw [evaluateHOLFiniteState_return] at hrun0
      simp only [evalHOLExact] at hrun0
      have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz] at hrun0
      injection hrun0 with hr hp
      injection hr with hret_eq
      injection hret_eq with hval_eq
      subst hp
      exact ⟨1#64, hval_eq.symm, by decide, heff1.with_locals_clock _ _⟩
    · rw [hsb] at hse; dsimp only at hse; subst hse
      exact False.elim (not_resumes_error hres)
  · rw [if_neg hwz, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres hrun0
    dsimp only at hnt hres hrun0
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt hres hrun0
    have hev_c2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.var .local (ofString "w")) (.const 128)) =
        some (.val (.word (if w0 < 128 then 1 else 0))) := by
      simp [evalHOLExact, hw0, wordCmpHOL]
    rw [hev_c2] at hnt hres hrun0; dsimp only at hnt hres hrun0
    by_cases hw128 : w0 < 128
    · rw [if_pos hw128] at hnt hres hrun0
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      rw [if_neg h10, evaluateHOLFiniteState_seq_line780] at hres hrun0
      rcases hsb : evaluateHOLFiniteState s
          (.storeByte (.var .local (ofString "dst")) (.var .local (ofString "w"))) with ⟨rsb, s1⟩
      simp only [hsb] at hres hrun0
      rcases storeByte_only_none_or_error s (.var .local (ofString "dst")) (.var .local (ofString "w")) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn; dsimp only at hres hrun0
        obtain ⟨dst0, hdst0, _⟩ := storeByte_local_dst_inv s (.var .local (ofString "w")) hG.memaddrs (by rw [hsb])
        have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hdst0]
        obtain ⟨heff1, _⟩ := ByteRegionEffect.of_storeByte hsb (Rl := Rl) (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hdst0, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
        rw [evaluateHOLFiniteState_return] at hrun0
        simp only [evalHOLExact] at hrun0
        have hsz : sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word 1) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [if_pos hsz] at hrun0
        injection hrun0 with hr hp
        injection hr with hret_eq
        injection hret_eq with hval_eq
        subst hp
        exact ⟨1#64, hval_eq.symm, by decide, heff1.with_locals_clock _ _⟩
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact False.elim (not_resumes_error hres)
    · rw [if_neg hw128, if_pos rfl, evaluateHOLFiniteState_skip] at hnt hres hrun0
      dsimp only at hnt hres hrun0
      let contProg : ProgHOL 64 :=
        .seq
          (.storeByte (.var .local (ofString "dst")) (.op .add [.const 128, .var .local (ofString "ll")]))
          (.seq
            (.call (some (none, none)) (ofString "rlp_put_be")
              [.op .add [.var .local (ofString "dst"), .const 1],
               .var .local (ofString "w"),
               .var .local (ofString "ll")])
            (.return (.op .add [.const 1, .var .local (ofString "ll")])))
      obtain ⟨ll, mid, hll8, _, hmid_loc, hmid_eq, hnt_m, hr_eq, hs_eq⟩ :=
        eval_decCall_rlp_be_len s "ll" (.var .local (ofString "w")) w0 contProg hcode
          (by simp [evalHOLExact, hw0]) hnt
      have hrun_mid1 : (evaluateHOLFiniteState mid contProg).1 = some (.returned retVal) := by
        rw [← hr_eq, hrun0]
      have hpost_eq : post = { (evaluateHOLFiniteState mid contProg).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid contProg).2.locals
            (ofString "ll", s.locals.lookup (ofString "ll")) } := by
        rw [← hs_eq, hrun0]
      rw [hr_eq] at hres
      dsimp only [contProg] at hnt_m hres hrun_mid1 hpost_eq
      have hmid_code : mid.code = originalRuntimeCode := by rw [hmid_eq]; exact hcode
      have hmid_ma : mid.memaddrs = ordinaryDomain := by rw [hmid_eq]; exact hG.memaddrs
      have hmid_ll : mid.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hmid_w : mid.locals.lookup (ofString "w") = some (.val (.word w0)) := by
        have hne : ofString "ll" ≠ ofString "w" := by decide
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hw0]
      have hmid_dst_lk : mid.locals.lookup (ofString "dst") = s.locals.lookup (ofString "dst") := by
        have hne : ofString "ll" ≠ ofString "dst" := by decide
        rw [hmid_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
      have heff_s_mid : ByteRegionEffect s mid Rl := by
        rw [hmid_eq]; exact ByteRegionEffect.refl s Rl |>.with_locals_clock mid.locals mid.clock
      rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres hrun_mid1 hpost_eq
      rcases hsb : evaluateHOLFiniteState mid
          (.storeByte (.var .local (ofString "dst"))
            (.op .add [.const 128, .var .local (ofString "ll")])) with ⟨rsb, s2⟩
      simp only [hsb] at hnt_m hres hrun_mid1 hpost_eq
      rcases storeByte_only_none_or_error mid (.var .local (ofString "dst"))
          (.op .add [.const 128, .var .local (ofString "ll")]) with hsn | hse
      · rw [hsb] at hsn; dsimp only at hsn; subst hsn
        dsimp only at hnt_m hres hrun_mid1 hpost_eq
        obtain ⟨dst0, hmid_dst, hdst_lt_he⟩ :=
          storeByte_local_dst_inv mid (.op .add [.const 128, .var .local (ofString "ll")])
            hmid_ma (by rw [hsb])
        have hs_dst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [← hmid_dst_lk]; exact hmid_dst
        have hdst_nat : locN s "dst" = dst0.toNat := by simp [locN, hs_dst]
        obtain ⟨heff_hdr, hs2_loc⟩ := ByteRegionEffect.of_storeByte (Rl := Rl) hsb (fun addr hdst_ev _ => by
          simp only [evalHOLExact, hmid_dst, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hdst_ev
          subst hdst_ev
          exact ⟨(locN s "dst", 9), List.mem_singleton.2 rfl, by rw [hdst_nat], by rw [hdst_nat]; omega⟩)
        have hs2_code : s2.code = originalRuntimeCode := heff_hdr.code.trans hmid_code
        have hs2_dst : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
          rw [hs2_loc]; exact hmid_dst
        have hs2_w : s2.locals.lookup (ofString "w") = some (.val (.word w0)) := by
          rw [hs2_loc]; exact hmid_w
        have hs2_ll : s2.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
          rw [hs2_loc]; exact hmid_ll
        have hhe_val : heapEnd = 33806089704 := by decide
        have hdst1_nat : (dst0 + 1).toNat = dst0.toNat + 1 := by
          rw [hhe_val] at hdst_lt_he
          rw [BitVec.toNat_add]
          change (dst0.toNat + 1) % 2 ^ 64 = _
          exact Nat.mod_eq_of_lt (by omega)
        have hfit : (dst0 + 1).toNat + ll.toNat ≤ 2 ^ 64 := by
          rw [hhe_val] at hdst_lt_he; omega
        rw [evaluateHOLFiniteState_seq_line780] at hnt_m hres hrun_mid1 hpost_eq
        rcases hc_put : evaluateHOLFiniteState s2
          (.call (some (none, none)) (ofString "rlp_put_be")
            [.op .add [.var .local (ofString "dst"), .const 1],
             .var .local (ofString "w"),
             .var .local (ofString "ll")]) with ⟨rc, s3⟩
        have hnt_put : rc ≠ some .timeOut := by
          rintro rfl; rw [hc_put] at hnt_m; exact hnt_m rfl
        have hput := eval_call_rlp_put_be s2
          (.op .add [.var .local (ofString "dst"), .const 1])
          (.var .local (ofString "w"))
          (.var .local (ofString "ll"))
          (dst0 + 1) w0 ll Rl hs2_code
          (by simp [evalHOLExact, evalListHOLExact, hs2_dst, wordOpHOL, wordOp, valueIsWord, valueWord])
          (by simp [evalHOLExact, hs2_w])
          (by simp [evalHOLExact, hs2_ll])
          hfit
          (fun _ => ⟨(locN s "dst", 9), List.mem_singleton.2 rfl,
            by dsimp only; rw [hdst_nat, hdst1_nat]; omega,
            by dsimp only; rw [hdst_nat, hdst1_nat]; omega⟩)
          (by rw [hc_put]; exact hnt_put)
        dsimp only at hput
        rw [hc_put] at hput
        simp only [hc_put] at hres hrun_mid1 hpost_eq
        cases rc with
        | some r =>
          dsimp only at hres
          exact False.elim (hput.2 (by simp) hres)
        | none =>
          dsimp only at hres hrun_mid1 hpost_eq
          obtain ⟨heff_put, hs3_loc⟩ := hput.1 rfl
          have hs3_ll : s3.locals.lookup (ofString "ll") = some (.val (.word ll)) := by
            rw [hs3_loc]; exact hs2_ll
          rw [evaluateHOLFiniteState_return] at hrun_mid1 hpost_eq
          have hev_ret : @evalHOLExact 64 F _ s3.toExact
              (fun a => Classical.propDecidable (s3.memaddrs a))
              (.op .add [.const 1, .var .local (ofString "ll")]) =
              some (.val (.word (1 + ll))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_ll, wordOpHOL, wordOp, valueIsWord, valueWord]
          rw [hev_ret] at hrun_mid1 hpost_eq; dsimp only at hrun_mid1 hpost_eq
          have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word (1 + ll)) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [if_pos hsz] at hrun_mid1 hpost_eq; dsimp only at hrun_mid1 hpost_eq
          injection hrun_mid1 with hr'
          injection hr' with hval_eq
          subst hpost_eq
          refine ⟨1 + ll, hval_eq.symm, ?_,
            (((heff_s_mid.trans heff_hdr).trans heff_put).with_locals_clock _ _).with_locals_clock _ _⟩
          have h1ll : ((1 : BitVec 64) + ll).toNat = 1 + ll.toNat := by
            rw [BitVec.toNat_add]; change (1 + ll.toNat) % 2 ^ 64 = _; omega
          omega
      · rw [hsb] at hse; dsimp only at hse; subst hse
        exact False.elim (not_resumes_error hres)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.ByteFrame
