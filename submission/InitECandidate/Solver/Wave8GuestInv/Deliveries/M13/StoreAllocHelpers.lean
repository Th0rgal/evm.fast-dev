import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.Core
import InitECandidate.Solver.GuestTrapOutcomes

/-! Self-contained byte-store (`panMemStoreByte_getByte_same`, `evaluate_storeByte_word`) and
allocator (`alloc` / `scratch_alloc`) post-state helpers for m13, using only prebuilt `.olean`s. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.M13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded

def memWordAt (mem : BitVec 64 → HolWordLab 64) (addr : BitVec 64) : BitVec 64 :=
  match mem addr with
  | .word w => w

def memByteAt (mem : BitVec 64 → HolWordLab 64) (be : Bool) (addr : BitVec 64) : UInt8 :=
  panGetByteHOL addr (memWordAt mem (panByteAlignHOL addr)) be

theorem panMemStoreByte_getByte_same {mem : BitVec 64 → HolWordLab 64}
    {dom : BitVec 64 → Prop} [DecidablePred dom] {be : Bool}
    {addr : BitVec 64} {b : UInt8} {mem' : BitVec 64 → HolWordLab 64}
    (hst : panMemStoreByteWord8HOL mem dom be addr (BitVec.ofNat 8 b.toNat) = some mem') :
    memByteAt mem' be addr = b ∧
    ∀ addr' : BitVec 64, addr' ≠ addr → memByteAt mem' be addr' = memByteAt mem be addr' := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hcell : mem (panByteAlignHOL addr) with
  | word cell =>
    rw [hcell] at hst
    split at hst
    · injection hst with hmem
      subst hmem
      have hb8 : b.toNat < 256 := b.toNat_lt_size
      have hb_mod : (BitVec.ofNat 8 b.toNat).toNat = b.toNat := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hb8
      have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
      have hK_le : byteBitIndex addr be + 8 ≤ 64 := by
        cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
      have hpow_div : ∀ (x y z K : Nat), y < 256 → z < 2 ^ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ K % 256 = y := by
        intro x y z K hy hz
        have hpK : 0 < 2 ^ K := Nat.two_pow_pos K
        have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z = z + (y + x * 256) * 2 ^ K := by
          rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.add_mul,
            Nat.mul_assoc x 256 (2 ^ K), Nat.mul_comm 256 (2 ^ K), ← Nat.mul_assoc]
          omega
        rw [h1, Nat.add_mul_div_right _ _ hpK, Nat.div_eq_of_lt hz, Nat.zero_add]
        omega
      have hpow_div_low : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → J + 8 ≤ K →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
        intro x y z K J _ _ hJK
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
      have hpow_div_high : ∀ (x y z K J : Nat), y < 256 → z < 2 ^ K → K + 8 ≤ J →
          (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
            (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
        intro x y z K J hy hz hKJ
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
      have hcell_high : ∀ J : Nat, byteBitIndex addr be + 8 ≤ J →
          ((cell.toNat / 2 ^ (byteBitIndex addr be + 8)) * 2 ^ (byteBitIndex addr be + 8)) / 2 ^ J =
            cell.toNat / 2 ^ J := by
        intro J hKJ
        have hdJ : 2 ^ J = 2 ^ (byteBitIndex addr be + 8) * 2 ^ (J - (byteBitIndex addr be + 8)) := by
          have hj_eq : J = (byteBitIndex addr be + 8) + (J - (byteBitIndex addr be + 8)) := by omega
          conv_lhs => rw [hj_eq]
          rw [Nat.pow_add]
        have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
        rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]
      have h256_pow : ∀ a : BitVec 64,
          (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
        intro a
        have : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by
          rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
        rw [this]
        cases be <;> simp [byteBitIndex, Nat.mul_comm 8]
      constructor
      · simp only [memByteAt, memWordAt, ↓reduceIte, hb_mod, panGetByteHOL]
        have heq_nat : (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
            256 ^ (if be then 64 / 8 - 1 - addr.toNat % (64 / 8) else addr.toNat % (64 / 8)) % 256 =
            b.toNat := by
          change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr.toNat % 8 else addr.toNat % 8) % 256 = b.toNat
          rw [hset_nat, h256_pow addr]
          exact hpow_div _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _))
        rw [heq_nat, UInt8.ofNat_toNat]
      · intro addr' hne
        by_cases hal : panByteAlignHOL addr' = panByteAlignHOL addr
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte, hb_mod, hcell, panGetByteHOL]
          have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
            intro hmeq; apply hne; apply BitVec.eq_of_toNat_eq
            have ha1 := panByteAlign_toNat64 addr'
            have ha2 := panByteAlign_toNat64 addr
            rw [hal] at ha1; omega
          have hidx_ne : byteBitIndex addr' be ≠ byteBitIndex addr be := by
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
          have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
              byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
            cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] at hidx_ne ⊢ <;> omega
          apply congrArg UInt8.ofNat
          change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
              256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
            cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
          rw [hset_nat, h256_pow addr']
          rcases hidx_sep with hlow | hhigh
          · rw [hpow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
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
            rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
            omega
          · rw [hpow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh,
              hcell_high _ hhigh]
        · simp only [memByteAt, memWordAt, hal, ↓reduceIte]
    · cases hst

theorem evaluate_storeByte_word {F : Type} {state : PanSemStateFiniteExact 64 F}
    {dstExp srcExp : ExpHOL 64} {addr val : BitVec 64}
    (hdst : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) dstExp = some (.val (.word addr)))
    (hsrc : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) srcExp = some (.val (.word val)))
    (hdom : state.memaddrs (panByteAlignHOL addr)) :
    ∃ mem',
      evaluateHOLFiniteState state (.storeByte dstExp srcExp) = (none, { state with memory := mem' }) ∧
      memByteAt mem' state.be addr = UInt8.ofNat (val.toNat % 256) ∧
      (∀ addr' : BitVec 64, addr' ≠ addr → memByteAt mem' state.be addr' = memByteAt state.memory state.be addr') ∧
      (∀ c : BitVec 64, c ≠ panByteAlignHOL addr → mem' c = state.memory c) := by
  rw [evaluateHOLFiniteState_storeByte]
  simp only [hdst, hsrc]
  cases hcell : state.memory (panByteAlignHOL addr) with
  | word cell =>
    have hst : @panMemStoreByteWord8HOL 64 _ state.memory state.memaddrs
        (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
        (BitVec.ofNat 8 val.toNat) =
        some (fun current => if current = panByteAlignHOL addr
          then .word (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 val.toNat).toNat) cell state.be)
          else state.memory current) := by
      simp [panMemStoreByteWord8HOL, hcell, hdom]
    have hb_eq : BitVec.ofNat 8 val.toNat = BitVec.ofNat 8 (UInt8.ofNat (val.toNat % 256)).toNat := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, UInt8.toNat_ofNat']
    have hst' : @panMemStoreByteWord8HOL 64 _ state.memory state.memaddrs
        (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
        (BitVec.ofNat 8 (UInt8.ofNat (val.toNat % 256)).toNat) =
        some (fun current => if current = panByteAlignHOL addr
          then .word (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 val.toNat).toNat) cell state.be)
          else state.memory current) := by
      rw [← hb_eq]; exact hst
    obtain ⟨hsame, hdiff⟩ := @panMemStoreByte_getByte_same state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be addr
      (UInt8.ofNat (val.toNat % 256)) _ hst'
    refine ⟨_, ?_, hsame, hdiff, fun c hc => if_neg hc⟩
    rw [hst]

theorem alloc_bounds_general (p n : BitVec 64)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hp_lt_264 : p.toNat < 2 ^ 64 := p.isLt
  have hn_lt_264 : n.toNat < 2 ^ 64 := n.isLt
  have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
  have hq_mod : q.toNat % 8 = 0 := by omega
  have hsub : (cMax - p).toNat = cMax.toNat - p.toNat := by rw [BitVec.toNat_sub]; omega
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, show (7 : BitVec 64).toNat = 7 from rfl]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
  exact ⟨by omega, hq_le, hq_mod⟩

theorem evaluate_alloc_body_general {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧
      out.2.globals = state.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      out.2.memory = state.memory ∧
      p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 := by
  dsimp only
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
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  set pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
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
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => intro retVal hret; exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only; rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only; rw [if_pos hsh_q]; dsimp only
    set qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780]
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
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => intro retVal hret; exact False.elim (hno_ret retVal hret)
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
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hb := alloc_bounds_general p n hp_le hcmp1 hcmp2
      intro retVal hret
      injection hret with hr; injection hr with hr'
      exact ⟨hr'.symm, rfl, rfl, hb⟩

theorem scratch_alloc_bounds_general (ptr frame size : BitVec 64)
    (hlo : frame.toNat ≤ ptr.toNat)
    (hcmp1 : ¬ ((ptr - frame).toNat < size.toNat))
    (hcmp2 : ¬ (((ptr - size) &&& ((0 : BitVec 64) - 8)).toNat < frame.toNat)) :
    let q := (ptr - size) &&& ((0 : BitVec 64) - 8)
    frame.toNat ≤ q.toNat ∧ q.toNat + size.toNat ≤ ptr.toNat ∧ q.toNat % 8 = 0 := by
  intro q
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by decide
  have hp : ptr.toNat < 2 ^ 64 := ptr.isLt
  have hf : frame.toNat < 2 ^ 64 := frame.isLt
  have hs : size.toNat < 2 ^ 64 := size.isLt
  have hsub_pf : (ptr - frame).toNat = ptr.toNat - frame.toNat := by rw [BitVec.toNat_sub]; omega
  have hsub_ps : (ptr - size).toNat = ptr.toNat - size.toNat := by rw [BitVec.toNat_sub]; omega
  have hq_eq : q.toNat = (ptr - size).toNat / 8 * 8 := and_neg8_toNat (ptr - size)
  exact ⟨Nat.le_of_not_lt hcmp2, by omega, by omega⟩

theorem evaluate_scratch_alloc_body_general {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p frame n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hlo : frame.toNat ≤ p.toNat)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    let q := (p - n) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word q) ∧
      out.2.globals = state.globals.update (ofString "scratch_ptr", .val (.word q)) ∧
      out.2.memory = state.memory ∧
      frame.toNat ≤ q.toNat ∧ q.toNat + n.toNat ≤ p.toNat ∧ q.toNat % 8 = 0 := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  set pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := hf_lookup
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (p - frame).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hf_g, hn_loc,
      wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
  by_cases hcmp1 : (p - frame).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState (BitVec.ofNat 64 7) hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState (BitVec.ofNat 64 7) w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => intro retVal hret; exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]; dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p - n) &&& ((0 : BitVec 64) - 8)
    have hq_word : (p - n) &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 8 &&& ~~~0#64) = q := by
      have : (BitVec.ofNat 64 0 - BitVec.ofNat 64 8 &&& ~~~0#64) = ((0 : BitVec 64) - 8) := by decide
      rw [this]
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
          .op .sub [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 8)]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) hq_word
    dsimp only; rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only; rw [if_pos hsh_q]; dsimp only
    set qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hf_g_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := hf_lookup
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
        some (.val (.word (if q.toNat < frame.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, hf_g_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : q.toNat < frame.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState (BitVec.ofNat 64 7) hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState (BitVec.ofNat 64 7) w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => intro retVal hret; exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 7)]) .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]; dsimp only
      have hp_g : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "q")))) =
          (some (.returned (.val (.word q))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hb := scratch_alloc_bounds_general p frame n hlo hcmp1 hcmp2
      intro retVal hret
      injection hret with hr; injection hr with hr'
      exact ⟨hr'.symm, rfl, rfl, hb⟩

end InitECandidate.Solver.Wave8GuestInv.M13
