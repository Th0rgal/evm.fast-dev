import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.NewScratchSpec
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Tables
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.AllocJournalStep
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkGetCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBalBase

/-! `fk_frame_open` and `ek_depth0_prepare`: the outermost frame is opened by `frame_open`
(kind 0) on top of `MsgReady`, and `depth0_prepare` keeps the EVM invariant. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

theorem lookup_compute_jumpdests :
    originalRuntimeCode.lookup (ofString "compute_jumpdests") =
      some ([(ofString "code", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_compute_jumpdests, .one) :=
  lookup_of_guestAst_getElem 463 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_jumpdests) rfl

/-! ## `memzero` on an aligned word range -/

/-! ## Loop rule: `Flw` body step, invariant plus failed test on normal exit -/

theorem while_flw {F : Type} (I : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → LoopActive cond s → s.clock ≠ 0 →
      Flw (decClockHOLFinite s) body (fun r t => r = none ∧ I t)) :
    ∀ s : PanSemStateFiniteExact 64 F, I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      I (evaluateHOLFiniteState s (.while cond body)).2 ∧
        CondFalse cond (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro s hI hnone
  have := while_inv2 I (fun _ => False) cond body ?_ s.clock s le_rfl hI hnone
  · rcases this with h | h
    · exact h
    · exact h.elim
  · intro x hx hact hc
    have hf := hstep x hx hact hc
    unfold Flw at hf
    refine ⟨fun hr => (hf (by rcases hr with h | h <;> simp [h, FlowR])).2, fun hb => ?_⟩
    have := (hf (by simp [hb, FlowR])).1
    rw [hb] at this
    cases this

/-! ## `memzero(dst, n)` for aligned `dst` and `n % 8 = 0` -/

/-- `m` with the aligned words of `[dst, dst + k)` set to zero. -/
def zeroOn (m : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (k : Nat) :
    BitVec 64 → HolWordLab 64 :=
  fun c => if dst.toNat ≤ c.toNat ∧ c.toNat < dst.toNat + k ∧ (c.toNat - dst.toNat) % 8 = 0
    then .word 0#64 else m c

theorem zeroOn_zero (m : BitVec 64 → HolWordLab 64) (dst : BitVec 64) : zeroOn m dst 0 = m := by
  funext c
  simp only [zeroOn]
  rw [if_neg (by omega)]

theorem zeroOn_step (m : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (k : Nat) (a : BitVec 64)
    (ha : a.toNat = dst.toNat + k) (hk : k % 8 = 0) :
    updW (zeroOn m dst k) a 0#64 = zeroOn m dst (k + 8) := by
  funext c
  simp only [updW, zeroOn]
  by_cases hc : c = a
  · subst hc
    rw [if_pos rfl, if_pos (by omega)]
  · have hne : c.toNat ≠ a.toNat := fun h => hc (BitVec.eq_of_toNat_eq h)
    rw [if_neg hc]
    by_cases h1 : dst.toNat ≤ c.toNat ∧ c.toNat < dst.toNat + k ∧ (c.toNat - dst.toNat) % 8 = 0
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem zeroOn_memW_lt (m : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (k : Nat)
    (c : BitVec 64) (hc : c.toNat < dst.toNat ∨ dst.toNat + k ≤ c.toNat) :
    zeroOn m dst k c = m c := by
  simp only [zeroOn]
  rw [if_neg (by omega)]

/-- Loop invariant of the two word loops of `memzero`. -/
def MzInv {F : Type} (s : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (L : HolFiniteMapExact MlS (ValueHOL 64)) (C : Nat) (iv : BitVec 64),
    t = NS s L s.globals (zeroOn s.memory dst iv.toNat) C ∧
    L.lookup (ofString "dst") = some (.val (.word dst)) ∧
    L.lookup (ofString "n") = some (.val (.word n)) ∧
    L.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat % 8 = 0 ∧ iv.toNat ≤ n.toNat

@[local simp] private theorem mzn1 : (ofString "i" = ofString "dst") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] private theorem mzn2 : (ofString "i" = ofString "n") = False := by
  simp only [eq_iff_iff, iff_false]; decide

private theorem mz_add_toNat (dst iv : BitVec 64) (k : Nat) (hk : k ≤ 32) (n : BitVec 64)
    (hle : iv.toNat + 32 ≤ n.toNat) (hn : n.toNat < 2 ^ 32) (hdn : dst.toNat + n.toNat < 2 ^ 64) :
    (dst + (iv + BitVec.ofNat 64 k)).toNat = dst.toNat + (iv.toNat + k) := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : (iv.toNat + k) % 2 ^ 64 = iv.toNat + k := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  exact Nat.mod_eq_of_lt (by omega)

private theorem mz_ev_addr {F : Type} (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) (dst iv : BitVec 64)
    (hd : L.lookup (ofString "dst") = some (.val (.word dst)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv))) (k : BitVec 64) :
    ev (NS s L s.globals M C) (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const k]) =
      some (.val (.word (dst + (iv + k)))) := by
  simp [ev, evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord]

private theorem mz_ev_addr0 {F : Type} (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) (dst iv : BitVec 64)
    (hd : L.lookup (ofString "dst") = some (.val (.word dst)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv))) :
    ev (NS s L s.globals M C) (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
      some (.val (.word (dst + iv))) := by
  simp [ev, evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord]

private theorem mz_ev_inc {F : Type} (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) (iv : BitVec 64)
    (hi : L.lookup (ofString "i") = some (.val (.word iv))) (k : BitVec 64) :
    ev (NS s L s.globals M C) (.op .add [.var .local (ofString "i"), .const k]) =
      some (.val (.word (iv + k))) := by
  simp [ev, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp, valueIsWord, valueWord]

private theorem mz_ev_zero {F : Type} (t : PanSemStateFiniteExact 64 F) :
    ev t (.const 0#64) = some (.val (.word 0#64)) := rfl

/-- The test `n >=+ i + k` (k ∈ {8, 32}) read off a `MzInv` state. -/
private theorem mz_cond_true {F : Type} (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) (n iv : BitVec 64) (k : Nat) (hk : k ≤ 32)
    (hn : L.lookup (ofString "n") = some (.val (.word n)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv)))
    (hn32 : n.toNat < 2 ^ 32) (hle : iv.toNat ≤ n.toNat) (w : BitVec 64)
    (hw : evalHOLFinite (NS s L s.globals M C) (h := fun x => Classical.propDecidable ((NS s L s.globals M C).memaddrs x))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 k)])) = some (.val (.word w)))
    (hw0 : w ≠ 0) : iv.toNat + k ≤ n.toNat := by
  rw [evalHOLFinite_eq_toExact] at hw
  simp [evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hw
  split at hw
  · rename_i h
    have := Nat.mod_eq_of_lt (show iv.toNat + k < 18446744073709551616 by omega)
    omega
  · exact absurd hw.symm hw0

private theorem mz_cond_false {F : Type} (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) (n iv : BitVec 64) (k : Nat) (hk : k ≤ 32)
    (hn : L.lookup (ofString "n") = some (.val (.word n)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv)))
    (hn32 : n.toNat < 2 ^ 32) (hle : iv.toNat ≤ n.toNat)
    (hc : CondFalse (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 k)])) (NS s L s.globals M C)) :
    n.toNat < iv.toNat + k := by
  unfold CondFalse at hc
  simp [evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hc
  have := Nat.mod_eq_of_lt (show iv.toNat + k < 18446744073709551616 by omega)
  omega

private theorem mz_step_w32 {F : Type} (s : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hn32 : n.toNat < 2 ^ 32) (hdn : dst.toNat + n.toNat < 2 ^ 64) :
    ∀ t : PanSemStateFiniteExact 64 F, MzInv s dst n t →
      LoopActive (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32#64])) t →
      t.clock ≠ 0 →
      Flw (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))
        (fun r t' => r = none ∧ MzInv s dst n t') := by
  intro t hI hact _
  obtain ⟨L, C, iv, rfl, hd, hn, hi, h8, hle⟩ := hI
  obtain ⟨w, hw, hw0⟩ := hact
  have hle32 : iv.toNat + 32 ≤ n.toNat := mz_cond_true s L _ C n iv 32 le_rfl hn hi hn32 hle w hw hw0
  show Flw (NS s L s.globals (zeroOn s.memory dst iv.toNat) (C - 1)) _ _
  apply Flw.seq
  refine Flw.storeW (dst + iv) 0#64 (mz_ev_addr0 s L _ _ dst iv hd hi) (mz_ev_zero _) ?_
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  show Flw (NS s L s.globals (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64) (C - 1)) _ _
  apply Flw.seq
  refine Flw.storeW (dst + (iv + 8#64)) 0#64 (mz_ev_addr s L _ _ dst iv hd hi 8#64) (mz_ev_zero _) ?_
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  show Flw (NS s L s.globals (updW (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64)
    (dst + (iv + 8#64)) 0#64) (C - 1)) _ _
  apply Flw.seq
  refine Flw.storeW (dst + (iv + 16#64)) 0#64 (mz_ev_addr s L _ _ dst iv hd hi 16#64) (mz_ev_zero _) ?_
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  show Flw (NS s L s.globals (updW (updW (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64)
    (dst + (iv + 8#64)) 0#64) (dst + (iv + 16#64)) 0#64) (C - 1)) _ _
  apply Flw.seq
  refine Flw.storeW (dst + (iv + 24#64)) 0#64 (mz_ev_addr s L _ _ dst iv hd hi 24#64) (mz_ev_zero _) ?_
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  show Flw (NS s L s.globals (updW (updW (updW (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64)
    (dst + (iv + 8#64)) 0#64) (dst + (iv + 16#64)) 0#64) (dst + (iv + 24#64)) 0#64) (C - 1)) _ _
  apply Flw.assign
  intro v hv
  rw [mz_ev_inc s L _ _ iv hi 32#64] at hv
  cases hv
  have h32 : (iv + 32#64).toNat = iv.toNat + 32 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
  refine ⟨rfl, L.update (ofString "i", .val (.word (iv + 32#64))), C - 1, iv + 32#64, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ha0 : (dst + iv).toNat = dst.toNat + iv.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    show NS s _ s.globals (updW (updW (updW (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64)
      (dst + (iv + 8#64)) 0#64) (dst + (iv + 16#64)) 0#64) (dst + (iv + 24#64)) 0#64) (C - 1) =
      NS s _ s.globals _ (C - 1)
    rw [zeroOn_step _ _ _ _ ha0 h8,
      zeroOn_step _ _ _ _ (mz_add_toNat dst iv 8 (by omega) n hle32 hn32 hdn) (by omega),
      zeroOn_step _ _ _ _ (mz_add_toNat dst iv 16 (by omega) n hle32 hn32 hdn) (by omega),
      zeroOn_step _ _ _ _ (mz_add_toNat dst iv 24 (by omega) n hle32 hn32 hdn) (by omega), h32]
    rfl
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hd]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hn]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [h32]; omega
  · rw [h32]; omega

private theorem mz_step_w8 {F : Type} (s : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hn32 : n.toNat < 2 ^ 32) (hdn : dst.toNat + n.toNat < 2 ^ 64) :
    ∀ t : PanSemStateFiniteExact 64 F, MzInv s dst n t →
      LoopActive (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8#64])) t →
      t.clock ≠ 0 →
      Flw (decClockHOLFinite t)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))
        (fun r t' => r = none ∧ MzInv s dst n t') := by
  intro t hI hact _
  obtain ⟨L, C, iv, rfl, hd, hn, hi, h8, hle⟩ := hI
  obtain ⟨w, hw, hw0⟩ := hact
  have hle8 : iv.toNat + 8 ≤ n.toNat := mz_cond_true s L _ C n iv 8 (by omega) hn hi hn32 hle w hw hw0
  show Flw (NS s L s.globals (zeroOn s.memory dst iv.toNat) (C - 1)) _ _
  apply Flw.seq
  refine Flw.storeW (dst + iv) 0#64 (mz_ev_addr0 s L _ _ dst iv hd hi) (mz_ev_zero _) ?_
  intro _
  refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
  show Flw (NS s L s.globals (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64) (C - 1)) _ _
  apply Flw.assign
  intro v hv
  rw [mz_ev_inc s L _ _ iv hi 8#64] at hv
  cases hv
  have h8' : (iv + 8#64).toNat = iv.toNat + 8 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
  refine ⟨rfl, L.update (ofString "i", .val (.word (iv + 8#64))), C - 1, iv + 8#64, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ha0 : (dst + iv).toNat = dst.toNat + iv.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    show NS s _ s.globals (updW (zeroOn s.memory dst iv.toNat) (dst + iv) 0#64) (C - 1) =
      NS s _ s.globals _ (C - 1)
    rw [zeroOn_step _ _ _ _ ha0 h8, h8']
    rfl
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hd]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE, hn]
  · simp [HolFiniteMapExact.lookup_update, FUPDATE]
  · rw [h8']; omega
  · rw [h8']; omega

/-- A `while` whose test evaluates to `0` is a no-op. -/
private theorem while_exit {F : Type} (st : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (body : ProgHOL 64) (hcond : CondFalse cond st) :
    evaluateHOLFiniteState st (.while cond body) = (none, st) := by
  have hcond' : evalHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x))
      cond = some (.val (.word 0#64)) := by
    rw [evalHOLFinite_eq_toExact]; exact hcond
  rw [evaluateHOLFiniteState_while_total, hcond']
  simp

/-- The word phase of `memzero` (aligned `dst`): both word loops, from `i = 0`. -/
private theorem mz_word_phase {F : Type} (s : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hn32 : n.toNat < 2 ^ 32) (hdn : dst.toNat + n.toNat < 2 ^ 64) (hn8 : n.toNat % 8 = 0)
    (t : PanSemStateFiniteExact 64 F) (hI : MzInv s dst n t) :
    let w32 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32#64]))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))
    let w8 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8#64]))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8#64])))
    (evaluateHOLFiniteState t (.seq w32 w8)).1 = none →
      ∃ L C, (evaluateHOLFiniteState t (.seq w32 w8)).2 = NS s L s.globals (zeroOn s.memory dst n.toNat) C ∧
        L.lookup (ofString "dst") = some (.val (.word dst)) ∧
        L.lookup (ofString "n") = some (.val (.word n)) ∧
        L.lookup (ofString "i") = some (.val (.word n)) := by
  intro w32 w8 hnone
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases h1 : evaluateHOLFiniteState t w32 with ⟨r1, t1⟩
  rw [h1] at hnone
  simp only [h1]
  dsimp only at hnone ⊢
  rcases r1 with _ | r1
  · have hw32 := while_flw (MzInv s dst n) _ _ (mz_step_w32 s dst n hn32 hdn) t hI (by rw [h1])
    rw [h1] at hw32
    obtain ⟨hI1, _⟩ := hw32
    have hw8 := while_flw (MzInv s dst n) _ _ (mz_step_w8 s dst n hn32 hdn) t1 hI1 hnone
    obtain ⟨⟨L, C, iv, ht2, hd, hn, hi, h8, hle⟩, hcf⟩ := hw8
    rw [ht2] at hcf
    have hlt := mz_cond_false s L _ C n iv 8 (by omega) hn hi hn32 hle hcf
    have hiv : iv = n := by
      apply BitVec.eq_of_toNat_eq; omega
    subst hiv
    exact ⟨L, C, ht2, hd, hn, hi⟩
  · cases hnone

private theorem NoRet.storeByte' {d e : ExpHOL 64} : NoRet (.storeByte d e) := by
  intro F st v
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split <;> simp
    · simp
  · simp

private theorem NoRet.while' {c : ExpHOL 64} {b : ProgHOL 64} (hb : NoRet b) : NoRet (.while c b) :=
  fun {_F} st v => while_noRet c b (fun s v => hb s v) st.clock st le_rfl v

private theorem mz_align_cond {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat) (dst : BitVec 64)
    (hd : L.lookup (ofString "dst") = some (.val (.word dst))) (hal : dst.toNat % 8 = 0) :
    ev (NS s L s.globals M C)
      (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64)) =
      some (.val (.word 1#64)) := by
  have hand0 : dst &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change dst.toNat &&& (2 ^ 3 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact hal
  have h7top : wordOpHOL (width := 64) .and [dst, 7#64] = some 0#64 := by
    simp only [wordOpHOL, wordOp, List.foldr]
    have h1 : AndOp.and 7#64 (~~~(0 : BitVec 64)) = 7#64 := by decide
    have h2 : AndOp.and dst 7#64 = 0#64 := hand0
    rw [h1, h2]
  simp only [ev, evalHOLExact, evalListHOLExact, NS, hd, valueIsWord, valueWord, List.all, List.map,
    Option.map, Bool.and_self, ↓reduceIte, h7top, Compiler.Encoders.Asm.wordCmpHOL]
  rfl

private theorem mz_cond_false_of {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (n iv : BitVec 64) (k : Nat) (hk : k ≤ 32)
    (hn : L.lookup (ofString "n") = some (.val (.word n)))
    (hi : L.lookup (ofString "i") = some (.val (.word iv)))
    (hn32 : n.toNat < 2 ^ 32) (hle : iv.toNat ≤ n.toNat) (hlt : n.toNat < iv.toNat + k) :
    CondFalse (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 k)])) (NS s L s.globals M C) := by
  unfold CondFalse
  simp [evalHOLExact, evalListHOLExact, hn, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
  have := Nat.mod_eq_of_lt (show iv.toNat + k < 18446744073709551616 by omega)
  omega

private theorem mz_tail_cond_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : BitVec 64 → HolWordLab 64) (C : Nat)
    (n : BitVec 64)
    (hn : L.lookup (ofString "n") = some (.val (.word n)))
    (hi : L.lookup (ofString "i") = some (.val (.word n))) :
    CondFalse (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) (NS s L s.globals M C) := by
  unfold CondFalse
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL]

/-- `memzero(dst, n)` with `dst` word-aligned and `n` a multiple of `8` (and small): returns `0`,
memory becomes `zeroOn s.memory dst n`, globals/code/memaddrs unchanged. -/
theorem memzero_run {F : Type} (s : PanSemStateFiniteExact 64 F) (dst n : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hal : dst.toNat % 8 = 0) (hn8 : n.toNat % 8 = 0)
    (hn32 : n.toNat < 2 ^ 32) (hdn : dst.toNat + n.toNat < 2 ^ 64) :
    Ret s (sourceFnBody Guest.Software.guestFn_memzero) (fun v post =>
      v = .val (.word 0#64) ∧ ∃ L C, post = NS s L s.globals (zeroOn s.memory dst n.toNat) C) := by
  have hb : sourceFnBody Guest.Software.guestFn_memzero =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_memzero).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.dec
  intro v0 hv0
  have hv0' : v0 = .val (.word 0#64) := by
    simp [ev, evalHOLExact] at hv0; exact hv0.symm
  subst hv0'
  let L0 := s.locals.update (ofString "i", .val (.word 0#64))
  have hL0d : L0.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [L0, HolFiniteMapExact.lookup_update, FUPDATE, hd]
  have hL0n : L0.lookup (ofString "n") = some (.val (.word n)) := by
    simp [L0, HolFiniteMapExact.lookup_update, FUPDATE, hn]
  have hL0i : L0.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [L0, HolFiniteMapExact.lookup_update, FUPDATE]
  show Ret (NS s L0 s.globals s.memory s.clock) _ _
  refine seq_ite_true 1#64 (mz_align_cond s L0 _ _ dst hL0d hal) (by decide) (Ret.seq ?_ ?_)
  · intro v hv
    exact absurd hv (NoRet.seq (NoRet.while' (NoRet.seq NoRet.store' (NoRet.seq NoRet.store'
      (NoRet.seq NoRet.store' (NoRet.seq NoRet.store' NoRet.assign)))))
      (NoRet.while' (NoRet.seq NoRet.store' NoRet.assign)) _ v)
  · intro t ht
    have hI0 : MzInv s dst n (NS s L0 s.globals s.memory s.clock) :=
      ⟨L0, s.clock, 0#64, by rw [show (0#64 : BitVec 64).toNat = 0 from rfl, zeroOn_zero],
        hL0d, hL0n, hL0i, rfl, by simp⟩
    obtain ⟨L, C, ht2, hLd, hLn, hLi⟩ :=
      mz_word_phase s dst n hn32 hdn hn8 _ hI0 (by rw [ht])
    rw [ht] at ht2
    dsimp only at ht2
    subst ht2
    refine Ret.seq ?_ ?_
    · intro v hv
      exact absurd hv (NoRet.while' (NoRet.seq NoRet.storeByte' (NoRet.seq NoRet.storeByte'
        (NoRet.seq NoRet.storeByte' (NoRet.seq NoRet.storeByte' (NoRet.seq NoRet.storeByte'
        (NoRet.seq NoRet.storeByte' (NoRet.seq NoRet.storeByte' (NoRet.seq NoRet.storeByte'
        NoRet.assign)))))))) _ v)
    · intro t1 ht1
      rw [while_exit _ _ _ (mz_cond_false_of s L _ C n n 8 (by omega) hLn hLi hn32 le_rfl (by omega))]
        at ht1
      cases ht1
      refine Ret.seq ?_ ?_
      · intro v hv
        exact absurd hv (NoRet.while' (NoRet.seq NoRet.storeByte' NoRet.assign) _ v)
      · intro t2 ht2
        rw [while_exit _ _ _ (mz_tail_cond_false s L _ C n hLn hLi)] at ht2
        cases ht2
        apply Ret.ret
        intro val hval
        have hval' : val = .val (.word 0#64) := by
          simp [ev, evalHOLExact] at hval; exact hval.symm
        subst hval'
        exact ⟨rfl, _, C, rfl⟩

/-! ## Single-frame assembly for `fk_frame_open`

After `frame_open(msg, 0)` the chain is the one frame `(ev, cur_cont)` with kind `0`. The
following lemmas assemble `EvmMsgReady` from explicit facts about that one frame, so that a body
run of `frame_open` only has to deliver the head-frame facts. -/

theorem evmChain_single {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h0 : memW s (globN s "cur_cont" + 16) = 0) :
    evmChain s = [(globN s "ev", globN s "cur_cont")] := by
  rw [evmChain_cons, if_pos h0]

theorem evmInvAt_single {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (h0 : memW s (globN s "cur_cont" + 16) = 0)
    (hWT : WorldTyped s S)
    (hWF : FrameWF s S (globN s "ev", globN s "cur_cont"))
    (hPD : (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj)
    (hTF : ∀ o ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j)
    (hAT : AvoidsTries s S (frameObjects s (globN s "ev", globN s "cur_cont")))
    (hRO : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s [(globN s "ev", globN s "cur_cont")])
      (journalRoleSlots s))
    (hG : memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) + 1 < 2 ^ 64) :
    EvmInvAt s S := by
  have hch := evmChain_single s h0
  refine ⟨hWT, ?_⟩
  simp only [hch]
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRO, ?_⟩
  · simp [maxChain]
  · exact ⟨(globN s "ev", globN s "cur_cont"), by simp, h0⟩
  · intro ec hec; simp at hec; subst hec; exact hWF
  · intro ec hec; simp at hec
  · intro i hi; simp at hi
  · simpa using hPD
  · intro ec hec; simp at hec; subst hec; exact hTF
  · simpa using hAT
  · intro i hi; simp at hi
  · simpa using hG

theorem evmMsgReady_of_single {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hAR : ArenaReady s)
    (h0 : memW s (globN s "cur_cont" + 16) = 0)
    (hWT : WorldTyped s S)
    (hWF : FrameWF s S (globN s "ev", globN s "cur_cont"))
    (hPD : (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj)
    (hTF : ∀ o ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
      (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj o i) ∧ ∀ j ∈ fixedObjects s, Disj o j)
    (hAT : AvoidsTries s S (frameObjects s (globN s "ev", globN s "cur_cont")))
    (hRO : RolesOK s S (worldRoleSlots s ++ frameRoleSlots s [(globN s "ev", globN s "cur_cont")])
      (journalRoleSlots s))
    (hG : memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) + 1 < 2 ^ 64) :
    EvmMsgReady s :=
  ⟨hAR, S, evmInvAt_single s S h0 hWT hWF hPD hTF hAT hRO hG,
    hWF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- `fk_frame_open` reduced to a `Ret` run of the `frame_open` body from a `FrameOpenReady` entry
with word parameters `msg = m`, `kind = k`. -/
theorem fk_frame_open_of_ret
    (hrun : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      FrameOpenReady s → ∀ (m k : BitVec 64),
      s.locals.lookup (ofString "msg") = some (.val (.word m)) →
      s.locals.lookup (ofString "kind") = some (.val (.word k)) → k.toNat = 0 →
      Ret s (sourceFnBody Guest.Software.guestFn_frame_open) (fun _ post => EvmMsgReady post)) :
    KeepsOn FrameOpenReady EvmMsgReady (ofString "frame_open") := by
  refine ⟨_, _, _, lookup_frame_open, fun s hcode hP hex _hnt hr => ?_⟩
  obtain ⟨w1, hw1⟩ := hex
  obtain ⟨⟨m, hm⟩, ⟨k, hk⟩⟩ := fo_param_words_two s (p1 := "msg") (p2 := "kind") (by decide)
    lookup_frame_open ⟨w1, hw1⟩
  have hlk : locN s "kind" = k.toNat := by unfold locN; rw [hk]
  obtain ⟨v, hv⟩ := frame_open_resumes_returned s hcode hw1 hr
  exact hrun s hcode hP m k hm hk (by rw [← hlk]; exact hP.2) v hv

/-! ## `depth0_prepare`: lookup and contract plumbing -/

theorem lookup_depth0_prepare :
    originalRuntimeCode.lookup (ofString "depth0_prepare") =
      some ([], sourceFnBody Guest.Software.guestFn_depth0_prepare, .one) :=
  lookup_of_guestAst_getElem 587 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_depth0_prepare) rfl

/-- `ek_depth0_prepare` reduced to the body: every resuming, non-timeout run of the
`depth0_prepare` body from an `EvmMsgReady` entry is an `EvmStep`. -/
theorem ek_depth0_prepare_of_body
    (hrun : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmMsgReady s →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_depth0_prepare)).1 ≠
        some .timeOut →
      Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_depth0_prepare)).1 →
      EvmStep ["heap_ptr", "journal_n", "scratch_ptr"] s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_depth0_prepare)).2) :
    EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "depth0_prepare") :=
  ⟨_, _, _, lookup_depth0_prepare, fun s hcode hP _hex hnt hr => hrun s hcode hP hnt hr⟩

/-- The owned message record of `EvmMsgReady` is an `EvmAvoids` region: writes through it
(`msg+48` in `depth0_prepare`, `msg+112`/`msg+120` in `prepare_dispatch`) are byte-region effects
that `ByteRegionEffect.to_evmStep_avoids` turns into an `EvmStep`. -/
theorem evmAvoids_msg_of_evmMsgReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : EvmMsgReady s) :
    EvmAvoids (fun s => [(memW s (globN s "ev" + 112), 176)]) s := by
  obtain ⟨hAR, S, hInv, hAl, hW, hT, hFx, hFr, Nd, hTr, hNd⟩ := h
  refine ⟨hAR, S, hInv, Nd, hTr, ?_⟩
  intro o ho j hj
  simp only [List.mem_singleton] at ho
  subst ho
  rcases List.mem_append.1 hj with hjw | hjf
  · have hjo := R13Shards.worldTypedIvls_sub_worldOwned hjw
    unfold worldOwned at hjo
    rcases List.mem_append.1 hjo with hjo | hjn
    · rcases List.mem_append.1 hjo with hjt | hjx
      · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 hjt
        exact hT t ht j hi
      · exact hFx j hjx
    · exact hNd _ (List.mem_singleton.2 rfl) j hjn
  · obtain ⟨os, hos, hjo⟩ := List.mem_flatten.1 hjf
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hos
    exact hFr ec hec j hjo


/-! ## Head-record field store: `ev+192`/`ev+200` writes keep `EvmInv` -/

section HeadStore
open R10Shards.GbodyProcessMsg

/-- A single word store into the head record at `ev+192` (state-gas spilled) or `ev+200`
(auth state-gas used) keeps `EvmInvAt` for the same table set, the chain, and every owned
message, provided the head's `gas + spilled` does not grow. -/
theorem evmInvAt_store_ev_gas {F : Type} {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInvAt : EvmInvAt s S) {x : BitVec 64} {k : Nat} (hk : k = 192 ∨ k = 200)
    (hx_eq : x.toNat = globN s "ev" + k)
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    ArenaReady post ∧ EvmInvAt post S ∧ evmChain post = evmChain s ∧
      (∀ m, MsgOwned s S m → MsgOwned post S m) ∧
      (∀ k', k' + 8 ≤ 280 → k' ≠ 192 → k' ≠ 200 →
        memW post (globN s "ev" + k') = memW s (globN s "ev" + k')) := by
  obtain ⟨hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInvAt
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  have hch_cons_ex : ∃ tail, evmChain s = (globN s "ev", globN s "cur_cont") :: tail := by
    unfold evmChain
    exact ⟨_, rfl⟩
  obtain ⟨chTail, hch_cons⟩ := hch_cons_ex
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [hch_cons]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb_e0, hb_c0, _⟩ := frameWF_bounds hhead_FW
  dsimp only at hb_e0
  have hcont_in_scr : Inside (globN s "ev", 280) (globN s "scratch_ptr") scratchEnd :=
    (hhead_FW.1 (globN s "ev", 280) (by simp)).1
  have hx_in_cont : Inside (x.toNat, 8) (globN s "ev") (globN s "ev" + 280) := by
    unfold Inside; dsimp only; omega
  have hcont_fo : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hcont_fl : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
    rw [List.mem_flatten]
    exact ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hcont_fo⟩
  have hdisj_wti_of_nd : ∀ {Nd : List Nat},
      (∀ j ∈ nodeExtents s Nd, Disj (globN s "ev", 280) j) →
      ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8) := by
    intro Nd hnd_c j hj
    apply disj_of_inside_right (j' := (globN s "ev", 280)) hx_in_cont
    unfold worldTypedIvls at hj
    simp only [List.mem_append] at hj
    rcases hj with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact ((hFO_disj _ hhead_mem _ hcont_fo).1 t ht j hfp).flip
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ (typedRecord_mem_fixedObjects s hr)).flip
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
          32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right; simp
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_j).flip
    · have hfix_bo : j ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h4)))
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_bo).flip
    · have hfix_bal : j ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append.2 (Or.inr h5)
      exact ((hFO_disj _ hhead_mem _ hcont_fo).2 _ hfix_bal).flip
    · exact (hnd_c j h6).flip
  have hstep_at := worldTypedWith_store_word_disj hAs hx_dom hpost hWT
    (hdisj_wti_of_nd (fun j hj => hAT_at _ hcont_fl j hj))
  obtain ⟨hAp, hWT_post, hfix_eq, hnd_at_eq, hwrs_eq, hjr_eq, htab_fp_hdr, hworldRefs_eq⟩ := hstep_at
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hpost.2.2.2.2.2.1]
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 → a ≠ globN s "ev" + k → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    have hbv_ne : BitVec.ofNat 64 a ≠ x := by
      intro heq
      have h1 : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt ha
      rw [heq, hx_eq] at h1
      exact hne h1.symm
    rw [hpost.2.2.2.2.2.2 _ hbv_ne]
  have hx_ge_hl : heapLimit ≤ x.toNat := by
    have hsep : heapLimit ≤ scratchStart := by decide
    have hss : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
    have hsc : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hAs.2.2.2.2.1
    have hc_lo : globN s "scratch_ptr" ≤ globN s "ev" := hcont_in_scr.1
    omega
  have hm_heap : ∀ a : Nat, a < heapLimit → memW post a = memW s a := by
    intro a ha
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    exact hmemW_ne a (by omega) (by omega)
  have hnd_disj_any : ∀ {Nd : List Nat}, NodeHeap s Nd → ∀ j ∈ nodeExtents s Nd, Disj j (x.toNat, 8) := by
    intro Nd hN j hj
    unfold nodeExtents at hj
    obtain ⟨n, hn, hj_np⟩ := List.mem_flatMap.1 hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_np
    rcases hj_np with rfl | rfl
    · have hin := (hN.1 n hn).2.2.1
      exact Or.inr (Or.inr (Or.inl (le_trans hin.2 hx_ge_hl)))
    · unfold nodePath
      split_ifs with hcond
      · rcases (hN.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, _, hin, _⟩
        · exact absurd h0 hcond.2
        · exact Or.inr (Or.inr (Or.inl (le_trans hin.2 hx_ge_hl)))
      · exact disj_zero_left _
  have htr_any_post : ∀ Nd, TriesTypedWith s S Nd → TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
    intro Nd hTr_any
    have hWT_any : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_any⟩
    have hstep_any := worldTypedWith_store_word_disj hAs hx_dom hpost hWT_any (by
      intro j hj
      unfold worldTypedIvls at hj
      rcases List.mem_append.1 hj with hj_rest | hj_nd
      · exact hdisj_wti_of_nd (fun k hk => hAT_at _ hcont_fl k hk) j (List.mem_append.2 (Or.inl hj_rest))
      · exact hnd_disj_any hTr_any.1 j hj_nd)
    exact ⟨hstep_any.2.1.2.2.2, hstep_any.2.2.2.1⟩
  have hpw_head_tail :
      (frameObjects s (globN s "ev", globN s "cur_cont")).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (globN s "ev", globN s "cur_cont"),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_cons, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    rw [List.mem_flatten]
    exact ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hcont_disj_head : ∀ o ∈ [(globN s "cur_cont", 104),
      (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
      (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
      (memW s (globN s "ev" + 88), 24),
      frameLogs s (globN s "ev", globN s "cur_cont"),
      frameRet s (globN s "ev", globN s "cur_cont")],
      Disj (globN s "ev", 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    simp only [List.cons_append, List.pairwise_cons] at hpw0
    obtain ⟨hd0, _⟩ := hpw0
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hd0 _ (by simp)
  have hrec_other_eq : ∀ ec ∈ evmChain s,
      (∀ k', k' + 8 ≤ 280 → k' ≠ 192 → k' ≠ 200 → memW post (ec.1 + k') = memW s (ec.1 + k')) ∧
      (∀ k, k + 8 ≤ 104 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    obtain ⟨hb_e, hb_c, hb_88⟩ := frameWF_bounds (hFW_all ec hec)
    have hdisj_c : Disj (globN s "ev", 280) (ec.2, 104) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hdisj_88 : Disj (globN s "ev", 280) (memW s (ec.1 + 88), 24) := by
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    refine ⟨?_, ?_, ?_⟩
    · intro k' hk' hkne1 hkne2
      apply hmemW_ne (ec.1 + k') (by omega)
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · dsimp only; omega
      · have hd := hpw_head_tail.2 _ hcont_fo ec htail (ec.1, 280) (by simp [frameObjects])
        rcases hd with h | h | h | h
        · cases h
        · cases h
        · dsimp only at h; omega
        · dsimp only at h; omega
    · intro k hk
      apply hmemW_ne (ec.2 + k) (by omega)
      rcases hdisj_c with h | h | h | h
      · cases h
      · cases h
      · dsimp only at h; omega
      · dsimp only at h; omega
    · intro k hk
      apply hmemW_ne (memW s (ec.1 + 88) + k) (by omega)
      rcases hdisj_88 with h | h | h | h
      · cases h
      · cases h
      · dsimp only at h; omega
      · dsimp only at h; omega
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
    exact hchain_aux (maxChain + 1) (globN s "ev") (globN s "cur_cont") (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega),
        h88_eq 16 (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega), he_eq 144 (by omega) (by omega) (by omega)]
  have hframeLogObjects_eq : ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    have hfw := hFW_all ec hec
    unfold frameLogObjects
    dsimp only
    rw [he_eq 88 (by omega) (by omega) (by omega), h88_eq 8 (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega)]
    apply List.flatMap_congr
    intro i hi_r
    have hi_lt : i < memW s (memW s (ec.1 + 88) + 8) := List.mem_range.1 hi_r
    have h88_le16 : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
      hfw.2.2.2.2.2.2.2.2.2.2.2.1
    have hd_flogs_x : Disj (frameLogs s ec) (x.toNat, 8) := by
      apply disj_of_inside_right (j' := (globN s "ev", 280)) hx_in_cont
      apply Disj.flip
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hal_fl : Allocated s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hflogs_hi : memW s (memW s (ec.1 + 88)) + 8 * memW s (memW s (ec.1 + 88) + 16) ≤ 2 ^ 64 :=
      (ivl_allocated_bound hAs.2 hal_fl).2
    have hslot_eq : memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
        memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      apply hmemW_ne _ (by omega)
      rcases hd_flogs_x with h | h | h | h
      · unfold frameLogs at h; dsimp only at h; omega
      · cases h
      · unfold frameLogs at h; dsimp only at h; rw [hx_eq] at h; omega
      · unfold frameLogs at h; dsimp only at h; rw [hx_eq] at h; omega
    rw [hslot_eq]
    have hll := hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rcases hll with h88_0 | ⟨_, _, _, _, hle_i⟩
    · have hin88 := (hfw.1 (memW s (ec.1 + 88), 24) (by simp)).1
      have hss : 32 ≤ scratchStart := by decide
      have := hAs.2.2.2.1; have := hAs.2.2.2.2.1
      dsimp [Inside] at hin88; omega
    · obtain ⟨_, hle_ok⟩ := hle_i i hi_lt
      have hlog_in : Inside (memW s (memW s (ec.1 + 88)) + 8 * i |> memW s, 40) sourceBase (globN s "heap_ptr") :=
        hle_ok.2.1
      have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
      dsimp [Inside] at hlog_in
      unfold logOwnedIvls logRecordIvls
      rw [hglob_eq "vm_system_address",
          hm_heap _ (by omega), hm_heap _ (by omega), hm_heap _ (by omega),
          hm_heap _ (by omega), hm_heap _ (by omega)]
  have hframeObjects_eq : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by omega) (by omega), he_eq 232 (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega), he_eq 40 (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega), hframeLogs_eq ec hec, hframeRet_eq ec hec, hframeLogObjects_eq ec hec]
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by omega), he_eq 232 (by omega) (by omega) (by omega), he_eq 88 (by omega) (by omega) (by omega)]
  have hmap_fo_eq : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hframeObjects_eq
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_other_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega), he_eq 168 (by omega) (by omega) (by omega), he_eq 176 (by omega) (by omega) (by omega)]
  refine ⟨hAp, ⟨hW_post, ?_⟩, hchain_eq, fun m hm => msgOwned_transfer hAs.1 hAp.1
    (hglob_eq "heap_ptr") (hglob_eq "scratch_ptr") (fun t ht => (htab_fp_hdr t ht).2) hfix_eq
    hchain_eq hframeObjects_eq htr_any_post hm, (hrec_other_eq _ hhead_mem).1⟩
  dsimp only
  rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_other_eq ec hec_mem).2.1 16 (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_other_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hFW_all ec hec
    have hd_88_x : Disj (memW s (ec.1 + 88), 24) (x.toNat, 8) := by
      apply disj_of_inside_right (j' := (globN s "ev", 280)) hx_in_cont
      apply Disj.flip
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hd_flogs_x : Disj (frameLogs s ec) (x.toNat, 8) := by
      apply disj_of_inside_right (j' := (globN s "ev", 280)) hx_in_cont
      apply Disj.flip
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hcont_disj_head _ (by simp)
      · exact hpw_head_tail.2 _ hcont_fo ec htail _ (by simp [frameObjects])
    have hflogs_al : (memW s (memW s (ec.1 + 88))) % 8 = 0 ∧
        memW s (memW s (ec.1 + 88)) + 8 * memW s (memW s (ec.1 + 88) + 16) ≤ 2 ^ 64 := by
      have hal_fl : Allocated s (frameLogs s ec) := c13
      exact ⟨c14.1, (ivl_allocated_bound hAs.2 hal_fl).2⟩
    have hc16_post : LogsListOK post (memW post (ec.1 + 88)) := by
      rw [he_eq 88 (by omega) (by omega) (by omega)]
      exact logsListOK_transfer hAs.1 hAp.1 (hglob_eq "heap_ptr") (hglob_eq "scratch_ptr") hAs.2
        hpost.2.2.2.2.2.2 hm_heap (fun _ => hd_88_x) (fun _ => hd_flogs_x) (fun _ => hflogs_al) c16
    have hc17_post : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega) (by omega)]
      exact msgOwned_transfer hAs.1 hAp.1 (hglob_eq "heap_ptr") (hglob_eq "scratch_ptr")
        (fun t ht => (htab_fp_hdr t ht).2) hfix_eq hchain_eq hframeObjects_eq htr_any_post c17
    unfold FrameWF
    dsimp only
    rw [he_eq 8 (by omega) (by omega) (by omega), he_eq 232 (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega), he_eq 24 (by omega) (by omega) (by omega),
        he_eq 40 (by omega) (by omega) (by omega), he_eq 16 (by omega) (by omega) (by omega),
        he_eq 32 (by omega) (by omega) (by omega),
        he_eq 136 (by omega) (by omega) (by omega), he_eq 168 (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega),
        h88_eq 16 (by omega), h88_eq 8 (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by omega), he_eq 144 (by omega) (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    refine ⟨?_, c2, wordsOK_transfer hAs.1 hAp.1 c3, c4, c5, c6, c7,
      c8, c9, c10, c11, c12, c13, wordsOK_transfer hAs.1 hAp.1 c14, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨hin, hw⟩ := c1 i hi
      exact ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩
    · simpa [he_eq 88 (by omega) (by omega) (by omega)] using hc16_post
    · simpa [he_eq 112 (by omega) (by omega) (by omega)] using hc17_post
  · intro ec hec
    have hec_mem : ec ∈ evmChain s := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_other_eq ec hec_mem).1 16 (by omega) (by omega) (by omega), (hrec_other_eq ec hec_mem).1 232 (by omega) (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_other_eq _ hi0).2.1 80 (by omega),
        (hrec_other_eq _ hi0).2.1 72 (by omega),
        (hrec_other_eq _ hi1).1 40 (by omega) (by omega) (by omega)]
    exact hRW i hi
  · rw [hmap_fo_eq]; exact hFO_pw
  · intro ec hec o ho
    rw [hframeObjects_eq ec hec] at ho
    rw [hfix_eq]
    refine ⟨fun t ht i hi => ?_, (hFO_disj ec hec o ho).2⟩
    rw [(htab_fp_hdr t ht).2] at hi
    exact (hFO_disj ec hec o ho).1 t ht i hi
  · rw [hmap_fo_eq]
    refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [hnd_at_eq] at hj
    exact hAT_at o ho j hj
  · have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k ≠ 192 ∧ k ≠ 200 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> omega
      rw [(hrec_other_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_other_eq _ hi_mem).2.1 48 (by omega)
    have hmm_eq := (hrec_other_eq _ hi_mem).2.1 56 (by omega)
    have he24_eq := (hrec_other_eq _ hi_mem).1 24 (by omega) (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_other_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega)
    have hM := hMarks i hi
    dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfix_eq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      obtain ⟨he_j, _, _⟩ := hrec_other_eq _ hj_mem
      rw [hframeScratch_eq _ hj_mem, hframeObjects_eq _ hj_mem, hframeLogs_eq _ hj_mem, he_j 112 (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · intro t ht
      rw [(htab_fp_hdr t ht).2, hdelEx_iff i t]
      exact m8 t ht
  · rw [hwrs_eq, hframeRoleSlots_eq, hjr_eq]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    rw [(htab_fp_hdr a.1 haS).1 0 (by omega)]
    exact ⟨haS, hkl⟩
  · have hle : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum ≤
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      apply List.Forall₂.sum_le_sum
      rw [List.forall₂_map_right_iff, List.forall₂_map_left_iff, List.forall₂_same]
      intro ec hec
      have hec' := hec
      rw [hch_cons, List.mem_cons] at hec
      rcases hec with rfl | htail
      · exact hgas
      · have hd := hpw_head_tail.2 _ hcont_fo ec htail (ec.1, 280) (by simp [frameObjects])
        obtain ⟨hb_e, _, _⟩ := frameWF_bounds (hFW_all ec hec')
        have htail_eq : ∀ k', k' + 8 ≤ 280 → memW post (ec.1 + k') = memW s (ec.1 + k') := by
          intro k' hk'
          apply hmemW_ne (ec.1 + k') (by omega)
          rcases hd with h | h | h | h
          · cases h
          · cases h
          · dsimp only at h; omega
          · dsimp only at h; omega
        rw [htail_eq 64 (by omega), htail_eq 192 (by omega)]
    omega

theorem evmInv_store_ev_gas {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {x : BitVec 64} {k : Nat} (hk : k = 192 ∨ k = 200)
    (hx_eq : x.toNat = globN s "ev" + k)
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmInv post := by
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  obtain ⟨hAp, hInvAt', _⟩ := evmInvAt_store_ev_gas hAs hInvAt hk hx_eq hx_dom hpost hgas
  exact ⟨hAp, S, hInvAt'⟩

/-- The same store from an `EvmMsgReady` state: `EvmMsgReady` again and an `EvmStep []`. -/
theorem evmMsgReady_store_ev_gas {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hP : EvmMsgReady s) {x : BitVec 64} {k : Nat} (hk : k = 192 ∨ k = 200)
    (hx_eq : x.toNat = globN s "ev" + k)
    (hx_dom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hgas : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) :
    EvmMsgReady post ∧ EvmStep [] s post := by
  obtain ⟨hAs, S, hInvAt, hMO⟩ := hP
  obtain ⟨hAp, hInvAt', hch, hmo, hhead⟩ := evmInvAt_store_ev_gas hAs hInvAt hk hx_eq hx_dom hpost hgas
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hpost.2.2.2.2.2.1]
  refine ⟨⟨hAp, S, hInvAt', ?_⟩, ⟨hAp, S, hInvAt'⟩, by rw [hglob_eq], ?_, hch⟩
  · rw [hglob_eq, hhead 112 (by omega) (by omega) (by omega)]
    exact hmo _ hMO
  · intro g _
    rw [hpost.2.2.2.2.2.1]

/-- `st ev + 192, 0` (`depth0_prepare` clears the spilled state gas) from `EvmMsgReady`:
`EvmMsgReady` again and an `EvmStep []` from the entry state. -/
theorem hoare_store_ev_192_zero :
    Hoare EvmMsgReady
      (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
      (fun r t => r = none → EvmMsgReady t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  have hrun := evaluateHOLFiniteState_store s
    (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with ⟨res, post⟩
  rw [hev] at hr hrun
  dsimp only at hr ⊢
  subst hr
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const 192]) with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.const 0) = some (.val (.word 0)) := by
        simp [evalHOLExact]
      rw [hsrc]
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
          have hInv := evmInv_of_evmMsgReady s hP
          have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
            unfold evmChain; exact List.mem_cons_self
          obtain ⟨_, S, _, _, _, _, hFW_all, _⟩ := hInv
          have hb_e := (R10Shards.GbodyProcessMsg.frameWF_bounds (hFW_all _ hhead_mem)).1
          dsimp only at hb_e
          have haddr_nat : addr.toNat = globN s "ev" + 192 := by
            simp [evalHOLExact, evalListHOLExact] at hdst
            rcases hg : s.globals.lookup (ofString "ev") with _ | gv
            · simp [hg] at hdst
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
                subst hdst
                have hglob : globN s "ev" = gw.toNat := by simp [globN, hg]
                rw [hglob] at hb_e ⊢
                have h192 : (192#64).toNat = 192 := by decide
                rw [BitVec.toNat_add, h192, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at hdst
              · simp [hg, valueIsWord] at hdst
          set post : PanSemStateFiniteExact 64 F :=
            { s with memory := fun current => if current = addr then .word 0 else s.memory current } with hpost_def
          have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
              post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
              ∀ a : BitVec 64, a ≠ addr → post.memory a = s.memory a :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by simp [post, hne]⟩
          have hne64 : BitVec.ofNat 64 (globN s "ev" + 64) ≠ addr := by
            intro heq
            have h1 : (BitVec.ofNat 64 (globN s "ev" + 64)).toNat = globN s "ev" + 64 :=
              Nat.mod_eq_of_lt (by omega)
            rw [heq, haddr_nat] at h1
            omega
          have hw64 : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) := by
            unfold memW; simp [post, hne64]
          have hw192 : memW post (globN s "ev" + 192) = 0 := by
            unfold memW
            have heq : BitVec.ofNat 64 (globN s "ev" + 192) = addr := by
              apply BitVec.eq_of_toNat_eq
              rw [haddr_nat]
              exact Nat.mod_eq_of_lt (by omega)
            simp [post, heq]
          exact (evmMsgReady_store_ev_gas hP (Or.inl rfl) haddr_nat hdom hpost
            (by rw [hw64, hw192]; omega)).1
        · simp [hdom] at hst
      · simp
    · simp
    · simp

/-- `EvmInv` already owns the head frame's message (`FrameWF`'s last conjunct for the head
`(ev, cur_cont)`), so `EvmMsgReady` follows from `EvmInv` for the same table set. -/
theorem evmMsgReady_of_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    EvmMsgReady s := by
  obtain ⟨hA, S, hInvAt⟩ := h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  exact ⟨hA, S, hInvAt, (hInvAt.2.2.2.2.1 _ hhead_mem).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem evmMsgReady_iff_evmInv {F : Type} (s : PanSemStateFiniteExact 64 F) :
    EvmMsgReady s ↔ EvmInv s :=
  ⟨evmInv_of_evmMsgReady s, evmMsgReady_of_evmInv s⟩

/-- `EvmStep gw s post` from an `EvmMsgReady` entry gives `EvmMsgReady post`. -/
theorem evmMsgReady_of_evmStep {F : Type} {gw : List String} {s post : PanSemStateFiniteExact 64 F}
    (h : EvmStep gw s post) : EvmMsgReady post :=
  evmMsgReady_of_evmInv post h.1

/-- `st msg + 48, lds 1 (ev + 72)` (`depth0_prepare` writes the reservoir into the message) from
`EvmMsgReady` with the local `msg` equal to the owned message `ev+112`: the message record is an
`EvmAvoids` region, so the store is a byte-region effect that yields `EvmStep []`, hence
`EvmMsgReady` again. -/
theorem hoare_store_msg_48 :
    Hoare (fun s => EvmMsgReady s ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (.store (.op .add [.var .local (ofString "msg"), .const 48])
        (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
      (fun r t => r = none → EvmMsgReady t) := by
  refine ⟨fun {F} s _ ⟨hP, m, hm, hm_eq⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .local (ofString "msg"), .const 48])
      (.load .one (.op .add [.var .global (ofString "ev"), .const 72]))) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  have hAs : ArenaReady s := hP.1
  have hm_bnd : memW s (globN s "ev" + 112) + 176 ≤ 2 ^ 64 := by
    obtain ⟨_, S, _, hal, _⟩ := hP
    exact allocated_le_2pow64 hAs.2 hal
  obtain ⟨heff, _⟩ := M11.ByteRegionEffect.of_store_word
    (Rl := [(memW s (globN s "ev" + 112), 176)]) hAs.1.memaddrs hev
    (fun v hv => M11.eval_load_one_word s _ v hv)
    (fun addr hdst _ => by
      refine ⟨(memW s (globN s "ev" + 112), 176), List.mem_singleton.2 rfl, ?_⟩
      have haddr : addr.toNat = m.toNat + 48 := by
        simp [evalHOLExact, evalListHOLExact, hm, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
        subst hdst
        have h48 : (48#64).toNat = 48 := by decide
        rw [BitVec.toNat_add, h48, Nat.mod_eq_of_lt (by omega)]
      dsimp only
      omega)
  exact evmMsgReady_of_evmStep
    (ByteRegionEffect.to_evmStep_avoids (evmAvoids_msg_of_evmMsgReady s hP)
      (m11Bre_to_evmBre (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; simp) heff))

/-- `st ev + 200, used` (`depth0_prepare` records the authorization state gas) from
`EvmMsgReady` with a word local `used`: `EvmMsgReady` again (`ev+200` is outside the gas sum),
locals and globals unchanged, and the owned message pointer `ev+112` unchanged. -/
theorem store_ev_200_used_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : EvmMsgReady s) {w_used : BitVec 64}
    (hused : s.locals.lookup (ofString "used") = some (.val (.word w_used)))
    {post : PanSemStateFiniteExact 64 F}
    (hev : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))) =
      (none, post)) :
    EvmMsgReady post ∧ post.locals = s.locals ∧ post.globals = s.globals ∧
      memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
  have hrun := evaluateHOLFiniteState_store s
    (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))
  rw [hev] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const 200]) with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString "used")) = some (.val (.word w_used)) := by
        simp [evalHOLExact, hused]
      rw [hsrc]
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
          have hInv := evmInv_of_evmMsgReady s hP
          have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
            unfold evmChain; exact List.mem_cons_self
          obtain ⟨_, S, _, _, _, _, hFW_all, _⟩ := hInv
          have hb_e := (R10Shards.GbodyProcessMsg.frameWF_bounds (hFW_all _ hhead_mem)).1
          dsimp only at hb_e
          have haddr_nat : addr.toNat = globN s "ev" + 200 := by
            simp [evalHOLExact, evalListHOLExact] at hdst
            rcases hg : s.globals.lookup (ofString "ev") with _ | gv
            · simp [hg] at hdst
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
                subst hdst
                have hglob : globN s "ev" = gw.toNat := by simp [globN, hg]
                rw [hglob] at hb_e ⊢
                have h200 : (200#64).toNat = 200 := by decide
                rw [BitVec.toNat_add, h200, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at hdst
              · simp [hg, valueIsWord] at hdst
          set post : PanSemStateFiniteExact 64 F :=
            { s with memory := fun current => if current = addr then .word w_used else s.memory current } with hpost_def
          have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
              post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
              ∀ a : BitVec 64, a ≠ addr → post.memory a = s.memory a :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by simp [post, hne]⟩
          have hne_of : ∀ k, k < 280 → k ≠ 200 → BitVec.ofNat 64 (globN s "ev" + k) ≠ addr := by
            intro k hk hkne heq
            have h1 : (BitVec.ofNat 64 (globN s "ev" + k)).toNat = globN s "ev" + k :=
              Nat.mod_eq_of_lt (by omega)
            rw [heq, haddr_nat] at h1
            omega
          have hwk : ∀ k, k < 280 → k ≠ 200 → memW post (globN s "ev" + k) = memW s (globN s "ev" + k) := by
            intro k hk hkne
            unfold memW; simp [post, hne_of k hk hkne]
          refine ⟨(evmMsgReady_store_ev_gas hP (Or.inr rfl) haddr_nat hdom hpost
            (by rw [hwk 64 (by omega) (by omega), hwk 192 (by omega) (by omega)])).1, rfl, rfl,
            hwk 112 (by omega) (by omega)⟩
        · simp [hdom] at hst
      · simp
    · simp
    · simp

theorem hoare_store_ev_200_used :
    Hoare (fun s => EvmMsgReady s ∧ ∃ w : BitVec 64,
        s.locals.lookup (ofString "used") = some (.val (.word w)))
      (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
      (fun r t => r = none → EvmMsgReady t) := by
  refine ⟨fun {F} s _ ⟨hP, w_used, hused⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  exact (store_ev_200_used_run s hP hused hev).1

/-- The three stores closing the authorization branch of `depth0_prepare`
(`st ev+200, used; st msg+48, lds(ev+72); st ev+192, 0`), from `EvmMsgReady` with word locals
`used` and `msg = ev+112`: `EvmMsgReady` again. -/
theorem hoare_depth0_auth_stores :
    Hoare (fun s => EvmMsgReady s ∧
        (∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w))) ∧
        ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
          m.toNat = memW s (globN s "ev" + 112))
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
        (.seq
          (.store (.op .add [.var .local (ofString "msg"), .const 48])
            (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
          (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))))
      (fun r t => r = none → EvmMsgReady t) := by
  refine Hoare.seq (R := fun s => EvmMsgReady s ∧
      ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112)) ?_ ?_
  · refine ⟨fun {F} s hcode ⟨hP, ⟨w_used, hused⟩, m, hm, hm_eq⟩ hnt => ?_⟩
    rcases hev : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))) with ⟨res, post⟩
    dsimp only
    refine ⟨fun hr => ?_, fun hr hr' => absurd hr' hr⟩
    subst hr
    obtain ⟨hP', hloc, hglob, h112⟩ := store_ev_200_used_run s hP hused hev
    have hglobN : globN post "ev" = globN s "ev" := by simp [globN, hglob]
    refine ⟨hP', m, by rw [hloc]; exact hm, ?_⟩
    rw [hglobN, h112]; exact hm_eq
  · refine Hoare.seq (R := EvmMsgReady) ?_ hoare_store_ev_192_zero
    refine ⟨fun {F} s hcode hR hnt => ?_⟩
    have h2 := (hoare_store_msg_48).run s hcode hR hnt
    exact ⟨fun hr => h2 hr, fun hr hr' => absurd hr' hr⟩

/-- `frame_state_gas_used` (AST index 451) reads only. -/
theorem ro_frame_state_gas_used : ReadOnlyFn (ofString "frame_state_gas_used") :=
  OpHandlersB.HeadMemBridge.RbM15.readOnlyFn_of_guestAst 451 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_frame_state_gas_used rfl (fun _ => false) (fun _ h => by cases h) rfl

/-- The guard of the `depth0_prepare` auth branch reads only the local `msg`. -/
theorem localsOnly_msgPtr :
    LocalsOnly ["msg"] (fun s => EvmMsgReady s ∧ ∃ m : BitVec 64,
      s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
      m.toNat = memW s (globN s "ev" + 112)) := by
  intro F s locals k hl ⟨hP, m, hm, hm_eq⟩
  exact ⟨localsFree_evmMsgReady s locals k hP, m, by rw [hl "msg" (by simp)]; exact hm, hm_eq⟩

/-- `decCall` with a word result shape: the continuation additionally knows the declared local
holds a word (`Hoare.decCall_fall` of `PtxPhase45R11` with the shape check exposed). -/
theorem Hoare.decCall_fall_word {P Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare (fun s => R s ∧ ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w)))
      cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name .one fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name .one fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · rename_i hsh
              obtain ⟨w, rfl⟩ := R10Shards.GbodyProcessMsg.value_shape_one_word
                (Bool.and_eq_true_iff.1 hsh).1
              set resumed := setVarHOLFinite name (.val (.word w)) { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' _ bpost hcode hP hargs hl hb
              have hresW : resumed.locals.lookup name = some (.val (.word w)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode ⟨hresR, w, hresW⟩ (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

/-- The `depth0_prepare` auth branch after `set_delegation`:
`var used = frame_state_gas_used(ev); st ev+200, used; st msg+48, lds(ev+72); st ev+192, 0`,
from `EvmMsgReady` with `msg = ev+112`: `EvmMsgReady` again. -/
theorem hoare_depth0_auth_tail :
    Hoare (fun s => EvmMsgReady s ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (.decCall (ofString "used") .one (ofString "frame_state_gas_used") [.var .global (ofString "ev")]
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
          (.seq
            (.store (.op .add [.var .local (ofString "msg"), .const 48])
              (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
            (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)))))
      (fun r t => r = none → EvmMsgReady t) := by
  have hres : DecCallResumeOn
      (fun s => EvmMsgReady s ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (fun s => EvmMsgReady s ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (ofString "used") (ofString "frame_state_gas_used") [.var .global (ofString "ev")] :=
    ReadOnlyFn.resumeOn localsOnly_msgPtr
      (fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1))
      ro_frame_state_gas_used (ofString "used") (by decide) _
  have hcont := Hoare.mono hoare_depth0_auth_stores
    (P := fun s => (EvmMsgReady s ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112)) ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w)))
    (fun s h => ⟨h.1.1, h.2, h.1.2⟩)
  exact Hoare.decCall_fall_word (names := []) (by simp)
    (LocalsOnly.of_localsFree localsFree_evmMsgReady) (fun {F} => @hres F) hcont

/-! ## `StepFrom`: `EvmStep` with the entry state captured by value, for `Hoare` chaining -/

/-- `EvmStep gw s₀ t` with the entry data (`heap_ptr`, globals, chain) of `s₀` taken as values, so
it is an ordinary (locals-free) state predicate usable as a `Hoare` pre/postcondition. -/
def StepFrom (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  EvmInv t ∧ hp ≤ globN t "heap_ptr" ∧ (∀ k : MlS, k ∉ gw.map ofString → G k = t.globals.lookup k) ∧
    evmChain t = ch

theorem evmStep_iff_stepFrom {F : Type} (gw : List String) (s t : PanSemStateFiniteExact 64 F) :
    EvmStep gw s t ↔ StepFrom gw (globN s "heap_ptr") s.globals.lookup (evmChain s) t :=
  Iff.rfl

theorem stepFrom_refl {F : Type} (gw : List String) (s : PanSemStateFiniteExact 64 F)
    (h : EvmInv s) : StepFrom gw (globN s "heap_ptr") s.globals.lookup (evmChain s) s :=
  ⟨h, le_rfl, fun _ _ => rfl, rfl⟩

/-- Chaining: an `EvmStep gw'` from a `StepFrom gw` state lands in a `StepFrom gw` state when
`gw' ⊆ gw`. -/
theorem stepFrom_of_evmStep {F : Type} {gw gw' : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {s t : PanSemStateFiniteExact 64 F}
    (hsub : ∀ g ∈ gw', g ∈ gw) (h0 : StepFrom gw hp G ch s) (h : EvmStep gw' s t) :
    StepFrom gw hp G ch t := by
  obtain ⟨_, hhp, hG, hch⟩ := h0
  obtain ⟨hInv, hhp', hG', hch'⟩ := h
  refine ⟨hInv, Nat.le_trans hhp hhp', fun k hk => ?_, hch'.trans hch⟩
  have hk' : k ∉ gw'.map ofString := by
    intro hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, hsub g hg, rfl⟩)
  exact (hG k hk).trans (hG' k hk')

theorem localsFree_stepFrom (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) : LocalsFree (StepFrom gw hp G ch) := by
  intro F s locals k h
  obtain ⟨hInv, hhp, hG, hch⟩ := h
  exact ⟨localsFree_evmInv s locals k hInv, hhp, hG, by rw [evmChain_with_locals]; exact hch⟩

/-- `Hoare` lifting: a triple that is an `EvmStep gw'` from its own entry becomes a triple between
`StepFrom gw` states. -/
theorem hoare_stepFrom_of_evmStep {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {gw gw' : List String} (hsub : ∀ g ∈ gw', g ∈ gw)
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
      (evaluateHOLFiniteState s prog).1 = none →
      EvmStep gw' s (evaluateHOLFiniteState s prog).2)
    (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => P s ∧ StepFrom gw hp G ch s) prog
      (fun r t => r = none → StepFrom gw hp G ch t) :=
  ⟨fun s hcode hP hnt hr => EvmEkFk.stepFrom_of_evmStep hsub hP.2 (h s hcode hP.1 hnt hr)⟩

/-! ## Head-record stores as `EvmStep []` (for `StepFrom` chaining) -/

/-- Generic word store `st ev + k, src` (`k ∈ {192, 200}`) from `EvmMsgReady`, with the source
evaluating to the word `w` and (for `k = 192`) `w` not exceeding the old spilled gas: `EvmMsgReady`
again, an `EvmStep []`, and locals unchanged. -/
theorem store_ev_gas_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : EvmMsgReady s) {k : Nat} (hk : k = 192 ∨ k = 200) {src : ExpHOL 64} {w : BitVec 64}
    (hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src =
      some (.val (.word w)))
    (hgas : k = 200 ∨ w.toNat ≤ memW s (globN s "ev" + 192))
    {post : PanSemStateFiniteExact 64 F}
    (hev : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const k]) src) = (none, post)) :
    EvmMsgReady post ∧ EvmStep [] s post ∧ post.locals = s.locals := by
  have hrun := evaluateHOLFiniteState_store s
    (.op .add [.var .global (ofString "ev"), .const k]) src
  rw [hev] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const k]) with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rw [hsrc]
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
          have hInv := evmInv_of_evmMsgReady s hP
          have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
            unfold evmChain; exact List.mem_cons_self
          obtain ⟨_, S, _, _, _, _, hFW_all, _⟩ := hInv
          have hb_e := (R10Shards.GbodyProcessMsg.frameWF_bounds (hFW_all _ hhead_mem)).1
          dsimp only at hb_e
          have hk_lt : k < 280 := by rcases hk with rfl | rfl <;> omega
          have haddr_nat : addr.toNat = globN s "ev" + k := by
            simp [evalHOLExact, evalListHOLExact] at hdst
            rcases hg : s.globals.lookup (ofString "ev") with _ | gv
            · simp [hg] at hdst
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
                subst hdst
                have hglob : globN s "ev" = gw.toNat := by simp [globN, hg]
                rw [hglob] at hb_e ⊢
                have hkk : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
                rw [BitVec.toNat_add, hkk, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at hdst
              · simp [hg, valueIsWord] at hdst
          set post : PanSemStateFiniteExact 64 F :=
            { s with memory := fun current => if current = addr then .word w else s.memory current } with hpost_def
          have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
              post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
              ∀ a : BitVec 64, a ≠ addr → post.memory a = s.memory a :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a hne => by simp [post, hne]⟩
          have hne_of : ∀ j, j < 280 → j ≠ k → BitVec.ofNat 64 (globN s "ev" + j) ≠ addr := by
            intro j hj hjne heq
            have h1 : (BitVec.ofNat 64 (globN s "ev" + j)).toNat = globN s "ev" + j :=
              Nat.mod_eq_of_lt (by omega)
            rw [heq, haddr_nat] at h1
            omega
          have hwj : ∀ j, j < 280 → j ≠ k → memW post (globN s "ev" + j) = memW s (globN s "ev" + j) := by
            intro j hj hjne
            unfold memW; simp [post, hne_of j hj hjne]
          have hwk : memW post (globN s "ev" + k) = w.toNat := by
            unfold memW
            have heq : BitVec.ofNat 64 (globN s "ev" + k) = addr := by
              apply BitVec.eq_of_toNat_eq
              rw [haddr_nat]
              exact Nat.mod_eq_of_lt (by omega)
            simp [post, heq]
          have hgas' : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
              memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
            rw [hwj 64 (by omega) (by omega)]
            rcases hk with rfl | rfl
            · rw [hwk]
              rcases hgas with h | h
              · omega
              · omega
            · rw [hwj 192 (by omega) (by omega)]
          have hres := evmMsgReady_store_ev_gas hP hk haddr_nat hdom hpost hgas'
          exact ⟨hres.1, hres.2, rfl⟩
        · simp [hdom] at hst
      · simp
    · simp
    · simp

/-- `st ev + 192, 0` between `StepFrom` states. -/
theorem hoare_store_ev_192_zero_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
      (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))
      (fun r t => r = none → EvmMsgReady t ∧ StepFrom gw hp G ch t) := by
  refine ⟨fun {F} s _ ⟨hP, hS⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  obtain ⟨hP', hstep, _⟩ := store_ev_gas_run s hP (Or.inl rfl) (src := .const 0) (w := 0)
    (by simp [evalHOLExact]) (Or.inr (by simp)) hev
  exact ⟨hP', stepFrom_of_evmStep (fun _ h => by cases h) hS hstep⟩

/-- `st ev + 200, used` between `StepFrom` states, carrying the `msg = ev+112` local relation. -/
theorem hoare_store_ev_200_used_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧
        (∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w))) ∧
        ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
          m.toNat = memW s (globN s "ev" + 112))
      (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
      (fun r t => r = none → (EvmMsgReady t ∧ StepFrom gw hp G ch t) ∧
        ∃ m : BitVec 64, t.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
          m.toNat = memW t (globN t "ev" + 112)) := by
  refine ⟨fun {F} s _ ⟨⟨hP, hS⟩, ⟨w_used, hused⟩, m, hm, hm_eq⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used"))) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  obtain ⟨hP', hloc, hglob, h112⟩ := store_ev_200_used_run s hP hused hev
  obtain ⟨_, hstep, _⟩ := store_ev_gas_run s hP (Or.inr rfl) (src := .var .local (ofString "used"))
    (w := w_used) (by simp [evalHOLExact, hused]) (Or.inl rfl) hev
  have hglobN : globN post "ev" = globN s "ev" := by simp [globN, hglob]
  refine ⟨⟨hP', stepFrom_of_evmStep (fun _ h => by cases h) hS hstep⟩, m, by rw [hloc]; exact hm, ?_⟩
  rw [hglobN, h112]; exact hm_eq

/-- `st msg + 48, lds 1 (ev + 72)` from `EvmMsgReady` with `msg = ev+112`: `EvmMsgReady` again and
an `EvmStep []` (the message record is an `EvmAvoids` region). -/
theorem store_msg_48_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : EvmMsgReady s) {m : BitVec 64}
    (hm : s.locals.lookup (ofString "msg") = some (.val (.word m)))
    (hm_eq : m.toNat = memW s (globN s "ev" + 112))
    {post : PanSemStateFiniteExact 64 F}
    (hev : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "msg"), .const 48])
        (.load .one (.op .add [.var .global (ofString "ev"), .const 72]))) = (none, post)) :
    EvmMsgReady post ∧ EvmStep [] s post := by
  have hAs : ArenaReady s := hP.1
  have hm_bnd : memW s (globN s "ev" + 112) + 176 ≤ 2 ^ 64 := by
    obtain ⟨_, S, _, hal, _⟩ := hP
    exact allocated_le_2pow64 hAs.2 hal
  obtain ⟨heff, _⟩ := M11.ByteRegionEffect.of_store_word
    (Rl := [(memW s (globN s "ev" + 112), 176)]) hAs.1.memaddrs hev
    (fun v hv => M11.eval_load_one_word s _ v hv)
    (fun addr hdst _ => by
      refine ⟨(memW s (globN s "ev" + 112), 176), List.mem_singleton.2 rfl, ?_⟩
      have haddr : addr.toNat = m.toNat + 48 := by
        simp [evalHOLExact, evalListHOLExact, hm, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
        subst hdst
        have h48 : (48#64).toNat = 48 := by decide
        rw [BitVec.toNat_add, h48, Nat.mod_eq_of_lt (by omega)]
      dsimp only
      omega)
  have hstep : EvmStep [] s post :=
    ByteRegionEffect.to_evmStep_avoids (evmAvoids_msg_of_evmMsgReady s hP)
      (m11Bre_to_evmBre (fun i hi => by simp only [List.mem_singleton] at hi; subst hi; simp) heff)
  exact ⟨evmMsgReady_of_evmStep hstep, hstep⟩

/-- `st msg + 48, lds 1 (ev + 72)` between `StepFrom` states. -/
theorem hoare_store_msg_48_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧
        ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
          m.toNat = memW s (globN s "ev" + 112))
      (.store (.op .add [.var .local (ofString "msg"), .const 48])
        (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
      (fun r t => r = none → EvmMsgReady t ∧ StepFrom gw hp G ch t) := by
  refine ⟨fun {F} s _ ⟨⟨hP, hS⟩, m, hm, hm_eq⟩ _ hr => ?_⟩
  rcases hev : evaluateHOLFiniteState s
    (.store (.op .add [.var .local (ofString "msg"), .const 48])
      (.load .one (.op .add [.var .global (ofString "ev"), .const 72]))) with ⟨res, post⟩
  rw [hev] at hr
  dsimp only at hr ⊢
  subst hr
  obtain ⟨hP', hstep⟩ := store_msg_48_run s hP hm hm_eq hev
  exact ⟨hP', stepFrom_of_evmStep (fun _ h => by cases h) hS hstep⟩

/-- The three auth-branch stores of `depth0_prepare`, between `StepFrom` states. -/
theorem hoare_depth0_auth_stores_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧
        (∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w))) ∧
        ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
          m.toNat = memW s (globN s "ev" + 112))
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
        (.seq
          (.store (.op .add [.var .local (ofString "msg"), .const 48])
            (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
          (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))))
      (fun r t => r = none → EvmMsgReady t ∧ StepFrom gw hp G ch t) := by
  refine Hoare.seq (R := fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧
      ∃ m : BitVec 64, s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112)) ?_ ?_
  · refine ⟨fun {F} s hcode hP hnt => ?_⟩
    have h1 := (hoare_store_ev_200_used_step gw hp G ch).run s hcode hP hnt
    exact ⟨fun hr => h1 hr, fun hr hr' => absurd hr' hr⟩
  · refine Hoare.seq (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) ?_
      (hoare_store_ev_192_zero_step gw hp G ch)
    refine ⟨fun {F} s hcode hR hnt => ?_⟩
    have h2 := (hoare_store_msg_48_step gw hp G ch).run s hcode hR hnt
    exact ⟨fun hr => h2 hr, fun hr hr' => absurd hr' hr⟩

/-- The `depth0_prepare` auth branch after `set_delegation`, between `StepFrom` states. -/
theorem hoare_depth0_auth_tail_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (.decCall (ofString "used") .one (ofString "frame_state_gas_used") [.var .global (ofString "ev")]
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
          (.seq
            (.store (.op .add [.var .local (ofString "msg"), .const 48])
              (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
            (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0)))))
      (fun r t => r = none → EvmMsgReady t ∧ StepFrom gw hp G ch t) := by
  have hLO : LocalsOnly ["msg"] (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
      s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
      m.toNat = memW s (globN s "ev" + 112)) := by
    intro F s locals k hl ⟨⟨hP, hS⟩, m, hm, hm_eq⟩
    exact ⟨⟨localsFree_evmMsgReady s locals k hP, localsFree_stepFrom gw hp G ch s locals k hS⟩,
      m, by rw [hl "msg" (by simp)]; exact hm, hm_eq⟩
  have hres : DecCallResumeOn
      (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (fun s => (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112))
      (ofString "used") (ofString "frame_state_gas_used") [.var .global (ofString "ev")] :=
    ReadOnlyFn.resumeOn hLO
      (fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1))
      ro_frame_state_gas_used (ofString "used") (by decide) _
  have hLF : LocalsFree (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) := by
    intro F s locals k h
    exact ⟨localsFree_evmMsgReady s locals k h.1, localsFree_stepFrom gw hp G ch s locals k h.2⟩
  have hQ : LocalsOnly [] (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) :=
    LocalsOnly.of_localsFree hLF
  have hcont := Hoare.mono (hoare_depth0_auth_stores_step gw hp G ch)
    (P := fun s => ((EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
        s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧
        m.toNat = memW s (globN s "ev" + 112)) ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w)))
    (fun s h => ⟨h.1.1, h.2, h.1.2⟩)
  exact Hoare.decCall_fall_word (names := []) (by simp) hQ (fun {F} => @hres F) hcont

/-! ## `Fall`: fall-through-or-resume postconditions, and `EvmKeeps` callee glue -/

/-- Post shape for `EvmKeeps` bodies: on fall-through or any resuming result, `Q` holds. -/
def Fall (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none ∨ Resumes r) → Q t

theorem Hoare.weaken {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q Q' : ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} (h : Hoare P prog Q)
    (hQQ : ∀ {F : Type} (r : Option (PanSemResultExact 64)) (t : PanSemStateFiniteExact 64 F),
      Q r t → Q' r t) : Hoare P prog Q' :=
  ⟨fun s hcode hP hnt => hQQ _ _ (h.run s hcode hP hnt)⟩

theorem Hoare.fall_of_none {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} (h : Hoare P prog (fun r t => r = none → Q t))
    (hnr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∀ r, Resumes r → (evaluateHOLFiniteState s prog).1 ≠ r) :
    Hoare P prog (Fall Q) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  rcases hr with hr | hr
  · exact h.run s hcode hP hnt hr
  · exact absurd rfl (hnr s hP _ hr)

theorem Hoare.seq_fall' {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (Fall R)) (h2 : Hoare R second (Fall Q))
    (hRQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s → Q s) :
    Hoare P (.seq first second) (Fall Q) := by
  refine Hoare.seq (R := R) (Hoare.weaken h1 ?_) h2
  intro F r t h
  refine ⟨fun hr => h (Or.inl hr), fun _ hr => hRQ t (h hr)⟩

theorem Hoare.skip_fall {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    Hoare P .skip (Fall P) :=
  Hoare.skip fun _ h _ => h

theorem Hoare.ite_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes (Fall Q))
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no (Fall Q)) :
    Hoare P (.ite cond yes no) (Fall Q) :=
  Hoare.ite hyes hno (fun _ _ h => by
    rcases h with h | h
    · cases h
    · exact absurd h not_resumes_error)

/-- `return (const c)` from a locals-free `P`. -/
theorem Hoare.return_const_fall {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : LocalsFree P) (c : BitVec 64) :
    Hoare P (.return (.const c)) (Fall P) := by
  refine ⟨fun {F} s _ hs _ hr => ?_⟩
  rw [evaluateHOLFiniteState_return] at hr ⊢
  have hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const c) = some (.val (.word c)) := by simp [evalHOLExact]
  rw [hc] at hr ⊢
  dsimp only at hr ⊢
  split at hr
  · rename_i hsz
    rw [if_pos hsz]
    exact hP s _ s.clock hs
  · rename_i hsz
    rw [if_neg hsz]
    rcases hr with hr | hr
    · cases hr
    · exact absurd hr not_resumes_error

/-- A handler-free, destination-free call to an `EvmKeeps P' gw'` callee, between `StepFrom gw`
states (`gw' ⊆ gw`): fall-through and every resuming exception land in a `StepFrom gw` state. -/
theorem Hoare.call_evmKeeps_fall {P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw gw' : List String} {hp : Nat} {G : MlS → Option (ValueHOL 64)} {ch : List Ivl}
    {fname : MlS} (hk : EvmKeeps P' gw' fname) (hsub : ∀ g ∈ gw', g ∈ gw)
    (hP' : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), StepFrom gw hp G ch s → P' s)
    (arguments : List (ExpHOL 64)) :
    Hoare (StepFrom gw hp G ch) (.call (some (none, none)) fname arguments)
      (Fall (StepFrom gw hp G ch)) := by
  refine ⟨fun {F} s hcode hS hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · rw [hargs] at hr
    rcases hr with hr | hr
    · cases hr
    · exact absurd hr not_resumes_error
  · simp only [hargs] at hnt hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hr
      rcases hr with hr | hr
      · cases hr
      · exact absurd hr not_resumes_error
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hSe : StepFrom gw hp G ch (callEntryStateHOLFinite s callee) :=
          localsFree_stepFrom gw hp G ch s callee (s.clock - 1) hS
        have hPe : P' (callEntryStateHOLFinite s callee) := hP' _ hSe
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hr ⊢
        have hQc (hsafe : res ≠ some .timeOut) :
            Resumes res → EvmStep gw' (callEntryStateHOLFinite s callee) post := by
          have := FunSpec.at_lookup hk s hcode values body' callee ret' hl hPe (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none =>
          rcases hr with hr | hr
          · cases hr
          · exact absurd hr not_resumes_error
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              have hSp : StepFrom gw hp G ch post :=
                stepFrom_of_evmStep hsub hSe (hQc (by simp) (Or.inl ⟨v, rfl⟩))
              exact localsFree_stepFrom gw hp G ch post s.locals post.clock hSp
            · rename_i hsh
              rw [if_neg hsh]
              rcases hr with hr | hr
              · cases hr
              · exact absurd hr not_resumes_error
          | timeOut => simp at hnt
          | exception e v =>
            dsimp only at hr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hr with hr | hr
              · cases hr
              · exact hr
            have hSp : StepFrom gw hp G ch post :=
              stepFrom_of_evmStep hsub hSe (hQc (by simp) hres)
            exact localsFree_stepFrom gw hp G ch post _ post.clock hSp
          | error =>
            rcases hr with hr | hr
            · cases hr
            · exact absurd hr not_resumes_error
          | _ =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

/-- `decCall` of a read-only callee with a word result, with the `Fall` post shape: a resuming
exception from the callee leaves the state unchanged up to locals/clock (`ReadOnlyFn`), and the
continuation's resuming results carry `Q` through the `resVarEq` locals restore (`Q` locals-free). -/
theorem Hoare.decCall_ro_fall {P Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hro : ReadOnlyFn fname)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (hQ : LocalsFree Q)
    (hPQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare (fun s => R s ∧ ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w)))
      cont (Fall Q)) :
    Hoare P (.decCall name .one fname arguments cont) (Fall Q) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name .one fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr hnt
  dsimp only at hr hnt ⊢
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    rcases hr with hr | hr
    · cases hr
    · exact absurd hr not_resumes_error
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      rcases hr with hr | hr
      · cases hr
      · exact absurd hr not_resumes_error
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        exact absurd rfl hnt
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        have hGe : GuestInv (callEntryStateHOLFinite s callee) := guestInv_callEntry s callee (hPG s hP)
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        have hro_run (hsafe : bres ≠ some .timeOut) : Resumes bres →
            bpost = { callEntryStateHOLFinite s callee with locals := bpost.locals, clock := bpost.clock } := by
          have := FunSpec.at_lookup hro s hcode values body' callee ret' hl hGe (by rw [hb]; exact hsafe)
          rw [hb] at this
          exact this
        cases bres with
        | none =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          rcases hr with hr | hr
          · cases hr
          · exact absurd hr not_resumes_error
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · rename_i hsh
              obtain ⟨w, rfl⟩ := R10Shards.GbodyProcessMsg.value_shape_one_word
                (Bool.and_eq_true_iff.1 hsh).1
              set resumed := setVarHOLFinite name (.val (.word w)) { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' _ bpost hcode hP hargs hl hb
              have hresW : resumed.locals.lookup name = some (.val (.word w)) := by
                simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode ⟨hresR, w, hresW⟩ (by rw [hc]; exact hnt)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 hr
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock hQc
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
              rcases hr with hr | hr
              · cases hr
              · exact absurd hr not_resumes_error
          | exception e v =>
            dsimp only at hrun
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
            have hres' : Resumes (some (.exception e v)) := by
              rcases hr with hr | hr
              · cases hr
              · exact hr
            have heq := hro_run (by simp) hres'
            rw [heq]
            simp only [emptyLocalsHOLFinite, callEntryStateHOLFinite]
            exact hQ s _ _ (hPQ s hP)
          | timeOut =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
            exact absurd rfl hnt
          | _ =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

/-- `dec name .one init body` with the `Fall` post shape, `Q` locals-free: the initializer's
failure is an error (not a resuming result), and resuming results restore the outer local. -/
theorem Hoare.dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (Fall Q)) (hQ : LocalsFree Q) :
    Hoare P (.dec name shape init body) (Fall Q) :=
  Hoare.dec (names := []) (by simp) hinit hbody
    (fun r t locals _ h hr => hQ t locals t.clock (h hr))
    (fun _ _ h => by
      rcases h with h | h
      · cases h
      · exact absurd h not_resumes_error)

/-- The initializer `lds 1 (ev + 112)` of `depth0_prepare`'s `msg` local evaluates to the owned
message pointer. -/
theorem dec_msg_init {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : EvmMsgReady s)
    (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) = some v) :
    ∃ m : BitVec 64, v = .val (.word m) ∧ m.toNat = memW s (globN s "ev" + 112) := by
  have hInv := evmInv_of_evmMsgReady s hP
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hb_e := (R10Shards.GbodyProcessMsg.frameWF_bounds (hFW_all _ hhead_mem)).1
  dsimp only at hb_e
  generalize haddrE : (.op .add [.var .global (ofString "ev"), .const 112] : ExpHOL 64) = addrE at hv
  simp only [evalHOLExact] at hv
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      addrE with _ | va
  · rw [ha] at hv; simp at hv
  · rw [ha] at hv
    subst haddrE
    rcases va with ⟨⟨a⟩⟩ | _ | _
    · simp only [memLoadHOLExact] at hv
      by_cases hdom : s.memaddrs a
      · simp only [hdom, ↓reduceIte, Option.some.injEq] at hv
        cases hmem : s.memory a with
        | word w =>
          rw [hmem] at hv
          have hv' : v = .val (.word w) := by
            split at hv
            · exact (Option.some.inj hv).symm
            · cases hv
          have haddr : a.toNat = globN s "ev" + 112 := by
            simp [evalHOLExact, evalListHOLExact] at ha
            rcases hg : s.globals.lookup (ofString "ev") with _ | gv
            · simp [hg] at ha
            · rcases gv with ⟨⟨gw⟩⟩ | _ | _
              · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at ha
                subst ha
                have hglob : globN s "ev" = gw.toNat := by simp [globN, hg]
                rw [hglob] at hb_e ⊢
                have h112 : (112#64).toNat = 112 := by decide
                rw [BitVec.toNat_add, h112, Nat.mod_eq_of_lt (by omega)]
              · simp [hg, valueIsWord] at ha
              · simp [hg, valueIsWord] at ha
          refine ⟨w, hv', ?_⟩
          unfold memW
          have heq : BitVec.ofNat 64 (globN s "ev" + 112) = a := by
            apply BitVec.eq_of_toNat_eq
            rw [haddr]
            exact Nat.mod_eq_of_lt (by omega)
          rw [heq, hmem]
      · simp [hdom] at hv
    · simp at hv
    · simp at hv

/-! ## `ek_depth0_prepare` from the callee contracts -/

/-- The body of `depth0_prepare` (AST index 587) as a `ProgHOL`. -/
theorem depth0_prepare_body_eq :
    sourceFnBody Guest.Software.guestFn_depth0_prepare =
      .seq .skip
        (.dec (ofString "msg") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 112]))
          (.dec (ofString "te") .one (.load .one (.op .add [.var .local (ofString "msg"), .const 8]))
            (.seq
              (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "te"), .const 152]))
                  (.const 0))
                (.seq (.call (some (none, none)) (ofString "set_delegation") [])
                  (.decCall (ofString "used") .one (ofString "frame_state_gas_used")
                    [.var .global (ofString "ev")]
                    (.seq
                      (.store (.op .add [.var .global (ofString "ev"), .const 200])
                        (.var .local (ofString "used")))
                      (.seq
                        (.store (.op .add [.var .local (ofString "msg"), .const 48])
                          (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
                        (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))))))
                .skip)
              (.seq .skip
                (.seq (.call (some (none, none)) (ofString "prepare_dispatch") [])
                  (.seq .skip (.return (.const 0)))))))) := rfl

/-- The entry/`msg`-relation invariant threaded through the `depth0_prepare` body. -/
def D0Pre (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (EvmMsgReady s ∧ StepFrom gw hp G ch s) ∧ ∃ m : BitVec 64,
    s.locals.lookup (ofString "msg") = some (.val (.word m)) ∧ m.toNat = memW s (globN s "ev" + 112)

/-- `D0Pre` does not depend on the locals other than `msg`. -/
theorem d0Pre_locals (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (k : Nat) (hl : locals.lookup (ofString "msg") = s.locals.lookup (ofString "msg"))
    (h : D0Pre gw hp G ch s) : D0Pre gw hp G ch { s with locals := locals, clock := k } := by
  obtain ⟨⟨hP, hS⟩, m, hm, hm_eq⟩ := h
  exact ⟨⟨localsFree_evmMsgReady s locals k hP, localsFree_stepFrom gw hp G ch s locals k hS⟩,
    m, by rw [hl]; exact hm, hm_eq⟩

theorem d0Pre_of_stepFrom (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64))
    (ch : List Ivl) {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hpre : D0Pre gw hp G ch s) (hS : StepFrom gw hp G ch t) (hloc : t.locals = s.locals)
    (hG : t.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev"))
    (hmem : memW t (globN s "ev" + 112) = memW s (globN s "ev" + 112)) :
    D0Pre gw hp G ch t := by
  obtain ⟨_, m, hm, hm_eq⟩ := hpre
  refine ⟨⟨evmMsgReady_of_evmInv t hS.1, hS⟩, m, by rw [hloc]; exact hm, ?_⟩
  have hev : globN t "ev" = globN s "ev" := by simp [globN, hG]
  rw [hev, hmem]; exact hm_eq

/-- A `store` never produces a resuming result. -/
theorem store_result_none_or_error {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store dst src)).1 = none ∨
      (evaluateHOLFiniteState s (.store dst src)).1 = some .error := by
  rw [evaluateHOLFiniteState_store]
  split <;> (try split) <;> (try split) <;> simp

theorem Hoare.store_fall_of_none {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64} (h : Hoare P (.store dst src) (fun r t => r = none → Q t)) :
    Hoare P (.store dst src) (Fall Q) :=
  Hoare.fall_of_none h (fun s _ r hr heq => by
    rcases store_result_none_or_error s dst src with h0 | h0
    · rw [h0] at heq; subst heq; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    · rw [h0] at heq; subst heq; exact not_resumes_error hr)

/-- The three auth-branch stores of `depth0_prepare`, `Fall` form. -/
theorem hoare_depth0_auth_stores_fall (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "used") = some (.val (.word w)))
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 200]) (.var .local (ofString "used")))
        (.seq
          (.store (.op .add [.var .local (ofString "msg"), .const 48])
            (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
          (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.seq_fall' (R := D0Pre gw hp G ch) ?_ ?_ (fun _ h => h.1)
  · refine Hoare.store_fall_of_none (Hoare.mono (hoare_store_ev_200_used_step gw hp G ch) ?_)
    intro F s ⟨⟨hPS, hmsg⟩, hused⟩
    exact ⟨hPS, hused, hmsg⟩
  · refine Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) ?_ ?_ (fun _ h => h)
    · exact Hoare.store_fall_of_none (hoare_store_msg_48_step gw hp G ch)
    · exact Hoare.store_fall_of_none (hoare_store_ev_192_zero_step gw hp G ch)

/-- Post shape of a call inside a `D0Pre` sequence: fall-through keeps `D0Pre` (the caller's
locals are restored), a resuming exception (locals emptied) keeps `EvmMsgReady ∧ StepFrom`. -/
def D0CallPost (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    ∀ {F : Type}, Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop :=
  fun r t => (r = none → D0Pre gw hp G ch t) ∧ (Resumes r → EvmMsgReady t ∧ StepFrom gw hp G ch t)

/-- The `set_delegation` call followed by the auth tail, from a `D0Pre` state: the callee is
given as a `Hoare` triple with the `D0CallPost` shape (what an `ek_set_delegation` contract that
also keeps the `ev+112` message slot provides, see `hoare_call_d0CallPost_of_evmKeeps`). -/
theorem hoare_depth0_auth_branch (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (hsd : Hoare (D0Pre gw hp G ch) (.call (some (none, none)) (ofString "set_delegation") [])
      (D0CallPost gw hp G ch)) :
    Hoare (D0Pre gw hp G ch)
      (.seq (.call (some (none, none)) (ofString "set_delegation") [])
        (.decCall (ofString "used") .one (ofString "frame_state_gas_used")
          [.var .global (ofString "ev")]
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 200])
              (.var .local (ofString "used")))
            (.seq
              (.store (.op .add [.var .local (ofString "msg"), .const 48])
                (.load .one (.op .add [.var .global (ofString "ev"), .const 72])))
              (.store (.op .add [.var .global (ofString "ev"), .const 192]) (.const 0))))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.seq (R := D0Pre gw hp G ch) (Hoare.weaken hsd ?_) ?_
  · intro F r t ⟨h1, h2⟩
    refine ⟨h1, fun hne hr => ?_⟩
    rcases hr with hr | hr
    · exact absurd hr hne
    · exact h2 hr
  have hLO : LocalsOnly ["msg"] (D0Pre gw hp G ch) := by
    intro F s locals k hl h
    exact d0Pre_locals gw hp G ch s locals k (hl "msg" (by simp)) h
  have hLF : LocalsFree (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) := by
    intro F s locals k h
    exact ⟨localsFree_evmMsgReady s locals k h.1, localsFree_stepFrom gw hp G ch s locals k h.2⟩
  refine Hoare.decCall_ro_fall ro_frame_state_gas_used
    (fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1)) hLF (fun _ h => h.1)
    (ReadOnlyFn.resumeOn hLO (fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1))
      ro_frame_state_gas_used (ofString "used") (by decide) _)
    (hoare_depth0_auth_stores_fall gw hp G ch)

/-- `ek_depth0_prepare` from the callee contracts: `set_delegation` as a `D0CallPost` triple
(for every `StepFrom` frame) and `prepare_dispatch` as `EvmKeeps EvmMsgReady gw_pd` with
`gw_pd ⊆ ["heap_ptr", "journal_n", "scratch_ptr"]`. -/
theorem ek_depth0_prepare_of_callees {gw_pd : List String}
    (hsd : ∀ (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl),
      Hoare (D0Pre ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch)
        (.call (some (none, none)) (ofString "set_delegation") [])
        (D0CallPost ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch))
    (hpd : EvmKeeps EvmMsgReady gw_pd (ofString "prepare_dispatch"))
    (hsub : ∀ g ∈ gw_pd, g ∈ ["heap_ptr", "journal_n", "scratch_ptr"]) :
    EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "depth0_prepare") := by
  set gw : List String := ["heap_ptr", "journal_n", "scratch_ptr"] with hgw
  have hbody : ∀ (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl),
      Hoare (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
        (sourceFnBody Guest.Software.guestFn_depth0_prepare)
        (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
    intro hp G ch
    have hLF : LocalsFree (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) := by
      intro F s locals k h
      exact ⟨localsFree_evmMsgReady s locals k h.1, localsFree_stepFrom gw hp G ch s locals k h.2⟩
    rw [depth0_prepare_body_eq]
    refine Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
      Hoare.skip_fall ?_ (fun _ h => h)
    -- `dec msg`
    refine Hoare.dec_fall (P' := D0Pre gw hp G ch) ?_ ?_ hLF
    · intro F s v hP hv
      obtain ⟨m, rfl, hm⟩ := dec_msg_init s hP.1 v hv
      refine ⟨⟨localsFree_evmMsgReady s _ _ hP.1, localsFree_stepFrom gw hp G ch s _ _ hP.2⟩,
        m, ?_, hm⟩
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    -- `dec te`
    refine Hoare.dec_fall (P' := D0Pre gw hp G ch) ?_ ?_ hLF
    · intro F s v hP _
      refine d0Pre_locals gw hp G ch s _ _ ?_ hP
      have hne : (ofString "te" == ofString "msg") = false := by decide
      simp [HolFiniteMapExact.update, FUPDATE, hne]
    -- `ite ...; (skip; prepare_dispatch(); skip; return 0)`
    refine Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) ?_ ?_ (fun _ h => h)
    · refine Hoare.ite_fall ?_ ?_
      · exact Hoare.mono (hoare_depth0_auth_branch gw hp G ch (hsd hp G ch)) (fun _ h => h.1)
      · exact Hoare.mono Hoare.skip_fall (fun _ h => h.1.1)
    · refine Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
        Hoare.skip_fall ?_ (fun _ h => h)
      refine Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) ?_ ?_ (fun _ h => h)
      · refine Hoare.mono (Hoare.weaken
          (Hoare.call_evmKeeps_fall (gw := gw) (hp := hp) (G := G) (ch := ch) hpd hsub
            (fun s h => evmMsgReady_of_evmInv s h.1) []) ?_) (fun _ h => h.2)
        intro F r t h hr
        exact ⟨evmMsgReady_of_evmInv t (h hr).1, h hr⟩
      · exact Hoare.seq_fall' (R := fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
          Hoare.skip_fall (Hoare.return_const_fall hLF 0) (fun _ h => h)
  refine ek_depth0_prepare_of_body (fun {F} s hcode hP hnt hres => ?_)
  have h := (hbody (globN s "heap_ptr") s.globals.lookup (evmChain s)).run s hcode
    ⟨hP, stepFrom_refl gw s (evmInv_of_evmMsgReady s hP)⟩ hnt (Or.inr hres)
  exact (evmStep_iff_stepFrom gw s _).2 h.2

/-! ## Generic handler-free call glue and the `set_delegation` bridge -/

/-- Handler-free, destination-free call of a `FunSpec` callee, `Fall` form: `Q` must follow from
the callee's postcondition on every resuming result, for every outer locals map (the call restores
the caller's locals on return and empties them on an exception). -/
theorem Hoare.call0_fall {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname)
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)), P s → Pc (callEntryStateHOLFinite s callee))
    (hpost : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (r : Option (PanSemResultExact 64))
      (post : PanSemStateFiniteExact 64 F), P s → Resumes r →
      Qc (callEntryStateHOLFinite s callee) r post →
      ∀ locals : HolFiniteMapExact MlS (ValueHOL 64), Q { post with locals := locals })
    (arguments : List (ExpHOL 64)) :
    Hoare P (.call (some (none, none)) fname arguments) (Fall Q) := by
  refine ⟨fun {F} s hcode hS hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt hr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) arguments with
    _ | values
  · rw [hargs] at hr
    rcases hr with hr | hr
    · cases hr
    · exact absurd hr not_resumes_error
  · simp only [hargs] at hnt hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hr
      rcases hr with hr | hr
      · cases hr
      · exact absurd hr not_resumes_error
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hPe : Pc (callEntryStateHOLFinite s callee) := hentry s callee hS
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hr ⊢
        have hQc (hsafe : res ≠ some .timeOut) :
            Qc (callEntryStateHOLFinite s callee) res post := by
          have := FunSpec.at_lookup hf s hcode values body' callee ret' hl hPe (by rw [hrun]; exact hsafe)
          rw [hrun] at this
          exact this
        cases res with
        | none =>
          rcases hr with hr | hr
          · cases hr
          · exact absurd hr not_resumes_error
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              exact hpost s callee _ post hS (Or.inl ⟨v, rfl⟩) (hQc (by simp)) s.locals
            · rename_i hsh
              rw [if_neg hsh]
              rcases hr with hr | hr
              · cases hr
              · exact absurd hr not_resumes_error
          | timeOut => simp at hnt
          | exception e v =>
            dsimp only at hr ⊢
            have hres : Resumes (some (.exception e v)) := by
              rcases hr with hr | hr
              · cases hr
              · exact hr
            exact hpost s callee _ post hS hres (hQc (by simp)) _
          | error =>
            rcases hr with hr | hr
            · cases hr
            · exact absurd hr not_resumes_error
          | _ =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

/-- A callee that keeps the owned message slot `ev+112` (word-level) on every resuming result;
what `set_delegation` needs beyond `EvmKeeps EvmMsgReady` for `depth0_prepare`'s `msg` local. -/
def KeepsMsgSlot (fname : MlS) : Prop :=
  FunSpec EvmMsgReady (fun s r post => Resumes r →
    memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)) fname

/-- A handler-free call of an `EvmKeeps EvmMsgReady gw_sd` callee that also keeps the message slot,
from a `D0Pre gw` state (`gw_sd ⊆ gw`, `ev ∉ gw`): the `D0CallPost` shape. -/
theorem hoare_call_d0CallPost_of_evmKeeps {gw gw_sd : List String} {fname : MlS}
    (hk : EvmKeeps EvmMsgReady gw_sd fname) (hslot : KeepsMsgSlot fname)
    (hsub : ∀ g ∈ gw_sd, g ∈ gw) (hev : ofString "ev" ∉ gw.map ofString)
    (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (D0Pre gw hp G ch) (.call (some (none, none)) fname [])
      (D0CallPost gw hp G ch) := by
  obtain ⟨params, body, ret, hlook, h1⟩ := hk
  obtain ⟨params2, body2, ret2, hlook2, h2⟩ := hslot
  rw [hlook] at hlook2
  obtain ⟨hpe, hbe, hre⟩ : params = params2 ∧ body = body2 ∧ ret = ret2 := by
    have := Option.some.inj hlook2
    exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj (Prod.mk.inj this).2).1,
      (Prod.mk.inj (Prod.mk.inj this).2).2⟩
  subst hpe hbe hre
  have hf : FunSpec (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
      (fun s r post => Resumes r → StepFrom gw hp G ch post ∧
        memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112)) fname :=
    ⟨params, body, ret, hlook, fun s hc hP hex hnt hres =>
      ⟨stepFrom_of_evmStep hsub hP.2 (h1 s hc hP.1 hex hnt hres), h2 s hc hP.1 hex hnt hres⟩⟩
  refine ⟨fun {F} s hcode hD hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  simp only [hargs] at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname [] with _ | ⟨body', callee, ret'⟩
  · simp only [hl]
    exact ⟨(fun h => by cases h), fun h => absurd h not_resumes_error⟩
  · simp only [hl] at hnt ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · simp only [hz, ↓reduceIte] at hnt ⊢
      have hSe := localsFree_stepFrom gw hp G ch s callee (s.clock - 1) hD.1.2
      have hPe : EvmMsgReady (callEntryStateHOLFinite s callee) ∧
          StepFrom gw hp G ch (callEntryStateHOLFinite s callee) :=
        ⟨evmMsgReady_of_evmInv _ hSe.1, hSe⟩
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
      simp only [hrun] at hnt ⊢
      have hQc (hsafe : res ≠ some .timeOut) : Resumes res → StepFrom gw hp G ch post ∧
          memW post (globN (callEntryStateHOLFinite s callee) "ev" + 112) =
            memW (callEntryStateHOLFinite s callee)
              (globN (callEntryStateHOLFinite s callee) "ev" + 112) := by
        have := FunSpec.at_lookup hf s hcode [] body' callee ret' hl hPe (by rw [hrun]; exact hsafe)
        rw [hrun] at this
        exact this
      obtain ⟨⟨hP, hS⟩, m, hm, hm_eq⟩ := hD
      have hGs := hS.2.2.1 (ofString "ev") hev
      have hpost (hres : Resumes res) (hsafe : res ≠ some .timeOut)
          (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
          EvmMsgReady { post with locals := locals } ∧
            StepFrom gw hp G ch { post with locals := locals } := by
        have hSl := localsFree_stepFrom gw hp G ch post locals post.clock (hQc hsafe hres).1
        exact ⟨evmMsgReady_of_evmInv _ hSl.1, hSl⟩
      have hmsg (hres : Resumes res) (hsafe : res ≠ some .timeOut) :
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
        have := (hQc hsafe hres).2
        simpa only [callEntryStateHOLFinite, globN, memW] using this
      cases res with
      | none => exact ⟨(fun h => by cases h), fun h => absurd h not_resumes_error⟩
      | some r =>
        cases r with
        | returned v =>
          dsimp only
          split
          · rename_i hsh
            refine ⟨fun _ => ?_, fun h => absurd h (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)⟩
            have hres : Resumes (some (.returned v)) := Or.inl ⟨v, rfl⟩
            have hSp := (hQc (by simp) hres).1
            have hGp := hSp.2.2.1 (ofString "ev") hev
            have hevN : globN post "ev" = globN s "ev" := by
              simp only [globN]; rw [← hGp, hGs]
            refine ⟨hpost hres (by simp) s.locals, m, hm, ?_⟩
            have hmsg' := hmsg hres (by simp)
            simp only [memW, globN] at hevN hm_eq hmsg' ⊢
            rw [hevN, hmsg']
            exact hm_eq
          · exact ⟨(fun h => by cases h), fun h => absurd h not_resumes_error⟩
        | timeOut => simp at hnt
        | exception e v =>
          dsimp only
          exact ⟨(fun h => by cases h), fun hres => hpost hres (by simp) _⟩
        | error => exact ⟨(fun h => by cases h), fun h => absurd h not_resumes_error⟩
        | _ => exact ⟨(fun h => by cases h), fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h⟩

/-- `ek_depth0_prepare` from pure callee contracts: `ek_set_delegation : EvmKeeps EvmMsgReady gw_sd`
together with message-slot preservation, and `ek_prepare_dispatch : EvmKeeps EvmMsgReady gw_pd`,
both `gw_* ⊆ ["heap_ptr", "journal_n", "scratch_ptr"]`. -/
theorem ek_depth0_prepare_of_ek {gw_sd gw_pd : List String}
    (hsd : EvmKeeps EvmMsgReady gw_sd (ofString "set_delegation"))
    (hslot : KeepsMsgSlot (ofString "set_delegation"))
    (hsub_sd : ∀ g ∈ gw_sd, g ∈ ["heap_ptr", "journal_n", "scratch_ptr"])
    (hpd : EvmKeeps EvmMsgReady gw_pd (ofString "prepare_dispatch"))
    (hsub_pd : ∀ g ∈ gw_pd, g ∈ ["heap_ptr", "journal_n", "scratch_ptr"]) :
    EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "depth0_prepare") :=
  ek_depth0_prepare_of_callees
    (fun hp G ch => hoare_call_d0CallPost_of_evmKeeps hsd hslot hsub_sd (by decide) hp G ch)
    hpd hsub_pd

/-! ## Word writes in the owned message record

The stores at offsets `104`, `112`, `120`, and `168` in `prepare_dispatch` all use
this rule.  The frame's message-pointer slot is preserved separately from the
message payload: subsequent calls can therefore retain the caller's `msg` local.
-/

theorem hoare_store_msg_word_step_with (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0Pre gw hp G ch s → L s.locals → ev s value = some v → ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (fun s => D0Pre gw hp G ch s ∧ L s.locals)) := by
  apply Hoare.store_fall_of_none
  refine ⟨fun {F} s _ ⟨hD, hL⟩ _ hnone => ?_⟩
  obtain ⟨⟨hP, hS⟩, m, hm, hm_eq⟩ := hD
  have hD : D0Pre gw hp G ch s := ⟨⟨hP, hS⟩, m, hm, hm_eq⟩
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      with ⟨res, post⟩
  rw [hrun] at hnone
  dsimp only at hnone ⊢
  subst res
  have hm_bnd : m.toNat + 176 ≤ 2 ^ 64 := by
    rw [hm_eq]
    exact allocated_le_2pow64 hP.1.2 hP.2.choose_spec.2.1
  obtain ⟨heff, hloc⟩ := M11.ByteRegionEffect.of_store_word
    (Rl := [(m.toNat, 176)]) hP.1.1.memaddrs hrun
    (fun v hv => hword s v hD hL (by simpa only [ev] using hv))
    (fun addr hdst _ => by
      refine ⟨(m.toNat, 176), List.mem_singleton.2 rfl, ?_⟩
      have haddr : addr.toNat = m.toNat + off := by
        simp [evalHOLExact, evalListHOLExact, hm, valueIsWord, valueWord, wordOpHOL, wordOp] at hdst
        subst hdst
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      dsimp only
      omega)
  have heff' : EvmStepLemmas.ByteRegionEffect s post
      [(memW s (globN s "ev" + 112), 176)] := by
    rw [← hm_eq]
    exact m11Bre_to_evmBre (fun i hi => by
      simp only [List.mem_singleton] at hi; subst hi; simp) heff
  have hstep : EvmStep [] s post :=
    ByteRegionEffect.to_evmStep_avoids (evmAvoids_msg_of_evmMsgReady s hP) heff'
  have hslot : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
    have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      unfold evmChain; exact List.mem_cons_self
    have hd := hP.2.choose_spec.2.2.2.2.2.1 _ hhead (globN s "ev", 280)
      (by simp [frameObjects])
    have hb := frameWF_bounds (hP.2.choose_spec.1.2.2.2.2.1 _ hhead)
    unfold memW
    rw [heff'.cell_frame _ ?_]
    intro i hi _ hhit
    simp only [List.mem_singleton] at hi
    subst i
    unfold CellHits at hhit
    have haddr : (BitVec.ofNat 64 (globN s "ev" + 112)).toNat = globN s "ev" + 112 :=
      Nat.mod_eq_of_lt (by omega)
    rw [haddr] at hhit
    rcases hd with hd | hd | hd | hd <;> dsimp only at hd <;> omega
  refine ⟨d0Pre_of_stepFrom gw hp G ch hD
    (stepFrom_of_evmStep (fun g hg => by simp at hg) hS hstep) hloc
    (congrArg (fun gs => gs.lookup (ofString "ev")) heff'.globals) hslot, ?_⟩
  rw [hloc]
  exact hL

theorem hoare_store_msg_word_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0Pre gw hp G ch s → ev s value = some v → ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (D0Pre gw hp G ch)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (D0Pre gw hp G ch)) := by
  have h := hoare_store_msg_word_step_with gw hp G ch off hoff value (fun _ => True)
    (fun s v hD _ hv => hword s v hD hv)
  exact Hoare.mono (Hoare.weaken h (fun _ _ h hr => (h hr).1)) (fun _ hD => ⟨hD, trivial⟩)

/-- A message store preserves all caller-local facts, including the code words needed
by the subsequent dispatch stores. -/
theorem hoare_store_msg_local_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off + 8 ≤ 176) (name : MlS) (w : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hL : ∀ locals, L locals → locals.lookup name = some (.val (.word w))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) (.var .local name))
      (Fall (fun s => D0Pre gw hp G ch s ∧ L s.locals)) := by
  apply hoare_store_msg_word_step_with gw hp G ch off hoff (.var .local name) L
  intro F s v _ hlocals hv
  simp only [ev, evalHOLExact, hL _ hlocals] at hv
  exact ⟨w, (Option.some.inj hv).symm⟩

theorem hoare_store_msg_const_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off + 8 ≤ 176) (w : BitVec 64) :
    Hoare (D0Pre gw hp G ch)
      (.store (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 off)]) (.const w))
      (Fall (D0Pre gw hp G ch)) := by
  apply hoare_store_msg_word_step gw hp G ch off hoff
  intro F s v _ hv
  exact ⟨w, (Option.some.inj hv).symm⟩

/-- The final two message stores of `prepare_dispatch`, preserving the code locals
for the subsequent head-frame stores and jump-destination computation. -/
theorem hoare_prepare_dispatch_msg_stores (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (.seq
        (.store (.op .add [.var .local (ofString "msg"), .const 112])
          (.var .local (ofString "code")))
        (.store (.op .add [.var .local (ofString "msg"), .const 120])
          (.var .local (ofString "code_n"))))
      (Fall (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))) := by
  let L : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun locals =>
    locals.lookup (ofString "code") = some (.val (.word code)) ∧
    locals.lookup (ofString "code_n") = some (.val (.word code_n))
  exact Hoare.seq_fall'
    (hoare_store_msg_local_step gw hp G ch 112 (by decide) (ofString "code") code L
      (fun _ h => h.1))
    (hoare_store_msg_local_step gw hp G ch 120 (by decide) (ofString "code_n") code_n L
      (fun _ h => h.2))
    (fun _ h => h)

/-- The delegated-code branch marks the message and records the freshly copied
address without invalidating its owned-record invariant or caller locals. -/
theorem hoare_prepare_dispatch_delegated_stores (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (daddr : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq
        (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
        (.store (.op .add [.var .local (ofString "msg"), .const 104])
          (.var .local (ofString "daddr"))))
      (Fall (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))) := by
  let L : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun locals =>
    locals.lookup (ofString "daddr") = some (.val (.word daddr))
  refine Hoare.seq_fall'
    (hoare_store_msg_word_step_with gw hp G ch 168 (by decide) (.const 1) L ?_)
    (hoare_store_msg_local_step gw hp G ch 104 (by decide) (ofString "daddr") daddr L
      (fun _ h => h)) (fun _ h => h)
  intro F s v _ _ hv
  exact ⟨1, (Option.some.inj hv).symm⟩

/-! ## Resuming loop rule for authorization processing -/

/-- A loop whose body preserves `P` on normal and resuming exits preserves `P`
on those exits too. `break` and `continue` are excluded explicitly, as they are
not covered by `Fall`. -/
theorem Hoare.while_fall {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body (Fall P))
    (hcontrol : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      (evaluateHOLFiniteState s body).1 ≠ some .break ∧
      (evaluateHOLFiniteState s body).1 ≠ some .continue) :
    Hoare P (.while cond body) (Fall P) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → P st →
      (evaluateHOLFiniteState st (.while cond body)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState st (.while cond body)).1 = none ∨
        Resumes (evaluateHOLFiniteState st (.while cond body)).1) →
      P (evaluateHOLFiniteState st (.while cond body)).2 from
    this s.clock s rfl hcode hP hnt hr
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hPs hnt hr
    rw [evaluateHOLFiniteState_while_total] at hnt hr ⊢
    split at hnt
    · rename_i w hw
      simp only [hw] at hr ⊢
      split at hnt
      · rename_i hwnz
        simp only [if_pos hwnz] at hr ⊢
        split at hnt
        · simp at hnt
        · rename_i hnz
          simp only [if_neg hnz] at hr ⊢
          dsimp only at hnt
          rw [fixClockHOLFinite_evaluateState] at hnt hr ⊢
          have hPd := hdec st hPs
          have hct : CondTrue cond (decClockHOLFinite st) := by
            obtain ⟨_, hw', hwnz'⟩ := loopActive_decClock (s := st) ⟨w, hw, hwnz⟩
            exact ⟨_, hw', hwnz'⟩
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hctrl := hcontrol (decClockHOLFinite st) hPd
          rcases hb : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hb] at hnt hr hmeta hclk hctrl
          have hmid (hntb : r ≠ some .timeOut) (hrb : r = none ∨ Resumes r) : P mid := by
            have hp := hbody.run (decClockHOLFinite st) hc ⟨hPd, hct⟩
              (by rw [hb]; exact hntb)
            rw [hb] at hp
            exact hp hrb
          cases r with
          | none =>
            exact ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hmeta.trans hc) (hmid (by simp) (Or.inl rfl)) hnt hr
          | some r =>
            cases r with
            | «break» => exact (hctrl.1 rfl).elim
            | «continue» => exact (hctrl.2 rfl).elim
            | timeOut => simp at hnt
            | _ => exact hmid (by simp) hr
      · rename_i hz
        simpa only [if_neg hz] using hPs
    · rename_i hbad
      simp only [hbad] at hr ⊢
      rcases hr with hr | hr
      · cases hr
      · exact absurd hr not_resumes_error

/-- Loading the owned message pointer establishes the common body invariant of
`set_delegation` and `prepare_dispatch`, retaining the original step origin. -/
theorem d0Pre_msg_init (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hP : EvmMsgReady s ∧ StepFrom gw hp G ch s)
    (hv : ev s (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) = some v) :
    D0Pre gw hp G ch (setVarHOLFinite (ofString "msg") v s) := by
  obtain ⟨m, rfl, hm⟩ := dec_msg_init s hP.1 v hv
  refine ⟨⟨localsFree_evmMsgReady s _ _ hP.1,
    localsFree_stepFrom gw hp G ch s _ _ hP.2⟩, m, ?_, hm⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Common message-pointer binder for the two depth-zero callees. The body's
postcondition is locals-free, so leaving the scope restores the caller's locals. -/
theorem hoare_dec_msg_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (body : ProgHOL 64)
    (hbody : Hoare (D0Pre gw hp G ch) body
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)
      (.dec (ofString "msg") .one
        (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) body)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.dec_fall (P' := D0Pre gw hp G ch) ?_ hbody ?_
  · intro F s v hP hv
    exact d0Pre_msg_init gw hp G ch s v hP hv
  · intro F s locals k hP
    exact ⟨localsFree_evmMsgReady s locals k hP.1,
      localsFree_stepFrom gw hp G ch s locals k hP.2⟩

/-- The source authorization loop contains no escaping loop-control statements.
The syntactic checks avoid a separate semantic side proof at every loop entry. -/
theorem Hoare.while_fall_checked {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body (Fall P))
    (hbreak : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hcontinue : noTopContinue body = true) :
    Hoare P (.while cond body) (Fall P) :=
  Hoare.while_fall hdec hbody (fun s _ =>
    ⟨InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hbreak s,
      evaluate_noTopContinue body hcontinue s⟩)

theorem lookup_set_delegation :
    originalRuntimeCode.lookup (ofString "set_delegation") =
      some ([], sourceFnBody Guest.Software.guestFn_set_delegation, .one) :=
  lookup_of_guestAst_getElem 575 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_delegation) rfl

theorem lookup_prepare_dispatch :
    originalRuntimeCode.lookup (ofString "prepare_dispatch") =
      some ([], sourceFnBody Guest.Software.guestFn_prepare_dispatch, .one) :=
  lookup_of_guestAst_getElem 576 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_prepare_dispatch) rfl

/-- Convert a body proof carrying the entry heap, globals and chain into the
callee's exact `EvmKeeps` contract. -/
theorem evmKeeps_of_stepFrom_body {fname : MlS} {params : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {ret : ShapeHOL} (gw : List String)
    (hlookup : originalRuntimeCode.lookup fname = some (params, body, ret))
    (hbody : ∀ (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl),
      Hoare (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) body
        (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    EvmKeeps EvmMsgReady gw fname := by
  refine ⟨params, body, ret, hlookup, fun s hc hP _ hnt hr => ?_⟩
  have h := (hbody (globN s "heap_ptr") s.globals.lookup (evmChain s)).run s hc
    ⟨hP, stepFrom_refl gw s (evmInv_of_evmMsgReady s hP)⟩ hnt (Or.inr hr)
  exact (evmStep_iff_stepFrom gw s _).2 h.2

theorem ek_set_delegation_of_body
    (hbody : ∀ (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl),
      Hoare (fun s => EvmMsgReady s ∧ StepFrom ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch s)
        (sourceFnBody Guest.Software.guestFn_set_delegation)
        (Fall (fun s => EvmMsgReady s ∧ StepFrom ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch s))) :
    EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "set_delegation") :=
  evmKeeps_of_stepFrom_body _ lookup_set_delegation hbody

theorem ek_prepare_dispatch_of_body
    (hbody : ∀ (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl),
      Hoare (fun s => EvmMsgReady s ∧ StepFrom ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch s)
        (sourceFnBody Guest.Software.guestFn_prepare_dispatch)
        (Fall (fun s => EvmMsgReady s ∧ StepFrom ["heap_ptr", "journal_n", "scratch_ptr"] hp G ch s))) :
    EvmKeeps EvmMsgReady ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "prepare_dispatch") :=
  evmKeeps_of_stepFrom_body _ lookup_prepare_dispatch hbody

/-- Local assignments in dispatch retain the owned message and step origin. -/
theorem hoare_assign_d0_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (name : MlS)
    (hne : name ≠ ofString "msg") (source : ExpHOL 64)
    (L L' : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hlocal : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      L s.locals → ev s source = some v → L' (setVarHOLFinite name v s).locals) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.assign .local name source) (Fall (fun s => D0Pre gw hp G ch s ∧ L' s.locals)) := by
  apply Hoare.assign
  · intro F s v hP hv _
    refine ⟨d0Pre_locals gw hp G ch s _ _ ?_ hP.1, hlocal s v hP.2 hv⟩
    simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update]
    simp [FUPDATE, hne]
  · intro F s _ hr
    rcases hr with hr | hr
    · cases hr
    · exact absurd hr not_resumes_error

/-- An assignment cannot resume, so sequencing it needs no implication from
the intermediate local predicate to the final one. -/
theorem Hoare.seq_assign_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name : MlS} {source : ExpHOL 64} {tail : ProgHOL 64}
    (ha : Hoare P (.assign .local name source) (Fall R))
    (ht : Hoare R tail (Fall Q)) :
    Hoare P (.seq (.assign .local name source) tail) (Fall Q) := by
  refine Hoare.seq (R := R) ?_ ht
  refine ⟨fun {F} s hc hP hnt => ?_⟩
  have h := ha.run s hc hP hnt
  refine ⟨fun hn => h (Or.inl hn), fun hn hr => ?_⟩
  have hnr : ¬ Resumes (evaluateHOLFiniteState s (.assign .local name source)).1 := by
    rw [evaluateHOLFiniteState_assign]
    repeat' split
    all_goals first | exact not_resumes_error | rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
  rcases hr with hr | hr
  · exact (hn hr).elim
  · exact (hnr hr).elim

/-- The delegated-code branch's final four instructions: unpack the returned
code pair, mark delegation and record the copied address. Both code words are
retained for the subsequent common dispatch tail. -/
theorem hoare_prepare_dispatch_delegated_finish (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n daddr : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
        (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
          (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
            (.store (.op .add [.var .local (ofString "msg"), .const 104])
              (.var .local (ofString "daddr"))))))
      (Fall (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)) ∧
        s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))) := by
  let L0 : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun l =>
    l.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
    l.lookup (ofString "daddr") = some (.val (.word daddr))
  let L1 : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun l =>
    l.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
    l.lookup (ofString "daddr") = some (.val (.word daddr)) ∧
    l.lookup (ofString "code") = some (.val (.word code))
  let L2 : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun l =>
    l.lookup (ofString "code") = some (.val (.word code)) ∧
    l.lookup (ofString "code_n") = some (.val (.word code_n)) ∧
    l.lookup (ofString "daddr") = some (.val (.word daddr))
  have hcd : ofString "code" ≠ ofString "dcode" := by decide
  have hca : ofString "code" ≠ ofString "daddr" := by decide
  have hnc : ofString "code_n" ≠ ofString "code" := by decide
  have hna : ofString "code_n" ≠ ofString "daddr" := by decide
  refine Hoare.seq_assign_fall
    (hoare_assign_d0_step gw hp G ch (ofString "code") (by decide) _ L0 L1 ?_) ?_
  · intro F s v hL hv
    have hv' : v = .val (.word code) := by
      simpa [ev, evalHOLExact, hL.1] using hv.symm
    subst v
    dsimp [L1]
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcd, hca, L0] using
      (show L0 s.locals ∧ True from ⟨hL, trivial⟩)
  · refine Hoare.seq_assign_fall
      (hoare_assign_d0_step gw hp G ch (ofString "code_n") (by decide) _ L1 L2 ?_)
      ?_
    · intro F s v hL hv
      have hv' : v = .val (.word code_n) := by
        simpa [ev, evalHOLExact, hL.1] using hv.symm
      subst v
      dsimp [L2]
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnc, hna] using
        (show s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
          s.locals.lookup (ofString "daddr") = some (.val (.word daddr)) from ⟨hL.2.2, hL.2.1⟩)
    · exact Hoare.seq_fall'
        (hoare_store_msg_word_step_with gw hp G ch 168 (by decide) (.const 1) L2
          (fun _ v _ _ hv => ⟨1, (Option.some.inj hv).symm⟩))
        (hoare_store_msg_local_step gw hp G ch 104 (by decide) (ofString "daddr") daddr L2
          (fun _ h => h.2.2)) (fun _ h => h)

/-- After finishing the delegated branch, the common message-code stores
retain the code locals needed by the head-frame update. -/
theorem hoare_prepare_dispatch_delegated_msg_tail (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n daddr : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq
        (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
          (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
            (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
              (.store (.op .add [.var .local (ofString "msg"), .const 104])
                (.var .local (ofString "daddr"))))))
        (.seq (.store (.op .add [.var .local (ofString "msg"), .const 112])
            (.var .local (ofString "code")))
          (.store (.op .add [.var .local (ofString "msg"), .const 120])
            (.var .local (ofString "code_n")))))
      (Fall (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))) := by
  have hfinish := hoare_prepare_dispatch_delegated_finish gw hp G ch code code_n daddr
  have hfinish' := Hoare.weaken (Q' := Fall (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))))
    hfinish (fun _ _ h hr => let h' := h hr; ⟨h'.1, h'.2.1, h'.2.2.1⟩)
  exact Hoare.seq_fall' hfinish'
    (hoare_prepare_dispatch_msg_stores gw hp G ch code code_n) (fun _ h => h)

/-- Reassociate a verified sequence to the right-associated source AST. -/
theorem Hoare.seq_assoc_fall
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {a b c : ProgHOL 64}
    (h : Hoare P (.seq (.seq a b) c) (Fall Q)) :
    Hoare P (.seq a (.seq b c)) (Fall Q) := by
  refine ⟨fun {F} s hc hp hnt => ?_⟩
  have heq := srd_eval_seq_assoc s a b c
  rw [← heq] at hnt ⊢
  exact h.run s hc hp hnt

theorem eval_seq_assoc_six {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b c d e f : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq a (.seq (.seq b (.seq c d)) (.seq e f))) =
      evaluateHOLFiniteState s (.seq a (.seq b (.seq c (.seq d (.seq e f))))) := by
  have ht : ∀ t : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState t (.seq (.seq b (.seq c d)) (.seq e f)) =
        evaluateHOLFiniteState t (.seq b (.seq c (.seq d (.seq e f)))) := by
    intro t
    rw [srd_eval_seq_assoc]
    conv_lhs => rw [evaluateHOLFiniteState_seq_line780]
    conv_rhs => rw [evaluateHOLFiniteState_seq_line780]
    rcases evaluateHOLFiniteState t b with ⟨r, u⟩
    cases r with
    | none => exact srd_eval_seq_assoc u c d (.seq e f)
    | some _ => rfl
  conv_lhs => rw [evaluateHOLFiniteState_seq_line780]
  conv_rhs => rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨r, t⟩
  cases r with
  | none => exact ht t
  | some _ => rfl

/-- The delegated message tail in the right-associated shape emitted by the
source translator. -/
theorem hoare_prepare_dispatch_delegated_msg_tail_source (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n daddr : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
        (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
          (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
            (.seq (.store (.op .add [.var .local (ofString "msg"), .const 104])
                (.var .local (ofString "daddr")))
              (.seq (.store (.op .add [.var .local (ofString "msg"), .const 112])
                  (.var .local (ofString "code")))
                (.store (.op .add [.var .local (ofString "msg"), .const 120])
                  (.var .local (ofString "code_n"))))))))
      (Fall (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))) := by
  have h := Hoare.seq_assoc_fall
    (hoare_prepare_dispatch_delegated_msg_tail gw hp G ch code code_n daddr)
  refine ⟨fun {F} s hc hp hnt => ?_⟩
  have hr := h.run s hc hp
  rw [eval_seq_assoc_six] at hr
  exact hr hnt

/-- Dispatch's code pointer, length and jump-destination slots do not contribute
to any frame-owned interval. This bridge exposes the exact unchanged footprint
needed when transporting the head invariant through those stores. -/
theorem frameObjects_eq_of_dispatch_slots {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (ec : Ivl)
    (hkeep : ∀ k, k + 8 ≤ 280 → k ∉ ([48, 56, 80] : List Nat) →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) =
      memW s (memW s (ec.1 + 88) + k))
    (hlogs : frameLogObjects post ec = frameLogObjects s ec) :
    frameObjects post ec = frameObjects s ec ∧
      frameScratch post ec = frameScratch s ec ∧
      frameRoleSlots post [ec] = frameRoleSlots s [ec] := by
  have h8 := hkeep 8 (by decide) (by decide)
  have h24 := hkeep 24 (by decide) (by decide)
  have h40 := hkeep 40 (by decide) (by decide)
  have h88 := hkeep 88 (by decide) (by decide)
  have h232 := hkeep 232 (by decide) (by decide)
  have hfl : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs
    rw [h88]
    rw [show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hheader 0 (by decide), hheader 16 (by decide)]
  have hfr : frameRet post ec = frameRet s ec := by
    unfold frameRet
    rw [hkeep 216 (by decide) (by decide), hkeep 144 (by decide) (by decide)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [frameObjects, h8, h24, h40, h88, h232, hfl, hfr, hlogs]
  · simp only [frameScratch, h8, h88, h232]
  · simp only [frameRoleSlots, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      hkeep 136 (by decide) (by decide), hkeep 168 (by decide) (by decide),
      hkeep 176 (by decide) (by decide)]

/-- Transport frame well-formedness across the three dispatch slots once the
owned message and log predicates have been transported. -/
theorem frameWF_of_dispatch_slots {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (hfw : FrameWF s S ec) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hg : ∀ name, globN post name = globN s name)
    (hkeep : ∀ k, k + 8 ≤ 280 → k ∉ ([48, 56, 80] : List Nat) →
      memW post (ec.1 + k) = memW s (ec.1 + k))
    (hheader : ∀ k, k + 8 ≤ 24 → memW post (memW s (ec.1 + 88) + k) =
      memW s (memW s (ec.1 + 88) + k))
    (hlogs : LogsListOK post (memW s (ec.1 + 88)))
    (hmsg : MsgOwned post S (memW s (ec.1 + 112))) :
    FrameWF post S ec := by
  have hfl : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs
    rw [hkeep 88 (by decide) (by decide)]
    rw [show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hheader 0 (by decide), hheader 16 (by decide)]
  have hfr : frameRet post ec = frameRet s ec := by
    unfold frameRet
    rw [hkeep 216 (by decide) (by decide), hkeep 144 (by decide) (by decide)]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
    c14, c15, _, _⟩ := hfw
  unfold FrameWF
  dsimp only
  rw [hkeep 8 (by decide) (by decide), hkeep 232 (by decide) (by decide),
    hkeep 88 (by decide) (by decide), hkeep 24 (by decide) (by decide),
    hkeep 40 (by decide) (by decide), hkeep 16 (by decide) (by decide),
    hkeep 32 (by decide) (by decide), hkeep 136 (by decide) (by decide),
    hkeep 168 (by decide) (by decide), hkeep 176 (by decide) (by decide),
    hheader 16 (by decide), hheader 8 (by decide), hfl,
    hkeep 216 (by decide) (by decide), hkeep 144 (by decide) (by decide), hfr,
    hkeep 112 (by decide) (by decide), hg "scratch_ptr", hg "frame_mem_ptr",
    hg "heap_ptr", hg "evm_empty"]
  refine ⟨?_, c2, wordsOK_transfer hAs.1 hAp.1 c3, c4, c5, c6, c7,
    c8, c9, c10, c11, c12, c13, wordsOK_transfer hAs.1 hAp.1 c14, ?_, hlogs, hmsg⟩
  · intro i hi
    obtain ⟨hin, hw⟩ := c1 i hi
    exact ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩
  · rcases c15 with hz | ⟨hin, hw⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hin, wordsOK_transfer hAs.1 hAp.1 hw⟩

/-- The three dispatch fields are outside every structural frame projection.
This packages their transport into the complete chain invariant. -/
theorem evmInvAt_of_frame_transport {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hfwpost : ∀ ec ∈ evmChain s, FrameWF post S ec)
    (hch : evmChain post = evmChain s)
    (hworld : WorldTyped post S)
    (hkeep : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 →
      k ∉ ([48, 56, 80] : List Nat) → memW post (ec.1 + k) = memW s (ec.1 + k))
    (hc : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hh : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hl : ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec ∧
      LogsListOK post (memW s (ec.1 + 88)))
    (hm : ∀ m, MsgOwned s S m → MsgOwned post S m)
    (hfix : fixedObjects post = fixedObjects s)
    (hfp : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (htries : ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd)
    (hwr : worldRoleSlots post = worldRoleSlots s)
    (hjr : journalRoleSlots post = journalRoleSlots s)
    (hwrefs : worldTableRefs post S = worldTableRefs s S)
    (htag : ∀ t ∈ S, memW post t = memW s t) :
    EvmInvAt post S := by
  obtain ⟨hw, hn, hlen, hlast, hfw, hroom, hwin, hpw, hdisj, hat,
    hmarks, hroles, hgas⟩ := hInv
  have hfo : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec :=
    fun ec hec => (frameObjects_eq_of_dispatch_slots ec (hkeep ec hec)
      (hh ec hec) (hl ec hec).1).1
  have hfs : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec :=
    fun ec hec => (frameObjects_eq_of_dispatch_slots ec (hkeep ec hec)
      (hh ec hec) (hl ec hec).1).2.1
  have hfl : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    unfold frameLogs
    rw [hkeep ec hec 88 (by decide) (by decide)]
    rw [show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hh ec hec 0 (by decide), hh ec hec 16 (by decide)]
  have hmap : (evmChain s).map (frameObjects post) = (evmChain s).map (frameObjects s) :=
    List.map_congr_left hfo
  have hslots : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots
    apply List.flatMap_congr
    intro ec hec
    rw [hkeep ec hec 136 (by decide) (by decide),
      hkeep ec hec 168 (by decide) (by decide), hkeep ec hec 176 (by decide) (by decide)]
  refine ⟨hworld, ?_⟩
  dsimp only
  rw [hch]
  refine ⟨hn, hlen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hz⟩ := hlast
    exact ⟨ec, hec, by rw [hc ec (List.mem_of_mem_getLast? hec) 16 (by decide)]; exact hz⟩
  · exact hfwpost
  · intro ec hec
    have he := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [hkeep ec he 16 (by decide) (by decide), hkeep ec he 232 (by decide) (by decide)]
    exact hroom ec hec
  · intro i hi
    have h0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have h1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [hc _ h0 80 (by decide), hc _ h0 72 (by decide),
      hkeep _ h1 40 (by decide) (by decide)]
    exact hwin i hi
  · rw [hmap]; exact hpw
  · intro ec hec o ho
    rw [hfo ec hec] at ho
    rw [hfix]
    refine ⟨fun t ht i hi => ?_, (hdisj ec hec o ho).2⟩
    rw [hfp t ht] at hi
    exact (hdisj ec hec o ho).1 t ht i hi
  · obtain ⟨Nd, ht, hd⟩ := hat
    rw [hmap]
    refine ⟨Nd, (htries Nd ht).1, fun o ho j hj => ?_⟩
    rw [(htries Nd ht).2] at hj
    exact hd o ho j hj
  · have hdel : ∀ i t, DelExclusive post S (evmChain s) i t ↔
        DelExclusive s S (evmChain s) i t := by
      intro i t
      unfold DelExclusive
      rw [hwrefs]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hk' : k + 8 ≤ 280 ∧ k ∉ ([48, 56, 80] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      rw [hkeep _ (List.getElem_mem _) k hk'.1 hk'.2]
    intro i hi
    have hi' : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have htake : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left
      intro ec hec
      exact hkeep ec (List.mem_of_mem_take hec) 136 (by decide) (by decide)
    dsimp only
    rw [hc _ hi' 48 (by decide), hc _ hi' 56 (by decide),
      hkeep _ hi' 24 (by decide) (by decide), hfs _ hi', hfix, htake]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hmarks i hi
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj' : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hfs _ hj', hfo _ hj', hfl _ hj', hkeep _ hj' 112 (by decide) (by decide)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp t ht, hdel i t]
      exact m8 t ht
  · rw [hwr, hslots, hjr]
    unfold RolesOK at hroles ⊢
    refine ⟨fun a ha => ?_, hroles.2⟩
    obtain ⟨haS, hk⟩ := hroles.1 a ha
    change a.1 ∈ S ∧ memW post (a.1 + 0) = roleKeyLen a.2
    simp only [Nat.add_zero]
    rw [htag a.1 haS]
    exact ⟨haS, hk⟩
  · have heq : ((evmChain s).map fun ec => memW post (ec.1 + 64) +
        memW post (ec.1 + 192)) = ((evmChain s).map fun ec =>
        memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
      apply List.map_congr_left
      intro ec hec
      rw [hkeep ec hec 64 (by decide) (by decide), hkeep ec hec 192 (by decide) (by decide)]
    rw [heq]
    exact hgas

/-- Dispatch-slot specialization of the chain-invariant assembly rule. -/
theorem evmInvAt_of_dispatch_transport {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInvAt s S) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hg : ∀ name, globN post name = globN s name)
    (hch : evmChain post = evmChain s)
    (hworld : WorldTyped post S)
    (hkeep : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 280 →
      k ∉ ([48, 56, 80] : List Nat) → memW post (ec.1 + k) = memW s (ec.1 + k))
    (hc : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k))
    (hh : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k))
    (hl : ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec ∧
      LogsListOK post (memW s (ec.1 + 88)))
    (hm : ∀ m, MsgOwned s S m → MsgOwned post S m)
    (hfix : fixedObjects post = fixedObjects s)
    (hfp : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (htries : ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd)
    (hwr : worldRoleSlots post = worldRoleSlots s)
    (hjr : journalRoleSlots post = journalRoleSlots s)
    (hwrefs : worldTableRefs post S = worldTableRefs s S)
    (htag : ∀ t ∈ S, memW post t = memW s t) :
    EvmInvAt post S := by
  apply evmInvAt_of_frame_transport hInv hAs hAp ?_ hch hworld hkeep hc hh hl hm
    hfix hfp htries hwr hjr hwrefs htag
  intro ec hec
  have hfw := hInv.2.2.2.2.1 ec hec
  exact frameWF_of_dispatch_slots hfw hAs hAp hg (hkeep ec hec) (hh ec hec)
    (hl ec hec).2 (hm _ hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)

/-- A dispatch-field write preserves the structural words of every frame,
every continuation and every logs header, including suspended ancestors. -/
theorem dispatch_store_chain_words {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    {x : BitVec 64} {k : Nat} (hk : k ∈ ([48, 56, 80] : List Nat))
    (hx : x.toNat = globN s "ev" + k)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 280 →
      j ∉ ([48, 56, 80] : List Nat) → memW post (ec.1 + j) = memW s (ec.1 + j)) ∧
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 104 →
      memW post (ec.2 + j) = memW s (ec.2 + j)) ∧
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + j) = memW s (memW s (ec.1 + 88) + j)) := by
  obtain ⟨hAs, S, hI⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  have hklt : k + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  have hpoint : ∀ a, a < 2 ^ 64 → a ≠ globN s "ev" + k → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem (BitVec.ofNat 64 a) ?_]
    intro heq
    have he := congrArg BitVec.toNat heq
    rw [hx, show (BitVec.ofNat 64 a).toNat = a from Nat.mod_eq_of_lt ha] at he
    exact hne he
  have hpw := hI.2.2.2.2.2.2.2.1
  have hfw := hI.2.2.2.2.1
  have hcons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
  obtain ⟨tl, htl⟩ := hcons
  rw [htl, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
  have hhead_disj : ∀ o ∈ [(globN s "cur_cont", 104),
      (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
      (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)),
      (memW s (globN s "ev" + 88), 24), frameLogs s (globN s "ev", globN s "cur_cont"),
      frameRet s (globN s "ev", globN s "cur_cont")], Disj (globN s "ev", 280) o := by
    have h := hpw.1
    unfold frameObjects at h
    simp only [List.cons_append, List.pairwise_cons] at h
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h.1 _ (by simp)
  have htail : ∀ ec ∈ tl, ∀ o ∈ frameObjects s ec, Disj (globN s "ev", 280) o := by
    intro ec hec o ho
    apply hpw.2.2 (globN s "ev", 280) (by simp [frameObjects]) o
    exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩
  have hdisj : ∀ {base n : Nat}, Disj (globN s "ev", 280) (base, n) →
      ∀ j, j + 8 ≤ n → base + j ≠ globN s "ev" + k := by
    intro base n hd j hj
    rcases hd with hd | hd | hd | hd <;> dsimp only at hd <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec j hj hnot
    have hb := (frameWF_bounds (hfw ec hec)).1
    apply hpoint _ (by omega)
    rw [htl, List.mem_cons] at hec
    rcases hec with rfl | hec
    · dsimp only
      intro heq
      have hjk : j = k := by omega
      exact hnot (hjk ▸ hk)
    · exact hdisj (htail ec hec (ec.1, 280) (by simp [frameObjects])) j hj
  · intro ec hec j hj
    have hb := (frameWF_bounds (hfw ec hec)).2.1
    apply hpoint _ (by omega)
    apply hdisj (n := 104) (j := j) ?_ hj
    rw [htl, List.mem_cons] at hec
    rcases hec with rfl | hec
    · exact hhead_disj _ (by simp)
    · exact htail ec hec _ (by simp [frameObjects])
  · intro ec hec j hj
    have hb := (frameWF_bounds (hfw ec hec)).2.2
    apply hpoint _ (by omega)
    apply hdisj (n := 24) (j := j) ?_ hj
    rw [htl, List.mem_cons] at hec
    rcases hec with rfl | hec
    · exact hhead_disj _ (by simp)
    · exact htail ec hec _ (by simp [frameObjects])

/-- Continuation-word preservation suffices to transport the bounded frame
chain, independently of changes to dispatch's code fields. -/
theorem evmChain_eq_of_cont_words {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hg : ∀ name, globN post name = globN s name)
    (hc : ∀ ec ∈ evmChain s, ∀ k, k + 8 ≤ 104 →
      memW post (ec.2 + k) = memW s (ec.2 + k)) :
    evmChain post = evmChain s := by
  have haux : ∀ fuel e c,
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      have h0 : memW post c = memW s c := by
        simpa only [Nat.add_zero] using hc (e, c) hec 0 (by decide)
      simp only [evmChainFrom, hc (e, c) hec 16 (by decide), h0,
        hc (e, c) hec 8 (by decide)]
      split
      · rfl
      · rename_i hn
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec he
        apply hsub ec
        simp only [evmChainFrom, hn, ↓reduceIte, List.mem_cons]
        exact Or.inr he
  unfold evmChain
  rw [hg "ev", hg "cur_cont"]
  exact haux _ _ _ (fun _ h => h)

/-- The head record is separated from every typed world cell and trie node.
This is the world-side premise for dispatch's three frame-local stores. -/
theorem head_store_world_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hInv : EvmInvAt s S) (_hTr : TriesTypedWith s S Nd)
    {x : BitVec 64} {k : Nat} (hk : k + 8 ≤ 280)
    (hx : x.toNat = globN s "ev" + k)
    (hNodes : ∀ j ∈ nodeExtents s Nd, Disj (globN s "ev", 280) j) :
    ∀ j ∈ worldTypedIvls s S Nd, Disj j (x.toNat, 8) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  have hfo : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
    simp [frameObjects]
  have hdisj := hInv.2.2.2.2.2.2.2.2.1 _ hhead _ hfo
  have hin : Inside (x.toNat, 8) (globN s "ev") (globN s "ev" + 280) := by
    unfold Inside
    rw [hx]
    dsimp only
    omega
  intro j hj
  apply disj_of_inside_right (j' := (globN s "ev", 280)) hin
  unfold worldTypedIvls at hj
  simp only [List.mem_append] at hj
  rcases hj with ((((h1 | h2) | h3) | h4) | h5) | h6
  · obtain ⟨t, ht, hi⟩ := List.mem_flatMap.1 h1
    exact (hdisj.1 t ht j hi).flip
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
    exact (hdisj.2 _ (typedRecord_mem_fixedObjects s hr)).flip
  · simp only [List.mem_singleton] at h3
    subst h3
    have hj : (if globN s "journal_cap" = 0 then 0 else globN s "journal",
        32 * globN s "journal_cap") ∈ fixedObjects s := by
      unfold fixedObjects
      apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; right; simp
    exact (hdisj.2 _ hj).flip
  · have hj : j ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr h4)))
    exact (hdisj.2 _ hj).flip
  · have hj : j ∈ fixedObjects s := by
      unfold fixedObjects
      exact List.mem_append.2 (Or.inr h5)
    exact (hdisj.2 _ hj).flip
  · exact (hNodes j h6).flip

/-- World typing and all world-side projections survive a word write to the
head record. Trie witnesses are retained rather than chosen afresh. -/
theorem dispatch_store_world_transport {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hInv : EvmInvAt s S) (hTr : TriesTypedWith s S Nd)
    {x : BitVec 64} {k : Nat} (hk : k + 8 ≤ 280)
    (hx : x.toNat = globN s "ev" + k) (hdom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a)
    (hNodes : ∀ j ∈ nodeExtents s Nd, Disj (globN s "ev", 280) j) :
    ArenaReady post ∧ WorldTypedWith post S Nd ∧
      fixedObjects post = fixedObjects s ∧ nodeExtents post Nd = nodeExtents s Nd ∧
      worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s ∧
      (∀ t ∈ S, (∀ j, j < 11 → hdr post t j = hdr s t j) ∧
        htabFootprint post t = htabFootprint s t) ∧
      worldTableRefs post S = worldTableRefs s S := by
  have hW := hInv.1
  have hWT : WorldTypedWith s S Nd := ⟨hW.1, hW.2.1, hW.2.2.1, hTr⟩
  exact worldTypedWith_store_word_disj hAs hdom hpost hWT
    (head_store_world_disj hInv hTr hk hx hNodes)

/-- Head-frame scratch stores are above every heap-resident trie node, so
all existing trie witnesses can be transported through the same store. -/
theorem dispatch_store_all_tries {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hInv : EvmInvAt s S)
    {x : BitVec 64} {k : Nat} (hk : k + 8 ≤ 280)
    (hx : x.toNat = globN s "ev" + k) (hdom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    ∀ Nd, TriesTypedWith s S Nd →
      TriesTypedWith post S Nd ∧ nodeExtents post Nd = nodeExtents s Nd := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  have hin := ((hInv.2.2.2.2.1 _ hhead).1 (globN s "ev", 280) (by simp)).1
  have helo : heapLimit ≤ globN s "ev" := by
    have hsep : heapLimit ≤ scratchStart := by decide
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    dsimp [Inside] at hin
    omega
  intro Nd ht
  have hnodes : ∀ j ∈ nodeExtents s Nd, Disj (globN s "ev", 280) j := by
    intro j hj
    unfold nodeExtents at hj
    obtain ⟨n, hn, hj⟩ := List.mem_flatMap.1 hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · have h := (ht.1.1 n hn).2.2.1
      exact Or.inr (Or.inr (Or.inr (le_trans h.2 helo)))
    · unfold nodePath
      split_ifs with hcond
      · rcases (ht.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with hz | ⟨_, _, h, _⟩
        · exact absurd hz hcond.2
        · exact Or.inr (Or.inr (Or.inr (le_trans h.2 helo)))
      · exact disj_zero_right _
  have h := dispatch_store_world_transport hAs hInv ht hk hx hdom hpost hnodes
  exact ⟨h.2.1.2.2.2, h.2.2.2.1⟩

/-- A head-record store leaves the entire heap unchanged. -/
theorem head_store_heap_words {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    {x : BitVec 64} {k : Nat} (hx : x.toNat = globN s "ev" + k)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    ∀ a, a < heapLimit → memW post a = memW s a := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  obtain ⟨hAs, S, hI⟩ := hInv
  have hin := ((hI.2.2.2.2.1 _ hhead).1 (globN s "ev", 280) (by simp)).1
  have hxlo : heapLimit ≤ x.toNat := by
    have hsep : heapLimit ≤ scratchStart := by decide
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    dsimp [Inside] at hin
    omega
  intro a ha
  unfold memW
  rw [hmem (BitVec.ofNat 64 a) ?_]
  intro heq
  have hlim : heapLimit ≤ 2 ^ 64 := by decide
  have he := congrArg BitVec.toNat heq
  rw [show (BitVec.ofNat 64 a).toNat = a from Nat.mod_eq_of_lt (by omega)] at he
  omega

/-- The head record is disjoint from every chain frame's logs header and
backing array, so a store to it cannot invalidate live log entries. -/
theorem head_store_logs_disj {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) :
    ∀ ec ∈ evmChain s,
      Disj (globN s "ev", 280) (memW s (ec.1 + 88), 24) ∧
      Disj (globN s "ev", 280) (frameLogs s ec) := by
  obtain ⟨_, S, hI⟩ := hInv
  have hpw := hI.2.2.2.2.2.2.2.1
  have hcons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
  obtain ⟨tl, htl⟩ := hcons
  rw [htl, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
  intro ec hec
  rw [htl, List.mem_cons] at hec
  rcases hec with rfl | hec
  · have h := hpw.1
    unfold frameObjects at h
    simp only [List.cons_append, List.pairwise_cons] at h
    exact ⟨h.1 _ (by simp), h.1 _ (by simp)⟩
  · have h : ∀ o ∈ frameObjects s ec, Disj (globN s "ev", 280) o := by
      intro o ho
      apply hpw.2.2 _ (by simp [frameObjects]) o
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map.2 ⟨ec, hec, rfl⟩, ho⟩
    exact ⟨h _ (by simp [frameObjects]), h _ (by simp [frameObjects])⟩

/-- Live log lists remain valid under a dispatch-field store. -/
theorem dispatch_store_logs_ok {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) (hAp : ArenaReady post)
    (hg : ∀ name, globN post name = globN s name)
    {x : BitVec 64} {k : Nat} (hk : k + 8 ≤ 280)
    (hx : x.toNat = globN s "ev" + k)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    ∀ ec ∈ evmChain s, LogsListOK post (memW s (ec.1 + 88)) := by
  have hdisj := head_store_logs_disj hInv
  have hheap := head_store_heap_words hInv hx hmem
  obtain ⟨hAs, S, hI⟩ := hInv
  have hin : Inside (x.toNat, 8) (globN s "ev") (globN s "ev" + 280) := by
    unfold Inside
    rw [hx]
    dsimp only
    omega
  intro ec hec
  have hfw := hI.2.2.2.2.1 ec hec
  have hd := hdisj ec hec
  apply logsListOK_transfer hAs.1 hAp.1 (hg "heap_ptr") (hg "scratch_ptr")
    hAs.2 hmem hheap
  · intro _
    exact disj_of_inside_right hin hd.1.flip
  · intro _
    exact disj_of_inside_right hin hd.2.flip
  · intro _
    have hal : Allocated s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hw : WordsOK s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨hw.1, (ivl_allocated_bound hAs.2 hal).2⟩
  · exact hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Dispatch stores preserve the intervals occupied by every live log. -/
theorem dispatch_store_log_objects {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hg : ∀ name, globN post name = globN s name)
    {x : BitVec 64} {k : Nat} (hk : k ∈ ([48, 56, 80] : List Nat))
    (hx : x.toNat = globN s "ev" + k)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec := by
  have hwords := dispatch_store_chain_words hInv hk hx hmem
  have hheap := head_store_heap_words hInv hx hmem
  have hdisj := head_store_logs_disj hInv
  obtain ⟨hAs, S, hI⟩ := hInv
  have hklt : k + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  have hin : Inside (x.toNat, 8) (globN s "ev") (globN s "ev" + 280) := by
    unfold Inside
    rw [hx]
    dsimp only
    omega
  intro ec hec
  have hfw := hI.2.2.2.2.1 ec hec
  have hh := hwords.2.2 ec hec
  unfold frameLogObjects
  dsimp only
  rw [hwords.1 ec hec 88 (by decide) (by decide), hh 8 (by decide),
    show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hh 0 (by decide)]
  apply List.flatMap_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  have hle := hfw.2.2.2.2.2.2.2.2.2.2.2.1
  have hal : Allocated s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := (ivl_allocated_bound hAs.2 hal).2
  have hbase8 : memW s (memW s (ec.1 + 88)) % 8 = 0 :=
    hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  have hslot : memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
      memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
    apply R10Shards.GbodyProcessMsg.memW_eq_of_ivlUnhit
      (ivlUnhit_of_single_cell_disj hmem (disj_of_inside_right hin (hdisj ec hec).2.flip))
      (by omega) hb
    unfold frameLogs
    dsimp only
    exact ⟨by omega, by omega⟩
  rw [hslot]
  have hll := hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hll with hz | ⟨_, _, _, _, hentries⟩
  · have hs := (hfw.1 (memW s (ec.1 + 88), 24) (by simp)).1
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    have hpos : 0 < scratchStart := by decide
    unfold Inside at hs
    dsimp only at hs
    omega
  · have hlog := (hentries i hi').2.2.1
    have hhp := hAs.2.2.1
    unfold Inside at hlog
    dsimp only at hlog
    unfold logOwnedIvls logRecordIvls
    rw [hg "vm_system_address", hheap _ (by omega), hheap _ (by omega),
      hheap _ (by omega), hheap _ (by omega), hheap _ (by omega)]

/-- The head-store invariant bridge for dispatch's code, size and jumpdest
fields. No assumption about the stored word is needed. -/
theorem evmMsgReady_store_dispatch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hP : EvmMsgReady s)
    {x : BitVec 64} {k : Nat} (hk : k ∈ ([48, 56, 80] : List Nat))
    (hx : x.toNat = globN s "ev" + k) (hdom : s.memaddrs x)
    (hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    EvmMsgReady post ∧ EvmStep [] s post := by
  have hInv := evmInv_of_evmMsgReady s hP
  have hwords := dispatch_store_chain_words hInv hk hx hpost.2.2.2.2.2.2
  have hg : ∀ name, globN post name = globN s name := fun name => by
    simp [globN, hpost.2.2.2.2.2.1]
  have hch := evmChain_eq_of_cont_words hg hwords.2.1
  have hlogs := dispatch_store_log_objects hInv hg hk hx hpost.2.2.2.2.2.2
  obtain ⟨hAs, S, hI, hmsg⟩ := hP
  obtain ⟨Nd, ht, hd⟩ := hI.2.2.2.2.2.2.2.2.2.1
  have hklt : k + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl <;> decide
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  have hheadflat : (globN s "ev", 280) ∈ ((evmChain s).map (frameObjects s)).flatten := by
    exact List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
      List.mem_map.2 ⟨_, hhead, rfl⟩, by simp [frameObjects]⟩
  obtain ⟨hAp, hWT, hfix, hnd, hwr, hjr, hfp, hrefs⟩ :=
    dispatch_store_world_transport hAs hI ht hklt hx hdom hpost
      (fun j hj => hd _ hheadflat j hj)
  have htries := dispatch_store_all_tries hAs hI hklt hx hdom hpost
  have hfo : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec :=
    fun ec hec => (frameObjects_eq_of_dispatch_slots ec (hwords.1 ec hec)
      (hwords.2.2 ec hec) (hlogs ec hec)).1
  have hm : ∀ m, MsgOwned s S m → MsgOwned post S m := fun m hm =>
    msgOwned_transfer hAs.1 hAp.1 (hg "heap_ptr") (hg "scratch_ptr")
      (fun t ht => (hfp t ht).2) hfix hch hfo htries hm
  have hIpost : EvmInvAt post S := evmInvAt_of_dispatch_transport hI hAs hAp hg hch
    ⟨hWT.1, hWT.2.1, hWT.2.2.1, Nd, hWT.2.2.2⟩ hwords.1 hwords.2.1 hwords.2.2
    (fun ec hec => ⟨hlogs ec hec,
      dispatch_store_logs_ok hInv hAp hg hklt hx hpost.2.2.2.2.2.2 ec hec⟩)
    hm hfix (fun t ht => (hfp t ht).2) htries hwr hjr hrefs
    (fun t ht => by simpa [hdr] using (hfp t ht).1 0 (by decide))
  refine ⟨⟨hAp, S, hIpost, ?_⟩, ⟨hAp, S, hIpost⟩, ?_, ?_, hch⟩
  · rw [hg "ev", hwords.1 _ hhead 112 (by decide) (by decide)]
    exact hm _ hmsg
  · rw [hg "heap_ptr"]
  · intro name _
    rw [hpost.2.2.2.2.2.1]

/-- Hoare rule for the actual dispatch stores, retaining caller-local facts
and the original step frame. -/
theorem hoare_store_dispatch_word_step_with (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off ∈ ([48, 56, 80] : List Nat)) (value : ExpHOL 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hword : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      D0Pre gw hp G ch s → L s.locals → ev s value = some v → ∃ w : BitVec 64, v = .val (.word w)) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) value)
      (Fall (fun s => D0Pre gw hp G ch s ∧ L s.locals)) := by
  apply Hoare.store_fall_of_none
  refine ⟨fun {F} s _ ⟨hD, hL⟩ _ hnone => ?_⟩
  rcases hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) value)
      with ⟨res, post⟩
  rw [hrun] at hnone
  dsimp only at hnone ⊢
  subst res
  have hP := hD.1.1
  have hInv := evmInv_of_evmMsgReady s hP
  obtain ⟨hb, _, ⟨ew, hew, hen⟩, _⟩ := R11Shards.evm_head_globals hInv
  have hofflt : off + 8 ≤ 280 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl <;> decide
  let x := BitVec.ofNat 64 (globN s "ev" + off)
  have hx : x.toNat = globN s "ev" + off := Nat.mod_eq_of_lt (by omega)
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word x)) := by
    simp only [evalHOLExact, evalListHOLExact, hew, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
    congr 3
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hen,
      show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show globN s "ev" + off < 2 ^ 64 by omega), hx]
  obtain ⟨w, hv, hpst⟩ := R11Shards.store_global_off_word hew hen (by omega)
    (fun v hv => hword s v hD hL hv) hrun
  have hdom : s.memaddrs x := by
    by_contra hn
    rw [evaluateHOLFiniteState_store, hdst, hv] at hrun
    simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hn] at hrun
  have hpost : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.baseAddr = s.baseAddr ∧ post.be = s.be ∧ post.globals = s.globals ∧
      ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a := by
    rw [hpst]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro a ha
    simp [R11Shards.updW, show a ≠ BitVec.ofNat 64 (globN s "ev" + off) from ha]
  have hs := evmMsgReady_store_dispatch hP hoff hx hdom hpost
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    exact List.mem_cons_self
  have hslot := (dispatch_store_chain_words hInv hoff hx hpost.2.2.2.2.2.2).1
    _ hhead 112 (by decide) (by decide)
  have hloc : post.locals = s.locals := by rw [hpst]
  refine ⟨d0Pre_of_stepFrom gw hp G ch hD
    (stepFrom_of_evmStep (fun g hg => by simp at hg) hD.1.2 hs.2) hloc
    (congrArg (fun gs => gs.lookup (ofString "ev")) hpost.2.2.2.2.2.1) hslot, ?_⟩
  rw [hloc]
  exact hL

/-- Local-word specialization of the dispatch store rule. -/
theorem hoare_store_dispatch_local_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (off : Nat) (hoff : off ∈ ([48, 56, 80] : List Nat)) (name : MlS) (w : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hL : ∀ locals, L locals → locals.lookup name = some (.val (.word w))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) (.var .local name))
      (Fall (fun s => D0Pre gw hp G ch s ∧ L s.locals)) := by
  apply hoare_store_dispatch_word_step_with gw hp G ch off hoff (.var .local name) L
  intro F s v _ hlocals hv
  simp only [ev, evalHOLExact, hL _ hlocals] at hv
  exact ⟨w, (Option.some.inj hv).symm⟩

/-- The final code pointer and code length stores retain the owned message. -/
theorem hoare_prepare_dispatch_code_stores (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (hc : ∀ locals, L locals → locals.lookup (ofString "code") = some (.val (.word code)))
    (hn : ∀ locals, L locals → locals.lookup (ofString "code_n") = some (.val (.word code_n))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ L s.locals)
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 48#64]) (.var .local (ofString "code")))
        (.store (.op .add [.var .global (ofString "ev"), .const 56#64]) (.var .local (ofString "code_n"))))
      (Fall (fun s => D0Pre gw hp G ch s ∧ L s.locals)) := by
  exact Hoare.seq_fall'
    (hoare_store_dispatch_local_step gw hp G ch 48 (by decide) _ code L hc)
    (hoare_store_dispatch_local_step gw hp G ch 56 (by decide) _ code_n L hn)
    (fun _ h => h)

/-- The four common message/code stores in dispatch, with the source's
right-associated sequence shape and the subsequent program left abstract. -/
theorem hoare_prepare_dispatch_common_stores (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (tail : ProgHOL 64) (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (hQ : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)) → Q s)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n))) tail (Fall Q)) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (.seq (.store (.op .add [.var .local (ofString "msg"), .const 112#64])
          (.var .local (ofString "code")))
        (.seq (.store (.op .add [.var .local (ofString "msg"), .const 120#64])
            (.var .local (ofString "code_n")))
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const 48#64])
              (.var .local (ofString "code")))
            (.seq (.store (.op .add [.var .global (ofString "ev"), .const 56#64])
                (.var .local (ofString "code_n"))) tail))))
      (Fall Q) := by
  let L : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun locals =>
    locals.lookup (ofString "code") = some (.val (.word code)) ∧
    locals.lookup (ofString "code_n") = some (.val (.word code_n))
  refine Hoare.seq_fall'
    (hoare_store_msg_local_step gw hp G ch 112 (by decide) _ code L (fun _ h => h.1))
    (Hoare.seq_fall'
      (hoare_store_msg_local_step gw hp G ch 120 (by decide) _ code_n L (fun _ h => h.2))
      (Hoare.seq_fall'
        (hoare_store_dispatch_local_step gw hp G ch 48 (by decide) _ code L (fun _ h => h.1))
        (Hoare.seq_fall'
          (hoare_store_dispatch_local_step gw hp G ch 56 (by decide) _ code_n L (fun _ h => h.2))
          htail hQ) hQ) hQ) hQ

/-- The final jumpdest store and return, for a word-valued local result. -/
theorem hoare_prepare_dispatch_jumpdest_finish (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (jd : BitVec 64) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "jd") = some (.val (.word jd)))
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
          (.var .local (ofString "jd"))) (.return (.const 0#64)))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.seq_fall'
    (hoare_store_dispatch_local_step gw hp G ch 80 (by decide) _ jd
      (fun locals => locals.lookup (ofString "jd") = some (.val (.word jd)))
      (fun _ h => h))
    (Hoare.mono (Hoare.return_const_fall ?_ 0#64) (fun _ h => h.1.1)) (fun _ h => h.1.1)
  intro F s locals k h
  exact ⟨localsFree_evmMsgReady s locals k h.1, localsFree_stepFrom gw hp G ch s locals k h.2⟩

/-- Fresh scratch allocation is below every existing frame record,
continuation and log header. Its writes preserve all of their words. -/
theorem fresh_scratch_chain_words {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (q n : Nat) (hq : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a) :
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 280 →
      memW post (ec.1 + j) = memW s (ec.1 + j)) ∧
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 104 →
      memW post (ec.2 + j) = memW s (ec.2 + j)) ∧
    (∀ ec ∈ evmChain s, ∀ j, j + 8 ≤ 24 →
      memW post (memW s (ec.1 + 88) + j) = memW s (memW s (ec.1 + 88) + j)) := by
  obtain ⟨_, S, hI⟩ := hInv
  have hpoint : ∀ a, a < 2 ^ 64 → globN s "scratch_ptr" ≤ a →
      memW post a = memW s a := by
    intro a ha hlo
    unfold memW
    rw [hmem (BitVec.ofNat 64 a) ?_]
    rw [show (BitVec.ofNat 64 a).toNat = a from Nat.mod_eq_of_lt ha]
    unfold CellHits
    dsimp only
    omega
  have hblock : ∀ ec ∈ evmChain s, ∀ i ∈
      [(ec.1, 280), (ec.2, 104), (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)),
        (memW s (ec.1 + 88), 24)], ∀ j, j + 8 ≤ i.2 →
      memW post (i.1 + j) = memW s (i.1 + j) := by
    intro ec hec i hi j hj
    have hin := ((hI.2.2.2.2.1 ec hec).1 i hi).1
    have hend : scratchEnd ≤ 2 ^ 64 := by decide
    unfold Inside at hin
    apply hpoint <;> omega
  exact ⟨fun ec hec j hj => hblock ec hec (ec.1, 280) (by simp) j hj,
    fun ec hec j hj => hblock ec hec (ec.2, 104) (by simp) j hj,
    fun ec hec j hj => hblock ec hec (memW s (ec.1 + 88), 24) (by simp) j hj⟩

/-- A fresh scratch write cannot alter the linked frame chain when its two
root globals are retained. -/
theorem fresh_scratch_chain_eq {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (q n : Nat) (hq : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (he : globN post "ev" = globN s "ev")
    (hc : globN post "cur_cont" = globN s "cur_cont") :
    evmChain post = evmChain s := by
  have hw := (fresh_scratch_chain_words hInv q n hq hmem).2.1
  have haux : ∀ fuel e c,
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel
    induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      have h0 : memW post c = memW s c := by
        simpa only [Nat.add_zero] using hw (e, c) hec 0 (by decide)
      simp only [evmChainFrom, hw (e, c) hec 16 (by decide), h0,
        hw (e, c) hec 8 (by decide)]
      split
      · rfl
      · rename_i hn
        rw [ih (memW s c) (memW s (c + 8))]
        intro ec hm
        apply hsub ec
        simp only [evmChainFrom, hn, ↓reduceIte, List.mem_cons]
        exact Or.inr hm
  unfold evmChain
  rw [he, hc]
  exact haux _ _ _ (fun _ h => h)

/-- Fresh scratch writes preserve words in every previously allocated block. -/
theorem fresh_scratch_allocated_words {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hA : ArenaOK s)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    {i : Ivl} (hi : Allocated s i) {k : Nat} (hk : k + 8 ≤ i.2) :
    memW post (i.1 + k) = memW s (i.1 + k) := by
  have hb := allocated_le_2pow64 hA hi
  unfold memW
  rw [hmem (BitVec.ofNat 64 (i.1 + k)) ?_]
  rw [show (BitVec.ofNat 64 (i.1 + k)).toNat = i.1 + k from Nat.mod_eq_of_lt (by omega)]
  unfold CellHits
  rcases hi with hi | hi
  · have hh := hA.2.1
    have hs := hA.2.2.1
    have hsep : heapLimit ≤ scratchStart := by decide
    unfold Inside at hi
    dsimp only at hi ⊢
    omega
  · unfold Inside at hi
    dsimp only at hi ⊢
    omega

/-- All live log-object intervals retain their original addresses and sizes
through fresh scratch writes. -/
theorem fresh_scratch_log_objects {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hvm : globN post "vm_system_address" = globN s "vm_system_address") :
    ∀ ec ∈ evmChain s, frameLogObjects post ec = frameLogObjects s ec := by
  have hw := fresh_scratch_chain_words hInv q n hhi hmem
  obtain ⟨hAs, S, hI⟩ := hInv
  have heq := fun {i : Ivl} (hi : Allocated s i) {k : Nat} (hk : k + 8 ≤ i.2) =>
    fresh_scratch_allocated_words hAs.2 q n hlo hhi hmem hi hk
  intro ec hec
  have hfw := hI.2.2.2.2.1 ec hec
  have hh := hw.2.2 ec hec
  unfold frameLogObjects
  dsimp only
  rw [hw.1 ec hec 88 (by decide), hh 8 (by decide),
    show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hh 0 (by decide)]
  apply List.flatMap_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  have hle := hfw.2.2.2.2.2.2.2.2.2.2.2.1
  have hal : Allocated s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hslot := heq hal (k := 8 * i) (by dsimp [frameLogs]; omega)
  change memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
    memW s (memW s (memW s (ec.1 + 88)) + 8 * i) at hslot
  rw [hslot]
  have hll := hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rcases hll with hz | ⟨_, _, _, _, hentries⟩
  · have hs := (hfw.1 (memW s (ec.1 + 88), 24) (by simp)).1
    have h1 := hAs.2.2.2.1
    have h2 := hAs.2.2.2.2.1
    have hpos : 0 < scratchStart := by decide
    unfold Inside at hs
    dsimp only at hs
    omega
  · have hlog : Allocated s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) :=
      Or.inl (hentries i hi').2.2.1
    unfold logOwnedIvls logRecordIvls
    have h0 := heq hlog (k := 0) (by omega)
    simp only [Nat.add_zero] at h0
    simp only [hvm, h0, heq hlog (k := 8) (by omega),
      heq hlog (k := 16) (by omega), heq hlog (k := 24) (by omega),
      heq hlog (k := 32) (by omega)]

/-- Fresh scratch writes preserve each live log list, including allocation
when the scratch frontier is lowered. -/
theorem fresh_scratch_logs_ok {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hdom : post.memaddrs = s.memaddrs)
    (hhp : globN post "heap_ptr" = globN s "heap_ptr")
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    ∀ ec ∈ evmChain s, LogsListOK post (memW s (ec.1 + 88)) := by
  have hw := (fresh_scratch_chain_words hInv q n hhi hmem).2.2
  obtain ⟨hAs, S, hI⟩ := hInv
  have heq := fun {i : Ivl} (hi : Allocated s i) {k : Nat} (hk : k + 8 ≤ i.2) =>
    fresh_scratch_allocated_words hAs.2 q n hlo hhi hmem hi hk
  intro ec hec
  have hfw := hI.2.2.2.2.1 ec hec
  have hh := hw ec hec
  have h0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
    simpa only [Nat.add_zero] using hh 0 (by decide)
  rcases hfw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw24, ha24, hb, hc, he⟩
  · exact Or.inl hz
  refine Or.inr ⟨(wordsOK_congr_of_dom hdom).2 hw24,
    allocated_mono (by omega) hsp ha24, ?_, ?_, ?_⟩
  · rw [hh 8 (by decide)]; exact hb
  · rw [hh 8 (by decide), hh 16 (by decide)]; exact hc
  · intro i hi
    rw [hh 8 (by decide)] at hi
    rw [h0]
    have hback : Allocated s (frameLogs s ec) := hfw.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hs := heq hback (k := 8 * i) (by dsimp [frameLogs]; omega)
    change memW post (memW s (memW s (ec.1 + 88)) + 8 * i) =
      memW s (memW s (memW s (ec.1 + 88)) + 8 * i) at hs
    rw [hs]
    obtain ⟨hwptr, hw40, hin40, hn4, hn32, hin20, hintop, hindat⟩ := he i hi
    have hal : Allocated s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) := Or.inl hin40
    have hz := heq hal (k := 0) (by omega)
    simp only [Nat.add_zero] at hz
    refine ⟨?_, (wordsOK_congr_of_dom hdom).2 hw40, ?_⟩
    · obtain ⟨_, hptrdom, _⟩ := hwptr
      rcases hm : post.memory (BitVec.ofNat 64 (memW s (memW s (ec.1 + 88)) + 8 * i)) with ⟨w⟩
      exact ⟨w, by rw [hdom]; exact hptrdom, hm⟩
    · rw [hz, heq hal (k := 8) (by omega), heq hal (k := 16) (by omega),
        heq hal (k := 24) (by omega), heq hal (k := 32) (by omega), hhp]
      exact ⟨hin40, hn4, hn32, hin20, hintop, hindat⟩

/-- The frame shape survives fresh scratch writes and a decreasing scratch
frontier once its owned message has been transported. -/
theorem frameWF_of_fresh_scratch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hInv : EvmInv s)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name)
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr")
    (hdom : post.memaddrs = s.memaddrs)
    {ec : Ivl} (hec : ec ∈ evmChain s) (hfw : FrameWF s S ec)
    (hmsg : MsgOwned post S (memW s (ec.1 + 112))) :
    FrameWF post S ec := by
  have hw := fresh_scratch_chain_words hInv q n hhi hmem
  have hk := hw.1 ec hec
  have hh := hw.2.2 ec hec
  have hlogs := fresh_scratch_logs_ok hInv q n hlo hhi hmem hdom (hg _ (by decide)) hsp ec hec
  have hfl : frameLogs post ec = frameLogs s ec := by
    unfold frameLogs
    rw [hk 88 (by decide)]
    rw [show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by
      simpa only [Nat.add_zero] using hh 0 (by decide), hh 16 (by decide)]
  have hfr : frameRet post ec = frameRet s ec := by
    unfold frameRet
    rw [hk 216 (by decide), hk 144 (by decide)]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
    c14, c15, _, _⟩ := hfw
  unfold FrameWF
  dsimp only
  rw [hk 8 (by decide), hk 232 (by decide), hk 88 (by decide), hk 24 (by decide),
    hk 40 (by decide), hk 16 (by decide), hk 32 (by decide), hk 136 (by decide),
    hk 168 (by decide), hk 176 (by decide), hh 16 (by decide), hh 8 (by decide), hfl,
    hk 216 (by decide), hk 144 (by decide), hfr, hk 112 (by decide),
    hg "frame_mem_ptr" (by decide), hg "heap_ptr" (by decide), hg "evm_empty" (by decide)]
  refine ⟨?_, c2, (wordsOK_congr_of_dom hdom).2 c3, c4, c5, c6, c7,
    c8, c9, c10, c11, c12, ?_, (wordsOK_congr_of_dom hdom).2 c14, ?_, hlogs, hmsg⟩
  · intro i hi
    obtain ⟨hin, hw⟩ := c1 i hi
    refine ⟨?_, (wordsOK_congr_of_dom hdom).2 hw⟩
    unfold Inside at hin ⊢
    exact ⟨le_trans hsp hin.1, hin.2⟩
  · rcases c13 with hh | hs
    · exact Or.inl hh
    · exact Or.inr ⟨le_trans hsp hs.1, hs.2⟩
  · rcases c15 with hz | ⟨hin, hw⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hin, (wordsOK_congr_of_dom hdom).2 hw⟩

/-- Aligned cells intersecting an allocated interval cannot intersect the
fresh scratch interval. -/
theorem fresh_scratch_allocated_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hA : ArenaOK s)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    {i : Ivl} (hi : Allocated s i) :
    R10Shards.GbodyProcessMsg.IvlUnhit s post i := by
  right
  intro a ha hh
  apply hmem a
  have hsep : heapLimit ≤ scratchStart := by decide
  have hhp := hA.2.1
  have hfm := hA.2.2.1
  have hsp8 := hA.2.2.2.2.2.2.2.1
  have hfm8 := hA.2.2.2.2.2.2.1
  have hlow8 : a.toNat + 8 ≤ globN s "frame_mem_ptr" ∨ globN s "scratch_ptr" ≤ a.toNat := by
    rcases hi with hi | hi <;> unfold Inside at hi <;> unfold CellHits at hh
    · left
      have hfmpos : 0 < globN s "frame_mem_ptr" := by
        have hs : 0 < scratchStart := by decide
        omega
      omega
    · right
      omega
  unfold CellHits
  dsimp only
  rcases hlow8 with h | h <;> omega

/-- Fresh scratch writes preserve both words and bytes used by world typing. -/
theorem fresh_scratch_sameTypedCells {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a) :
    EvmBase.SameTypedCells s post S Nd := by
  refine ⟨hbe, hdom, hAs.1.memaddrs, hout, ?_, ?_⟩
  · intro a ha ⟨i, hi, ha1, ha2⟩
    have hal : Allocated s i := by
      rcases worldTypedIvls_allocated hWT hi with hz | hal
      · omega
      · exact hal
    have hu := fresh_scratch_allocated_unhit hAs.2 q n hlo hhi hmem hal
    rcases hu with hz | hu
    · omega
    · apply hmem
      have hh : ¬ CellHits a (q, n) := by
        have hsep : heapLimit ≤ scratchStart := by decide
        have hhp := hAs.2.2.1
        have hfm := hAs.2.2.2.1
        rcases hal with hal | hal <;> unfold Inside at hal <;> unfold CellHits <;> dsimp only at hal ⊢ <;> omega
      rwa [show (BitVec.ofNat 64 a).toNat = a from Nat.mod_eq_of_lt ha]
  · intro b hb ⟨i, hi, hb1, hb2⟩
    have hal : Allocated s i := by
      rcases worldTypedIvls_allocated hWT hi with hz | hal
      · omega
      · exact hal
    exact R10Shards.GbodyProcessMsg.memB_eq_of_ivlUnhit
      (fresh_scratch_allocated_unhit hAs.2 q n hlo hhi hmem hal) hbe
      (allocated_le_2pow64 hAs.2 hal) ⟨hb1, hb2⟩

/-- World typing, fixed objects, trie extents and role slots are retained
through fresh scratch writes with a lowered frontier. -/
theorem fresh_scratch_world_transport {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hWT : WorldTypedWith s S Nd)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name)
    (hglob : ∀ name, ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    WorldTypedWith post S Nd ∧ fixedObjects post = fixedObjects s ∧
      nodeExtents post Nd = nodeExtents s Nd ∧
      worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s ∧
      (∀ t ∈ S, htabFootprint post t = htabFootprint s t) := by
  have hc := fresh_scratch_sameTypedCells hAs hWT q n hlo hhi hmem hbe hdom hout
  have hfix : fixedObjects post = fixedObjects s := by
    have hgb : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
        (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
      apply List.map_congr_left
      intro gn hgn
      have hn : ofString gn.1 ≠ ofString "scratch_ptr" := by
        have hm : ofString gn.1 ∈ (globalBuffers.map Prod.fst).map ofString :=
          List.mem_map.2 ⟨gn.1, List.mem_map.2 ⟨gn, hgn, rfl⟩, rfl⟩
        intro he; rw [he] at hm
        exact (by decide : ofString "scratch_ptr" ∉ (globalBuffers.map Prod.fst).map ofString) hm
      rw [hg gn.1 hn]
    unfold fixedObjects
    rw [hgb, blockOutObjects_eq hAs.2 hWT.2.2.1 hc (hg "bo" (by decide)),
      balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hc (hg "bal_accounts" (by decide)),
      hg "journal" (by decide), hg "journal_cap" (by decide)]
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hg _ (by decide)]
  have hFT := fixedTyped_of_eq hAp hWT.2.2.1 hhp hsp hfix
  have hcg : ∀ name ∈ coreWorldGlobals, globN post name = globN s name := by
    intro name hn
    apply hg
    intro heq
    have hm := List.mem_map.2 ⟨name, hn, heq⟩
    exact (by decide : ofString "scratch_ptr" ∉ coreWorldGlobals.map ofString) hm
  have hW := (worldTypedWith_congr_w1 hAs hAp hhp hsp hcg hc hWT
    ⟨hFT, fun o ho => Or.inl (by rw [← hfix]; exact ho)⟩).1
  exact ⟨hW, hfix, nodeExtents_eq hWT.2.2.2.1 hc,
    worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hc hcg,
    journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hc hcg,
    fun t ht => htabFootprint_eq hc ht (hWT.1.2.1 t ht).1⟩

/-- Every previously owned message remains owned through fresh scratch
writes, including messages of suspended ancestors. -/
theorem fresh_scratch_msgOwned {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hI : EvmInvAt s S) (hWT : WorldTypedWith s S Nd)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name)
    (hglob : ∀ name, ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    ∀ m, MsgOwned s S m → MsgOwned post S m := by
  have hInv : EvmInv s := ⟨hAs, S, hI⟩
  have hw := fresh_scratch_chain_words hInv q n hhi hmem
  have hch := fresh_scratch_chain_eq hInv q n hhi hmem (hg _ (by decide)) (hg _ (by decide))
  have hl := fresh_scratch_log_objects hInv q n hlo hhi hmem (hg _ (by decide))
  have hfo : ∀ ec ∈ evmChain s, frameObjects post ec = frameObjects s ec := by
    intro ec hec
    exact (frameObjects_eq_of_dispatch_slots ec
      (fun k hk _ => hw.1 ec hec k hk) (hw.2.2 ec hec) (hl ec hec)).1
  have hc := fresh_scratch_sameTypedCells hAs hWT q n hlo hhi hmem hbe hdom hout
  have ht := fresh_scratch_world_transport hAs hAp hWT q n hlo hhi hmem hbe hdom hout hg hglob hsp
  intro m hm
  exact msgOwned_congr hAs.2 hWT.1 hWT.2.2.2 hc (by rw [hg _ (by decide)]) hsp
    (hg _ (by decide)) hWT.2.2.1 ht.1.2.2.1 ht.2.1 ht.1.1 hch hfo hm

/-- Typed-cell preservation fixes every world-side reference, independently
of changes to the scratch allocator frontier. -/
theorem worldTableRefs_eq_of_typedCells {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaOK s) (hWT : WorldTypedWith s S Nd)
    (hc : EvmBase.SameTypedCells s post S Nd)
    (hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name) :
    worldTableRefs post S = worldTableRefs s S := by
  have hrec : ∀ name sz, (name, sz) ∈ typedRecords → ∀ k, k + 8 ≤ sz →
      globN s name ≠ 0 → memW post (globN s name + k) = memW s (globN s name + k) := by
    intro name sz hr k hk hn
    exact memW_typedRec_eq hAs hWT.2.2.1 hc hr hn hk
  have hslots : ∀ name ks sz, (name, sz) ∈ typedRecords →
      ofString name ≠ ofString "scratch_ptr" → (∀ k ∈ ks, k + 8 ≤ sz) →
      recordSlots post name ks = recordSlots s name ks := by
    intro name ks sz hr hn hk
    unfold recordSlots
    rw [hg name hn]
    split
    · rfl
    · rename_i hnz
      exact List.map_congr_left (fun k h => hrec name sz hr k (hk k h) hnz)
  have hn : ∀ name sz, (name, sz) ∈ typedRecords → ofString name ≠ ofString "scratch_ptr" → 40 ≤ sz →
      (if globN post name ≠ 0 ∧ memW post (globN post name + 32) ∈ S then
        htabValues post (memW post (globN post name + 32)) else []) =
      (if globN s name ≠ 0 ∧ memW s (globN s name + 32) ∈ S then
        htabValues s (memW s (globN s name + 32)) else []) := by
    intro name sz hr hne hsz
    rw [hg name hne]
    by_cases hz : globN s name = 0
    · simp [hz]
    · rw [hrec name sz hr 32 (by omega) hz]
      by_cases hm : memW s (globN s name + 32) ∈ S
      · simp [hz, hm, htabValues_eq hc hm (hWT.1.2.1 _ hm).1]
      · simp [hz, hm]
  have hw := hslots "ws" wsTableSlots 40 (by decide) (by decide) (by
    intro k hk; simp [wsTableSlots] at hk; rcases hk with rfl | rfl <;> decide)
  have hb := hslots "bs" bsTableSlots 80 (by decide) (by decide) (by
    intro k hk; simp [bsTableSlots] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have ht := hslots "ts" tsTableSlots 72 (by decide) (by decide) (by
    intro k hk; simp [tsTableSlots] at hk
    omega)
  have hbal : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
      (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
    apply List.flatMap_congr
    intro ad had
    have hm := balRecord_ivl_mem had
    rcases fixedObject_le_2pow64 hAs hWT.2.2.1 (bal_in_fixedObjects hm) with hz | hbound
    · dsimp only at hz; omega
    · dsimp only at hbound
      have hi := mem_worldTypedIvls_bal (S := S) (Nd := Nd) hm
      rw [memW_eq_of_cellHits hc (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩,
        memW_eq_of_cellHits hc (by omega) hi ⟨by dsimp only; omega, by dsimp only; omega⟩]
  have hj : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
      (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
    apply List.map_congr_left
    intro k hk
    have hk := List.mem_range.1 hk
    have hnz : globN s "journal_cap" ≠ 0 := by have := hWT.2.1.1; omega
    rcases hWT.2.1.2.2.1 with hz | ⟨hal, _⟩
    · exact absurd hz hnz
    · have hb := allocated_le_2pow64 hAs hal
      dsimp only at hb
      have hlen := hWT.2.1.1
      have hi := mem_worldTypedIvls_journal (s := s) (S := S) (Nd := Nd)
      simp only [hnz, ↓reduceIte] at hi
      exact memW_eq_of_cellHits hc (by omega) hi
        ⟨by dsimp only; omega, by dsimp only; omega⟩
  unfold worldTableRefs
  dsimp only
  rw [hw, hb, ht, hn "bs" 80 (by decide) (by decide) (by decide),
    hn "ts" 72 (by decide) (by decide) (by decide),
    show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
      simp only [globalTableRoots, List.map, hg "bal_accounts" (by decide),
        hg "bal_idx_accts" (by decide), hg "bal_idx_stor" (by decide)],
    balRecords_eq hWT.1 hc (hg _ (by decide)), hg "journal_n" (by decide), hg "journal" (by decide),
    hbal, hj]

/-- Full invariant transport through fresh scratch writes and a lowered
scratch frontier. -/
theorem evmInvAt_of_fresh_scratch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hI : EvmInvAt s S)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name)
    (hglob : ∀ name, ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name))
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    EvmInvAt post S := by
  have hInv : EvmInv s := ⟨hAs, S, hI⟩
  obtain ⟨Nd, htr⟩ := hI.1.2.2.2
  have hWT : WorldTypedWith s S Nd := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, htr⟩
  have ht := fresh_scratch_world_transport hAs hAp hWT q n hlo hhi hmem hbe hdom hout hg hglob hsp
  have hc := fresh_scratch_sameTypedCells hAs hWT q n hlo hhi hmem hbe hdom hout
  have hm := fresh_scratch_msgOwned hAs hAp hI hWT q n hlo hhi hmem hbe hdom hout hg hglob hsp
  have hw := fresh_scratch_chain_words hInv q n hhi hmem
  have htries : ∀ Ns, TriesTypedWith s S Ns →
      TriesTypedWith post S Ns ∧ nodeExtents post Ns = nodeExtents s Ns := by
    intro Ns hs
    have hW : WorldTypedWith s S Ns := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, hs⟩
    have ht' := fresh_scratch_world_transport hAs hAp hW q n hlo hhi hmem hbe hdom hout hg hglob hsp
    exact ⟨ht'.1.2.2.2, ht'.2.2.1⟩
  apply evmInvAt_of_frame_transport hI hAs hAp
    (fun ec hec => frameWF_of_fresh_scratch hInv q n hlo hhi hmem hg hsp hdom hec
      (hI.2.2.2.2.1 ec hec) (hm _ (hI.2.2.2.2.1 ec hec).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2))
    (fresh_scratch_chain_eq hInv q n hhi hmem (hg _ (by decide)) (hg _ (by decide)))
    ⟨ht.1.1, ht.1.2.1, ht.1.2.2.1, Nd, ht.1.2.2.2⟩
    (fun ec hec k hk _ => hw.1 ec hec k hk) hw.2.1 hw.2.2
    (fun ec hec => ⟨fresh_scratch_log_objects hInv q n hlo hhi hmem (hg _ (by decide)) ec hec,
      fresh_scratch_logs_ok hInv q n hlo hhi hmem hdom (hg _ (by decide)) hsp ec hec⟩)
    hm ht.2.1 ht.2.2.2.2.2 htries ht.2.2.2.1 ht.2.2.2.2.1
    (worldTableRefs_eq_of_typedCells hAs.2 hWT hc hg)
  intro t htS
  have he := htab_hdr_eq hc htS
    ((hWT.1.2.1 t htS).1.1 (t, 88) (by simp [htabFootprint])).1 0 (by decide)
  simpa [hdr] using he

/-- Fresh scratch effects give an EVM step with only `scratch_ptr` writable. -/
theorem evmMsgReady_fresh_scratch {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hP : EvmMsgReady s)
    (hAp : ArenaReady post)
    (q n : Nat) (hlo : globN s "frame_mem_ptr" ≤ q)
    (hhi : q + n ≤ globN s "scratch_ptr")
    (hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q, n) → post.memory a = s.memory a)
    (hbe : post.be = s.be) (hdom : post.memaddrs = s.memaddrs)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a → post.memory a = s.memory a)
    (hglob : ∀ name : MlS, name ∉ (["scratch_ptr"] : List String).map ofString →
      post.globals.lookup name = s.globals.lookup name)
    (hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr") :
    EvmMsgReady post ∧ EvmStep ["scratch_ptr"] s post := by
  have hgl : ∀ name, ofString name ≠ ofString "scratch_ptr" →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name) := by
    intro name hn
    exact (hglob (ofString name) (by simpa using hn)).symm
  have hg : ∀ name, ofString name ≠ ofString "scratch_ptr" → globN post name = globN s name := by
    intro name hn
    exact (globN_eq_of_lookup_eq (hgl name hn)).symm
  have hInv := evmInv_of_evmMsgReady s hP
  have hch := fresh_scratch_chain_eq hInv q n hhi hmem (hg _ (by decide)) (hg _ (by decide))
  obtain ⟨hAs, S, hI, hm⟩ := hP
  have hi := evmInvAt_of_fresh_scratch hAs hAp hI q n hlo hhi hmem hbe hdom hout hg hgl hsp
  obtain ⟨Nd, ht⟩ := hI.1.2.2.2
  have hWT : WorldTypedWith s S Nd := ⟨hI.1.1, hI.1.2.1, hI.1.2.2.1, ht⟩
  have hm' := fresh_scratch_msgOwned hAs hAp hI hWT q n hlo hhi hmem hbe hdom hout hg hgl hsp _ hm
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hslot := (fresh_scratch_chain_words hInv q n hhi hmem).1 _ hhead 112 (by decide)
  refine ⟨⟨hAp, S, hi, ?_⟩, ⟨hAp, S, hi⟩, ?_, ?_, hch⟩
  · rw [hg "ev" (by decide), hslot]
    exact hm'
  · rw [hg "heap_ptr" (by decide)]
  · intro name hn
    exact (hglob name hn).symm

/-- Word stores cannot alter cells outside their checked memory domain. -/
theorem scratch_panMemStores_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (ws : List (HolWordLab 64)) (x : BitVec 64) (mem mem' : BitVec 64 → HolWordLab 64),
      @panMemStoresHOL 64 _ x ws dom dec mem = some mem' →
      ∀ a : BitVec 64, ¬ dom a → mem' a = mem a
  | [], _, mem, mem', hst, a, _ => by
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    rw [← hst]
  | w :: ws, x, mem, mem', hst, a, ha => by
    unfold panMemStoresHOL panMemStoreHOL at hst
    split_ifs at hst with hdom
    have hax : a ≠ x := fun he => ha (he ▸ hdom)
    exact (scratch_panMemStores_out_dom ws (x + panBytesInWord 64)
      (fun current => if current = x then w else mem current) mem' hst a ha).trans (if_neg hax)

/-- Byte stores retain even unaligned cells outside the checked domain. -/
theorem scratch_panMemStoreByte_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {b : BitVec 8}
    (hst : @panMemStoreByteWord8HOL 64 _ mem dom dec be addr b = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStoreByteWord8HOL at hst
  dsimp only at hst
  cases hm : mem (panByteAlignHOL (width := 64) addr) with
  | word cell =>
    rw [hm] at hst
    dsimp only at hst
    split at hst
    · rename_i hdom
      simp only [Option.some.injEq] at hst
      subst hst
      exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr => ha (heq.symm ▸ hdom))
    · cases hst

theorem scratch_panMemStore32_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom}
    {mem mem' : BitVec 64 → HolWordLab 64} {be : Bool} {addr : BitVec 64} {val : BitVec 32}
    (hst : @panMemStore32HOL 64 _ mem dom dec be addr val = some mem')
    {a : BitVec 64} (ha : ¬ dom a) : mem' a = mem a := by
  unfold panMemStore32HOL at hst
  split at hst
  · dsimp only at hst
    cases hm : mem (panByteAlignHOL (width := 64) addr) with
    | word cell =>
      rw [hm] at hst
      dsimp only at hst
      split at hst
      · rename_i hdom
        simp only [Option.some.injEq] at hst
        subst hst
        exact if_neg (fun heq : a = panByteAlignHOL (width := 64) addr => ha (heq.symm ▸ hdom))
      · cases hst
  · cases hst

theorem scratch_panWriteBytearray_out_dom {dom : BitVec 64 → Prop} {dec : DecidablePred dom} :
    ∀ (bs : List (BitVec 8)) (addr : BitVec 64) (mem : BitVec 64 → HolWordLab 64) (be : Bool)
      {a : BitVec 64}, ¬ dom a →
      @panWriteBytearrayWord8HOL 64 _ addr bs mem dom dec be a = mem a
  | [], _, _, _, _, _ => rfl
  | b :: bs, addr, mem, be, a, ha => by
    unfold panWriteBytearrayWord8HOL
    cases hst : @panMemStoreByteWord8HOL 64 _
        (@panWriteBytearrayWord8HOL 64 _ (addr + 1) bs mem dom dec be) dom dec be addr b with
    | none => rfl
    | some updated =>
      exact (scratch_panMemStoreByte_out_dom hst ha).trans
        (scratch_panWriteBytearray_out_dom bs (addr + 1) mem be ha)

/-- Runtime jump-destination computation preserves readiness and the chain,
given its out-of-domain cell frame. -/
theorem compute_jumpdests_evm_run_with_out_dom {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : EvmMsgReady s) (nw p f : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hnb : nw.toNat < 2 ^ 40)
    (hout : ∀ a : BitVec 64, ¬ ordinaryDomain a →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_jumpdests)).2.memory a = s.memory a) :
    InitECandidate.Solver.Wave8M19.Htab.Ret s
      (sourceFnBody Guest.Software.guestFn_compute_jumpdests) (fun v post =>
      ∃ q : BitVec 64, v = .val (.word q) ∧
        EvmMsgReady post ∧ EvmStep ["scratch_ptr"] s post) := by
  have hAs := hP.1
  have hpn : globN s "scratch_ptr" = p.toNat := by simp [globN, hp]
  have hfn : globN s "frame_mem_ptr" = f.toNat := by simp [globN, hf]
  have hfp : f.toNat ≤ p.toNat := by
    rw [← hpn, ← hfn]; exact hAs.2.2.2.2.1
  intro v hv
  obtain ⟨q, hval, hq, _, hlo, hhi, hg, _, hd, hm⟩ :=
    compute_jumpdests_run s hAs.1.code hAs.1 nw p f hn hp hf hfp hnb v hv
  let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_compute_jumpdests)).2
  have hlow : globN s "frame_mem_ptr" ≤ q.toNat := by rw [hfn]; omega
  have hhigh : q.toNat + (jdLen nw).toNat ≤ globN s "scratch_ptr" := by rwa [hpn]
  have hq8 : q.toNat % 8 = 0 := by
    rw [hq, and_neg8_toNat]
    omega
  have hApost : ArenaReady post := hb_arenaReady_update_scratch_ptr
    (guestInv_evaluate s _ hAs.1) hAs.2 hg hlow
    (by have := hAs.2.2.2.2.2.1; omega) hq8
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
    have he : globN post "scratch_ptr" = q.toNat := by
      unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    omega
  have hglob : ∀ name : MlS, name ∉ (["scratch_ptr"] : List String).map ofString →
      post.globals.lookup name = s.globals.lookup name := by
    intro name hn
    rw [hg]
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
  obtain ⟨hr, hs⟩ := evmMsgReady_fresh_scratch hP hApost q.toNat (jdLen nw).toNat
    hlow hhigh hm (InitECandidate.Solver.Wave8GuestInv.R16Shards.evaluate_be_eq s _) hd hout hglob hsp
  exact ⟨q, hval, hr, hs⟩

/-- Shared-memory operations leave ordinary memory unchanged. -/
theorem scratch_shMemStore_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (address value : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemStore operator address value)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · unfold shMemStoreHOLExact
    split <;> split
    all_goals simp [ofExact, toExact]
    all_goals split <;> simp
  · rfl

theorem scratch_shMemLoad_mem_eq {F : Type} (state : PanSemStateFiniteExact 64 F) (operator : OpSize)
    (kind : VarKind) (name : MlS) (address : ExpHOL 64) :
    (evaluateHOLFiniteState state (.shMemLoad operator kind name address)).2.memory = state.memory := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      dsimp only
      cases kind <;> split <;> split <;> (try split) <;>
        simp [emptyLocalsHOLFinite, setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite]
    · rfl
  · rfl

/-- Out-of-domain preservation across a function call and its exception handler. -/
theorem scratch_call_out_dom_aux {F : Type}
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (function : MlS) (arguments : List (ExpHOL 64)) (state : PanSemStateFiniteExact 64 F)
    {a : BitVec 64} (ha : ¬ state.memaddrs a)
    (ihBody : ∀ values body callee rs,
      lookupCodeHOLFinite state.code.lookup function values = some (body, callee, rs) →
      state.clock ≠ 0 →
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a)
    (ihHandler : ∀ dest hid hv hp, info = some (dest, some (hid, hv, hp)) →
      ∀ (t : PanSemStateFiniteExact 64 F),
        t.clock < state.clock → ¬ t.memaddrs a →
        (evaluateHOLFiniteState t hp).2.memory a = t.memory a) :
    (evaluateHOLFiniteState state (.call info function arguments)).2.memory a = state.memory a := by
  rw [evaluateHOLFiniteState_call]
  split
  · rfl
  · rename_i values _
    split
    · rfl
    · rename_i body callee rs found
      split
      · rfl
      · rename_i nonzero
        have ih := ihBody values body callee rs found nonzero
        have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite state callee) body
        have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
        obtain ⟨r, st⟩ := out
        dsimp only at ih meta' cl ⊢
        change st.clock ≤ state.clock - 1 at cl
        have stc : st.clock < state.clock := by omega
        have st_ha : ¬ st.memaddrs a := by
          have hm : st.memaddrs = state.memaddrs := meta'.2.1
          rw [hm]; exact ha
        rcases info with _ | ⟨dest, handler⟩
        · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
            simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
        · rcases handler with _ | ⟨hid, hv, hp⟩
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih]
          · rcases dest with _ | ⟨⟨⟩, nm⟩ <;>
              rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              first
                | (exact (ihHandler _ hid hv hp rfl _ (by exact stc) (by exact st_ha)).trans ih)
                | (simp [setKvarHOLFinite, setVarHOLFinite, setGlobalHOLFinite, emptyLocalsHOLFinite, ih])

/-- Evaluation preserves every memory cell outside the initial memory domain,
including on errors, timeouts and exceptions. -/
theorem scratch_evaluate_mem_out_dom {F : Type}
    (state : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    {a : BitVec 64} (ha : ¬ state.memaddrs a) :
    (evaluateHOLFiniteState state program).2.memory a = state.memory a := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact scratch_evaluate_mem_out_dom _ body ha
      · rfl
  | decCall name kind function arguments continuation =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have ih : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory a = state.memory a :=
            scratch_evaluate_mem_out_dom (callEntryStateHOLFinite state callee) body ha
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at ih meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have st_ha : ¬ st.memaddrs a := by
            have hm : st.memaddrs = state.memaddrs := meta'.2.1
            rw [hm]; exact ha
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [emptyLocalsHOLFinite])
          all_goals (try exact ih)
          split
          · have small : st.clock < state.clock := by omega
            exact (scratch_evaluate_mem_out_dom
              (setVarHOLFinite name v { st with locals := state.locals })
              continuation st_ha).trans ih
          · exact ih
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · rfl
    · split
      · cases kind <;> rfl
      · rfl
  | seq first second =>
    have memory := scratch_evaluate_mem_out_dom state first ha
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining meta'
      dsimp only at memory remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
        exact (scratch_evaluate_mem_out_dom middle second m_ha).trans memory
      | some _ => exact memory
  | ite condition yes no =>
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact scratch_evaluate_mem_out_dom state no ha
      · exact scratch_evaluate_mem_out_dom state yes ha
    · rfl
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := scratch_evaluate_mem_out_dom (decClockHOLFinite state) body ha
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining meta'
            dsimp only at memory remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have m_ha : ¬ middle.memaddrs a := by rw [meta'.2.1]; exact ha
            cases result with
            | none => exact (scratch_evaluate_mem_out_dom middle (.while condition body) m_ha).trans memory
            | some result =>
              cases result with
              | «continue» =>
                exact (scratch_evaluate_mem_out_dom middle (.while condition body) m_ha).trans memory
              | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot _ _ => rw [evaluateHOLFiniteState_annot]
  | tick =>
    rw [evaluateHOLFiniteState_tick]
    split <;> rfl
  | raise _ value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rename_i mem' hst
          exact scratch_panMemStores_out_dom _ _ _ _ hst a ha
        · rfl
      · rfl
    · rfl
  | store32 destination value =>
    rw [evaluateHOLFiniteState_store32]
    split
    · split
      · split
        · rename_i mem' hst
          exact scratch_panMemStore32_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rename_i mem' hst
          exact scratch_panMemStoreByte_out_dom hst ha
        · rfl
      · rfl
    · rfl
  | extCall _ _ _ _ _ =>
    rw [evaluateHOLFiniteState_extCall_source]
    split
    · split
      · split
        · rfl
        · dsimp only [ofExact, toExact]
          exact scratch_panWriteBytearray_out_dom _ _ _ _ ha
      · rfl
    · rfl
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl
  | shMemStore op addr val =>
    exact congrFun (scratch_shMemStore_mem_eq state op addr val) a
  | shMemLoad op kind name addr =>
    exact congrFun (scratch_shMemLoad_mem_eq state op kind name addr) a
  | call info function arguments =>
    refine scratch_call_out_dom_aux info function arguments state ha
      (fun values body callee rs _ _ =>
        scratch_evaluate_mem_out_dom (callEntryStateHOLFinite state callee) body ha)
      (fun _ _ _ hp _ t _ tha => scratch_evaluate_mem_out_dom t hp tha)
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | (simp only [callEntryStateHOLFinite] at small; exact Or.inl small)
      | omega
      | (by_cases hc : state.clock = 0
         · right; refine ⟨by omega, ?_⟩; simp +arith
         · left; omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)

/-- Jump-destination computation needs no additional memory-frame assumption. -/
theorem compute_jumpdests_evm_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : EvmMsgReady s) (nw p f : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hnb : nw.toNat < 2 ^ 40) :
    InitECandidate.Solver.Wave8M19.Htab.Ret s
      (sourceFnBody Guest.Software.guestFn_compute_jumpdests) (fun v post =>
      ∃ q : BitVec 64, v = .val (.word q) ∧
        EvmMsgReady post ∧ EvmStep ["scratch_ptr"] s post) := by
  apply compute_jumpdests_evm_run_with_out_dom s hP nw p f hn hp hf hnb
  intro a ha
  apply scratch_evaluate_mem_out_dom
  rwa [hP.1.1.memaddrs]

/-- The jumpdest callee exposes a word result and the exact scratch-only step. -/
theorem compute_jumpdests_spec :
    FunSpec (fun s => EvmMsgReady s ∧ ∃ nw : BitVec 64,
      s.locals.lookup (ofString "n") = some (.val (.word nw)) ∧ nw.toNat < 2 ^ 40)
      (fun s r post => ∀ v, r = some (.returned v) →
        (∃ q : BitVec 64, v = .val (.word q)) ∧ EvmMsgReady post ∧
          EvmStep ["scratch_ptr"] s post) (ofString "compute_jumpdests") := by
  refine ⟨_, _, _, lookup_compute_jumpdests, fun s _ hP _ _ v hr => ?_⟩
  obtain ⟨hP, nw, hn, hnb⟩ := hP
  obtain ⟨p, hp⟩ := hP.1.2.2.2.2.2.2.2.2.2 "scratch_ptr" (by decide)
  obtain ⟨f, hf⟩ := hP.1.2.2.2.2.2.2.2.2.2 "frame_mem_ptr" (by decide)
  obtain ⟨q, hv, hready, hs⟩ := compute_jumpdests_evm_run s hP nw p f hn hp hf hnb v hr
  exact ⟨⟨q, hv⟩, hready, hs⟩

/-- A returning jumpdest call retains the caller's message local and threads
the original step frame through its scratch allocation. -/
theorem compute_jumpdests_resume (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    DecCallResumeOn
      (fun s => D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
        s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (fun s => D0Pre gw hp G ch s ∧ ∃ jd : BitVec 64,
        s.locals.lookup (ofString "jd") = some (.val (.word jd)))
      (ofString "jd") (ofString "compute_jumpdests")
      [.var .local (ofString "code"), .var .local (ofString "code_n")] := by
  intro F s values body callee ret v post hc hD hargs hl hb
  have hvals : values = [.val (.word code), .val (.word code_n)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hD.2.1, hD.2.2] using hargs.symm
  subst values
  have hlookup := lookup_compute_jumpdests
  rw [hc] at hl
  have hparams : body = sourceFnBody Guest.Software.guestFn_compute_jumpdests ∧
      callee.lookup (ofString "n") = some (.val (.word code_n)) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i b l rs raw
      cases hl
      unfold lookupCodeHOLExact at raw
      rw [hlookup] at raw
      simp [shapeOfHOLExact, shapeEqHOL] at raw
      exact ⟨raw.2.1.symm, by dsimp only; rw [← raw.2.2.1]; simp⟩
  rcases hparams with ⟨rfl, hncal⟩
  have hentry : EvmMsgReady (callEntryStateHOLFinite s callee) :=
    localsFree_evmMsgReady s _ _ hD.1.1.1
  have hn : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
      some (.val (.word code_n)) := hncal
  obtain ⟨p, hpw⟩ := hentry.1.2.2.2.2.2.2.2.2.2 "scratch_ptr" (by decide)
  obtain ⟨f, hfw⟩ := hentry.1.2.2.2.2.2.2.2.2.2 "frame_mem_ptr" (by decide)
  have hrun := compute_jumpdests_evm_run (callEntryStateHOLFinite s callee) hentry code_n p f hn hpw hfw hnb v (by rw [hb])
  rw [hb] at hrun
  obtain ⟨jd, rfl, hready, hstep⟩ := hrun
  have hs0 : StepFrom gw hp G ch (callEntryStateHOLFinite s callee) :=
    localsFree_stepFrom gw hp G ch s _ _ hD.1.1.2
  have hs := stepFrom_of_evmStep (fun g hg => by simpa using (List.mem_singleton.1 hg ▸ hsub)) hs0 hstep
  have hpn : globN s "scratch_ptr" = p.toNat := by
    simp [GlobalWord, callEntryStateHOLFinite] at hpw
    simp [globN, hpw]
  have hfn : globN s "frame_mem_ptr" = f.toNat := by
    simp [GlobalWord, callEntryStateHOLFinite] at hfw
    simp [globN, hfw]
  have hfp : f.toNat ≤ p.toNat := by rw [← hpn, ← hfn]; exact hD.1.1.1.1.2.2.2.2.1
  obtain ⟨q, _, _, _, _, hhi, hg, _, _, hm⟩ := compute_jumpdests_run
    (callEntryStateHOLFinite s callee) hentry.1.1.code hentry.1.1 code_n p f hn hpw hfw hfp hnb
    (.val (.word jd)) (by rw [hb])
  rw [hb] at hg hm
  have hmem : ∀ a : BitVec 64, ¬ CellHits a.toNat (q.toNat, (jdLen code_n).toNat) → post.memory a = s.memory a := hm
  have hhigh : q.toNat + (jdLen code_n).toNat ≤ globN s "scratch_ptr" := by rw [hpn]; exact hhi
  have hw := (fresh_scratch_chain_words (evmInv_of_evmMsgReady s hD.1.1.1) _ _ hhigh hmem).1
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain; exact List.mem_cons_self
  have hev : globN post "ev" = globN s "ev" := by
    unfold globN
    rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, callEntryStateHOLFinite,
      show ofString "scratch_ptr" ≠ ofString "ev" by decide]
  obtain ⟨_, m, hm0, hmeq⟩ := hD.1
  refine ⟨⟨⟨localsFree_evmMsgReady post _ _ hready, localsFree_stepFrom gw hp G ch post _ _ hs⟩,
    m, ?_, ?_⟩, jd, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "jd" ≠ ofString "msg" by decide] using hm0
  · change m.toNat = memW post (globN post "ev" + 112)
    rw [hev, hw _ hhead 112 (by decide)]
    exact hmeq

/-- The returning common dispatch tail allocates jumpdest scratch, installs
the bitmap pointer and retains readiness together with the original step. -/
theorem prepare_dispatch_jumpdest_ret {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (hcode : s.code = originalRuntimeCode) (code code_n : BitVec 64)
    (hD : D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Ret s (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
      [.var .local (ofString "code"), .var .local (ofString "code_n")]
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
        (.var .local (ofString "jd"))) (.return (.const 0#64))))
      (fun _ post => EvmMsgReady post ∧ StepFrom gw hp G ch post) := by
  apply Ret.decCall_gen
  intro values body callee ret v post hargs hl hb
  have hR := compute_jumpdests_resume gw hp G ch code code_n hnb hsub
    s values body callee ret v post hcode hD hargs hl hb
  obtain ⟨hD', jd, hjd⟩ := hR
  have hmeta := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).1
  rw [hb] at hmeta
  have hc' : (setVarHOLFinite (ofString "jd") v {post with locals := s.locals}).code = originalRuntimeCode :=
    hmeta.trans hcode
  intro w hw
  have h := (hoare_prepare_dispatch_jumpdest_finish gw hp G ch jd).run _ hc' ⟨hD', hjd⟩
    (by rw [hw]; simp) (Or.inr (Or.inl ⟨w, hw⟩))
  exact ⟨localsFree_evmMsgReady _ _ _ h.1, localsFree_stepFrom gw hp G ch _ _ _ h.2⟩

/-- The complete common dispatch tail, including all four code stores and
the returning jumpdest call, retains the caller's original step frame. -/
theorem prepare_dispatch_common_ret {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gw : List String) (hp : Nat) (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (hcode : s.code = originalRuntimeCode) (code code_n : BitVec 64)
    (hD : D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Ret s
      (.seq (.store (.op .add [.var .local (ofString "msg"), .const 112#64])
          (.var .local (ofString "code")))
        (.seq (.store (.op .add [.var .local (ofString "msg"), .const 120#64])
            (.var .local (ofString "code_n")))
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const 48#64])
              (.var .local (ofString "code")))
            (.seq (.store (.op .add [.var .global (ofString "ev"), .const 56#64])
                (.var .local (ofString "code_n")))
              (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
                [.var .local (ofString "code"), .var .local (ofString "code_n")]
                (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
                  (.var .local (ofString "jd"))) (.return (.const 0#64))))))))
      (fun _ post => EvmMsgReady post ∧ StepFrom gw hp G ch post) := by
  let L : HolFiniteMapExact MlS (ValueHOL 64) → Prop := fun locals =>
    locals.lookup (ofString "code") = some (.val (.word code)) ∧
    locals.lookup (ofString "code_n") = some (.val (.word code_n))
  have step : ∀ (t : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) (tail : ProgHOL 64),
      t.code = originalRuntimeCode → (D0Pre gw hp G ch t ∧ L t.locals) →
      Hoare (fun t => D0Pre gw hp G ch t ∧ L t.locals) (.store d e)
        (Fall (fun t => D0Pre gw hp G ch t ∧ L t.locals)) →
      (∀ u : PanSemStateFiniteExact 64 F, u.code = originalRuntimeCode →
        (D0Pre gw hp G ch u ∧ L u.locals) →
        Ret u tail (fun _ post => EvmMsgReady post ∧ StepFrom gw hp G ch post)) →
      Ret t (.seq (.store d e) tail) (fun _ post => EvmMsgReady post ∧ StepFrom gw hp G ch post) := by
    intro t d e tail hc ht hstore htail
    apply Ret.seq
    · intro v hv
      rcases store_result_none_or_error t d e with h | h <;> rw [h] at hv <;> cases hv
    · intro u hu
      have h := hstore.run t hc ht (by rw [hu]; simp) (Or.inl (by rw [hu]))
      rw [hu] at h
      have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata t (.store d e)).1
      rw [hu] at hm
      exact htail u (hm.trans hc) h
  apply step s _ _ _ hcode hD
    (hoare_store_msg_local_step gw hp G ch 112 (by decide) _ code L (fun _ h => h.1))
  intro s1 hc1 h1
  apply step s1 _ _ _ hc1 h1
    (hoare_store_msg_local_step gw hp G ch 120 (by decide) _ code_n L (fun _ h => h.2))
  intro s2 hc2 h2
  apply step s2 _ _ _ hc2 h2
    (hoare_store_dispatch_local_step gw hp G ch 48 (by decide) _ code L (fun _ h => h.1))
  intro s3 hc3 h3
  apply step s3 _ _ _ hc3 h3
    (hoare_store_dispatch_local_step gw hp G ch 56 (by decide) _ code_n L (fun _ h => h.2))
  intro s4 hc4 h4
  exact prepare_dispatch_jumpdest_ret s4 gw hp G ch hc4 code code_n h4 hnb hsub

/-- Compose a returning call with a continuation, excluding catchable
exceptions from the callee and restoring the caller's local scope. -/
theorem Hoare.decCall_returning_fall
    {P Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hQ : LocalsFree Q) (hres : DecCallResumeOn P R name fname args)
    (hnox : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → P s →
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      ∀ e v, e ≠ ofString "TrapErr" →
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some (.exception e v))
    (hcont : Hoare R cont (Fall Q)) :
    Hoare P (.decCall name shape fname args cont) (Fall Q) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [ha] at hr
    rcases hr with hr | hr
    · cases hr
    · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  · simp only [ha] at hnt hr ⊢
    rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hr
      rcases hr with hr | hr
      · cases hr
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body).1
        have hnox' := hnox s values body callee ret hc hP hl
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        rw [hb] at hm hnox'
        simp only [hb] at hnt hr ⊢
        cases r with
        | none =>
          rcases hr with hr | hr
          · cases hr
          · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh] at hnt ⊢
              have hR := hres s values body callee ret v post hc hP ha hl hb
              have hc' : (setVarHOLFinite name v {post with locals := s.locals}).code = originalRuntimeCode := hm.trans hc
              have h := hcont.run _ hc' hR hnt hr
              exact hQ _ _ _ h
            · rw [if_neg ‹_›] at hnt ⊢
              rcases hr with hr | hr
              · cases hr
              · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          | timeOut => simp at hnt
          | exception e v =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨e', v', he, hne⟩
              · cases h
              cases he
              exact (hnox' e v hne rfl).elim
          | error =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          | _ =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

/-- The jumpdest tail preserves readiness on every resuming outcome. -/
theorem hoare_prepare_dispatch_jumpdest (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
        [.var .local (ofString "code"), .var .local (ofString "code_n")]
        (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
          (.var .local (ofString "jd"))) (.return (.const 0#64))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  apply Hoare.decCall_returning_fall
    (R := fun s => D0Pre gw hp G ch s ∧ ∃ jd : BitVec 64,
      s.locals.lookup (ofString "jd") = some (.val (.word jd)))
    (fun s locals k h => ⟨localsFree_evmMsgReady s locals k h.1,
      localsFree_stepFrom gw hp G ch s locals k h.2⟩)
    (fun {_} => compute_jumpdests_resume gw hp G ch code code_n hnb hsub)
  · intro F s values body callee ret hc _ hl e v hne
    rw [hc] at hl
    exact StateRestoreEpilogue.evaluate_noCatchableRaise
      frameOpenCallees frameOpenCallees_good body
      (frameOpenCallees_good _ (by decide) values body callee ret hl)
      (callEntryStateHOLFinite s callee) hc e v hne
  · refine ⟨fun {F} s hc hR hnt hr => ?_⟩
    obtain ⟨hD, jd, hjd⟩ := hR
    exact (hoare_prepare_dispatch_jumpdest_finish gw hp G ch jd).run s hc ⟨hD, hjd⟩ hnt hr

/-- All four common dispatch stores and the jumpdest call preserve the
original step frame on every resuming outcome. -/
theorem hoare_prepare_dispatch_common (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (.seq (.store (.op .add [.var .local (ofString "msg"), .const 112#64])
          (.var .local (ofString "code")))
        (.seq (.store (.op .add [.var .local (ofString "msg"), .const 120#64])
            (.var .local (ofString "code_n")))
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const 48#64])
              (.var .local (ofString "code")))
            (.seq (.store (.op .add [.var .global (ofString "ev"), .const 56#64])
                (.var .local (ofString "code_n")))
              (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
                [.var .local (ofString "code"), .var .local (ofString "code_n")]
                (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
                  (.var .local (ofString "jd"))) (.return (.const 0#64))))))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  exact hoare_prepare_dispatch_common_stores gw hp G ch code code_n _ _
    (fun _ h => h.1.1) (hoare_prepare_dispatch_jumpdest gw hp G ch code code_n hnb hsub)

/-- Continue directly from the delegated-code assignments and message stores,
in the right-associated shape of the translated source. -/
theorem hoare_prepare_dispatch_delegated_cont (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n daddr : BitVec 64) (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
        (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
          (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
            (.seq (.store (.op .add [.var .local (ofString "msg"), .const 104])
              (.var .local (ofString "daddr"))) tail))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  have hf := Hoare.weaken (hoare_prepare_dispatch_delegated_finish gw hp G ch code code_n daddr)
    (Q' := Fall (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))))
    (fun _ _ h hr => ⟨(h hr).1, (h hr).2.1, (h hr).2.2.1⟩)
  have h := Hoare.seq_assoc_fall (Hoare.seq_fall' hf htail (fun _ h => h.1.1))
  refine ⟨fun {F} s hc hp hnt => ?_⟩
  have hr := h.run s hc hp
  rw [evaluateHOLFiniteState_seq_line780] at hr hnt ⊢
  rcases hb : evaluateHOLFiniteState s
      (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode")))) with ⟨r, t⟩
  simp only [hb] at hr hnt ⊢
  cases r with
  | some _ => exact hr hnt
  | none =>
    rw [srd_eval_seq_assoc] at hr
    rw [evaluateHOLFiniteState_seq_line780] at hr hnt ⊢
    rcases hb2 : evaluateHOLFiniteState t
        (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode")))) with ⟨r2, t2⟩
    simp only [hb2] at hr hnt ⊢
    cases r2 with
    | some _ => exact hr hnt
    | none =>
      rw [srd_eval_seq_assoc] at hr
      exact hr hnt

/-- Bind the two words returned by `ext_code_of`, preserving the message and
step frame for the delegated-code test and common dispatch tail. -/
theorem hoare_prepare_dispatch_code_binders (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n : BitVec 64) (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "rcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "rcode") = some (.rStruct [.val (.word code), .val (.word code_n)]))
      (.dec (ofString "code") .one (.rfield 0 (.var .local (ofString "rcode")))
        (.dec (ofString "code_n") .one (.rfield 1 (.var .local (ofString "rcode"))) tail))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  have hLF : LocalsFree (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s) :=
    fun s l k h => ⟨localsFree_evmMsgReady s l k h.1, localsFree_stepFrom gw hp G ch s l k h.2⟩
  refine Hoare.dec_fall (P' := fun s => D0Pre gw hp G ch s ∧
    s.locals.lookup (ofString "rcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
    s.locals.lookup (ofString "code") = some (.val (.word code))) ?_ ?_ hLF
  · intro F s v hP hv
    have hv' : v = .val (.word code) := by
      simpa [evalHOLExact, hP.2] using hv.symm
    subst v
    refine ⟨d0Pre_locals gw hp G ch s _ _ ?_ hP.1, ?_, ?_⟩
    · simp (config := {decide := true}) [HolFiniteMapExact.lookup_update, FUPDATE]
    · simpa (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hP.2
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · refine Hoare.dec_fall ?_ htail hLF
    intro F s v hP hv
    have hv' : v = .val (.word code_n) := by
      simpa [evalHOLExact, hP.2.1] using hv.symm
    subst v
    refine ⟨d0Pre_locals gw hp G ch s _ _ ?_ hP.1, ?_, ?_, ?_⟩
    · simp (config := {decide := true}) [HolFiniteMapExact.lookup_update, FUPDATE]
    · simpa (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hP.2.1
    · simpa (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hP.2.2
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- The source common dispatch suffix, after resolving direct or delegated code. -/
def prepareDispatchCommon : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "msg"), .const 112#64])
      (.var .local (ofString "code")))
    (.seq (.store (.op .add [.var .local (ofString "msg"), .const 120#64])
        (.var .local (ofString "code_n")))
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const 48#64])
          (.var .local (ofString "code")))
        (.seq (.store (.op .add [.var .global (ofString "ev"), .const 56#64])
            (.var .local (ofString "code_n")))
          (.decCall (ofString "jd") .one (ofString "compute_jumpdests")
            [.var .local (ofString "code"), .var .local (ofString "code_n")]
            (.seq (.store (.op .add [.var .global (ofString "ev"), .const 80#64])
              (.var .local (ofString "jd"))) (.return (.const 0#64)))))))

/-- Direct code-pair binding followed by the complete common dispatch suffix. -/
theorem hoare_prepare_dispatch_direct (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "rcode") = some (.rStruct [.val (.word code), .val (.word code_n)]))
      (.dec (ofString "code") .one (.rfield 0 (.var .local (ofString "rcode")))
        (.dec (ofString "code_n") .one (.rfield 1 (.var .local (ofString "rcode")))
          prepareDispatchCommon))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  apply hoare_prepare_dispatch_code_binders
  exact Hoare.mono (hoare_prepare_dispatch_common gw hp G ch code code_n hnb hsub)
    (fun _ h => ⟨h.1, h.2.2⟩)

/-- Delegated code-pair assignment and message updates followed by the same
complete common dispatch suffix. -/
theorem hoare_prepare_dispatch_delegated_common (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (code code_n daddr : BitVec 64)
    (hnb : code_n.toNat < 2 ^ 40) (hsub : "scratch_ptr" ∈ gw) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)))
      (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
        (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
          (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
            (.seq (.store (.op .add [.var .local (ofString "msg"), .const 104])
              (.var .local (ofString "daddr"))) prepareDispatchCommon))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  exact hoare_prepare_dispatch_delegated_cont gw hp G ch code code_n daddr _
    (hoare_prepare_dispatch_common gw hp G ch code code_n hnb hsub)

/-- The dispatch value test is read-only: its word result is available to
the continuation while the owned message and original step frame are retained. -/
theorem hoare_prepare_dispatch_value_zero (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ w : BitVec 64,
      s.locals.lookup (ofString "vz") = some (.val (.word w))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (D0Pre gw hp G ch)
      (.decCall (ofString "vz") .one (ofString "u256_is_zero")
        [.load (.comb [.one, .one, .one, .one])
          (.op .add [.var .local (ofString "msg"), .const 56])] tail)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  have hLO : LocalsOnly ["msg"] (D0Pre gw hp G ch) := by
    intro F s l k hl h
    exact d0Pre_locals gw hp G ch s l k (hl "msg" (by simp)) h
  have hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), D0Pre gw hp G ch s → GuestInv s :=
    fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1)
  exact Hoare.decCall_ro_fall EvmFrameSpecs.ro_u256_is_zero hG
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (fun _ h => h.1)
    (ReadOnlyFn.resumeOn hLO hG EvmFrameSpecs.ro_u256_is_zero (ofString "vz") (by decide) _)
    htail

/-- The read-only value test also retains the recipient local used by the
account-aliveness test and subsequent code lookup. -/
theorem hoare_prepare_dispatch_value_zero_recipient (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (recipient : ValueHOL 64)
    (tail : ProgHOL 64)
    (htail : Hoare (fun s => (D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "recipient") = some recipient) ∧ ∃ w : BitVec 64,
      s.locals.lookup (ofString "vz") = some (.val (.word w))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ s.locals.lookup (ofString "recipient") = some recipient)
      (.decCall (ofString "vz") .one (ofString "u256_is_zero")
        [.load (.comb [.one, .one, .one, .one])
          (.op .add [.var .local (ofString "msg"), .const 56])] tail)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  have hLO : LocalsOnly ["msg", "recipient"] (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "recipient") = some recipient) := by
    intro F s l k hl h
    exact ⟨d0Pre_locals gw hp G ch s l k (hl "msg" (by simp)) h.1,
      (hl "recipient" (by simp)).trans h.2⟩
  have hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      D0Pre gw hp G ch s ∧ s.locals.lookup (ofString "recipient") = some recipient → GuestInv s :=
    fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1.1)
  exact Hoare.decCall_ro_fall EvmFrameSpecs.ro_u256_is_zero hG
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (fun _ h => h.1.1)
    (ReadOnlyFn.resumeOn hLO hG EvmFrameSpecs.ro_u256_is_zero (ofString "vz") (by decide) _)
    htail

/-- Compose the source recipient binder with the value-zero call while
retaining the recipient for the remaining dispatch prelude. -/
theorem hoare_prepare_dispatch_recipient (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (tail : ProgHOL 64)
    (htail : ∀ recipient : ValueHOL 64,
      Hoare (fun s => (D0Pre gw hp G ch s ∧
        s.locals.lookup (ofString "recipient") = some recipient) ∧ ∃ w : BitVec 64,
        s.locals.lookup (ofString "vz") = some (.val (.word w))) tail
        (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (D0Pre gw hp G ch)
      (.dec (ofString "recipient") .one
        (.load .one (.op .add [.var .local (ofString "msg"), .const 32]))
        (.decCall (ofString "vz") .one (ofString "u256_is_zero")
          [.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "msg"), .const 56])] tail))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.dec_fall (P' := fun s => D0Pre gw hp G ch s ∧
    ∃ recipient, s.locals.lookup (ofString "recipient") = some recipient) ?_ ?_ ?_
  · intro F s v hP _
    refine ⟨d0Pre_locals gw hp G ch s _ _ ?_ hP, v, ?_⟩
    · simp (config := {decide := true}) [HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · refine ⟨fun {F} s hc hP hnt hr => ?_⟩
    obtain ⟨hD, recipient, hrecipient⟩ := hP
    exact (hoare_prepare_dispatch_value_zero_recipient gw hp G ch recipient tail
      (htail recipient)).run s hc ⟨hD, hrecipient⟩ hnt hr
  · exact fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩

/-- Checking the three-byte delegation prefix performs no writes. -/
theorem ro_is_valid_delegation : ReadOnlyFn (ofString "is_valid_delegation") :=
  OpHandlersB.HeadMemBridge.RbM15.readOnlyFn_of_guestAst 446 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_valid_delegation rfl
    (fun _ => false) (fun _ h => by cases h) rfl

/-- Resolving a delegation address only checks the prefix and returns a
pointer into the supplied code; it retains memory and globals. -/
theorem ro_get_delegated_code_address : ReadOnlyFn (ofString "get_delegated_code_address") := by
  refine OpHandlersB.HeadMemBridge.RbM15.readOnlyFn_of_guestAst 571
    (by rw [guestAst_len]; decide) Guest.Software.guestFn_get_delegated_code_address rfl
    (fun n => n == ofString "is_valid_delegation") ?_ rfl
  intro n hn
  have he : n = ofString "is_valid_delegation" := by simpa using hn
  rw [he]
  intro values body callee rs hl
  have hlook : originalRuntimeCode.lookup (ofString "is_valid_delegation") =
      some ([(ofString "code", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_is_valid_delegation, .one) :=
    lookup_of_guestAst_getElem 446 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_is_valid_delegation) rfl
  have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup
    (ofString "is_valid_delegation") _ _ body .one rs values callee hlook hl
  subst body
  rfl

/-- The delegation-address call retains both code locals for the source
branch and common suffix, and supplies a word-valued delegation address. -/
theorem hoare_prepare_dispatch_delegation_address (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (code code_n : BitVec 64)
    (tail : ProgHOL 64)
    (htail : Hoare (fun s => (D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))) ∧ ∃ da : BitVec 64,
      s.locals.lookup (ofString "da") = some (.val (.word da))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n)))
      (.decCall (ofString "da") .one (ofString "get_delegated_code_address")
        [.rfield 0 (.var .local (ofString "rcode")),
          .rfield 1 (.var .local (ofString "rcode"))] tail)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    D0Pre gw hp G ch s ∧
      s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
      s.locals.lookup (ofString "code_n") = some (.val (.word code_n))
  have hLO : LocalsOnly ["msg", "code", "code_n"] P := by
    intro F s l k hl h
    exact ⟨d0Pre_locals gw hp G ch s l k (hl "msg" (by simp)) h.1,
      (hl "code" (by simp)).trans h.2.1, (hl "code_n" (by simp)).trans h.2.2⟩
  have hG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s :=
    fun s h => evmInv_guestInv s (evmInv_of_evmMsgReady s h.1.1.1)
  exact Hoare.decCall_ro_fall ro_get_delegated_code_address hG
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (fun _ h => h.1.1)
    (ReadOnlyFn.resumeOn hLO hG ro_get_delegated_code_address (ofString "da") (by decide) _)
    htail

/-- The code words selected by either dispatch branch, including the bound
required by `compute_jumpdests`. -/
def DispatchCodeReady (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  D0Pre gw hp G ch s ∧ ∃ code code_n : BitVec 64,
    s.locals.lookup (ofString "code") = some (.val (.word code)) ∧
    s.locals.lookup (ofString "code_n") = some (.val (.word code_n)) ∧ code_n.toNat < 2 ^ 40

theorem hoare_prepare_dispatch_common_ready (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hsub : "scratch_ptr" ∈ gw) :
    Hoare (DispatchCodeReady gw hp G ch) prepareDispatchCommon
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  obtain ⟨hD, code, code_n, hcode, hn, hnb⟩ := hP
  exact (hoare_prepare_dispatch_common gw hp G ch code code_n hnb hsub).run
    s hc ⟨hD, hcode, hn⟩ hnt hr

/-- Compose the source delegation conditional with the common suffix once
the delegated path has established code readiness. -/
theorem hoare_prepare_dispatch_branch_common (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hsub : "scratch_ptr" ∈ gw)
    (delegated : ProgHOL 64)
    (hdelegated : Hoare (fun s => DispatchCodeReady gw hp G ch s ∧
      CondTrue (.cmp .notEqual (.var .local (ofString "da")) (.const 0)) s)
      delegated (Fall (DispatchCodeReady gw hp G ch))) :
    Hoare (DispatchCodeReady gw hp G ch)
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "da")) (.const 0)) delegated .skip)
        prepareDispatchCommon)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.seq_fall' (Hoare.ite_fall hdelegated ?_)
    (hoare_prepare_dispatch_common_ready gw hp G ch hsub) (fun _ h => h.1.1)
  exact Hoare.mono Hoare.skip_fall (fun _ h => h.1)

/-- The delegated-code assignments preserve the callee's length bound while
establishing readiness for the common suffix. -/
theorem hoare_prepare_dispatch_delegated_finish_ready (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ code code_n daddr : BitVec 64,
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)) ∧ code_n.toNat < 2 ^ 40)
      (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
        (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
          (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
            (.store (.op .add [.var .local (ofString "msg"), .const 104])
              (.var .local (ofString "daddr"))))))
      (Fall (DispatchCodeReady gw hp G ch)) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  obtain ⟨hD, code, code_n, daddr, hdcode, hdaddr, hnb⟩ := hP
  have h := (hoare_prepare_dispatch_delegated_finish gw hp G ch code code_n daddr).run
    s hc ⟨hD, hdcode, hdaddr⟩ hnt hr
  exact ⟨h.1, code, code_n, h.2.1, h.2.2.1, hnb⟩

/-- A pure heap allocation preserves the owned message and the complete EVM frame. -/
theorem evmMsgReady_of_heap_alloc_pure {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (h : EvmMsgReady s)
    (p q : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hpq : p.toNat ≤ q.toNat) (hq : q.toNat ≤ heapLimit) (hq8 : q.toNat % 8 = 0)
    (hc : post.code = s.code) (hd : post.memaddrs = s.memaddrs)
    (hs : post.shMemaddrs = s.shMemaddrs) (hb : post.baseAddr = s.baseAddr)
    (hbe : post.be = s.be)
    (hg : post.globals = s.globals.update (ofString "heap_ptr", .val (.word q)))
    (hm : post.memory = s.memory) :
    EvmMsgReady post ∧ EvmStep ["heap_ptr"] s post := by
  have hA := h.1
  have hpn : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hqn : globN post "heap_ptr" = q.toNat := by
    simp [globN, hg, HolFiniteMapExact.lookup_update, FUPDATE]
  have hG : GlobalsKept ["heap_ptr"] s post := by
    intro g hn
    have hne : g ≠ ofString "heap_ptr" := by simpa using hn
    simp [hg, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  have hgn : ∀ g : String, ofString g ≠ ofString "heap_ptr" →
      globN post g = globN s g := by
    intro g hn
    unfold globN
    rw [hG (ofString g) (by simpa using hn)]
  have hAp : ArenaReady post := by
    refine ⟨⟨hc.trans hA.1.code, hd.trans hA.1.memaddrs,
      hs.trans hA.1.shMemaddrs, hb.trans hA.1.baseAddr⟩, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hqn]; have := hA.2.1; rw [hpn] at this; omega
    · rw [hqn]; exact hq
    · rw [hgn "frame_mem_ptr" (by decide)]; exact hA.2.2.2.1
    · rw [hgn "frame_mem_ptr" (by decide), hgn "scratch_ptr" (by decide)]
      exact hA.2.2.2.2.1
    · rw [hgn "scratch_ptr" (by decide)]; exact hA.2.2.2.2.2.1
    · rw [hqn]; exact hq8
    · rw [hgn "frame_mem_ptr" (by decide)]; exact hA.2.2.2.2.2.2.2.1
    · rw [hgn "scratch_ptr" (by decide)]; exact hA.2.2.2.2.2.2.2.2.1
    · exact globalsWord_update _ _ hg hA.2.2.2.2.2.2.2.2.2
  obtain ⟨_, S, hI⟩ := evmInv_of_evmMsgReady s h
  obtain ⟨hIp, hch, _⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step hA hI hAp hbe
    (by rw [hpn, hqn]; exact hpq) hG (fun _ _ => by rw [hm])
    (fun _ _ _ => by simp [memB, hm, hbe])
  have hInv : EvmInv post := ⟨hAp, S, hIp⟩
  exact ⟨evmMsgReady_of_evmInv post hInv, hInv, by rw [hpn, hqn]; exact hpq,
    hG, hch⟩

/-- The actual allocator returns the old heap pointer, reserves the requested
bytes and changes no memory, retaining the dispatch frame. -/
theorem dispatch_alloc_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (h : EvmMsgReady s)
    (p n : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    Ret s (sourceFnBody Guest.Software.guestFn_alloc) (fun v post =>
      v = .val (.word p) ∧ EvmMsgReady post ∧ EvmStep ["heap_ptr"] s post ∧
      p.toNat + n.toNat ≤ globN post "heap_ptr" ∧ post.memory = s.memory ∧
      post.globals = s.globals.update (ofString "heap_ptr",
        .val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8))))) := by
  intro v hv
  have hpn : globN s "heap_ptr" = p.toNat := by simp [globN, hp]
  have hp_le : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    change p.toNat ≤ heapLimit
    rw [← hpn]
    exact h.1.2.2.1
  obtain ⟨rfl, hg, hm, hfit, hlim, h8⟩ :=
    M13.evaluate_alloc_body_general s p n hc hp_le hp hn v hv
  have hmeta := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata s
    (sourceFnBody Guest.Software.guestFn_alloc)
  have hguest := M13.evaluateHOLFiniteState_guestInv_be s
    (sourceFnBody Guest.Software.guestFn_alloc) h.1.1
  have hr := evmMsgReady_of_heap_alloc_pure h p _ hp (by omega) hlim h8
    hmeta.1 hmeta.2.1 (hguest.1.shMemaddrs.trans h.1.1.shMemaddrs.symm)
    (hguest.1.baseAddr.trans h.1.1.baseAddr.symm) hguest.2 hg hm
  refine ⟨rfl, hr.1, hr.2, ?_, hm, hg⟩
  simpa [globN, hg, HolFiniteMapExact.lookup_update, FUPDATE] using hfit

/-- Allocate the aligned 24-byte delegation-address buffer while retaining
the caller's message local and original step frame. -/
theorem dispatch_alloc_resume (gw : List String) (hp0 : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hh : "heap_ptr" ∈ gw) :
    DecCallResumeOn (D0Pre gw hp0 G ch)
      (fun s => D0Pre gw hp0 G ch s ∧ ∃ p : BitVec 64,
        s.locals.lookup (ofString "daddr") = some (.val (.word p)) ∧
        sourceBase ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat + 24 ≤ globN s "heap_ptr")
      (ofString "daddr") (ofString "alloc") [.const 24] := by
  intro F s values body callee ret v post hc hD ha hl hb
  have hv : values = [.val (.word (24 : BitVec 64))] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using ha.symm
  subst values
  rw [hc] at hl
  have hlookup : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
  have hparams : body = sourceFnBody Guest.Software.guestFn_alloc ∧
      callee.lookup (ofString "n") = some (.val (.word (24 : BitVec 64))) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i b l rs raw
      cases hl
      unfold lookupCodeHOLExact at raw
      rw [hlookup] at raw
      simp [shapeOfHOLExact, shapeEqHOL] at raw
      exact ⟨raw.1.symm, by dsimp only; rw [← raw.2.1]; simp⟩
  rcases hparams with ⟨rfl, hn⟩
  have hE := localsFree_evmMsgReady s callee (s.clock - 1) hD.1.1
  obtain ⟨p, hp⟩ := hE.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  have hrun := dispatch_alloc_run (callEntryStateHOLFinite s callee) hc hE p 24 hp hn v
    (by rw [hb])
  rw [hb] at hrun
  obtain ⟨rfl, hready, hstep, hfit, hm, hg⟩ := hrun
  dsimp only at hready hstep hfit hm hg
  have hS := stepFrom_of_evmStep
    (fun g hg => by simpa using (List.mem_singleton.1 hg ▸ hh))
    (localsFree_stepFrom gw hp0 G ch s callee (s.clock - 1) hD.1.2) hstep
  have hev : globN post "ev" = globN s "ev" := by
    simp (config := {decide := true}) [globN, hg, HolFiniteMapExact.lookup_update,
      FUPDATE, callEntryStateHOLFinite]
  obtain ⟨_, m, hml, hmw⟩ := hD
  refine ⟨⟨⟨localsFree_evmMsgReady post _ _ hready,
    localsFree_stepFrom gw hp0 G ch post _ _ hS⟩, m, ?_, ?_⟩, p, ?_, ?_, ?_, hfit⟩
  · simpa (config := {decide := true}) [setVarHOLFinite,
      HolFiniteMapExact.lookup_update, FUPDATE] using hml
  · change m.toNat = memW post (globN post "ev" + 112)
    rw [hev]
    simpa [memW, hm, callEntryStateHOLFinite] using hmw
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · have hpn : globN s "heap_ptr" = p.toNat := by
      change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
      simp [globN, hp]
    rw [← hpn]
    exact hE.1.2.1
  · have hpn : globN s "heap_ptr" = p.toNat := by
      change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
      simp [globN, hp]
    rw [← hpn]
    exact hE.1.2.2.2.2.2.2.1

/-- Resolve direct or delegated code and enter the verified common suffix. -/
theorem hoare_prepare_dispatch_resolve_branch (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hsub : "scratch_ptr" ∈ gw)
    (delegated : ProgHOL 64)
    (hdelegated : Hoare (fun s => DispatchCodeReady gw hp G ch s ∧
      CondTrue (.cmp .notEqual (.var .local (ofString "da")) (.const 0)) s)
      delegated (Fall (DispatchCodeReady gw hp G ch))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ code code_n : BitVec 64,
      s.locals.lookup (ofString "rcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      code_n.toNat < 2 ^ 40)
      (.dec (ofString "code") .one (.rfield 0 (.var .local (ofString "rcode")))
        (.dec (ofString "code_n") .one (.rfield 1 (.var .local (ofString "rcode")))
          (.decCall (ofString "da") .one (ofString "get_delegated_code_address")
            [.rfield 0 (.var .local (ofString "rcode")),
              .rfield 1 (.var .local (ofString "rcode"))]
            (.seq (.ite (.cmp .notEqual (.var .local (ofString "da")) (.const 0)) delegated .skip)
              prepareDispatchCommon))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  obtain ⟨hD, code, code_n, hrcode, hnb⟩ := hP
  have hbranch := hoare_prepare_dispatch_branch_common gw hp G ch hsub delegated hdelegated
  have hda := hoare_prepare_dispatch_delegation_address gw hp G ch code code_n _
    (Hoare.mono hbranch (fun _ h =>
      ⟨h.1.1, code, code_n, h.1.2.1, h.1.2.2, hnb⟩))
  have hbind := hoare_prepare_dispatch_code_binders gw hp G ch code code_n _
    (Hoare.mono hda (fun _ h => ⟨h.1, h.2.2⟩))
  exact hbind.run s hc ⟨hD, hrcode⟩ hnt hr

/-- Continue after allocating the delegation-address buffer on every
resuming outcome; allocator exceptions cannot escape as catchable raises. -/
theorem hoare_prepare_dispatch_alloc (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hh : "heap_ptr" ∈ gw)
    (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ p : BitVec 64,
      s.locals.lookup (ofString "daddr") = some (.val (.word p)) ∧
      sourceBase ≤ p.toNat ∧ p.toNat % 8 = 0 ∧ p.toNat + 24 ≤ globN s "heap_ptr")
      tail (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (D0Pre gw hp G ch)
      (.decCall (ofString "daddr") .one (ofString "alloc") [.const 24] tail)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.decCall_returning_fall
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (dispatch_alloc_resume gw hp G ch hh) ?_ htail
  intro F s values body callee ret hc _ hl e v he
  rw [hc] at hl
  exact StateRestoreEpilogue.evaluate_noCatchableRaise
    StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good body
    (StateRestoreEpilogue.htabMutCallees_good _ (by decide) values body callee ret hl)
    (callEntryStateHOLFinite s callee) hc e v he

/-- The source delegation copy writes only its twenty destination bytes. -/
theorem dispatch_memcpy_effect {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : BitVec 64) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hdst : s.locals.lookup (ofString "daddr") = some (.val (.word dst)))
    (hsrc : s.locals.lookup (ofString "da") = some (.val (.word src)))
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).1) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).2
      [(dst.toNat, 20)] := by
  have he := R13Shards.Keccak256.call0_byteEff R13Shards.Keccak256.funByteEff_memcpy s
    [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20]
    [(dst.toNat, 20)] hc hG (by
      intro vals hv i hi _
      have hv' : vals = [.val (.word dst), .val (.word src), .val (.word (20 : BitVec 64))] := by
        simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hdst, hsrc] using hv.symm
      subst vals
      simp [R13Shards.Keccak256.valWordNat] at hi
      subst i
      exact ⟨(dst.toNat, 20), by simp, le_rfl, le_rfl⟩) hnt hr
  refine ⟨he.code, he.memaddrs, he.shMemaddrs, he.baseAddr, he.be, he.globals, ?_, ?_, ?_⟩
  · intro a ha
    by_contra hn
    exact ha (he.out_dom a hn)
  · intro a hn
    by_contra hne
    obtain ⟨i, hi, hpos, hhit⟩ := he.cell_frame a hne
    exact hn i hi (by omega) hhit
  · intro b hb hn
    by_contra hne
    obtain ⟨i, hi, hin⟩ := he.byte_frame b hb hne
    exact hn i hi hin

/-- Allocation followed by a twenty-byte write inside its fresh extent
preserves the original EVM frame, including all messages and trie ownership. -/
theorem evmStep_of_alloc_copy {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReady s) (hmid : ArenaReady mid)
    (hhp : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hG : GlobalsKept ["heap_ptr"] s mid)
    (hm : mid.memory = s.memory) (hbe : mid.be = s.be)
    (dst : Nat) (hlo : globN s "heap_ptr" ≤ dst)
    (hhi : dst + 20 ≤ globN mid "heap_ptr")
    (he : ByteRegionEffect mid post [(dst, 20)]) :
    EvmMsgReady post ∧ EvmStep ["heap_ptr"] s post := by
  have hgn : ∀ name : String, globN post name = globN mid name := by
    intro name; unfold globN; rw [he.globals]
  have hAp : ArenaReady post := by
    refine ⟨⟨he.code.trans hmid.1.code, he.memaddrs.trans hmid.1.memaddrs,
      he.shMemaddrs.trans hmid.1.shMemaddrs, he.baseAddr.trans hmid.1.baseAddr⟩, ?_⟩
    simpa only [ArenaOK, globN, he.globals, GlobalsWord, GlobalWord] using hmid.2
  obtain ⟨hAs, S, hI⟩ := evmInv_of_evmMsgReady s h
  have hmem : ∀ a, ¬ s.memaddrs a → post.memory a = s.memory a := by
    intro a ha
    have hd : mid.memaddrs = s.memaddrs := hmid.1.memaddrs.trans hAs.1.memaddrs.symm
    exact (he.out_dom a (by rw [hd]; exact ha)).trans (congrFun hm a)
  have hbyte : ∀ b, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b := by
    intro b hb hn
    rw [hgn] at hn
    have hmB : memB mid b = memB s b := by simp [memB, hm, hbe]
    refine (he.byte_frame b hb ?_).trans hmB
    intro i hi hin
    simp only [List.mem_singleton] at hi
    subst i
    unfold InIvl at hin
    exact hn ⟨by omega, by omega⟩
  have hG' : GlobalsKept ["heap_ptr"] s post := by
    intro g hg; rw [he.globals]; exact hG g hg
  obtain ⟨hIp, hch, _⟩ := OpHandlersB.evmInvAt_of_fresh_heap_step hAs hI hAp
    (he.be.trans hbe) (by rw [hgn]; exact hhp) hG' hmem hbyte
  have hInv : EvmInv post := ⟨hAp, S, hIp⟩
  exact ⟨evmMsgReady_of_evmInv post hInv, hInv, by rw [hgn]; exact hhp, hG', hch⟩

/-- The delegation copy also retains the caller's message-pointer relation. -/
theorem d0Pre_of_alloc_copy (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (hD : D0Pre gw hp G ch s) (hmid : ArenaReady mid)
    (hh : "heap_ptr" ∈ gw) (hhp : globN s "heap_ptr" ≤ globN mid "heap_ptr")
    (hG : GlobalsKept ["heap_ptr"] s mid)
    (hm : mid.memory = s.memory) (hbe : mid.be = s.be)
    (hloc : post.locals = s.locals)
    (dst : Nat) (hlo : globN s "heap_ptr" ≤ dst)
    (hhi : dst + 20 ≤ globN mid "heap_ptr")
    (he : ByteRegionEffect mid post [(dst, 20)]) : D0Pre gw hp G ch post := by
  have hP := hD.1.1
  have hstep := (evmStep_of_alloc_copy hP hmid hhp hG hm hbe dst hlo hhi he).2
  have hev : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") := by
    rw [he.globals]; exact (hG (ofString "ev") (by decide)).symm
  have hslot : memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
    have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      unfold evmChain; exact List.mem_cons_self
    have hb := frameWF_bounds (hP.2.choose_spec.1.2.2.2.2.1 _ hhead)
    have hin := ((hP.2.choose_spec.1.2.2.2.2.1 _ hhead).1
      (globN s "ev", 280) (by simp)).1
    have hbound : globN s "scratch_ptr" ≤ globN s "ev" := hin.1
    have hscr : scratchStart ≤ globN s "scratch_ptr" := by
      have h1 := hP.1.2.2.2.1
      have h2 := hP.1.2.2.2.2.1
      omega
    have hheap : globN mid "heap_ptr" ≤ scratchStart := hmid.2.2.1
    unfold memW
    rw [he.cell_frame _ ?_, hm]
    intro i hi _ hhit
    simp only [List.mem_singleton] at hi
    subst i
    unfold CellHits at hhit
    have haddr : (BitVec.ofNat 64 (globN s "ev" + 112)).toNat = globN s "ev" + 112 :=
      Nat.mod_eq_of_lt (by omega)
    rw [haddr] at hhit
    dsimp only at hhit
    omega
  exact d0Pre_of_stepFrom gw hp G ch hD
    (stepFrom_of_evmStep (fun g hg => by simpa using (List.mem_singleton.1 hg ▸ hh))
      hD.1.2 hstep) hloc hev hslot

/-- Allocation evidence retained until the fresh delegation buffer is copied. -/
def DispatchCopyReady (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (mid : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (s : PanSemStateFiniteExact 64 F) (dst src : BitVec 64),
    D0Pre gw hp G ch s ∧ ArenaReady mid ∧
    globN s "heap_ptr" ≤ globN mid "heap_ptr" ∧ GlobalsKept ["heap_ptr"] s mid ∧
    mid.memory = s.memory ∧ mid.be = s.be ∧ mid.locals = s.locals ∧
    mid.locals.lookup (ofString "daddr") = some (.val (.word dst)) ∧
    mid.locals.lookup (ofString "da") = some (.val (.word src)) ∧
    globN s "heap_ptr" ≤ dst.toNat ∧ dst.toNat + 20 ≤ globN mid "heap_ptr"

theorem dispatch_alloc_copy_resume (gw : List String) (hp0 : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) :
    DecCallResumeOn (fun s => D0Pre gw hp0 G ch s ∧ ∃ src : BitVec 64,
      s.locals.lookup (ofString "da") = some (.val (.word src)))
      (DispatchCopyReady gw hp0 G ch) (ofString "daddr") (ofString "alloc") [.const 24] := by
  intro F s values body callee ret v post hc hP ha hl hb
  obtain ⟨hD, src, hsrc⟩ := hP
  have hv : values = [.val (.word (24 : BitVec 64))] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using ha.symm
  subst values
  rw [hc] at hl
  have hlookup : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_alloc) rfl
  have hparams : body = sourceFnBody Guest.Software.guestFn_alloc ∧
      callee.lookup (ofString "n") = some (.val (.word (24 : BitVec 64))) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i b l rs raw
      cases hl
      unfold lookupCodeHOLExact at raw
      rw [hlookup] at raw
      simp [shapeOfHOLExact, shapeEqHOL] at raw
      exact ⟨raw.1.symm, by dsimp only; rw [← raw.2.1]; simp⟩
  rcases hparams with ⟨rfl, hn⟩
  have hE := localsFree_evmMsgReady s callee (s.clock - 1) hD.1.1
  obtain ⟨p, hp⟩ := hE.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  have hrun := dispatch_alloc_run (callEntryStateHOLFinite s callee) hc hE p 24 hp hn v
    (by rw [hb])
  rw [hb] at hrun
  obtain ⟨rfl, hready, hstep, hfit, hm, hg⟩ := hrun
  dsimp only at hready hstep hfit hm hg
  let L := (setVarHOLFinite (ofString "daddr") (.val (.word p)) s).locals
  let s0 := { s with locals := L }
  have hD0 : D0Pre gw hp0 G ch s0 := by
    apply d0Pre_locals gw hp0 G ch s L s.clock _ hD
    simp (config := {decide := true}) [L, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hready' := localsFree_evmMsgReady post L post.clock hready
  refine ⟨s0, p, src, hD0, hready'.1, ?_, ?_, hm, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact hstep.2.1
  · exact hstep.2.2.1
  · exact (M13.evaluateHOLFiniteState_guestInv_be
      (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_alloc)
      (evmInv_guestInv _ (evmInv_of_evmMsgReady _ hE))).2 |> fun he => by
        rw [hb] at he; exact he
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · simpa (config := {decide := true}) [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hsrc
  · have hpn : globN s "heap_ptr" = p.toNat := by
      change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
      simp [globN, hp]
    exact le_of_eq hpn
  · change p.toNat + 20 ≤ globN post "heap_ptr"
    have hn24 : (24 : BitVec 64).toNat = 24 := rfl
    rw [hn24] at hfit
    omega

theorem dispatch_call_none_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  unfold evalListHOLFinite at hnone ⊢
  rcases h1 : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp [h1] at hnone
  · simp only [h1] at hnone ⊢
    rcases h2 : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn vs with _ | ⟨b, c, r⟩
    · simp [h2] at hnone
    · simp only [h2] at hnone ⊢
      split at hnone
      · simp at hnone
      · rename_i hcz; rw [if_neg hcz]
        rcases h3 : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, sb⟩
        simp only [h3] at hnone ⊢
        rcases rb with _ | rb'
        · simp at hnone
        · cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hsh; rw [if_pos hsh]
            · simp at hnone
          | _ => simp at hnone

/-- Copy the delegated address while preserving the original dispatch frame. -/
theorem hoare_prepare_dispatch_memcpy (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hh : "heap_ptr" ∈ gw) :
    Hoare (DispatchCopyReady gw hp G ch)
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])
      (Fall (fun s => D0Pre gw hp G ch s ∧ ∃ dst : BitVec 64,
        s.locals.lookup (ofString "daddr") = some (.val (.word dst)))) := by
  refine ⟨fun {F} mid hc hP hnt hr => ?_⟩
  obtain ⟨s, dst, src, hD, hmid, hhp, hG, hm, hbe, hloc, hdst, hsrc, hlo, hhi⟩ := hP
  have he := dispatch_memcpy_effect mid dst src hc (arenaReady_guestInv mid hmid)
    hdst hsrc hnt hr
  have hnox := StateRestoreEpilogue.evaluate_noCatchableRaise
    StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])
    (by decide) mid hc
  have hnone : (evaluateHOLFiniteState mid (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20])).1 = none := by
    rcases hr with hr | ⟨v, hv⟩ | ⟨e, v, hev, hne⟩
    · exact hr
    · rw [evaluateHOLFiniteState_call] at hv
      exfalso
      revert hv
      split <;> [simp; (split <;> [simp; (split <;> [simp; skip])])]
      rcases evaluateHOLFiniteState (callEntryStateHOLFinite mid _) _ with ⟨rc, _⟩
      rcases rc with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only <;> (repeat' split) <;> simp
    · exact (hnox e v hne hev).elim
  have hl := dispatch_call_none_locals mid _ _ hnone
  exact ⟨d0Pre_of_alloc_copy gw hp G ch hD hmid hh hhp hG hm hbe
    (hl.trans hloc) dst.toNat hlo hhi he, dst, by rw [hl]; exact hdst⟩

/-- The actual allocation/copy prefix, composed with a remaining dispatch tail. -/
theorem hoare_prepare_dispatch_alloc_memcpy (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hh : "heap_ptr" ∈ gw)
    (tail : ProgHOL 64)
    (htail : Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ dst : BitVec 64,
      s.locals.lookup (ofString "daddr") = some (.val (.word dst))) tail
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ src : BitVec 64,
      s.locals.lookup (ofString "da") = some (.val (.word src)))
      (.decCall (ofString "daddr") .one (ofString "alloc") [.const 24]
        (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "daddr"), .var .local (ofString "da"), .const 20]) tail))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.decCall_returning_fall
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (dispatch_alloc_copy_resume gw hp G ch) ?_
    (Hoare.seq_fall' (hoare_prepare_dispatch_memcpy gw hp G ch hh) htail (fun _ h => h.1.1))
  intro F s values body callee ret hc _ hl e v he
  rw [hc] at hl
  exact StateRestoreEpilogue.evaluate_noCatchableRaise
    StateRestoreEpilogue.htabMutCallees StateRestoreEpilogue.htabMutCallees_good body
    (StateRestoreEpilogue.htabMutCallees_good _ (by decide) values body callee ret hl)
    (callEntryStateHOLFinite s callee) hc e v he

/-- A code slice contained in the allocated heap has the length bound needed
by the dispatch bitmap allocator. -/
theorem dispatch_code_length_lt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {p n : Nat}
    (hin : Inside (p, n) sourceBase (globN s "heap_ptr")) : n < 2 ^ 40 := by
  have hh : globN s "heap_ptr" ≤ heapLimit := hA.2.2.1
  have hl : heapLimit < 2 ^ 40 := by decide
  obtain ⟨_, hhi⟩ := hin
  dsimp only at hhi
  exact lt_of_le_of_lt (le_trans (Nat.le_add_left n p) (le_trans hhi hh)) hl

/-- Loading a typed code record produces two actual words and preserves the
heap-derived length bound, without relying on its structural return shape. -/
theorem dispatch_code_record_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {v : Nat} (hwords : WordsOK s (v, 16))
    (hin : Inside (memW s v, memW s (v + 8)) sourceBase (globN s "heap_ptr")) :
    ∃ code code_n : BitVec 64,
      s.memory (BitVec.ofNat 64 v) = .word code ∧
      s.memory (BitVec.ofNat 64 (v + 8)) = .word code_n ∧
      code_n.toNat < 2 ^ 40 := by
  obtain ⟨hal, hlen, hw⟩ := hwords
  obtain ⟨code, hc⟩ := hw 0 (by omega)
  obtain ⟨code_n, hn⟩ := hw 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hc
  simp only [Nat.mul_one] at hn
  refine ⟨code, code_n, hc.2, hn.2, ?_⟩
  have hb := dispatch_code_length_lt hA hin
  simpa [memW, hn.2] using hb

/-- Loading a heap-owned code record returns a pair of actual words with the
length bound required by dispatch. -/
theorem dispatch_code_record_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {v : Nat} (hwords : WordsOK s (v, 16))
    (hin : Inside (memW s v, memW s (v + 8)) sourceBase (globN s "heap_ptr"))
    (e0 e8 : ExpHOL 64)
    (h0 : ev s e0 = some (.val (.word (BitVec.ofNat 64 v))))
    (h8 : ev s e8 = some (.val (.word (BitVec.ofNat 64 (v + 8))))) :
    ∃ code code_n : BitVec 64,
      ev s (.rstruct [.load .one e0, .load .one e8]) =
        some (.rStruct [.val (.word code), .val (.word code_n)]) ∧ code_n.toNat < 2 ^ 40 := by
  obtain ⟨code, code_n, hc, hn, hb⟩ := dispatch_code_record_words hA hwords hin
  have hd0 := (hwords.2.2 0 (by omega)).choose_spec.1
  have hd8 := (hwords.2.2 1 (by omega)).choose_spec.1
  simp only [Nat.mul_zero, Nat.add_zero] at hd0
  simp only [Nat.mul_one] at hd8
  unfold ev at h0 h8
  refine ⟨code, code_n, ?_, hb⟩
  simp [ev, evalHOLExact, evalListHOLExact, h0, h8, memLoadHOLExact,
    isWfShapeExactHOL, hd0, hd8, hc, hn]

/-- A returning call may resume by a catchable exception when the callee
establishes the final invariant on that path. -/
theorem Hoare.decCall_returning_exception_fall
    {P Q R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hQ : LocalsFree Q) (hres : DecCallResumeOn P R name fname args)
    (hexc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → P s →
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      ∀ e v post, e ≠ ofString "TrapErr" →
        evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.exception e v), post) → Q post)
    (hcont : Hoare R cont (Fall Q)) :
    Hoare P (.decCall name shape fname args cont) (Fall Q) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [ha] at hr
    rcases hr with hr | hr
    · cases hr
    · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  · simp only [ha] at hnt hr ⊢
    rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hr
      rcases hr with hr | hr
      · cases hr
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    · simp only [hl] at hnt hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hr ⊢
        have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body).1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        rw [hb] at hm
        simp only [hb] at hnt hr ⊢
        cases r with
        | none =>
          rcases hr with hr | hr
          · cases hr
          · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh] at hnt ⊢
              have hR := hres s values body callee ret v post hc hP ha hl hb
              have hc' : (setVarHOLFinite name v {post with locals := s.locals}).code = originalRuntimeCode := hm.trans hc
              exact hQ _ _ _ (hcont.run _ hc' hR hnt hr)
            · rw [if_neg ‹_›] at hnt ⊢
              rcases hr with hr | hr
              · cases hr
              · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          | timeOut => simp at hnt
          | exception e v =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨e', v', he, hne⟩
              · cases h
              cases he
              exact hQ _ _ _ (hexc s values body callee ret hc hP hl e v post hne hb)
          | error =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
          | _ =>
            rcases hr with hr | hr
            · cases hr
            · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

/-- Compose the external-code call with the delegated stores and common
dispatch suffix, including the callee's catchable-exception path. -/
theorem hoare_prepare_dispatch_ext_delegated (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hsub : "scratch_ptr" ∈ gw)
    (hres : DecCallResumeOn
      (fun s => D0Pre gw hp G ch s ∧ ∃ dst : BitVec 64,
        s.locals.lookup (ofString "daddr") = some (.val (.word dst)))
      (fun s => D0Pre gw hp G ch s ∧ ∃ code code_n daddr : BitVec 64,
        s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
        s.locals.lookup (ofString "daddr") = some (.val (.word daddr)) ∧ code_n.toNat < 2 ^ 40)
      (ofString "dcode") (ofString "ext_code_of") [.var .local (ofString "daddr")])
    (hexc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → D0Pre gw hp G ch s →
      PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "ext_code_of") values =
        some (body, callee, ret) → ∀ e v post, e ≠ ofString "TrapErr" →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.exception e v), post) →
      EvmMsgReady post ∧ StepFrom gw hp G ch post) :
    Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ dst : BitVec 64,
      s.locals.lookup (ofString "daddr") = some (.val (.word dst)))
      (.decCall (ofString "dcode") (.comb [.one, .one]) (ofString "ext_code_of")
        [.var .local (ofString "daddr")]
        (.seq (.assign .local (ofString "code") (.rfield 0 (.var .local (ofString "dcode"))))
          (.seq (.assign .local (ofString "code_n") (.rfield 1 (.var .local (ofString "dcode"))))
            (.seq (.store (.op .add [.var .local (ofString "msg"), .const 168]) (.const 1))
              (.seq (.store (.op .add [.var .local (ofString "msg"), .const 104])
                (.var .local (ofString "daddr"))) prepareDispatchCommon)))))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.decCall_returning_exception_fall
    (R := fun s => D0Pre gw hp G ch s ∧ ∃ code code_n daddr : BitVec 64,
      s.locals.lookup (ofString "dcode") = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
      s.locals.lookup (ofString "daddr") = some (.val (.word daddr)) ∧ code_n.toNat < 2 ^ 40)
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩) (fun {F} => @hres F) ?_ ?_
  · intro F s values body callee ret hc hP hl
    exact hexc s values body callee ret hc hP.1 hl
  · refine ⟨fun {F} s hc hP hnt hr => ?_⟩
    obtain ⟨hD, code, code_n, daddr, hdcode, hdaddr, hnb⟩ := hP
    exact (hoare_prepare_dispatch_delegated_common gw hp G ch code code_n daddr hnb hsub).run
      s hc ⟨hD, hdcode, hdaddr⟩ hnt hr

/-! ## Concrete read-only external-code exception contract -/

/-- `ws_get_code` may raise `StateErr` for a missing code hash.  Every
catchable exception preserves the dispatch invariant, including its original
heap/global/chain anchor. -/
theorem ws_get_code_exception_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret
    (hc : s.code = originalRuntimeCode) (hP : D0Pre gw hp G ch s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values =
      some (body, callee, ret)) (e : MlS) (v : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F) (hne : e ≠ ofString "TrapErr")
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.exception e v), post)) :
    EvmMsgReady post ∧ StepFrom gw hp G ch post := by
  have hG := guestInv_callEntry s callee (evmInv_guestInv s (evmInv_of_evmMsgReady s hP.1.1))
  have heq := FunSpec.at_lookup R16WkAcctWs.ro_ws_get_code s hc values body callee ret hl hG
    (by rw [hr]; simp)
  rw [hr] at heq
  have hres : Resumes (some (.exception e v)) := Or.inr ⟨e, v, rfl, hne⟩
  have heq' := heq hres
  dsimp only [Prod.snd, callEntryStateHOLFinite] at heq'
  rw [heq']
  exact ⟨localsFree_evmMsgReady s post.locals post.clock hP.1.1,
    localsFree_stepFrom gw hp G ch s post.locals post.clock hP.1.2⟩

/-- A normal return from `ws_get_code` restores the caller's message local
and preserves the anchored dispatch precondition for any distinct binder. -/
theorem ws_get_code_resume_step (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (name : MlS) (hne : name ≠ ofString "msg") (args : List (ExpHOL 64)) :
    DecCallResumeOn (D0Pre gw hp G ch) (D0Pre gw hp G ch)
      name (ofString "ws_get_code") args := by
  intro F s values body callee ret v post hc hP _ha hl hr
  have hG := guestInv_callEntry s callee (evmInv_guestInv s (evmInv_of_evmMsgReady s hP.1.1))
  have heq := FunSpec.at_lookup R16WkAcctWs.ro_ws_get_code s hc values body callee ret hl hG
    (by rw [hr]; simp)
  rw [hr] at heq
  have heq' := heq (Or.inl ⟨v, rfl⟩)
  dsimp only [Prod.snd, callEntryStateHOLFinite] at heq'
  have hpost : D0Pre gw hp G ch {post with locals := s.locals} := by
    rw [heq']
    exact d0Pre_locals gw hp G ch s s.locals post.clock rfl hP
  apply d0Pre_locals gw hp G ch _ _ _ ?_ hpost
  simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-- Compose a concrete `ws_get_code` invocation with a dispatch continuation;
both ordinary return and catchable `StateErr` paths preserve its invariant. -/
theorem hoare_ws_get_code_dispatch (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (name : MlS) (hne : name ≠ ofString "msg") (args : List (ExpHOL 64))
    (cont : ProgHOL 64)
    (hcont : Hoare (D0Pre gw hp G ch) cont
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (D0Pre gw hp G ch)
      (.decCall name (.comb [.one, .one]) (ofString "ws_get_code") args cont)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.decCall_returning_exception_fall
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (ws_get_code_resume_step gw hp G ch name hne args) ?_ hcont
  intro F s values body callee ret hc hP hl e v post hne hr
  exact ws_get_code_exception_step gw hp G ch s values body callee ret hc hP hl e v post hne hr

/-- The successful code-record return is a concrete bounded word pair, with
no effect beyond the return epilogue's local reset. -/
theorem dispatch_code_record_return {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {p : Nat} (hw : WordsOK s (p, 16))
    (hin : Inside (memW s p, memW s (p + 8)) sourceBase (globN s "heap_ptr"))
    (e0 e8 : ExpHOL 64)
    (h0 : ev s e0 = some (.val (.word (BitVec.ofNat 64 p))))
    (h8 : ev s e8 = some (.val (.word (BitVec.ofNat 64 (p + 8))))) :
    Ret s (.return (.rstruct [.load .one e0, .load .one e8]))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  obtain ⟨code, code_n, he, hb⟩ := dispatch_code_record_eval hA hw hin e0 e8 h0 h8
  apply Ret.ret
  intro v hv
  rw [he] at hv
  cases hv
  exact ⟨code, code_n, rfl, hb, rfl⟩

/-- The successful `ws_get_code` suffix forwards the concrete code words
from `nodedb_lookup`, retaining their heap-derived bound. -/
theorem ws_get_code_tail_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found code code_n : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]))
    (hn : code_n.toNat < 2 ^ 40) (hf : found ≠ 0) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))])))
      (fun v post => v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  intro v hv
  have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
      some (.val (.word 0)) := by
    simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
    exact hf
  have hi : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip) = (none, s) := by
    rw [evaluateHOLFiniteState_ite]
    change ev s _ = _ at he
    unfold ev at he
    rw [he]
    simp [evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hi] at hv ⊢
  dsimp only at hv ⊢
  rw [evaluateHOLFiniteState_return] at hv ⊢
  simp [evalHOLExact, evalListHOLExact, hr, shapeOfHOLExact,
    sizeOfShapeWithContextHOL] at hv ⊢
  exact ⟨hv.symm, hn, rfl⟩

/-- The final `ext_code_of` return forwards the actual bounded code pair. -/
theorem ext_code_of_tail_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code code_n : BitVec 64)
    (hc : s.locals.lookup (ofString "c") =
      some (.rStruct [.val (.word code), .val (.word code_n)]))
    (hn : code_n.toNat < 2 ^ 40) :
    Ret s (.return (.var .local (ofString "c")))
      (fun v post => v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  apply Ret.ret
  intro v hv
  have he : ev s (.var .local (ofString "c")) =
      some (.rStruct [.val (.word code), .val (.word code_n)]) := hc
  rw [he] at hv
  cases hv
  exact ⟨rfl, hn, rfl⟩

/-- A missing code entry takes exactly the catchable `StateErr(2)` path. -/
theorem ws_get_code_missing_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code code_n : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word 0), .val (.word code), .val (.word code_n)]))
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))]))) =
      (some (.exception (ofString "StateErr") (.val (.word 2))), emptyLocalsHOLFinite s) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
      some (.val (.word 1)) := by
    simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
  unfold ev at he
  rw [he]
  simp [evaluateHOLFiniteState_raise, hshape, evalHOLExact, shapeOfHOLExact]

/-- The successful `nodedb_lookup` return loads a typed code record into
three actual words, with the length bound needed by the `ws_get_code` suffix. -/
theorem nodedb_code_record_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hw : WordsOK s (ptr.toNat, 16))
    (hin : Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) :
    Ret s (.return (.rstruct [.const 1,
      .load .one (.rfield 1 (.var .local (ofString "r"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])]))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word 1), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  obtain ⟨code, code_n, hc, hn, hb⟩ := dispatch_code_record_words hA hw hin
  have hd0 := (hw.2.2 0 (by omega)).choose_spec.1
  have hd8 := (hw.2.2 1 (by omega)).choose_spec.1
  simp only [Nat.mul_zero, Nat.add_zero] at hd0
  simp only [Nat.mul_one] at hd8
  have hc' : s.memory ptr = .word code := by simpa using hc
  have hd0' : s.memaddrs ptr := by simpa using hd0
  have haddr : ptr + 8#64 = BitVec.ofNat 64 (ptr.toNat + 8) := by
    rw [BitVec.ofNat_add]; simp
  have he : ev s (.rstruct [.const 1,
      .load .one (.rfield 1 (.var .local (ofString "r"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])]) =
      some (.rStruct [.val (.word 1), .val (.word code), .val (.word code_n)]) := by
    simp [ev, evalHOLExact, evalListHOLExact, hr, memLoadHOLExact,
      isWfShapeExactHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
      haddr, hd0', hd8, hc', hn]
  apply Ret.ret
  intro v hv
  rw [he] at hv
  cases hv
  exact ⟨code, code_n, rfl, hb, rfl⟩

/-- A successful table lookup reaches the bounded code-record return through
the concrete `nodedb_lookup` found/not-found branch. -/
theorem nodedb_lookup_code_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hfound : found ≠ 0)
    (hw : WordsOK s (ptr.toNat, 16))
    (hin : Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip)
        (.return (.rstruct [.const 1,
          .load .one (.rfield 1 (.var .local (ofString "r"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])])) )
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word 1), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
      some (.val (.word 0)) := by
    simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
    exact hfound
  have hi : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip) = (none, s) := by
    rw [evaluateHOLFiniteState_ite]
    unfold ev at he
    rw [he]
    simp [evaluateHOLFiniteState_skip]
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, hi] at hv ⊢
  exact nodedb_code_record_return s hA found ptr hr hw hin v hv

/-- The missing-table-entry branch returns three zero words without loading
the unconstrained value pointer. -/
theorem nodedb_lookup_missing_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word 0), .val (.word ptr)])) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip)
        (.return (.rstruct [.const 1,
          .load .one (.rfield 1 (.var .local (ofString "r"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])])) ) =
      (some (.returned (.rStruct [.val (.word 0), .val (.word 0), .val (.word 0)])),
        emptyLocalsHOLFinite s) := by
  have he : ev s (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) =
      some (.val (.word 1)) := by
    simp [ev, evalHOLExact, hr, Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  unfold ev at he
  rw [he]
  simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact,
    shapeOfHOLExact, sizeOfShapeWithContextHOL]

/-- Both `nodedb_lookup` suffix branches return bounded word triples when
present table values designate heap-contained code records. -/
theorem nodedb_lookup_code_tail_cases {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hrecord : found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧
      Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.return (.rstruct [.const 0, .const 0, .const 0])) .skip)
        (.return (.rstruct [.const 1,
          .load .one (.rfield 1 (.var .local (ofString "r"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])])) )
      (fun v post => ∃ flag code code_n : BitVec 64,
        v = .rStruct [.val (.word flag), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ (flag = 0 ∨ flag = 1) ∧
        post = {s with locals := post.locals, clock := post.clock}) := by
  by_cases hf : found = 0
  · subst found
    intro v hv
    rw [nodedb_lookup_missing_tail s ptr hr] at hv ⊢
    cases hv
    exact ⟨0, 0, 0, rfl, by decide, Or.inl rfl, rfl⟩
  · intro v hv
    obtain ⟨hw, hin⟩ := hrecord hf
    obtain ⟨code, code_n, hv, hn, hp⟩ := nodedb_lookup_code_tail s hA found ptr hr hf hw hin v hv
    exact ⟨1, code, code_n, hv, hn, Or.inr rfl, hp⟩

/-- Concrete table lookup selects actual bounded code words once its live
values are known to designate heap-contained code records. -/
theorem htab_get_code_record_words {F : Type}
    (s : PanSemStateFiniteExact 64 F) (tw kw : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hk : s.locals.lookup (ofString "key") = some (.val (.word kw)))
    (hW : HtabWF s tw.toNat)
    (hvalues : ∀ p ∈ htabValues s tw.toNat, WordsOK s (p, 16) ∧
      Inside (memW s p, memW s (p + 8)) sourceBase (globN s "heap_ptr"))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_get)).1 =
      some (.returned v)) :
    ∃ found ptr : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word ptr)] ∧
      (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧
        ∃ code code_n : BitVec 64,
          s.memory ptr = .word code ∧
          s.memory (BitVec.ofNat 64 (ptr.toNat + 8)) = .word code_n ∧
          code_n.toNat < 2 ^ 40) := by
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values s tw kw hcode ht hk hW v hret
  refine ⟨found, ptr, hv, fun hf => ?_⟩
  obtain ⟨hw, hin⟩ := hvalues ptr.toNat (hm hf)
  obtain ⟨code, code_n, hc, hn, hb⟩ := dispatch_code_record_words hA hw hin
  exact ⟨hw, code, code_n, by simpa using hc, hn, hb⟩

/-- A returning `ws_get_code` lookup suffix must have found its entry. Missing
entries take the catchable exception branch, so require no code-length premise. -/
theorem ws_get_code_tail_return_cases {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found code code_n : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]))
    (hn : found ≠ 0 → code_n.toNat < 2 ^ 40)
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one) :
    Ret s
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))])))
      (fun v post => found ≠ 0 ∧
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  by_cases hf : found = 0
  · subst found
    intro v hv
    rw [ws_get_code_missing_tail s code code_n hr hshape] at hv
    cases hv
  · intro v hv
    exact ⟨hf, ws_get_code_tail_return s found code code_n hr (hn hf) hf v hv⟩

/-- Equality with the empty code hash returns the empty pair immediately,
independently of the table-lookup continuation. -/
theorem ws_get_code_empty_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (eqw : BitVec 64) (heq : s.locals.lookup (ofString "eq") = some (.val (.word eqw)))
    (hne : eqw ≠ 0) (tail : ProgHOL 64) :
    evaluateHOLFiniteState s
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
        (.return (.rstruct [.const 0, .const 0])) .skip) tail) =
      (some (.returned (.rStruct [.val (.word 0), .val (.word 0)])), emptyLocalsHOLFinite s) := by
  have he : ev s (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) =
      some (.val (.word 1)) := by
    simp [ev, evalHOLExact, heq, Compiler.Encoders.Asm.wordCmpHOL]
    exact hne
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  unfold ev at he
  rw [he]
  simp [evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact,
    shapeOfHOLExact, sizeOfShapeWithContextHOL]

/-- Compose the actual `nodedb_lookup` invocation with both `ws_get_code`
suffix branches. The callee bound is needed only for a present entry. -/
theorem ws_get_code_nodedb_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64))
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hcallee : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "nodedb_lookup") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      post.eshapes = s.eshapes ∧ ∃ found code code_n : BitVec 64,
        v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
        (found ≠ 0 → code_n.toNat < 2 ^ 40)) :
    Ret s (.decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "nodedb_lookup") args
      (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
        (.raise (ofString "StateErr") (.const 2)) .skip)
        (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
          .rfield 2 (.var .local (ofString "r"))]))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  obtain ⟨hs, found, code, code_n, hv, hn⟩ := hcallee values body callee ret v post ha hl hb
  subst v
  let st := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]) {post with locals := s.locals}
  have hr : st.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word code), .val (.word code_n)]) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsh : st.eshapes.lookup (ofString "StateErr") = some .one := by
    change post.eshapes.lookup _ = _
    rw [hs]; exact hshape
  intro w hw
  obtain ⟨_, hv, hb, _⟩ := ws_get_code_tail_return_cases st found code code_n hr hn hsh w hw
  exact ⟨code, code_n, hv, hb⟩

/-- Compose the code-hash comparison with the empty return and the nonempty
lookup continuation. Only the latter needs the bounded lookup contract. -/
theorem ws_get_code_compare_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hcallee : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      ∃ eqw : BitVec 64, v = .val (.word eqw) ∧
        (eqw = 0 → Ret (setVarHOLFinite (ofString "eq") v {post with locals := s.locals}) tail
          (fun v _ => ∃ code code_n : BitVec 64,
            v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40))) :
    Ret s (.decCall (ofString "eq") .one (ofString "memeq") args
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
        (.return (.rstruct [.const 0, .const 0])) .skip) tail))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  obtain ⟨eqw, hv, htail⟩ := hcallee values body callee ret v post ha hl hb
  subst v
  let st := setVarHOLFinite (ofString "eq") (.val (.word eqw)) {post with locals := s.locals}
  have heq : st.locals.lookup (ofString "eq") = some (.val (.word eqw)) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hz : eqw = 0
  · have he : ev st (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) =
        some (.val (.word 0)) := by
      simp [ev, evalHOLExact, heq, hz, Compiler.Encoders.Asm.wordCmpHOL]
    have hi : evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
          (.return (.rstruct [.const 0, .const 0])) .skip) = (none, st) := by
      rw [evaluateHOLFiniteState_ite]
      unfold ev at he
      rw [he]
      simp [evaluateHOLFiniteState_skip]
    intro w hw
    rw [evaluateHOLFiniteState_seq_line780, hi] at hw
    exact htail hz w hw
  · intro w hw
    rw [ws_get_code_empty_tail st eqw heq hz tail] at hw
    cases hw
    exact ⟨0, 0, rfl, by decide⟩

/-- The concrete nonempty-hash lookup continuation of `ws_get_code`. -/
def wsCodeLookupTail : ProgHOL 64 :=
  .decCall (ofString "r") (.comb [.one, .one, .one]) (ofString "nodedb_lookup")
    [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
      .var .local (ofString "code_hash")]
    (.seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0))
      (.raise (ofString "StateErr") (.const 2)) .skip)
      (.return (.rstruct [.rfield 1 (.var .local (ofString "r")),
        .rfield 2 (.var .local (ofString "r"))])))

theorem ws_get_code_body_eq :
    sourceFnBody Guest.Software.guestFn_ws_get_code =
      .decCall (ofString "eq") .one (ofString "memeq")
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
          (.return (.rstruct [.const 0, .const 0])) .skip) wsCodeLookupTail) := by rfl

/-- Full-body return composition, with the remaining nonempty lookup
obligation exposed at the comparison's concrete resumed state. -/
theorem ws_get_code_body_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcompare : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      ∃ eqw : BitVec 64, v = .val (.word eqw) ∧
        (eqw = 0 → Ret (setVarHOLFinite (ofString "eq") v {post with locals := s.locals}) wsCodeLookupTail
          (fun v _ => ∃ code code_n : BitVec 64,
            v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40))) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  rw [ws_get_code_body_eq]
  exact ws_get_code_compare_return s _ wsCodeLookupTail hcompare

/-- Returning declaration calls expose their successful result-shape check
to the continuation proof. -/
theorem Ret.decCall_gen_shape {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) ret) = true →
      Ret (setVarHOLFinite x v {post with locals := s.locals}) cont
        (fun w t => Φ w {t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x)})) :
    Ret s (.decCall x sh fname args cont) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hv ⊢
  revert hv
  split
  · simp
  · rename_i values ha
    split
    · simp
    · rename_i body callee ret hl
      split
      · simp
      · dsimp only
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        dsimp only
        rcases r with _ | r
        · simp
        · cases r with
          | returned w =>
            dsimp only
            split
            · rename_i hs
              intro hv
              exact hk values body callee ret w post ha hl hr hs v hv
            · simp
          | exception _ _ => simp
          | _ => simp

/-- The comparison result is a word by the call's shape check; only the
zero-comparison continuation remains as a callee obligation. -/
theorem ws_get_code_compare_return_of_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (htail : ∀ values body callee ret eqw post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word eqw))), post) →
      eqw = 0 → Ret (setVarHOLFinite (ofString "eq") (.val (.word eqw)) {post with locals := s.locals}) tail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (.decCall (ofString "eq") .one (ofString "memeq") args
      (.seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
        (.return (.rstruct [.const 0, .const 0])) .skip) tail))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen_shape
  intro values body callee ret v post ha hl hb hs
  rcases v with ⟨⟨eqw⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hs)
  let st := setVarHOLFinite (ofString "eq") (.val (.word eqw)) {post with locals := s.locals}
  have heq : st.locals.lookup (ofString "eq") = some (.val (.word eqw)) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hz : eqw = 0
  · have he : ev st (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) =
        some (.val (.word 0)) := by
      simp [ev, evalHOLExact, heq, hz, Compiler.Encoders.Asm.wordCmpHOL]
    have hi : evaluateHOLFiniteState st
        (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
          (.return (.rstruct [.const 0, .const 0])) .skip) = (none, st) := by
      rw [evaluateHOLFiniteState_ite]
      unfold ev at he
      rw [he]
      simp [evaluateHOLFiniteState_skip]
    intro w hw
    rw [evaluateHOLFiniteState_seq_line780, hi] at hw
    exact htail values body callee ret eqw post ha hl hb hz w hw
  · intro w hw
    rw [ws_get_code_empty_tail st eqw heq hz tail] at hw
    cases hw
    exact ⟨0, 0, rfl, by decide⟩

/-- Full concrete `ws_get_code` return composition. Only calls reached after
a zero hash comparison need the present-entry bound from `nodedb_lookup`. -/
theorem ws_get_code_return_of_nodedb {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hlookup : ∀ values body callee ret post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word 0))), post) →
      let st := setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}
      st.eshapes.lookup (ofString "StateErr") = some .one ∧
      ∀ values' body' callee' ret' v' post',
        evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
            .var .local (ofString "code_hash")] = some values' →
        lookupCodeHOLFinite st.code.lookup (ofString "nodedb_lookup") values' = some (body', callee', ret') →
        evaluateHOLFiniteState (callEntryStateHOLFinite st callee') body' = (some (.returned v'), post') →
        post'.eshapes = st.eshapes ∧ ∃ found code code_n : BitVec 64,
          v' = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
          (found ≠ 0 → code_n.toNat < 2 ^ 40)) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  rw [ws_get_code_body_eq]
  apply ws_get_code_compare_return_of_tail
  intro values body callee ret eqw post ha hl hb hz
  subst eqw
  obtain ⟨hs, hn⟩ := hlookup values body callee ret post ha hl hb
  exact ws_get_code_nodedb_return _ _ hs hn

/-- Live database values designate two-word records and heap-contained code.
`WorldOK` types the database table, but does not type its payload records. -/
def NodeDbEntriesStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (db : Nat) : Prop :=
  ∀ p ∈ htabValues s db, WordsOK s (p, 16) ∧
    Inside (memW s p, memW s (p + 8)) sourceBase (globN s "heap_ptr")

theorem nodedb_lookup_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hdb : s.locals.lookup (ofString "db") = some (.val (.word db)))
    (hhash : s.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesStrong s db.toNat) :
    Ret s (sourceFnBody Guest.Software.guestFn_nodedb_lookup)
      (fun v _ => ∃ found code code_n : BitVec 64,
        v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ (found = 0 ∨ found = 1)) := by
  change Ret s (.decCall (ofString "r") (.comb [.one, .one]) (ofString "htab_get")
    [.var .local (ofString "db"), .var .local (ofString "hash")] _) _
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  have hvals : values = [.val (.word db), .val (.word hash)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hdb, hhash] using ha.symm
  subst values
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hcode]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := WkBal.htabWF_with_locals s callee (s.clock - 1) db.toNat |>.2 hW
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values ce db hash hcode ht hk hWce v
    (congrArg Prod.fst hb)
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good (sourceFnBody Guest.Software.guestFn_htab_get)
    (by decide) ce hcode
  rw [hb] at hframe
  have hpost : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, ce, callEntryStateHOLFinite] using hframe
  subst v
  let st := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word found), .val (.word ptr)]) {post with locals := s.locals}
  have hst : st = {s with locals := st.locals, clock := st.clock} := by
    dsimp only [st, setVarHOLFinite]; rw [hpost]
  have hr : st.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hAst : ArenaReady st := by rw [hst]; exact localsFree_arenaReady s _ _ hA
  have hrecord : found ≠ 0 → WordsOK st (ptr.toNat, 16) ∧
      Inside (memW st ptr.toNat, memW st (ptr.toNat + 8)) sourceBase (globN st "heap_ptr") := by
    intro hf
    have hin : ptr.toNat ∈ htabValues s db.toNat := by
      simpa [ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW] using hm hf
    have he := hentries ptr.toNat hin
    rw [hst]
    simpa [WordsOK, WordAt, memW, globN] using he
  intro w hw
  obtain ⟨f, c, n, hv, hn, hf, _⟩ := nodedb_lookup_code_tail_cases st hAst found ptr hr hrecord w hw
  exact ⟨f, c, n, hv, hn, hf⟩

theorem lookup_nodedb_lookup_local :
    originalRuntimeCode.lookup (ofString "nodedb_lookup") =
      some ([(ofString "db", .one), (ofString "hash", .one)],
        sourceFnBody Guest.Software.guestFn_nodedb_lookup, .comb [.one, .one, .one]) :=
  lookup_of_guestAst_getElem 254 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_nodedb_lookup) rfl

theorem nodedb_lookup_call_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesStrong s db.toNat)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "nodedb_lookup")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post.eshapes = s.eshapes ∧ ∃ found code code_n : BitVec 64,
      v = .rStruct [.val (.word found), .val (.word code), .val (.word code_n)] ∧
      (found ≠ 0 → code_n.toNat < 2 ^ 40) := by
  obtain ⟨hbody, hd⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup") []
    (ofString "db") .one [(ofString "hash", .one)] _ (.comb [.one, .one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact lookup_nodedb_lookup_local) (vpre := []) (by simp) hl
  obtain ⟨_, hh⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "nodedb_lookup")
    [(ofString "db", .one)] (ofString "hash") .one [] _ (.comb [.one, .one, .one])
    (by simp) (by rw [hcode]; exact lookup_nodedb_lookup_local)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hAce : ArenaReady ce := localsFree_arenaReady s _ _ hA
  have hWce : HtabWF ce db.toNat := (WkBal.htabWF_with_locals s _ _ _).2 hW
  have he : NodeDbEntriesStrong ce db.toNat := by
    simpa [NodeDbEntriesStrong, ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW,
      WordsOK, WordAt, globN] using hentries
  obtain ⟨f, c, n, hv, hn, _⟩ := nodedb_lookup_return_strong ce db hash hcode hAce hd hh hWce he v
    (congrArg Prod.fst hb)
  refine ⟨?_, f, c, n, hv, fun _ => hn⟩
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata ce (sourceFnBody Guest.Software.guestFn_nodedb_lookup)
  rw [hb] at hm
  exact hm.2.2.2.2

/-- At each reached lookup, the database argument names a well-formed table
whose live payloads are heap-contained code records. -/
def WsCodeLookupStrong {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧ ∀ values,
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
        .var .local (ofString "code_hash")] = some values →
    ∃ db hash : BitVec 64, values = [.val (.word db), .val (.word hash)] ∧
      HtabWF s db.toNat ∧ NodeDbEntriesStrong s db.toNat

/-- Full code retrieval with the exact strengthened payload invariant exposed
at the zero-comparison continuation. -/
theorem ws_get_code_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hstrong : ∀ values body callee ret post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word 0))), post) →
      WsCodeLookupStrong (setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals})) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply ws_get_code_return_of_nodedb
  intro values body callee ret post ha hl hb
  let st := setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}
  obtain ⟨hA, hargs⟩ := hstrong values body callee ret post ha hl hb
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  rw [hb] at hm
  have hstcode : st.code = originalRuntimeCode := hm.1.trans hcode
  have hstshape : st.eshapes.lookup (ofString "StateErr") = some .one := by
    change post.eshapes.lookup _ = _
    rw [hm.2.2.2.2]; exact hshape
  refine ⟨hstshape, ?_⟩
  intro values' body' callee' ret' v' post' ha' hl' hb'
  obtain ⟨db, hash, hv, hW, he⟩ := hargs values' ha'
  subst values'
  exact nodedb_lookup_call_return_strong st db hash hstcode hA hW he _ _ _ _ _ hl' hb'

/-- Entry-state form of the strong code lookup contract. The read-only hash
comparison transports the table and payload invariant to the lookup. -/
theorem ws_get_code_return_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hentry : WsCodeLookupStrong s) :
    Ret s (sourceFnBody Guest.Software.guestFn_ws_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply ws_get_code_return_strong s hcode hshape
  intro values body callee ret post ha hl hb
  have hl' := hl
  rw [hcode] at hl'
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good body
    (R16WkAcctWs.wsGetCodeCallees_good _ (by decide) values body callee ret hl')
    (callEntryStateHOLFinite s callee) hcode
  rw [hb] at hframe
  have hp : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, callEntryStateHOLFinite] using hframe
  let st := setVarHOLFinite (ofString "eq") (.val (.word (0 : BitVec 64))) {post with locals := s.locals}
  change WsCodeLookupStrong st
  have hs : st = {s with locals := st.locals, clock := st.clock} := by
    dsimp only [st, setVarHOLFinite]; rw [hp]
  refine ⟨?_, ?_⟩
  · rw [hs]; exact localsFree_arenaReady s _ _ hentry.1
  · intro vs hvs
    have hs' : st = setVarHOLFinite (ofString "eq") (.val (.word (0 : BitVec 64)))
        {s with clock := post.clock} := by
      dsimp only [st]
      conv_lhs => rw [hp]
    rw [hs'] at hvs
    have heval : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
          .var .local (ofString "code_hash")] = some vs := by
      have he : evalListHOLFinite
          (setVarHOLFinite (ofString "eq") (.val (.word (0 : BitVec 64))) {s with clock := post.clock})
          (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
            .var .local (ofString "code_hash")] =
          evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.load .one (.op .add [.var .global (ofString "ws"), .const 16]),
            .var .local (ofString "code_hash")] := by
        simp (config := {decide := true}) [evalListHOLFinite, evalListHOLExact, evalHOLExact,
          setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      exact he ▸ hvs
    obtain ⟨db, hash, hv, hW, he⟩ := hentry.2 vs heval
    refine ⟨db, hash, hv, ?_, ?_⟩
    · rw [hs]; exact (WkBal.htabWF_with_locals s _ _ _).2 hW
    · rw [hs]
      simpa [NodeDbEntriesStrong, htabValues, hdr, nodeF, memW, WordsOK, WordAt, globN] using he

/-- Word-level entry facts suffice to establish the strong lookup predicate. -/
theorem wsCodeLookupStrong_of_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hA : ArenaReady s)
    (hdb : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hh : s.locals.lookup (ofString "code_hash") = some (.val (.word hash)))
    (hW : HtabWF s db.toNat) (he : NodeDbEntriesStrong s db.toNat) : WsCodeLookupStrong s := by
  refine ⟨hA, ?_⟩
  intro values hv
  have hv' : values = [.val (.word db), .val (.word hash)] := by
    unfold evalHOLFinite at hdb
    simp only [evalListHOLFinite, evalListHOLExact] at hv
    rw [hdb] at hv
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hh] using hv.symm
  exact ⟨db, hash, hv', hW, he⟩

theorem lookup_ws_get_code_local :
    originalRuntimeCode.lookup (ofString "ws_get_code") =
      some ([(ofString "code_hash", .one)], sourceFnBody Guest.Software.guestFn_ws_get_code,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 370 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ws_get_code) rfl

/-- The entry-state result is available directly at a concrete caller lookup. -/
theorem ws_get_code_call_return_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (values : List (ValueHOL 64)) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hentry : WsCodeLookupStrong (callEntryStateHOLFinite s callee))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "ws_get_code")
    _ _ body _ ret values callee (by rw [hcode]; exact lookup_ws_get_code_local) hl
  subst body
  exact ws_get_code_return_entry_strong (callEntryStateHOLFinite s callee) hcode hshape hentry v
    (congrArg Prod.fst hb)

/-- Bounded code words and the original dispatch anchor survive the actual
`ws_get_code` return epilogue and caller-local restoration. -/
theorem ws_get_code_resume_bounded (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (name : MlS) (hne : name ≠ ofString "msg") (args : List (ExpHOL 64))
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → D0Pre gw hp G ch s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret) →
      s.eshapes.lookup (ofString "StateErr") = some .one ∧
        WsCodeLookupStrong (callEntryStateHOLFinite s callee)) :
    DecCallResumeOn (D0Pre gw hp G ch)
      (fun s => D0Pre gw hp G ch s ∧ ∃ code code_n : BitVec 64,
        s.locals.lookup name = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
        code_n.toNat < 2 ^ 40) name (ofString "ws_get_code") args := by
  intro F s values body callee ret v post hc hP ha hl hb
  have hD := ws_get_code_resume_step gw hp G ch name hne args s values body callee ret v post
    hc hP ha hl hb
  obtain ⟨hs, he⟩ := hentry s values body callee ret hc hP ha hl
  obtain ⟨code, code_n, hv, hn⟩ := ws_get_code_call_return_entry_strong s body callee ret
    values v post hc hs he hl hb
  refine ⟨hD, code, code_n, ?_, hn⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv]

/-- Compose bounded code retrieval with a dispatch continuation, including
the missing-entry exception branch and the caller restoration epilogue. -/
theorem hoare_ws_get_code_dispatch_bounded (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl)
    (name : MlS) (hne : name ≠ ofString "msg") (args : List (ExpHOL 64))
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → D0Pre gw hp G ch s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret) →
      s.eshapes.lookup (ofString "StateErr") = some .one ∧
        WsCodeLookupStrong (callEntryStateHOLFinite s callee))
    (cont : ProgHOL 64)
    (hcont : Hoare (fun s => D0Pre gw hp G ch s ∧ ∃ code code_n : BitVec 64,
        s.locals.lookup name = some (.rStruct [.val (.word code), .val (.word code_n)]) ∧
        code_n.toNat < 2 ^ 40) cont
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s))) :
    Hoare (D0Pre gw hp G ch)
      (.decCall name (.comb [.one, .one]) (ofString "ws_get_code") args cont)
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  refine Hoare.decCall_returning_exception_fall
    (fun s l k h => ⟨localsFree_evmMsgReady s l k h.1,
      localsFree_stepFrom gw hp G ch s l k h.2⟩)
    (ws_get_code_resume_bounded gw hp G ch name hne args hentry) ?_ hcont
  intro F s values body callee ret hc hP hl e v post hne hr
  exact ws_get_code_exception_step gw hp G ch s values body callee ret hc hP hl e v post hne hr

/-- The concrete direct dispatch suffix consumes the bounded lookup result. -/
theorem hoare_ws_get_code_dispatch_direct (gw : List String) (hp : Nat)
    (G : MlS → Option (ValueHOL 64)) (ch : List Ivl) (hsub : "scratch_ptr" ∈ gw)
    (args : List (ExpHOL 64))
    (hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values body callee ret,
      s.code = originalRuntimeCode → D0Pre gw hp G ch s →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret) →
      s.eshapes.lookup (ofString "StateErr") = some .one ∧
        WsCodeLookupStrong (callEntryStateHOLFinite s callee)) :
    Hoare (D0Pre gw hp G ch)
      (.decCall (ofString "rcode") (.comb [.one, .one]) (ofString "ws_get_code") args
        (.dec (ofString "code") .one (.rfield 0 (.var .local (ofString "rcode")))
          (.dec (ofString "code_n") .one (.rfield 1 (.var .local (ofString "rcode")))
            prepareDispatchCommon)))
      (Fall (fun s => EvmMsgReady s ∧ StepFrom gw hp G ch s)) := by
  apply hoare_ws_get_code_dispatch_bounded gw hp G ch (ofString "rcode") (by decide) args hentry
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  obtain ⟨hD, code, code_n, hv, hn⟩ := hP
  exact (hoare_prepare_dispatch_direct gw hp G ch code code_n hn hsub).run
    s hc ⟨hD, hv⟩ hnt hr

/-- Both cache-hit branches of `get_code` load a bounded two-word code record. -/
theorem get_code_cache_record_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (found ptr : BitVec 64)
    (hwlocal : s.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hw : WordsOK s (ptr.toNat, 16))
    (hin : Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) :
    Ret s (.return (.rstruct [
      .load .one (.rfield 1 (.var .local (ofString "w"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])]))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  obtain ⟨code, code_n, hc, hn, hb⟩ := dispatch_code_record_words hA hw hin
  have hd0 := (hw.2.2 0 (by omega)).choose_spec.1
  have hd8 := (hw.2.2 1 (by omega)).choose_spec.1
  simp only [Nat.mul_zero, Nat.add_zero] at hd0
  simp only [Nat.mul_one] at hd8
  have hc' : s.memory ptr = .word code := by simpa using hc
  have hd0' : s.memaddrs ptr := by simpa using hd0
  have haddr : ptr + 8#64 = BitVec.ofNat 64 (ptr.toNat + 8) := by
    rw [BitVec.ofNat_add]; simp
  have he : ev s (.rstruct [
      .load .one (.rfield 1 (.var .local (ofString "w"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])]) =
      some (.rStruct [.val (.word code), .val (.word code_n)]) := by
    simp [ev, evalHOLExact, evalListHOLExact, hwlocal, memLoadHOLExact,
      isWfShapeExactHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
      haddr, hd0', hd8, hc', hn]
  apply Ret.ret
  intro v hv
  rw [he] at hv
  cases hv
  exact ⟨code, code_n, rfl, hb, rfl⟩

/-- A cache hit returns its bounded code pair; a miss reaches the next cache
or world-state fallback without changing the current state. -/
theorem get_code_cache_branch_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hA : ArenaReady s) (found ptr : BitVec 64) (tail : ProgHOL 64)
    (hwlocal : s.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hrecord : found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧
      Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr"))
    (hmiss : found = 0 → Ret s tail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
      (.return (.rstruct [
        .load .one (.rfield 1 (.var .local (ofString "w"))),
        .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) tail)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  by_cases hz : found = 0
  · have he : ev s (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) =
        some (.val (.word 0)) := by
      simp [ev, evalHOLExact, hwlocal, hz, Compiler.Encoders.Asm.wordCmpHOL]
    have hi : evaluateHOLFiniteState s
        (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
          (.return (.rstruct [
            .load .one (.rfield 1 (.var .local (ofString "w"))),
            .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) = (none, s) := by
      rw [evaluateHOLFiniteState_ite]
      unfold ev at he
      rw [he]
      exact evaluateHOLFiniteState_skip s
    intro v hv
    rw [evaluateHOLFiniteState_seq_line780, hi] at hv
    exact hmiss hz v hv
  · have he : ev s (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) =
        some (.val (.word 1)) := by
      simp [ev, evalHOLExact, hwlocal, Compiler.Encoders.Asm.wordCmpHOL]
      exact hz
    intro v hv
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hv
    unfold ev at he
    rw [he] at hv
    simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hv
    split at hv
    · rename_i hn
      rw [evaluateHOLFiniteState_return] at hn
      split at hn <;> simp_all
      split at hn <;> simp_all
    · obtain ⟨hw, hin⟩ := hrecord hz
      obtain ⟨code, code_n, hv', hn, _⟩ := get_code_cache_record_return s hA found ptr hwlocal hw hin v hv
      exact ⟨code, code_n, hv', hn⟩

/-- Concrete cache lookup supplies the hit payload from its live table values;
only a genuine miss requires the next-cache/fallback continuation. -/
theorem get_code_cache_lookup_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word db), .val (.word hash)])
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesStrong s db.toNat)
    (hmiss : ∀ values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      Ret (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := s.locals}) tail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (.decCall (ofString "w") (.comb [.one, .one]) (ofString "htab_get") args
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
        (.return (.rstruct [
          .load .one (.rfield 1 (.var .local (ofString "w"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) tail))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  have hvals : values = [.val (.word db), .val (.word hash)] := by
    rw [hargs] at ha; exact Option.some.inj ha.symm
  subst values
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hcode]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := WkBal.htabWF_with_locals s callee (s.clock - 1) db.toNat |>.2 hW
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values ce db hash hcode ht hk hWce v
    (congrArg Prod.fst hb)
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good (sourceFnBody Guest.Software.guestFn_htab_get)
    (by decide) ce hcode
  rw [hb] at hframe
  have hpost : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, ce, callEntryStateHOLFinite] using hframe
  subst v
  let st := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found), .val (.word ptr)]) {post with locals := s.locals}
  have hst : st = {s with locals := st.locals, clock := st.clock} := by
    dsimp only [st, setVarHOLFinite]; rw [hpost]
  have hr : st.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found), .val (.word ptr)]) := by
    simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hAst : ArenaReady st := by rw [hst]; exact localsFree_arenaReady s _ _ hA
  have hrecord : found ≠ 0 → WordsOK st (ptr.toNat, 16) ∧
      Inside (memW st ptr.toNat, memW st (ptr.toNat + 8)) sourceBase (globN st "heap_ptr") := by
    intro hf
    have hin : ptr.toNat ∈ htabValues s db.toNat := by
      simpa [ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW] using hm hf
    have he := hentries ptr.toNat hin
    rw [hst]
    simpa [WordsOK, WordAt, memW, globN] using he
  intro w hw
  apply get_code_cache_branch_return st hAst found ptr tail hr hrecord ?_ w hw
  intro hz
  subst found
  exact hmiss _ _ _ _ post ptr ha hl hb

/-- The final world-state fallback of `get_code` forwards the bounded pair
from the concrete installed `ws_get_code` call. -/
theorem get_code_ws_fallback_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hentry : ∀ values body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash")] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "ws_get_code") values = some (body, callee, ret) →
      WsCodeLookupStrong (callEntryStateHOLFinite s callee)) :
    Ret s (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
      [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  obtain ⟨code, code_n, hv, hn⟩ := ws_get_code_call_return_entry_strong s body callee ret
    values v post hcode hshape (hentry values body callee ret ha hl) hl hb
  subst v
  have hc : (setVarHOLFinite (ofString "c")
      (.rStruct [.val (.word code), .val (.word code_n)]) {post with locals := s.locals}).locals.lookup
      (ofString "c") = some (.rStruct [.val (.word code), .val (.word code_n)]) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  intro w hw
  obtain ⟨hv, hn, _⟩ := ext_code_of_tail_return _ code code_n hc hn w hw
  exact ⟨code, code_n, hv, hn⟩

/-- Returning assignment calls expose the actual resumed caller state. This
handles the second cache lookup, which reuses `w` rather than declaring it. -/
theorem Ret.seq_callAssign_gen {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hk : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      Ret (setVarHOLFinite x v {post with locals := s.locals}) cont Φ) :
    Ret s (.seq (.call (some (some (.local, x), none)) fname args) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (callAssign_noRet s x fname args v hv)) ?_
  intro t ht
  obtain ⟨values, body, callee, ret, v, post, ha, hl, hb, hr⟩ := callAssign_inv ht
  rw [hr]
  exact hk values body callee ret v post ha hl hb

/-- Cache lookup returns a genuine live payload and preserves nonlocal state. -/
theorem get_code_cache_call_resume_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hW : HtabWF s db.toNat)
    (hentries : NodeDbEntriesStrong s db.toNat)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get")
      [.val (.word db), .val (.word hash)] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post = {s with locals := post.locals, clock := post.clock} ∧
      ∃ found ptr : BitVec 64, v = .rStruct [.val (.word found), .val (.word ptr)] ∧
        (found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧
          Inside (memW s ptr.toNat, memW s (ptr.toNat + 8)) sourceBase (globN s "heap_ptr")) := by
  obtain ⟨hbody, ht⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [] (ofString "t") .one [(ofString "key", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by intro p hp; simp at hp; rw [hp]; decide)
    (by rw [hcode]; exact WkBal.lookup_htab_get) (vpre := []) (by simp) hl
  obtain ⟨_, hk⟩ := lookupCodeHOLFinite_param_at
    s.code.lookup (ofString "htab_get") [(ofString "t", .one)] (ofString "key") .one []
    (sourceFnBody Guest.Software.guestFn_htab_get) (.comb [.one, .one])
    (by simp) (by rw [hcode]; exact WkBal.lookup_htab_get)
    (vpre := [.val (.word db)]) (by simp) hl
  subst body
  let ce := callEntryStateHOLFinite s callee
  have hWce : HtabWF ce db.toNat := WkBal.htabWF_with_locals s callee (s.clock - 1) db.toNat |>.2 hW
  obtain ⟨found, ptr, hv, hm⟩ := WkBal.htab_get_ret_in_values ce db hash hcode ht hk hWce v
    (congrArg Prod.fst hb)
  have hframe := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good (sourceFnBody Guest.Software.guestFn_htab_get)
    (by decide) ce hcode
  rw [hb] at hframe
  refine ⟨?_, found, ptr, hv, fun hf => ?_⟩
  · simpa [R16WkAcctWs.LocFrameR16, ce, callEntryStateHOLFinite] using hframe
  · apply hentries ptr.toNat
    simpa [ce, callEntryStateHOLFinite, htabValues, hdr, nodeF, memW] using hm hf

/-- The second cache uses an assignment call; its hit/miss contract is the
same bounded record contract as the first cache's declaration call. -/
theorem get_code_cache_assign_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (args : List (ExpHOL 64)) (tail : ProgHOL 64)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args =
      some [.val (.word db), .val (.word hash)])
    (hW : HtabWF s db.toNat) (hentries : NodeDbEntriesStrong s db.toNat)
    (hmiss : ∀ values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      Ret (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := s.locals}) tail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (.seq (.call (some (some (.local, ofString "w"), none)) (ofString "htab_get") args)
      (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
        (.return (.rstruct [
          .load .one (.rfield 1 (.var .local (ofString "w"))),
          .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) tail))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.seq_callAssign_gen
  intro values body callee ret v post ha hl hb
  have hvals : values = [.val (.word db), .val (.word hash)] := by
    rw [hargs] at ha; exact Option.some.inj ha.symm
  subst values
  obtain ⟨hpost, found, ptr, hv, hrecord⟩ :=
    get_code_cache_call_resume_strong s db hash body callee ret v post hcode hW hentries hl hb
  subst v
  let st := setVarHOLFinite (ofString "w")
    (.rStruct [.val (.word found), .val (.word ptr)]) {post with locals := s.locals}
  have hst : st = {s with locals := st.locals, clock := st.clock} := by
    dsimp only [st, setVarHOLFinite]; rw [hpost]
  apply get_code_cache_branch_return st
    (by rw [hst]; exact localsFree_arenaReady s _ _ hA) found ptr tail
    (by simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  · intro hf
    rw [hst]
    simpa [WordsOK, WordAt, memW, globN] using hrecord hf
  · intro hz
    subst found
    exact hmiss _ _ _ _ post ptr ha hl hb

/-- Cache-miss access recording followed by the world-state code fallback. -/
def getCodeAccessTail : ProgHOL 64 :=
  .decCall (ofString "k") .one (ofString "sk_make")
    [.var .local (ofString "addr"), .var .local (ofString "code_hash")]
    (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]),
        .var .local (ofString "k"), .const 1])
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c")))))

/-- Access-recording composition exposes the exact strong lookup entry fact
needed after the mutating table call, without assuming its preservation. -/
theorem get_code_access_tail_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hentry : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "addr"), .var .local (ofString "code_hash")] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "sk_make") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      ∀ values' body' callee' ret' v' post',
      let st := setVarHOLFinite (ofString "k") v {post with locals := s.locals}
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ts"), .const 40]),
          .var .local (ofString "k"), .const 1] = some values' →
      lookupCodeHOLFinite st.code.lookup (ofString "htab_set") values' = some (body', callee', ret') →
      evaluateHOLFiniteState (callEntryStateHOLFinite st callee') body' = (some (.returned v'), post') →
      let resumed := {post' with locals := st.locals}
      resumed.code = originalRuntimeCode ∧
      resumed.eshapes.lookup (ofString "StateErr") = some .one ∧
      ∀ vals b cl r,
        evalListHOLFinite resumed (h := fun a => Classical.propDecidable (resumed.memaddrs a))
          [.var .local (ofString "code_hash")] = some vals →
        lookupCodeHOLFinite resumed.code.lookup (ofString "ws_get_code") vals = some (b, cl, r) →
        WsCodeLookupStrong (callEntryStateHOLFinite resumed cl)) :
    Ret s getCodeAccessTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  unfold getCodeAccessTail
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  apply Ret.seq_call00
  intro values' body' callee' ret' v' post' ha' hl' hb'
  obtain ⟨hc, hs, he⟩ := hentry values body callee ret v post ha hl hb
    values' body' callee' ret' v' post' ha' hl' hb'
  exact get_code_ws_fallback_return_strong _ hc hs he

/-- The two code caches share their lookup arguments and hit branch. -/
def getCodeCacheArgs (owner : String) : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .global (ofString owner), .const 48]),
    .var .local (ofString "code_hash")]

def getCodeCacheBranch (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
    (.return (.rstruct [.load .one (.rfield 1 (.var .local (ofString "w"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) tail

def getCodeCacheTail : ProgHOL 64 :=
  .decCall (ofString "w") (.comb [.one, .one]) (ofString "htab_get") (getCodeCacheArgs "ts")
    (getCodeCacheBranch (.seq
      (.call (some (some (.local, ofString "w"), none)) (ofString "htab_get") (getCodeCacheArgs "bs"))
      (getCodeCacheBranch getCodeAccessTail)))

/-- Typed cache arguments and live bounded payloads at a lookup entry. -/
def CodeCacheLookupStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (owner : String) : Prop :=
  ArenaReady s ∧ ∃ db hash : BitVec 64,
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (getCodeCacheArgs owner) =
      some [.val (.word db), .val (.word hash)] ∧
    HtabWF s db.toNat ∧ NodeDbEntriesStrong s db.toNat

/-- Compose both concrete caches; only two actual misses reach access recording. -/
theorem get_code_cache_tail_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hfirst : CodeCacheLookupStrong s "ts")
    (hsecond : ∀ values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) (getCodeCacheArgs "ts") = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      CodeCacheLookupStrong
        (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
          {post with locals := s.locals}) "bs")
    (hfallback : ∀ (st : PanSemStateFiniteExact 64 F) values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a)) (getCodeCacheArgs "bs") = some values →
      lookupCodeHOLFinite st.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      Ret (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := st.locals}) getCodeAccessTail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s getCodeCacheTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  obtain ⟨hA, db, hash, ha, hW, he⟩ := hfirst
  apply get_code_cache_lookup_return_strong s db hash _ _ hcode hA ha hW he
  intro values body callee ret post ptr ha hl hb
  obtain ⟨hA', db', hash', ha', hW', he'⟩ := hsecond values body callee ret post ptr ha hl hb
  have hc := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).1
  rw [hb] at hc
  apply get_code_cache_assign_return_strong
    (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
      {post with locals := s.locals}) db' hash' _ _ (hc.trans hcode) hA' ha' hW' he'
  exact hfallback _

theorem get_code_body_eq :
    sourceFnBody Guest.Software.guestFn_get_code =
      .decCall (ofString "eq") .one (ofString "memeq")
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
          (.return (.rstruct [.const 0, .const 0])) .skip) getCodeCacheTail) := by rfl

/-- Full `get_code` return composition. The empty-hash branch needs no cache
invariant; the cache contract is required only after a zero comparison. -/
theorem get_code_return_of_cache_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcache : ∀ values body callee ret post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word 0))), post) →
      Ret (setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals})
        getCodeCacheTail (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (sourceFnBody Guest.Software.guestFn_get_code)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  rw [get_code_body_eq]
  apply ws_get_code_compare_return_of_tail
  intro values body callee ret eqw post ha hl hb hz
  subst eqw
  exact hcache values body callee ret post ha hl hb

/-- Cache-tail obligation at the actual zero-comparison continuation. -/
def GetCodeCacheContinuationStrong {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ values body callee ret post,
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "code_hash"), .var .global (ofString "empty_code_hash"), .const 32] = some values →
    lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret) →
    evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned (.val (.word 0))), post) →
    Ret (setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals})
      getCodeCacheTail (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)

/-- Lift the full hash/cache proof through the installed `get_code` call. -/
theorem get_code_call_return_of_cache_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hentry : GetCodeCacheContinuationStrong (callEntryStateHOLFinite s callee))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_code") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40 := by
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "get_code")
    _ _ body _ ret values callee (by rw [hc]; exact R16WkAcctWs.lookup_get_code) hl
  subst body
  exact get_code_return_of_cache_tail (callEntryStateHOLFinite s callee) hentry v
    (congrArg Prod.fst hb)

/-- The concrete external-code suffix forwards the bounded `get_code` result. -/
theorem ext_code_of_get_code_return_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hentry : ∀ values body callee ret,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "a"), .const 48]),
          .var .local (ofString "addr")] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "get_code") values = some (body, callee, ret) →
      GetCodeCacheContinuationStrong (callEntryStateHOLFinite s callee)) :
    Ret s (.decCall (ofString "c") (.comb [.one, .one]) (ofString "get_code")
      [.load .one (.op .add [.var .local (ofString "a"), .const 48]),
        .var .local (ofString "addr")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  obtain ⟨code, code_n, hv, hn⟩ := get_code_call_return_of_cache_tail s values body callee ret
    v post hc (hentry values body callee ret ha hl) hl hb
  subst v
  have hlocal : (setVarHOLFinite (ofString "c")
      (.rStruct [.val (.word code), .val (.word code_n)]) {post with locals := s.locals}).locals.lookup
      (ofString "c") = some (.rStruct [.val (.word code), .val (.word code_n)]) := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  intro w hw
  obtain ⟨hv, hn, _⟩ := ext_code_of_tail_return _ code code_n hlocal hn w hw
  exact ⟨code, code_n, hv, hn⟩

/-- Lift bounded code retrieval through the concrete account lookup wrapper.
The entry obligation is checked after the actual account call resumes. -/
theorem ext_code_of_return_of_cache_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hentry : ∀ values body callee ret v post,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "addr")] = some values →
      lookupCodeHOLFinite s.code.lookup (ofString "get_account") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post) →
      ∀ vals b cl r,
      let st := setVarHOLFinite (ofString "a") v {post with locals := s.locals}
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        [.load .one (.op .add [.var .local (ofString "a"), .const 48]),
          .var .local (ofString "addr")] = some vals →
      lookupCodeHOLFinite st.code.lookup (ofString "get_code") vals = some (b, cl, r) →
      GetCodeCacheContinuationStrong (callEntryStateHOLFinite st cl)) :
    Ret s (sourceFnBody Guest.Software.guestFn_ext_code_of)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  change Ret s (.decCall (ofString "a") .one (ofString "get_account")
    [.var .local (ofString "addr")]
    (.decCall (ofString "c") (.comb [.one, .one]) (ofString "get_code")
      [.load .one (.op .add [.var .local (ofString "a"), .const 48]),
        .var .local (ofString "addr")] (.return (.var .local (ofString "c"))))) _
  apply Ret.decCall_gen
  intro values body callee ret v post ha hl hb
  have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).1
  rw [hb] at hm
  exact ext_code_of_get_code_return_strong _ (hm.trans hc)
    (hentry values body callee ret v post ha hl hb)

/-- Rebinding the cache result cannot change the other cache's typed entry. -/
theorem codeCacheLookupStrong_set_w {F : Type} (s : PanSemStateFiniteExact 64 F)
    (owner : String) (value : ValueHOL 64) (clock : Nat)
    (h : CodeCacheLookupStrong s owner) :
    CodeCacheLookupStrong (setVarHOLFinite (ofString "w") value {s with clock := clock}) owner := by
  obtain ⟨hA, db, hash, ha, hW, he⟩ := h
  refine ⟨localsFree_arenaReady s _ _ hA, db, hash, ?_, ?_, ?_⟩
  · have heval : evalListHOLFinite
        (setVarHOLFinite (ofString "w") value {s with clock := clock})
        (h := fun a => Classical.propDecidable (_)) (getCodeCacheArgs owner) =
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          (getCodeCacheArgs owner) := by
      simp (config := {decide := true}) only [getCodeCacheArgs, evalListHOLFinite,
        evalListHOLExact, evalHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
      rfl
    exact heval.trans ha
  · exact (WkBal.htabWF_with_locals s _ _ _).2 hW
  · simpa [NodeDbEntriesStrong, htabValues, hdr, nodeF, memW, WordsOK, WordAt,
      globN, setVarHOLFinite] using he

/-- A genuine first-cache miss preserves the second cache entry invariant. -/
theorem get_code_second_cache_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (post : PanSemStateFiniteExact 64 F) (ptr : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hsecond : CodeCacheLookupStrong s "bs")
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_get") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post)) :
    CodeCacheLookupStrong
      (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := s.locals}) "bs" := by
  have hl' := hl
  rw [hc] at hl'
  have hf := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good body
    (R16WkAcctWs.wsGetCodeCallees_good _ (by decide) values body callee ret hl')
    (callEntryStateHOLFinite s callee) hc
  rw [hb] at hf
  have hp : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, callEntryStateHOLFinite] using hf
  rw [hp]
  exact codeCacheLookupStrong_set_w s "bs" _ post.clock hsecond

/-- Both cache invariants may be supplied at entry: the first lookup's
read-only contract discharges preservation of the second lookup entry. -/
theorem get_code_cache_tail_return_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hfirst : CodeCacheLookupStrong s "ts") (hsecond : CodeCacheLookupStrong s "bs")
    (hfallback : ∀ (st : PanSemStateFiniteExact 64 F) values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        (getCodeCacheArgs "bs") = some values →
      lookupCodeHOLFinite st.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      Ret (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := st.locals}) getCodeAccessTail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s getCodeCacheTail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply get_code_cache_tail_return_strong s hc hfirst ?_ hfallback
  intro values body callee ret post ptr _ha hl hb
  exact get_code_second_cache_entry_strong s values body callee ret post ptr hc hsecond hl hb

/-- The initial hash comparison only binds `eq`, leaving cache entry facts intact. -/
theorem codeCacheLookupStrong_set_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (owner : String) (value : ValueHOL 64) (clock : Nat)
    (h : CodeCacheLookupStrong s owner) :
    CodeCacheLookupStrong (setVarHOLFinite (ofString "eq") value {s with clock := clock}) owner := by
  obtain ⟨hA, db, hash, ha, hW, he⟩ := h
  refine ⟨localsFree_arenaReady s _ _ hA, db, hash, ?_, ?_, ?_⟩
  · have heval : evalListHOLFinite
        (setVarHOLFinite (ofString "eq") value {s with clock := clock})
        (h := fun a => Classical.propDecidable (_)) (getCodeCacheArgs owner) =
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          (getCodeCacheArgs owner) := by
      simp (config := {decide := true}) only [getCodeCacheArgs, evalListHOLFinite,
        evalListHOLExact, evalHOLExact, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE]
      rfl
    exact heval.trans ha
  · exact (WkBal.htabWF_with_locals s _ _ _).2 hW
  · simpa [NodeDbEntriesStrong, htabValues, hdr, nodeF, memW, WordsOK, WordAt,
      globN, setVarHOLFinite] using he

theorem get_code_cache_entry_after_compare {F : Type} (s : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (post : PanSemStateFiniteExact 64 F) (owner : String)
    (hc : s.code = originalRuntimeCode) (hcache : CodeCacheLookupStrong s owner)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memeq") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned (.val (.word 0))), post)) :
    CodeCacheLookupStrong
      (setVarHOLFinite (ofString "eq") (.val (.word 0)) {post with locals := s.locals}) owner := by
  have hl' := hl
  rw [hc] at hl'
  have hf := R16WkAcctWs.evaluate_roProgR16 R16WkAcctWs.wsGetCodeCallees
    R16WkAcctWs.wsGetCodeCallees_good body
    (R16WkAcctWs.wsGetCodeCallees_good _ (by decide) values body callee ret hl')
    (callEntryStateHOLFinite s callee) hc
  rw [hb] at hf
  have hp : post = {s with locals := post.locals, clock := post.clock} := by
    simpa [R16WkAcctWs.LocFrameR16, callEntryStateHOLFinite] using hf
  rw [hp]
  exact codeCacheLookupStrong_set_eq s owner _ post.clock hcache

/-- Both cache entry facts survive the hash comparison and suffice for the
complete bounded return proof, with the access-recording fallback exposed. -/
theorem get_code_return_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode)
    (hfirst : CodeCacheLookupStrong s "ts") (hsecond : CodeCacheLookupStrong s "bs")
    (hfallback : ∀ (st : PanSemStateFiniteExact 64 F) values body callee ret post (ptr : BitVec 64),
      evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
        (getCodeCacheArgs "bs") = some values →
      lookupCodeHOLFinite st.code.lookup (ofString "htab_get") values = some (body, callee, ret) →
      evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body =
        (some (.returned (.rStruct [.val (.word 0), .val (.word ptr)])), post) →
      Ret (setVarHOLFinite (ofString "w") (.rStruct [.val (.word 0), .val (.word ptr)])
        {post with locals := st.locals}) getCodeAccessTail
        (fun v _ => ∃ code code_n : BitVec 64,
          v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (sourceFnBody Guest.Software.guestFn_get_code) (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply get_code_return_of_cache_tail s
  intro values body callee ret post _ha hl hb
  have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).1
  rw [hb] at hm
  exact get_code_cache_tail_return_entry_strong _ (hm.trans hc)
    (get_code_cache_entry_after_compare s values body callee ret post "ts" hc hfirst hl hb)
    (get_code_cache_entry_after_compare s values body callee ret post "bs" hc hsecond hl hb)
    hfallback

/-- Payload typing survives heap growth when table values and payload words
are preserved; no preservation of unrelated memory is required. -/
theorem nodeDbEntriesStrong_of_preserved_payloads {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {db : Nat}
    (he : NodeDbEntriesStrong s db)
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hvalues : htabValues post db = htabValues s db)
    (hwords : ∀ p ∈ htabValues s db,
      memW post p = memW s p ∧ memW post (p + 8) = memW s (p + 8)) :
    NodeDbEntriesStrong post db := by
  intro p hp
  rw [hvalues] at hp
  obtain ⟨hw, hin⟩ := he p hp
  refine ⟨wordsOK_transfer hAs.1 hAp.1 hw, ?_⟩
  rw [(hwords p hp).1, (hwords p hp).2]
  exact ⟨hin.1, le_trans hin.2 hhp⟩

/-- Transport the actual cache lookup arguments along with its table and
payload facts, retaining the concrete database and hash witnesses. -/
theorem codeCacheLookupStrong_of_preserved_payloads {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (owner : String)
    (he : CodeCacheLookupStrong s owner) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hargs : evalListHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      (getCodeCacheArgs owner) =
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (getCodeCacheArgs owner))
    (hwf : ∀ db, HtabWF s db → HtabWF post db)
    (hvalues : ∀ db, HtabWF s db → htabValues post db = htabValues s db)
    (hwords : ∀ db, HtabWF s db → ∀ p ∈ htabValues s db,
      memW post p = memW s p ∧ memW post (p + 8) = memW s (p + 8)) :
    CodeCacheLookupStrong post owner := by
  obtain ⟨hAs, db, hash, ha, hW, he⟩ := he
  exact ⟨hAp, db, hash, hargs.trans ha, hwf _ hW,
    nodeDbEntriesStrong_of_preserved_payloads he hAs hAp hhp (hvalues _ hW) (hwords _ hW)⟩

/-- Concrete fallback entry words discharge the installed callee-entry
obligation; the call only replaces locals and decrements the clock. -/
theorem get_code_ws_fallback_return_entry_strong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db hash : BitVec 64) (hc : s.code = originalRuntimeCode)
    (hs : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hA : ArenaReady s)
    (hdb : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hh : s.locals.lookup (ofString "code_hash") = some (.val (.word hash)))
    (hW : HtabWF s db.toNat) (he : NodeDbEntriesStrong s db.toNat) :
    Ret s (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
      [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply get_code_ws_fallback_return_strong s hc hs
  intro values body callee ret ha hl
  have hv : values = [.val (.word hash)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact, hh] using ha.symm
  subst values
  obtain ⟨_, hhash⟩ := lookupCodeHOLFinite_param_at s.code.lookup (ofString "ws_get_code")
    [] (ofString "code_hash") .one [] _ (.comb [.one, .one])
    (by simp) (by rw [hc]; exact lookup_ws_get_code_local)
    (vpre := []) (by simp) hl
  apply wsCodeLookupStrong_of_words (callEntryStateHOLFinite s callee) db hash
    (localsFree_arenaReady s _ _ hA) ?_ hhash
    ((WkBal.htabWF_with_locals s _ _ _).2 hW) ?_
  · rw [evalHOLFinite_eq_toExact] at hdb ⊢
    exact hdb
  · simpa [NodeDbEntriesStrong, callEntryStateHOLFinite, htabValues, hdr, nodeF,
      memW, WordsOK, WordAt, globN] using he

/-- The concrete key-building call preserves both code-record words when
the record is separated from its 52-byte global scratch buffer. -/
theorem sk_make_preserves_code_record {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (p : Nat) (hp : p + 16 ≤ 2 ^ 64)
    (hd : Disj (p, 16) (globN s "sk_buf", 52))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post)) :
    memW post p = memW s p ∧ memW post (p + 8) = memW s (p + 8) := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hword : ∀ off, off = 0 ∨ off = 8 →
      memW post (p + off) = memW s (p + off) := by
    intro off hoff
    unfold memW
    rw [heff.cell_frame _ ?_]
    intro i hi _ hhit
    simp only [List.mem_singleton] at hi
    subst i
    have hnat : (BitVec.ofNat 64 (p + off)).toNat = p + off :=
      Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl <;> omega)
    rw [hnat] at hhit
    change globN s "sk_buf" < p + off + 8 ∧ p + off < globN s "sk_buf" + 52 at hhit
    rcases hd with hd | hd | hd | hd <;> dsimp only at hd <;>
      rcases hoff with rfl | rfl <;> omega
  exact ⟨by simpa using hword 0 (Or.inl rfl), hword 8 (Or.inr rfl)⟩

/-- A table mutation's concrete write frame preserves an old code record
separated from the table footprint. Its two cells precede the fresh heap. -/
theorem htab_frame_preserves_code_record {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (t p : Nat)
    (hp : p + 16 ≤ globN s "heap_ptr") (hp64 : p + 16 ≤ 2 ^ 64)
    (hpos : ∀ i ∈ htabFootprint s t, 0 < i.2)
    (hd : ∀ i ∈ htabFootprint s t, Disj (p, 16) i)
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr")) :
    memW post p = memW s p ∧ memW post (p + 8) = memW s (p + 8) := by
  have hword : ∀ off, off = 0 ∨ off = 8 →
      memW post (p + off) = memW s (p + off) := by
    intro off hoff
    have hnat : (BitVec.ofNat 64 (p + off)).toNat = p + off :=
      Nat.mod_eq_of_lt (by rcases hoff with rfl | rfl <;> omega)
    unfold memW
    rw [hfr _ ?_ ?_]
    · intro i hi hhit
      rw [hnat] at hhit
      have hdisj := hd i hi
      have hipos := hpos i hi
      rcases hdisj with h | h | h | h <;> try dsimp only at h
      all_goals
        unfold CellHits at hhit
        rcases hoff with rfl | rfl <;> omega
    · rw [hnat]
      unfold CellHits
      dsimp only
      rcases hoff with rfl | rfl <;> omega
  exact ⟨by simpa using hword 0 (Or.inl rfl), hword 8 (Or.inr rfl)⟩

/-- Payload typing survives a concrete table-mutator exit when the database
values are unchanged and their records belong to separated old heap. -/
theorem nodeDbEntriesStrong_of_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db : Nat)
    (he : NodeDbEntriesStrong s db) (hAs : ArenaReady s)
    (hx : HtabExit s post)
    (hvalues : htabValues post db = htabValues s db)
    (hrec : ∀ p ∈ htabValues s db,
      p + 16 ≤ globN s "heap_ptr" ∧ p + 16 ≤ 2 ^ 64 ∧
      ∀ i ∈ htabFootprint s (locN s "t"), Disj (p, 16) i)
    (hpos : ∀ i ∈ htabFootprint s (locN s "t"), 0 < i.2) :
    NodeDbEntriesStrong post db := by
  obtain ⟨hAp, _, _, _, hhp, _, hfr, _⟩ := hx
  apply nodeDbEntriesStrong_of_preserved_payloads he hAs hAp hhp hvalues
  intro p hp
  obtain ⟨hb, hb64, hd⟩ := hrec p hp
  exact htab_frame_preserves_code_record (locN s "t") p hb hb64 hpos hd hfr

/-- The concrete key-builder preserves database payload typing for separated
records, using its actual two-cell frame rather than a whole-memory premise. -/
theorem nodeDbEntriesStrong_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db : Nat)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (he : NodeDbEntriesStrong s db) (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hvalues : htabValues post db = htabValues s db)
    (hrec : ∀ p ∈ htabValues s db, p + 16 ≤ 2 ^ 64 ∧
      Disj (p, 16) (globN s "sk_buf", 52)) :
    NodeDbEntriesStrong post db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hhp : globN s "heap_ptr" = globN post "heap_ptr" := by
    unfold globN
    rw [heff.globals]
  apply nodeDbEntriesStrong_of_preserved_payloads he hAs hAp (Nat.le_of_eq hhp) hvalues
  intro p hp
  obtain ⟨hp64, hd⟩ := hrec p hp
  exact sk_make_preserves_code_record s hc hma hfit p hp64 hd v post hb

/-! ## Explicit code-payload strengthening

Cutover bridge: replace `WorldTyped s S` by `WorldTypedCodeStrong s S` in the
world conjunct shared by `WorldOK` and `EvmInvAt` in `ContractParts/C00.lean`.
The additional conjunct describes record contents and separation, not execution
or the desired postcondition. Existing world consumers use its first projection.
-/

/-- Code payload records occupy protected old heap; their code bytes are
bounded by `NodeDbEntriesStrong`. Table values themselves remain unrestricted. -/
def CodeDbPayloadStrong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (db : Nat) : Prop :=
  NodeDbEntriesStrong s db ∧ ∀ p ∈ htabValues s db,
    Inside (p, 16) sourceBase (globN s "heap_ptr") ∧ p + 16 ≤ 2 ^ 64 ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (p, 16) i) ∧
    ∀ i ∈ fixedObjects s, Disj (p, 16) i

/-- Only the three code databases gain payload typing: the witness database
at `ws+16` and the block/transaction code caches at `bs+48` and `ts+48`. -/
def WorldTypedCodeStrong {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) : Prop :=
  WorldTyped s S ∧
  ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
    globN s g ≠ 0 → CodeDbPayloadStrong s S (memW s (globN s g + k))

def WorldOKCodeStrong {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧ ∃ S, WorldTypedCodeStrong s S

theorem worldOK_of_codeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WorldOKCodeStrong s) : WorldOK s := by
  obtain ⟨hA, S, hW, _⟩ := h
  exact ⟨hA, S, hW⟩

/-- The strengthened entry invariant supplies all payload-side premises of
the mutating-table transport lemma. -/
theorem codeDbPayloadStrong_entries_of_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadStrong s S db) (hAs : ArenaReady s)
    (hx : HtabExit s post) (ht : locN s "t" ∈ S)
    (hw : HtabWF s (locN s "t"))
    (hv : htabValues post db = htabValues s db) : NodeDbEntriesStrong post db := by
  apply nodeDbEntriesStrong_of_htab_exit db h.1 hAs hx hv
  · intro p hp
    obtain ⟨hin, hp64, hd, _⟩ := h.2 p hp
    exact ⟨hin.2, hp64, hd _ ht⟩
  · exact htabFootprint_pos s _ hw.2.2.1 hw.2.2.2.2.1

/-- Fixed-object separation in the strong invariant discharges the key
builder's payload-separation premise, including its shorter 52-byte write. -/
theorem codeDbPayloadStrong_entries_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hvalues : htabValues post db = htabValues s db) : NodeDbEntriesStrong post db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hnz, _⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  apply nodeDbEntriesStrong_of_sk_make db hc hma hfit v hb h.1 hAs hAp hvalues
  intro p hp
  obtain ⟨_, hp64, _, hd⟩ := h.2 p hp
  refine ⟨hp64, ?_⟩
  have hmem : (globN s "sk_buf", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨("sk_buf", 64), by decide, by simp [hnz]⟩
  have hsep := hd _ hmem
  rcases hsep with h | h | h | h
  · exact (by omega)
  · exact (by omega)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- The actual key-builder write region cannot change a separated table's
live values; only aligned cells of its well-formed footprint are read. -/
theorem htabValues_eq_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db : Nat)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hw : HtabWF s db)
    (hd : ∀ i ∈ htabFootprint s db, Disj i (globN s "sk_buf", 52)) :
    htabValues post db = htabValues s db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  apply InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.htabValues_eq_of_unhit hw
  intro i hi
  right
  intro a ha hhit
  apply heff.cell_frame
  intro j hj _
  simp only [List.mem_singleton] at hj
  subst j
  have hi8 := (hw.1 i hi).2.1
  have hi28 := (hw.1 i hi).2.2.1
  intro hh
  have hs := hd i hi
  unfold CellHits at hhit hh
  rcases hs with hs | hs | hs | hs <;> try dsimp only at hs
  all_goals omega

/-- A table-mutator frame preserves another allocated table's live values.
The explicit alignment premises cover empty write regions as well. -/
theorem htabValues_eq_of_mutator_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db t : Nat)
    (hw : HtabWF s db)
    (hal : ∀ i ∈ htabFootprint s db, Allocated s i)
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hfr : FrameOutside s post (htabFootprint s t)
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    (hkal : ∀ j ∈ htabFootprint s t, j.1 % 8 = 0 ∧ j.2 % 8 = 0)
    (hfal : (globN s "heap_ptr") % 8 = 0 ∧
      (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0)
    (hd : ∀ i ∈ htabFootprint s db, ∀ j ∈ htabFootprint s t, Disj i j) :
    htabValues post db = htabValues s db := by
  apply InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.htabValues_eq_of_unhit hw
  intro i hi
  right
  exact ivlUnhit_of_frameOutside ⟨(hw.1 i hi).2.1, (hw.1 i hi).2.2.1⟩
    hfr hkal hfal (hd i hi) (disj_fresh_of_allocated hAs.2 hAp.2 hhp (hal i hi))

/-- The table-exit contract and old-world allocation discharge the frame's
alignment and fresh-heap premises without additional entry assumptions. -/
theorem htabValues_eq_of_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db : Nat)
    (hw : HtabWF s db) (ht : HtabWF s (locN s "t"))
    (hal : ∀ i ∈ htabFootprint s db, Allocated s i)
    (hAs : ArenaReady s) (hx : HtabExit s post)
    (hd : ∀ i ∈ htabFootprint s db,
      ∀ j ∈ htabFootprint s (locN s "t"), Disj i j) :
    htabValues post db = htabValues s db := by
  obtain ⟨hAp, _, _, _, hhp, _, hfr, _⟩ := hx
  apply htabValues_eq_of_mutator_frame db (locN s "t") hw hal hAs hAp hhp hfr
  · intro j hj
    exact ⟨(ht.1 j hj).2.1, (ht.1 j hj).2.2.1⟩
  · have hs := hAs.2.2.2.2.2.2.1
    have hp := hAp.2.2.2.2.2.2.1
    exact ⟨hs, by omega⟩
  · exact hd

/-- Both value preservation and payload-word preservation follow from the
same old-world table separation at the concrete mutator exit. -/
theorem codeDbPayloadStrong_entries_of_separated_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadStrong s S db) (hAs : ArenaReady s)
    (hW : WorldTyped s S) (hdb : db ∈ S) (ht : locN s "t" ∈ S)
    (hne : db ≠ locN s "t") (hx : HtabExit s post) :
    NodeDbEntriesStrong post db := by
  have hw := (hW.1.2.1 db hdb).1
  have htw := (hW.1.2.1 (locN s "t") ht).1
  have hv : htabValues post db = htabValues s db := by
    apply htabValues_eq_of_htab_exit db hw htw
    · intro i hi
      exact ((hW.1.2.1 db hdb).2 i hi).1
    · exact hAs
    · exact hx
    · exact hW.1.2.2.1 db hdb (locN s "t") ht hne
  exact codeDbPayloadStrong_entries_of_htab_exit db h hAs hx ht htw hv

/-- The fallback's witness database and accessed-code table have different
key lengths, so even the raw typed world already rules out their aliasing. -/
theorem fallback_code_roots_distinct {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (hW : WorldTyped s S)
    (hws : globN s "ws" ≠ 0) (hts : globN s "ts" ≠ 0)
    (hdb : memW s (globN s "ws" + 16) ≠ 0)
    (ht : memW s (globN s "ts" + 40) ≠ 0) :
    memW s (globN s "ws" + 16) ∈ S ∧
    memW s (globN s "ts" + 40) ∈ S ∧
    memW s (globN s "ws" + 16) ≠ memW s (globN s "ts" + 40) := by
  have hmdb : (memW s (globN s "ws" + 16), "ws+16") ∈ worldRoleSlots s := by
    simp [worldRoleSlots, recRoles, hws, hdb]
  have hmt : (memW s (globN s "ts" + 40), "ts+40") ∈ worldRoleSlots s := by
    simp [worldRoleSlots, recRoles, hts, ht]
  have hr := hW.1.2.2.2.2.2.2.2.2.2.2.2
  have hd := hr.1 _ (List.mem_append_left _ hmdb)
  have ht' := hr.1 _ (List.mem_append_left _ hmt)
  refine ⟨hd.1, ht'.1, ?_⟩
  intro heq
  have hdlen : hdr s (memW s (globN s "ws" + 16)) 0 = 32 := hd.2
  have htlen : hdr s (memW s (globN s "ts" + 40)) 0 = 52 := ht'.2
  rw [heq] at hdlen
  omega

/-- Instantiation for the fallback's actual `ts+40` access table and
`ws+16` witness-code database. -/
theorem fallback_witness_entries_after_access_set {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hW : WorldTypedCodeStrong s S) (hAs : ArenaReady s)
    (hws : globN s "ws" ≠ 0) (hts : globN s "ts" ≠ 0)
    (hdb : memW s (globN s "ws" + 16) ≠ 0)
    (ht : memW s (globN s "ts" + 40) ≠ 0)
    (hlocal : locN s "t" = memW s (globN s "ts" + 40))
    (hx : HtabExit s post) :
    NodeDbEntriesStrong post (memW s (globN s "ws" + 16)) := by
  obtain ⟨hmdb, hmt, hne⟩ := fallback_code_roots_distinct s S hW.1 hws hts hdb ht
  apply codeDbPayloadStrong_entries_of_separated_htab_exit _
    (hW.2 "ws" 16 (by simp) hws) hAs hW.1 hmdb
  · rw [hlocal]; exact hmt
  · rw [hlocal]; exact hne
  · exact hx

/-- An update preserves well-formedness of every distinct typed world table. -/
theorem htabWF_of_separated_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (hdb : db ∈ S) (ht : locN s "t" ∈ S)
    (hne : db ≠ locN s "t") (hx : HtabExit s post) : HtabWF post db := by
  have hw := (hW.1.2.1 db hdb).1
  have htw := (hW.1.2.1 (locN s "t") ht).1
  apply InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.htabWF_congr_unhit
    hAs.1 hx.1.1 hw
  intro i hi
  right
  apply ivlUnhit_of_frameOutside ⟨(hw.1 i hi).2.1, (hw.1 i hi).2.2.1⟩ hx.2.2.2.2.2.2.1
  · intro j hj
    exact ⟨(htw.1 j hj).2.1, (htw.1 j hj).2.2.1⟩
  · have hs := hAs.2.2.2.2.2.2.1
    have hp := hx.1.2.2.2.2.2.2.1
    exact ⟨hs, by omega⟩
  · exact hW.1.2.2.1 db hdb (locN s "t") ht hne i hi
  · exact disj_fresh_of_allocated hAs.2 hx.1.2 hx.2.2.2.2.1
      (((hW.1.2.1 db hdb).2 i hi).1)

/-- The actual access-table exit supplies the witness payload fact for the
resumed `ws_get_code` continuation; caller locals may be restored freely. -/
theorem fallback_ws_return_after_access_set {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hW : WorldTypedCodeStrong s S) (hAs : ArenaReady s)
    (hws : globN s "ws" ≠ 0) (hts : globN s "ts" ≠ 0)
    (hdb : memW s (globN s "ws" + 16) ≠ 0)
    (ht : memW s (globN s "ts" + 40) ≠ 0)
    (hlocal : locN s "t" = memW s (globN s "ts" + 40))
    (hx : HtabExit s post)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (db hash : BitVec 64)
    (hdbnat : db.toNat = memW s (globN s "ws" + 16))
    (hc : post.code = originalRuntimeCode)
    (hs : post.eshapes.lookup (ofString "StateErr") = some .one)
    (heval : evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hh : locals.lookup (ofString "code_hash") = some (.val (.word hash))) :
    Ret {post with locals := locals}
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  have he := fallback_witness_entries_after_access_set hW hAs hws hts hdb ht hlocal hx
  obtain ⟨hmdb, hmt, hne⟩ := fallback_code_roots_distinct s S hW.1 hws hts hdb ht
  have hw : HtabWF post db.toNat := by
    rw [hdbnat]
    apply htabWF_of_separated_htab_exit _ hAs hW.1 hmdb
    · rw [hlocal]; exact hmt
    · rw [hlocal]; exact hne
    · exact hx
  rw [← hdbnat] at he
  apply get_code_ws_fallback_return_entry_strong {post with locals := locals} db hash hc hs
    (localsFree_arenaReady post locals post.clock hx.1)
  · rw [evalHOLFinite_eq_toExact] at heval ⊢
    exact heval
  · exact hh
  · exact (WkBal.htabWF_with_locals post locals post.clock db.toNat).2 hw
  · simpa [NodeDbEntriesStrong, htabValues, hdr, nodeF, memW, WordsOK, WordAt, globN] using he

/-- Transport the structural part as well as entry typing when the key
builder leaves the old table and fixed-object footprints unchanged. -/
theorem codeDbPayloadStrong_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hAs : ArenaReady s) (hAp : ArenaReady post)
    (hvalues : htabValues post db = htabValues s db)
    (hfp : ∀ t ∈ S, htabFootprint post t = htabFootprint s t)
    (hfixed : fixedObjects post = fixedObjects s) : CodeDbPayloadStrong post S db := by
  refine ⟨codeDbPayloadStrong_entries_of_sk_make db h hc hma hfit v hb hAs hAp hvalues, ?_⟩
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := by
    unfold globN
    rw [heff.globals]
  intro p hp
  rw [hvalues] at hp
  obtain ⟨hin, hp64, htables, hobjects⟩ := h.2 p hp
  refine ⟨?_, hp64, ?_, ?_⟩
  · rw [hhp]; exact hin
  · intro t ht i hi
    rw [hfp t ht] at hi
    exact htables t ht i hi
  · intro i hi
    rw [hfixed] at hi
    exact hobjects i hi

/-- The key builder preserves a table's footprint whenever its header is
separated from the concrete scratch-buffer write. -/
theorem htabFootprint_eq_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (db : Nat)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hw : HtabWF s db)
    (hd : Disj (db, 88) (globN s "sk_buf", 52)) :
    htabFootprint post db = htabFootprint s db := by
  have hhdr : (db, 88) ∈ htabFootprint s db := by simp [htabFootprint]
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hd8 := (hw.1 _ hhdr).2.1
  have h264 : heapEnd ≤ 2 ^ 64 := by decide
  apply (InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.htabFootprint_eq_of_hdr_unhit
    hd8 (by have := (hw.1 _ hhdr).1.2; dsimp only at this; omega) ?_).2
  right
  intro a ha hh
  apply heff.cell_frame
  intro j hj _ hhj
  simp only [List.mem_singleton] at hj
  subst j
  unfold CellHits at hh hhj
  rcases hd with hz | hz | hz | hz <;> try dsimp only at hz
  all_goals omega

/-- Old-world fixed-object separation discharges key-builder preservation
of every typed table's values and footprint. -/
theorem typed_tables_preserved_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hW : WorldTyped s S)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post)) :
    ∀ db ∈ S, htabValues post db = htabValues s db ∧
      htabFootprint post db = htabFootprint s db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hnz, _⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  have hmem : (globN s "sk_buf", 64) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨("sk_buf", 64), by decide, by simp [hnz]⟩
  intro db hdb
  have hw := (hW.1.2.1 db hdb).1
  have hd : ∀ i ∈ htabFootprint s db, Disj i (globN s "sk_buf", 52) := by
    intro i hi
    have hh := ((hW.1.2.1 db hdb).2 i hi).2 _ hmem
    rcases hh with hh | hh | hh | hh <;> try dsimp only at hh
    all_goals unfold Disj; omega
  exact ⟨htabValues_eq_of_sk_make db hc hma hfit v hb hw hd,
    htabFootprint_eq_of_sk_make db hc hma hfit v hb hw (hd _ (by simp [htabFootprint]))⟩

/-- Compose both mutating fallback steps for a protected database. Table
values and footprints at the intermediate state are derived from execution. -/
theorem code_entries_after_key_and_access {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {S : List Nat} (db : Nat)
    (h : CodeDbPayloadStrong s S db) (hW : WorldTyped s S)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), mid))
    (hAs : ArenaReady s) (hAm : ArenaReady mid)
    (hfixed : fixedObjects mid = fixedObjects s)
    (hWm : WorldTyped mid S) (hdb : db ∈ S)
    (ht : locN mid "t" ∈ S) (hne : db ≠ locN mid "t")
    (hx : HtabExit mid post) : NodeDbEntriesStrong post db := by
  have hp := typed_tables_preserved_of_sk_make hW hc hma hfit v hb
  have hm : CodeDbPayloadStrong mid S db :=
    codeDbPayloadStrong_of_sk_make db h hc hma hfit v hb hAs hAm
      (hp db hdb).1 (fun t ht => (hp t ht).2) hfixed
  exact codeDbPayloadStrong_entries_of_separated_htab_exit db hm hAm hWm hdb ht hne hx

/-- Key construction preserves fixed-object identities once its typed-cell
frame is established; globals are obtained from the concrete execution. -/
theorem fixedObjects_eq_of_sk_make_typed_cells {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hcells : EvmBase.SameTypedCells s post S Nd)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post)) : fixedObjects post = fixedObjects s := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hg : ∀ name, globN post name = globN s name := by
    intro name
    unfold globN
    rw [heff.globals]
  have hgb : (globalBuffers.map fun gn => (globN post gn.1, if globN post gn.1 = 0 then 0 else gn.2)) =
      (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) := by
    simp only [hg]
  unfold fixedObjects
  rw [hgb, blockOutObjects_eq hAs.2 hWT.2.2.1 hcells (hg "bo"),
    balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcells (hg "bal_accounts"),
    hg "journal", hg "journal_cap"]

/-- The concrete key-builder byte effect gives the typed-cell frame from
separation of the world-readable intervals. -/
theorem sameTypedCells_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hd : ∀ i ∈ worldTypedIvls s S Nd, Disj i (globN s "sk_buf", 52)) :
    EvmBase.SameTypedCells s post S Nd := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  refine ⟨heff.be, heff.memaddrs, hma, ?_, ?_, ?_⟩
  · intro a ha
    exact heff.out_dom a (by rwa [hma])
  · intro a ha hi
    obtain ⟨i, hi, hlo, hhi⟩ := hi
    apply heff.cell_frame
    intro j hj _ hh
    simp only [List.mem_singleton] at hj
    subst j
    have hs := hd i hi
    unfold CellHits at hh
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hh
    rcases hs with hs | hs | hs | hs <;> try dsimp only at hs
    all_goals omega
  · intro b hb hi
    obtain ⟨i, hi, hlo, hhi⟩ := hi
    apply heff.byte_frame b hb
    intro j hj hh
    simp only [List.mem_singleton] at hj
    subst j
    have hs := hd i hi
    unfold InIvl at hh
    rcases hs with hs | hs | hs | hs <;> try dsimp only at hs
    all_goals omega

/-- World typing and fixed-object identities follow from the key-builder
frame and arena readiness, with no intermediate world-typing premise. -/
theorem worldTypedWith_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hWT : WorldTypedWith s S Nd)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hd : ∀ i ∈ worldTypedIvls s S Nd, Disj i (globN s "sk_buf", 52)) :
    WorldTypedWith post S Nd ∧ fixedObjects post = fixedObjects s := by
  have hcells := sameTypedCells_of_sk_make hc hma hfit v hb hd
  have hfixed := fixedObjects_eq_of_sk_make_typed_cells hAs hWT hcells hc hma hfit v hb
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  have hg : ∀ name, globN post name = globN s name := by
    intro name
    unfold globN
    rw [heff.globals]
  have hhp : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hg]
  have hsp : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hg]
  have hFT := fixedTyped_of_eq hAp hWT.2.2.1 hhp hsp hfixed
  exact ⟨(worldTypedWith_congr_w1 hAs hAp hhp hsp (fun g _ => hg g) hcells hWT
    ⟨hFT, fun o ho => Or.inl (by rw [← hfixed]; exact ho)⟩).1, hfixed⟩

/-- Key construction preserves arena readiness directly from its byte effect. -/
theorem arenaReady_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hAs : ArenaReady s)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post)) : ArenaReady post := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, _, heff⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  rw [hb] at heff
  exact ⟨guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hAs.1,
    arenaOK_congr heff.globals hAs.2⟩

/-- The combined intermediate state needed before access-table insertion. -/
theorem world_and_payload_of_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} (db : Nat)
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hW : WorldTyped s S) (hdb : db ∈ S) (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post))
    (hd : ∀ i ∈ worldTypedIvls s S Nd, Disj i (globN s "sk_buf", 52)) :
    ArenaReady post ∧ WorldTypedWith post S Nd ∧ CodeDbPayloadStrong post S db := by
  have hAp := arenaReady_of_sk_make hAs hc hma hfit v hb
  obtain ⟨hWp, hfixed⟩ := worldTypedWith_of_sk_make hAs hAp hWT hc hma hfit v hb hd
  have hp := typed_tables_preserved_of_sk_make hW hc hma hfit v hb
  exact ⟨hAp, hWp, codeDbPayloadStrong_of_sk_make db h hc hma hfit v hb hAs hAp
    (hp db hdb).1 (fun t ht => (hp t ht).2) hfixed⟩

/-- World buffer separation discharges the last typed-cell frame premise
for the concrete key-builder execution. -/
theorem world_and_payload_after_sk_make {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} (db : Nat)
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hW : WorldTyped s S) (hdb : db ∈ S) (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), post)) :
    ArenaReady post ∧ WorldTypedWith post S Nd ∧ CodeDbPayloadStrong post S db := by
  have hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make)).1 := by
    rw [hb]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨_, _, _, hnz, _⟩ := eval_sk_make_body_evm s hc hma hfit (by rw [hb]; simp) hr
  apply world_and_payload_of_sk_make db hAs hWT hW hdb h hc hma hfit v hb
  intro i hi
  have hd := bufferRegion_disj_le hWT ("sk_buf", 64) (by decide) (by decide) 52 (by decide) i hi
  have hd' := Disj.flip hd
  simpa [bufferRegion, hnz] using hd'

/-- Strong payload typing is independent of caller locals and fuel. -/
theorem codeDbPayloadStrong_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (db : Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    CodeDbPayloadStrong {s with locals := L, clock := k} S db ↔ CodeDbPayloadStrong s S db := by
  rfl

theorem worldTypedCodeStrong_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WorldTypedCodeStrong {s with locals := L, clock := k} S ↔ WorldTypedCodeStrong s S := by
  simp only [WorldTypedCodeStrong, worldTyped_with_locals]
  rfl

/-- Both fallback mutations preserve code entries using only the original
world typing and the concrete table-exit contract. -/
theorem code_entries_after_key_and_access_world {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} (db : Nat)
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hdb : db ∈ S) (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (v : ValueHOL 64)
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_sk_make) =
      (some (.returned v), mid))
    (ht : locN mid "t" ∈ S) (hne : db ≠ locN mid "t")
    (hx : HtabExit mid post) : NodeDbEntriesStrong post db := by
  have hW : WorldTyped s S := ⟨hWT.1, hWT.2.1, hWT.2.2.1, Nd, hWT.2.2.2⟩
  obtain ⟨hAm, hWm, hm⟩ := world_and_payload_after_sk_make db hAs hWT hW hdb h hc hma hfit v hb
  have hworld : WorldTyped mid S := ⟨hWm.1, hWm.2.1, hWm.2.2.1, Nd, hWm.2.2.2⟩
  exact codeDbPayloadStrong_entries_of_separated_htab_exit db hm hAm hworld hdb ht hne hx

/-- Concrete `sk_make` lookup, callee entry, and restoration of the caller
all preserve the world and protected payload facts used by the fallback. -/
theorem world_and_payload_after_sk_call {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat} (db : Nat)
    (hAs : ArenaReady s) (hWT : WorldTypedWith s S Nd)
    (hdb : db ∈ S) (h : CodeDbPayloadStrong s S db)
    (hc : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hfit : ∀ (_ : globN s "sk_buf" ≠ 0), globN s "sk_buf" + 52 ≤ 2 ^ 64)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "sk_make") values = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned v), post)) :
    let resumed := setVarHOLFinite (ofString "k") v {post with locals := s.locals}
    ArenaReady resumed ∧ WorldTyped resumed S ∧ CodeDbPayloadStrong resumed S db := by
  have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "sk_make")
    _ _ _ _ _ values callee (by rw [hc]; exact lookup_sk_make) hl
  subst body
  have hW : WorldTyped s S := ⟨hWT.1, hWT.2.1, hWT.2.2.1, Nd, hWT.2.2.2⟩
  have hWe : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd := by
    unfold WorldTypedWith callEntryStateHOLFinite
    simp only [tablesTyped_with_locals]
    exact hWT
  have hworldEntry : WorldTyped (callEntryStateHOLFinite s callee) S :=
    (worldTyped_with_locals s _ _ S).2 hW
  obtain ⟨hAp, hWp, hp⟩ := world_and_payload_after_sk_make db
    (localsFree_arenaReady s _ _ hAs) hWe hworldEntry hdb h hc hma hfit v hb
  have hworld : WorldTyped post S := ⟨hWp.1, hWp.2.1, hWp.2.2.1, Nd, hWp.2.2.2⟩
  exact ⟨localsFree_arenaReady post _ _ hAp,
    (worldTyped_with_locals post _ _ S).2 hworld, hp⟩

/-- Transport through access-table callee entry and caller restoration,
retaining all database facts required by the resumed witness lookup. -/
theorem protected_db_after_access_call {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db) (hdb : db ∈ S) (ht : t ∈ S)
    (hne : db ≠ t) (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hx : HtabExit (callEntryStateHOLFinite s callee) post) :
    let resumed := {post with locals := s.locals}
    ArenaReady resumed ∧ HtabWF resumed db ∧ NodeDbEntriesStrong resumed db := by
  let ent := callEntryStateHOLFinite s callee
  have hAe : ArenaReady ent := localsFree_arenaReady s _ _ hAs
  have hWe : WorldTyped ent S := (worldTyped_with_locals s _ _ S).2 hW
  have he : CodeDbPayloadStrong ent S db := h
  have hte : locN ent "t" ∈ S := by rw [hloc]; exact ht
  have hne' : db ≠ locN ent "t" := by rw [hloc]; exact hne
  have hp := codeDbPayloadStrong_entries_of_separated_htab_exit db he hAe hWe hdb hte hne' hx
  have hw := htabWF_of_separated_htab_exit db hAe hWe hdb hte hne' hx
  refine ⟨localsFree_arenaReady post _ _ hx.1,
    (WkBal.htabWF_with_locals post _ _ db).2 hw, ?_⟩
  exact hp

/-- Extract the access-table exit contract from its installed concrete body. -/
theorem access_set_exit_of_execution {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (harg : HtabArgWF s)
    (values : List (ValueHOL 64)) (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
      some (sourceFnBody Guest.Software.guestFn_htab_set, s.locals, .one))
    (hb : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set) =
      (some (.returned v), post)) : HtabExit s post := by
  obtain ⟨params, body, ret, hlookup, hspec⟩ := SoloHtabSet.htab_set_spec_proof
  have heq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one),
      (ofString "value", ShapeHOL.one)], sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) =
      (params, body, ret) := Option.some.inj (lookup_htab_set.symm.trans hlookup)
  rcases Prod.mk.inj heq with ⟨_, heq⟩
  rcases Prod.mk.inj heq with ⟨hbody, hret⟩
  subst body ret
  have hx := hspec s hc harg ⟨values, hl⟩ (by rw [hb]; simp) v (by rw [hb])
  simpa only [hb] using hx

/-- World allocation and typing discharge the concrete access-call arguments. -/
theorem access_argWF_of_world {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S) (ht : t ∈ S)
    (hloc : locN (callEntryStateHOLFinite s callee) "t" = t) :
    HtabArgWF (callEntryStateHOLFinite s callee) := by
  refine ⟨localsFree_arenaReady s _ _ hAs, ?_, ?_⟩
  · rw [hloc]
    exact (WkBal.htabWF_with_locals s _ _ t).2 (hW.1.2.1 t ht).1
  · rw [hloc]
    intro i hi
    exact ((hW.1.2.1 t ht).2 i hi).1

/-- Protected database facts follow from the concrete installed access-table
execution, rather than an assumed exit contract. -/
theorem protected_db_after_access_execution {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db) (hdb : db ∈ S) (ht : t ∈ S)
    (hne : db ≠ t) (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hc : s.code = originalRuntimeCode) (values : List (ValueHOL 64)) (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
      some (sourceFnBody Guest.Software.guestFn_htab_set, callee, .one))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_htab_set) = (some (.returned v), post)) :
    let resumed := {post with locals := s.locals}
    ArenaReady resumed ∧ HtabWF resumed db ∧ NodeDbEntriesStrong resumed db := by
  have hx := access_set_exit_of_execution (callEntryStateHOLFinite s callee) post hc
    (access_argWF_of_world s S t callee hAs hW ht hloc) values v hl hb
  exact protected_db_after_access_call db t callee hAs hW h hdb ht hne hloc hx

/-- Resume witness-code lookup after concrete access-table execution. -/
theorem witness_return_after_access_execution {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db hash : BitVec 64) (t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db.toNat) (hdb : db.toNat ∈ S) (ht : t ∈ S)
    (hne : db.toNat ≠ t) (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hc : s.code = originalRuntimeCode) (values : List (ValueHOL 64)) (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
      some (sourceFnBody Guest.Software.guestFn_htab_set, callee, .one))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_htab_set) = (some (.returned v), post))
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hload : evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hhash : s.locals.lookup (ofString "code_hash") = some (.val (.word hash))) :
    Ret {post with locals := s.locals}
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  obtain ⟨hAp, hw, he⟩ := protected_db_after_access_execution db.toNat t callee
    hAs hW h hdb ht hne hloc hc values v hl hb
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) (sourceFnBody Guest.Software.guestFn_htab_set)
  rw [hb] at hm
  have hcode : post.code = originalRuntimeCode := hm.1.trans hc
  have hshape' : post.eshapes.lookup (ofString "StateErr") = some .one := by
    rw [hm.2.2.2.2]; exact hshape
  apply get_code_ws_fallback_return_entry_strong {post with locals := s.locals} db hash
    hcode hshape' hAp ?_ hhash hw he
  rw [evalHOLFinite_eq_toExact] at hload ⊢
  exact hload

/-- An allocated aligned word outside the mutated table survives its exit. -/
theorem protected_word_after_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (a : Nat)
    (hAs : ArenaReady s) (ht : HtabWF s (locN s "t"))
    (ha : Allocated s (a, 8)) (hal : a % 8 = 0)
    (hd : ∀ j ∈ htabFootprint s (locN s "t"), Disj (a, 8) j)
    (hx : HtabExit s post) : memW post a = memW s a := by
  have hu : InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.IvlUnhit s post (a, 8) := by
    right
    apply ivlUnhit_of_frameOutside ⟨hal, by norm_num⟩ hx.2.2.2.2.2.2.1
    · intro j hj
      exact ⟨(ht.1 j hj).2.1, (ht.1 j hj).2.2.1⟩
    · have hs := hAs.2.2.2.2.2.2.1
      have hp := hx.1.2.2.2.2.2.2.1
      exact ⟨hs, by omega⟩
    · exact hd
    · exact disj_fresh_of_allocated hAs.2 hx.1.2 hx.2.2.2.2.1 ha
  apply InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.memW_eq_of_ivlUnhit hu hal
  · exact allocated_le_2pow64 hAs.2 ha
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Fixed-object typing supplies allocation and separation for root words. -/
theorem fixed_word_after_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (a : Nat) (i : Ivl)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (ht : locN s "t" ∈ S) (hi : i ∈ fixedObjects s)
    (hin : Inside (a, 8) i.1 (i.1 + i.2)) (hal : a % 8 = 0)
    (hx : HtabExit s post) : memW post a = memW s a := by
  have hiPos : i.2 ≠ 0 := by unfold Inside at hin; omega
  have hai := ((hW.2.2.1.1 i hi).resolve_left hiPos).1
  have ha : Allocated s (a, 8) := by
    rcases hai with hai | hai
    · left; unfold Inside at hai hin ⊢; omega
    · right; unfold Inside at hai hin ⊢; omega
  apply protected_word_after_htab_exit a hAs (hW.1.2.1 _ ht).1 ha hal
  · intro j hj
    have hd := Disj.flip (((hW.1.2.1 _ ht).2 j hj).2 i hi)
    apply InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg.disj_of_inside_left hin hd
  · exact hx

/-- The witness-code root is a protected word of the fixed witness record. -/
theorem ws_code_root_after_htab_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (ht : locN s "t" ∈ S) (hws : globN s "ws" ≠ 0)
    (hx : HtabExit s post) :
    memW post (globN s "ws" + 16) = memW s (globN s "ws" + 16) := by
  have hi : (globN s "ws", 40) ∈ fixedObjects s := by
    unfold fixedObjects
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.2 ⟨("ws", 40), by decide, by simp [hws]⟩
  have hw := ((hW.2.2.1.1 _ hi).resolve_left (by norm_num)).2
  have hal : globN s "ws" % 8 = 0 := hw.1
  apply fixed_word_after_htab_exit _ (globN s "ws", 40) hAs hW ht hi
  · unfold Inside; dsimp; omega
  · omega
  · exact hx

/-- Restore the caller's witness root after the access-call exit, including
the unchanged global used to address the root slot. -/
theorem ws_code_root_after_access_call_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S) (ht : t ∈ S)
    (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hws : globN s "ws" ≠ 0)
    (hx : HtabExit (callEntryStateHOLFinite s callee) post) :
    globN post "ws" = globN s "ws" ∧
    memW post (globN post "ws" + 16) = memW s (globN s "ws" + 16) := by
  have hg := hx.2.2.2.2.2.2.2 (ofString "ws") (by decide)
  have hglob : globN post "ws" = globN s "ws" := by
    unfold globN
    rw [← hg]
    rfl
  refine ⟨hglob, ?_⟩
  rw [hglob]
  apply ws_code_root_after_htab_exit
    (s := callEntryStateHOLFinite s callee) (S := S)
    (localsFree_arenaReady s _ _ hAs) ((worldTyped_with_locals s _ _ S).2 hW)
  · rw [hloc]; exact ht
  · exact hws
  · exact hx

/-- Lift preservation of a root word and its addressing global to expression
evaluation, including the load's memory-domain test. -/
theorem global_load_preserved {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64) (v : ValueHOL 64)
    (hg : post.globals.lookup (ofString g) = s.globals.lookup (ofString g))
    (hd : post.memaddrs = s.memaddrs)
    (hm : memW post (globN s g + k.toNat) = memW s (globN s g + k.toNat))
    (he : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const k])) = some v := by
  simp only [evalHOLFinite_eq_toExact] at he ⊢
  simp [evalHOLExact, evalListHOLExact] at he ⊢
  rcases hlookup : s.globals.lookup (ofString g) with _ | gv
  · simp [hlookup] at he
  · rcases gv with ⟨⟨w⟩⟩ | _ | _
    · have hadd : BitVec.ofNat 64 (w.toNat + k.toNat) = w + k := by rw [BitVec.add_def]
      have hmem : post.memory (w + k) = s.memory (w + k) := by
        simp only [memW, globN, hlookup, hadd] at hm
        cases hpost : post.memory (w + k) with
        | word wp =>
          cases hs : s.memory (w + k) with
          | word ws =>
            simp only [hpost, hs] at hm
            rw [BitVec.eq_of_toNat_eq hm]
      simpa [hg, hlookup, valueIsWord, valueWord, wordOpHOL, wordOp,
        memLoadHOLExact, hd, hmem] using he
    · simp [hlookup, valueIsWord] at he
    · simp [hlookup, valueIsWord] at he

/-- The concrete witness-root load survives the access-table call exit. -/
theorem ws_code_load_after_access_exit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S) (ht : t ∈ S)
    (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hws : globN s "ws" ≠ 0)
    (hx : HtabExit (callEntryStateHOLFinite s callee) post)
    (v : ValueHOL 64)
    (he : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some v) :
    evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some v := by
  have hr := ws_code_root_after_access_call_exit t callee hAs hW ht hloc hws hx
  apply global_load_preserved s post "ws" 16 v
  · exact (hx.2.2.2.2.2.2.2 (ofString "ws") (by decide)).symm
  · exact hx.1.1.memaddrs.trans hAs.1.memaddrs.symm
  · change memW post (globN s "ws" + 16) = memW s (globN s "ws" + 16)
    simpa only [hr.1] using hr.2
  · exact he

/-- Concrete access execution supplies the resumed witness lookup, with
all root-load evidence taken before the call. -/
theorem witness_return_after_access_execution_preload {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db hash : BitVec 64) (t : Nat)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db.toNat) (hdb : db.toNat ∈ S) (ht : t ∈ S)
    (hne : db.toNat ≠ t) (hloc : locN (callEntryStateHOLFinite s callee) "t" = t)
    (hc : s.code = originalRuntimeCode) (values : List (ValueHOL 64)) (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set") values =
      some (sourceFnBody Guest.Software.guestFn_htab_set, callee, .one))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (sourceFnBody Guest.Software.guestFn_htab_set) = (some (.returned v), post))
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hws : globN s "ws" ≠ 0)
    (hload : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hhash : s.locals.lookup (ofString "code_hash") = some (.val (.word hash))) :
    Ret {post with locals := s.locals}
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  have hx := access_set_exit_of_execution (callEntryStateHOLFinite s callee) post hc
    (access_argWF_of_world s S t callee hAs hW ht hloc) values v hl hb
  exact witness_return_after_access_execution db hash t callee hAs hW h hdb ht hne hloc
    hc values v hl hb hshape
    (ws_code_load_after_access_exit t callee hAs hW ht hloc hws hx _ hload) hhash

/-- Concrete access lookup installs both the expected body and table local. -/
theorem access_lookup_body_and_table
    (tw : BitVec 64) (key value : ValueHOL 64)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
      [.val (.word tw), key, value] = some (body, callee, ret)) :
    body = sourceFnBody Guest.Software.guestFn_htab_set ∧
    callee.lookup (ofString "t") = some (.val (.word tw)) := by
  exact lookupCodeHOLFinite_param_at originalRuntimeCode.lookup (ofString "htab_set") []
    (ofString "t") .one [(ofString "key", .one), (ofString "value", .one)]
    (sourceFnBody Guest.Software.guestFn_htab_set) .one
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> decide)
    lookup_htab_set (vpre := []) (by simp) hl

/-- Installed lookup discharges body, return shape, and table-local premises
for resuming witness retrieval after an access update. -/
theorem witness_return_after_access_lookup {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S : List Nat} (db hash tw : BitVec 64)
    (key value : ValueHOL 64) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db.toNat) (hdb : db.toNat ∈ S) (ht : tw.toNat ∈ S)
    (hne : db.toNat ≠ tw.toNat) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set")
      [.val (.word tw), key, value] = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post))
    (hshape : s.eshapes.lookup (ofString "StateErr") = some .one)
    (hws : globN s "ws" ≠ 0)
    (hload : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hhash : s.locals.lookup (ofString "code_hash") = some (.val (.word hash))) :
    Ret {post with locals := s.locals}
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c"))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  rw [hc] at hl
  obtain ⟨hbody, hlocal⟩ := access_lookup_body_and_table tw key value body callee ret hl
  subst body
  have hloc : locN (callEntryStateHOLFinite s callee) "t" = tw.toNat := by
    simp [locN, callEntryStateHOLFinite, hlocal]
  have hlone : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
      [.val (.word tw), key, value] =
      some (sourceFnBody Guest.Software.guestFn_htab_set, callee, .one) := by
    have hr : ret = .one := by
      unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
      split at hl
      · simp at hl
      · rename_i b l r raw
        unfold lookupCodeHOLExact at raw
        rw [lookup_htab_set] at raw
        dsimp only at raw
        split at raw
        · have hr := (Prod.mk.inj (Option.some.inj raw)).2
          have hf := (Prod.mk.inj (Option.some.inj hl)).2
          exact (congrArg Prod.snd hf).symm.trans (congrArg Prod.snd hr).symm
        · simp at raw
    subst ret
    exact hl
  exact witness_return_after_access_execution_preload db hash tw.toNat callee hAs hW h hdb ht
    hne hloc hc _ v hlone hb hshape hws hload hhash

/-- Compose the access update itself with resumed bounded witness retrieval. -/
theorem access_set_then_witness_return {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (db hash tw : BitVec 64) (key : ValueHOL 64)
    (hAs : ArenaReady s) (hW : WorldTyped s S)
    (h : CodeDbPayloadStrong s S db.toNat) (hdb : db.toNat ∈ S) (ht : tw.toNat ∈ S)
    (hne : db.toNat ≠ tw.toNat) (hc : s.code = originalRuntimeCode)
    (hs : s.eshapes.lookup (ofString "StateErr") = some .one) (hws : globN s "ws" ≠ 0)
    (hload : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ws"), .const 16])) = some (.val (.word db)))
    (hh : s.locals.lookup (ofString "code_hash") = some (.val (.word hash)))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]),
        .var .local (ofString "k"), .const 1] = some [.val (.word tw), key, .val (.word 1)]) :
    Ret s (.seq (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 40]),
        .var .local (ofString "k"), .const 1])
      (.decCall (ofString "c") (.comb [.one, .one]) (ofString "ws_get_code")
        [.var .local (ofString "code_hash")] (.return (.var .local (ofString "c")))))
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  apply Ret.seq_call00
  intro values body callee ret v post ha' hl hb
  have hv := Option.some.inj (ha.symm.trans ha')
  subst values
  exact witness_return_after_access_lookup db hash tw key (.val (.word 1)) body callee ret
    hAs hW h hdb ht hne hc v hl hb hs hws hload hh

end HeadStore
