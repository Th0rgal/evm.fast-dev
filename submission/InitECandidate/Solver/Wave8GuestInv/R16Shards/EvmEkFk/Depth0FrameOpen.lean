import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.NewScratchSpec
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Tables
import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11

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

end HeadStore
