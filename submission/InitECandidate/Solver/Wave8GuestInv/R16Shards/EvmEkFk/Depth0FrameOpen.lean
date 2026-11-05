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

end HeadStore
