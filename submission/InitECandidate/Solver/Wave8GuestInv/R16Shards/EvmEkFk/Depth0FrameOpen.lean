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

end HeadStore

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
