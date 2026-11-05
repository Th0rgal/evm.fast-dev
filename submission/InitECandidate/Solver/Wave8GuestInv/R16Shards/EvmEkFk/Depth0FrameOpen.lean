import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.EkWarmStorageKey
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyProcessMsg
import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.NewScratchSpec
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2Tables

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

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
