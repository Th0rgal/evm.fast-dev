import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

/-! `fb_merkleize` for Wave 8 shard s14 (`wave8/leaves-s14`).

`merkleize` (AST index 186) has three loops: the outer loop halves `cur` (at most 64
iterations, since the condition is the signed comparison `1 < cur`), wrapping an inner counted
loop over `j < half`, and a trailing counted loop `d < target`. All three are bounded by the
light-cone rules in `Core.lean`; the halved counter needs the one extra rule `while_halving`
below. Imports only the light cone via `campaign.leaves.s14.Core`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- Rank of a halved counter: the word's bit width, so `cur := cur >>> 1` strictly decreases it
while the signed condition `1 < cur` holds. -/
def halvingRank {F : Type} (c : MlS) (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup c with
  | some (.val (.word w)) => w.toNat.log2 + 1
  | _ => 0

theorem lt_two_mul_pow_log2 (n : Nat) (hn : n ≠ 0) : n < 2 ^ (n.log2 + 1) := by
  have h := (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  exact h

theorem halvingRank_le (c : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    halvingRank c s ≤ 64 := by
  unfold halvingRank
  split
  · rename_i w _
    by_cases hw0 : w.toNat = 0
    · simp [hw0]
    · have hw := w.isLt
      have hlt : w.toNat.log2 < 64 := (Nat.log2_lt hw0).mpr hw
      omega
  · omega

theorem wordShift_lsr1 (w : BitVec 64) :
    wordShiftHOL (width := 64) .lsr w 1 = some (w >>> 1) := by
  simp [wordShiftHOL]

theorem eval_shift_lsr1 {F : Type} (s : PanSemStateFiniteExact 64 F) (c : MlS) (w : BitVec 64)
    (h : s.locals.lookup c = some (.val (.word w))) :
    evalAt s (.shift .lsr (.var .local c) (.const 1#64)) = some (.val (.word (w >>> 1))) := by
  simp [evalAt, evalHOLExact, h, wordShift_lsr1]

theorem signedLess_one (w : BitVec 64) :
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess (1 : BitVec 64) w = true ↔
      1 < w.toNat ∧ w.toNat < 2 ^ 63 := by
  have hw := w.isLt
  unfold Flapjack.Compiler.Encoders.Asm.holAsmSignedLess
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [h1]
  split_ifs <;> simp_all

theorem halving_step (w : BitVec 64) (h : 1 < w.toNat) :
    (w >>> (1 : Nat)).toNat.log2 + 1 < w.toNat.log2 + 1 := by
  have hd : (w >>> (1 : Nat)).toNat = w.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [hd]
  have hpos : w.toNat / 2 ≠ 0 := by omega
  have hlt : w.toNat / 2 < 2 ^ w.toNat.log2 := by
    have := lt_two_mul_pow_log2 w.toNat (by omega)
    rw [Nat.pow_succ] at this
    omega
  have hlog : (w.toNat / 2).log2 < w.toNat.log2 := (Nat.log2_lt hpos).mpr hlt
  omega

theorem halving_assign_run {F : Type} (s : PanSemStateFiniteExact 64 F) (c half : MlS)
    (w v : BitVec 64) (h : s.locals.lookup c = some (.val (.word w)))
    (hv : s.locals.lookup half = some (.val (.word v))) :
    evaluateHOLFiniteState s (.assign .local c (.var .local half)) =
      (none, setVarHOLFinite c (.val (.word v)) s) := by
  simp [evaluateHOLFiniteState_assign, evalHOLExact, hv, h, lookupKvarHOLExact,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]

/-- Outer loop of `merkleize`: `while (1 < cur) (dec half := cur >>> 1 (dec j ... (cur := half)))`.
Each continuing iteration replaces `cur` by `cur >>> 1`, so the bit width decreases. -/
theorem while_halving {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    (c half j : MlS) (hch : c ≠ half) (hcj : c ≠ j) (hhj : half ≠ j) {wloop : ProgHOL 64} {B : Nat}
    (hwloop : TerminatingProgBoundedOn P wloop B)
    (havoid : avoidsLocal c wloop = true)
    (hnoCont : noTopContinue wloop = true)
    (hhalf : avoidsLocal half wloop = true) :
    TerminatingProgBoundedOn P
      (.while (.cmp .less (.const 1#64) (.var .local c))
        (.dec half .one (.shift .lsr (.var .local c) (.const 1#64))
          (.dec j .one (.const 0#64)
            (.seq wloop (.assign .local c (.var .local half))))))
      ((64 + 1) * (B + 1)) := by
  let body : ProgHOL 64 := .dec half .one (.shift .lsr (.var .local c) (.const 1#64))
    (.dec j .one (.const 0#64) (.seq wloop (.assign .local c (.var .local half))))
  have hb : TerminatingProgBoundedOn P
      (.dec half .one (.shift .lsr (.var .local c) (.const 1#64))
        (.dec j .one (.const 0#64) (.seq wloop (.assign .local c (.var .local half))))) B :=
    TerminatingProgBoundedOn.weaken'
      (dec_meta hP half .one (.shift .lsr (.var .local c) (.const 1#64))
        (dec_meta hP j .one (.const 0#64)
          (seq_meta hP hwloop (straightOn (.assign .local c (.var .local half)) rfl))))
      (Nat.le_refl B)
  apply TerminatingProgBoundedOn.while_rank (halvingRank c)
    (fun s hs => metadataInv_decClock hP s hs) hb
  · intro F s _ _ _
    exact halvingRank_le c s
  · intro F s _ hs hact hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, w, ha, hw', hword⟩ := evalAt_cmp s .less _ _ word hw
    simp only [evalAt, evalHOLExact] at ha hw'
    have hone : a = 1#64 := by
      injection ha with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
    subst a
    have hcur : s.locals.lookup c = some (.val (.word w)) := by simpa using hw'
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .less (1#64) w = true := by
      by_contra hc
      simp only [hc, if_false] at hword
      exact hnz hword
    have hpos : 1 < w.toNat := by
      have : 1 < w.toNat ∧ w.toNat < 2 ^ 63 := by
        have hcmp' : Flapjack.Compiler.Encoders.Asm.holAsmSignedLess (1#64) w = true := by
          simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hcmp
        exact (signedLess_one w).mp hcmp'
      exact this.1
    have hncBody : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .continue :=
      evaluate_noTopContinue body (by simp [body, noTopContinue, hnoCont]) (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hncBody
    rcases hbodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, post⟩
    rw [hbodyRun] at hnone
    dsimp only at hnone
    subst hnone
    have hdec1 := hbodyRun
    dsimp only [body] at hdec1
    rw [evaluateHOLFiniteState_dec_total] at hdec1
    have hcurDec : (decClockHOLFinite s).locals.lookup c = some (.val (.word w)) := hcur
    have h1nat : (1#64).toNat = 1 := rfl
    simp only [evalHOLExact, hcurDec, h1nat, wordShift_lsr1, Option.map,
      shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hdec1
    rcases hrun1 : evaluateHOLFiniteState
        (setVarHOLFinite half (.val (.word (w >>> 1))) (decClockHOLFinite s))
        (.dec j .one (.const 0#64) (.seq wloop (.assign .local c (.var .local half)))) with
      ⟨r1, inner1⟩
    rw [hrun1] at hdec1
    injection hdec1 with hr1 hpostEq
    subst hr1
    obtain ⟨vj, inner2, hrun2, hloc2⟩ := dec_flowing (Or.inl rfl) hrun1
    have hseq := hrun2
    rw [evaluateHOLFiniteState_seq_line780] at hseq
    have hframeH := evaluate_avoidsLocal_flowing half wloop hhalf
      (setVarHOLFinite j vj (setVarHOLFinite half (.val (.word (w >>> 1))) (decClockHOLFinite s)))
    have hframeC := evaluate_avoidsLocal_flowing c wloop havoid
      (setVarHOLFinite j vj (setVarHOLFinite half (.val (.word (w >>> 1))) (decClockHOLFinite s)))
    rcases hwRun : evaluateHOLFiniteState
        (setVarHOLFinite j vj (setVarHOLFinite half (.val (.word (w >>> 1))) (decClockHOLFinite s)))
        wloop with ⟨rwl, mid⟩
    rw [hwRun] at hseq hframeH hframeC
    dsimp only at hseq hframeH hframeC
    cases rwl with
    | some _ => simp at hseq
    | none =>
      dsimp only at hseq
      have hmidH : mid.locals.lookup half = some (.val (.word (w >>> 1))) := by
        rw [hframeH (Or.inl rfl)]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hhj]
      have hmidC : mid.locals.lookup c = some (.val (.word w)) := by
        rw [hframeC (Or.inl rfl)]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hcj, Ne.symm hch,
          decClockHOLFinite, hcur]
      have hassign := halving_assign_run mid c half w (w >>> 1) hmidC hmidH
      rw [hassign] at hseq
      injection hseq with _ hinner2
      have hpostC : post.locals.lookup c = some (.val (.word (w >>> 1))) := by
        rw [← hpostEq]
        dsimp only
        rw [PanRunBounded.resVarEq_lookup, if_neg hch, hloc2, PanRunBounded.resVarEq_lookup,
          if_neg hcj, ← hinner2]
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      unfold halvingRank
      change (match post.locals.lookup c with | some (.val (.word w)) => w.toNat.log2 + 1 | _ => 0) <
        (match s.locals.lookup c with | some (.val (.word w)) => w.toNat.log2 + 1 | _ => 0)
      rw [hpostC, hcur]
      exact halving_step w hpos

theorem fb_merkleize_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (hP : MetadataInv P)
    {K_ceil_log2 K_max K_memcpy K_heap_mark K_alloc K_memzero K_sha256_pair K_heap_release : Nat}
    (h_ceil_log2 : TerminatingFunBoundedOn P (ofString "ceil_log2") K_ceil_log2)
    (h_max : TerminatingFunBoundedOn P (ofString "max") K_max)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_sha256_pair : TerminatingFunBoundedOn P (ofString "sha256_pair") K_sha256_pair)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "merkleize")
      ((K_ceil_log2 + 1) + (K_ceil_log2 + 1) + (K_max + 1) + Nat.max ((K_memcpy + 1)) (0) +
        (K_heap_mark + 1) + (K_alloc + 1) + (K_memcpy + 1) + (K_memzero + 1) +
        (64 + 1) * ((2 ^ 64 + 1) * ((K_sha256_pair + 1) + 1) + 1) +
        (2 ^ 64 + 1) * ((K_sha256_pair + 1) + 1) + (K_memcpy + 1) + (K_heap_release + 1)) := by
  fb_unfold 186 Guest.Software.guestFn_merkleize
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_meta hP
    · exact h_ceil_log2
    · apply decCall_meta hP
      · exact h_ceil_log2
      · apply decCall_meta hP
        · exact h_max
        · apply seq_meta hP
          · apply ite_meta
            · apply seq_meta hP
              · exact call_meta hP h_memcpy
              · exact straightOn _ rfl
            · exact straightOn _ rfl
          · apply decCall_meta hP
            · exact h_heap_mark
            · apply dec_meta hP
              apply decCall_meta hP
              · exact h_alloc
              · apply seq_meta hP
                · exact call_meta hP h_memcpy
                · apply seq_meta hP
                  · exact call_meta hP h_memzero
                  · apply dec_meta hP
                    apply seq_meta hP
                    · apply while_halving hP (ofString "cur") (ofString "half") (ofString "j")
                        (by decide) (by decide) (by decide)
                      · apply while_counter_meta hP .less (Or.inl rfl)
                        · apply seq_meta hP
                          · exact call_meta hP h_sha256_pair
                          · exact straightOn _ rfl
                        · incr_body
                        · rfl
                      · rfl
                      · rfl
                      · rfl
                    · fb_auto hP
  · fb_arith

end InitECandidate.Solver.Wave8Leaves.S14
