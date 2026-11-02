import InitECandidate.Solver.Wave8GuestInv.Shards.S00.Core
import InitECandidate.Solver.PanTerminatingCombinators
import InitECandidate.Solver.Wave8GuestInv.Shards.S00.LightSpec

/-! Adapted from wave8/leaves-rlp-opus55 at 998817a20efa0796e7eb06992d98f332943646bc, RlpWalk and RlpCore.
RLP / byte-walk family leaves (Wave 8, speculative, branch `wave8/leaves-rlp-opus55`).

Generic fresh-address walk rule `while_walk` and its uses. A walk loop is a strict counter step
`i := i + stride` whose first statement accesses `d + i`; every continuing iteration therefore has
`d + i ∈ ordinaryDomain ⊆ [sourceBase, heapEnd)` (`GuestInv.memaddrs`), and the rank
`min (heapEnd - (d + i)) (domainBytes + 1)` strictly decreases. The loop rule is step0's
`PanTerminatingCombinators.TerminatingProgBoundedOn.while_measure`; composition uses only the
spec's proved `dec_on` / `seq_guestInv` / `ite_on` / `call_guestInv` / `decCall_guestInv`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.S00

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8Leaves.S00Spec InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

theorem addresses_bounds (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ base.toNat + 8 * n := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt] <;>
          simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord] <;> omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

theorem ordinaryDomain_bounds (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have := addresses_bounds _ _ x (by rw [hs]; decide) h
  rw [hs] at this
  have e1 : sourceBase = 2701131776 := by decide
  have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  omega


/-- Rank of a walk address: bytes left below `heapEnd`, capped at `domainBytes + 1`. -/
def walkRank (a : BitVec 64) : Nat := min (heapEnd - a.toNat) (domainBytes + 1)

/-- Walk measure: the rank of `d + i` (`0` if either local is not a word). -/
def walkMu (d i : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup d, s.locals.lookup i with
  | some (.val (.word x)), some (.val (.word y)) => walkRank (x + y)
  | _, _ => 0

theorem walkMu_le (d i : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    walkMu d i s ≤ domainBytes + 1 := by
  unfold walkMu
  split
  · exact Nat.min_le_right _ _
  · exact Nat.zero_le _

/-- A program whose flowing runs access the address `d + i` inside `[sourceBase, heapEnd)`. -/
def FirstAccess (d i : MlS) (first : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s →
    (evaluateHOLFiniteState s first).1 = none →
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧
      sourceBase ≤ (x + y).toNat ∧ (x + y).toNat < heapEnd

theorem seq_none_first {F : Type} (s : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (h : (evaluateHOLFiniteState s (.seq first tail)).1 = none) :
    (evaluateHOLFiniteState s first).1 = none := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s first with ⟨r, mid⟩
  rw [hr] at h
  cases r with
  | none => rfl
  | some r => simp at h

theorem firstAccess_seq {d i : MlS} {first : ProgHOL 64} (tail : ProgHOL 64)
    (h : FirstAccess d i first) : FirstAccess d i (.seq first tail) :=
  fun s hP hn => h s hP (seq_none_first s first tail hn)

theorem walkRank_step (a stride : BitVec 64) (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64)
    (hlo : sourceBase ≤ a.toNat) (hhi : a.toNat < heapEnd) :
    walkRank (a + stride) < walkRank a := by
  have eH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  have eS : sourceBase = 2701131776 := by decide
  have eD : domainBytes = heapEnd - sourceBase := rfl
  have hadd : (a + stride).toNat = a.toNat + stride.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  unfold walkRank
  rw [hadd]
  omega

/-- Fresh-address walk rule: the loop body is a strict counter step `i := i + stride` whose first
statement accesses `d + i` (so `d + i ∈ [sourceBase, heapEnd)` on every continuing iteration). -/
theorem while_walk {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS} {stride : BitVec 64}
    (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64)
    (hcount : CountedBody i stride body 0)
    (hd : avoidsLocal d body = true)
    (hfirst : FirstAccess d i body)
    (hstraight : extStraightLine body = true)
    (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while cond body)
      ((domainBytes + 1 + 1) * (0 + 1)) := by
  have hstep : LoopStep (walkMu d i) cond body 0 GuestInv := by
    intro F s word hcode hP _ _ hclk
    dsimp only
    intro hnt
    have hPd : GuestInv (decClockHOLFinite s) :=
      guestInv_congr (s := s) rfl rfl rfl rfl hP
    have hflowAcc := hfirst (decClockHOLFinite s) hPd
    rcases hacc : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, post⟩
    have hpostInv : GuestInv post := by
      have := guestInv_evaluate (decClockHOLFinite s) body hPd
      rw [hacc] at this; exact this
    have hclk' := TerminatingProgBounded.straight _ hstraight (decClockHOLFinite s) hcode
    have hnc' := evaluate_noTopContinue _ hnc (decClockHOLFinite s)
    unfold TerminatingRunBounded at hclk'
    rw [hacc] at hclk' hnc' hnt
    obtain ⟨c1, c2⟩ := hclk' hnt
    dsimp only at c1 c2 hnc' ⊢
    refine ⟨by simpa [decClockHOLFinite] using c1, by simpa [decClockHOLFinite] using c2, fun hflow => ?_⟩
    have hnone : res = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    subst hnone
    obtain ⟨x, y, hx, hy, hlo, hhi⟩ :=
      hflowAcc (by rw [hacc])
    obtain ⟨_, _, _, _, c5⟩ := hcount.run (decClockHOLFinite s) hcode y hy (Nat.zero_le _)
    have hdk := evaluate_avoidsLocal_flowing d _ hd (decClockHOLFinite s) (by rw [hacc]; exact Or.inl rfl)
    rw [hacc] at c5 hdk
    obtain ⟨c5a, c5b⟩ := c5 rfl
    dsimp only at c5a c5b hdk
    refine ⟨?_, ?_, hpostInv⟩
    · have hx' : s.locals.lookup d = some (.val (.word x)) := by simpa [decClockHOLFinite] using hx
      have hy' : s.locals.lookup i = some (.val (.word y)) := by simpa [decClockHOLFinite] using hy
      have hxp : post.locals.lookup d = some (.val (.word x)) := by
        rw [hdk]; exact hx
      unfold walkMu
      rw [hxp, c5a, hx', hy']
      dsimp only
      rw [← BitVec.add_assoc]
      exact walkRank_step _ _ hs hs2 hlo hhi
    · exact c5b.trans (by simp [decClockHOLFinite])
  intro F s hcode hP
  exact TerminatingProgBoundedOn.while_measure (walkMu d i) cond _ hstep s hcode
    ⟨hP, walkMu_le d i s⟩

theorem eval_add2_word {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (d i : MlS) (a : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i]) =
      some (.val (.word a))) :
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧ a = x + y := by
  simp only [evalHOLExact, evalListHOLExact] at he
  rcases hd : s.locals.lookup d with _ | vd <;> rcases hi : s.locals.lookup i with _ | vi <;>
    simp only [hd, hi] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vd with ⟨⟨x⟩⟩ | _ | _ <;> rcases vi with ⟨⟨y⟩⟩ | _ | _ <;>
      simp [valueIsWord] at he
    refine ⟨x, y, rfl, rfl, ?_⟩
    simp [valueWord, wordOpHOL, wordOp] at he
    exact he.symm

theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat]
  have ha := a.isLt
  have : a.toNat / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

theorem firstAccess_store (d i : MlS) (v : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (h : DecidablePred s.memaddrs)
      (val : ValueHOL 64), @evalHOLExact 64 F _ s.toExact h v = some val → ∃ w, val = .val w) :
    FirstAccess d i (.store (.op .add [.var .local d, .var .local i]) v) := by
  intro F s hP h
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hv s _ val hval
      split at h
      · rename_i mem hmem
        have hdom : s.memaddrs (x + y) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc
          simp [hc] at hmem
        rw [hP.memaddrs] at hdom
        have := ordinaryDomain_bounds _ hdom
        omega
      · simp at h
    · simp at h
  · simp at h

theorem firstAccess_storeByte (d i : MlS) (v : ExpHOL 64) :
    FirstAccess d i (.storeByte (.op .add [.var .local d, .var .local i]) v) := by
  intro F s hP h
  rw [evaluateHOLFiniteState_storeByte] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · split at h
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (x + y)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hP.memaddrs] at hdom
        have := ordinaryDomain_bounds _ hdom
        have := byteAlign_bounds (x + y)
        omega
      · simp at h
    · simp at h
  · simp at h

theorem const_isVal (c : BitVec 64) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : DecidablePred s.memaddrs) (val : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact h (.const c) = some val → ∃ w, val = .val w := by
  intro F s h val hv
  simp [evalHOLExact] at hv
  exact ⟨_, hv.symm⟩

theorem eval_load_one {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.load .one e) = some v) :
    ∃ a : BitVec 64, @evalHOLExact 64 F _ s.toExact h e = some (.val (.word a)) ∧ s.memaddrs a ∧
      ∃ w, v = .val w := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · rename_i a ha
      simp only [memLoadHOLExact] at he
      split at he
      · rename_i hd
        exact ⟨a, ha, hd, _, (Option.some.inj he).symm⟩
      · simp at he
    · simp at he
  · simp at he

theorem eval_loadByte {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.loadByte e) = some v) :
    ∃ a : BitVec 64, @evalHOLExact 64 F _ s.toExact h e = some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i a ha
    refine ⟨a, ha, ?_⟩
    by_contra hc
    revert he
    simp only [panMemLoadByteHOL]
    split <;> first | contradiction | simp [hc]
  · simp at he

theorem eval_cmp_left {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (c : Cmp) (l r : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.cmp c l r) = some v) :
    ∃ vl, @evalHOLExact 64 F _ s.toExact h l = some vl := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i _ _ w _ hl _
    exact ⟨_, hl⟩
  · simp at he

theorem load_isVal (e : ExpHOL 64) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : DecidablePred s.memaddrs) (val : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact h (.load .one e) = some val → ∃ w, val = .val w := by
  intro F s h val hv
  obtain ⟨_, _, _, w, hw⟩ := eval_load_one s (h := h) e val hv
  exact ⟨w, hw⟩

theorem ite_cond_some {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (yes no : ProgHOL 64) (h : (evaluateHOLFiniteState s (.ite cond yes no)).1 = none) :
    ∃ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some v := by
  rw [evaluateHOLFiniteState_ite] at h
  split at h
  · exact ⟨_, by assumption⟩
  · simp at h

theorem firstAccess_ite_load (d i : MlS) (c : Cmp) (r : ExpHOL 64) (yes no : ProgHOL 64) :
    FirstAccess d i (.ite (.cmp c (.load .one (.op .add [.var .local d, .var .local i])) r) yes no) := by
  intro F s hP h
  obtain ⟨v, hv⟩ := ite_cond_some s _ yes no h
  obtain ⟨vl, hl⟩ := eval_cmp_left s (h := fun a => Classical.propDecidable (s.memaddrs a)) c _ r v hv
  obtain ⟨a, ha, hdom, _⟩ := eval_load_one s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vl hl
  obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
  refine ⟨x, y, hx, hy, ?_⟩
  rw [hP.memaddrs] at hdom
  have := ordinaryDomain_bounds _ hdom
  omega

theorem firstAccess_ite_loadByte (d i : MlS) (c : Cmp) (r : ExpHOL 64) (yes no : ProgHOL 64) :
    FirstAccess d i (.ite (.cmp c (.loadByte (.op .add [.var .local d, .var .local i])) r) yes no) := by
  intro F s hP h
  obtain ⟨v, hv⟩ := ite_cond_some s _ yes no h
  obtain ⟨vl, hl⟩ := eval_cmp_left s (h := fun a => Classical.propDecidable (s.memaddrs a)) c _ r v hv
  obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vl hl
  obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
  refine ⟨x, y, hx, hy, ?_⟩
  rw [hP.memaddrs] at hdom
  have := ordinaryDomain_bounds _ hdom
  have := byteAlign_bounds (x + y)
  omega

theorem firstAccess_dec_loadByte (d i : MlS) (name : MlS) (shape : ShapeHOL) (body : ProgHOL 64) :
    FirstAccess d i (.dec name shape (.loadByte (.op .add [.var .local d, .var .local i])) body) := by
  intro F s hP h
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ v hv
    obtain ⟨x, y, hx, hy, rfl⟩ :=
      eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
    refine ⟨x, y, hx, hy, ?_⟩
    rw [hP.memaddrs] at hdom
    have := ordinaryDomain_bounds _ hdom
    have := byteAlign_bounds (x + y)
    omega

theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true) (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true) (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

theorem countedBody_seq' {counter : MlS} {step : BitVec 64} {first tail : ProgHOL 64} {cost : Nat}
    (hrest : CountedBody counter step tail cost) (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true) (hn : noTopContinue first = true) :
    CountedBody counter step (.seq first tail) cost :=
  countedBody_seq_straight first hs ha hn hrest

theorem countedBody_dec' {counter : MlS} {step : BitVec 64} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {cost : Nat}
    (rest : CountedBody counter step body cost) (distinct : counter ≠ name) :
    CountedBody counter step (.dec name shape initializer body) cost :=
  CountedBody.dec name shape initializer distinct rest

/-- `while_walk` with the counter/access hypotheses first (they fix `i`, `stride` and `d`). -/
theorem while_walk' {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS} {stride : BitVec 64}
    (hcount : CountedBody i stride body 0) (hfirst : FirstAccess d i body)
    (hd : avoidsLocal d body = true) (hstraight : extStraightLine body = true)
    (hnc : noTopContinue body = true) (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64) :
    TerminatingProgBoundedOn GuestInv (.while cond body) ((domainBytes + 1 + 1) * (0 + 1)) :=
  while_walk hs hs2 hcount hd hfirst hstraight hnc

/-- Strict counter body: straight-line prefix statements then `i := i + stride`. -/
syntax "counted_auto" : tactic
macro_rules
  | `(tactic| counted_auto) => `(tactic| first
      | exact CountedBody.incr
      | (apply countedBody_seq'
         · counted_auto
         · rfl
         · rfl
         · rfl)
      | (apply countedBody_dec'
         · counted_auto
         · decide))

/-- First access of a walk body at `d + i`. -/
syntax "access_auto" : tactic
macro_rules
  | `(tactic| access_auto) => `(tactic| first
      | exact firstAccess_store _ _ _ (const_isVal _)
      | exact firstAccess_store _ _ _ (load_isVal _)
      | exact firstAccess_storeByte _ _ _
      | exact firstAccess_ite_load _ _ _ _ _ _
      | exact firstAccess_ite_loadByte _ _ _ _ _ _
      | exact firstAccess_dec_loadByte _ _ _ _ _
      | (apply firstAccess_seq; access_auto))

/-- Structural bound of a program built from straight-line code, `seq`, `ite`, `dec` and walks. -/
syntax "walk_auto" : tactic
macro_rules
  | `(tactic| walk_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · walk_auto
         · walk_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · walk_auto
         · walk_auto)
      | (apply dec_guestInv; walk_auto)
      | (apply while_walk'
         · counted_auto
         · access_auto
         · rfl
         · rfl
         · rfl
         · decide
         · decide))

def ctrMu (i n : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup i, s.locals.lookup n with
  | some (.val (.word y)), some (.val (.word m)) => m.toNat - y.toNat
  | _, _ => 0

theorem ctrMu_le (i n : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ctrMu i n s ≤ 2 ^ 64 := by
  unfold ctrMu
  split
  · rename_i y m _ _
    have := m.isLt
    omega
  · exact Nat.zero_le _

theorem eval_lower_locals {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (i n : MlS) (w : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.cmp .lower (.var .local i) (.var .local n)) =
      some (.val (.word w))) (hw : w ≠ 0) :
    ∃ y m : BitVec 64, s.locals.lookup i = some (.val (.word y)) ∧
      s.locals.lookup n = some (.val (.word m)) ∧ y.toNat < m.toNat := by
  simp only [evalHOLExact] at he
  rcases hi : s.locals.lookup i with _ | vi <;> rcases hn : s.locals.lookup n with _ | vn <;>
    simp only [hi, hn] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vi with ⟨⟨y⟩⟩ | _ | _ <;> rcases vn with ⟨⟨m⟩⟩ | _ | _ <;> simp at he
    refine ⟨y, m, rfl, rfl, ?_⟩
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at he
    by_contra hc
    have : ¬ (y < m) := by rw [BitVec.lt_def]; omega
    simp [this] at he
    exact hw he.symm

theorem while_ctr {i n : MlS} {body : ProgHOL 64}
    (hcount : CountedBody i 1 body 0) (hn : avoidsLocal n body = true)
    (hstraight : extStraightLine body = true) (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local i) (.var .local n)) body)
      ((2 ^ 64 + 1) * (0 + 1)) := by
  have hstep : LoopStep (ctrMu i n) (.cmp .lower (.var .local i) (.var .local n)) body 0 GuestInv := by
    intro F s word hcode hP hcond hw hclk
    dsimp only
    intro hnt
    have hPd : GuestInv (decClockHOLFinite s) :=
      guestInv_congr (s := s) rfl rfl rfl rfl hP
    obtain ⟨y, m, hy, hm, hlt⟩ := eval_lower_locals s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) i n word hcond hw
    rcases hacc : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨res, post⟩
    have hpostInv : GuestInv post := by
      have := guestInv_evaluate (decClockHOLFinite s) body hPd
      rw [hacc] at this; exact this
    have hclk' := TerminatingProgBounded.straight _ hstraight (decClockHOLFinite s) hcode
    have hnc' := evaluate_noTopContinue _ hnc (decClockHOLFinite s)
    unfold TerminatingRunBounded at hclk'
    rw [hacc] at hclk' hnc' hnt
    obtain ⟨c1, c2⟩ := hclk' hnt
    dsimp only at c1 c2 hnc' ⊢
    refine ⟨by simpa [decClockHOLFinite] using c1, by simpa [decClockHOLFinite] using c2, fun hflow => ?_⟩
    have hnone : res = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    subst hnone
    have hyd : (decClockHOLFinite s).locals.lookup i = some (.val (.word y)) := by
      simpa [decClockHOLFinite] using hy
    obtain ⟨_, _, _, _, c5⟩ := hcount.run (decClockHOLFinite s) hcode y hyd (Nat.zero_le _)
    have hnk := evaluate_avoidsLocal_flowing n _ hn (decClockHOLFinite s) (by rw [hacc]; exact Or.inl rfl)
    rw [hacc] at c5 hnk
    obtain ⟨c5a, c5b⟩ := c5 rfl
    dsimp only at c5a c5b hnk
    refine ⟨?_, c5b.trans (by simp [decClockHOLFinite]), hpostInv⟩
    have hmp : post.locals.lookup n = some (.val (.word m)) := by
      rw [hnk]; simpa [decClockHOLFinite] using hm
    unfold ctrMu
    rw [c5a, hmp, hy, hm]
    dsimp only
    have hadd : (y + 1).toNat = y.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
    omega
  intro F s hcode hP
  exact TerminatingProgBoundedOn.while_measure (ctrMu i n) _ _ hstep s hcode ⟨hP, ctrMu_le i n s⟩

theorem while_ctr' {i n : MlS} {body : ProgHOL 64}
    (hcount : CountedBody i 1 body 0) (hn : avoidsLocal n body = true)
    (hstraight : extStraightLine body = true) (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local i) (.var .local n)) body)
      ((2 ^ 64 + 1) * (0 + 1)) :=
  while_ctr hcount hn hstraight hnc


syntax "s00_loop_auto" : tactic
macro_rules
  | `(tactic| s00_loop_auto) => `(tactic| first
      | (apply while_ctr'
         · counted_auto
         · rfl
         · rfl
         · rfl)
      | (apply while_walk'
         · counted_auto
         · access_auto
         · rfl
         · rfl
         · rfl
         · decide
         · decide))

syntax "s00_auto" : tactic
macro_rules
  | `(tactic| s00_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · s00_auto
         · s00_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · s00_auto
         · s00_auto)
      | (apply dec_guestInv; s00_auto)
      | (apply call_guestInv'; assumption)
      | (apply decCall_guestInv'
         · assumption
         · s00_auto)
      | s00_loop_auto)

end InitECandidate.Solver.Wave8Leaves.S00
