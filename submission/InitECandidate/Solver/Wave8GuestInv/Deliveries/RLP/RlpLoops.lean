import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpLeaves1

/-! RLP family, part 4: loops whose first statement strictly decreases a local word
(`v := v >>> 8` under `v ≠ 0`, `i := i - 1` under `0 < i`), via step0's `while_measure`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8Leaves.Rlp

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingCombinators

def localMu (x : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup x with
  | some (.val (.word w)) => w.toNat
  | _ => 0

theorem localMu_le (x : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    localMu x s ≤ 2 ^ 64 := by
  unfold localMu
  split
  · rename_i w _
    have := w.isLt
    omega
  · exact Nat.zero_le _

/-- Active condition fixes `x` to a word `w`, and `e` then evaluates to a strictly smaller word. -/
def LocalDecreases (cond : ExpHOL 64) (x : MlS) (e : ExpHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word word)) → word ≠ 0 →
    ∃ w w' : BitVec 64, s.locals.lookup x = some (.val (.word w)) ∧
      @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
        (fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a)) e =
        some (.val (.word w')) ∧ w'.toNat < w.toNat

theorem while_localDec {cond : ExpHOL 64} {x : MlS} {e : ExpHOL 64} {rest : ProgHOL 64}
    (hdec : LocalDecreases cond x e) (hrest : avoidsLocal x rest = true)
    (hstraight : extStraightLine (.seq (.assign .local x e) rest) = true)
    (hnc : noTopContinue (.seq (.assign .local x e) rest) = true) :
    TerminatingProgBoundedOn GuestInv (.while cond (.seq (.assign .local x e) rest))
      ((2 ^ 64 + 1) * (0 + 1)) := by
  have hstep : LoopStep (localMu x) cond (.seq (.assign .local x e) rest) 0 GuestInv := by
    intro F s word hcode hP hcond hw hclk
    dsimp only
    intro hnt
    have hPd : GuestInv (decClockHOLFinite s) :=
      guestInv_congr (s := s) rfl rfl rfl rfl hP
    obtain ⟨w, w', hx, he, hlt⟩ := hdec s word hcond hw
    rcases hacc : evaluateHOLFiniteState (decClockHOLFinite s) (.seq (.assign .local x e) rest) with
      ⟨res, post⟩
    have hpostInv : GuestInv post := by
      have := guestInv_evaluate (decClockHOLFinite s) (.seq (.assign .local x e) rest) hPd
      rw [hacc] at this; exact this
    have hclk' := TerminatingProgBounded.straight (.seq (.assign .local x e) rest) hstraight
      (decClockHOLFinite s) hcode
    have hnc' := evaluate_noTopContinue _ hnc (decClockHOLFinite s)
    have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s)
      (.seq (.assign .local x e) rest)).1
    unfold TerminatingRunBounded at hclk'
    rw [hacc] at hclk' hnc' hnt hmeta
    obtain ⟨c1, c2⟩ := hclk' hnt
    dsimp only at c1 c2 hnc' hmeta ⊢
    refine ⟨by simpa [decClockHOLFinite] using c1, by simpa [decClockHOLFinite] using c2,
      fun hflow => ?_⟩
    have hnone : res = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    subst hnone
    refine ⟨?_, hmeta.trans (by simp [decClockHOLFinite]), hpostInv⟩
    -- the assignment runs and sets `x := w'`
    have hasg : evaluateHOLFiniteState (decClockHOLFinite s) (.assign .local x e) =
        (none, setKvarHOLFinite .local x (.val (.word w')) (decClockHOLFinite s)) := by
      rw [evaluateHOLFiniteState_assign]
      simp only [he]
      have hvalid : isValidValueHOLFinite (decClockHOLFinite s) .local x (.val (.word w')) = true := by
        have hxd : (decClockHOLFinite s).locals.lookup x = some (.val (.word w)) := by
          simpa [decClockHOLFinite] using hx
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hxd, shapeOfHOLExact,
          shapeEqHOL, toExact]
      rw [if_pos hvalid]
    rw [evaluateHOLFiniteState_seq_line780, hasg] at hacc
    dsimp only at hacc
    have hmid : (setKvarHOLFinite .local x (.val (.word w')) (decClockHOLFinite s)).locals.lookup x =
        some (.val (.word w')) := by
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hkeep := evaluate_avoidsLocal_flowing x rest hrest
      (setKvarHOLFinite .local x (.val (.word w')) (decClockHOLFinite s)) (by rw [hacc]; exact Or.inl rfl)
    rw [hacc] at hkeep
    dsimp only at hkeep
    unfold localMu
    rw [hkeep, hmid, hx]
    exact hlt
  intro F s hcode hP
  exact TerminatingProgBoundedOn.while_measure (localMu x) _ _ hstep s hcode
    ⟨hP, localMu_le x s⟩


theorem localDec_shr8 (v : MlS) :
    LocalDecreases (.cmp .notEqual (.var .local v) (.const 0)) v
      (.shift .lsr (.var .local v) (.const 8)) := by
  intro F s word hcond hw
  simp only [evalHOLExact] at hcond
  rcases hv : s.locals.lookup v with _ | vv <;> simp only [hv] at hcond
  · simp at hcond
  · rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> simp at hcond
    refine ⟨w, w >>> 8, rfl, ?_, ?_⟩
    · simp [evalHOLExact, decClockHOLFinite, hv, toExact]
      simp [wordShiftHOL]
    · have hw0 : w ≠ 0 := by
        intro h; subst h; simp [Compiler.Encoders.Asm.wordCmpHOL] at hcond; exact hw hcond.symm
      have hpos : 0 < w.toNat := by
        rcases Nat.eq_zero_or_pos w.toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hw0
        · exact h
      have h1 : (w >>> 8).toNat = w.toNat >>> 8 := by simp
      have h2 : w.toNat >>> 8 = w.toNat / 2 ^ 8 := Nat.shiftRight_eq_div_pow _ _
      omega

theorem localDec_sub1 (i : MlS) :
    LocalDecreases (.cmp .lower (.const 0) (.var .local i)) i
      (.op .sub [.var .local i, .const 1]) := by
  intro F s word hcond hw
  simp only [evalHOLExact] at hcond
  rcases hv : s.locals.lookup i with _ | vv <;> simp only [hv] at hcond
  · simp at hcond
  · rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> simp at hcond
    refine ⟨w, w - 1, rfl, ?_, ?_⟩
    · simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hv, toExact, valueIsWord, valueWord,
        wordOpHOL, wordOp]
    · have hlt : (0#64) < w := by
        by_contra hc
        simp [Compiler.Encoders.Asm.wordCmpHOL, hc] at hcond
        exact hw hcond.symm
      rw [BitVec.lt_def] at hlt
      simp only [BitVec.toNat_ofNat] at hlt
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
      simp
      omega

/-- Verbatim copy of step0 `PanTerminatingCombinators.tail_clock_of_body` (private there). -/
theorem tail_clock_of_body {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body, callee, returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result, post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call none function arguments)
    output.1 ≠ some .timeOut ∧ output.2.clock = post.clock := by
  dsimp only
  rw [evaluateHOLFiniteState_call, args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock, run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp

/-- Guarded tail call (`.call none`): step0's `TerminatingProgBounded.tailCall` with the callee
body bound taken from the spec's `callee_body_bound` under `GuestInv`. -/
theorem tailCall_guestInv {fname : MlS} {B : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B) (arguments : List (ExpHOL 64)) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) := by
  obtain ⟨params, fbody, ret, hlook, hbody⟩ := hf
  intro F state hcode hP
  unfold TerminatingRunBounded
  dsimp only
  intro hnt
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  cases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | some values =>
    rw [hargs] at hnt
    dsimp only at hnt ⊢
    cases hlookup : lookupCodeHOLFinite state.code.lookup fname values with
    | none => exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    | some found =>
      obtain ⟨body, callee, returnShape⟩ := found
      rw [hlookup] at hnt
      dsimp only at hnt ⊢
      by_cases hzero : state.clock = 0
      · rw [if_pos hzero] at hnt; exact absurd rfl hnt
      · rw [if_neg hzero] at hnt ⊢
        obtain ⟨_, hentry⟩ := callee_body_bound hlook hbody (callEntryOn_guestInv fname arguments)
          state hcode hP values body callee returnShape hargs hlookup
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
          ⟨result, post⟩
        rw [hrun] at hnt
        have hntBody : result ≠ some .timeOut := fun hbad => by subst hbad; simp at hnt
        have hbound := hentry (by rw [hrun]; exact hntBody)
        rw [hrun] at hbound
        obtain ⟨hspent, hkept⟩ := hbound
        have hpair := tail_clock_of_body state post fname arguments values body callee
          returnShape result hargs hlookup hzero hrun hntBody
        dsimp only at hpair
        rw [evaluateHOLFiniteState_call, hargs] at hpair
        dsimp only at hpair
        rw [hlookup] at hpair
        dsimp only at hpair
        rw [if_neg hzero, hrun] at hpair
        rw [hpair.2]
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        exact ⟨by omega, by omega⟩

theorem tailCall_guestInv' {fname : MlS} {B : Nat} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  tailCall_guestInv hf arguments

macro_rules
  | `(tactic| loop_auto) => `(tactic| (apply tailCall_guestInv'; known_fb))

def byteLen64 (n : Nat) : Nat :=
  if n = 0 then 0
  else if n < 2 ^ 8 then 1
  else if n < 2 ^ 16 then 2
  else if n < 2 ^ 24 then 3
  else if n < 2 ^ 32 then 4
  else if n < 2 ^ 40 then 5
  else if n < 2 ^ 48 then 6
  else if n < 2 ^ 56 then 7
  else 8

theorem byteLen64_le (n : Nat) : byteLen64 n ≤ 8 := by
  unfold byteLen64; split_ifs <;> omega

theorem byteLen64_div256 (n : Nat) (h0 : 0 < n) (h64 : n < 2 ^ 64) :
    byteLen64 (n / 2 ^ 8) < byteLen64 n := by
  unfold byteLen64; split_ifs <;> omega

def shr8Mu (x : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup x with
  | some (.val (.word w)) => byteLen64 w.toNat
  | _ => 0

theorem while_shr8 {v : MlS} {rest : ProgHOL 64}
    (hrest : avoidsLocal v rest = true)
    (hstraight : extStraightLine (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) = true)
    (hnc : noTopContinue (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) = true) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .notEqual (.var .local v) (.const 0))
        (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest))
      ((8 + 1) * (0 + 1)) := by
  have hstep : LoopStep (shr8Mu v) (.cmp .notEqual (.var .local v) (.const 0))
      (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) 0 GuestInv := by
    intro F s word hcode hP hcond hw hclk
    dsimp only
    intro hnt
    have hPd : GuestInv (decClockHOLFinite s) :=
      guestInv_congr (s := s) rfl rfl rfl rfl hP
    obtain ⟨w, w', hx, he, _⟩ := localDec_shr8 v s word hcond hw
    have hw0 : w ≠ 0 := by
      intro h; subst h; simp [ evalHOLExact, hx, Compiler.Encoders.Asm.wordCmpHOL ] at hcond; exact hw hcond.symm
    have hpos : 0 < w.toNat := by
      rcases Nat.eq_zero_or_pos w.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hw0
      · exact h
    have hw'_eq : w'.toNat = w.toNat / 2 ^ 8 := by
      have he2 : @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
          (fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
          (.shift .lsr (.var .local v) (.const 8)) = some (.val (.word (w >>> 8))) := by
        simp [evalHOLExact, decClockHOLFinite, hx, wordShiftHOL]
      rw [he] at he2
      cases he2
      change (w >>> 8).toNat = w.toNat / 2 ^ 8
      have h1 : (w >>> 8).toNat = w.toNat >>> 8 := by simp
      rw [h1, Nat.shiftRight_eq_div_pow]
    rcases hacc : evaluateHOLFiniteState (decClockHOLFinite s)
        (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) with ⟨res, post⟩
    have hpostInv : GuestInv post := by
      have := guestInv_evaluate (decClockHOLFinite s)
        (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest) hPd
      rw [hacc] at this; exact this
    have hclk' := TerminatingProgBounded.straight _ hstraight (decClockHOLFinite s) hcode
    have hnc' := evaluate_noTopContinue _ hnc (decClockHOLFinite s)
    have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s)
      (.seq (.assign .local v (.shift .lsr (.var .local v) (.const 8))) rest)).1
    unfold TerminatingRunBounded at hclk'
    rw [hacc] at hclk' hnc' hnt hmeta
    obtain ⟨c1, c2⟩ := hclk' hnt
    dsimp only at c1 c2 hnc' hmeta ⊢
    refine ⟨by simpa [decClockHOLFinite] using c1, by simpa [decClockHOLFinite] using c2,
      fun hflow => ?_⟩
    have hnone : res = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc'
    subst hnone
    refine ⟨?_, hmeta.trans (by simp [decClockHOLFinite]), hpostInv⟩
    have hasg : evaluateHOLFiniteState (decClockHOLFinite s)
        (.assign .local v (.shift .lsr (.var .local v) (.const 8))) =
        (none, setKvarHOLFinite .local v (.val (.word w')) (decClockHOLFinite s)) := by
      rw [evaluateHOLFiniteState_assign]
      simp only [he]
      have hvalid : isValidValueHOLFinite (decClockHOLFinite s) .local v (.val (.word w')) = true := by
        have hxd : (decClockHOLFinite s).locals.lookup v = some (.val (.word w)) := by
          simpa [decClockHOLFinite] using hx
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hxd, shapeOfHOLExact,
          shapeEqHOL, toExact]
      rw [if_pos hvalid]
    rw [evaluateHOLFiniteState_seq_line780, hasg] at hacc
    dsimp only at hacc
    have hmid : (setKvarHOLFinite .local v (.val (.word w')) (decClockHOLFinite s)).locals.lookup v =
        some (.val (.word w')) := by
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hkeep := evaluate_avoidsLocal_flowing v rest hrest
      (setKvarHOLFinite .local v (.val (.word w')) (decClockHOLFinite s)) (by rw [hacc]; exact Or.inl rfl)
    rw [hacc] at hkeep
    dsimp only at hkeep
    unfold shr8Mu
    rw [hkeep, hmid, hx]
    dsimp only
    rw [hw'_eq]
    exact byteLen64_div256 w.toNat hpos w.isLt
  intro F s hcode hP
  refine TerminatingProgBoundedOn.while_measure (shr8Mu v) _ _ hstep s hcode ⟨hP, ?_⟩
  unfold shr8Mu
  split
  · exact byteLen64_le _
  · exact Nat.zero_le _

macro_rules
  | `(tactic| loop_auto) => `(tactic|
      (apply while_shr8
       · rfl
       · rfl
       · rfl))

macro_rules
  | `(tactic| loop_auto) => `(tactic|
      (apply while_localDec
       · exact localDec_sub1 _
       · rfl
       · rfl
       · rfl))

end InitECandidate.Solver.Wave8Leaves.Rlp
