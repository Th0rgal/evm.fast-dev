import InitECandidate.Solver.Wave8GuestInv.Deliveries.RLP.RlpWalk

/-! RLP / byte-decoding family, part 2: strict local counters, call composition, small leaves.

`while_ctr` is the strict-counter rule (`while i < n`, body steps `i := i + 1`, `n` untouched),
an instance of step0's `while_measure` with measure `n - i ≤ 2^64` for arbitrary memory. -/

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

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

/-! ### Strict local counter `while i < n` -/

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

/-! ### Calls -/

theorem call_guestInv' {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv hf destination arguments

theorem decCall_guestInv' {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv hf name shape arguments hcont

open Lean Elab Tactic Meta in
/-- Close `TerminatingFunBoundedOn GuestInv (ofString "f") B` with the leaf `fb_f` of this
namespace (selected syntactically from the string literal, no unification over names). -/
elab "known_fb" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some e := t.find? (fun e => e.isAppOfArity ``Flapjack.Basis.Pure.MlString.ofString 1 &&
      e.appArg!.isStringLit) | throwError "known_fb: no function name in goal"
  let .lit (.strVal name) := e.appArg! | throwError "known_fb: not a literal"
  let full := Name.mkStr `InitECandidate.Solver.Wave8Leaves.Rlp ("fb_" ++ name)
  unless (← getEnv).contains full do throwError "known_fb: {full} not proved yet"
  evalTactic (← `(tactic| exact $(mkIdent full):ident))

/-- Loop rules; extended by later files with further `macro_rules`. -/
syntax "loop_auto" : tactic
macro_rules
  | `(tactic| loop_auto) => `(tactic|
      (apply while_walk'
       · counted_auto
       · access_auto
       · rfl
       · rfl
       · rfl
       · decide
       · decide))
macro_rules
  | `(tactic| loop_auto) => `(tactic|
      (apply while_ctr'
       · counted_auto
       · rfl
       · rfl
       · rfl))

/-- Structural bound: straight-line code, `seq`, `ite`, `dec`, walks, strict counters, calls. -/
syntax "fb_auto" : tactic
macro_rules
  | `(tactic| fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto
         · fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto
         · fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; known_fb)
      | (apply decCall_guestInv'
         · known_fb
         · fb_auto)
      | loop_auto)

/-- Look up `fname` at index `idx` of `guestAst` and unfold its HOL body. -/
syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]))

open Lean Elab Tactic Meta in
/-- Generalize every remaining `K.«g»` constant of the goal into an opaque variable. -/
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8GuestInv.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

/-- Close `bound ≤ K.f` (callee bounds stay atoms; walks use `domainBytes + 2 ≤ 2^64 + 1`). -/
syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       omega))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

/-! ### Lifted cone bounds (total `FunBounded`, `GuestUniformClockBound`) -/

theorem «fb_trap_with» : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» :=
  fbOn_of_funBounded funBounded_trap_with (by decide)
theorem «fb_alloc» : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» :=
  fbOn_of_funBounded funBounded_alloc (by decide)
theorem «fb_scratch_alloc» : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc» :=
  fbOn_of_funBounded funBounded_scratch_alloc (by decide)
theorem «fb_scratch_mark» : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark» :=
  fbOn_of_funBounded funBounded_scratch_mark (by decide)
theorem «fb_scratch_release» : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release» :=
  fbOn_of_funBounded funBounded_scratch_release (by decide)
theorem «fb_ld_be64» : TerminatingFunBoundedOn GuestInv (ofString "ld_be64") K.«ld_be64» :=
  fbOn_of_funBounded funBounded_ld_be64 (by decide)
theorem «fb_st_le32» : TerminatingFunBoundedOn GuestInv (ofString "st_le32") K.«st_le32» :=
  fbOn_of_funBounded funBounded_st_le32 (by decide)
theorem «fb_st_le64» : TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64» :=
  fbOn_of_funBounded funBounded_st_le64 (by decide)


/-! ### Small leaves -/

/-- `rlp_fail` (AST line 4305): loop-free. -/
theorem «fb_rlp_fail» : TerminatingFunBoundedOn GuestInv (ofString "rlp_fail") K.«rlp_fail» := by
  fb_prove 105 Guest.Software.guestFn_rlp_fail K.«rlp_fail»

/-- `mpt_fail` (AST line 9769): loop-free. -/
theorem «fb_mpt_fail» : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail» := by
  fb_prove 246 Guest.Software.guestFn_mpt_fail K.«mpt_fail»

/-- `rlp_read_length` (AST line 4317): #0 WALK (`p + i`). -/
theorem «fb_rlp_read_length» :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_read_length") K.«rlp_read_length» := by
  fb_unfold 106 Guest.Software.guestFn_rlp_read_length
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · exact call_guestInv' fb_rlp_fail
      · exact straightOn _ rfl
    · apply dec_guestInv
      apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · apply while_walk'
        · counted_auto
        · access_auto
        · rfl
        · rfl
        · rfl
        · decide
        · decide
      · exact straightOn _ rfl
  · fb_arith K.«rlp_read_length»

end InitECandidate.Solver.Wave8Leaves.Rlp
