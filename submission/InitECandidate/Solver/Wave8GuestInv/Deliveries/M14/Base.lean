import InitECandidate.Solver.Wave8GuestInv.Defs
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! Light-cone read-only contract infrastructure for contract micro-shard m14 (`wave8/contracts-m14`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.Defs`,
`GuestTrapOutcomes`, and `Guest.SoftwareAst`.
Restates `FunSpec`, `Resumes`, and `ReadOnlyFn` verbatim from frozen revision 9
(`campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28bdd7a3522f8a9a81a892d9ecaabdeff`) so every
proved contract theorem is definitionally (`rfl`) equal to its spec statement, and proves
structural `ReadOnlyProg` combinators covering `skip`, `return`, `raise`, local `assign`,
`primitive`, `dec`, `seq`, `ite`, `while`, `call` (destination `none`), `decCall`, and `trap_with`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim contract definitions from frozen rev9 `GuestInv.lean` (`8a79d9f28`) -/

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ReadOnlyFn (fname : MlS) : Prop :=
  FunSpec GuestInv
    (fun s r post => Resumes r → post = { s with locals := post.locals, clock := post.clock })
    fname

/-! ## 2. Metadata preservation and state congruence helpers -/

theorem guestInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (h : GuestInv s) :
    GuestInv (decClockHOLFinite s) := by
  obtain ⟨c, m, sh, b⟩ := h
  exact ⟨c, m, sh, b⟩

/-- Outcome-sensitive read-only predicate on statements: every fallthrough, loop control, return,
or catchable (`≠ TrapErr`) exception leaves all fields other than `locals` and `clock` unchanged. -/
def FlowsOrResumes (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .break ∨ r = some .continue ∨ Resumes r

def ReadOnlyProg (prog : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode → GuestInv s →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    FlowsOrResumes (evaluateHOLFiniteState s prog).1 →
    (evaluateHOLFiniteState s prog).2 =
      { s with
        locals := (evaluateHOLFiniteState s prog).2.locals
        clock := (evaluateHOLFiniteState s prog).2.clock }

theorem state_eq_with_locals_clock {F : Type} {a b : PanSemStateFiniteExact 64 F}
    (h : a = { b with locals := a.locals, clock := a.clock })
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) :
    { a with locals := locals, clock := clock } = { b with locals := locals, clock := clock } := by
  cases a; cases b
  dsimp only at h
  injection h with _ hg hst hc he hm hma hsh _ hbe hffi hba hta
  subst hg hst hc he hm hma hsh hbe hffi hba hta
  rfl

theorem state_trans_locals_clock {F : Type} {s mid post : PanSemStateFiniteExact 64 F}
    (h1 : mid = { s with locals := mid.locals, clock := mid.clock })
    (h2 : post = { mid with locals := post.locals, clock := post.clock }) :
    post = { s with locals := post.locals, clock := post.clock } := by
  rw [h2]
  exact state_eq_with_locals_clock h1 post.locals post.clock

/-! ## 3. Structural `ReadOnlyProg` combinators -/

theorem ReadOnlyProg.skip : ReadOnlyProg .skip := by
  intro F s _ _ _ _
  rw [evaluateHOLFiniteState_skip]

theorem ReadOnlyProg.ret (e : ExpHOL 64) : ReadOnlyProg (.return e) := by
  intro F s _ _ _ _
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> (cases s; rfl)

theorem ReadOnlyProg.raise (eid : MlS) (e : ExpHOL 64) : ReadOnlyProg (.raise eid e) := by
  intro F s _ _ _ _
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> (cases s; rfl)
  · rfl

theorem ReadOnlyProg.assign_local (name : MlS) (e : ExpHOL 64) :
    ReadOnlyProg (.assign .local name e) := by
  intro F s _ _ _ _
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · simp only [setKvarHOLFinite, setVarHOLFinite]
    · rfl

theorem ReadOnlyProg.primitive (name : MlS) (op : PrimOp) (args : List (ExpHOL 64)) :
    ReadOnlyProg (.primitive name op args) := by
  intro F s _ _ _ _
  rw [evaluateHOLFiniteState_primitive]
  split
  · rfl
  · split
    · rfl
    · split
      · simp only [setVarHOLFinite]
      · rfl

theorem ReadOnlyProg.dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64} (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.dec name shape init body) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_dec_total] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · rfl
  · rename_i v hv
    by_cases hsh : shapeEqHOL shape (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
      have hb := hbody (setVarHOLFinite name v s) hcode (guestInv_setVar name v s hG) hnt hfr
      have hset : setVarHOLFinite name v s =
          { s with locals := (setVarHOLFinite name v s).locals, clock := s.clock } := by
        cases s; rfl
      have hcomb := state_trans_locals_clock hset hb
      exact state_eq_with_locals_clock hcomb _ _
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte]

theorem ReadOnlyProg.seq {first second : ProgHOL 64}
    (h1 : ReadOnlyProg first) (h2 : ReadOnlyProg second) :
    ReadOnlyProg (.seq first second) := by
  intro F s hcode hG hnt hfr
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s first).1
  have hGmid := guestInv_evaluate s first hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hGmid hnt hfr ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have hb1 := h1 s hcode hG (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at hb1
    dsimp only at hb1 hnt hfr ⊢
    have hb2 := h2 mid (hmeta.trans hcode) hGmid hnt hfr
    exact state_trans_locals_clock hb1 hb2
  | some r =>
    have hb1 := h1 s hcode hG (by rw [hr1]; exact hnt) (by rw [hr1]; exact hfr)
    rw [hr1] at hb1
    exact hb1

theorem ReadOnlyProg.ite (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hyes : ReadOnlyProg yes) (hno : ReadOnlyProg no) :
    ReadOnlyProg (.ite cond yes no) := by
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_ite] at hnt hfr ⊢
  revert hnt hfr
  split <;> intro hnt hfr
  · split at hnt
    · rename_i hz
      simp only [hz, ↓reduceIte] at hfr ⊢
      exact hno s hcode hG hnt hfr
    · rename_i hz
      simp only [hz, ↓reduceIte] at hfr ⊢
      exact hyes s hcode hG hnt hfr
  · cases s; rfl

theorem ReadOnlyProg.while_loop (cond : ExpHOL 64) {body : ProgHOL 64}
    (hbody : ReadOnlyProg body) :
    ReadOnlyProg (.while cond body) := by
  intro F s hcode hG hnt hfr
  generalize hk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    subst hk
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt hfr ⊢
    revert hnt hfr
    split <;> intro hnt hfr
    · rename_i w hw
      by_cases hnz : w = 0
      · subst hnz
        simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      · rw [if_pos hnz] at hnt hfr ⊢
        by_cases hclk : s.clock = 0
        · rw [if_pos hclk] at hnt
          simp at hnt
        · rw [if_neg hclk] at hnt hfr ⊢
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body).1
          have hGmid := guestInv_evaluate (decClockHOLFinite s) body (guestInv_decClock s hG)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          simp only [hrun] at hmeta hGmid hrem hnt hfr ⊢
          change mid.code = s.code at hmeta
          change mid.clock ≤ s.clock - 1 at hrem
          have hlt : mid.clock < s.clock := by omega
          have hdecEq : decClockHOLFinite s =
              { s with locals := s.locals, clock := (decClockHOLFinite s).clock } := by
            cases s; rfl
          cases r1 with
          | none =>
            have hb1 := hbody (decClockHOLFinite s) hcode (guestInv_decClock s hG)
              (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
            rw [hrun] at hb1
            have hmid := state_trans_locals_clock hdecEq hb1
            have hrec := ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl
            exact state_trans_locals_clock hmid hrec
          | some res =>
            cases res with
            | «continue» =>
              have hb1 := hbody (decClockHOLFinite s) hcode (guestInv_decClock s hG)
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hrun] at hb1
              have hmid := state_trans_locals_clock hdecEq hb1
              have hrec := ih mid.clock hlt mid (hmeta.trans hcode) hGmid hnt hfr rfl
              exact state_trans_locals_clock hmid hrec
            | «break» =>
              have hb1 := hbody (decClockHOLFinite s) hcode (guestInv_decClock s hG)
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inl rfl))
              rw [hrun] at hb1
              exact state_trans_locals_clock hdecEq hb1
            | timeOut =>
              simp at hnt
            | returned v =>
              have hb1 := hbody (decClockHOLFinite s) hcode (guestInv_decClock s hG)
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hrun] at hb1
              exact state_trans_locals_clock hdecEq hb1
            | exception e v =>
              have hres : Resumes (some (.exception e v)) := by
                rcases hfr with h | h | h | hr
                · simp at h
                · simp at h
                · simp at h
                · exact hr
              have hb1 := hbody (decClockHOLFinite s) hcode (guestInv_decClock s hG)
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inr (Or.inr (Or.inr hres)))
              rw [hrun] at hb1
              exact state_trans_locals_clock hdecEq hb1
            | error =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
            | finalFfi _ =>
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
    · rfl

/-- `trap_with` never resumes (`Resumes` excludes `TrapErr`, `error`, and `finalFfi`), so any
handler-free call to `trap_with` satisfies `ReadOnlyProg` vacuously! -/
theorem ReadOnlyProg.call_trap_with (args : List (ExpHOL 64)) :
    ReadOnlyProg (.call (some (none, none)) (ofString "trap_with") args) := by
  intro F s hcode _ hnt hfr
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "trap_with") values with
      _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "trap_with")
          [(ofString "code", .one)] (sourceFnBody Guest.Software.guestFn_trap_with) body'
          .one ret' values callee (by rw [hcode]; exact lookup_trap_with) hl
        subst hsame
        have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite s callee)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, post⟩
        simp only [hrun] at hout hnt hfr ⊢
        obtain ⟨hnone, hret, hexn⟩ := hout
        cases res with
        | none => exact absurd rfl hnone
        | some r =>
          cases r with
          | returned v => exact absurd rfl (hret v)
          | exception eid v =>
            dsimp only at hfr
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨e', v', h, hne⟩⟩
            · simp at h
            · simp at h
            · simp at h
            · simp at h
            · injection h with h'
              injection h' with he _
              subst he
              exact absurd rfl (hexn eid v hne)
          | timeOut => simp at hnt
          | «break» =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | «continue» =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | error =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | finalFfi _ =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

theorem ReadOnlyProg.decCall {fname : MlS} (hf : ReadOnlyFn fname)
    (name : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ReadOnlyProg cont) :
    ReadOnlyProg (.decCall name shape fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro F s hcode hG hnt hfr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hfr ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rfl
  · simp only [hargs] at hnt hfr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rfl
    · simp only [hl] at hnt hfr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hfr ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hmeta hnt hfr ⊢
        change post.code = s.code at hmeta
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        cases res with
        | none =>
          rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hfr ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hfr ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG)
                (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro
              dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let postCaller : PanSemStateFiniteExact 64 F :=
                { locals := s.locals, globals := post.globals, structs := post.structs,
                  code := post.code, eshapes := post.eshapes, memory := post.memory,
                  memaddrs := post.memaddrs, shMemaddrs := post.shMemaddrs, clock := post.clock,
                  be := post.be, ffi := post.ffi, baseAddr := post.baseAddr,
                  topAddr := post.topAddr }
              let cstate : PanSemStateFiniteExact 64 F := setVarHOLFinite name v postCaller
              have hcstateEq : cstate =
                  { s with locals := cstate.locals, clock := cstate.clock } := by
                have h1 : postCaller = { s with locals := s.locals, clock := post.clock } :=
                  state_eq_with_locals_clock hpost s.locals post.clock
                have h2 : cstate =
                    { postCaller with locals := cstate.locals, clock := cstate.clock } := by
                  dsimp only [cstate]
                  cases postCaller; rfl
                exact state_trans_locals_clock (by rw [h1]) h2
              have hGcstate : GuestInv cstate := by
                have hGpost : GuestInv post := by
                  have := guestInv_evaluate (callEntryStateHOLFinite s callee) body'
                    (guestInv_callEntry s callee hG)
                  rw [hrun] at this
                  exact this
                exact guestInv_setVar name v postCaller
                  (guestInv_with_locals_clock post s.locals post.clock hGpost)
              have hcCode : cstate.code = originalRuntimeCode := hGcstate.code
              have hbcont := hcont cstate hcCode hGcstate hnt hfr
              have hcomb := state_trans_locals_clock hcstateEq hbcont
              exact state_eq_with_locals_clock hcomb _ _
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hfr
              rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | exception e v =>
            have hres : Resumes (some (.exception e v)) := by
              rcases hfr with h | h | h | hr
              · simp at h
              · simp at h
              · simp at h
              · exact hr
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG)
              (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro
            dsimp only at hro
            have hpost : post = { s with locals := post.locals, clock := post.clock } :=
              state_trans_locals_clock hentryEq hro
            exact state_eq_with_locals_clock hpost _ post.clock
          | timeOut => simp at hnt
          | «break» =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | «continue» =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | error =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h
          | finalFfi _ =>
            rcases hfr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> simp at h

/-! ## 4. Packaging a `ReadOnlyProg` body as a `ReadOnlyFn` theorem -/

theorem readOnlyFn_of_guestAst
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64))
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : ReadOnlyProg
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    ReadOnlyFn (ofString (extractFn d).name) := by
  refine ⟨(extractFn d).params.map InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape,
    originalRuntimeCode_lookup_of_guestAst_getElem i hi (extractFn d) hd, ?_⟩
  intro F s hcode hG hnt hres
  exact hprog s hcode hG hnt (Or.inr (Or.inr (Or.inr hres)))

end InitECandidate.Solver.Wave8Contracts.M14
