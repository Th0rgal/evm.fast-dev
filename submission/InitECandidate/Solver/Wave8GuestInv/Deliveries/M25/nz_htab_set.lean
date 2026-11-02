import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! `nz_htab_set`: `htab_set(t, key, value)` resumes only on a nonzero table (`load(t + 0)`
errors at `0`, AST line 5156).
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M25

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def FunSpec_nz (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def Resumes_nz (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def ArgNonNull (x : String) (fname : MlS) : Prop :=
  FunSpec_nz GuestInv (fun s r _ => Resumes_nz r → locN s x ≠ 0) fname

private theorem lookup_htab_set :
    originalRuntimeCode.lookup (ofString "htab_set") =
      some ([(ofString "t", .one), (ofString "key", .one), (ofString "value", .one)],
        sourceFnBody Guest.Software.guestFn_htab_set, .one) :=
  lookup_of_guestAst_getElem 138 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_set) rfl

private theorem not_resumes_error : ¬ Resumes_nz (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem addresses_ge_base (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]; omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

private theorem not_ordinaryDomain_zero : ¬ ordinaryDomain (0 : BitVec 64) := by
  intro h
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have hge := addresses_ge_base _ _ 0 (by rw [hs]; decide) h
  rw [hs] at hge
  simp at hge

private theorem htab_set_head_eq :
    ∃ rest : ProgHOL 64,
      sourceFnBody Guest.Software.guestFn_htab_set =
        .dec (ofString "klen") .one (.load .one (.op .add [.var .local (ofString "t"), .const 0])) rest :=
  ⟨_, rfl⟩

/-- `htab_set` (AST line 5149): resumes only on a nonzero table (`load(t + 0)` errors at `0`, AST 5156). -/
theorem «nz_htab_set» :
    ArgNonNull "t" (ofString "htab_set") := by
  refine ⟨_, _, _, lookup_htab_set, ?_⟩
  intro F s _hcode hginv _ _hnt hres hzero
  obtain ⟨rest, hbody⟩ := htab_set_head_eq
  rw [hbody, evaluateHOLFiniteState_dec_total] at hres
  dsimp only at hres
  rcases ht : s.locals.lookup (ofString "t") with _ | vt
  · simp [evalHOLExact, evalListHOLExact, ht] at hres
    exact not_resumes_error hres
  · rcases vt with ⟨⟨tw⟩⟩ | fs | ⟨nm, fs⟩
    · have htw0 : tw = 0 := by
        apply BitVec.eq_of_toNat_eq
        simpa [locN, ht] using hzero
      subst htw0
      have hdom0 : ¬ s.memaddrs 0#64 := by
        rw [hginv.memaddrs]
        exact not_ordinaryDomain_zero
      have hev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "t"), .const 0])) = none := by
        simp [evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
          memLoadHOLExact, panMemLoadHOL, hdom0]
      rw [hev] at hres
      exact not_resumes_error hres
    · simp [evalHOLExact, evalListHOLExact, ht, valueIsWord] at hres
      exact not_resumes_error hres
    · have ht' : s.locals.lookup (ofString "t") = some (.nStruct nm fs) := ht
      simp [evalHOLExact, evalListHOLExact, ht', valueIsWord] at hres
      exact not_resumes_error hres

end InitECandidate.Solver.Wave8Contracts.M25
