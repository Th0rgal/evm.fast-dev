import InitECandidate.Solver.Wave8Stage.WordCostEffectRules

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost

private theorem share_shape {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (reg : Nat) (address : BitVec width)
    (s : WordSemStateFiniteExact width C F)
    (ne : (shareInst (rw := width) op reg address s).1 ≠ some .error) :
    (shareInst (rw := width) op reg address s).1 = none ∨
      ∃ event, (shareInst (rw := width) op reg address s).1 = some (.finalFfi event) := by
  cases op <;>
    simp only [shareInst,shMemLoad,shMemLoadByte,shMemLoad16,shMemLoad32,
      shMemStore,shMemStoreByte,shMemStore16,shMemStore32,shMemSetVar] at ne ⊢ <;>
    (repeat' split at ne) <;> simp_all [shMemSetVar]

/-- Shared-memory instructions cost one extra tick on either successful
fallthrough or terminal FFI, for every shared-memory oracle. -/
theorem share_at {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (reg : Nat) (exp : WordLangExpHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    At (merge (atom .fall 1) (atom .final 1)) (.shareInst op reg exp) s := by
  intro ne nt
  have mono := (evaluate_clock_proj (.shareInst op reg exp) s).1
  have shape : (evaluate (.shareInst op reg exp) s).1 = none ∨
      ∃ event, (evaluate (.shareInst op reg exp) s).1 = some (.finalFfi event) := by
    rw [evaluate] at ne ⊢
    cases h : wordExp s exp with
    | none => simp only [h] at ne; exact (ne rfl).elim
    | some value =>
      cases value with
      | loc _ _ => simp only [h] at ne; exact (ne rfl).elim
      | word address => simpa only [h] using share_shape op reg address s (by simpa only [h] using ne)
  rcases shape with normal | ⟨event,final⟩
  · apply fits_merge_left
    simp only [Fits,netCost,normal,classify,atom,if_true,sourceCost,covers_some]
    omega
  · apply fits_merge_right
    simp only [Fits,netCost,final,classify,atom,if_true,sourceCost,covers_some]
    omega

def ffiEffects (terminal : Bool) : Effects :=
  if terminal then atom .final 0 else merge (atom .fall 0) (atom .final 0)

/-- The terminal flag requires a fact about the real oracle call. It is never
inferred merely from a syntactic FFI name. -/
theorem ffi_at {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString) (ptr1 len1 ptr2 len2 : Nat)
    (names : WordLangCutsetsHOL) (terminal : Bool)
    (s : WordSemStateFiniteExact width C F)
    (terminalCall : terminal = true → ∀ config bytes,
      ∃ event, callFFIHOL s.ffi (.extCall name) config bytes = .final event) :
    At (ffiEffects terminal) (.ffi name ptr1 len1 ptr2 len2 names) s := by
  intro ne nt
  have mono := (evaluate_clock_proj (.ffi name ptr1 len1 ptr2 len2 names) s).1
  have shape :
      ((evaluate (.ffi name ptr1 len1 ptr2 len2 names) s).1 = none ∧ terminal = false) ∨
      ∃ event, (evaluate (.ffi name ptr1 len1 ptr2 len2 names) s).1 = some (.finalFfi event) := by
    rw [evaluate] at ne ⊢
    cases h1 : getVar len1 s <;> cases h2 : getVar ptr1 s <;>
      cases h3 : getVar len2 s <;> cases h4 : getVar ptr2 s <;>
      simp only [h1,h2,h3,h4] at ne ⊢
    all_goals try exact (ne rfl).elim
    rename_i v1 v2 v3 v4
    cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> try exact (ne rfl).elim
    cases cut : wordSemCutEnv names s.locals with
    | none => simp only [cut] at ne; exact (ne rfl).elim
    | some env =>
      simp only [cut] at ne ⊢
      split at ne
      · rename_i bytes bytes2 r1 r2
        try simp only [r1,r2]
        cases oracle : callFFIHOL s.ffi (.extCall name) bytes bytes2 with
        | final event => simp [oracle]
        | ret ffi out =>
          have notTerminal : terminal = false := by
            cases terminal with
            | false => rfl
            | true =>
              obtain ⟨event,final⟩ := terminalCall rfl bytes bytes2
              rw [oracle] at final
              cases final
          simp [oracle,notTerminal]
      · exact (ne rfl).elim
  rcases shape with ⟨normal,nonterminal⟩ | ⟨event,final⟩
  · simp only [ffiEffects,nonterminal,Bool.false_eq_true,if_false]
    apply fits_merge_left
    simp only [Fits,netCost,normal,classify,atom,if_true,sourceCost,covers_some]
    omega
  · cases terminal with
    | false =>
      simp only [ffiEffects,Bool.false_eq_true,if_false]
      apply fits_merge_right
      simp only [Fits,netCost,final,classify,atom,if_true,sourceCost,covers_some]
      omega
    | true =>
      simp only [ffiEffects,if_true,Fits,netCost,final,classify,atom,if_true,sourceCost,covers_some]
      omega

end InitECandidate.Solver.Wave8Stage.WordCostEffects
