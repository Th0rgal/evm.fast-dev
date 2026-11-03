import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.DomainArithmetic
import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.CounterUp

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

/-- A successful evaluation of this expression returns one word. -/
def WordExpression (e : ExpHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
    ∃ w : BitVec 64, v = .val (.word w)

theorem WordExpression.const (w : BitVec 64) : WordExpression (.const w) := by
  intro F s v h
  cases h
  exact ⟨w, rfl⟩

theorem WordExpression.load (a : ExpHOL 64) : WordExpression (.load .one a) := by
  classical
  intro F s v h
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at h
  split at h
  · rename_i address ha
    simp only [memLoadHOLExact] at h
    split at h
    · cases hm : s.memory address with
      | word w => exact ⟨w, by simpa [hm] using h.symm⟩
    · cases h
  · cases h

/-- Every continuing run has evaluated the address inside the ordinary byte interval. -/
def DomainTouch (address : ExpHOL 64) (body : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s →
    ((evaluateHOLFiniteState s body).1 = none ∨ (evaluateHOLFiniteState s body).1 = some .continue) →
    ∃ a : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) address = some (.val (.word a)) ∧
      sourceBase ≤ a.toNat ∧ a.toNat < heapEnd

theorem DomainTouch.storeByte (address value : ExpHOL 64) :
    DomainTouch address (.storeByte address value) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_storeByte] at hflow
  split at hflow
  · rename_i addr haddr
    split at hflow
    · rename_i w hw
      split at hflow
      · rename_i memory hmem
        refine ⟨addr, haddr, ordinaryDomain_byte_interval addr ?_⟩
        unfold panMemStoreByteWord8HOL at hmem
        cases hm : s.memory (panByteAlignHOL addr) with
        | word cell =>
          simp only [hm] at hmem
          split at hmem
          · rename_i hd
            rw [hguest.memaddrs] at hd
            exact hd
          · cases hmem
      · simp at hflow
    · simp at hflow
  · simp at hflow

theorem DomainTouch.store (address value : ExpHOL 64) (hw : WordExpression value) :
    DomainTouch address (.store address value) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_store] at hflow
  split at hflow
  · rename_i addr haddr
    split at hflow
    · rename_i v hv
      obtain ⟨w, rfl⟩ := hw s v hv
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hflow
      by_cases hd : s.memaddrs addr
      · rw [hguest.memaddrs] at hd
        have hi := ordinaryDomain_interval addr hd
        exact ⟨addr, haddr, hi.1, by omega⟩
      · simp [hd] at hflow
    · simp at hflow
  · simp at hflow

theorem DomainTouch.seq (address : ExpHOL 64) (first rest : ProgHOL 64)
    (ht : DomainTouch address first) : DomainTouch address (.seq first rest) := by
  intro F s hguest hflow
  apply ht s hguest
  rw [evaluateHOLFiniteState_seq_line780] at hflow
  cases hfirst : evaluateHOLFiniteState s first with
  | mk result mid =>
    rw [hfirst] at hflow
    cases result with
    | none => exact Or.inl rfl
    | some result =>
      cases result <;> simp_all
end InitECandidate.Solver.Wave8GuestInv.Arith
