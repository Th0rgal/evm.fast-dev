import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryStructRead

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators

private theorem scaled_locals_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const 32]]) = some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧ address = b + i * 32 := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w <;> simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
    | nStruct _ _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w <;> simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, panOpHOL] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using h.symm

private def scaledMemoryWalkRank (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => domainRank (b + i * 32)
  | _, _ => 0

private theorem scaledMemoryWalkRank_bound (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaledMemoryWalkRank base counter s ≤ domainBytes + 1 := by
  unfold scaledMemoryWalkRank
  split
  · exact domainRank_bound _
  · omega

/-- A memory access before each increment bounds the loop by the source-domain size. -/
theorem while_scaled_memory_walk (base counter : MlS) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBounded body B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 32]]) body)
    (hadd : CounterAdd counter 1 body)
    (hbase : avoidsLocal base body = true) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 1 + 1) * (B + 1)) := by
  have hentry : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s → GuestInv (decClockHOLFinite s) :=
    fun s h => guestInv_congr (s := s) rfl rfl rfl rfl h
  have hs : LoopStep (scaledMemoryWalkRank base counter) condition body B GuestInv := by
    apply while_step_of_progBoundedOn GuestInv (scaledMemoryWalkRank base counter) condition
      (fun s hcode _ => hbody s hcode) hentry
    intro F s word hcode hguest hcond hnz hclock
    dsimp only
    intro hflow
    have hguest' := hentry s hguest
    obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
    obtain ⟨b, i, hb, hi, rfl⟩ := scaled_locals_inv (decClockHOLFinite s) base counter addr haddr
    have hipost := hadd (decClockHOLFinite s) i hi hflow
    have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
      (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
    change s.locals.lookup base = some (.val (.word b)) at hb
    change s.locals.lookup counter = some (.val (.word i)) at hi
    have hbpost' := hbpost.trans hb
    refine ⟨?_, guestInv_evaluate (decClockHOLFinite s) body hguest'⟩
    simp only [scaledMemoryWalkRank, hipost, hbpost', hb, hi]
    have heq : b + (i + 1) * 32 = (b + i * 32) + BitVec.ofNat 64 32 := by
      rw [BitVec.add_mul, BitVec.add_assoc]
      congr 2
    rw [heq]
    exact domainRank_add_lt (b + i * 32) 32 ⟨hlow, hhigh⟩ (by decide) (by decide)
  intro F s hcode hguest
  exact TerminatingProgBoundedOn.while_measure (scaledMemoryWalkRank base counter) condition body hs
    s hcode ⟨hguest, scaledMemoryWalkRank_bound base counter s⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
