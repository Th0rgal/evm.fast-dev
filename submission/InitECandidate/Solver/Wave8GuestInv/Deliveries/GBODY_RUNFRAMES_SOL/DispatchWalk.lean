import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.Base
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

structure DispatchWalk (p : ProgHOL 64) (k : Nat) : Prop where
  bound : TerminatingProgBoundedOn EvmRun p k
  keeps : Hoare EvmRun p (fun r t => r = none → EvmRun t)

theorem return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem seq_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p (.return e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  cases r with
  | none => exact return_ne_none t e
  | some r => simp

theorem DispatchWalk.skip : DispatchWalk .skip 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_skip s), Hoare.skip (fun _ hi _ => hi)⟩

theorem DispatchWalk.returned (e : ExpHOL 64) : DispatchWalk (.return e) 0 :=
  ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_return s e),
    ⟨fun s _ _ _ hn => (return_ne_none s e hn).elim⟩⟩

theorem DispatchWalk.raise (n : MlS) (e : ExpHOL 64) : DispatchWalk (.raise n e) 0 := by
  refine ⟨TerminatingProgBoundedOn.of_clock (fun s => clock_raise s n e), ?_⟩
  refine ⟨fun s _ _ _ hn => ?_⟩
  rw [evaluateHOLFiniteState_raise] at hn
  split at hn <;> dsimp only at hn
  · split at hn <;> simp_all
  · simp_all

theorem DispatchWalk.callReturn {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {b : Nat} (hf : TerminatingFunBoundedOn Pc fname b)
    (args : List (ExpHOL 64)) (e : ExpHOL 64) (hentry : CallEntryOn EvmRun Pc fname args) :
    DispatchWalk (.seq (.call (some (none, none)) fname args) (.return e)) (b + 1) := by
  refine ⟨?_, ⟨fun s _ _ _ hn => (seq_return_ne_none s _ e hn).elim⟩⟩
  have hb : TerminatingProgBoundedOn EvmRun _ _ := TerminatingProgBoundedOn.seq_guestInv_after
    (TerminatingProgBoundedOn.call_on hf none args hentry)
    (fun s hi => evmInv_guestInv s hi.1)
    (TerminatingProgBoundedOn.of_clock (fun s => clock_return s e))
  intro F s hc hi
  simpa only [Nat.add_zero] using hb s hc hi

theorem DispatchWalk.seq {p q : ProgHOL 64} {a b : Nat}
    (h1 : DispatchWalk p a) (h2 : DispatchWalk q b) : DispatchWalk (.seq p q) (a + b) := by
  refine ⟨?_, Hoare.seq
    ⟨fun s hc hi hnt => ⟨h1.keeps.run s hc hi hnt, fun hn hz => (hn hz).elim⟩⟩ h2.keeps⟩
  intro F state hcode hi hnt
  have hm := PanRunBounded.evaluateHOLFiniteState_metadata state p
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState state p with ⟨r, mid⟩
  simp only [hr] at hm hnt ⊢
  cases r with
  | none =>
    dsimp only at hnt ⊢
    have hn : (evaluateHOLFiniteState state p).1 ≠ some .timeOut := by simp [hr]
    have hp := h1.keeps.run state hcode hi hn
    rw [hr] at hp
    obtain ⟨s1, k1⟩ := h1.bound state hcode hi hn
    rw [hr] at s1 k1
    obtain ⟨s2, k2⟩ := h2.bound mid (hm.1.trans hcode) (hp rfl) hnt
    exact ⟨by dsimp only at s1; omega, by dsimp only at k1; omega⟩
  | some r =>
    dsimp only at hnt ⊢
    have hn : (evaluateHOLFiniteState state p).1 ≠ some .timeOut := by simpa [hr] using hnt
    obtain ⟨s1, k1⟩ := h1.bound state hcode hi hn
    rw [hr] at s1 k1
    exact ⟨by dsimp only at s1; omega, k1⟩

theorem DispatchWalk.ite (c : ExpHOL 64) {p q : ProgHOL 64} {a b : Nat}
    (h1 : DispatchWalk p a) (h2 : DispatchWalk q b) : DispatchWalk (.ite c p q) (max a b) :=
  ⟨TerminatingProgBoundedOn.ite_on h1.bound h2.bound,
    Hoare.ite (Hoare.mono h1.keeps (fun _ h => h.1))
      (Hoare.mono h2.keeps (fun _ h => h.1)) (fun _ _ h => by cases h)⟩

theorem dispatchEntry_guest (f : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn EvmRun GuestInv f args :=
  fun s _ _ callee _ _ hi _ _ => guestInv_callEntry s callee (evmInv_guestInv s hi.1)

theorem dispatchEntry_run (f : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn EvmRun EvmRun f args := by
  intro F s values body callee ret hc hi hargs hl
  exact ⟨evmInv_entry callee hi.1,
    fun hd => hi.2 ((evmDone_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).1 hd)⟩

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
