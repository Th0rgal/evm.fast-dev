import InitECandidate.Solver.Wave8Stage.WordCostControl

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordCostEffects
open Flapjack WordSemStateFiniteExact WordToStackSourceCost

/-- None excludes a result; a finite signed bound retains credit from ticks. -/
abbrev Budget := Option Int

def Covers (bound : Budget) (cost : Int) : Prop :=
  ∃ value, bound = some value ∧ cost ≤ value

def join : Budget → Budget → Budget
  | none,b => b
  | a,none => a
  | some a,some b => some (max a b)

def add : Budget → Budget → Budget
  | some a,some b => some (a+b)
  | _,_ => none

@[simp] theorem covers_none (cost : Int) : ¬ Covers none cost := by
  simp [Covers]

@[simp] theorem covers_some (value cost : Int) : Covers (some value) cost ↔ cost ≤ value := by
  simp [Covers]

theorem covers_mono {bound : Budget} {first second : Int}
    (h : Covers bound first) (le : second ≤ first) : Covers bound second := by
  obtain ⟨value,equal,bound⟩ := h
  exact ⟨value,equal,by omega⟩

theorem covers_join_left (a b : Budget) (cost : Int) (h : Covers a cost) :
    Covers (join a b) cost := by
  obtain ⟨value,rfl,bound⟩ := h
  cases b with
  | none => exact ⟨value,rfl,bound⟩
  | some other => exact ⟨max value other,rfl,by have := Int.le_max_left value other; omega⟩

theorem covers_join_right (a b : Budget) (cost : Int) (h : Covers b cost) :
    Covers (join a b) cost := by
  obtain ⟨value,rfl,bound⟩ := h
  cases a with
  | none => exact ⟨value,rfl,bound⟩
  | some other => exact ⟨max other value,rfl,by have := Int.le_max_right other value; omega⟩

theorem covers_add (a b : Budget) (first second : Int)
    (ha : Covers a first) (hb : Covers b second) :
    Covers (add a b) (first+second) := by
  obtain ⟨va,rfl,ha⟩ := ha
  obtain ⟨vb,rfl,hb⟩ := hb
  exact ⟨va+vb,rfl,by omega⟩

inductive Exit where
  | fall | returned | raised | final | breakTo (label : Nat) | continueTo (label : Nat) | invalid
  deriving DecidableEq, Repr

abbrev Effects := Exit → Budget

def atom (exit : Exit) (value : Int) : Effects :=
  fun actual => if actual = exit then some value else none

def merge (a b : Effects) : Effects := fun exit => join (a exit) (b exit)

def shift (amount : Budget) (a : Effects) : Effects := fun exit => add amount (a exit)

/-- Only normal fallthrough reaches the second fragment. A terminal result
keeps the first fragment's bound and cannot spend later tick credits. -/
def seq (a b : Effects) : Effects := fun exit =>
  join (if exit = .fall then none else a exit) (add (a .fall) (b exit))

def classify {width : Nat} [NeZero width] : Option (WordSemResult width) → Exit
  | none => .fall
  | some (.result ..) => .returned
  | some (.exception ..) => .raised
  | some (.finalFfi _) => .final
  | some (.break label) => .breakTo label
  | some (.continue label) => .continueTo label
  | _ => .invalid

theorem classify_some_ne_fall {width : Nat} [NeZero width] (r : WordSemResult width) :
    classify (some r) ≠ .fall := by
  cases r <;> simp [classify]

/-- Raw additional Stack cost minus actual consumed Word ticks. -/
noncomputable def netCost {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Int :=
  (sourceCost p s : Int) + ((evaluate p s).2.clock : Int) - (s.clock : Int)

noncomputable def Fits {width : Nat} [NeZero width] {C F : Type}
    (effects : Effects) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  Covers (effects (classify (evaluate p s).1)) (netCost p s)

noncomputable def At {width : Nat} [NeZero width] {C F : Type}
    (effects : Effects) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  (evaluate p s).1 ≠ some .error → (evaluate p s).1 ≠ some .timeOut → Fits effects p s

/-- Semantic sequencing rule for the actual source-cost counter and evaluator.
Negative normal credits are used only when the first fragment falls through. -/
theorem seq_at {width : Nat} [NeZero width] {C F : Type}
    (a b : Effects) (first second : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (left : At a first s)
    (right : ∀ post, evaluate first s = (none,post) → At b second post) :
    At (seq a b) (.seq first second) s := by
  intro notError notTimeout
  rcases run : evaluate first s with ⟨r,t⟩
  have whole : evaluate (.seq first second) s =
      match (generalizing := false) r with | none => evaluate second t | some _ => (r,t) := by
    rw [evaluate,fix_clock_evaluate]
    simp only [run]
    cases r <;> rfl
  have costSeq : sourceCost (.seq first second) s = sourceCost first s +
      (match (generalizing := false) r with | none => sourceCost second t | some _ => 0) := by
    rw [sourceCost]
    split
    rename_i result post otherRun
    have equal := Prod.mk.inj (otherRun.symm.trans run)
    obtain ⟨rfl,rfl⟩ := equal
    cases result <;> rfl
  have ne : r ≠ some .error := by
    intro bad
    subst r
    exact notError (by rw [whole])
  have nt : r ≠ some .timeOut := by
    intro bad
    subst r
    exact notTimeout (by rw [whole])
  have hleft := left (by rw [run]; exact ne) (by rw [run]; exact nt)
  simp only [Fits,netCost,run] at hleft
  cases r with
  | none =>
    have hr := right t run (by simpa only [whole] using notError)
      (by simpa only [whole] using notTimeout)
    simp only [Fits,netCost] at hr
    have combined := covers_add (a .fall) (b (classify (evaluate second t).1)) _ _ hleft hr
    have joined := covers_join_right
      (if classify (evaluate second t).1 = .fall then none else a (classify (evaluate second t).1))
      _ _ combined
    simp only [Fits,netCost,whole,costSeq,Int.natCast_add,seq]
    apply covers_mono joined
    omega
  | some result =>
    have joined := covers_join_left _ (add (a .fall) (b (classify (some result)))) _ hleft
    simp only [Fits,netCost,whole,costSeq,Nat.add_zero]
    simp only [seq,if_neg (classify_some_ne_fall result)]
    exact joined

/-- Every explicit source tick supplies one unit of normal credit. -/
theorem tick_at {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) : At (atom .fall (-1)) .tick s := by
  intro notError notTimeout
  by_cases zero : s.clock = 0
  · simp [evaluate,zero] at notTimeout
  · simp only [Fits,netCost,evaluate,zero,if_false,sourceCost,classify,atom,if_true]
    apply (covers_some _ _).mpr
    dsimp only [decClock]
    omega

end InitECandidate.Solver.Wave8Stage.WordCostEffects
