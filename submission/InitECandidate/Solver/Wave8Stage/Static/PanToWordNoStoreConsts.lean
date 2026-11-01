/- Extracted from PanToWordNoStoreConsts.lean (SHA256 ae50a93ccb8c41b202dabd71f804e7ea295562ce0a1b51b820f9c91081b77e58).
Only pure compiler facts retained; original sources and statements unchanged. -/
import Flapjack.Pancake.LoopToWord
import InitECandidate.Solver.SelfContainedStageBounds



set_option autoImplicit false

/-!
# LoopToWord never emits `storeConsts` (nor `alloc`)

Grep audit (non-proof files of Flapjack): `storeConsts` appears in Word passes
(`WordSimp`, `WordCse`, `WordCopy`, `WordRemove`, `WordAlloc/SSACcTrans`, `Colour`) only as a
pattern that rebuilds a `storeConsts` from a `storeConsts`; no Word pass introduces it from
another constructor. Here we machine-check the frontend half: `LoopToWord.compHOL` output is
`storeConsts`/`alloc`-free for every Loop program.
-/

namespace InitECandidate.Solver.Wave8Stage.Static.PanToWordNoStoreConsts

open Flapjack
open Flapjack.LoopToWord

/-- Syntactic predicate: no `storeConsts` and no `alloc` anywhere (incl. call bodies). -/
def NoSC {α : Type} : WordLangProgHOL α → Bool
  | .storeConsts .. => false
  | .alloc .. => false
  | .mustTerminate b => NoSC b
  | .seq a b => NoSC a && NoSC b
  | .ite _ _ _ a b => NoSC a && NoSC b
  | .loop _ b _ => NoSC b
  | .call ret _ _ h =>
      (match ret with | none => true | some (_, _, r, _, _) => NoSC r) &&
      (match h with | none => true | some (_, p, _, _) => NoSC p)
  | _ => true

theorem NoSC_storeConsts {α : Type} (a b c d : Nat) (ws : List (Bool × α)) :
    NoSC (WordLangProgHOL.storeConsts a b c d ws) = false := rfl

theorem NoSC_alloc {α : Type} (d : Nat) (c : WordLangCutsetsHOL) :
    NoSC (WordLangProgHOL.alloc (α := α) d c) = false := rfl

theorem NoSC_seq {α : Type} (a b : WordLangProgHOL α) :
    NoSC (.seq a b) = (NoSC a && NoSC b) := rfl

/-- Main result: every LoopToWord output satisfies `NoSC`. -/
theorem compHOL_NoSC {width : Nat} [NeZero width] (ctx : Spt Nat)
    (p : HolLoopProg width) (l : Nat × Nat) : NoSC (LoopToWord.compHOL ctx p l).1 = true := by
  induction p, l using LoopToWord.compHOL.induct (context := ctx) <;>
    (try simp_all [LoopToWord.compHOL, NoSC]) <;> (try split) <;> (try simp_all [NoSC])
  all_goals
    rename_i e1 e2 ih2 ih1
    first
      | (simp_all (config := {zetaDelta := true}) [NoSC]; done)
      | (unfold LoopToWord.compHOL; simp_all [NoSC]; done)
      | (rw [LoopToWord.compHOL.eq_def]; simp_all [NoSC])

/-- The whole-program image of LoopToWord (list of functions) is `NoSC`. -/
theorem compHOL_list_NoSC {width : Nat} [NeZero width] (ctx : Spt Nat) (l : Nat × Nat)
    (ps : List (HolLoopProg width)) :
    ∀ q ∈ ps.map (fun p => (LoopToWord.compHOL ctx p l).1), NoSC q = true := by
  intro q hq
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hq
  exact compHOL_NoSC ctx p l

/-- `NoSC` is a genuine restriction: a `storeConsts` nested in `seq` violates it. -/
theorem NoSC_nested_counterexample {α : Type} :
    NoSC (WordLangProgHOL.seq (α := α) .skip (.storeConsts 0 2 4 6 [])) = false := rfl

/-- `tick` and `skip` (what LoopToWord emits around loops/ifs) satisfy `NoSC`. -/
theorem NoSC_tick_skip {α : Type} :
    NoSC (WordLangProgHOL.tick (α := α)) = true ∧ NoSC (WordLangProgHOL.skip (α := α)) = true :=
  ⟨rfl, rfl⟩


end InitECandidate.Solver.Wave8Stage.Static.PanToWordNoStoreConsts
