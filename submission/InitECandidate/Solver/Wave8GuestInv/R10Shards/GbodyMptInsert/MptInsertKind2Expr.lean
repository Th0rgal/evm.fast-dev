import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind2Code

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evalAt_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (locN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.locals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [locN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `local + k` that succeeds yields the word `memW t (locN t g + k)`. -/
theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.locals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadL' t g k a h⟩

theorem locN_lt {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) :
    locN s n < 2 ^ 64 := by
  unfold locN
  split
  · exact BitVec.isLt _
  · decide

theorem condTrue_eq {F : Type} {s : PanSemStateFiniteExact 64 F} {l r : ExpHOL 64}
    (h : CondTrue (.cmp .equal l r) s) :
    ∃ a : BitVec 64, evalAt s l = some (.val (.word a)) ∧ evalAt s r = some (.val (.word a)) := by
  obtain ⟨w, hw, hz⟩ := h
  obtain ⟨a, b, ha, hb, he⟩ := evalAt_cmp s .equal l r w hw
  by_cases hab : a = b
  · subst b
    exact ⟨a, ha, hb⟩
  · have : w = 0 := by simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hab] using he
    exact False.elim (hz this)

theorem condFalse_eq {F : Type} {s : PanSemStateFiniteExact 64 F} {l r : ExpHOL 64}
    (h : CondFalse (.cmp .equal l r) s) :
    ∃ a b : BitVec 64, evalAt s l = some (.val (.word a)) ∧
      evalAt s r = some (.val (.word b)) ∧ a ≠ b := by
  obtain ⟨a, b, ha, hb, he⟩ := evalAt_cmp s .equal l r 0 h
  refine ⟨a, b, ha, hb, ?_⟩
  rintro rfl
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at he

theorem condTrue_local_eq_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {k : Nat} (h : CondTrue (.cmp .equal (lv n) (constant k)) s) :
    locN s n = k % 2 ^ 64 := by
  obtain ⟨a, ha, hb⟩ := condTrue_eq h
  cases RunFramesRace.evalAt_const s (BitVec.ofNat 64 k) _ hb
  exact (RunFramesRace.evalAt_local s n _ ha).symm

theorem condFalse_local_eq_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {k : Nat} (h : CondFalse (.cmp .equal (lv n) (constant k)) s) :
    locN s n ≠ k % 2 ^ 64 := by
  obtain ⟨a, b, ha, hb, hne⟩ := condFalse_eq h
  cases RunFramesRace.evalAt_const s (BitVec.ofNat 64 k) _ hb
  intro he
  apply hne
  apply BitVec.eq_of_toNat_eq
  exact (RunFramesRace.evalAt_local s n _ ha).trans he

theorem eval_add_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : String) (v : ValueHOL 64)
    (he : evalAt s (.op .add [lv d, lv i]) = some v) :
    ∃ x y : BitVec 64, s.locals.lookup (ofString d) = some (.val (.word x)) ∧
      s.locals.lookup (ofString i) = some (.val (.word y)) ∧ v = .val (.word (x + y)) := by
  simp only [lv, evalAt, evalHOLExact, evalListHOLExact] at he
  rcases hd : s.locals.lookup (ofString d) with _ | vd <;>
    rcases hi : s.locals.lookup (ofString i) with _ | vi <;> simp only [hd, hi] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vd with ⟨⟨x⟩⟩ | _ | _ <;> rcases vi with ⟨⟨y⟩⟩ | _ | _ <;>
      simp [valueIsWord] at he
    refine ⟨x, y, rfl, rfl, ?_⟩
    simp [valueWord, wordOpHOL, wordOp] at he
    exact he.symm

theorem eval_sub_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : String) (v : ValueHOL 64)
    (he : evalAt s (.op .sub [lv d, lv i]) = some v) :
    ∃ x y : BitVec 64, s.locals.lookup (ofString d) = some (.val (.word x)) ∧
      s.locals.lookup (ofString i) = some (.val (.word y)) ∧ v = .val (.word (x - y)) := by
  simp only [lv, evalAt, evalHOLExact, evalListHOLExact] at he
  rcases hd : s.locals.lookup (ofString d) with _ | vd <;>
    rcases hi : s.locals.lookup (ofString i) with _ | vi <;> simp only [hd, hi] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vd with ⟨⟨x⟩⟩ | _ | _ <;> rcases vi with ⟨⟨y⟩⟩ | _ | _ <;>
      simp [valueIsWord] at he
    refine ⟨x, y, rfl, rfl, ?_⟩
    simp [valueWord, wordOpHOL, wordOp] at he
    exact he.symm

noncomputable abbrev evalArgs {F : Type} (s : PanSemStateFiniteExact 64 F) (es : List (ExpHOL 64)) :=
  @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es

theorem args_cons {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {es : List (ExpHOL 64)} {values : List (ValueHOL 64)}
    (h : evalArgs s (e :: es) = some values) :
    ∃ v vs, evalAt s e = some v ∧ evalArgs s es = some vs ∧ values = v :: vs := by
  simp only [evalArgs, evalListHOLExact] at h
  split at h
  · rename_i v vs hv hvs
    exact ⟨v, vs, hv, hvs, (Option.some.inj h).symm⟩
  · cases h

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertKind2
