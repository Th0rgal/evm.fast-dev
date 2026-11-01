import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Body

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanRunBounded

theorem mpt_seq_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64} (h : evaluateHOLFiniteState s (.seq a b) = (none, t)) :
    ∃ u, evaluateHOLFiniteState s a = (none, u) ∧ evaluateHOLFiniteState u b = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases he : evaluateHOLFiniteState s a with ⟨r, u⟩
  rw [he] at h
  cases r with
  | none => exact ⟨u, rfl, h⟩
  | some r => cases h

theorem mpt_dec_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64} {body : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec name shape e body) = (none, t)) :
    ∃ v u, evalAt s e = some v ∧ shapeEqHOL shape (shapeOfHOLExact v) = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name v s) body = (none, u) ∧
      t = {u with locals := HolFiniteMapExact.resVarEq u.locals (name, s.locals.lookup name)} := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  rcases hv : evalAt s e with _ | v
  · simp only [evalAt] at hv
    rw [hv] at h; cases h
  · simp only [evalAt] at hv
    rw [hv] at h
    dsimp only at h
    by_cases hs : shapeEqHOL shape (shapeOfHOLExact v) = true
    · rw [if_pos hs] at h
      rcases he : evaluateHOLFiniteState (setVarHOLFinite name v s) body with ⟨r, u⟩
      rw [he] at h
      obtain ⟨rfl, ht⟩ := Prod.mk.inj h
      exact ⟨v, u, rfl, hs, he, ht.symm⟩
    · rw [if_neg hs] at h; cases h

theorem mpt_ite_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {yes no : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.ite e yes no) = (none, t)) :
    ∃ w : BitVec 64, evalAt s e = some (.val (.word w)) ∧
      (if w = 0 then evaluateHOLFiniteState s no else evaluateHOLFiniteState s yes) = (none, t) := by
  rw [evaluateHOLFiniteState_ite] at h
  split at h
  · rename_i w hw
    exact ⟨w, hw, h⟩
  · cases h

def MptLocalWord {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))

theorem mpt_assign_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (e : ExpHOL 64) (w : BitVec 64) (hl : MptLocalWord s name)
    (he : evalAt s e = some (.val (.word w))) :
    evaluateHOLFiniteState s (.assign .local (ofString name) e) =
      (none, setVarHOLFinite (ofString name) (.val (.word w)) s) := by
  obtain ⟨v, hv⟩ := hl
  simp only [evalAt] at he
  rw [evaluateHOLFiniteState_assign, he]
  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hv, shapeOfHOLExact, shapeEqHOL,
    setKvarHOLFinite]

theorem mptLocalWord_setVar {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name other : String) (w : BitVec 64) (h : MptLocalWord s name) :
    MptLocalWord (setVarHOLFinite (ofString other) (.val (.word w)) s) name := by
  by_cases he : ofString name = ofString other
  · refine ⟨w, ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he]
  · obtain ⟨v, hv⟩ := h
    refine ⟨v, ?_⟩
    simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, he, Ne.symm he] using hv

theorem mpt_eval_add2_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (v : ValueHOL 64)
    (h : evalAt s (.op .add [e1, e2]) = some v) :
    ∃ a b : BitVec 64, evalAt s e1 = some (.val (.word a)) ∧
      evalAt s e2 = some (.val (.word b)) ∧ v = .val (.word (a + b)) := by
  rcases h1 : evalAt s e1 with _ | (⟨⟨a⟩⟩ | fs | ⟨nm, fs⟩)
  all_goals rcases h2 : evalAt s e2 with _ | (⟨⟨b⟩⟩ | gs | ⟨nn, gs⟩)
  all_goals simp only [evalAt, evalHOLExact, evalListHOLExact, h1, h2,
    valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
    wordOpHOL, wordOp, List.foldr, BitVec.add_zero] at h
  all_goals first | contradiction | exact ⟨a, b, rfl, rfl, by simpa only [add_zero] using (Option.some.inj h).symm⟩

theorem mpt_assign_none_word {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (name : String) (e : ExpHOL 64) (w : BitVec 64)
    (he : evalAt s e = some (.val (.word w)))
    (h : evaluateHOLFiniteState s (.assign .local (ofString name) e) = (none, t)) :
    t = setVarHOLFinite (ofString name) (.val (.word w)) s := by
  simp only [evalAt] at he
  rw [evaluateHOLFiniteState_assign, he] at h
  dsimp only at h
  split at h
  · exact (Prod.mk.inj h).2.symm
  · cases h

theorem mpt_store_self_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (e v : ExpHOL 64) (a w : BitVec 64)
    (he : evalAt s e = some (.val (.word a)))
    (hv : evalAt s v = some (.val (.word w)))
    (hm : s.memory a = .word w)
    (h : evaluateHOLFiniteState s (.store e v) = (none, t)) : t = s := by
  simp only [evalAt] at he hv
  rw [evaluateHOLFiniteState_store, he] at h
  dsimp only at h
  rw [hv] at h
  by_cases hd : s.memaddrs a
  · simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hd, ↓reduceIte] at h
    have heq : (fun b => if b = a then HolWordLab.word w else s.memory b) = s.memory := by
      funext b
      split
      · rename_i hb; simpa only [hb] using hm.symm
      · rfl
    simp only [heq] at h
    exact (Prod.mk.inj h).2.symm
  · simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, hd] at h

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
