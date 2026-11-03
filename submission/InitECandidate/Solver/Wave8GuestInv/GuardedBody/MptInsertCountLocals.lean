import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptInsertCountSupport

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.Rlp

/-- The large kind dispatch is used here only through its local-variable footprint. -/
def core := mptDecBody (mptDecBody (mptDecBody (mptDecBody mptInsertBody)))
def branch := mptLeft (mptRight core)
def storeResult := mptLeft (mptRight (mptRight core))
def moves := mptRight (mptRight (mptRight core))

theorem core_ast : core = .seq (.assign .local (ofString "go") (.const 0))
    (.seq branch (.seq storeResult moves)) := rfl

theorem storeResult_ast : storeResult =
    .ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
      (.assign .local (ofString "result") (.var .local (ofString "r")))
      (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))) := rfl

theorem moves_ast : moves =
    .seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
      (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
        (.assign .local (ofString "level") (.var .local (ofString "next_level")))) := rfl

theorem seq_none {F : Type} {s t : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.seq a b) = (none, t)) :
    ∃ u, evaluateHOLFiniteState s a = (none, u) ∧ evaluateHOLFiniteState u b = (none, t) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  cases ha : evaluateHOLFiniteState s a with
  | mk r u =>
    rw [ha] at h
    cases r with
    | none => exact ⟨u, rfl, h⟩
    | some r => simp at h

theorem dec_const_none {F : Type} {s t : PanSemStateFiniteExact 64 F} {n : MlS}
    {w : BitVec 64} {b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec n .one (.const w) b) = (none, t)) :
    ∃ u, evaluateHOLFiniteState (setVarHOLFinite n (.val (.word w)) s) b = (none, u) ∧
      t = {u with locals := HolFiniteMapExact.resVarEq u.locals (n, s.locals.lookup n)} := by
  rw [evaluateHOLFiniteState_dec_total] at h
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at h
  cases hb : evaluateHOLFiniteState (setVarHOLFinite n (.val (.word w)) s) b with
  | mk r u =>
    rw [hb] at h
    obtain ⟨rfl, ht⟩ := Prod.mk.inj h
    exact ⟨u, rfl, ht.symm⟩

theorem word_of_assign_var {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x y : MlS} (hw : WordLocal y s)
    (h : evaluateHOLFiniteState s (.assign .local x (.var .local y)) = (none, t)) :
    WordLocal x t := by
  obtain ⟨w, hw⟩ := hw
  rw [evaluateHOLFiniteState_assign] at h
  simp only [evalHOLExact, hw] at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj h
    exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  · simp at h

theorem assign_const_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {x : MlS} {w : BitVec 64}
    (h : evaluateHOLFiniteState s (.assign .local x (.const w)) = (none, t)) :
    t = setVarHOLFinite x (.val (.word w)) s := by
  rw [evaluateHOLFiniteState_assign] at h
  simp only [evalHOLExact] at h
  split at h
  · exact (Prod.mk.inj h).2.symm
  · simp at h

theorem word_run {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    (x : MlS) (hp : wsafe p = true) (hw : WordLocal x s)
    (h : evaluateHOLFiniteState s p = (none, t)) : WordLocal x t := by
  have h' := evaluate_wordLocal x p hp s hw (by rw [h]; exact Or.inl rfl)
  simpa only [h] using h'

theorem keep_run {F : Type} {s t : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    (x : MlS) (hp : avoidsLocal x p = true)
    (h : evaluateHOLFiniteState s p = (none, t)) : t.locals.lookup x = s.locals.lookup x := by
  have h' := evaluate_avoidsLocal_flowing x p hp s (by rw [h]; exact Or.inl rfl)
  simpa only [h] using h'

theorem storeResult_keep {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : locN s "slot" ≠ 0) :
    (evaluateHOLFiniteState s storeResult).2.locals.lookup (ofString "result") =
      s.locals.lookup (ofString "result") := by
  rw [storeResult_ast, evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    obtain ⟨a, b, ha, hb, hcmp⟩ := RunFramesRace.cond_local s .equal "slot" (.const 0) w hw
    cases RunFramesRace.evalAt_const s 0 _ hb
    have hz : a ≠ 0 := by intro hz; apply hs; rw [← ha, hz]; rfl
    have hw0 : w = 0 := by
      simp only [Compiler.Encoders.Asm.wordCmpHOL, beq_iff_eq] at hcmp
      rw [if_neg hz] at hcmp
      exact hcmp
    rw [if_pos hw0, (evaluate_store_control_frame s _ _).2.1]
  · rfl

/-- Successful completion of the fixed epilogue makes its three destinations words. -/
theorem moves_words {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hn : WordLocal (ofString "next_node") s)
    (hs : WordLocal (ofString "next_slot") s)
    (hl : WordLocal (ofString "next_level") s)
    (h : evaluateHOLFiniteState s moves = (none, t)) :
    WordLocal (ofString "node") t ∧ WordLocal (ofString "slot") t ∧
      WordLocal (ofString "level") t := by
  rw [moves_ast] at h
  obtain ⟨u, hu, hrest⟩ := seq_none h
  obtain ⟨v, hv, ht⟩ := seq_none hrest
  have hnu := word_of_assign_var hn hu
  have hsv := word_of_assign_var (word_run _ rfl hs hu) hv
  have hlt := word_of_assign_var (word_run _ rfl (word_run _ rfl hl hu) hv) ht
  exact ⟨word_run _ rfl (word_run _ rfl hnu hv) ht, word_run _ rfl hsv ht, hlt⟩

/-- The kind dispatch need not be proved: its successful runs preserve the scratch
word shapes, and its writes to `go` are visibly Boolean constants. -/
theorem core_locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hn : WordLocal (ofString "next_node") s)
    (hs : WordLocal (ofString "next_slot") s)
    (hl : WordLocal (ofString "next_level") s)
    (h : evaluateHOLFiniteState s core = (none, t)) :
    BoolLocal (ofString "go") t ∧ WordLocal (ofString "node") t ∧
      WordLocal (ofString "slot") t ∧ WordLocal (ofString "level") t ∧
      (locN s "slot" ≠ 0 → t.locals.lookup (ofString "result") = s.locals.lookup (ofString "result")) := by
  rw [core_ast] at h
  obtain ⟨a, ha, hrest⟩ := seq_none h
  obtain ⟨b, hb, hrest⟩ := seq_none hrest
  obtain ⟨c, hc, hd⟩ := seq_none hrest
  have hga : BoolLocal (ofString "go") a := by
    rw [assign_const_none ha]
    left
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hgb : BoolLocal (ofString "go") b := by
    have h' := evaluate_boolLocal (ofString "go") branch (by decide) a hga (by rw [hb]; exact Or.inl rfl)
    simpa only [hb] using h'
  have hgt : BoolLocal (ofString "go") t := boolLocal_congr _
    ((keep_run _ (by decide) hd).trans (keep_run _ (by decide) hc)) hgb
  have wn := word_run _ (by decide) (word_run _ (by decide) (word_run _ rfl hn ha) hb) hc
  have ws := word_run _ (by decide) (word_run _ (by decide) (word_run _ rfl hs ha) hb) hc
  have wl := word_run _ (by decide) (word_run _ (by decide) (word_run _ rfl hl ha) hb) hc
  obtain ⟨wn, ws, wl⟩ := moves_words wn ws wl hd
  refine ⟨hgt, wn, ws, wl, ?_⟩
  intro hslot
  have hsb : b.locals.lookup (ofString "slot") = s.locals.lookup (ofString "slot") :=
    (keep_run _ (by decide) hb).trans (keep_run _ (by decide) ha)
  have hslotb : locN b "slot" ≠ 0 := by simpa only [locN, hsb] using hslot
  have hrc := storeResult_keep b hslotb
  rw [hc] at hrc
  exact (keep_run _ (by decide) hd).trans (hrc.trans
    ((keep_run _ (by decide) hb).trans (keep_run _ (by decide) ha)))


def observed : List MlS := ["go", "node", "slot", "level", "result"].map ofString

theorem body_locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : evaluateHOLFiniteState s mptInsertBody = (none, t)) :
    BoolLocal (ofString "go") t ∧ WordLocal (ofString "node") t ∧
      WordLocal (ofString "slot") t ∧ WordLocal (ofString "level") t ∧
      (locN s "slot" ≠ 0 → t.locals.lookup (ofString "result") = s.locals.lookup (ofString "result")) := by
  change evaluateHOLFiniteState s
    (.dec (ofString "r") .one (.const 0)
      (.dec (ofString "next_node") .one (.const 0)
        (.dec (ofString "next_slot") .one (.const 0)
          (.dec (ofString "next_level") .one (.const 0) core)))) = (none, t) at h
  obtain ⟨a, ha, ht⟩ := dec_const_none h
  obtain ⟨b, hb, hat⟩ := dec_const_none ha
  obtain ⟨c, hc, hbt⟩ := dec_const_none hb
  obtain ⟨d, hd, hct⟩ := dec_const_none hc
  have hpre (x : MlS) (hx : x ∈ observed) :
      (setVarHOLFinite (ofString "next_level") (.val (.word 0))
        (setVarHOLFinite (ofString "next_slot") (.val (.word 0))
          (setVarHOLFinite (ofString "next_node") (.val (.word 0))
            (setVarHOLFinite (ofString "r") (.val (.word 0)) s)))).locals.lookup x = s.locals.lookup x := by
    simp only [observed, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString]
  have hpost (x : MlS) (hx : x ∈ observed) : t.locals.lookup x = d.locals.lookup x := by
    rw [ht, hat, hbt, hct]
    simp only [observed, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp [PanRunBounded.resVarEq_lookup, ofString]
  have hw (x : MlS) (hx : x ∈ ["next_node", "next_slot", "next_level"].map ofString) :
      WordLocal x (setVarHOLFinite (ofString "next_level") (.val (.word 0))
        (setVarHOLFinite (ofString "next_slot") (.val (.word 0))
          (setVarHOLFinite (ofString "next_node") (.val (.word 0))
            (setVarHOLFinite (ofString "r") (.val (.word 0)) s)))) := by
    refine ⟨0, ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString]
  obtain ⟨hg, hn, hs, hl, hr⟩ := core_locals
    (hw (ofString "next_node") (by simp)) (hw (ofString "next_slot") (by simp))
    (hw (ofString "next_level") (by simp)) hd
  refine ⟨boolLocal_congr _ (hpost (ofString "go") (by simp [observed])) hg, ?_, ?_, ?_, ?_⟩
  · simpa only [WordLocal, hpost (ofString "node") (by simp [observed])] using hn
  · simpa only [WordLocal, hpost (ofString "slot") (by simp [observed])] using hs
  · simpa only [WordLocal, hpost (ofString "level") (by simp [observed])] using hl
  · intro hslot
    rw [hpost (ofString "result") (by simp [observed]), hr, hpre (ofString "result") (by simp [observed])]
    simpa only [locN, hpre (ofString "slot") (by simp [observed])] using hslot

theorem body_flow_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hf : MptFlow s mptInsertBody) : (evaluateHOLFiniteState s mptInsertBody).1 = none := by
  exact hf.resolve_right (evaluate_noTopContinue mptInsertBody (by decide) s)

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
