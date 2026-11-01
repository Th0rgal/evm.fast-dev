import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Flow

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptFinishState {F : Type} (s : PanSemStateFiniteExact 64 F) (nn ns nl : BitVec 64) :=
  setVarHOLFinite (ofString "level") (.val (.word nl))
    (setVarHOLFinite (ofString "slot") (.val (.word ns))
      (setVarHOLFinite (ofString "node") (.val (.word nn)) s))

theorem mpt_finish_tail_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nn ns nl : BitVec 64)
    (hn : MptLocalWord s "node") (hs : MptLocalWord s "slot") (hl : MptLocalWord s "level")
    (hNN : s.locals.lookup (ofString "next_node") = some (.val (.word nn)))
    (hNS : s.locals.lookup (ofString "next_slot") = some (.val (.word ns)))
    (hNL : s.locals.lookup (ofString "next_level") = some (.val (.word nl))) :
    evaluateHOLFiniteState s
      (.seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
        (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
          (.assign .local (ofString "level") (.var .local (ofString "next_level"))))) =
      (none, mptFinishState s nn ns nl) := by
  rw [evaluateHOLFiniteState_seq_line780,
    mpt_assign_word s "node" (.var .local (ofString "next_node")) nn hn hNN]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,
    mpt_assign_word _ "slot" (.var .local (ofString "next_slot")) ns (mptLocalWord_setVar s "slot" "node" nn hs)
      (by simpa [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, ofString] using hNS)]
  dsimp only
  exact mpt_assign_word _ "level" (.var .local (ofString "next_level")) nl
    (mptLocalWord_setVar _ "level" "slot" ns (mptLocalWord_setVar s "level" "node" nn hl))
    (by simpa [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update,
      FUPDATE, ofString] using hNL)

/-- On a continuing branch descent the parent store writes the pointer already there. -/
theorem mpt_finish_none {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (Nd : List Nat) (n nn ns nl : BitVec 64)
    (hnode : s.locals.lookup (ofString "node") = some (.val (.word n)))
    (hlevel : MptLocalWord s "level")
    (hr : s.locals.lookup (ofString "r") = some (.val (.word n)))
    (hNN : s.locals.lookup (ofString "next_node") = some (.val (.word nn)))
    (hNS : s.locals.lookup (ofString "next_slot") = some (.val (.word ns)))
    (hNL : s.locals.lookup (ofString "next_level") = some (.val (.word nl)))
    (hslot : MptSlotOK s Nd)
    (h : evaluateHOLFiniteState s mptInsertFinish = (none, t)) :
    t = {s with locals := t.locals} ∧
      t.locals.lookup (ofString "node") = some (.val (.word nn)) ∧
      t.locals.lookup (ofString "slot") = some (.val (.word ns)) ∧
      t.locals.lookup (ofString "level") = some (.val (.word nl)) := by
  obtain ⟨u, hfirst, htail⟩ := mpt_seq_none_inv h
  obtain ⟨w, hw, hbranch⟩ := mpt_ite_none_inv hfirst
  obtain ⟨p, z, hp, hz, hcmp⟩ := evalAt_cmp s .equal _ _ w hw
  have hz0 : z = 0#64 := by
    have := evalAt_const s 0 (.val (.word z)) hz
    simpa using this
  subst z
  change s.locals.lookup (ofString "slot") = some (.val (.word p)) at hp
  have hcond : w = if p = 0#64 then 1 else 0 := by
    simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using hcmp
  rw [hcond] at hbranch
  have hu : u = s ∨ u = setVarHOLFinite (ofString "result") (.val (.word n)) s := by
    by_cases hp0 : p = 0#64
    · right
      simp only [hp0, ↓reduceIte, ne_eq, one_ne_zero] at hbranch
      exact mpt_assign_none_word s u "result" (.var .local (ofString "r")) n hr hbranch
    · left
      simp only [hp0, ↓reduceIte] at hbranch
      have hm : memW s p.toNat = n.toNat := by
        rcases hslot with h0 | ⟨_, _, _, hv⟩
        · have hpN : p.toNat = 0 := by simpa only [locN, hp] using h0
          exact (hp0 (BitVec.eq_of_toNat_eq hpN)).elim
        · simpa only [locN, hp, hnode] using hv
      have hmem : s.memory p = .word n := by
        simpa using mpt_memW_word s p.toNat n hm
      exact mpt_store_self_none s u (.var .local (ofString "slot")) (.var .local (ofString "r")) p n hp hr hmem hbranch
  have hnU : MptLocalWord u "node" := by
    rcases hu with rfl | rfl
    · exact ⟨n, hnode⟩
    · exact mptLocalWord_setVar s "node" "result" n ⟨n, hnode⟩
  have hsU : MptLocalWord u "slot" := by
    rcases hu with rfl | rfl
    · exact ⟨p, hp⟩
    · exact mptLocalWord_setVar s "slot" "result" n ⟨p, hp⟩
  have hlU : MptLocalWord u "level" := by
    rcases hu with rfl | rfl
    · exact hlevel
    · exact mptLocalWord_setVar s "level" "result" n hlevel
  have hNNu : u.locals.lookup (ofString "next_node") = some (.val (.word nn)) := by
    rcases hu with rfl | rfl <;>
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hNN
  have hNSu : u.locals.lookup (ofString "next_slot") = some (.val (.word ns)) := by
    rcases hu with rfl | rfl <;>
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hNS
  have hNLu : u.locals.lookup (ofString "next_level") = some (.val (.word nl)) := by
    rcases hu with rfl | rfl <;>
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString] using hNL
  rw [mpt_finish_tail_eval u nn ns nl hnU hsU hlU hNNu hNSu hNLu] at htail
  have ht : t = mptFinishState u nn ns nl := (Prod.mk.inj htail).2.symm
  rw [ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hu with rfl | rfl <;> rfl
  all_goals simp [mptFinishState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ofString]

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
