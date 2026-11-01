import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptInsertKind3Progress

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanRunBounded

def mptRestore {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (saved : Option (ValueHOL 64)) : PanSemStateFiniteExact 64 F :=
  {s with locals := HolFiniteMapExact.resVarEq s.locals (name, saved)}

@[simp] theorem mpt_restore_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name current : MlS) (saved : Option (ValueHOL 64)) (hne : name ≠ current) :
    (mptRestore s name saved).locals.lookup current = s.locals.lookup current := by
  simp only [mptRestore, lookup_resVarEq_toExact, resVarHOLExact]
  cases saved <;> simp [FUPDATE_HOL, FDOMSUB_HOL, hne, Ne.symm hne]

theorem mpt_dec_const_none_inv {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {name : MlS} {c : BitVec 64} {body : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec name .one (.const c) body) = (none, t)) :
    ∃ u, evaluateHOLFiniteState (setVarHOLFinite name (.val (.word c)) s) body = (none, u) ∧
      t = mptRestore u name (s.locals.lookup name) := by
  obtain ⟨v, u, hv, _, he, ht⟩ := mpt_dec_none_inv h
  have hv' := evalAt_const s c v hv
  subst v
  exact ⟨u, he, ht⟩

theorem mpt_head_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (he : ∀ name ∈ ["go", "level", "klen", "node", "key", "slot", "vlen"],
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hs : MptInsertHead s) : MptInsertHead {s with locals := locals, clock := clock} := by
  let t : PanSemStateFiniteExact 64 F := {s with locals := locals, clock := clock}
  have hl : ∀ name ∈ ["go", "level", "klen", "node", "key", "slot", "vlen"], locN t name = locN s name := by
    intro name hm
    simp only [t, locN, he name hm]
  refine ⟨(arenaReady_with_locals s locals clock).2 hs.1, fun hg => ?_⟩
  change locN t "go" ≠ 0 at hg
  rw [hl "go" (by simp)] at hg
  obtain ⟨hle, Nd, hn, hr, hk, hslot, hvlen, hklen⟩ := hs.2 hg
  refine ⟨?_, Nd, hn, ?_, ?_, ?_, ?_, ?_⟩
  · change locN t "level" ≤ locN t "klen"
    simpa only [hl "level" (by simp), hl "klen" (by simp)] using hle
  · change RootIn Nd (locN t "node")
    simpa only [hl "node" (by simp)] using hr
  · change KeyIn s Nd (locN t "key" + locN t "level") (locN t "klen" - locN t "level")
    simpa only [hl "key" (by simp), hl "level" (by simp), hl "klen" (by simp)] using hk
  · change MptSlotOK t Nd
    have hmem : ∀ a, memW t a = memW s a := fun _ => rfl
    simpa only [MptSlotOK, hl "slot" (by simp), hl "node" (by simp), hmem] using hslot
  · change locN t "vlen" < 2 ^ 40
    simpa only [hl "vlen" (by simp)] using hvlen
  · change locN t "klen" ≤ 64
    simpa only [hl "klen" (by simp)] using hklen

theorem mpt_ite_eq_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (w c : BitVec 64) (a b : ProgHOL 64)
    (hw : s.locals.lookup (ofString name) = some (.val (.word w))) :
    evaluateHOLFiniteState s (.ite (.cmp .equal (.var .local (ofString name)) (.const c)) a b) =
      if w = c then evaluateHOLFiniteState s a else evaluateHOLFiniteState s b := by
  rw [evaluateHOLFiniteState_ite]
  simp only [evalAt, evalHOLExact, hw, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : w = c <;> simp only [beq_iff_eq, h, ↓reduceIte] <;> rfl

theorem mpt_memW_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock a : Nat) :
    memW {s with locals := locals, clock := clock} a = memW s a := rfl

theorem mpt_slot_clock {F : Type} (s : PanSemStateFiniteExact 64 F) (clock : Nat) (Nd : List Nat) :
    MptSlotOK {s with clock := clock} Nd ↔ MptSlotOK s Nd := Iff.rfl

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
