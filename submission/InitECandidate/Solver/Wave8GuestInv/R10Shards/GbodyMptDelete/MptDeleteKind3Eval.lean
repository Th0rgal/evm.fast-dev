import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Fresh

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptAddLocals_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String} {a b : BitVec 64}
    (ha : s.locals.lookup (ofString n) = some (.val (.word a)))
    (hb : s.locals.lookup (ofString m) = some (.val (.word b))) :
    evalAt s (.op .add [.var .local (ofString n), .var .local (ofString m)]) =
      some (.val (.word (a + b))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem mptAddConst_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {a : BitVec 64} (off : Nat)
    (ha : s.locals.lookup (ofString n) = some (.val (.word a))) :
    evalAt s (.op .add [.var .local (ofString n), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (a.toNat + off)))) := by
  have heq : a + BitVec.ofNat 64 off = BitVec.ofNat 64 (a.toNat + off) := by
    simp [BitVec.ofNat_add]
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, wordOpHOL, wordOp, heq]

theorem mptAddLocals_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String} {v : ValueHOL 64}
    (h : evalAt s (.op .add [.var .local (ofString n), .var .local (ofString m)]) = some v) :
    ∃ a b : BitVec 64,
      s.locals.lookup (ofString n) = some (.val (.word a)) ∧
      s.locals.lookup (ofString m) = some (.val (.word b)) ∧ v = .val (.word (a + b)) := by
  cases ha : s.locals.lookup (ofString n) with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, ha] at h
  | some a =>
    cases hb : s.locals.lookup (ofString m) with
    | none => simp [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at h
    | some b =>
      cases a <;> cases b
      all_goals simp only [evalAt, evalHOLExact, evalListHOLExact, ha, hb] at h
      all_goals try { simp [valueIsWord] at h }
      rename_i a b
      cases a with | word a =>
        cases b with | word b =>
          simp only [List.all_cons, List.all_nil, valueIsWord, Bool.and_self, if_true, List.map_cons, List.map_nil, valueWord, wordOpHOL, wordOp, Option.map_some, List.foldr, BitVec.add_zero] at h
          refine ⟨a, b, rfl, rfl, ?_⟩
          simpa using (Option.some.inj h).symm

theorem mptLoad_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {a : Nat} {v : ValueHOL 64}
    (ha : evalAt s addr = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s (.load .one addr) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s a := by
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr = _ at ha
  simp only [evalAt, evalHOLExact, isWfShapeExactHOL, ha, memLoadHOLExact] at hv
  cases hm : s.memory (BitVec.ofNat 64 a) with
  | word w =>
    simp only [hm] at hv
    simp only [if_true] at hv
    split at hv
    · exact ⟨w, (Option.some.inj hv).symm, by simp only [memW, hm]⟩
    · cases hv

theorem mptByte_inv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {a : Nat} {v : ValueHOL 64}
    (ha : evalAt s addr = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s (.loadByte addr) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memB s a := by
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr = _ at ha
  simp only [evalAt, evalHOLExact, ha, panMemLoadByteHOL] at hv
  cases hm : s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w =>
    simp only [hm] at hv
    split at hv
    · simp only [Option.map_some] at hv
      refine ⟨_, (Option.some.inj hv).symm, ?_⟩
      simp only [BitVec.toNat_ofNat, memB, hm]
      apply Nat.mod_eq_of_lt
      have hh := (panGetByteHOL (BitVec.ofNat 64 a) w s.be).toNat_lt
      omega
    · cases hv

theorem mptStore_word_none {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {dst src : ExpHOL 64} {a : Nat} {w : BitVec 64}
    (hd : evalAt s dst = some (.val (.word (BitVec.ofNat 64 a))))
    (hv : evalAt s src = some (.val (.word w)))
    (hr : evaluateHOLFiniteState s (.store dst src) = (none, t)) :
    t = mptWordWrite s a w := by
  rw [evaluateHOLFiniteState_store] at hr
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst = _ at hd
  change @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) src = _ at hv
  rw [hd, hv] at hr
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hr
  by_cases hdom : s.memaddrs (BitVec.ofNat 64 a)
  · simp only [hdom, if_true] at hr
    exact (Prod.mk.inj hr).2.symm
  · simp only [hdom, if_false] at hr
    cases hr

theorem mptByte_addr {F : Type} {s : PanSemStateFiniteExact 64 F}
    {addr : ExpHOL 64} {v : ValueHOL 64}
    (hv : evalAt s (.loadByte addr) = some v) :
    ∃ a : BitVec 64, evalAt s addr = some (.val (.word a)) := by
  unfold evalAt at hv
  rw [evalHOLExact] at hv
  split at hv
  · rename_i a ha
    exact ⟨a, ha⟩
  · cases hv

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
