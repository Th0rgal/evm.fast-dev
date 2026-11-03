import InitECandidate.Solver.Wave8GuestInv.ContractParts.C09

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.P3MptSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem lookup_mpt_nibble_key :
    originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mpt_nibble_key).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl

theorem lookup__mpt_insert_node :
    originalRuntimeCode.lookup (ofString "_mpt_insert_node") =
      some ((sourceFunctionEntry Guest.Software.guestFn__mpt_insert_node).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 275 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__mpt_insert_node) rfl

theorem lookup__mpt_delete_node :
    originalRuntimeCode.lookup (ofString "_mpt_delete_node") =
      some ((sourceFunctionEntry Guest.Software.guestFn__mpt_delete_node).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 279 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__mpt_delete_node) rfl

theorem lookup_mpt_set :
    originalRuntimeCode.lookup (ofString "mpt_set") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mpt_set).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 280 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_set) rfl

theorem callee_param_three_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 : MlS) (s1 s2 s3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3)], body, ret))
    (e1 e2 e3 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧ evalAt state e3 = some v3 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧ callee.lookup p3 = some v3 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
    simp only [evalAt] at he1 he2 he3 <;>
    simp only [he1, he2, he3, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2]
      · simp [List.zip, List.foldl, hnd.2]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_four_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 : MlS) (s1 s2 s3 s4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
  rcases he4 : evalAt state e4 with _ | v4 <;>
    simp only [evalAt] at he1 he2 he3 he4 <;>
    simp only [he1, he2, he3, he4, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, v4, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2]
      · simp [List.zip, List.foldl]
    · cases raw

theorem callee_param_six_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 p5 p6 : MlS) (s1 s2 s3 s4 s5 s6 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4), (p5, s5), (p6, s6)], body, ret))
    (e1 e2 e3 e4 e5 e6 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4, e5, e6] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4 v5 v6,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧
      evalAt state e5 = some v5 ∧ evalAt state e6 = some v6 ∧
      callee.lookup p1 = some v1 ∧ callee.lookup p2 = some v2 ∧
      callee.lookup p3 = some v3 ∧ callee.lookup p4 = some v4 ∧
      callee.lookup p5 = some v5 ∧ callee.lookup p6 = some v6 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
  rcases he4 : evalAt state e4 with _ | v4 <;>
  rcases he5 : evalAt state e5 with _ | v5 <;>
  rcases he6 : evalAt state e6 with _ | v6 <;>
    simp only [evalAt] at he1 he2 he3 he4 he5 he6 <;>
    simp only [he1, he2, he3, he4, he5, he6, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, v4, v5, v6, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.1.1, hnd.1.2.1, hnd.1.2.2.1, hnd.1.2.2.2.1, hnd.1.2.2.2.2]
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2.1, hnd.2.1.2.2.1, hnd.2.1.2.2.2]
      · simp [List.zip, List.foldl, hnd.2.2.1.1, hnd.2.2.1.2.1, hnd.2.2.1.2.2]
      · simp [List.zip, List.foldl, hnd.2.2.2.1.1, hnd.2.2.2.1.2]
      · simp [List.zip, List.foldl, hnd.2.2.2.2]
      · simp [List.zip, List.foldl]
    · cases raw

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

theorem dec_guard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {k : Nat}
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s init = some v → Q (setVarHOLFinite name v s))
    (hb : TerminatingProgBoundedOn Q body k) :
    TerminatingProgBoundedOn P (.dec name shape init body) k := by
  intro F s hc hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rename_i v hv
    revert hnt
    split <;> intro hnt
    · have h := hb (setVarHOLFinite name v s) hc (hi s v hP hv) hnt
      simpa only [setVarHOLFinite] using h
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

end InitECandidate.Solver.Wave8GuestInv.P3MptSet
