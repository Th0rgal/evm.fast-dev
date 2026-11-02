import InitECandidate.Solver.Wave8GuestInv.ContractParts.C09

/-! Node encoding guard transfers and concrete body bounds. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace NodeRlpProof

theorem localsOnly : LocalsOnly ["node"] NodeRlpReady := by
  intro F s locals k hl hP
  have ht := locN_congr s locals k "node" (hl "node" (by simp))
  simp only [NodeRlpReady, arenaReady_with_locals] at hP ⊢
  rw [ht]
  exact hP

theorem entry {fname : MlS} {e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some e)
    (hp : e.1 = [(ofString "node", .one)]) :
    CallEntryOn NodeRlpReady NodeRlpReady fname [.var .local (ofString "node")] := by
  obtain ⟨ps, b, r⟩ := e
  dsimp only at hp
  subst hp
  intro F state values body' callee ret' hcode hP hargs hlook
  have hc := callee_param_one state fname (ofString "node") .one b r
    (by rw [hcode]; exact hl) values body' callee ret' hargs hlook
  exact localsOnly state callee (state.clock - 1) (by simpa using hc) hP

theorem straight (p : ProgHOL 64) (h : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p h s hc

theorem weakenGuard {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {k : Nat} (h : TerminatingProgBoundedOn Q p k)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    TerminatingProgBoundedOn P p k := fun s hc hP => h s hc (hp s hP)

theorem skip_preserves {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} :
    PreservesOn P P .skip := by
  intro F s _ hP _
  simpa [evaluateHOLFiniteState_skip] using hP

theorem call_ro {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {f : MlS} (h : ReadOnlyFn f) (args : List (ExpHOL 64)) :
    Hoare P (.call (some (none, none)) f args) (fun r t => r = none → P t) := by
  apply Hoare.call0 h (callEntryOn_of_imp localsFree_guestInv hPG _ _)
  · intro F s callee post v hc hPs hq _
    rw [hq (Or.inl ⟨v, rfl⟩)]
    exact hP s s.locals post.clock (fun _ _ => rfl) hPs
  · intro F r t hr _ he
    exact False.elim (hr he)

theorem lookup_fill : originalRuntimeCode.lookup (ofString "_node_rlp_fill") =
    some ((sourceFunctionEntry Guest.Software.guestFn__node_rlp_fill).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 284 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_fill) rfl

theorem lookup_rlp : originalRuntimeCode.lookup (ofString "node_rlp") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_rlp).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 285 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_rlp) rfl

theorem lookup_hash : originalRuntimeCode.lookup (ofString "node_hash") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_hash).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 290 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_hash) rfl

theorem lookup_root : originalRuntimeCode.lookup (ofString "mpt_root") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

theorem node_rlp
    (hf : TerminatingFunBoundedOn NodeRlpReady (ofString "_node_rlp_fill") K.«_node_rlp_fill»)
    (hm : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail»)
    (hr : ReadOnlyFn (ofString "mpt_fail")) :
    TerminatingFunBoundedOn NodeRlpReady (ofString "node_rlp") K.«node_rlp» := by
  refine ⟨_, _, _, lookup_rlp, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (weakenGuard (straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hm _ _
              (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1) _ _))
            (weakenGuard (straight _ rfl) (fun s h => h.1.1)))
          (Hoare.ite
            (Hoare.mono (call_ro localsOnly (fun s h => h.1.1) hr _) (fun s h => h.1))
            (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
          (TerminatingProgBoundedOn.seq_guestInv_after
            (TerminatingProgBoundedOn.call_on hf _ _ (entry lookup_fill (by rfl)))
            (fun s h => h.1.1)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«node_rlp»
  simp only [Nat.max_def]
  split <;> omega

theorem node_hash
    (ha : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hk : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hn : TerminatingFunBoundedOn NodeRlpReady (ofString "node_rlp") K.«node_rlp») :
    TerminatingFunBoundedOn NodeRlpReady (ofString "node_hash") K.«node_hash» := by
  refine ⟨_, _, _, lookup_hash, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_node_hash,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.dec_onLocals localsOnly _ (by decide) _ _
      (TerminatingProgBoundedOn.seq_hoare
        (weakenGuard (straight _ rfl) (fun s h => h.1.1))
        (Hoare.ite_return_skip _ _)
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ (entry lookup_rlp (by rfl))
          (decCallResumeOn_guestInv (fun s h => h.1.1) _ _ _)
          (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv hk _ _)
              (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
                (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))))) ?_
  unfold K.«node_hash»
  omega

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

/-- A one-word load from `global + k` that succeeds yields the word `memW t (locN t g + k)`. -/
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


theorem callee_param_alias {F : Type} (state : PanSemStateFiniteExact 64 F) (fname pk caller : MlS)
    (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(pk, sk)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local caller] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup pk = state.locals.lookup caller := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, evalHOLExact] at hargs
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
    rcases hv : state.locals.lookup caller with _ | v
    · rw [hv] at hargs; cases hargs
    · rw [hv] at hargs
      cases hargs
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        simp
      · cases raw


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

def RootReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "root") ∧
    ∀ j ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
           (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
      (j.2 = 0 ∨ Allocated s j) ∧ ∀ o ∈ nodeExtents s Nd, Disj o j

theorem root_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : MptObjReady s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    RootReady (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "m" 0 v hv
  obtain ⟨ha, S, hS, ⟨Nd, hm⟩, rest⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ ha, Nd, hm.2.2.2.2.1, ?_, ?_⟩
  · rw [locN_setVar_same, hw]
    simpa using hm.2.2.2.2.2.1
  · intro j hj
    have hj_fix : j ∈ fixedObjects s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      have hbuf : j ∈ globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2) := by
        rcases hj with rfl | rfl
        · exact List.mem_map.mpr ⟨("keccak_pad", 136), by decide, rfl⟩
        · exact List.mem_map.mpr ⟨("keccak_st", 200), by decide, rfl⟩
      simp only [fixedObjects, List.mem_append]
      exact Or.inl (Or.inl (Or.inl hbuf))
    have halloc : j.2 = 0 ∨ Allocated s j := by
      rcases hS.2.2.1.1 j hj_fix with hz | ⟨hal, _⟩
      · exact Or.inl hz
      · exact Or.inr hal
    exact ⟨halloc, fun o ho => (hm.2.2.2.2.2.2 o ho).2.2 j hj_fix⟩

theorem root_entry :
    CallEntryOn RootReady NodeRlpReady (ofString "node_hash") [.var .local (ofString "root")] := by
  intro F s vs b callee r hc hP hargs hl
  have hp := callee_param_alias s (ofString "node_hash") (ofString "node") (ofString "root")
    .one _ _ (by rw [hc]; exact lookup_hash) vs b callee r hargs hl
  refine ⟨localsFree_arenaReady s _ _ hP.1, ?_⟩
  have hx : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [locN, callEntryStateHOLFinite, hp]
  rw [hx]
  exact hP.2

theorem mpt_root
    (hm : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (hn : TerminatingFunBoundedOn NodeRlpReady (ofString "node_hash") K.«node_hash») :
    TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root» := by
  refine ⟨_, _, _, lookup_root, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_root,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (dec_guard _ _ _ root_init
      (TerminatingProgBoundedOn.seq_hoare
        (TerminatingProgBoundedOn.ite_on
          (weakenGuard
            (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
              (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))
            (fun s h => h.1.1))
          (weakenGuard (straight _ rfl) (fun s h => h.1.1)))
        (Hoare.ite
          ⟨fun s hc hP hnt he => by
            rw [evaluateHOLFiniteState_seq_line780] at he
            dsimp only at he
            split at he
            · exact False.elim (return_ne_none _ _ he)
            · simp_all⟩
          (Hoare.skip (fun s h _ => h.1)) (fun _ _ h => absurd h (by simp)))
        (TerminatingProgBoundedOn.decCall_on hn _ _ _ root_entry
          (decCallResumeOn_guestInv (fun s h => h.1.1) _ _ _)
          (TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv hm _ _)
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_root»
  simp only [Nat.max_def]
  split <;> omega

/-! The branch scan is bounded independently of the node payload. -/

def scanCond : ExpHOL 64 :=
  .op .and [.cmp .notEqual (.const 0) (.cmp .less (.var .local (ofString "i")) (.const 16)),
    .cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "found")) (.const 0))]

def scanBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "child")
    (.load .one (.op .add [.var .local (ofString "nd"), .const 32,
      .panop .mul [.var .local (ofString "i"), .const 8]])))
    (.seq (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"), .const 1]))
      (.call (some (some (.local, ofString "found"), none)) (ofString "_node_needs_rlp")
        [.var .local (ofString "child")]))

def ScanReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "i" ≤ 16

theorem seq_none {F : Type} (s : PanSemStateFiniteExact 64 F) (p q : ProgHOL 64)
    (h : (evaluateHOLFiniteState s (.seq p q)).1 = none) :
    (evaluateHOLFiniteState s p).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).1 = none ∧
    (evaluateHOLFiniteState s (.seq p q)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s p).2 q).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s p with ⟨r, t⟩
  simp only [hr] at h ⊢
  cases r with
  | none => exact ⟨rfl, h, rfl⟩
  | some r => simp at h

theorem scan_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (w : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w)))
    (hn : (evaluateHOLFiniteState s scanBody).1 = none) :
    (evaluateHOLFiniteState s scanBody).2.locals.lookup (ofString "i") =
      some (.val (.word (w + 1))) := by
  unfold scanBody at hn ⊢
  obtain ⟨hn1, hn2, heq⟩ := seq_none _ _ _ hn
  rw [heq]
  obtain ⟨hn3, hn4, heq2⟩ := seq_none _ _ _ hn2
  rw [heq2]
  rw [evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) _ (Or.inl hn4)]
  have hkeep := evaluate_avoidsLocal_flowing (ofString "i") _ (by decide) s (Or.inl hn1)
  have hcount : CountedBody (ofString "i") 1
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 :=
    CountedBody.incr
  exact (hcount.run _ ((evaluateHOLFiniteState_metadata s _).1.trans hc) w
    (hkeep.trans hi) (Nat.zero_le _)).2.2.2.2 hn3 |>.1

theorem scan_active {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : ScanReady s)
    (ha : LoopActive scanCond s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w)) ∧ w.toNat < 16 := by
  obtain ⟨word, he, hw⟩ := ha
  rw [evalHOLFinite_eq_toExact] at he
  rcases hi : s.locals.lookup (ofString "i") with _ | vi
  · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he
  · rcases vi with ⟨⟨i⟩⟩ | fs | ⟨n, fs⟩
    · have hle : i.toNat ≤ 16 := by simpa [ScanReady, locN, hi] using hP.2
      refine ⟨i, rfl, ?_⟩
      by_contra hn
      have hi16 : i = 16 := BitVec.eq_of_toNat_eq (by simpa using (show i.toNat = 16 by omega))
      subst hi16
      rcases hf : s.locals.lookup (ofString "found") with _ | vf
      · simp [scanCond, evalHOLExact, evalListHOLExact, hi, hf] at he
      · rcases vf with ⟨⟨f⟩⟩ | fs | ⟨n, fs⟩ <;>
          simp [scanCond, evalHOLExact, evalListHOLExact, hi, hf,
            Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
            Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, valueIsWord, valueWord,
            wordOpHOL, wordOp] at he
        split at he <;> exact hw he.symm
    · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he
    · simp [scanCond, evalHOLExact, evalListHOLExact, hi] at he

theorem scan_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hP : ScanReady s) (ha : LoopActive scanCond s)
    (hnone : (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).1 = none) :
    ScanReady (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 ∧
      16 - locN (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 "i" <
        16 - locN s "i" := by
  obtain ⟨i, hi, hil⟩ := scan_active s hP ha
  have hnew := scan_advance (decClockHOLFinite s) hc i hi hnone
  have hadd : (i + 1).toNat = i.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)
  have hnloc : locN (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).2 "i" =
      i.toNat + 1 := by simp only [locN, hnew, hadd]
  have hiloc : locN s "i" = i.toNat := by simp only [locN, hi]
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_congr (s := s) rfl rfl rfl rfl hP.1), ?_⟩, ?_⟩
  · rw [hnloc]; omega
  · rw [hnloc, hiloc]; omega

theorem scan_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanReady (.while scanCond scanBody)
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank (fun s => 16 - locN s "i")
  · intro F s hP
    exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hP.1, hP.2⟩
  · refine weakenGuard (P := ScanReady) (Q := GuestInv) ?_ (fun s h => h.1)
    unfold scanBody
    refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
  · intro F s hc hP ha
    exact Nat.sub_le _ _
  · intro F s hc hP ha hf
    have hnc := evaluate_noTopContinue scanBody (by rfl) (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) scanBody).1 = none :=
      hf.elim id (fun h => False.elim (hnc h))
    exact scan_step s hc hP ha hnone

/-- The saved child index of the current scratch frame is in range. -/
def ScanEntry : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ memW s (locN s "top" + 16) ≤ 16

theorem scanEntry_locals : LocalsOnly ["top"] ScanEntry := by
  intro F s ls k hl hs
  have ht := locN_congr s ls k "top" (hl "top" (by simp))
  refine ⟨guestInv_with_locals_clock s ls k hs.1, ?_⟩
  change memW s (locN { s with locals := ls, clock := k } "top" + 16) ≤ 16
  rw [ht]
  exact hs.2

def scanProgram : ProgHOL 64 :=
  .dec (ofString "i") .one (.load .one (.op .add [.var .local (ofString "top"), .const 16]))
    (.seq (.while scanCond scanBody)
      (.store (.op .add [.var .local (ofString "top"), .const 16]) (.var .local (ofString "i"))))

theorem scan_program_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanEntry scanProgram
      ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) := by
  unfold scanProgram
  refine TerminatingProgBoundedOn.mono_bound (dec_guard _ _ _ ?_
    (TerminatingProgBoundedOn.seq_guestInv_after (scan_bound hn) (fun s h => h.1)
      (straight _ rfl))) (by omega)
  intro F s v hs hv
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "top" 16 v hv
  refine ⟨guestInv_setVar _ _ _ hs.1, ?_⟩
  rw [locN_setVar_same, hw]
  exact hs.2

/-- Extract the two nested loops from the installed body without changing its AST. -/
def fillBody : ProgHOL 64 :=
  match sourceFnBody Guest.Software.guestFn__node_rlp_fill with
  | .decCall _ _ _ _ (.decCall _ _ _ _
      (.seq _ (.seq _ (.seq _ (.seq _ (.dec _ _ _ (.seq (.while _ b) _))))))) => b
  | _ => .skip

def fillSearch : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq p _)))) => p
  | _ => .skip

def fillTail : ProgHOL 64 :=
  match fillBody with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq _ p)))) => p
  | _ => .skip

theorem fillSearch_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp») :
    TerminatingProgBoundedOn ScanEntry fillSearch
      (max (max (K.«_node_needs_rlp» + 1) 0)
        (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0)) := by
  change TerminatingProgBoundedOn ScanEntry
    (.ite _ (.ite _ (.seq _ (.seq _ (.call _ _ _))) .skip)
      (.ite _ scanProgram .skip)) _
  apply TerminatingProgBoundedOn.ite_on
  · apply TerminatingProgBoundedOn.ite_on
    · refine weakenGuard (P := ScanEntry) (Q := GuestInv) ?_ (fun s h => h.1)
      exact TerminatingProgBoundedOn.mono_bound
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
            (TerminatingProgBoundedOn.call_guestInv hn _ _))) (by omega)
    · exact weakenGuard (straight _ rfl) (fun s h => h.1)
  · exact TerminatingProgBoundedOn.ite_on (scan_program_bound hn)
      (weakenGuard (straight _ rfl) (fun s h => h.1))

theorem fillTail_bound
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn GuestInv fillTail
      (max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)) := by
  change TerminatingProgBoundedOn GuestInv (.ite _ (.decCall _ _ _ _
    (.seq _ (.seq _ (.seq _ (.seq (.call _ _ _) (.assign _ _ _))))))
    (.seq (.call _ _ _) (.assign _ _ _))) _
  apply TerminatingProgBoundedOn.ite_on
  · refine TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.decCall_guestInv ha _ _ _
        (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
          (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
            (TerminatingProgBoundedOn.seq_guestInv (straight _ rfl)
              (TerminatingProgBoundedOn.seq_guestInv
                (TerminatingProgBoundedOn.call_guestInv hb _ _) (straight _ rfl)))))) (by omega)
  · exact TerminatingProgBoundedOn.mono_bound
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hf _ _) (straight _ rfl)) (by omega)

def fillBodyCost : Nat :=
  max (max (K.«_node_needs_rlp» + 1) 0)
    (max ((16 + 1) * ((K.«_node_needs_rlp» + 1) + 1)) 0) +
  max ((K.«scratch_alloc» + 1) + (K.«_node_rlp_begin» + 1)) (K.«_node_rlp_finish» + 1)

theorem fillBody_bound
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish») :
    TerminatingProgBoundedOn ScanEntry fillBody fillBodyCost := by
  change TerminatingProgBoundedOn ScanEntry (.dec _ _ _ (.dec _ _ _ (.dec _ _ _
    (.dec _ _ _ (.seq fillSearch fillTail))))) _
  exact TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
    (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
      (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
        (TerminatingProgBoundedOn.dec_onLocals scanEntry_locals _ (by decide) _ _
          (TerminatingProgBoundedOn.seq_guestInv_after (fillSearch_bound hn) (fun s h => h.1)
            (fillTail_bound ha hb hf)))))

/-! The search phase preserves the allocator globals. -/

def needsGood (f : MlS) : Bool := f == ofString "_node_needs_rlp"

theorem needs_bodies (watched : MlS) :
    ∀ function, needsGood function = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG watched needsGood body = true := by
  intro f hf vs b callee rs hl
  have hfn : f = ofString "_node_needs_rlp" := by simpa only [needsGood, beq_iff_eq] using hf
  subst hfn
  have heq := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ b _ rs vs callee
    (lookup_of_guestAst_getElem 283 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn__node_needs_rlp) rfl) hl
  subst heq
  rfl

theorem search_globals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s fillSearch).2.globals = s.globals := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  exact InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG key needsGood (needs_bodies key)
    fillSearch rfl s hc

theorem search_arena {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ArenaReady s) :
    ArenaReady (evaluateHOLFiniteState s fillSearch).2 := by
  refine ⟨guestInv_evaluate _ _ hs.1, ?_⟩
  simpa only [ArenaOK, globN, search_globals s hc] using hs.2

/-- Remaining allocator capacity; either a scratch push or a nonempty encoding lowers it. -/
def allocationMeasure : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat :=
  fun s => heapLimit - globN s "heap_ptr" + (globN s "scratch_ptr" - scratchStart)

theorem allocationMeasure_le {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : ArenaReady s) : allocationMeasure s ≤ 2 ^ 62 := by
  have hsp := hs.2.2.2.2.2.1
  dsimp only [allocationMeasure, heapLimit, scratchStart, scratchEnd] at *
  omega

theorem allocationMeasure_decreases {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (_hs : ArenaReady s) (ht : ArenaReady t) (hg : AllocatorGrows s t)
    (hstrict : globN s "heap_ptr" < globN t "heap_ptr" ∨
      globN t "scratch_ptr" < globN s "scratch_ptr") :
    allocationMeasure t < allocationMeasure s := by
  have hhp := ht.2.2.1
  have hsl : scratchStart ≤ globN t "scratch_ptr" := ht.2.2.2.1.trans ht.2.2.2.2.1
  rcases hg with ⟨hh, hsp⟩
  unfold allocationMeasure
  omega

theorem scratch48_progress {F : Type} (s t : PanSemStateFiniteExact 64 F) (p : Nat)
    (hf : FreshScratch s t p 48) (hp : globN t "scratch_ptr" = p) :
    globN t "scratch_ptr" + 48 ≤ globN s "scratch_ptr" := by
  rw [hp]
  exact hf.2.2.1.2

/-! Semantic composition for the scratch-frame setup. -/

/-- A declaration-call carries the resumed invariant through its continuation, and
restores only the declared local when the continuation falls through. -/
theorem hoare_decCall_flow
    {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hres : DecCallResumeOn P R name fname args)
    (hcont : Hoare R cont (fun r t => r = none → Q t))
    (hQ : LocalsOnly names Q) (hne : ∀ n ∈ names, ofString n ≠ name) :
    Hoare P (.decCall name shape fname args cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hc hs hnt => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases ha : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | vs
  · simp only [ha]; intro he; cases he
  · simp only [ha] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨b, callee, ret⟩
    · simp only [hl]; intro he; cases he
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) b).1
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨r, t⟩
        simp only [hr] at hnt hm ⊢
        change t.code = s.code at hm
        cases r with
        | none => intro he; cases he
        | some r =>
          cases r with
          | returned v =>
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                shapeEqHOL (shapeOfHOLExact v) ret) = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              have hR := hres s vs b callee ret v t hc hs ha hl hr
              have h := hcont.run (setVarHOLFinite name v { t with locals := s.locals })
                (hm.trans hc) hR hnt
              intro hn
              exact hQ _ _ _
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hne n hn)) (h hn)
            · simp only [hsh, ↓reduceIte]; intro he; cases he
          | timeOut => simp at hnt
          | _ => intro he; cases he

/-- The single argument of a successful one-parameter lookup is the callee's
parameter value. This also covers literal allocation sizes. -/
theorem callee_param_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname pk : MlS) (sk : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : s.code.lookup fname = some ([(pk, sk)], body, ret))
    (v : ValueHOL 64) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hlook : lookupCodeHOLFinite s.code.lookup fname [v] = some (body', callee, ret')) :
    callee.lookup pk = some v := by
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
    · have heq := Option.some.inj raw
      rcases Prod.mk.inj heq with ⟨-, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, -⟩
      subst hloc
      simp
    · cases raw

def ScratchAllocated48 (dst : String) (old : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ globN s "scratch_ptr" + 48 ≤ old ∧
    locN s dst = globN s "scratch_ptr" ∧ WordsOK s (locN s dst, 48)

theorem scratch48_resume (dst : String) (old : Nat)
    (hret : Returns ArenaReady (fun s post p => FreshScratch s post p (locN s "n") ∧
      globN post "scratch_ptr" = p) (ofString "scratch_alloc")) :
    DecCallResumeOn (fun s => ArenaReady s ∧ globN s "scratch_ptr" = old)
      (ScratchAllocated48 dst old) (ofString dst) (ofString "scratch_alloc") [.const 48] := by
  intro F s vs b callee ret v post hc hs ha hl hr
  have hav : vs = [.val (.word 48)] := by
    rw [evalListHOLFinite_eq_toExact] at ha
    simpa only [evalListHOLExact, evalHOLExact, Option.some.injEq] using ha.symm
  subst vs
  have hn := callee_param_value s (ofString "scratch_alloc") (ofString "n") .one _ _
    (by
      rw [hc]
      exact lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_scratch_alloc) rfl)
    (.val (.word 48)) b callee ret hl
  have hspec := FunSpec.at_lookup hret s hc [.val (.word 48)] b callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hs.1) (by rw [hr]; simp)
  rw [hr] at hspec
  obtain ⟨w, rfl, hA, hG, hfresh, hsp⟩ := hspec _ rfl
  have hn48 : locN (callEntryStateHOLFinite s callee) "n" = 48 := by
    simp only [locN, callEntryStateHOLFinite, hn]
    rfl
  rw [hn48] at hfresh
  have hp : globN post "scratch_ptr" + 48 ≤ old := by
    have h := scratch48_progress (callEntryStateHOLFinite s callee) post w.toNat hfresh hsp
    simpa only [globN, callEntryStateHOLFinite, ← hs.2] using h
  refine ⟨localsFree_arenaReady post _ _ hA, hp, ?_, ?_⟩
  · simpa [locN, globN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      using hsp.symm
  · simpa [locN, WordsOK, WordAt, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      using hfresh.2.2.2

/-! The encoding closure never changes the scratch or frame-memory pointers. -/

def encodingGood (f : MlS) : Bool :=
  (["_node_rlp_begin", "_node_rlp_finish", "alloc", "keccak256", "keccak_absorb_block", "keccak_f1600", "memcpy", "memzero", "mpt_fail", "nibble_list_to_compact", "node_hash_cached", "node_ref_len", "node_write_ref", "rlp_be_len", "rlp_bytes_encoded_len", "rlp_encode_bytes", "rlp_encode_list_header", "rlp_header_len", "rlp_list_header_len", "rlp_put_be", "rlp_value_encoded_len", "rlp_write_header", "trap_with"] : List String).map ofString |>.contains f

theorem encoding_bodies (watched : MlS)
    (hw : watched = ofString "scratch_ptr" ∨ watched = ofString "frame_mem_ptr") :
    ∀ f, encodingGood f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG watched encodingGood body = true := by
  intro f hf values body callee rs hl
  simp only [encodingGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn__node_rlp_begin) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn__node_rlp_finish) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_alloc) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak256) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memcpy) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_memzero) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_node_hash_cached) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_node_ref_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_node_write_ref) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_be_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_header_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_put_be) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_rlp_write_header) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee
      (lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide)
        (extractFn Guest.Software.guestFn_trap_with) rfl) hl
    subst hb
    rcases hw with rfl | rfl <;> rfl

theorem encoding_keeps_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (hc : s.code = originalRuntimeCode)
    (hp : InitECandidate.Solver.GuestGlobalKeep.keepsG (ofString "scratch_ptr") encodingGood p = true) :
    globN (evaluateHOLFiniteState s p).2 "scratch_ptr" = globN s "scratch_ptr" := by
  have h := InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG (ofString "scratch_ptr")
    encodingGood (encoding_bodies _ (Or.inl rfl)) p hp s hc
  simp only [globN, h]

/-- An invariant for an ordinary loop needs to be preserved only by active,
fall-through iterations. Callee returns and errors do not create obligations
on cleared caller locals. -/
theorem while_preserves_none
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hbreak : noTopBreak body = true) (hcont : noTopContinue body = true)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s → LoopActive cond s →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      P (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hs : P s) (hn : (evaluateHOLFiniteState s (.while cond body)).1 = none) :
    P (evaluateHOLFiniteState s (.while cond body)).2 := by
  have recur : ∀ k {F : Type} (s : PanSemStateFiniteExact 64 F), s.clock = k →
      s.code = originalRuntimeCode → P s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      P (evaluateHOLFiniteState s (.while cond body)).2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F s hk hc hs hn
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hn ⊢
      split
      · rename_i w hw
        simp only [hw] at hn
        by_cases hz : w = 0
        · rw [if_neg (by simp [hz])]
          exact hs
        · rw [if_pos hz] at hn ⊢
          by_cases hclock : s.clock = 0
          · simp [hclock] at hn
          · rw [if_neg hclock] at hn ⊢
            have hb := hstep s hc hs ⟨w, hw, hz⟩
            have hnb := evaluate_noTopBreak body hbreak (decClockHOLFinite s)
            have hnc := evaluate_noTopContinue body hcont (decClockHOLFinite s)
            have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite s) body).1
            have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
            rcases hr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r, t⟩
            simp only [hr] at hn hb hnb hnc hmeta hle ⊢
            change t.code = s.code at hmeta
            change t.clock ≤ s.clock - 1 at hle
            cases r with
            | none =>
              exact ih t.clock (by omega) t rfl (hmeta.trans hc) (hb rfl) hn
            | some r =>
              cases r with
              | «break» => exact False.elim (hnb rfl)
              | «continue» => exact False.elim (hnc rfl)
              | _ => cases hn
      · split at hn <;> simp_all
  exact recur s.clock s rfl hc hs hn

theorem scan_exit_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ScanReady s)
    (hn : (evaluateHOLFiniteState s (.while scanCond scanBody)).1 = none) :
    ScanReady (evaluateHOLFiniteState s (.while scanCond scanBody)).2 :=
  while_preserves_none scanCond scanBody rfl rfl
    (fun s hc hs ha hn => (scan_step s hc hs ha hn).1) s hc hs hn

theorem store_arena (dst src : ExpHOL 64) :
    Hoare ArenaReady (.store dst src) (fun _ t => ArenaReady t) := by
  refine ⟨fun {F} s _ hs _ => ?_⟩
  rw [evaluateHOLFiniteState_store]
  repeat' split
  all_goals exact ⟨guestInv_congr (s := s) rfl rfl rfl rfl hs.1, hs.2⟩

/-- A successful word store changes exactly its destination cell. -/
theorem store_word_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : ExpHOL 64) (a w : BitVec 64)
    (hd : evalAt s dst = some (.val (.word a)))
    (hv : evalAt s src = some (.val (.word w)))
    (hn : (evaluateHOLFiniteState s (.store dst src)).1 = none) :
    (evaluateHOLFiniteState s (.store dst src)).2 =
      { s with memory := fun b => if b = a then .word w else s.memory b } := by
  rw [evaluateHOLFiniteState_store] at hn ⊢
  simp only [evalAt] at hd hv
  simp only [hd, hv, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hn ⊢
  by_cases hdom : s.memaddrs a
  · simp only [hdom, ↓reduceIte]
  · simp only [hdom, ↓reduceIte] at hn
    cases hn

theorem scan_exit_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ScanReady s)
    (hi : ∃ i, s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : (evaluateHOLFiniteState s (.while scanCond scanBody)).1 = none) :
    let t := (evaluateHOLFiniteState s (.while scanCond scanBody)).2
    ScanReady t ∧ ∃ i, t.locals.lookup (ofString "i") = some (.val (.word i)) := by
  refine while_preserves_none (P := fun s => ScanReady s ∧
      ∃ i, s.locals.lookup (ofString "i") = some (.val (.word i)))
    scanCond scanBody rfl rfl ?_ s hc ⟨hs, hi⟩ hn
  intro F s hc hs ha hn
  refine ⟨(scan_step s hc hs.1 ha hn).1, ?_⟩
  obtain ⟨i, hi, _⟩ := scan_active s hs.1 ha
  exact ⟨i + 1, scan_advance (decClockHOLFinite s) hc i hi hn⟩

theorem evalAt_addL {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (v k : BitVec 64) (hv : s.locals.lookup (ofString name) = some (.val (.word v))) :
    evalAt s (.op .add [.var .local (ofString name), .const k]) =
      some (.val (.word (v + k))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, hv,
    valueIsWord, valueWord, wordOpHOL, wordOp]

/-- Saving a completed scan writes an in-range index back to the current frame. -/
theorem save_scan_index {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : ScanReady s) (t i : BitVec 64)
    (ht : s.locals.lookup (ofString "top") = some (.val (.word t)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "top"), .const 16])
        (.var .local (ofString "i")))).1 = none) :
    ScanEntry (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "top"), .const 16])
        (.var .local (ofString "i")))).2 := by
  have he := store_word_none s _ _ (t + 16) i (evalAt_addL s "top" t 16 ht)
    (by simpa only [evalAt, evalHOLExact] using hi) hn
  have hil : i.toNat ≤ 16 := by simpa only [locN, hi] using hs.2
  refine ⟨guestInv_evaluate _ _ hs.1, ?_⟩
  rw [he]
  have hadd : BitVec.ofNat 64 (t.toNat + (16 : Nat)) = t + (16 : BitVec 64) := by
    rw [BitVec.add_def]
    rfl
  simpa only [memW, locN, ht, hadd, ↓reduceIte] using hil

theorem scan_run_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ScanReady s) (t i : BitVec 64)
    (ht : s.locals.lookup (ofString "top") = some (.val (.word t)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hn : (evaluateHOLFiniteState s
      (.seq (.while scanCond scanBody)
        (.store (.op .add [.var .local (ofString "top"), .const 16])
          (.var .local (ofString "i"))))).1 = none) :
    ScanEntry (evaluateHOLFiniteState s
      (.seq (.while scanCond scanBody)
        (.store (.op .add [.var .local (ofString "top"), .const 16])
          (.var .local (ofString "i"))))).2 := by
  obtain ⟨hwhile, hstore, heq⟩ := seq_none _ _ _ hn
  rw [heq]
  obtain ⟨hready, i', hi'⟩ := scan_exit_word s hc hs ⟨i, hi⟩ hwhile
  have htop := evaluate_avoidsLocal_flowing (ofString "top")
    (.while scanCond scanBody) (by decide) s (Or.inl hwhile)
  exact save_scan_index _ hready t i' (htop.trans ht) hi' hstore

theorem evalAt_loadL_base {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (k : BitVec 64) (v : ValueHOL 64)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString name), .const k])) = some v) :
    ∃ t, s.locals.lookup (ofString name) = some (.val (.word t)) := by
  cases ht : s.locals.lookup (ofString name) with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, ht] at hv
  | some tv =>
    cases tv with
    | val tw =>
      cases tw with
      | word t => exact ⟨t, rfl⟩
    | rStruct fs => simp [evalAt, evalHOLExact, evalListHOLExact, ht, valueIsWord] at hv
    | nStruct n fs => simp [evalAt, evalHOLExact, evalListHOLExact, ht, valueIsWord] at hv

theorem scan_program_preserves {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ScanEntry s)
    (hn : (evaluateHOLFiniteState s scanProgram).1 = none) :
    ScanEntry (evaluateHOLFiniteState s scanProgram).2 := by
  unfold scanProgram at hn ⊢
  rw [evaluateHOLFiniteState_dec_total] at hn ⊢
  dsimp only at hn ⊢
  revert hn
  split <;> intro hn
  · cases hn
  · rename_i v hv
    have hv' : evalAt s (.load .one (.op .add [.var .local (ofString "top"), .const 16])) =
        some v := hv
    obtain ⟨t, ht⟩ := evalAt_loadL_base s "top" 16 v hv'
    obtain ⟨i, rfl, hi⟩ := evalAt_loadL s "top" 16 v hv'
    revert hn
    split <;> intro hn
    · dsimp only at hn ⊢
      have hR : ScanReady (setVarHOLFinite (ofString "i") (.val (.word i)) s) := by
        refine ⟨guestInv_setVar _ _ _ hs.1, ?_⟩
        rw [locN_setVar_same, hi]
        exact hs.2
      have hkeep : (setVarHOLFinite (ofString "i") (.val (.word i)) s).locals.lookup
          (ofString "top") = some (.val (.word t)) := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "i" ≠ ofString "top" by decide]
      have hnew := scan_run_ready (setVarHOLFinite (ofString "i") (.val (.word i)) s) hc hR t i hkeep
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hn
      apply scanEntry_locals _ _ _ _ hnew
      intro n hn
      have hn' : n = "top" := by simpa only [List.mem_singleton] using hn
      subst n
      exact resVarEq_lookup_ne _ _ _ _ (by decide)
    · cases hn

theorem hoare_flow_seq
    {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p q : ProgHOL 64}
    (hp : Hoare P p (fun r t => r = none → R t))
    (hq : Hoare R q (fun r t => r = none → Q t)) :
    Hoare P (.seq p q) (fun r t => r = none → Q t) := by
  apply Hoare.seq (R := R) (h2 := hq)
  refine ⟨fun s hc hs hn => ⟨hp.run s hc hs hn, ?_⟩⟩
  intro hne heq
  exact False.elim (hne heq)

theorem hoare_assign_flow
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {names : List String}
    (hP : LocalsOnly names P) (name : MlS) (hne : ∀ n ∈ names, ofString n ≠ name)
    (e : ExpHOL 64) :
    Hoare P (.assign .local name e) (fun r t => r = none → P t) := by
  apply Hoare.assign
  · intro F s v hs _ _
    exact hP.setVar hne v s hs
  · intro F s _ he
    cases he

theorem call_ro_local
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {names : List String}
    (hP : LocalsOnly names P)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {fname : MlS} (hro : ReadOnlyFn fname) (dst : MlS)
    (hne : ∀ n ∈ names, ofString n ≠ dst) (args : List (ExpHOL 64)) :
    Hoare P (.call (some (some (.local, dst), none)) fname args)
      (fun r t => r = none → P t) := by
  refine ⟨fun {F} s hc hs hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases ha : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) args with _ | vs
  · simp only [ha]; intro he; cases he
  · simp only [ha] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨b, callee, ret⟩
    · simp only [hl]; intro he; cases he
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨r, t⟩
        simp only [hr] at hnt ⊢
        cases r with
        | none => intro he; cases he
        | some r =>
          cases r with
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              split
              · intro _
                have hq := FunSpec.at_lookup hro s hc vs b callee ret hl
                  (guestInv_callEntry s callee (hPG s hs)) (by rw [hr]; simp)
                rw [hr] at hq
                have he := hq (Or.inl ⟨v, rfl⟩)
                dsimp only at he
                have he' : ({ t with locals := s.locals } : PanSemStateFiniteExact 64 F) =
                    { s with clock := t.clock } := by rw [he]; rfl
                rw [he']
                exact hP.setVar hne v _ (hP s s.locals t.clock (fun _ _ => rfl) hs)
              · intro he; cases he
            · simp only [hsh, ↓reduceIte]; intro he; cases he
          | timeOut => simp at hnt
          | _ => intro he; cases he

theorem save_frame_index_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs : GuestInv s) (i : BitVec 64) (hi : i.toNat ≤ 16)
    (hn : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "top"), .const 16]) (.const i))).1 = none) :
    ScanEntry (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "top"), .const 16]) (.const i))).2 := by
  cases ht : s.locals.lookup (ofString "top") with
  | none =>
    simp [evaluateHOLFiniteState_store, evalHOLExact, evalListHOLExact, ht] at hn
  | some tv =>
    cases tv with
    | val tw =>
      cases tw with
      | word t =>
        have he := store_word_none s _ _ (t + 16) i (evalAt_addL s "top" t 16 ht) rfl hn
        refine ⟨guestInv_evaluate _ _ hs, ?_⟩
        rw [he]
        have hadd : BitVec.ofNat 64 (t.toNat + (16 : Nat)) = t + (16 : BitVec 64) := by
          rw [BitVec.add_def]
          rfl
        simpa only [memW, locN, ht, hadd, ↓reduceIte] using hi
    | rStruct fs =>
      simp [evaluateHOLFiniteState_store, evalHOLExact, evalListHOLExact, ht, valueIsWord] at hn
    | nStruct n fs =>
      simp [evaluateHOLFiniteState_store, evalHOLExact, evalListHOLExact, ht, valueIsWord] at hn

theorem fillSearch_preserves (hro : ReadOnlyFn (ofString "_node_needs_rlp")) :
    Hoare ScanEntry fillSearch (fun r t => r = none → ScanEntry t) := by
  change Hoare ScanEntry (.ite _ (.ite _ (.seq _ (.seq _ (.call _ _ _))) .skip)
    (.ite _ scanProgram .skip)) _
  apply Hoare.ite
  · apply Hoare.mono (P' := ScanEntry) ?_ (fun s h => h.1)
    apply Hoare.ite
    · apply Hoare.mono (P' := ScanEntry) ?_ (fun s h => h.1)
      apply hoare_flow_seq (R := ScanEntry)
      · exact ⟨fun s _ hs _ hn => save_frame_index_const s hs.1 1 (by decide) hn⟩
      · exact hoare_flow_seq
          (hoare_assign_flow scanEntry_locals _ (by decide) _)
          (call_ro_local scanEntry_locals (fun s h => h.1) hro _ (by decide) _)
    · exact Hoare.skip (fun s h _ => h.1)
    · intro F s hs he; cases he
  · apply Hoare.mono (P' := ScanEntry) ?_ (fun s h => h.1)
    apply Hoare.ite
    · exact ⟨fun s hc hs _ hn => scan_program_preserves s hc hs.1 hn⟩
    · exact Hoare.skip (fun s h _ => h.1)
    · intro F s hs he; cases he
  · intro F s hs he; cases he

/-! The allocator return proof is adapted from the checked M25 delivery on
`origin/wave8/integration`; R10 adds the successful-entry lookup argument. -/
namespace Alloc
open InitECandidate.Solver.HeapPotential

private theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem ordinaryDomain_of_aligned_heap (addr : Nat) (halign : addr % 8 = 0)
    (hlo : sourceBase ≤ addr) (hhi : addr < heapLimit) :
    ordinaryDomain (BitVec.ofNat 64 addr) := by
  refine (Flapjack.Compiler.Backend.StackRemove.mem_addresses _ _ _).mpr
    ⟨(addr - sourceBase) / 8, ?_, ?_⟩
  · simp only [heapLimit, scratchStart, sourceBase, stackStart, ramEnd, ramStart, ramSize,
      stackSize, globalsWords] at hlo hhi ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 addr).toNat = (BitVec.ofNat 64 sourceBase +
      BitVec.ofNat 64 ((addr - sourceBase) / 8) * BitVec.ofNat 64 8).toNat
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
    simp only [BitVec.toNat_ofNat]
    simp only [heapLimit, scratchStart, sourceBase] at hlo hhi ⊢
    omega

theorem alloc_returned_props {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hP : ArenaReady s)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat (locN s "n") := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rcases harena : hP with ⟨hginv, hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩
  -- `heap_ptr` must be a word because `sourceBase > 0` and `globN s "heap_ptr" ≥ sourceBase`
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨p, hp_lookup⟩ := hp_word
  have hp_glob : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lookup]
  -- `n` must be a word for `alloc` body to return (the first `ite` evaluates local `"n"`).
  have hn_word : ∃ n : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rcases hl : s.locals.lookup (ofString "n") with _ | lv
    · exfalso
      rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
      have hp_ev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
      dsimp only at hret
      rw [hp_ev] at hret
      have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only at hret
      rw [if_pos hsh_p] at hret
      dsimp only at hret
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = none := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
          show ofString "p" ≠ ofString "n" by decide]
      simp [evalHOLExact, evalListHOLExact, hnl] at hret
    · rcases lv with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨n, rfl⟩
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
        dsimp only at hret
        rw [hp_ev] at hret
        have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hret
        rw [if_pos hsh_p] at hret
        dsimp only at hret
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = some (.rStruct fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
            show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hret
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
        dsimp only at hret
        rw [hp_ev] at hret
        have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hret
        rw [if_pos hsh_p] at hret
        dsimp only at hret
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = some (.nStruct nm fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
            show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hret
  obtain ⟨n, hn_lookup⟩ := hn_word
  have hn_loc : locN s "n" = n.toNat := by simp [locN, hn_lookup]
  -- Step through `alloc` body explicitly to get the exact post state and both guard inequalities
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hp_eval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hret ⊢
  rw [hp_eval] at hret ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hret ⊢
  rw [if_pos hsh_p] at hret ⊢
  dsimp only at hret ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc_p : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lookup,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc_p,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hret
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret hret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact absurd hret (hno_ret v)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hret ⊢
    dsimp only at hret ⊢
    rw [evaluateHOLFiniteState_dec_total] at hret ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc_p,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hret ⊢
    rw [hq_eval] at hret ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hret ⊢
    rw [if_pos hsh_q] at hret ⊢
    dsimp only at hret ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hret
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret hret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact absurd hret (hno_ret v)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2] at hret ⊢
      dsimp only at hret ⊢
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end] at hret ⊢
      dsimp only at hret ⊢
      injection hret with hr
      injection hr with hr'
      subst hr'
      -- Capture the exact evaluated post state
      set post : PanSemStateFiniteExact 64 F :=
        { locals :=
            ((setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                          qState).emptyLocalsHOLFinite.locals.resVarEq
                  (ofString "q", pState.locals.lookup (ofString "q"))).resVarEq
              (ofString "p", s.locals.lookup (ofString "p")),
          globals :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.globals,
          structs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.structs,
          code :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.code,
          eshapes :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.eshapes,
          memory :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.memory,
          memaddrs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.memaddrs,
          shMemaddrs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.shMemaddrs,
          clock :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.clock,
          be :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.be,
          ffi :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.ffi,
          baseAddr :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.baseAddr,
          topAddr :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.topAddr }
      -- Arithmetic bounds on `p`, `n`, `q`
      have hcMax_val : cMax.toNat = 2952790016 := rfl
      have hhl_val : heapLimit = 2952790016 := rfl
      have hp_le_cMax : p.toNat ≤ cMax.toNat := by omega
      have hsub_toNat : (cMax - p).toNat = cMax.toNat - p.toNat := by
        rw [BitVec.toNat_sub_of_le]
        exact BitVec.le_def.mpr hp_le_cMax
      have hn_le : n.toNat ≤ 2952790016 - p.toNat := by omega
      have h7 : (7 : BitVec 64).toNat = 7 := rfl
      have hn7 : (n + 7).toNat = n.toNat + 7 := by
        rw [BitVec.toNat_add, h7]
        omega
      have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
        rw [BitVec.toNat_add, hn7]
        omega
      have hq_toNat : q.toNat = (p.toNat + n.toNat + 7) / 8 * 8 := by
        have hq1 := and_neg8_toNat (p + (n + 7))
        change q.toNat = _ at hq1
        rw [hq1, hsum]
      have hp_mod8 : p.toNat % 8 = 0 := by omega
      have hq_exact : q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 := by omega
      have hq_le_hl : q.toNat ≤ heapLimit := by omega
      have hpost_hp : globN post "heap_ptr" = q.toNat := by
        simp [post, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hpost_fm : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        simp [post, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
      have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
        simp [post, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
      have hpost_ginv : GuestInv post := ⟨hginv.code, hginv.memaddrs, hginv.shMemaddrs, hginv.baseAddr⟩
      have hpost_arena : ArenaOK post := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpost_hp]; omega
        · rw [hpost_hp]; exact hq_le_hl
        · rw [hpost_fm]; exact hfm_lo
        · rw [hpost_fm, hpost_sp]; exact hfm_hi
        · rw [hpost_sp]; exact hsp_hi
        · rw [hpost_hp]; omega
        · rw [hpost_fm]; exact hfm_al
        · rw [hpost_sp]; exact hsp_al
      have hgrows : AllocatorGrows s post := by
        refine ⟨?_, ?_⟩
        · rw [hp_glob, hpost_hp]; omega
        · rw [hpost_sp]
      refine ⟨p, rfl, ⟨hpost_ginv, hpost_arena⟩, hgrows, ?_⟩
      refine ⟨hp_mod8, ?_, ?_⟩
      · rw [hp_glob, hpost_hp, hn_loc]
        exact ⟨Nat.le_refl _, by omega⟩
      · rw [hn_loc]
        refine ⟨hp_mod8, by omega, ?_⟩
        intro k hk
        dsimp only at hk ⊢
        have haddr_lo : sourceBase ≤ p.toNat + 8 * k := by omega
        have haddr_hi : p.toNat + 8 * k < heapLimit := by omega
        have haddr_al : (p.toNat + 8 * k) % 8 = 0 := by omega
        have hdom : post.memaddrs (BitVec.ofNat 64 (p.toNat + 8 * k)) := by
          change s.memaddrs _
          rw [hginv.memaddrs]
          exact ordinaryDomain_of_aligned_heap (p.toNat + 8 * k) haddr_al haddr_lo haddr_hi
        cases hcell : post.memory (BitVec.ofNat 64 (p.toNat + 8 * k)) with
        | word cw => exact ⟨cw, hdom, hcell⟩

/-- `alloc` (AST line 66): returns a fresh aligned heap block of `n` bytes. -/
theorem «rt_alloc» :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
      (ofString "alloc") := by
  refine ⟨_, _, _, lookup_alloc, ?_⟩
  intro F s hcode hP _hentry _hnt v hret
  exact alloc_returned_props s hcode hP v hret

end Alloc

/-- A normally returned allocation of a positive size strictly advances the heap. -/
theorem alloc_nonempty_progress {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hs : ArenaReady s) (v : ValueHOL 64)
    (hn : 0 < locN s "n")
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v)) :
    globN s "heap_ptr" < globN
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2 "heap_ptr" := by
  obtain ⟨w, _, _, _, hfresh⟩ := Alloc.alloc_returned_props s hc hs v hr
  have hb := hfresh.2.1
  dsimp only [Inside] at hb
  omega

theorem begin_keeps_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_rlp_begin)).2
      "scratch_ptr" = globN s "scratch_ptr" :=
  encoding_keeps_scratch s _ hc rfl

theorem finish_keeps_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) :
    globN (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__node_rlp_finish)).2
      "scratch_ptr" = globN s "scratch_ptr" :=
  encoding_keeps_scratch s _ hc rfl

def fillCond : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "top")) (.const 0)

/-- The exact outer-loop bound, once its reachable-state invariant and allocator
progress have been established. The invariant is kept abstract so it can carry
the node and scratch-frame ownership facts needed by the concrete callees. -/
theorem fill_loop_bound
    {I : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), I s → I (decClockHOLFinite s))
    (hguard : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), I s → ArenaReady s ∧ ScanEntry s)
    (hn : TerminatingFunBoundedOn GuestInv (ofString "_node_needs_rlp") K.«_node_needs_rlp»)
    (ha : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc»)
    (hb : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_begin") K.«_node_rlp_begin»)
    (hf : TerminatingFunBoundedOn GuestInv (ofString "_node_rlp_finish") K.«_node_rlp_finish»)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      I s → LoopActive fillCond s →
      (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).1 = none →
      let t := (evaluateHOLFiniteState (decClockHOLFinite s) fillBody).2
      I t ∧ AllocatorGrows s t ∧ (globN s "heap_ptr" < globN t "heap_ptr" ∨
        globN t "scratch_ptr" < globN s "scratch_ptr")) :
    TerminatingProgBoundedOn I (.while fillCond fillBody)
      ((2 ^ 62 + 1) * (fillBodyCost + 1)) := by
  apply TerminatingProgBoundedOn.while_rank allocationMeasure hdec
    (weakenGuard (fillBody_bound hn ha hb hf) (fun s hs => (hguard s hs).2))
  · intro F s _ hs _
    exact allocationMeasure_le s (hguard s hs).1
  · intro F s hc hs hact hflow
    have hnc := evaluate_noTopContinue fillBody (by rfl) (decClockHOLFinite s)
    have hnone := hflow.elim id (fun h => False.elim (hnc h))
    obtain ⟨ht, hg, hp⟩ := hstep s hc hs hact hnone
    exact ⟨ht, allocationMeasure_decreases _ _ (hguard s hs).1 (hguard _ ht).1 hg hp⟩

/-! ### Encoding closure write-frame and heap monotonicity (`_node_rlp_begin` / `_node_rlp_finish`) -/

def encodingNonHeapGlobals (watched : MlS) : Prop :=
  watched ≠ ofString "heap_ptr"

theorem encoding_bodies_nonHeap (watched : MlS)
    (hw : watched ≠ ofString "heap_ptr") :
    ∀ f, encodingGood f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      InitECandidate.Solver.GuestGlobalKeep.keepsG watched encodingGood body = true := by
  intro f hf values body callee rs hl
  simp only [encodingGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  have hne : (ofString "heap_ptr" == watched) = false := beq_false_of_ne (Ne.symm hw)
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_begin) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_finish) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl) hl
    subst hb
    have hbody : InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_alloc).body =
        sourceFnBody Guest.Software.guestFn_alloc := rfl
    rw [hbody]
    have htw : encodingGood (ofString "trap_with") = true := by decide
    simp [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_alloc,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.GuestGlobalKeep.keepsG, htw, hne]
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak256) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memzero) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_hash_cached) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_ref_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_write_ref) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_be_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_header_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_put_be) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_write_header) rfl) hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 3 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl) hl; subst hb; rfl

theorem encoding_keeps_nonHeap {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : ProgHOL 64) (hc : s.code = originalRuntimeCode) (watched : MlS)
    (hw : watched ≠ ofString "heap_ptr")
    (hp : InitECandidate.Solver.GuestGlobalKeep.keepsG watched encodingGood p = true) :
    (evaluateHOLFiniteState s p).2.globals.lookup watched = s.globals.lookup watched :=
  InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG watched
    encodingGood (encoding_bodies_nonHeap watched hw) p hp s hc

private def heapSafeProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => heapSafeProg body
  | .seq first second => heapSafeProg first && heapSafeProg second
  | .ite _ yes no => heapSafeProg yes && heapSafeProg no
  | .while _ body => heapSafeProg body
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ | .shMemStore _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | .decCall _ _ function _ continuation => encodingGood function && heapSafeProg continuation
  | .call none function _ => encodingGood function
  | .call (some (none, none)) function _ => encodingGood function
  | .call (some (some (.local, _), none)) function _ => encodingGood function
  | _ => false

private theorem alloc_body_heap_mono {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : ArenaOK s) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ArenaOK post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rcases hA with ⟨hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | _ | _
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨p, hp_lk⟩ := hp_word
  have hp_glob : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lk]
  have hsame : ∀ t : PanSemStateFiniteExact 64 F, t.globals = s.globals →
      ArenaOK t ∧ globN s "heap_ptr" ≤ globN t "heap_ptr" := by
    intro t hg
    exact ⟨by simpa only [ArenaOK, globN, hg] using
      (⟨hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩ : ArenaOK s),
      by simp [globN, hg]⟩
  have htrap_globals : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 1])).2.globals = t.globals := by
    intro t htc
    apply HolFiniteMapExact.ext_lookup
    intro key
    refine InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG key (fun f => f == ofString "trap_with") ?_ _ rfl t htc
    intro f hf vs b callee rs hl
    have hfn : f = ofString "trap_with" := by simpa only [beq_iff_eq] using hf
    subst hfn
    have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ b _ rs vs callee lookup_trap_with hl
    subst hb; rfl
  rw [hbody, evaluateHOLFiniteState_dec_total]
  have hp_ev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lk
  dsimp only; rw [hp_ev]; dsimp only
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hn_lk : s.locals.lookup (ofString "n") with _ | nv
  · have hnl : pState.locals.lookup (ofString "n") = none := by
      simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
        show ofString "p" ≠ ofString "n" by decide]
    have herr : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (some .error, pState) := by
      rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl]
    rw [herr]; exact hsame _ rfl
  · rcases nv with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (HeapPotential.cMax - p).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
      by_cases hcmp1 : (HeapPotential.cMax - p).toNat < n.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1]
        have hno_none := evaluate_call_trap_with_no_none pState 1 hc
        have htg := htrap_globals pState hc
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
        rw [htr] at hno_none htg
        cases r1 with
        | none => exact absurd rfl hno_none
        | some _ => exact hsame _ htg
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1]; dsimp only; rw [evaluateHOLFiniteState_dec_total]
        let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (HeapPotential.alloc_q_word_eq p n)
        dsimp only; rw [hq_eval]; dsimp only
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_q]; dsimp only
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q"))) =
            some (.val (.word (if HeapPotential.cMax.toNat < q.toNat then 1 else 0))) := by
          simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        by_cases hcmp2 : HeapPotential.cMax.toNat < q.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2]
          have hno_none := evaluate_call_trap_with_no_none qState 1 hc
          have htg := htrap_globals qState hc
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
          rw [htr] at hno_none htg
          cases r2 with
          | none => exact absurd rfl hno_none
          | some _ => exact hsame _ htg
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2]; dsimp only
          have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lk
          have heval_end : evaluateHOLFiniteState qState
              (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p")))) =
              (some (.returned (.val (.word p))),
                emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]; dsimp only
          have hcMax_val : HeapPotential.cMax.toNat = 2952790016 := rfl
          have hhl_val : heapLimit = 2952790016 := rfl
          have hp_le_cMax : p.toNat ≤ HeapPotential.cMax.toNat := by omega
          have hsub_toNat : (HeapPotential.cMax - p).toNat = HeapPotential.cMax.toNat - p.toNat := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_le_cMax)]
          have h7 : (7 : BitVec 64).toNat = 7 := rfl
          have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
          have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
          have hq_toNat : q.toNat = (p.toNat + n.toNat + 7) / 8 * 8 := by
            have hq1 := and_neg8_toNat (p + (n + 7))
            change q.toNat = _ at hq1
            rw [hq1, hsum]
          set fin := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)
          have hfin_hp : globN fin "heap_ptr" = q.toNat := by
            simp [fin, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hfin_fm : globN fin "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have hfin_sp : globN fin "scratch_ptr" = globN s "scratch_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          change ArenaOK { fin with locals := _ } ∧ globN s "heap_ptr" ≤ globN { fin with locals := _ } "heap_ptr"
          have hfin_ok : ArenaOK fin := by
            unfold ArenaOK
            rw [hfin_hp, hfin_fm, hfin_sp]
            exact ⟨by omega, by omega, hfm_lo, hfm_hi, hsp_hi, by omega, hfm_al, hsp_al⟩
          have hfin_le : globN s "heap_ptr" ≤ globN fin "heap_ptr" := by
            rw [hp_glob, hfin_hp]; omega
          exact ⟨hfin_ok, hfin_le⟩
    · have hnl : pState.locals.lookup (ofString "n") = some (.rStruct fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl
    · have hnl : pState.locals.lookup (ofString "n") = some (.nStruct nm fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl

private theorem encoding_body_heapSafe (f : MlS) (hf : encodingGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    (f = ofString "alloc" ∧ body = sourceFnBody Guest.Software.guestFn_alloc) ∨
      heapSafeProg body = true := by
  simp only [encodingGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_begin) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_finish) rfl) hl; subst hb; rfl
  · left; exact ⟨rfl, lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_alloc hl⟩
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak256) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_memzero hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_hash_cached) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_ref_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_write_ref) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_be_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_put_be) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_write_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_trap_with hl; subst hb; rfl

private theorem arenaOK_congr_globals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals) (h : ArenaOK s) : ArenaOK t := by
  simpa only [ArenaOK, globN, hg] using h

theorem evaluate_heapSafeProg {F : Type} (program : ProgHOL 64)
    (supported : heapSafeProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (hA : ArenaOK state) :
    ArenaOK (evaluateHOLFiniteState state program).2 ∧
      globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState state program).2 "heap_ptr" := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨hA, Nat.le_refl _⟩
  | dec name kind initializer body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i val _
      split
      · obtain ⟨hAb, hle⟩ := evaluate_heapSafeProg body child (setVarHOLFinite name val state) code hA
        exact ⟨arenaOK_congr_globals rfl hAb, hle⟩
      · exact ⟨hA, Nat.le_refl _⟩
  | decCall name kind function arguments continuation =>
    have children : encodingGood function = true ∧ heapSafeProg continuation = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          have hbodyA : ArenaOK (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 ∧
              globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 "heap_ptr" := by
            rcases encoding_body_heapSafe function children.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact hbodyA)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            obtain ⟨hAc, hlec⟩ := evaluate_heapSafeProg continuation children.2 resumed
              stCode (arenaOK_congr_globals rfl hbodyA.1)
            exact ⟨arenaOK_congr_globals rfl hAc, Nat.le_trans hbodyA.2 hlec⟩
          · exact hbodyA
  | assign kind name value =>
    cases kind with
    | global => simp [shape, heapSafeProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · split <;> exact ⟨arenaOK_congr_globals rfl hA, Nat.le_refl _⟩
  | seq first second =>
    have children : heapSafeProg first = true ∧ heapSafeProg second = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    have hA1 := evaluate_heapSafeProg first children.1 state code hA
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at hA1 remaining meta'
      dsimp only at hA1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        obtain ⟨hA2, hle2⟩ := evaluate_heapSafeProg second children.2 middle (meta'.1.trans code) hA1.1
        exact ⟨hA2, Nat.le_trans hA1.2 hle2⟩
      | some _ => exact hA1
  | ite condition yes no =>
    have children : heapSafeProg yes = true ∧ heapSafeProg no = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_heapSafeProg no children.2 state code hA
      · exact evaluate_heapSafeProg yes children.1 state code hA
    · exact ⟨hA, Nat.le_refl _⟩
  | «while» condition body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hAb := evaluate_heapSafeProg body child (decClockHOLFinite state) code hA
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hAb remaining meta'
            dsimp only at hAb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
              exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
                exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
              | _ => exact hAb
      · exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨hA, Nat.le_refl _⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨hA, Nat.le_refl _⟩
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact ⟨hA, Nat.le_refl _⟩
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · split <;> exact ⟨hA, Nat.le_refl _⟩
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | shMemStore op a v =>
    have hg : (evaluateHOLFiniteState state (.shMemStore op a v)).2.globals = state.globals := by
      apply HolFiniteMapExact.ext_lookup
      intro k; exact InitECandidate.Solver.GuestGlobalKeep.shMemStore_globals state op a v k
    exact ⟨arenaOK_congr_globals hg hA, by unfold globN; rw [hg]⟩
  | extCall name a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite, ofExact, toExact]) hA,
      by simp [globN, emptyLocalsHOLFinite, ofExact, toExact]⟩
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | call info function arguments =>
    have hk : encodingGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, heapSafeProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, heapSafeProg] at supported
      · simp [shape, heapSafeProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          have hbodyA : let out := (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2
              ArenaOK out ∧ globN state "heap_ptr" ≤ globN out "heap_ptr" := by
            rcases encoding_body_heapSafe function hk.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite] using hbodyA.2⟩
  | _ => simp [shape, heapSafeProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega

/-! ### Encoding memory frame (`EncFrame`) and RLP/Keccak/node write-frame lemmas -/

structure EncFrame {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  arena : ArenaReady post
  heap_le : globN s "heap_ptr" ≤ globN post "heap_ptr"
  nonHeap : ∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k
  be : post.be = s.be
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) →
    ¬ CellHits a.toNat (globN s "heap_ptr", heapLimit - globN s "heap_ptr") →
    post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) →
    ¬ InIvl b (globN s "heap_ptr", heapLimit - globN s "heap_ptr") →
    memB post b = memB s b

theorem EncFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaReady s) (Rl : List Ivl) :
    EncFrame s s Rl :=
  ⟨hA, Nat.le_refl _, fun _ _ => rfl, rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem EncFrame.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : EncFrame s post Rl) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    EncFrame s { post with locals := L, clock := k } Rl :=
  ⟨localsFree_arenaReady post L k h.arena, h.heap_le, h.nonHeap, h.be, h.cell_frame, h.byte_frame⟩

theorem EncFrame.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : EncFrame s post R1)
    (hsub : ∀ i ∈ R1, (∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) ∨
      (globN s "heap_ptr" ≤ i.1 ∧ i.1 + i.2 ≤ heapLimit)) :
    EncFrame s post R2 := by
  refine ⟨h.arena, h.heap_le, h.nonHeap, h.be, ?_, ?_⟩
  · intro a ha hfr
    apply h.cell_frame a ?_ hfr
    intro i hi ⟨hc1, hc2⟩
    rcases hsub i hi with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩
    · exact ha j hj ⟨by omega, by omega⟩
    · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩
  · intro b hb hno hfr
    apply h.byte_frame b hb ?_ hfr
    intro i hi ⟨hb1, hb2⟩
    rcases hsub i hi with ⟨j, hj, h1, h2⟩ | ⟨hh1, hh2⟩
    · exact hno j hj ⟨by omega, by omega⟩
    · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩

theorem EncFrame.trans {F : Type} {s mid post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : EncFrame s mid Rl) (h2 : EncFrame mid post Rl) :
    EncFrame s post Rl := by
  refine ⟨h2.arena, Nat.le_trans h1.heap_le h2.heap_le,
    fun k hk => (h2.nonHeap k hk).trans (h1.nonHeap k hk),
    h2.be.trans h1.be, ?_, ?_⟩
  · intro a ha hfr
    have hfr_mid : ¬ CellHits a.toNat (globN mid "heap_ptr", heapLimit - globN mid "heap_ptr") := by
      intro ⟨hc1, hc2⟩
      dsimp only at hc1 hc2
      have hmid_hi := h1.arena.2.2.1
      exact hfr ⟨by dsimp only; have := h1.heap_le; omega, by dsimp only; omega⟩
    rw [h2.cell_frame a ha hfr_mid, h1.cell_frame a ha hfr]
  · intro b hb hno hfr
    have hfr_mid : ¬ InIvl b (globN mid "heap_ptr", heapLimit - globN mid "heap_ptr") := by
      intro ⟨hb1, hb2⟩
      dsimp only at hb1 hb2
      have hmid_hi := h1.arena.2.2.1
      exact hfr ⟨by dsimp only; have := h1.heap_le; omega, by dsimp only; omega⟩
    rw [h2.byte_frame b hb hno hfr_mid, h1.byte_frame b hb hno hfr]

private theorem pow_div_low (x y z K J : Nat) (_hy : y < 256) (_hz : z < 2 ^ K) (hJK : J + 8 ≤ K) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 = z / 2 ^ J % 256 := by
  have hpJ : 0 < 2 ^ J := Nat.two_pow_pos J
  have hdK : 2 ^ K = 2 ^ (K - J - 8) * (256 * 2 ^ J) := by
    have hk_eq : K = (K - J - 8) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have hdK8 : 2 ^ (K + 8) = 2 ^ (K - J) * (256 * 2 ^ J) := by
    have hk_eq : K + 8 = (K - J) + 8 + J := by omega
    conv_lhs => rw [hk_eq]
    rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide, Nat.mul_assoc]
  have h1 : x * 2 ^ (K + 8) + y * 2 ^ K + z =
      z + ((x * 2 ^ (K - J) + y * 2 ^ (K - J - 8)) * 256) * 2 ^ J := by
    rw [hdK, hdK8, ← Nat.mul_assoc x, ← Nat.mul_assoc y, ← Nat.add_mul, ← Nat.mul_assoc]
    omega
  rw [h1, Nat.add_mul_div_right _ _ hpJ]
  omega

private theorem pow_div_high (x y z K J : Nat) (hy : y < 256) (hz : z < 2 ^ K) (hKJ : K + 8 ≤ J) :
    (x * 2 ^ (K + 8) + y * 2 ^ K + z) / 2 ^ J % 256 =
      (x * 2 ^ (K + 8)) / 2 ^ J % 256 := by
  have hyz : y * 2 ^ K + z < 2 ^ (K + 8) := by
    have : y * 2 ^ K ≤ 255 * 2 ^ K := Nat.mul_le_mul_right _ (by omega)
    have h2 : 255 * 2 ^ K + 2 ^ K = 2 ^ (K + 8) := by
      rw [Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]; omega
    omega
  have hdJ : 2 ^ J = 2 ^ (K + 8) * 2 ^ (J - (K + 8)) := by
    have hj_eq : J = (K + 8) + (J - (K + 8)) := by omega
    conv_lhs => rw [hj_eq]
    rw [Nat.pow_add]
  have hpK8 : 0 < 2 ^ (K + 8) := Nat.two_pow_pos _
  have hsum : x * 2 ^ (K + 8) + y * 2 ^ K + z = (y * 2 ^ K + z) + x * 2 ^ (K + 8) := by omega
  rw [hsum, hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ hpK8, Nat.div_eq_of_lt hyz, Nat.zero_add,
    Nat.mul_div_cancel _ hpK8]

theorem panGetByte_panSetByte_ne (addr' addr : BitVec 64) (b : UInt8) (cell : BitVec 64) (be : Bool)
    (hal : panByteAlignHOL addr' = panByteAlignHOL addr) (hne : addr' ≠ addr) :
    panGetByteHOL addr' (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be) be =
      panGetByteHOL addr' cell be := by
  have hb8 : b.toNat < 256 := b.toNat_lt_size
  have hset_nat := panSetByteHOL_toNat (width := 64) (by decide) addr cell b be
  have h256_pow : ∀ a : BitVec 64,
      (256 : Nat) ^ (if be then 8 - 1 - a.toNat % 8 else a.toNat % 8) = 2 ^ byteBitIndex a be := by
    intro a
    rw [pow256_eq_two_pow_mul]
    cases be <;> simp [byteBitIndex]
  have hmod_ne : addr'.toNat % 8 ≠ addr.toNat % 8 := by
    intro hmeq
    apply hne
    apply BitVec.eq_of_toNat_eq
    have ha1 := panByteAlign_toNat64 addr'
    have ha2 := panByteAlign_toNat64 addr
    rw [hal] at ha1
    omega
  have hidx_sep : byteBitIndex addr' be + 8 ≤ byteBitIndex addr be ∨
      byteBitIndex addr be + 8 ≤ byteBitIndex addr' be := by
    have hm1 : addr'.toNat % 8 < 8 := by omega
    have hm2 : addr.toNat % 8 < 8 := by omega
    cases be <;> simp only [byteBitIndex, Bool.false_eq_true, if_true, if_false] <;> omega
  simp only [panGetByteHOL]
  apply congrArg UInt8.ofNat
  change (panSetByteHOL addr (BitVec.ofNat 64 b.toNat) cell be).toNat /
      256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256 =
    cell.toNat / 256 ^ (if be then 8 - 1 - addr'.toNat % 8 else addr'.toNat % 8) % 256
  rw [hset_nat, h256_pow addr']
  rcases hidx_sep with hlow | hhigh
  · rw [pow_div_low _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hlow]
    have hc_eq : 2 ^ byteBitIndex addr be =
        (2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8)) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hk_eq : byteBitIndex addr be =
          (byteBitIndex addr be - (byteBitIndex addr' be + 8)) + 8 + byteBitIndex addr' be := by omega
      conv_lhs => rw [hk_eq]
      rw [Nat.pow_add, Nat.pow_add, show (2 ^ 8 : Nat) = 256 by decide]
    have hcell_eq : cell.toNat =
        cell.toNat % 2 ^ byteBitIndex addr be +
        (((cell.toNat / 2 ^ byteBitIndex addr be) *
          2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
          2 ^ byteBitIndex addr' be := by
      have hdm := (Nat.div_add_mod cell.toNat (2 ^ byteBitIndex addr be)).symm
      rw [Nat.mul_comm (2 ^ byteBitIndex addr be)] at hdm
      have hmul : (cell.toNat / 2 ^ byteBitIndex addr be) * 2 ^ byteBitIndex addr be =
          (((cell.toNat / 2 ^ byteBitIndex addr be) *
            2 ^ (byteBitIndex addr be - (byteBitIndex addr' be + 8))) * 256) *
            2 ^ byteBitIndex addr' be := by
        rw [hc_eq, ← Nat.mul_assoc, ← Nat.mul_assoc]
      rw [hmul] at hdm
      omega
    conv_rhs => rw [hcell_eq]
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    omega
  · rw [pow_div_high _ _ _ _ _ hb8 (Nat.mod_lt _ (Nat.two_pow_pos _)) hhigh]
    have hdJ : 2 ^ byteBitIndex addr' be =
        2 ^ (byteBitIndex addr be + 8) * 2 ^ (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by
      have hj_eq : byteBitIndex addr' be =
          (byteBitIndex addr be + 8) + (byteBitIndex addr' be - (byteBitIndex addr be + 8)) := by omega
      conv_lhs => rw [hj_eq]
      rw [Nat.pow_add]
    have hpK8 : 0 < 2 ^ (byteBitIndex addr be + 8) := Nat.two_pow_pos _
    rw [hdJ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpK8]

private theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right; refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

private theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [this]; omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  unfold ordinaryDomain
  rw [h1, h2, addresses_iff_nat _ _ (by rw [hb]; decide), hb, hsb, hhe]
  omega

theorem EncFrame.of_storeByte {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hA : ArenaReady s)
    (hrun : evaluateHOLFiniteState s (.storeByte dst val) = (none, post))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      (∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat < i.1 + i.2) ∨
        (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat < heapLimit)) :
    EncFrame s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_storeByte] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | vv
      · simp
      · rcases vv with ⟨⟨v⟩⟩ | _ | _
        · dsimp only
          split
          · rename_i m' hst
            unfold panMemStoreByteWord8HOL at hst
            dsimp only at hst
            cases hm : s.memory (panByteAlignHOL addr) with
            | word cell =>
              have hcell : (s.memory (panByteAlignHOL addr)).1 = cell := by rw [hm]
              rw [hcell] at hst
              by_cases hdom : s.memaddrs (panByteAlignHOL addr)
              · simp only [hdom, ↓reduceIte, Option.some.injEq] at hst
                subst hst
                intro hrun
                injection hrun with _ hpost
                subst hpost
                have hloc_in := hin addr hdst hdom
                have hal : (panByteAlignHOL addr).toNat = addr.toNat / 8 * 8 := panByteAlign_toNat64 addr
                refine ⟨⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩, Nat.le_refl _,
                  fun _ _ => rfl, rfl, ?_, ?_⟩, rfl⟩
                · intro a hna hfr
                  dsimp only
                  have hne : a ≠ panByteAlignHOL addr := by
                    rintro rfl
                    rcases hloc_in with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩
                    · exact hna i hi ⟨by rw [hal]; omega, by rw [hal]; omega⟩
                    · exact hfr ⟨by dsimp only; rw [hal]; omega, by dsimp only; rw [hal]; omega⟩
                  rw [if_neg hne]
                · intro b hb hno hfr
                  unfold memB
                  dsimp only
                  by_cases hal_eq : panByteAlignHOL (BitVec.ofNat 64 b) = panByteAlignHOL addr
                  · rw [if_pos hal_eq]
                    have hrhs : (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 = cell := by
                      rw [hal_eq, hcell]
                    change (panGetByteHOL (BitVec.ofNat 64 b)
                        (panSetByteHOL addr (BitVec.ofNat 64 (BitVec.ofNat 8 v.toNat).toNat) cell s.be) s.be).toNat =
                      (panGetByteHOL (BitVec.ofNat 64 b) (s.memory (panByteAlignHOL (BitVec.ofNat 64 b))).1 s.be).toNat
                    rw [hrhs]
                    have hne : BitVec.ofNat 64 b ≠ addr := by
                      intro heq
                      have hbt : (BitVec.ofNat 64 b).toNat = b := Nat.mod_eq_of_lt hb
                      rw [heq] at hbt
                      subst hbt
                      rcases hloc_in with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩
                      · exact hno i hi ⟨h1, h2⟩
                      · exact hfr ⟨hh1, by dsimp only; omega⟩
                    let byte8 : UInt8 := UInt8.ofNat (BitVec.ofNat 8 v.toNat).toNat
                    have hbyte8 : byte8.toNat = (BitVec.ofNat 8 v.toNat).toNat := by simp [byte8]
                    rw [← hbyte8, panGetByte_panSetByte_ne _ _ byte8 cell s.be hal_eq hne]
                  · rw [if_neg hal_eq]
              · simp [hdom] at hst
          · simp
        · simp
        · simp
    · simp
    · simp

theorem EncFrame.of_store_word {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {Rl : List Ivl}
    (hA : ArenaReady s)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post))
    (hval_word : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      (∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) ∨
        (globN s "heap_ptr" ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapLimit)) :
    EncFrame s post Rl ∧ post.locals = s.locals := by
  rw [evaluateHOLFiniteState_store] at hrun
  revert hrun
  rcases hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · simp
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · simp
      · obtain ⟨w, rfl⟩ := hval_word v hv
        dsimp only
        split
        · rename_i m' hst
          unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
          by_cases hdom : s.memaddrs addr
          · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
            subst hst
            intro hrun
            injection hrun with _ hpost
            subst hpost
            have hloc_in := hin addr hdst hdom
            have ha8 : addr.toNat % 8 = 0 := by
              have hdom' := hA.1.memaddrs ▸ hdom
              exact (ordinaryDomain_iff addr).mp hdom' |>.1
            refine ⟨⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩, Nat.le_refl _,
              fun _ _ => rfl, rfl, ?_, ?_⟩, rfl⟩
            · intro a hna hfr
              dsimp only
              have hne : a ≠ addr := by
                rintro rfl
                rcases hloc_in with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩
                · exact hna i hi ⟨by omega, by omega⟩
                · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩
              rw [if_neg hne]
            · intro b hb hno hfr
              unfold memB
              dsimp only
              have hne : panByteAlignHOL (BitVec.ofNat 64 b) ≠ addr := by
                intro heq
                have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
                  rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
                rw [heq] at hal_b
                rcases hloc_in with ⟨i, hi, h1, h2⟩ | ⟨hh1, hh2⟩
                · exact hno i hi ⟨by omega, by omega⟩
                · exact hfr ⟨by dsimp only; omega, by dsimp only; omega⟩
              rw [if_neg hne]
          · simp [hdom] at hst
        · simp
    · simp
    · simp

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one e) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [he, valueIsWord, valueWord, memLoadHOLExact, ↓reduceIte] at hv
      split at hv
      · split at hv
        · cases hm : s.memory addr with
          | word w => exact ⟨w, by rw [← Option.some.inj hv, hm]⟩
        · simp at hv
      · simp at hv
    · simp [he, valueIsWord] at hv
    · simp [he, valueIsWord] at hv

theorem byteAlign_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma (panByteAlignHOL addr)) :
    sourceBase ≤ (panByteAlignHOL addr).toNat ∧ addr.toNat < heapEnd := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 addr
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 33806089704 := by decide
  omega

theorem word_dom_lt_heapEnd {s_ma : BitVec 64 → Prop} (hma : s_ma = ordinaryDomain)
    (addr : BitVec 64) (hdom : s_ma addr) :
    sourceBase ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapEnd ∧ addr.toNat % 8 = 0 := by
  rw [hma, ordinaryDomain_iff] at hdom
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 33806089704 := by decide
  omega

/-! ### Prefix-domain loop frame (`PrefixStoreLoop`): handles `memcpy`, `memzero`,
`rlp_put_be`, `nibble_list_to_compact`, `keccak_absorb_block`, `keccak_f1600` -/

private theorem bv_add_small (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

private theorem seq_none_enc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p q : ProgHOL 64} {Rl : List Ivl} {P : PanSemStateFiniteExact 64 F → Prop}
    (hp : ∀ m, evaluateHOLFiniteState s p = (none, m) → EncFrame s m Rl ∧ P m)
    (hq : ∀ m, evaluateHOLFiniteState s p = (none, m) → EncFrame s m Rl → P m →
      ∀ u, evaluateHOLFiniteState m q = (none, u) → EncFrame m u Rl) :
    ∀ u, evaluateHOLFiniteState s (.seq p q) = (none, u) → EncFrame s u Rl := by
  intro u hu
  rw [evaluateHOLFiniteState_seq_line780] at hu
  rcases hr : evaluateHOLFiniteState s p with ⟨r1, m⟩
  rw [hr] at hu
  cases r1 with
  | none =>
    obtain ⟨ef1, hPm⟩ := hp m hr
    exact ef1.trans (hq m hr ef1 hPm u hu)
  | some _ => simp at hu

/-- Evaluation of `rlp_be_len` body: read-only, returns `ll ≤ 8`. -/
private theorem lsr8_bound {v n : BitVec 64} (h : v.toNat < 256 ^ (8 - n.toNat)) (hnle : n.toNat ≤ 8)
    (hv : v ≠ 0) :
    n.toNat < 8 ∧ (v >>> (8 : BitVec 64).toNat).toNat < 256 ^ (8 - (n.toNat + 1)) := by
  have hn_lt : n.toNat < 8 := by
    by_contra hge
    have heq : 8 - n.toNat = 0 := by omega
    rw [heq, Nat.pow_zero] at h
    exact hv (BitVec.eq_of_toNat_eq (by simp; omega))
  refine ⟨hn_lt, ?_⟩
  have hsh : (v >>> (8 : BitVec 64).toNat).toNat = v.toNat / 256 := by
    change v.toNat >>> 8 = v.toNat / 256
    rw [Nat.shiftRight_eq_div_pow]
  rw [hsh]
  have hpow : 256 ^ (8 - n.toNat) = 256 * 256 ^ (8 - (n.toNat + 1)) := by
    have he : 8 - n.toNat = 1 + (8 - (n.toNat + 1)) := by omega
    rw [he, Nat.pow_add, Nat.pow_one]
  rw [hpow] at h
  exact Nat.div_lt_of_lt_mul h

private def rlpBeLenLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "v")) (.const 0))
    (.seq
      (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
      (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))

private theorem eval_rlp_be_len_while {F : Type} :
    ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F) (vw nw : BitVec 64),
      s.clock = k →
      s.locals.lookup (ofString "v") = some (.val (.word vw)) →
      s.locals.lookup (ofString "n") = some (.val (.word nw)) →
      nw.toNat ≤ 8 →
      vw.toNat < 256 ^ (8 - nw.toNat) →
      (evaluateHOLFiniteState s rlpBeLenLoop).1 = none →
      ∃ ll : BitVec 64,
        ll.toNat ≤ 8 ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2.locals.lookup (ofString "n") = some (.val (.word ll)) ∧
        (evaluateHOLFiniteState s rlpBeLenLoop).2 =
          { s with locals := (evaluateHOLFiniteState s rlpBeLenLoop).2.locals,
                   clock := (evaluateHOLFiniteState s rlpBeLenLoop).2.clock } := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s vw nw hclk hv hn hn_le hv_lt hnone
    unfold rlpBeLenLoop at hnone ⊢
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hcond : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) =
        some (.val (.word (if vw ≠ 0 then 1 else 0))) := by
      simp [evalHOLFinite, evalHOLExact, hv, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcond] at hnone ⊢
    dsimp only at hnone ⊢
    by_cases hvz : vw = 0
    · rw [if_neg (not_not.mpr hvz)] at hnone ⊢
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨nw, hn_le, hn, by cases s; rfl⟩
    · rw [if_pos hvz] at hnone ⊢
      have h10 : (1 : BitVec 64) ≠ 0 := by decide
      rw [if_pos h10] at hnone ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnone
      · rw [if_neg hk0] at hnone ⊢
        obtain ⟨hn_lt8, hv'_lt⟩ := lsr8_bound hv_lt hn_le hvz
        have hstep : evaluateHOLFiniteState (decClockHOLFinite s)
            (.seq
              (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
              (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1]))) =
            (none, setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
              (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))) := by
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hv_d : (decClockHOLFinite s).locals.lookup (ofString "v") = some (.val (.word vw)) := hv
          have hn_d : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word nw)) := hn
          have hne_vn : ofString "v" ≠ ofString "n" := by decide
          simp [evalHOLExact, evalListHOLExact, hv_d, hn_d, hne_vn, Ne.symm hne_vn,
            isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
            setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            evaluateHOLFiniteState_assign, wordShiftHOL, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hstep] at hnone ⊢
        dsimp only at hnone ⊢
        set mid := setVarHOLFinite (ofString "n") (.val (.word (nw + 1)))
          (setVarHOLFinite (ofString "v") (.val (.word (vw >>> (8 : BitVec 64).toNat))) (decClockHOLFinite s))
        have hmid_clk : mid.clock < k := by simp [mid, setVarHOLFinite, decClockHOLFinite, hclk]; omega
        have hmid_v : mid.locals.lookup (ofString "v") = some (.val (.word (vw >>> (8 : BitVec 64).toNat))) := by
          have hne : ofString "n" ≠ ofString "v" := by decide
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
        have hmid_n : mid.locals.lookup (ofString "n") = some (.val (.word (nw + 1))) := by
          simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hnw1 : (nw + 1).toNat = nw.toNat + 1 := by
          rw [BitVec.toNat_add]; change (nw.toNat + 1) % 2 ^ 64 = _; omega
        obtain ⟨ll, hll8, hll_lk, hst_eq⟩ :=
          ih mid.clock hmid_clk mid (vw >>> (8 : BitVec 64).toNat) (nw + 1) rfl hmid_v hmid_n
            (by omega) (by rw [hnw1]; exact hv'_lt) hnone
        unfold rlpBeLenLoop at hll_lk hst_eq
        refine ⟨ll, hll8, hll_lk, ?_⟩
        rw [hst_eq]; cases s; rfl

theorem eval_rlp_be_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).1 = some (.returned v)) :
    ∃ ll : BitVec 64,
      v = .val (.word ll) ∧ ll.toNat ≤ 8 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_be_len)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_be_len =
      .dec (ofString "n") .one (.const 0)
        (.seq rlpBeLenLoop (.return (.var .local (ofString "n")))) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsh0] at hret ⊢
  set s1 := setVarHOLFinite (ofString "n") (.val (.word 0)) s
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  rcases hl : evaluateHOLFiniteState s1 rlpBeLenLoop with ⟨rl, sl⟩
  simp only [hl] at hret ⊢
  cases rl with
  | some r =>
    exfalso
    have hnr : ∀ k (st : PanSemStateFiniteExact 64 F), st.clock = k →
        ∀ rv, (evaluateHOLFiniteState st rlpBeLenLoop).1 ≠ some (.returned rv) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro st hk rv hbad
        unfold rlpBeLenLoop at hbad
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hbad
        rcases hc : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
            (.cmp .notEqual (.var .local (ofString "v")) (.const 0)) with _ | cv
        · rw [hc] at hbad; simp at hbad
        · rw [hc] at hbad
          rcases cv with ⟨⟨cw⟩⟩ | _ | _
          · dsimp only at hbad
            by_cases hcw : cw = 0
            · subst hcw; simp at hbad
            · rw [if_pos hcw] at hbad
              by_cases hst0 : st.clock = 0
              · simp [hst0] at hbad
              · rw [if_neg hst0] at hbad
                have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite st)
                  (.seq (.assign .local (ofString "v") (.shift .lsr (.var .local (ofString "v")) (.const 8)))
                    (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1])))
                rcases hst_b : evaluateHOLFiniteState (decClockHOLFinite st) _ with ⟨rb, sb⟩
                rw [hst_b] at hbad hb_clk
                cases rb with
                | none =>
                  dsimp only at hbad hb_clk
                  exact ih sb.clock (by simp [decClockHOLFinite, hk] at hb_clk ⊢; omega) sb rfl rv hbad
                | some rb' =>
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hst_b
                  split at hst_b
                  · simp at hst_b; obtain ⟨rfl, _⟩ := hst_b; simp at hbad
                  · split at hst_b
                    · dsimp only at hst_b
                      rw [evaluateHOLFiniteState_assign] at hst_b
                      split at hst_b
                      · simp at hst_b; obtain ⟨rfl, _⟩ := hst_b; simp at hbad
                      · split at hst_b <;> simp at hst_b <;> obtain ⟨rfl, _⟩ := hst_b <;> simp at hbad
                    · simp at hst_b; obtain ⟨rfl, _⟩ := hst_b; simp at hbad
          · simp at hbad
          · simp at hbad
    dsimp only at hret
    exact hnr s1.clock s1 rfl v (by rw [hl]; exact hret)
  | none =>
    dsimp only at hret ⊢
    rcases hv_lk : s.locals.lookup (ofString "v") with _ | vv
    · exfalso
      have hs1_v : s1.locals.lookup (ofString "v") = none := by
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk, show ofString "n" ≠ ofString "v" by decide]
      unfold rlpBeLenLoop at hl
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hl
      simp [evalHOLFinite, evalHOLExact, hs1_v] at hl
    · rcases vv with ⟨⟨vw⟩⟩ | _ | _
      · have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk, show ofString "n" ≠ ofString "v" by decide]
        have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word 0)) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hv_lt : vw.toNat < 256 ^ (8 - (0 : BitVec 64).toNat) := by
          have : (256 ^ (8 - (0 : BitVec 64).toNat) : Nat) = 2 ^ 64 := by decide
          rw [this]; exact vw.isLt
        obtain ⟨ll, hll8, hsl_n, hsl_eq⟩ := eval_rlp_be_len_while s1.clock s1 vw 0 rfl hs1_v hs1_n (by decide) hv_lt (by rw [hl])
        rw [hl] at hsl_n hsl_eq
        dsimp only at hsl_n hsl_eq
        rw [evaluateHOLFiniteState_return] at hret ⊢
        have hev_n : @evalHOLExact 64 F _ sl.toExact
            (fun a => Classical.propDecidable (sl.memaddrs a)) (.var .local (ofString "n")) =
            some (.val (.word ll)) := by simp [evalHOLExact, hsl_n]
        have hsz : sizeOfShapeWithContextHOL sl.structs (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev_n] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsz] at hret ⊢
        injection hret with hr; injection hr with hr'
        subst hr'
        refine ⟨ll, rfl, hll8, ?_⟩
        dsimp only [emptyLocalsHOLFinite]
        rw [hsl_eq]; cases s; rfl
      · rename_i fs
        exfalso
        have hs1_v : s1.locals.lookup (ofString "v") = some (.rStruct fs) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk, show ofString "n" ≠ ofString "v" by decide]
        unfold rlpBeLenLoop at hl
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hl
        simp [evalHOLFinite, evalHOLExact, hs1_v] at hl
      · rename_i nm fs
        exfalso
        have hs1_v : s1.locals.lookup (ofString "v") = some (.nStruct nm fs) := by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk, show ofString "n" ≠ ofString "v" by decide]
        unfold rlpBeLenLoop at hl
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hl
        simp [evalHOLFinite, evalHOLExact, hs1_v] at hl

/-! ### `rlp_header_len`, `rlp_list_header_len`, `rlp_bytes_encoded_len`, `rlp_value_encoded_len`, `node_ref_len` -/

private theorem lookup_rlp_be_len :
    originalRuntimeCode.lookup (ofString "rlp_be_len") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_rlp_be_len, .one) :=
  lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_be_len) rfl

private theorem lookup_rlp_header_len :
    originalRuntimeCode.lookup (ofString "rlp_header_len") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_rlp_header_len, .one) :=
  lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_header_len) rfl

private theorem lookup_rlp_list_header_len :
    originalRuntimeCode.lookup (ofString "rlp_list_header_len") =
      some ([(ofString "payload_len", .one)], sourceFnBody Guest.Software.guestFn_rlp_list_header_len, .one) :=
  lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl

private theorem lookup_rlp_bytes_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len") =
      some ([(ofString "first_byte", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len, .one) :=
  lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl

private theorem lookup_rlp_value_encoded_len :
    originalRuntimeCode.lookup (ofString "rlp_value_encoded_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len, .one) :=
  lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl

private theorem lookup_node_ref_len :
    originalRuntimeCode.lookup (ofString "node_ref_len") =
      some ([(ofString "child", .one)], sourceFnBody Guest.Software.guestFn_node_ref_len, .one) :=
  lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_ref_len) rfl

private theorem lookup_mpt_fail :
    originalRuntimeCode.lookup (ofString "mpt_fail") =
      some ([(ofString "code", .one)], sourceFnBody Guest.Software.guestFn_mpt_fail, .one) :=
  lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

theorem eval_call_mpt_fail_no_none_no_ret {F : Type}
    (s : PanSemStateFiniteExact 64 F) (c : BitVec 64) (hc : s.code = originalRuntimeCode) :
    let out := evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [.const c])
    out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) := by
  dsimp only
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlk := pan_one_word_lookup s.code.lookup (ofString "mpt_fail") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_mpt_fail) c (by rw [hc]; exact lookup_mpt_fail)
  rw [hargs]; dsimp only; rw [hlk]; dsimp only
  split
  · exact ⟨by simp, fun _ => by simp⟩
  · have hb : sourceFnBody Guest.Software.guestFn_mpt_fail =
        .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
    have hraise_out : ∀ st : PanSemStateFiniteExact 64 F,
        let ro := (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")))).1
        ro = some .error ∨ ∃ ev, ro = some (.exception (ofString "MptErr") ev) := by
      intro st; dsimp only; rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only; split <;> simp
      · simp
    let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "code", .val (.word c)))
    rcases hbody : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨res, st⟩
    have hr := hraise_out entry
    rw [hb, evaluateHOLFiniteState_seq_line780] at hbody
    rcases hr_st : evaluateHOLFiniteState entry (.raise (ofString "MptErr") (.var .local (ofString "code"))) with ⟨rr, sr⟩
    rw [hr_st] at hr hbody
    dsimp only at hr hbody
    rcases hr with rfl | ⟨ev, rfl⟩
    · injection hbody with h1 _; subst h1; exact ⟨by simp, fun _ => by simp⟩
    · injection hbody with h1 _; subst h1; exact ⟨by simp, fun _ => by simp⟩

theorem eval_rlp_header_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).1 =
      some (.returned v)) :
    ∃ hl : BitVec 64,
      v = .val (.word hl) ∧ 1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_header_len)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_header_len =
      .seq
        (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
          (.return (.const 1))
          .skip)
        (.decCall (ofString "ll") .one (ofString "rlp_be_len") [.var .local (ofString "n")]
          (.return (.op .add [.const 1, .var .local (ofString "ll")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret ⊢
  rcases hn : s.locals.lookup (ofString "n") with _ | nv
  · simp [evalHOLExact, hn] at hret
  · rcases nv with ⟨⟨nw⟩⟩ | _ | _
    · have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notLower (.const 55) (.var .local (ofString "n"))) =
          some (.val (.word (if nw.toNat ≤ 55 then 1 else 0))) := by
        simp only [evalHOLExact, hn, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
          Bool.not_eq_true', decide_eq_false_iff_not]
        change some (ValueHOL.val (HolWordLab.word (if ¬(55 : Nat) < nw.toNat then 1 else 0))) = _
        by_cases hle : nw.toNat ≤ 55
        · have : ¬ (55 < nw.toNat) := by omega
          simp [hle, this]
        · have : 55 < nw.toNat := by omega
          simp [hle, this]
      rw [hcond] at hret ⊢; dsimp only at hret ⊢
      by_cases hle55 : nw.toNat ≤ 55
      · rw [if_pos hle55] at hret ⊢
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        rw [if_neg h10] at hret ⊢
        rw [evaluateHOLFiniteState_return] at hret ⊢
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret ⊢
        subst hret
        exact ⟨1, rfl, by decide, by decide, by cases s; rfl⟩
      · rw [if_neg hle55] at hret ⊢
        simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret ⊢
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret ⊢
        have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "n")] = some [.val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
        have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_be_len") (ofString "v")
          (sourceFnBody Guest.Software.guestFn_rlp_be_len) nw (by rw [hc]; exact lookup_rlp_be_len)
        simp only [hargs, hlk] at hret ⊢
        by_cases hclk0 : s.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret ⊢
          let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word nw)))
          rcases hbe : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_be_len) with ⟨rbe, sbe⟩
          have hbe' : evaluateHOLFiniteState
              (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word nw))))
              (sourceFnBody Guest.Software.guestFn_rlp_be_len) = (rbe, sbe) := hbe
          simp only [hbe'] at hret ⊢
          cases rbe with
          | none => simp at hret
          | some rb' =>
            cases rb' with
            | returned vbe =>
              obtain ⟨ll, rfl, hll8, hsbe_eq⟩ := eval_rlp_be_len_returned entry vbe (by rw [hbe])
              rw [hbe] at hsbe_eq; dsimp only at hsbe_eq
              have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word ll) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret ⊢
              have h1ll_nat : ((1 : BitVec 64) + ll).toNat = 1 + ll.toNat := by
                rw [BitVec.toNat_add]; change (1 + ll.toNat) % 2 ^ 64 = _; omega
              let resSt := setVarHOLFinite (ofString "ll") (.val (.word ll)) { sbe with locals := s.locals }
              rw [evaluateHOLFiniteState_return] at hret ⊢
              have hev_add : @evalHOLExact 64 F _ resSt.toExact
                  (fun a => Classical.propDecidable (resSt.memaddrs a))
                  (.op .add [.const 1, .var .local (ofString "ll")]) =
                  some (.val (.word ((1 : BitVec 64) + ll))) := by
                simp [resSt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
              have hsz : sizeOfShapeWithContextHOL resSt.structs
                  (shapeOfHOLExact (.val (.word ((1 : BitVec 64) + ll)) : ValueHOL 64)) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [hev_add] at hret ⊢; dsimp only at hret ⊢; rw [if_pos hsz] at hret ⊢
              injection hret with hr; injection hr with hr'
              subst hr'
              refine ⟨(1 : BitVec 64) + ll, rfl, by omega, by omega, ?_⟩
              dsimp only [resSt, emptyLocalsHOLFinite, setVarHOLFinite]
              rw [hsbe_eq]; cases s; rfl
            | _ => simp at hret
    · simp [evalHOLExact, hn, valueIsWord] at hret
    · simp [evalHOLExact, hn, valueIsWord] at hret

theorem eval_rlp_list_header_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).1 =
      some (.returned v)) :
    ∃ hl : BitVec 64,
      v = .val (.word hl) ∧ 1 ≤ hl.toNat ∧ hl.toNat ≤ 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_list_header_len)).2.clock } := by
  have hb : sourceFnBody Guest.Software.guestFn_rlp_list_header_len =
      .call none (ofString "rlp_header_len") [.var .local (ofString "payload_len")] := rfl
  rw [hb, evaluateHOLFiniteState_call] at hret ⊢
  rcases hpl : s.locals.lookup (ofString "payload_len") with _ | pv
  · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpl] at hret
  · rcases pv with ⟨⟨pw⟩⟩ | fs | ⟨nm, fs⟩
    · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "payload_len")] = some [.val (.word pw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpl]
      have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_rlp_header_len) pw (by rw [hc]; exact lookup_rlp_header_len)
      simp only [hargs, hlk] at hret ⊢
      by_cases hclk0 : s.clock = 0
      · simp [hclk0] at hret
      · simp only [hclk0, ↓reduceIte] at hret ⊢
        let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word pw)))
        rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
        have hcal' : evaluateHOLFiniteState
            (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word pw))))
            (sourceFnBody Guest.Software.guestFn_rlp_header_len) = (rc, sc) := hcal
        simp only [hcal'] at hret ⊢
        cases rc with
        | none => simp at hret
        | some rc' =>
          cases rc' with
          | returned vc =>
            obtain ⟨hl, rfl, h1, h9, hsc_eq⟩ := eval_rlp_header_len_returned entry hc vc (by rw [hcal])
            rw [hcal] at hsc_eq; dsimp only at hsc_eq
            have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word hl) : ValueHOL 64)) .one = true := by
              simp [shapeOfHOLExact, shapeEqHOL]
            simp only [hsh, ↓reduceIte] at hret ⊢
            injection hret with hr; injection hr with hr'; subst hr'
            refine ⟨hl, rfl, h1, h9, ?_⟩
            dsimp only [emptyLocalsHOLFinite]
            rw [hsc_eq]; cases s; rfl
          | _ => simp at hret
    · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "payload_len")] = some [ValueHOL.rStruct fs] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpl]
      have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "rlp_header_len") [ValueHOL.rStruct fs] = none := by
        rw [hc]
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite
        have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_header_len") [ValueHOL.rStruct fs] = none := by
          simp [lookupCodeHOLExact, lookup_rlp_header_len, shapeOfHOLExact, shapeEqHOL]
        split
        · rfl
        · rename_i _ _ _ h; rw [hraw] at h; cases h
      rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret
    · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "payload_len")] = some [ValueHOL.nStruct nm fs] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hpl]
      have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "rlp_header_len") [ValueHOL.nStruct nm fs] = none := by
        rw [hc]
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite
        have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_header_len") [ValueHOL.nStruct nm fs] = none := by
          simp [lookupCodeHOLExact, lookup_rlp_header_len, shapeOfHOLExact, shapeEqHOL]
        split
        · rfl
        · rename_i _ _ _ h; rw [hraw] at h; cases h
      rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret

private def roEncGood (f : MlS) : Bool :=
  ((["rlp_be_len", "rlp_header_len", "rlp_list_header_len", "rlp_bytes_encoded_len",
    "rlp_value_encoded_len", "node_ref_len", "mpt_fail"] : List String).map ofString).contains f

private def roEncProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => roEncProg body
  | .seq first second => roEncProg first && roEncProg second
  | .ite _ yes no => roEncProg yes && roEncProg no
  | .while _ body => roEncProg body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .decCall _ _ function _ continuation => roEncGood function && roEncProg continuation
  | .call none function _ => roEncGood function
  | .call (some (none, none)) function _ => roEncGood function
  | .call (some (some (.local, _), none)) function _ => roEncGood function
  | _ => false

private theorem roEnc_installed_body (f : MlS)
    (hf : roEncGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    roEncProg body = true := by
  simp only [roEncGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_be_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_list_header_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_bytes_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_rlp_value_encoded_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_node_ref_len hl; subst hb; rfl
  · have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_mpt_fail hl; subst hb; rfl

theorem evaluate_roEncProg {F : Type} (program : ProgHOL 64)
    (supported : roEncProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2 =
      { state with locals := (evaluateHOLFiniteState state program).2.locals,
                   clock := (evaluateHOLFiniteState state program).2.clock } := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · rfl
    · rename_i val _
      split
      · have ih := evaluate_roEncProg body child (setVarHOLFinite name val state) code
        dsimp only [setVarHOLFinite] at ih ⊢
        conv_lhs => rw [ih]
        cases state; rfl
      · rfl
  | decCall name kind function arguments continuation =>
    have children : roEncGood function = true ∧ roEncProg continuation = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          dsimp only
          have hsafe := roEnc_installed_body function children.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbody meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try (rw [hbody]; cases state; rfl))
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            have ih := evaluate_roEncProg continuation children.2 resumed stCode
            dsimp only [resumed, setVarHOLFinite] at ih ⊢
            conv_lhs => rw [ih]
            rw [hbody]; cases state; rfl
          · rw [hbody]; cases state; rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape, roEncProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> (cases state; rfl)
  | seq first second =>
    have children : roEncProg first = true ∧ roEncProg second = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    have h1 := evaluate_roEncProg first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at h1 remaining meta'
      dsimp only at h1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        have h2 := evaluate_roEncProg second children.2 middle (meta'.1.trans code)
        dsimp only
        rw [h2, h1]
      | some _ => exact h1
  | ite condition yes no =>
    have children : roEncProg yes = true ∧ roEncProg no = true := by
      simpa only [shape, roEncProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roEncProg no children.2 state code
      · exact evaluate_roEncProg yes children.1 state code
    · rfl
  | «while» condition body =>
    have child : roEncProg body = true := by simpa only [shape, roEncProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hb := evaluate_roEncProg body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hb remaining meta'
            dsimp only at hb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
              rw [hw, hb]; cases state; rfl
            | some r =>
              cases r with
              | «continue» =>
                have hw := evaluate_roEncProg (.while condition body) (by simpa [roEncProg] using child) middle mCode
                rw [hw, hb]; cases state; rfl
              | _ => rw [hb]; cases state; rfl
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (cases state; rfl)
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> (cases state; rfl)
  | call info function arguments =>
    have hk : roEncGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, roEncProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, roEncProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, roEncProg] at supported
      · simp [shape, roEncProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · rfl
    · rename_i values _
      split
      · rfl
      · rename_i body callee rs found
        rw [code] at found
        split
        · rfl
        · rename_i nonzero
          have hsafe := roEnc_installed_body function hk.1 values body callee rs found
          have hbody := evaluate_roEncProg body hsafe (callEntryStateHOLFinite state callee) code
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbody
          obtain ⟨r, st⟩ := out
          dsimp only at hbody ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (rw [hbody]; cases state; rfl)
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              (dsimp only [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]; rw [hbody]; cases state; rfl)
  | _ => simp [shape, roEncProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega

theorem eval_rlp_bytes_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (nw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).1 =
      some (.returned v)) :
    ∃ el : BitVec 64,
      v = .val (.word el) ∧ 1 ≤ el.toNat ∧ el.toNat ≤ nw.toNat + 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len =
      .seq
        (.ite (.op .and [
            .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
            .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))])
          (.return (.const 1#64))
          .skip)
        (.decCall (ofString "h") .one (ofString "rlp_header_len") [.var .local (ofString "n")]
          (.return (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .and [
        .cmp .notEqual (.const 0#64) (.cmp .equal (.var .local (ofString "n")) (.const 1#64)),
        .cmp .notEqual (.const 0#64) (.cmp .lower (.var .local (ofString "first_byte")) (.const 128#64))]) with _ | cv
  · simp [hcond] at hret
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcond] at hret
      by_cases hcw0 : cw = 0#64
      · rw [if_pos hcw0, evaluateHOLFiniteState_skip] at hret
        rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
        have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
            [.var .local (ofString "n")] = some [.val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
        have hlk := pan_one_word_lookup s.code.lookup (ofString "rlp_header_len") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_header_len) nw (by rw [hc]; exact lookup_rlp_header_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : s.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw)))
          rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_header_len) with ⟨rc, sc⟩
          have hcal' : evaluateHOLFiniteState
              (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nw))))
              (sourceFnBody Guest.Software.guestFn_rlp_header_len) = (rc, sc) := hcal
          simp only [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              obtain ⟨hlw, rfl, h1, h9, _⟩ := eval_rlp_header_len_returned entry hc vc (by rw [hcal])
              have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one &&
                  shapeEqHOL (shapeOfHOLExact (.val (.word hlw) : ValueHOL 64)) .one) = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              let resSt := setVarHOLFinite (ofString "h") (.val (.word hlw)) { sc with locals := s.locals }
              rw [evaluateHOLFiniteState_return] at hret
              have hev_add : @evalHOLExact 64 F _ resSt.toExact (fun a => Classical.propDecidable (resSt.memaddrs a))
                  (.op .add [.var .local (ofString "h"), .var .local (ofString "n")]) =
                  some (.val (.word (hlw + nw))) := by
                have hne : ofString "h" ≠ ofString "n" := by decide
                simp [resSt, evalHOLExact, evalListHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  hne, Ne.symm hne, hn, wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_zero]
              have hsz : sizeOfShapeWithContextHOL resSt.structs
                  (shapeOfHOLExact (.val (.word (hlw + nw)) : ValueHOL 64)) ≤ 32 := by simp [shapeOfHOLExact]
              rw [hev_add] at hret; dsimp only at hret; rw [if_pos hsz] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              have hsum : (hlw + nw).toNat = hlw.toNat + nw.toNat := by
                rw [BitVec.toNat_add]; omega
              exact ⟨hlw + nw, rfl, by omega, by omega, hro⟩
            | _ => simp at hret
      · rw [if_neg hcw0] at hret
        rw [evaluateHOLFiniteState_return] at hret
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
        subst hret
        exact ⟨1, rfl, by decide, by omega, hro⟩
    · simp [hcond] at hret
    · simp [hcond] at hret

theorem eval_rlp_value_encoded_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (pw nw : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hnw60 : nw.toNat < 2 ^ 60)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).1 =
      some (.returned v)) :
    ∃ vl : BitVec 64,
      v = .val (.word vl) ∧ 1 ≤ vl.toNat ∧ vl.toNat ≤ nw.toNat + 9 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_rlp_value_encoded_len =
      .dec (ofString "fb") .one (.const 0)
        (.seq
          (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
            (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
            .skip)
          (.call none (ofString "rlp_bytes_encoded_len")
            [.var .local (ofString "fb"), .var .local (ofString "n")])) := rfl
  rw [hb, evaluateHOLFiniteState_dec_total] at hret
  dsimp only at hret
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [hev0] at hret; dsimp only at hret; rw [if_pos hsh0] at hret
  let s1 := setVarHOLFinite (ofString "fb") (.val (.word 0)) s
  rw [evaluateHOLFiniteState_seq_line780] at hret
  rcases hite : evaluateHOLFiniteState s1
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p"))))
        .skip) with ⟨ri, si⟩
  have hsi_code : si.code = originalRuntimeCode :=
    (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata s1 _).1.trans hc |>.symm ▸
      by have hm := (InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata s1
            (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
              (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)).1
         rw [hite] at hm; exact hm.trans hc
  have hsi_n : ri = none → si.locals.lookup (ofString "n") = some (.val (.word nw)) := by
    intro hri
    have hn_keep := evaluate_avoidsLocal_flowing (ofString "n")
      (.ite (.cmp .lower (.const 0) (.var .local (ofString "n")))
        (.assign .local (ofString "fb") (.loadByte (.var .local (ofString "p")))) .skip)
      (by decide) s1 (Or.inl (by rw [hite]; exact hri))
    rw [hite] at hn_keep
    have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word nw)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "fb" ≠ ofString "n" by decide]
    exact hn_keep.trans hs1_n
  simp only [hite] at hret
  cases ri with
  | some ri' =>
    -- ite of assign/skip can only produce none or error
    rw [evaluateHOLFiniteState_ite] at hite
    split at hite
    · split at hite
      · rw [evaluateHOLFiniteState_skip] at hite; cases hite
      · rw [evaluateHOLFiniteState_assign] at hite
        split at hite
        · injection hite with hr _; cases hr; simp at hret
        · split at hite <;> injection hite with hr _ <;> cases hr <;> simp at hret
    · injection hite with hr _; cases hr; simp at hret
  | none =>
    dsimp only at hret
    have hsin := hsi_n rfl
    rw [evaluateHOLFiniteState_call] at hret
    rcases hfb : si.locals.lookup (ofString "fb") with _ | fbv
    · simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb] at hret
    · rcases fbv with ⟨⟨fbw⟩⟩ | fs | ⟨nm, fs⟩
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [.val (.word fbw), .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hlk := pan_two_word_lookup si.code.lookup (ofString "rlp_bytes_encoded_len")
          (ofString "first_byte") (ofString "n")
          (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) fbw nw
          (by decide) (by rw [hsi_code]; exact lookup_rlp_bytes_encoded_len)
        simp only [hargs, hlk] at hret
        by_cases hclk0 : si.clock = 0
        · simp [hclk0] at hret
        · simp only [hclk0, ↓reduceIte] at hret
          let cmap := (HolFiniteMapExact.empty.update (ofString "first_byte", ValueHOL.val (.word fbw))).update
            (ofString "n", ValueHOL.val (.word nw))
          let entry := callEntryStateHOLFinite si cmap
          have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word nw)) := by
            simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rcases hcal : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) with ⟨rc, sc⟩
          have hcal' : evaluateHOLFiniteState (callEntryStateHOLFinite si cmap)
              (sourceFnBody Guest.Software.guestFn_rlp_bytes_encoded_len) = (rc, sc) := hcal
          simp only [hcal'] at hret
          cases rc with
          | none => simp at hret
          | some rc' =>
            cases rc' with
            | returned vc =>
              obtain ⟨el, rfl, h1, hub, _⟩ := eval_rlp_bytes_encoded_len_returned entry hsi_code nw hent_n hnw60 vc (by rw [hcal])
              have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word el) : ValueHOL 64)) .one = true := by
                simp [shapeOfHOLExact, shapeEqHOL]
              simp only [hsh, ↓reduceIte] at hret
              injection hret with hr; injection hr with hr'; subst hr'
              exact ⟨el, rfl, h1, hub, hro⟩
            | _ => simp at hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.rStruct fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.rStruct fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.rStruct fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split; · rfl; · rename_i _ _ _ h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret
      · have hargs : evalListHOLFinite si (h := fun a => Classical.propDecidable (si.memaddrs a))
            [.var .local (ofString "fb"), .var .local (ofString "n")] =
            some [ValueHOL.nStruct nm fs, .val (.word nw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hfb, hsin]
        have hnone : PanSemStateFiniteExact.lookupCodeHOLFinite si.code.lookup (ofString "rlp_bytes_encoded_len")
            [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
          rw [hsi_code]; unfold PanSemStateFiniteExact.lookupCodeHOLFinite
          have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "rlp_bytes_encoded_len")
              [ValueHOL.nStruct nm fs, .val (.word nw)] = none := by
            simp [lookupCodeHOLExact, lookup_rlp_bytes_encoded_len, shapeOfHOLExact, shapeEqHOL]
          split; · rfl; · rename_i _ _ _ h; rw [hraw] at h; cases h
        rw [hargs] at hret; dsimp only at hret; rw [hnone] at hret; simp at hret

theorem eval_node_ref_len_returned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).1 =
      some (.returned v)) :
    ∃ rl : BitVec 64,
      v = .val (.word rl) ∧ rl.toNat ≤ 33 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2 =
        { s with locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.locals,
                 clock := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_node_ref_len)).2.clock } := by
  have hro := evaluate_roEncProg (sourceFnBody Guest.Software.guestFn_node_ref_len) rfl s hc
  have hb : sourceFnBody Guest.Software.guestFn_node_ref_len =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip)
        (.seq
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
            (.return (.const 33)) .skip)
          (.seq
            (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
              (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip)
            (.dec (ofString "rl") .one (.load .one (.op .add [.var .local (ofString "child"), .const 16]))
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "rl")) (.const 32))
                  (.return (.var .local (ofString "rl"))) .skip)
                (.return (.const 33)))))) := rfl
  rw [hb, evaluateHOLFiniteState_seq_line780] at hret
  rcases h1 : evaluateHOLFiniteState s
      (.ite (.cmp .equal (.var .local (ofString "child")) (.const 0)) (.return (.const 1)) .skip) with ⟨r1, s1⟩
  simp only [h1] at hret
  cases r1 with
  | some r1' =>
    rw [evaluateHOLFiniteState_ite] at h1
    split at h1
    · split at h1
      · rw [evaluateHOLFiniteState_skip] at h1; cases h1
      · rw [evaluateHOLFiniteState_return] at h1
        simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h1
        obtain ⟨rfl, _⟩ := h1; simp at hret; subst hret
        exact ⟨1, rfl, by decide, hro⟩
    · injection h1 with hr _; cases hr; simp at hret
  | none =>
    have hs1 : s1 = s := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; exact (Prod.mk.inj h1).2.symm
        · exfalso; exact return_ne_none s _ (congrArg Prod.fst h1)
      · cases h1
    subst hs1
    dsimp only at hret
    rw [evaluateHOLFiniteState_seq_line780] at hret
    rcases h2 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 0])) (.const 0))
          (.return (.const 33)) .skip) with ⟨r2, s2⟩
    simp only [h2] at hret
    cases r2 with
    | some r2' =>
      rw [evaluateHOLFiniteState_ite] at h2
      split at h2
      · split at h2
        · rw [evaluateHOLFiniteState_skip] at h2; cases h2
        · rw [evaluateHOLFiniteState_return] at h2
          simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at h2
          obtain ⟨rfl, _⟩ := h2; simp at hret; subst hret
          exact ⟨33, rfl, by decide, hro⟩
      · injection h2 with hr _; cases hr; simp at hret
    | none =>
      have hs2 : s2 = s := by
        rw [evaluateHOLFiniteState_ite] at h2
        split at h2
        · split at h2
          · rw [evaluateHOLFiniteState_skip] at h2; exact (Prod.mk.inj h2).2.symm
          · exfalso; exact return_ne_none s _ (congrArg Prod.fst h2)
        · cases h2
      subst hs2
      dsimp only at hret
      rw [evaluateHOLFiniteState_seq_line780] at hret
      rcases h3 : evaluateHOLFiniteState s
          (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "child"), .const 8])) (.const 0))
            (.call (some (none, none)) (ofString "mpt_fail") [.const 13]) .skip) with ⟨r3, s3⟩
      simp only [h3] at hret
      have hmf := eval_call_mpt_fail_no_none_no_ret s 13 hc
      cases r3 with
      | some r3' =>
        dsimp only at hret
        subst hret
        rw [evaluateHOLFiniteState_ite] at h3
        split at h3
        · split at h3
          · rw [evaluateHOLFiniteState_skip] at h3; cases h3
          · exact False.elim (hmf.2 v (congrArg Prod.fst h3))
        · cases h3
      | none =>
        have hs3 : s3 = s := by
          rw [evaluateHOLFiniteState_ite] at h3
          split at h3
          · split at h3
            · rw [evaluateHOLFiniteState_skip] at h3; exact (Prod.mk.inj h3).2.symm
            · exact False.elim (hmf.1 (congrArg Prod.fst h3))
          · cases h3
        subst hs3
        dsimp only at hret
        rw [evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
        rcases hld : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .local (ofString "child"), .const 16])) with _ | rlv
        · simp [hld] at hret
        · obtain ⟨rlw, rfl⟩ := eval_load_one_word s _ rlv hld
          have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word rlw) : ValueHOL 64)) = true := by
            simp [shapeOfHOLExact, shapeEqHOL]
          rw [hld] at hret; dsimp only at hret; rw [if_pos hsh] at hret
          let s4 := setVarHOLFinite (ofString "rl") (.val (.word rlw)) s
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
          have hcmp : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
              (.cmp .lower (.var .local (ofString "rl")) (.const 32)) =
              some (.val (.word (if rlw.toNat < 32 then 1 else 0))) := by
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
          rw [hcmp] at hret; dsimp only at hret
          by_cases hlt32 : rlw.toNat < 32
          · rw [if_pos hlt32] at hret
            have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            rw [if_neg h10, evaluateHOLFiniteState_return] at hret
            simp [s4, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨rlw, rfl, by omega, hro⟩
          · rw [if_neg hlt32] at hret
            simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hret
            rw [evaluateHOLFiniteState_return] at hret
            simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL] at hret
            subst hret
            exact ⟨33, rfl, by decide, hro⟩

end NodeRlpProof
end InitECandidate.Solver.Wave8GuestInv
