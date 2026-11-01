import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace InsertKind0

/-- A statement without a continuing control transfer, with a normal-exit assertion. -/
def Step (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (p : ProgHOL 64)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  Hoare P p (fun r t => r ≠ some .continue ∧ (r = none → Q t))

namespace Step
variable {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}

theorem mono {p : ProgHOL 64} (h : Step R p Q)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → R s) : Step P p Q :=
  Hoare.mono h hp

theorem seq {a b : ProgHOL 64} (ha : Step P a R) (hb : Step R b Q) :
    Step P (.seq a b) Q := by
  apply Hoare.seq (R := R) _ hb
  refine ⟨fun s hc hp hnt => ?_⟩
  have h := ha.run s hc hp hnt
  exact ⟨h.2, fun hn => ⟨h.1, fun hz => (hn hz).elim⟩⟩

theorem dead {p : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → False) : Step P p Q :=
  Hoare.of_false h

theorem ite {c : ExpHOL 64} {a b : ProgHOL 64}
    (ha : Step (fun s => P s ∧ CondTrue c s) a Q)
    (hb : Step (fun s => P s ∧ CondFalse c s) b Q) : Step P (.ite c a b) Q := by
  exact Hoare.ite ha hb (fun _ _ => by simp)

theorem assign {n : MlS} {e : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s e = some v → Q (setVarHOLFinite n v s)) :
    Step P (.assign .local n e) Q := by
  exact Hoare.assign (fun s v hp hv => ⟨by simp, fun _ => h s v hp hv⟩)
    (fun _ _ => by simp)

theorem store {a v : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (m : BitVec 64 → HolWordLab 64),
      P s → Q { s with memory := m }) : Step P (.store a v) Q := by
  refine ⟨fun s _ hp _ => ?_⟩
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split
      · exact ⟨by simp, fun _ => h s _ hp⟩
      · simp
    · simp
  · simp

theorem dec {n : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64}
    {names : List String}
    (hn : ∀ x ∈ names, ofString x ≠ n)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s e = some v → R (setVarHOLFinite n v s))
    (hp : Step R p Q) (hq : LocalsOnly names Q) : Step P (.dec n sh e p) Q := by
  apply Hoare.dec hn hi hp
  · intro F r s locals hl h
    exact ⟨h.1, fun hz => hq s locals s.clock hl (h.2 hz)⟩
  · intro F s _
    simp

theorem callLocal {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname n : MlS} {args : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (he : CallEntryOn P Pc fname args)
    (hr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q (setVarHOLFinite n v { post with locals := s.locals })) :
    Step P (.call (some (some (.local, n), none)) fname args) Q := by
  refine ⟨fun s hc hp hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        rcases hout : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        simp only [hout] at hnt ⊢
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned v =>
            have hs := FunSpec.at_lookup hf s hc values body callee ret hl
              (he s values body callee ret hc hp hargs hl) (by rw [hout]; simp)
            rw [hout] at hs
            dsimp only at hs ⊢
            split
            · split
              · exact ⟨by simp, fun _ => hr s callee post v hp hs⟩
              · simp
            · simp
          | timeOut => simp at hnt
          | _ => simp
end Step

/-- At kind zero a normal iteration exits with `go = 0`. -/
def Done : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "go" = 0

theorem done_locals : LocalsOnly ["go"] Done := by
  intro F s locals k hl h
  exact ⟨localsFree_arenaReady s locals k h.1,
    (locN_congr s locals k "go" (hl "go" (by simp))).trans h.2⟩

theorem done_set {F : Type} {s : PanSemStateFiniteExact 64 F} (h : Done s)
    {n : MlS} (hn : ofString "go" ≠ n) (v : ValueHOL 64) :
    Done (setVarHOLFinite n v s) :=
  done_locals.setVar (by simpa using hn) v s h

theorem done_memory {F : Type} {s : PanSemStateFiniteExact 64 F} (h : Done s)
    (m : BitVec 64 → HolWordLab 64) : Done { s with memory := m } :=
  ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl h.1.1, h.1.2⟩, h.2⟩

private def finish : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "slot")) (.const 0))
    (.assign .local (ofString "result") (.var .local (ofString "r")))
    (.store (.var .local (ofString "slot")) (.var .local (ofString "r"))))
    (.seq (.assign .local (ofString "node") (.var .local (ofString "next_node")))
      (.seq (.assign .local (ofString "slot") (.var .local (ofString "next_slot")))
        (.assign .local (ofString "level") (.var .local (ofString "next_level")))))

theorem finish_done : Step Done finish Done := by
  apply Step.seq (R := Done)
  · apply Step.ite
    · exact Step.assign (fun _ v hp _ => done_set hp.1 (by decide) v)
    · exact Step.store (fun _ m hp => done_memory hp.1 m)
  · apply Step.seq (R := Done)
    · exact Step.assign (fun _ v hp _ => done_set hp (by decide) v)
    · apply Step.seq (R := Done)
      · exact Step.assign (fun _ v hp _ => done_set hp (by decide) v)
      · exact Step.assign (fun _ v hp _ => done_set hp (by decide) v)

/-- Only the key guard and tag are needed before the null/hash split. -/
def Ready : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "level" ≤ locN s "klen" ∧
    (∃ Nd, NodeHeap s Nd ∧
      KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")) ∧
    mptKind s = 0 ∧ locN s "vlen" < 2 ^ 40

def Waiting : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => Ready s ∧ locN s "go" = 0

theorem ready_locals : LocalsOnly ["node", "key", "klen", "level", "vlen"] Ready := by
  intro F s locals k hl h
  dsimp only [Ready, mptKind] at h ⊢
  rw [arenaReady_with_locals,
    locN_congr s locals k "node" (hl "node" (by simp)),
    locN_congr s locals k "key" (hl "key" (by simp)),
    locN_congr s locals k "klen" (hl "klen" (by simp)),
    locN_congr s locals k "level" (hl "level" (by simp)),
    locN_congr s locals k "vlen" (hl "vlen" (by simp))]
  exact h

theorem ready_set {F : Type} {s : PanSemStateFiniteExact 64 F} (h : Ready s)
    {n : MlS} (hn : ∀ x ∈ ["node", "key", "klen", "level", "vlen"], ofString x ≠ n)
    (v : ValueHOL 64) : Ready (setVarHOLFinite n v s) :=
  ready_locals.setVar hn v s h

theorem reset_go : Step Ready (.assign .local (ofString "go") (.const 0)) Waiting := by
  apply Step.assign
  intro F s v hp hv
  cases RunFramesRace.evalAt_const s 0 v hv
  exact ⟨ready_set hp (by decide) _, RunFramesRace.locN_setVar_same s "go" 0⟩

private theorem fail_lookup : originalRuntimeCode.lookup (ofString "mpt_fail") =
    some ((sourceFunctionEntry Guest.Software.guestFn_mpt_fail).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_fail) rfl

/-- The literal failure body raises or errors; it never returns to this caller. -/
theorem fail_no_return : FunSpec (fun _ => True)
    (fun _ r _ => ∀ v, r ≠ some (.returned v)) (ofString "mpt_fail") := by
  refine ⟨_, _, _, fail_lookup, ?_⟩
  intro F s hc hp hlookup hnt v
  change (evaluateHOLFiniteState s (.seq
    (.raise (ofString "MptErr") (.var .local (ofString "code")))
    (.return (.const 0)))).1 ≠ some (.returned v)
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise]
  split <;> dsimp only <;> (try split_ifs) <;> simp

theorem fail_step (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    Step P (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) (fun _ => False) := by
  apply Hoare.call0 fail_no_return (fun _ _ _ _ _ _ _ _ _ => True.intro)
  · intro F s callee post v _ _ hr
    exact (hr v rfl).elim
  · intro F r s hne hcont
    exact ⟨hcont, fun hz => (hne hz).elim⟩

theorem condFalse_local_eq0 {F : Type} {s : PanSemStateFiniteExact 64 F} {n : String}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const 0)) s) :
    locN s n ≠ 0 := by
  obtain ⟨a, b, ha, hb, hw⟩ := RunFramesRace.cond_local s .equal n (.const 0) 0 h
  cases RunFramesRace.evalAt_const s 0 _ hb
  intro hz
  have heq : a = 0 := BitVec.eq_of_toNat_eq (by simpa using ha.trans hz)
  subst a
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw

theorem load_tag {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "node"), .const 0])) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "node") := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at hv
  rcases hn : s.locals.lookup (ofString "node") with _ | val
  · simp [hn] at hv
  · rcases val with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hn, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hv
        rcases hm : s.memory x with ⟨w⟩
        refine ⟨w, ?_, ?_⟩
        · rw [← hv.2, hm]
        · simp [memW, locN, hn, hm]
    · simp [hn, valueIsWord] at hv
    · simp [hn, valueIsWord] at hv

/-- A hashed node cannot fall through the failure guard. -/
theorem hashed (rest : ProgHOL 64) :
    Step (fun s => Waiting s ∧
      CondFalse (.cmp .equal (.var .local (ofString "node")) (.const 0)) s)
      (.dec (ofString "k") .one
        (.load .one (.op .add [.var .local (ofString "node"), .const 0]))
        (.seq (.ite (.cmp .equal (.var .local (ofString "k")) (.const 0))
          (.call (some (none, none)) (ofString "mpt_fail") [.const 2]) .skip) rest)) Done := by
  apply Step.dec (R := fun s => locN s "k" = 0) (names := ["go"]) (by decide)
  · intro F s v hp hv
    obtain ⟨w, rfl, hw⟩ := load_tag s v hv
    have hn := condFalse_local_eq0 hp.2
    have hk := hp.1.1.2.2.2.1
    simp only [mptKind, if_neg hn] at hk
    exact (RunFramesRace.locN_setVar_same s "k" w).trans (hw.trans hk)
  · apply Step.seq (R := fun _ => False)
    · apply Step.ite
      · exact fail_step _
      · exact Step.dead (fun _ hp => condFalse_local_eq0 hp.2 hp.1)
    · exact Step.dead (fun _ hp => hp)
  · exact done_locals

private theorem eval_add {F : Type} (s : PanSemStateFiniteExact 64 F) (n m : String)
    (v : ValueHOL 64)
    (hv : evalAt s (.op .add [.var .local (ofString n), .var .local (ofString m)]) = some v) :
    ∃ a b : BitVec 64, a.toNat = locN s n ∧ b.toNat = locN s m ∧
      v = .val (.word (a + b)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hv
  rcases ha : s.locals.lookup (ofString n) with _ | a
  · simp [ha] at hv
  · rcases hb : s.locals.lookup (ofString m) with _ | b
    · simp [ha, hb] at hv
    · rcases a with ⟨⟨a⟩⟩ | fs | ⟨name, fs⟩ <;>
        rcases b with ⟨⟨b⟩⟩ | gs | ⟨other, gs⟩ <;>
        simp [ha, hb, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
      exact ⟨a, b, by simp [locN, ha], by simp [locN, hb], hv.symm⟩

private theorem eval_sub {F : Type} (s : PanSemStateFiniteExact 64 F) (n m : String)
    (v : ValueHOL 64)
    (hv : evalAt s (.op .sub [.var .local (ofString n), .var .local (ofString m)]) = some v) :
    ∃ a b : BitVec 64, a.toNat = locN s n ∧ b.toNat = locN s m ∧
      v = .val (.word (a - b)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hv
  rcases ha : s.locals.lookup (ofString n) with _ | a
  · simp [ha] at hv
  · rcases hb : s.locals.lookup (ofString m) with _ | b
    · simp [ha, hb] at hv
    · rcases a with ⟨⟨a⟩⟩ | fs | ⟨name, fs⟩ <;>
        rcases b with ⟨⟨b⟩⟩ | gs | ⟨other, gs⟩ <;>
        simp [ha, hb, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
      exact ⟨a, b, by simp [locN, ha], by simp [locN, hb], hv.symm⟩

private def leafArgs : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "key"), .var .local (ofString "level")],
   .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")],
   .var .local (ofString "vptr"), .var .local (ofString "vlen")]

private theorem leaf_args {F : Type} (s : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (hle : locN s "level" ≤ locN s "klen")
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      leafArgs = some values) :
    ∃ a b : BitVec 64, ∃ v l, values = [.val (.word a), .val (.word b), v, l] ∧
      a.toNat = (locN s "key" + locN s "level") % 2^64 ∧
      b.toNat = locN s "klen" - locN s "level" ∧
      s.locals.lookup (ofString "vlen") = some l := by
  rw [evalListHOLFinite_eq_toExact] at ha
  dsimp only [leafArgs, evalListHOLExact] at ha
  rcases h0 : evalAt s (.op .add [.var .local (ofString "key"), .var .local (ofString "level")]) with _ | v0
  · simp only [h0] at ha; cases ha
  · rcases h1 : evalAt s (.op .sub [.var .local (ofString "klen"), .var .local (ofString "level")]) with _ | v1
    · simp only [h0, h1] at ha; cases ha
    · rcases h2 : evalAt s (.var .local (ofString "vptr")) with _ | v2
      · simp only [h0, h1, h2] at ha; cases ha
      · rcases h3 : evalAt s (.var .local (ofString "vlen")) with _ | v3
        · simp only [h0, h1, h2, h3] at ha; cases ha
        · simp only [h0, h1, h2, h3, Option.some.injEq] at ha
          obtain ⟨key, level, hk, hl, rfl⟩ := eval_add s "key" "level" v0 h0
          obtain ⟨klen, level', hkl, hl', rfl⟩ := eval_sub s "klen" "level" v1 h1
          refine ⟨key + level, klen - level', v2, v3, ha.symm, ?_, ?_, h3⟩
          · simp [BitVec.toNat_add, hk, hl]
          · rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; omega), hkl, hl']

private theorem leaf_lookup : originalRuntimeCode.lookup (ofString "node_new_leaf") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_new_leaf).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 256 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_new_leaf) rfl

private theorem leaf_params {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (a b : BitVec 64) (v l : ValueHOL 64)
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "node_new_leaf")
      [.val (.word a), .val (.word b), v, l] = some (body, callee, ret)) :
    callee.lookup (ofString "nib") = some (.val (.word a)) ∧
    callee.lookup (ofString "nlen") = some (.val (.word b)) ∧
    callee.lookup (ofString "vlen") = some l := by
  have raw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  unfold lookupCodeHOLExact at raw
  rw [hc, leaf_lookup] at raw
  change (if _ then some (_, _, _) else none) = some (body, callee.lookup, ret) at raw
  split at raw
  · have heq := (Prod.mk.inj (Option.some.inj raw)).2
    have hm := (Prod.mk.inj heq).1
    have hparams : (sourceFunctionEntry Guest.Software.guestFn_node_new_leaf).2.1 =
        [(ofString "nib", .one), (ofString "nlen", .one),
         (ofString "vptr", .one), (ofString "vlen", .one)] := rfl
    rw [hparams] at hm
    rw [← hm]
    simp +decide [List.zip, List.foldl]
  · cases raw

/-- The suffix arithmetic respects the key guard, including an empty suffix whose
pointer is allowed to wrap. -/
private theorem leaf_entry : CallEntryOn Waiting
    (NodeArgs [] (fun s Nd => KeyIn s Nd (locN s "nib") (locN s "nlen") ∧ locN s "vlen" < 2 ^ 40))
    (ofString "node_new_leaf") leafArgs := by
  intro F s values body callee ret hc hp ha hl
  obtain ⟨a, b, v, l, rfl, hab, hbb, hvl⟩ := leaf_args s values hp.1.2.1 ha
  obtain ⟨hnib, hnlen, hvlc⟩ := leaf_params s hc a b v l body callee ret hl
  have hnib' : locN (callEntryStateHOLFinite s callee) "nib" = a.toNat := by
    simp [locN, callEntryStateHOLFinite, hnib]
  have hnlen' : locN (callEntryStateHOLFinite s callee) "nlen" = b.toNat := by
    simp [locN, callEntryStateHOLFinite, hnlen]
  obtain ⟨Nd, hheap, hkey⟩ := hp.1.2.2.1
  refine ⟨localsFree_arenaReady s _ _ hp.1.1, Nd, hheap, by simp, ?_⟩
  refine ⟨?_, ?_⟩
  swap
  · have he : locN (callEntryStateHOLFinite s callee) "vlen" = locN s "vlen" := by
      simp only [locN, callEntryStateHOLFinite, hvlc, hvl]
    rw [he]
    exact hp.1.2.2.2.2
  change KeyIn (callEntryStateHOLFinite s callee) Nd _ _
  rw [hnib', hnlen', hbb]
  rcases hkey with hz | hkey
  · exact Or.inl hz
  · have hsmall : locN s "key" + locN s "level" < 2^64 := by
      have := hkey.2.2.1.2
      change locN s "key" + locN s "level" + (locN s "klen" - locN s "level") ≤ heapLimit at this
      have : heapLimit < 2^64 := by decide
      omega
    rw [hab, Nat.mod_eq_of_lt hsmall]
    exact Or.inr hkey

/-- The constructor restores the caller's locals, so its arena postcondition is
all that is needed when `go` is already zero. -/
theorem new_leaf (h : MptInsertCallees) :
    Step Waiting (.call (some (some (.local, ofString "r"), none))
      (ofString "node_new_leaf") leafArgs) Done := by
  apply Step.callLocal h.nf_node_new_leaf leaf_entry
  intro F s callee post v hp hpost
  have harena := (hpost (Or.inl ⟨v, rfl⟩)).1
  apply done_set (n := ofString "r") (hn := by decide)
  exact ⟨localsFree_arenaReady post s.locals post.clock harena, hp.2⟩

private theorem declare_ready {n : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64}
    (hn : ofString "go" ≠ n)
    (hr : ∀ x ∈ ["node", "key", "klen", "level", "vlen"], ofString x ≠ n)
    (h : Step Ready p Done) : Step Ready (.dec n sh e p) Done :=
  Step.dec (names := ["go"]) (by simpa using hn)
    (fun _ v hp _ => ready_set hp hr v) h done_locals

/-- Kernel reduction matches this walk to the literal insertion body. -/
theorem body_done (h : MptInsertCallees) : Step Ready mptInsertBody Done := by
  apply declare_ready (by decide) (by decide)
  apply declare_ready (by decide) (by decide)
  apply declare_ready (by decide) (by decide)
  apply declare_ready (by decide) (by decide)
  apply Step.seq reset_go
  apply Step.seq (R := Done)
  · apply Step.ite
    · exact (new_leaf h).mono (fun _ hp => hp.1)
    · exact hashed _
  · exact finish_done

end InsertKind0
end InitECandidate.Solver.Wave8GuestInv.GuardedBody
