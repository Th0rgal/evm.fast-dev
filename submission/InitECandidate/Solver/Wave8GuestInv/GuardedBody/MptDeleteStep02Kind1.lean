import InitECandidate.Solver.Wave8GuestInv.GuardedBody.MptCuts

/-! Cache framing, saved-stack preservation, and normal-outcome rules for leaf deletion.
The invalidation and comparison contracts are supplied by the caller. -/

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

theorem deleteStack_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clk p : Nat) (Nd fs : List Nat) :
    MptStack {s with locals := ls, clock := clk} Nd p fs ↔ MptStack s Nd p fs := by
  induction fs generalizing p with
  | nil => rfl
  | cons q qs ih => simp only [MptStack, ih]; rfl

/-- A cache write cannot change a disjoint key or an allocated scratch frame. -/
theorem deleteStack_cache {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {Nd Nd' : List Nat} {nd : Nat}
    (ha : ArenaReady s) (hn : NodeHeap s Nd) (hnd : nd ∈ Nd)
    (he : t = { clearCache s nd with locals := t.locals, clock := t.clock})
    (hsub : ∀ n ∈ Nd, n ∈ Nd') (hback : ∀ n ∈ Nd', n ∈ Nd)
    (hkind : ∀ n ∈ Nd, memW t n = memW s n) :
    ∀ p fs, MptStack s Nd p fs → MptStack t Nd' p fs := by
  have hsz : 32 ≤ nodeSize (memW s nd) := by
    unfold nodeSize; split_ifs <;> omega
  have hinside := (hn.1 nd hnd).2.2.1
  change sourceBase ≤ nd ∧ nd + nodeSize (memW s nd) ≤ heapLimit at hinside
  have hlimit : heapLimit < 2 ^ 64 := by decide
  have hndfit : nd + 24 < 2 ^ 64 := by omega
  have hmem (a : BitVec 64)
      (hne : a.toNat ≠ nd + 8 ∧ a.toNat ≠ nd + 16 ∧ a.toNat ≠ nd + 24) :
      t.memory a = s.memory a := by
    have h8 : a ≠ BitVec.ofNat 64 (nd + 8) := by
      intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nd + 8 < 2^64 by omega)] at this
      exact hne.1 this
    have h16 : a ≠ BitVec.ofNat 64 (nd + 16) := by
      intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nd + 16 < 2^64 by omega)] at this
      exact hne.2.1 this
    have h24 : a ≠ BitVec.ofNat 64 (nd + 24) := by
      intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hndfit] at this
      exact hne.2.2 this
    conv_lhs => rw [he]
    simp only [clearCache, h8, h16, h24, or_self, ite_false]
  have hg : t.globals = s.globals := by rw [he]; rfl
  have hd : t.memaddrs = s.memaddrs := by rw [he]; rfl
  have hb : t.be = s.be := by rw [he]; rfl
  have hgN (g : String) : globN t g = globN s g := by simp only [globN, hg]
  have hkey (p len : Nat) (hk : KeyIn s Nd p len) : KeyIn t Nd' p len := by
    rcases hk with hz | ⟨hnib, hal, hi, hdis⟩
    · exact Or.inl hz
    · right
      refine ⟨?_, ?_, hi, ?_⟩
      · intro k hk
        have hfit : p + k < 2 ^ 64 := by have := hi.2; omega
        have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
        have halign : (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat ≤ p + k ∧
            p + k < (panByteAlignHOL (BitVec.ofNat 64 (p + k))).toNat + 8 := by
          simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
          rw [Nat.mod_eq_of_lt (show (p + k) / 8 * 8 < 2^64 by omega)]
          omega
        have hsep := hdis nd hnd
        simp only [Disj, nodeIvl] at hsep
        have hsz : 32 ≤ nodeSize (memW s nd) := by unfold nodeSize; split_ifs <;> omega
        have hm := hmem (panByteAlignHOL (BitVec.ofNat 64 (p + k)))
          ⟨by omega, by omega, by omega⟩
        simpa only [memB, hm, hb] using hnib k hk
      · simpa only [Allocated, globN, hg] using hal
      · intro n hn'
        simp only [nodeIvl, hkind n (hback n hn')]
        exact hdis n (hback n hn')
  have hscratch (p : Nat) (hp : Inside (p, 40) (globN s "scratch_ptr") scratchEnd)
      (off : Nat) (hoff : off ≤ 32) : memW t (p + off) = memW s (p + off) := by
    have hlo := ha.2.2.2.1
    have hgap := ha.2.2.2.2.1
    have hsep : heapLimit ≤ scratchStart := by decide
    have hend : scratchEnd < 2^64 := by decide
    have hfit : p + off < 2^64 := by have := hp.2; dsimp only at this; omega
    unfold memW
    rw [hmem (BitVec.ofNat 64 (p + off))]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    dsimp only [Inside] at hp
    exact ⟨by omega, by omega, by omega⟩
  have hframe (p : Nat) (hf : MptFrameOK s Nd p) :
      MptFrameOK t Nd' p ∧ memW t p = memW s p := by
    obtain ⟨hi, hw, hm, htag⟩ := hf
    have hw0 := hscratch p hi 0 (by omega)
    have hw8 := hscratch p hi 8 (by omega)
    have hw16 := hscratch p hi 16 (by omega)
    have hw24 := hscratch p hi 24 (by omega)
    have hw32 := hscratch p hi 32 (by omega)
    refine ⟨?_, by simpa using hw0⟩
    unfold MptFrameOK
    rw [hgN, hw8, hw16, hw24, hw32]
    refine ⟨hi, ?_, hsub _ hm, ?_⟩
    · refine ⟨hw.1, hw.2.1, ?_⟩
      intro k hk
      obtain ⟨w, hdom, _⟩ := hw.2.2 k hk
      cases hm' : t.memory (BitVec.ofNat 64 (p + 8 * k)) with
      | word w' => exact ⟨w', by simpa only [hd] using hdom, hm'⟩
    · rw [hkind _ hm]
      rcases htag with ⟨h2, hn2, hk⟩ | h3
      · exact Or.inl ⟨h2, hn2, hkey _ _ hk⟩
      · exact Or.inr h3
  intro p fs
  induction fs generalizing p with
  | nil => exact id
  | cons q qs ih =>
    rintro ⟨hp, hz, hf, hlt, hs⟩
    obtain ⟨hf', hm⟩ := hframe p hf
    exact ⟨hp, hz, hf', hlt, by rw [hm]; exact ih _ hs⟩

/-- The node set and saved stack, with their addresses carried as ghosts. -/
def DeleteSaved (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd fs, NodeHeap s Nd ∧ MptStack s Nd top fs ∧ node ∈ Nd

theorem deleteSaved_locals (node top : Nat) : LocalsFree (DeleteSaved node top) := by
  intro F s ls clk h
  obtain ⟨ha, Nd, fs, hn, hs, hm⟩ := h
  exact ⟨localsFree_arenaReady s ls clk ha, Nd, fs, hn,
    (deleteStack_locals s ls clk top Nd fs).2 hs, hm⟩

theorem deleteInvalidate_spec (h : MptDeleteCallees) (node top : Nat) :
    FunSpec (fun s => DeleteSaved node top s ∧ locN s "nd" = node)
      (fun _ r t => Resumes r → DeleteSaved node top t) (ofString "node_invalidate") := by
  obtain ⟨ps, body, ret, hl, hnf⟩ := h.nf_node_invalidate
  obtain ⟨ps', body', ret', hl', hiz⟩ := h.iz_node_invalidate
  have heq := Option.some.inj (hl.symm.trans hl')
  cases heq
  refine ⟨ps, body, ret, hl, ?_⟩
  intro F s hc hp hlookup hnt hr
  obtain ⟨⟨ha, Nd, fs, hn, hs, hm⟩, hnd⟩ := hp
  have hroots : ∀ name ∈ ["nd"], RootIn Nd (locN s name) := by
    intro name hname
    simp only [List.mem_singleton] at hname
    subst name
    rw [hnd]
    exact Or.inr hm
  have hp : NodeArgs ["nd"] (fun _ _ => True) s := ⟨ha, Nd, hn, hroots, trivial⟩
  have hout := hnf s hc hp hlookup hnt hr
  have he := hiz s hc hp hlookup hnt hr
  change (evaluateHOLFiniteState s body).2 =
    { clearCache s (locN s "nd") with
      locals := (evaluateHOLFiniteState s body).2.locals,
      clock := (evaluateHOLFiniteState s body).2.clock } at he
  rw [hnd] at he
  obtain ⟨ha', _, _, hex⟩ := hout
  obtain ⟨Nd', hn', hsub, hkind, hnew, _⟩ := hex Nd hn hroots trivial
  have hg : globN (evaluateHOLFiniteState s body).2 "heap_ptr" = globN s "heap_ptr" := by
    rw [he]; rfl
  have hback : ∀ n ∈ Nd', n ∈ Nd := by
    intro n hm'
    rcases hnew n hm' with hm | hi
    · exact hm
    · rw [hg] at hi
      have hsize : 0 < nodeSize (memW (evaluateHOLFiniteState s body).2 n) := by
        unfold nodeSize; split_ifs <;> omega
      have := hi.1
      have := hi.2
      dsimp only [nodeIvl] at *
      omega
  exact ⟨ha', Nd', fs, hn', deleteStack_cache ha hn hm he hsub hback hkind top fs hs, hsub node hm⟩

/-- Normal fall-through triples also record that no `continue` is emitted. -/
def DeleteTriple (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (p : ProgHOL 64) (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  Hoare P p (fun r t => r ≠ some .continue ∧ (r = none → Q t))

namespace DeleteTriple
variable {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}

theorem mono {p : ProgHOL 64} (h : DeleteTriple R p Q)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → R s) : DeleteTriple P p Q :=
  Hoare.mono h hp

theorem of_false {p : ProgHOL 64}
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → False) : DeleteTriple P p Q :=
  Hoare.of_false hp

theorem skip (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s) :
    DeleteTriple P .skip Q := Hoare.skip (fun s h => ⟨by simp, fun _ => hp s h⟩)

theorem seq {p q : ProgHOL 64} (h1 : DeleteTriple P p R) (h2 : DeleteTriple R q Q) :
    DeleteTriple P (.seq p q) Q := by
  refine Hoare.seq ⟨fun s hc hp hnt => ?_⟩ h2
  have h := h1.run s hc hp hnt
  exact ⟨h.2, fun hr => ⟨h.1, fun hn => (hr hn).elim⟩⟩

theorem ite {c : ExpHOL 64} {p q : ProgHOL 64}
    (hy : DeleteTriple (fun s => P s ∧ CondTrue c s) p Q)
    (hn : DeleteTriple (fun s => P s ∧ CondFalse c s) q Q) :
    DeleteTriple P (.ite c p q) Q :=
  Hoare.ite hy hn (fun _ _ => ⟨by simp, fun h => by cases h⟩)

theorem assign {name : MlS} {e : ExpHOL 64}
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → Q (setVarHOLFinite name v s)) :
    DeleteTriple P (.assign .local name e) Q :=
  Hoare.assign (fun s v h hv => ⟨by simp, fun _ => hp s v h hv⟩)
    (fun _ _ => ⟨by simp, fun h => by cases h⟩)

theorem dec {names : List String} {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64}
    {body : ProgHOL 64} (hne : ∀ n ∈ names, ofString n ≠ name)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s e = some v → R (setVarHOLFinite name v s))
    (hb : DeleteTriple R body Q) (hq : LocalsOnly names Q) :
    DeleteTriple P (.dec name shape e body) Q :=
  Hoare.dec hne hp hb (fun _ t ls hl h => ⟨h.1, fun hr => hq t ls t.clock hl (h.2 hr)⟩)
    (fun _ _ => ⟨by simp, fun h => by cases h⟩)

theorem decCall {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)}
    {body : ProgHOL 64} {names : List String}
    (hres : DecCallResumeOn P R name fname args)
    (hb : DeleteTriple R body Q) (hq : LocalsOnly names Q)
    (hne : ∀ n ∈ names, ofString n ≠ name) :
    DeleteTriple P (.decCall name shape fname args body) Q := by
  refine ⟨fun s hc hp hnt => ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  cases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => exact ⟨by simp, fun h => by cases h⟩
  | some values =>
    simp only [ha] at hnt ⊢
    cases hl : lookupCodeHOLFinite s.code.lookup fname values with
    | none => exact ⟨by simp, fun h => by cases h⟩
    | some entry =>
      obtain ⟨b, callee, ret⟩ := entry
      simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) b).1
        cases hr : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with
        | mk r post =>
          simp only [hr] at hnt hm ⊢
          cases r with
          | none => exact ⟨by simp, fun h => by cases h⟩
          | some r =>
            cases r with
            | returned v =>
              by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) shape &&
                  shapeEqHOL (shapeOfHOLExact v) ret) = true
              · simp only [hsh, ↓reduceIte] at hnt ⊢
                have hi := hres s values b callee ret v post hc hp ha hl hr
                have hh := hb.run _ (by exact hm.trans hc) hi hnt
                exact ⟨hh.1, fun hn => hq _ _ _
                  (fun n hn => resVarEq_lookup_ne _ _ _ _ (hne n hn)) (hh.2 hn)⟩
              · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
                exact ⟨by simp, fun h => by cases h⟩
            | timeOut => simp at hnt
            | «continue» => exact ⟨by simp, fun h => by cases h⟩
            | «break» => exact ⟨by simp, fun h => by cases h⟩
            | error => exact ⟨by simp, fun h => by cases h⟩
            | exception _ _ => exact ⟨by simp, fun h => by cases h⟩
            | finalFfi _ => exact ⟨by simp, fun h => by cases h⟩

end DeleteTriple

theorem deleteInvalidate_lookup : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

theorem deleteCallee_one {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname actual formal : MlS) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : s.code.lookup fname = some ([(formal, .one)], body, ret))
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local actual] = some values)
    (hc : lookupCodeHOLFinite s.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup formal = s.locals.lookup actual := by
  rw [evalListHOLFinite_eq_toExact] at ha
  simp only [evalListHOLExact, evalHOLExact] at ha
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hc
  split at hc
  · cases hc
  · rename_i b ls sh raw
    obtain ⟨rfl, rfl, _⟩ := Prod.mk.inj (Option.some.inj hc)
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    cases hv : s.locals.lookup actual with
    | none => rw [hv] at ha; cases ha
    | some v =>
      rw [hv] at ha
      cases ha
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨_, hrest⟩
        rcases Prod.mk.inj hrest with ⟨hloc, _⟩
        subst hloc
        simp
      · cases raw

def DeleteTagged (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteSaved node top s ∧ locN s "node" = node ∧ locN s "top" = top ∧
    locN s "go" = 0 ∧ locN s "k" = 1

def DeleteLeafOut (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteSaved node top s ∧ locN s "top" = top ∧ locN s "go" = 0 ∧
    (locN s "res" = 0 ∨ locN s "res" = node)

theorem deleteTagged_invalidate (h : MptDeleteCallees) (node top : Nat) :
    DeleteTriple (DeleteTagged node top)
      (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
      (DeleteTagged node top) := by
  refine Hoare.call0 (deleteInvalidate_spec h node top) ?_ ?_
    (fun _ _ hn hc => ⟨hc, fun hz => (hn hz).elim⟩)
  · intro F s values body callee ret hc hp ha hl
    have he := deleteCallee_one s (ofString "node_invalidate") (ofString "node")
      (ofString "nd") _ _ (by rw [hc]; exact deleteInvalidate_lookup) values body callee ret ha hl
    refine ⟨deleteSaved_locals node top s callee (s.clock - 1) hp.1, ?_⟩
    change locN {s with locals := callee, clock := s.clock - 1} "nd" = node
    simpa only [locN, he] using hp.2.1
  · intro F s callee post v hc hp hq
    refine ⟨by simp, fun _ => ?_⟩
    exact ⟨deleteSaved_locals node top post s.locals post.clock (hq (Or.inl ⟨v, rfl⟩)), hp.2⟩

theorem deleteEval_loadL' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
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
theorem deleteEval_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
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
  exact ⟨a, rfl, deleteEval_loadL' t g k a h⟩

theorem deleteCond_eq_true {F : Type} {s : PanSemStateFiniteExact 64 F} {name : String}
    {k : BitVec 64} (h : CondTrue (.cmp .equal (.var .local (ofString name)) (.const k)) s) :
    locN s name = k.toNat := by
  obtain ⟨w, hw, hz⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local s _ name _ w hw
  cases evalAt_const s k _ hb
  by_cases he : a = k
  · simpa only [he] using ha.symm
  · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he] at hz

theorem deleteCond_eq_false {F : Type} {s : PanSemStateFiniteExact 64 F} {name : String}
    {k : BitVec 64} (h : CondFalse (.cmp .equal (.var .local (ofString name)) (.const k)) s) :
    locN s name ≠ k.toNat := by
  obtain ⟨a, b, ha, hb, hz⟩ := cond_local s _ name _ 0 h
  cases evalAt_const s k _ hb
  intro he
  have hak : a = k := BitVec.eq_of_toNat_eq (ha.trans he)
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hak] at hz

theorem deleteLeafOut_locals (node top : Nat) :
    LocalsOnly ["top", "go", "res"] (DeleteLeafOut node top) := by
  intro F s ls clk hl hp
  obtain ⟨hs, ht, hg, hr⟩ := hp
  refine ⟨deleteSaved_locals node top s ls clk hs, ?_, ?_, ?_⟩
  · rw [locN_congr s ls clk "top" (hl "top" (by simp))]; exact ht
  · rw [locN_congr s ls clk "go" (hl "go" (by simp))]; exact hg
  · rw [locN_congr s ls clk "res" (hl "res" (by simp))]; exact hr

theorem deleteTagged_locals (node top : Nat) :
    LocalsOnly ["node", "top", "go", "k"] (DeleteTagged node top) := by
  intro F s ls clk hl hp
  obtain ⟨hs, hn, ht, hg, hk⟩ := hp
  refine ⟨deleteSaved_locals node top s ls clk hs, ?_, ?_, ?_, ?_⟩
  · rw [locN_congr s ls clk "node" (hl "node" (by simp))]; exact hn
  · rw [locN_congr s ls clk "top" (hl "top" (by simp))]; exact ht
  · rw [locN_congr s ls clk "go" (hl "go" (by simp))]; exact hg
  · rw [locN_congr s ls clk "k" (hl "k" (by simp))]; exact hk

theorem deleteAssign_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src : String) (v : ValueHOL 64) (hv : evalAt s (.var .local (ofString src)) = some v) :
    locN (setVarHOLFinite (ofString dst) v s) dst = locN s src := by
  change s.locals.lookup (ofString src) = some v at hv
  simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv]

private theorem leafStraight (p : ProgHOL 64) (hs : extStraightLine p = true) :
    TerminatingProgBoundedOn GuestInv p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p hs s hc

private theorem leafDec {name : MlS} {shape : ShapeHOL} {e : ExpHOL 64}
    {p : ProgHOL 64} {b : Nat} (h : TerminatingProgBoundedOn GuestInv p b) :
    TerminatingProgBoundedOn GuestInv (.dec name shape e p) b :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape e h

private theorem leafCall {name : MlS} {b : Nat} {dst : Option (VarKind × MlS)}
    {args : List (ExpHOL 64)} (h : TerminatingFunBoundedOn GuestInv name b) :
    TerminatingProgBoundedOn GuestInv (.call (some (dst, none)) name args) (b + 1) :=
  TerminatingProgBoundedOn.call_guestInv h dst args

private theorem leafDecCall {name fname : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)}
    {p : ProgHOL 64} {b c : Nat} (h : TerminatingFunBoundedOn GuestInv fname b)
    (hp : TerminatingProgBoundedOn GuestInv p c) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname args p) (b + c + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv h name shape args hp

syntax "delete_bound" : tactic
macro_rules
  | `(tactic| delete_bound) => `(tactic| (first
      | assumption
      | exact leafStraight _ rfl
      | apply TerminatingProgBoundedOn.seq_guestInv
      | apply TerminatingProgBoundedOn.ite_on
      | apply leafDec
      | apply leafCall
      | apply leafDecCall) <;> delete_bound)

private theorem deleteBody_bound (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptDeleteBody mptDeleteCost := by
  have h1 := h.fb__collapse_branch
  have h2 := h.fb__delete_ext_finish
  have h3 := h.fb_common_prefix_length
  have h4 := h.fb_memeq
  have h5 := h.fb_mpt_fail
  have h6 := h.fb_node_invalidate
  have h7 := h.fb_scratch_alloc
  apply TerminatingProgBoundedOn.mono_bound
  · simp only [mptDeleteBody, mptDeleteTail, mptDeleteCode, mptDecBody, mptWhileBody,
      mptLeft, sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
    delete_bound
  · simp only [mptDeleteCost, Nat.zero_add, Nat.add_zero, Nat.zero_max,
      Nat.max_zero, Nat.add_assoc]
    simp only [Nat.add_left_comm]
    exact Nat.le_refl _

private def DeleteEntry (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteSaved node top s ∧ locN s "node" = node ∧ locN s "top" = top ∧ memW s node = 1

private def DeleteStarted (node top : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => DeleteEntry node top s ∧ locN s "go" = 0

private theorem deleteLeaf_walk (h : MptDeleteCallees) (node top : Nat) (hz : node ≠ 0) :
    DeleteTriple (DeleteEntry node top) mptDeleteBody (DeleteLeafOut node top) := by
  simp only [mptDeleteBody, mptDeleteTail, mptDeleteCode, mptDecBody, mptWhileBody,
    mptLeft, sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  apply DeleteTriple.seq (R := DeleteStarted node top)
  · apply DeleteTriple.assign
    intro F t v hp hv
    cases evalAt_const t 0 v hv
    refine ⟨⟨deleteSaved_locals node top t _ t.clock hp.1, ?_, ?_, hp.2.2.2⟩, ?_⟩
    · rw [locN_setVar_ne t "node" _ _ (by decide)]; exact hp.2.1
    · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.2.2.1
    · rw [locN_setVar_same]; rfl
  · apply DeleteTriple.ite
    · apply DeleteTriple.of_false
      intro F t hp
      have he := deleteCond_eq_true hp.2
      exact hz (hp.1.1.2.1.symm.trans he)
    · apply DeleteTriple.dec (R := DeleteTagged node top) (names := ["top", "go", "res"])
        (by decide)
      · intro F t v hp hv
        obtain ⟨a, rfl, ha⟩ := deleteEval_loadL t "node" 0 v hv
        have hat : a.toNat = 1 := by
          change a.toNat = memW t (locN t "node" + 0) at ha
          rw [Nat.add_zero, hp.1.1.2.1] at ha
          exact ha.trans hp.1.1.2.2.2
        refine ⟨deleteSaved_locals node top t _ t.clock hp.1.1.1, ?_, ?_, ?_, ?_⟩
        · rw [locN_setVar_ne t "node" _ _ (by decide)]; exact hp.1.1.2.1
        · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.1.1.2.2.1
        · rw [locN_setVar_ne t "go" _ _ (by decide)]; exact hp.1.2
        · rw [locN_setVar_same]; exact hat
      · apply DeleteTriple.seq (R := DeleteTagged node top)
        · apply DeleteTriple.ite
          · apply DeleteTriple.of_false
            intro F t hp
            have he := deleteCond_eq_true hp.2
            have hk := hp.1.2.2.2.2
            simp only [BitVec.toNat_zero] at he
            omega
          · exact DeleteTriple.skip (fun _ hp => hp.1)
        · apply DeleteTriple.seq (deleteTagged_invalidate h node top)
          apply DeleteTriple.ite
          · apply DeleteTriple.seq (R := DeleteLeafOut node top)
            · apply DeleteTriple.assign
              intro F t v hp hv
              have ht := LocalsOnly.setVar (P := DeleteTagged node top)
                (deleteTagged_locals node top)
                (name := ofString "res") (by decide) v t hp.1
              exact ⟨ht.1, ht.2.2.1, ht.2.2.2.1,
                Or.inr ((deleteAssign_local t "res" "node" v hv).trans hp.1.2.1)⟩
            · apply DeleteTriple.ite
              · refine DeleteTriple.mono ?_ (fun _ hp => hp.1)
                apply DeleteTriple.decCall (R := DeleteLeafOut node top)
                  (names := ["top", "go", "res"])
                · exact ReadOnlyFn.resumeOn (deleteLeafOut_locals node top)
                    (fun _ hp => hp.1.1.1) h.ro_memeq _ (by decide) _
                · apply DeleteTriple.ite
                  · apply DeleteTriple.assign
                    intro F t v hp hv
                    cases evalAt_const t 0 v hv
                    refine ⟨deleteSaved_locals node top t _ t.clock hp.1.1, ?_, ?_, Or.inl ?_⟩
                    · rw [locN_setVar_ne t "top" _ _ (by decide)]; exact hp.1.2.1
                    · rw [locN_setVar_ne t "go" _ _ (by decide)]; exact hp.1.2.2.1
                    · rw [locN_setVar_same]; rfl
                  · exact DeleteTriple.skip (fun _ hp => hp.1)
                · exact deleteLeafOut_locals node top
                · decide
              · exact DeleteTriple.skip (fun _ hp => hp.1)
          · apply DeleteTriple.of_false
            intro F t hp
            exact deleteCond_eq_false hp.2 hp.1.2.2.2.2
      · exact deleteLeafOut_locals node top

private theorem deleteLeaf_post (h : MptDeleteCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hp : MptDeleteActive s) (hk : mptKind s = 1) (hf : MptFlow s mptDeleteBody) :
    MptDeleteHead (evaluateHOLFiniteState s mptDeleteBody).2 ∧
      MptDeleteEffect s (evaluateHOLFiniteState s mptDeleteBody).2 := by
  have hz : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have htag : memW s (locN s "node") = 1 := by
    simpa only [mptKind, if_neg hz] using hk
  obtain ⟨Nd, fs, hn, hs, _, ha⟩ := hp.1.2
  have hm : locN s "node" ∈ Nd := ((ha hp.2).2.1).resolve_left hz
  have he : DeleteEntry (locN s "node") (locN s "top") s :=
    ⟨⟨hp.1.1, Nd, fs, hn, hs, hm⟩, rfl, rfl, htag⟩
  have hnt : (evaluateHOLFiniteState s mptDeleteBody).1 ≠ some .timeOut := by
    rcases hf with hf | hf <;> simp [hf]
  have hout := (deleteLeaf_walk h (locN s "node") (locN s "top") hz).run s hc he hnt
  have hdone : DeleteLeafOut (locN s "node") (locN s "top")
      (evaluateHOLFiniteState s mptDeleteBody).2 := by
    rcases hf with hf | hf
    · exact hout.2 hf
    · exact (hout.1 hf).elim
  obtain ⟨⟨ha', Nd', fs', hn', hs', hm'⟩, ht, hg, hr⟩ := hdone
  refine ⟨⟨ha', Nd', fs', hn', ?_, ?_, ?_⟩, Or.inl hg⟩
  · rw [ht]; exact hs'
  · rcases hr with hr | hr
    · exact Or.inl hr
    · exact Or.inr (hr ▸ hm')
  · intro hgo
    exact (hgo hg).elim

/-- One iteration with node tag 1; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind1 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 1 := by
  intro F s hc hp hk
  refine ⟨deleteBody_bound h s hc hp.1.1.1, ?_⟩
  intro hflow
  exact deleteLeaf_post h s hc hp hk hflow

end InitECandidate.Solver.Wave8GuestInv.GuardedBody
