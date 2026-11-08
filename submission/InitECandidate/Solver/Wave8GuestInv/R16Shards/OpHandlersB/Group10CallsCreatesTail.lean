import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## Private helpers copied verbatim from Group10CallsCreates.lean (frozen) -/
private theorem store_some_eq_error_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

private theorem evmInv_head_ev_bounds_g10 {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ heapEnd ∧ globN s "ev" + 280 ≤ 2 ^ 64 := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
  have hFW0 := hFW_all _ hhead
  have hin1 := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin2 := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  dsimp only at hin1 hin2
  have hfm1 := hAs.2.2.2.1
  have hfm2 := hAs.2.2.2.2.1
  rw [R11Shards.scratchStart_val] at hfm1
  rw [R11Shards.scratchEnd_val] at hin2
  rw [R11Shards.heapEnd_val]
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  rw [h264]
  exact ⟨by omega, by omega, by omega⟩

/-- The eval of a binary word-op is a word whenever it is defined (the `.op` case of
`evalHOLExact` either fails or produces `.val (.word _)`). -/
private theorem eval_op_word_g10 {F : Type} {st : PanSemStateFiniteExact 64 F}
    {op : BinOp} {args : List (ExpHOL 64)} {v : ValueHOL 64}
    (hv : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op op args) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  unfold evalHOLExact at hv
  revert hv
  cases hlist : @evalListHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) args with
  | none => intro h; simp at h
  | some vs =>
    intro hv
    dsimp only at hv
    split at hv
    · rename_i hall
      rcases hw : wordOpHOL op (vs.map valueWord) with _ | w
      · rw [hw] at hv; simp at hv
      · rw [hw] at hv; simp at hv
        exact ⟨w, hv.symm⟩
    · simp at hv

/-- ccA counterpart of `HandlerRunA.seq_store_ev_off_charged_g10`: a word store to global
`ev + off` inside a `ChildContinuationA` walk, with the caller supplying the invariant
preservation for the memory-updated state. -/
private theorem ccA_store_ev_off_g10 {F : Type} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {off : Nat} {valExp : ExpHOL 64} {cont : ProgHOL 64}
    (hoff : off < 280)
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hstep : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) →
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } ∧
      Group10.HeadMemChainWF { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } ∧
      evmChain { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } = evmChain t ∧
      evmR { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w } ≤ evmR t ∧
      Q { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w })
    (hcont : ChildContinuationA Q cont) :
    ChildContinuationA P
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) cont) := by
  intro t hc hi hw hp hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) with ⟨r1, t1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error_g10 hst
    subst herr
    refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hi
    obtain ⟨w, hw_ev, ht1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := t) (post := t1)
      (gname := "ev") (gbase := globN t "ev") (off := off) hevw hevw_nat (by omega)
      (fun v hv => hval t v hp hv) hst
    subst ht1_eq
    obtain ⟨hInv1, hWF1, hch1, hRle, hQ1⟩ := hstep t w hw_ev hi hw hp
    have hcc := hcont { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w }
      hc hInv1 hWF1 hQ1 hnt
    refine ⟨?_, ?_⟩
    · intro hv
      have hR2 := hcc.1 hv
      exact ⟨hR2.1, Nat.le_trans hR2.2 hRle⟩
    · intro he
      have hR2 := hcc.2 he
      rw [hch1] at hR2
      exact ⟨hR2.1, hR2.2.1, Nat.le_trans hR2.2.2 hRle⟩
/-! ## 6. `op_delegatecall`: chain-head and locals-purity helpers -/

/-- The chain-head read: a chain equality against the call entry of `t` pins `globN cpost "ev"`,
which then equals `globN t "ev"` definitionally. -/
private theorem globN_resume_eq_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hch : evmChain cpost = evmChain (callEntryStateHOLFinite t callee)) :
    globN cpost "ev" = globN t "ev" := by
  have h1 : ∀ s : PanSemStateFiniteExact 64 F, ∃ tl,
      evmChain s = (globN s "ev", globN s "cur_cont") :: tl := by
    intro s
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos
    rw [hm, evmChainFrom]
    exact ⟨_, rfl⟩
  obtain ⟨tl1, h1'⟩ := h1 cpost
  obtain ⟨tl2, h2'⟩ := h1 (callEntryStateHOLFinite t callee)
  rw [h1', h2'] at hch
  injection hch with hhead _
  exact ((Prod.mk.inj hhead).1).trans rfl

/-- A pending memory-expansion record survives a locals-update away from `x`. -/
private theorem mel_setVar_keep_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (hp : MemoryExpansionLocal_g10 t) (nm : MlS) (v : ValueHOL 64) (hne : nm ≠ ofString "x") :
    MemoryExpansionLocal_g10 (setVarHOLFinite nm v t) :=
  memoryExpansionLocal_transport_g10 hp
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]) rfl rfl

/-- Same for the `setKvar` form produced by `assign` nodes. -/
private theorem mel_setKvar_keep_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    (hp : MemoryExpansionLocal_g10 t) (nm : MlS) (v : ValueHOL 64) (hne : nm ≠ ofString "x") :
    MemoryExpansionLocal_g10 (setKvarHOLFinite .local nm v t) := by
  have h : setKvarHOLFinite .local nm v t = setVarHOLFinite nm v t := rfl
  rw [h]
  exact mel_setVar_keep_g10 hp nm v hne

/-- `PositiveCostLocal_g10` for a freshly assigned positive word, `setKvar` form. -/
private theorem posCost_setKvar_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (name : MlS)
    (w : BitVec 64) (hw : 0 < w.toNat) :
    PositiveCostLocal_g10 name (setKvarHOLFinite .local name (.val (.word w)) s) := by
  refine ⟨w, ?_, hw⟩
  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- The delegation-cost record: `dl` is the `calculate_delegation_cost` triple with the
gas-cost implications the handler's `ite` needs. -/
def DlPreG10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ d0 d1 d2 : BitVec 64,
    t.locals.lookup (ofString "dl") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2)]) ∧
    (d0 = 0#64 → d2 = 0#64) ∧ (d0 ≠ 0#64 → 0 < d2.toNat)

/-- `DlPreG10` is pure bookkeeping on the `dl` local: it survives any other locals-update. -/
private theorem dlPre_setVar_g10 {F : Type} {t : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    (hp : DlPreG10 t) {nm : MlS} (hne : nm ≠ ofString "dl") :
    DlPreG10 (setVarHOLFinite nm v t) := by
  obtain ⟨d0, d1, d2, hl, h1, h2⟩ := hp
  exact ⟨d0, d1, d2, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hl],
    h1, h2⟩

/-- `DlPreG10` survives a plain `call` whose post-state restores `t.locals`. -/
private theorem dlPre_locals_keep_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    (hp : DlPreG10 t) : DlPreG10 { cpost with locals := t.locals } :=
  hp

/-- The pending memory-expansion record survives a `decCall` whose post-state keeps the callee
entry's `ev` global (read off the chain head) and the entry's `ev+32` memory word. -/
private theorem mel_resume_keep32_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hp : MemoryExpansionLocal_g10 t)
    (hch : evmChain cpost = evmChain (callEntryStateHOLFinite t callee))
    (hmk : memW cpost (globN (callEntryStateHOLFinite t callee) "ev" + 32) =
      memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32))
    (nm : MlS) (v : ValueHOL 64) (hne : nm ≠ ofString "x") :
    MemoryExpansionLocal_g10 (setVarHOLFinite nm v { cpost with locals := t.locals }) := by
  have hge := globN_resume_eq_g10 callee hch
  refine memoryExpansionLocal_transport_g10 hp
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]) ?_ ?_
  · exact hge
  · exact hmk

/-- The pending memory-expansion record survives a plain `call` whose post-state keeps the
caller's `globals` field and the `ev+32` memory word. -/
private theorem mel_seq_call_resume_keep32_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    (hp : MemoryExpansionLocal_g10 t)
    (hglob : cpost.globals = t.globals)
    (hmk : memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32)) :
    MemoryExpansionLocal_g10 { cpost with locals := t.locals } := by
  refine memoryExpansionLocal_transport_g10 hp rfl ?_ ?_
  · show globN cpost "ev" = globN t "ev"
    unfold globN
    rw [hglob]
  · show memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32)
    exact hmk

/-- The pending memory-expansion record survives a plain `call` whose post-state is a
`LocFrame` of the callee entry (so its `globals`/`memory` fields agree with the caller's). -/
private theorem mel_seq_call_resume_g10 {F : Type} {t cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (hp : MemoryExpansionLocal_g10 t)
    (hlf : LocFrame (callEntryStateHOLFinite t callee) cpost) :
    MemoryExpansionLocal_g10 { cpost with locals := t.locals } := by
  unfold LocFrame at hlf
  rw [hlf]
  exact memoryExpansionLocal_transport_g10 hp rfl rfl rfl

/-- Refined `warm_address` spec that additionally records `ev+32` preservation. -/
private theorem three_one_word_call_args_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem eval_seq_htab_set_ev_slot_unhit_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (off : Nat) (keyVar : MlS) (v_ret : ValueHOL 64)
    (hoff : off < 280)
    (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s)
    (ht0 : ∀ S, EvmInvAt s S → memW s (globN s "ev" + off) ∈ S)
    (hret : (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).1 = some (.returned v_ret)) :
    let post := (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).2
    ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧ R16Shards.IvlUnhit s post (ec.2, 104) := by
  dsimp only
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hret; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_g10 s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]))
        (.var .local keyVar) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hev_pos, _, hb_ev⟩ := evmInv_head_ev_bounds_g10 ⟨hAs, S, hInvAt⟩
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have htw_nat : tw.toNat = memW s (globN s "ev" + off) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + off)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        have hz_add : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
        rw [hz_add]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hevw_nat, h264,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + off)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + off))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      have ht0_S : memW s (globN s "ev" + off) ∈ S := ht0 S hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + off) := by
        simp [locN, hcal_t, htw_nat]
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩, ?_, ?_⟩
        · rw [hloc_ts]
          exact (R16Shards.StateRestoreEpilogue.htabWF_lc s entry_s.locals s.globals entry_s.clock _).mpr
            (hInvAt.1.1.2.1 _ ht0_S).1
        · rw [hloc_ts]
          intro i hi
          exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, _, _, _, hhp_s, _, hfr_s, _⟩ := hexit_s
      obtain ⟨⟨hT, _, _, _⟩, _, _, _, hFW_all, _, _, _, hFO_disj, _⟩ := hInvAt
      have hpost_mem : post_c.memory = cpost_s.memory := by
        rw [← hpost_c, hs2_eq]; rfl
      have hfr_sp : FrameOutside s post_c
          (htabFootprint s (memW s (globN s "ev" + off)))
          (globN s "heap_ptr", globN cpost_s "heap_ptr" - globN s "heap_ptr") := by
        intro a h1 h2
        rw [hpost_mem]
        exact hfr_s a h1 h2
      have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
      have hf_al2 : (globN cpost_s "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
        have := hAs.2.2.2.2.2.2.1; have := hAp_s.2.2.2.2.2.2.1; omega
      have ht0_al : ∀ j ∈ htabFootprint s (memW s (globN s "ev" + off)),
          j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
        have hw := ((hT.2.1 _ ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
      intro ec hec
      have hFW := hFW_all ec hec
      have h1 := hFW.1 (ec.1, 280) (by simp)
      have h2 := hFW.1 (ec.2, 104) (by simp)
      exact ⟨R16Shards.ivlUnhit_of_frameOutside ⟨h1.2.1, h1.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h1.1)),
             R16Shards.ivlUnhit_of_frameOutside ⟨h2.2.1, h2.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h2.1))⟩

private theorem warm_address_keep32_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address)
      = (some (.returned v), post)) :
    memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
  have hb : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  have hu := eval_seq_htab_set_ev_slot_unhit_g10 s 168 (ofString "addr") v (by omega) hc hi
    (fun _ hIA => by
      have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
      exact (hIA.2.2.2.2.1 _ hhead).2.2.2.2.2.2.2.2.1)
    (by rw [← hb]; exact congrArg Prod.fst hr)
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hi.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hi.1.2 hFW0).1
  dsimp only at hb_ev
  have hev8 : globN s "ev" % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
  have hu_head := hu _ hhead_mem
  have ha8_32 : (globN s "ev" + 32) % 8 = 0 := by have := hev8; omega
  have hhi_32 : (globN s "ev", 280).1 + (globN s "ev", 280).2 ≤ 2 ^ 64 := hb_ev
  have hin_32 : (globN s "ev", 280).1 ≤ globN s "ev" + 32 ∧
      globN s "ev" + 32 + 8 ≤ (globN s "ev", 280).1 + (globN s "ev", 280).2 := by
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have := hb_ev
    show globN s "ev" + 40 ≤ globN s "ev" + 280
    omega
  have hmk := R16Shards.memW_eq_of_ivlUnhit hu_head.1 ha8_32 hhi_32 hin_32
  have hpost2 : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address)).2
      = post := by
    rw [hr]
  rw [← hpost2]
  exact hmk

private theorem epsA_warm_address_keep32_g10 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "warm_address") := by
  refine ⟨_, _, _, lookup_warm_address, ?_⟩
  intro F s hc hi hw hP hlookup hnt
  obtain ⟨params0, body0, rs0, hlk0, hs0⟩ := epsA_warm_address
  have hlk_eq := lookup_warm_address.symm.trans hlk0
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hb_eq, rfl⟩
  subst hb_eq
  have h := hs0 s hc hi hw hP hlookup hnt
  dsimp only at h ⊢
  refine ⟨fun v hv => ?_, h.2⟩
  obtain ⟨hIW, hch, hRle, hg, hReq⟩ := h.1 v hv
  have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address) =
      (some (.returned v), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address)).2) :=
    Prod.ext hv rfl
  exact ⟨hIW, hch, hRle, hg, hReq, warm_address_keep32_g10 s _ v hc hi hrun⟩

/-! ## 7. `op_delegatecall`: head-frame word stores -/

/-- One head-frame word store at `ev + off` with `off` outside the invariant-read offsets:
the stored state keeps `EvmInv`, the chain, `HeadMemChainWF`, and does not increase `evmR`. -/
private theorem headStore_pkg_g10 {F : Type} {t : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    (hi : EvmInv t) (hw : Group10.HeadMemChainWF t) (off : Nat) (hoff : off < 280)
    (hoff8 : off % 8 = 0)
    (hoffne : off ≠ 8 ∧ off ≠ 16 ∧ off ≠ 24 ∧ off ≠ 32 ∧ off ≠ 40 ∧ off ≠ 64 ∧ off ≠ 88 ∧
      off ≠ 112 ∧ off ≠ 136 ∧ off ≠ 144 ∧ off ≠ 168 ∧ off ≠ 176 ∧ off ≠ 192 ∧ off ≠ 216 ∧
      off ≠ 232) :
    let t' : PanSemStateFiniteExact 64 F :=
      { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w }
    EvmInv t' ∧ evmChain t' = evmChain t ∧ Group10.HeadMemChainWF t' ∧ evmR t' ≤ evmR t := by
  dsimp only
  let t' : PanSemStateFiniteExact 64 F :=
    { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w }
  have hmem_out : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN t "ev" + off) →
      t'.memory x = t.memory x := by
    intro x hx
    simp only [t', R14Shards.OpHandlersA.updW]
    exact if_neg hx
  have hGp : GuestInv t' := guestInv_congr (s := t) (t := t') rfl rfl rfl rfl hi.1.1
  obtain ⟨hInv1, hch1, hR1⟩ := evmInv_of_head_off_store_g10 hi hGp rfl rfl hoff hoff8 hoffne
    hmem_out
  refine ⟨hInv1, hch1, ?_, le_of_eq hR1⟩
  have hb := evmInv_head_ev_bounds_g10 hi
  have hx_safe : HeadSafeAddr (globN t "ev") (globN t "cur_cont")
      (BitVec.ofNat 64 (globN t "ev" + off)).toNat := by
    refine Or.inl ⟨off, ?_, hoff, hoffne.2.2.1, hoffne.2.2.2.1, hoffne.2.2.2.2.1⟩
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  exact headMemChainWF_store_headSafe hi hw hx_safe rfl hch1 hmem_out

/-- The stored state's pending memory-expansion record: a head-frame store at `ev + off`
with `off ≠ 32` never touches the `ev+32` memory word. -/
private theorem mel_store_keep_g10 {F : Type} {t : PanSemStateFiniteExact 64 F} {w : BitVec 64}
    {off : Nat} (hi : EvmInv t) (hoff : off ≠ 32) (hoff280 : off < 280)
    (hp : MemoryExpansionLocal_g10 t) :
    let t' : PanSemStateFiniteExact 64 F :=
      { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w }
    MemoryExpansionLocal_g10 t' := by
  dsimp only
  refine memoryExpansionLocal_transport_g10 hp rfl rfl ?_
  let t' : PanSemStateFiniteExact 64 F :=
    { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w }
  show memW t' (globN t "ev" + 32) = memW t (globN t "ev" + 32)
  simp only [t', memW, R14Shards.OpHandlersA.updW]
  split
  · rename_i hcon
    exfalso
    have hnat := congrArg BitVec.toNat hcon
    simp only [BitVec.toNat_ofNat] at hnat
    have hb := evmInv_head_ev_bounds_g10 hi
    omega
  · rfl

/-! ## 8. `op_delegatecall`: the charged suffix walk (ccA) -/

/-- The suffix tail: everything after the `mcg` call. -/
theorem delegatecallSuffixTail_ccA_g10 {F : Type}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    ChildContinuationA (F := F) MemoryExpansionLocal_g10 delegatecallChargedSuffixTail_g10 := by
  let _ := hW
  refine ccA_seq_call_g10 (Q := MemoryExpansionLocal_g10) epsA_charge_gas_exact_keep32_g10
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values body callee rs v cpost _ _ hp _ _ _ hq => ?_) ?_
  · obtain ⟨amtV, _, hglob, _, hmk⟩ := hq
    have hglob' : cpost.globals = t.globals := hglob
    exact mel_seq_call_resume_keep32_g10 hp hglob' hmk
  · refine ccA_store_ev_off_g10 (Q := MemoryExpansionLocal_g10) (by omega)
      (fun t v _ hv => eval_op_word_g10 hv) ?_ ?_
    · intro t w hw_ev hi hw hp
      obtain ⟨hInv1, hch1, hWF1, hRle⟩ := headStore_pkg_g10 (w := w) hi hw 184 (by omega) (by omega)
        (by decide)
      exact ⟨hInv1, hWF1, hch1, hRle, mel_store_keep_g10 hi (by decide) (by omega) hp⟩
    · refine ccA_seq_call_g10 (Q := fun _ => True) epsA_extend_memory
        (fun t values body callee rs hc hi hw hp ha hl =>
          memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
      refine ccA_dec_g10 (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_
      refine ccA_store_ev_off_g10 (Q := fun _ => True) (by omega) (fun t v _ hv => ?_) ?_ ?_
      · simp only [evalHOLExact] at hv
        exact ⟨0#64, (Option.some.inj hv).symm⟩
      · intro t w hw_ev hi hw hp
        obtain ⟨hInv1, hch1, hWF1, hRle⟩ := headStore_pkg_g10 (w := w) hi hw 72 (by omega) (by omega)
          (by decide)
        exact ⟨hInv1, hWF1, hch1, hRle, trivial⟩
      · refine ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
          (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
        refine ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
          (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
        refine ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
          (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
        refine ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
          (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
        refine ccA_decCall_g10 (Q := fun _ => True) hgc
          (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
        refine ccA_seq_ite_g10 ?_ ?_
        · intro t w hv hw0
          exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
            (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
            (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))
        · intro t hv
          exact ccA_seq_skip_g10 (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))

/-- The `op_delegatecall` charged suffix: the `mcg` call followed by the tail. -/
theorem delegatecallSuffix_ccA_g10 {F : Type}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    ChildContinuationA (F := F) MemoryExpansionLocal_g10 delegatecallChargedSuffix_g10 := by
  have hsfx_eq : delegatecallChargedSuffix_g10 =
      .decCall (ofString "mcg") (.comb [.one, .one]) (ofString "calculate_message_call_gas")
        [.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64],
         .var .local (ofString "gw"),
         .load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
         .const 0#64, .const 0#64]
        delegatecallChargedSuffixTail_g10 := rfl
  rw [hsfx_eq]
  refine ccA_decCall_g10 (Q := MemoryExpansionLocal_g10)
    epsA_calculate_message_call_gas
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t values body callee rs v cpost _ _ hp _ _ _ _ _ hq =>
      memoryExpansionLocal_bind_ro_g10 hp hq (ofString "mcg") v (by decide))
    (delegatecallSuffixTail_ccA_g10 hW hgc)

/-! ## 9. `op_delegatecall`: the prefix walk -/

/-- The full `op_delegatecall` body walk. -/
theorem op_delegatecall_run_full_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun _ => True) false
      (sourceFnBody Guest.Software.guestFn_op_delegatecall) := by
  have hsuffix : HandlerRunA s0 MemoryExpansionLocal_g10 true delegatecallChargedSuffix_g10 :=
    handlerRunA_of_childContinuation_g10 s0 MemoryExpansionLocal_g10
      delegatecallChargedSuffix_g10 (delegatecallSuffix_ccA_g10 hW hgc)
  -- nodes 1-7: stack pops and `to_address_masked`, all with `P = Q = True`
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_to_address_masked
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  -- node 8: `msg` dec
  apply HandlerRunA.dec_simple
  -- node 9: `x = extend_memory_cost2`, `Q := MemoryExpansionLocal_g10`
  apply HandlerRunA.decCall (Q := MemoryExpansionLocal_g10) epsA_extend_memory_cost2
  · intros; trivial
  · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
    obtain ⟨hlf, cw, ebw, hv_eq, hbound⟩ := hq
    refine ⟨cw, ebw, ?_, ?_⟩
    · rw [hv_eq]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rcases hbound with h0 | ⟨h1a, h1b⟩
      · exact Or.inl h0
      · have hg_eq : globN (setVarHOLFinite (ofString "x") v { cpost with locals := t.locals }) "ev" =
            globN (callEntryStateHOLFinite t callee) "ev" := by
          change globN cpost "ev" = globN (callEntryStateHOLFinite t callee) "ev"
          unfold globN
          rw [congrArg PanSemStateFiniteExact.globals hlf]
        have hm_eq : memW (setVarHOLFinite (ofString "x") v { cpost with locals := t.locals })
            (globN (callEntryStateHOLFinite t callee) "ev" + 32) =
            memW (callEntryStateHOLFinite t callee)
              (globN (callEntryStateHOLFinite t callee) "ev" + 32) := by
          change memW cpost _ = memW (callEntryStateHOLFinite t callee) _
          unfold memW
          rw [congrArg PanSemStateFiniteExact.memory hlf]
        rw [hg_eq, hm_eq]
        exact Or.inr ⟨h1a, h1b⟩
  · -- node 10: `warm = is_warm_address`, `Q := MemoryExpansionLocal_g10`
    apply HandlerRunA.decCall (Q := MemoryExpansionLocal_g10) epsA_is_warm_address
    · intros; trivial
    · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
      have hlf : LocFrame t cpost := hq
      exact memoryExpansionLocal_bind_ro_g10 hp hlf (ofString "warm") v (by decide)
    · -- node 11: `access_cost` dec 100
      apply HandlerRunA.dec (Q := fun s => MemoryExpansionLocal_g10 s ∧
        PositiveCostLocal_g10 (ofString "access_cost") s)
      · intro t v hv hi hp
        have hv100 : v = .val (.word 100#64) := by
          change some (ValueHOL.val (.word 100#64)) = some v at hv
          exact (Option.some.inj hv).symm
        refine ⟨mel_setVar_keep_g10 hp (ofString "access_cost") v (by decide), ?_⟩
        rw [hv100]
        exact bound_cost_local_positive_g10 t (ofString "access_cost") 100#64 (by decide)
      · -- node 12: the `access_cost` override `ite`
        refine HandlerRunA.seq_ite_branch
          (R := fun s => MemoryExpansionLocal_g10 s ∧
            PositiveCostLocal_g10 (ofString "access_cost") s)
          (fun hcont _ _ _ _ => ?_)
          (fun hcont _ _ => HandlerRunA.seq_skip hcont)
          ?_
        · refine HandlerRunA.seq_assign_local (Q := fun s => MemoryExpansionLocal_g10 s ∧
            PositiveCostLocal_g10 (ofString "access_cost") s) ?_ hcont
          intro t' v' hv' hi' hp'
          have hv3000 : v' = .val (.word 3000#64) := by
            change some (ValueHOL.val (.word 3000#64)) = some v' at hv'
            exact (Option.some.inj hv').symm
          refine ⟨mel_setKvar_keep_g10 hp'.1 (ofString "access_cost") v' (by decide), ?_⟩
          rw [hv3000]
          exact posCost_setKvar_g10 t' (ofString "access_cost") 3000#64 (by decide)
        · -- node 13: `need = add_sat [access_cost, x.0]`
          apply HandlerRunA.decCall (Q := fun s => PositiveCostLocal_g10 (ofString "need") s ∧
            MemoryExpansionLocal_g10 s) epsA_add_sat_ge_g10
          · intros; trivial
          · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
            obtain ⟨hlf, aw, rw, hca_aw, hve, hle⟩ := hq
            obtain ⟨acw, hloc_ac, hpos_ac⟩ := hp.2
            have hca1 : callee.lookup (ofString "a") = some (.val (.word aw)) := hca_aw
            obtain ⟨_, _, w1, w2, hvals, hca_w1, _⟩ :=
              two_word_arg_lookup (by decide) lookup_add_sat hl
            have haw : aw = w1 := by
              have h3 : some (ValueHOL.val (.word aw)) = some (ValueHOL.val (.word w1)) :=
                hca1.symm.trans hca_w1
              injection h3 with h4
              injection h4 with h5
              injection h5 with h6
            have hw1acw : w1 = acw := by
              have harg0 : evalListHOLFinite t
                  (h := fun a => Classical.propDecidable (t.memaddrs a))
                  [.var .local (ofString "access_cost"),
                    .rfield 0 (.var .local (ofString "x"))] =
                some [.val (.word w1), .val (.word w2)] := by
                rw [← hvals]
                exact hargs
              rw [evalListHOLFinite_eq_toExact] at harg0
              rcases hx2 : (@evalHOLExact 64 F _ t.toExact
                  (fun a => Classical.propDecidable (t.memaddrs a))
                  (.rfield 0 (.var .local (ofString "x")))) with _ | xv
              · simp [evalListHOLExact, hx2] at harg0
              · have hac_ev : @evalHOLExact 64 F _ t.toExact
                    (fun a => Classical.propDecidable (t.memaddrs a))
                    (.var .local (ofString "access_cost")) = some (.val (.word acw)) := hloc_ac
                simp only [evalListHOLExact, hac_ev, hx2] at harg0
                injection (Option.some.inj harg0) with hhead _
                injection hhead with hh2
                injection hh2 with hh3
                exact hh3.symm
            have hawle : aw.toNat ≤ rw.toNat := BitVec.le_def.mp hle
            have hrwpos : 0 < rw.toNat := by
              have e1 : acw.toNat = w1.toNat := congrArg BitVec.toNat hw1acw.symm
              have e2 : w1.toNat = aw.toNat := congrArg BitVec.toNat haw.symm
              omega
            refine ⟨⟨rw, ?_, hrwpos⟩, ?_⟩
            · rw [hve]
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · have hlf' : LocFrame t cpost := hlf
              exact memoryExpansionLocal_bind_ro_g10 hp.1 hlf' (ofString "need") v (by decide)
          · -- node 14: `charge_gas [need]` — flips the charged flag
            apply charge_positive_local_memory_sequence_g10 s0 (ofString "need") false
            -- node 15: the `warm_address` `ite`
            refine HandlerRunA.seq_ite_branch
              (R := fun s => PositiveCostLocal_g10 (ofString "need") s ∧
                MemoryExpansionLocal_g10 s)
              (fun hcont _ _ _ _ => ?_)
              (fun hcont _ _ => HandlerRunA.seq_skip hcont)
              ?_
            · refine HandlerRunA.seq_call epsA_warm_address_keep32_g10
                (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ hcont
              intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
              obtain ⟨hg, _, hmk⟩ := hq
              have hge := globN_resume_eq_g10 callee hch
              refine ⟨hp.1, memoryExpansionLocal_transport_g10 hp.2 rfl hge hmk⟩
            · -- node 16: `dl = calculate_delegation_cost [code_address0]`
              apply HandlerRunA.decCall (Q := fun s => DlPreG10 s ∧ MemoryExpansionLocal_g10 s)
                (epsA_calculate_delegation_cost_g10 hW)
              · intros; trivial
              · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
                obtain ⟨hR, hmk, d0, d1, d2, hv_eq, h1, h2⟩ := hq
                refine ⟨⟨d0, d1, d2, ?_, h1, h2⟩, ?_⟩
                · rw [hv_eq]
                  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                · exact mel_resume_keep32_g10 callee hp.2 hch hmk (ofString "dl") v (by decide)
              · -- node 17: `code_address` dec
                apply HandlerRunA.dec (Q := fun s => DlPreG10 s ∧ MemoryExpansionLocal_g10 s)
                · intro t v hv hi hp
                  exact ⟨dlPre_setVar_g10 hp.1 (by decide),
                    mel_setVar_keep_g10 hp.2 (ofString "code_address") v (by decide)⟩
                · -- node 18: the delegation-cost `ite`
                  refine HandlerRunA.seq_ite_branch
                    (R := fun s => DlPreG10 s ∧ MemoryExpansionLocal_g10 s)
                    (fun hcont _ _ _ _ => ?_)
                    (fun hcont _ _ => HandlerRunA.seq_skip hcont)
                    ?_
                  · refine HandlerRunA.seq_assoc ?_
                    refine HandlerRunA.seq_call (Q := fun s => DlPreG10 s ∧ MemoryExpansionLocal_g10 s)
                      epsA_charge_gas_exact_keep32_g10
                      (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ ?_
                    · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
                      obtain ⟨amtV, _, hglob, _, hmk⟩ := hq
                      have hglob' : cpost.globals = t.globals := hglob
                      exact ⟨dlPre_locals_keep_g10 hp.1,
                        mel_seq_call_resume_keep32_g10 hp.2 hglob' hmk⟩
                    · refine HandlerRunA.seq_call epsA_warm_address_keep32_g10
                        (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_ hcont
                      intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp hch hq
                      obtain ⟨hg, _, hmk⟩ := hq
                      have hge := globN_resume_eq_g10 callee hch
                      exact ⟨dlPre_locals_keep_g10 hp.1,
                        memoryExpansionLocal_transport_g10 hp.2 rfl hge hmk⟩
                  · -- node 19: `code = ext_code_of [code_address]`
                    apply HandlerRunA.decCall (Q := fun s => DlPreG10 s ∧
                      MemoryExpansionLocal_g10 s) hW.epsA_ext_code_of
                    · intros; trivial
                    · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp
                        hch hq
                      obtain ⟨_, _, hmk⟩ := hq
                      exact ⟨dlPre_setVar_g10 hp.1 (by decide),
                        mel_resume_keep32_g10 callee hp.2 hch hmk (ofString "code") v
                          (by decide)⟩
                    · -- node 20: `gw = sat_word [gasv]`, then the charged suffix
                      apply HandlerRunA.decCall (Q := MemoryExpansionLocal_g10) epsA_sat_word
                      · intros; trivial
                      · intro t values body callee rs v cpost hi hw hp hargs hl hi_cp hw_cp
                          hch hq
                        have hlf : LocFrame t cpost := hq
                        exact memoryExpansionLocal_bind_ro_g10 hp.2 hlf (ofString "gw") v
                          (by decide)
                      · exact hsuffix

/-! ## 10. `op_delegatecall`: the aligned spec -/

theorem op_delegatecall_specA_g10 (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerSpecA (ofString "op_delegatecall") := by
  refine opHandlerSpecA_of_run 605 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_delegatecall rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_delegatecall_run_full_g10 s0 hW hgc

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
