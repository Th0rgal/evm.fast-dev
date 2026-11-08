import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Router
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group06Stack

/-! # Aligned Cutover `op_dispatch` Router (`OpDispatchAlignedSpec`)

Range-aware aligned router for `guestFn_op_dispatch`:
- Tracks the `op` lower bound along `dispatchCode`'s fall-through spine (`0 -> 32 -> 96 -> 160`)
  so that:
  - `op == 95` calls `op_push [0#64]` with `nbytes = 0#64` (`0 ≤ 32`),
  - `96 ≤ op < 128` calls `op_push [op - 95#64]` with `nbytes.toNat ≤ 32`,
  - `160 ≤ op < 165` calls `op_log [op - 160#64]` with `ntopics.toNat ≤ 4`.
- Wires all 19 remaining A-side handlers (`Group05bEnv` + `Group06Stack` including
  `op_push_bounded_spec`) plus `op_extcodecopy` into `OpDispatchAlignedSpec`, shrinking
  the remaining aligned handler bundle to bounded `op_log` (`ntopics ≤ 4`) and the 6
  call/create opcodes (80 of 87 handlers closed under `WorldAccountSpecs` + `ExtCodeOfHeadSpec`).
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterAligned
open InitECandidate.Solver.Wave8Contracts.M23

theorem lookup_op_log_cutover :
    originalRuntimeCode.lookup (ofString "op_log") =
      some ([(ofString "ntopics", .one)], sourceFnBody Guest.Software.guestFn_op_log, .one) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 524 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_log) rfl

theorem op_dispatch_param_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {body : ProgHOL 64} {retShape : ShapeHOL}
    (hex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "op_dispatch") vals =
      some (body, s.locals, retShape)) :
    ∃ opw : BitVec 64, s.locals.lookup (ofString "op") = some (.val (.word opw)) := by
  obtain ⟨vals, hl⟩ := hex
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "op_dispatch") vals body s.locals retShape hl
  have hfn : originalRuntimeCode.lookup (ofString "op_dispatch") =
      some ([(ofString "op", .one)], dispatchCode, .one) := lookup_op_dispatch
  simp only [Flapjack.lookupCodeHOLExact, hfn] at hx
  rcases vals with _ | ⟨v0, _ | _⟩
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hsh : shapeEqHOL .one (shapeOfHOLExact v0) = true := by simpa [List.map] using hcond
      rcases v0 with ⟨⟨opw⟩⟩ | _ | _
      · refine ⟨opw, ?_⟩
        have hfn' := congrFun hloc.symm (ofString "op")
        simpa [FUPDATE_LIST, FUPDATE] using hfn'
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh
    · cases hx
  · simp at hx

theorem cmp_lower_op_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    {opw k : BitVec 64}
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "op")) (.const k)) =
      some (.val (.word (if opw < k then 1 else 0))) := by
  simp [evalHOLExact, hop, wordCmpHOL]

theorem ite_then_never_none_skip {F : Type}
    (s : PanSemStateFiniteExact 64 F) {opw k : BitVec 64}
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw)))
    {thenBr : ProgHOL 64}
    (hnn : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t thenBr).1 ≠ none) :
    (evaluateHOLFiniteState s
      (.ite (.cmp .lower (.var .local (ofString "op")) (.const k)) thenBr .skip)).1 = none →
    (evaluateHOLFiniteState s
      (.ite (.cmp .lower (.var .local (ofString "op")) (.const k)) thenBr .skip)).2 = s ∧
    k.toNat ≤ opw.toNat := by
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop]
  dsimp only
  by_cases hlt : opw < k
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10]
    intro hn
    exact (hnn s hn).elim
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    intro _
    exact ⟨rfl, by simp only [BitVec.lt_def, Nat.not_lt] at hlt; exact hlt⟩

theorem seq_raise_never_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) (nm : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p (.raise nm e))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s p with ⟨r, mid⟩
  cases r with
  | none => exact raise_ne_none mid nm e
  | some _ => simp

theorem body578_302_never_none {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p1 p2 p3 : ProgHOL 64) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 (.return e))))).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 with
  | some _ => simp
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr2 : evaluateHOLFiniteState s1 p2 with ⟨r2, s2⟩
    cases r2 with
    | some _ => simp
    | none => exact seq_return_ne_none s2 p3 e

theorem push_arg_sub95_le_32 {opw : BitVec 64}
    (hlo : 96 ≤ opw.toNat) (hhi : opw.toNat < 128) :
    (opw - 95#64).toNat ≤ 32 := by
  have hsub : (opw - 95#64).toNat = opw.toNat - 95 := by
    have h95 : (95#64 : BitVec 64).toNat = 95 := rfl
    rw [BitVec.toNat_sub_of_le]
    · rw [h95]
    · simp only [BitVec.le_def, h95]; omega
  omega

theorem log_arg_sub160_le_4 {opw : BitVec 64}
    (hlo : 160 ≤ opw.toNat) (hhi : opw.toNat < 165) :
    (opw - 160#64).toNat ≤ 4 := by
  have hsub : (opw - 160#64).toNat = opw.toNat - 160 := by
    have h160 : (160#64 : BitVec 64).toNat = 160 := rfl
    rw [BitVec.toNat_sub_of_le]
    · rw [h160]
    · simp only [BitVec.le_def, h160]; omega
  omega

theorem evalList_sub_op_const {F : Type} (s : PanSemStateFiniteExact 64 F)
    {opw k : BitVec 64}
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw))) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .sub [.var .local (ofString "op"), .const k]] =
      some [.val (.word (opw - k))] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact, evalHOLExact, hop, valueIsWord, valueWord, wordOpHOL, wordOp]

/-- Bounded `op_push` contract under `EvmRun ∧ HeadMemAligned`. Discharged unconditionally
by `Group06Stack2.op_push_bounded_spec`. -/
def OpPushBoundedAlignedSpec : Prop :=
  FunSpec
    (fun s => (EvmRun s ∧ HeadMemAligned s) ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nbytes") = some (.val (.word n)) ∧ n.toNat ≤ 32)
    OpDispatchPost
    (ofString "op_push")

theorem op_push_bounded_aligned_spec : OpPushBoundedAlignedSpec := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := op_push_bounded_spec
  exact ⟨params, body, retShape, hlk, fun s hc ⟨hRun, hnb⟩ hex hnt =>
    hspec s hc ⟨hRun.1, hnb⟩ hex hnt⟩

/-- Bounded `op_log` contract (`ntopics ≤ 4`) under `EvmRun ∧ HeadMemAligned`. -/
def OpLogBoundedAlignedSpec : Prop :=
  FunSpec
    (fun s => (EvmRun s ∧ HeadMemAligned s) ∧
      ∃ nt : BitVec 64, s.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
    OpDispatchPost
    (ofString "op_log")

/-- Remaining 7 B-side obligations for `OpDispatchAlignedSpec` after wiring `Group05bEnv`,
`Group06Stack` (including bounded `op_push`), and `op_extcodecopy`: bounded `op_log` (`ntopics ≤ 4`)
plus the 6 call/create opcodes. -/
structure RemainingCallCreateLogAlignedSpecs : Prop where
  op_log : OpLogBoundedAlignedSpec
  op_create : OpHandlerSpecA (ofString "op_create")
  op_call : OpHandlerSpecA (ofString "op_call")
  op_callcode : OpHandlerSpecA (ofString "op_callcode")
  op_delegatecall : OpHandlerSpecA (ofString "op_delegatecall")
  op_create2 : OpHandlerSpecA (ofString "op_create2")
  op_staticcall : OpHandlerSpecA (ofString "op_staticcall")

private theorem callReturnA_one_word_bounded
    {fname paramName : MlS} {bound : Nat} {argExp : ExpHOL 64}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hf : FunSpec
      (fun s => (EvmRun s ∧ HeadMemAligned s) ∧
        ∃ w : BitVec 64, s.locals.lookup paramName = some (.val (.word w)) ∧ w.toNat ≤ bound)
      OpDispatchPost fname)
    (hlk_param : ∃ fbody, originalRuntimeCode.lookup fname = some ([(paramName, .one)], fbody, .one))
    (harg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∃ w : BitVec 64,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] =
          some [.val (.word w)] ∧
        w.toNat ≤ bound) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      (EvmRun s ∧ HeadMemAligned s) → P s →
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1 ≠
        some .timeOut →
      OpDispatchPost s
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).2 := by
  intro F s hcode hRun hPs hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  obtain ⟨fbody, hlk_exact⟩ := hlk_param
  obtain ⟨argw, harg_ev, harg_le⟩ := harg s hPs
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rw [harg_ev] at hnt ⊢; dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname [.val (.word argw)] with _ | ⟨body', callee, ret'⟩
  · exact opDispatchPost_error s s
  · simp only [hl] at hnt ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · simp only [hz, ↓reduceIte] at hnt ⊢
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname [.val (.word argw)] =
          some (body', callee, ret') := by rwa [← hcode]
      obtain ⟨hbf, hret1, w', hw_eq, hcal_lk⟩ :=
        R14Shards.OpHandlersA.one_word_arg_lookup hlk_exact hl_orig
      injection hw_eq with hw1; injection hw1 with hw2; subst hw2
      have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
      have hce_pre : (EvmRun (callEntryStateHOLFinite s callee) ∧
          HeadMemAligned (callEntryStateHOLFinite s callee)) ∧
          ∃ w : BitVec 64, (callEntryStateHOLFinite s callee).locals.lookup paramName =
            some (.val (.word w)) ∧ w.toNat ≤ bound :=
        ⟨⟨evmRun_callEntry s callee hRun.1, headMemAligned_callEntry s callee hRun.2⟩,
         argw, hcal_lk, harg_le⟩
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
      simp only [hrun] at hnt ⊢
      have hQ (hsafe : res ≠ some .timeOut) :
          OpDispatchPost (callEntryStateHOLFinite s callee) res cpost := by
        have hbody : body' = body :=
          lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
            retShape ret' [.val (.word argw)] callee (by rw [hcode]; exact hlook) hl
        have hret : ret' = retShape := by
          have hlk_eq : some ([(paramName, ShapeHOL.one)], fbody, ShapeHOL.one) =
              some (params, body, retShape) := hlk_exact.symm.trans hlook
          injection hlk_eq with hp1
          rcases Prod.mk.inj hp1 with ⟨_, hp2⟩
          exact hret1.trans (Prod.mk.inj hp2).2
        have hce_ex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
            some (body, (callEntryStateHOLFinite s callee).locals, retShape) := by
          refine ⟨[.val (.word argw)], ?_⟩
          rwa [← hbody, ← hret]
        have hrun_b : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (res, cpost) := by
          rwa [← hbody]
        have hsp := hspec (callEntryStateHOLFinite s callee) hce_code hce_pre hce_ex
          (by rw [hrun_b]; exact hsafe)
        rw [hrun_b] at hsp
        exact hsp
      cases res with
      | none => exact opDispatchPost_error s cpost
      | some r0 =>
        cases r0 with
        | returned v =>
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
          · simp only [hsh, ↓reduceIte]
            exact RouterAligned.return_const0_post (hQ (by simp))
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
            exact opDispatchPost_error s cpost
        | timeOut => simp at hnt
        | exception eid ev => exact RouterAligned.call_exception_post (hQ (by simp))
        | «break» => exact opDispatchPost_error s cpost
        | «continue» => exact opDispatchPost_error s cpost
        | finalFfi f =>
          refine opDispatchPost_other (s := s) (t := cpost.emptyLocalsHOLFinite)
            (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
          rintro ⟨_, h⟩; cases h
        | error => exact opDispatchPost_error s cpost.emptyLocalsHOLFinite

private theorem push0_walkA (h_push : OpPushBoundedAlignedSpec) :
    DispatchSpecWalkA (.seq (.call (some (none, none)) (ofString "op_push") [.const 0#64]) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  exact callReturnA_one_word_bounded (P := fun _ => True) h_push ⟨_, lookup_op_push⟩
    (fun _ _ => ⟨0#64, rfl, by decide⟩) s hcode hRun trivial hnt

private theorem opDispatchSpecGroupA08_bounded
    (h_op_jump : OpHandlerSpecA (ofString "op_jump"))
    (h_op_jumpi : OpHandlerSpecA (ofString "op_jumpi"))
    (h_op_pc : OpHandlerSpecA (ofString "op_pc"))
    (h_op_msize : OpHandlerSpecA (ofString "op_msize"))
    (h_op_gas : OpHandlerSpecA (ofString "op_gas"))
    (h_op_jumpdest : OpHandlerSpecA (ofString "op_jumpdest"))
    (h_op_tload : OpHandlerSpecA (ofString "op_tload"))
    (h_op_tstore : OpHandlerSpecA (ofString "op_tstore"))
    (h_op_mcopy : OpHandlerSpecA (ofString "op_mcopy"))
    (h_op_push : OpPushBoundedAlignedSpec) :
    DispatchSpecWalkA dispatchGroup08 := by
  exact
    DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jump _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jumpi _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_pc _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_msize _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_gas _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_jumpdest _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_tload _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_tstore _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn h_op_mcopy _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.ite _ (push0_walkA h_op_push) DispatchSpecWalkA.skip)))))))))

private theorem ite_push_sub95_walkA
    (h_op_push : OpPushBoundedAlignedSpec)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmRun s ∧ HeadMemAligned s)
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw)))
    (hlo : 96 ≤ opw.toNat)
    {p_push : ProgHOL 64}
    (hp_eq : p_push = .ite (.cmp .lower (.var .local (ofString "op")) (.const 128#64))
      (.seq (.call (some (none, none)) (ofString "op_push")
        [.op .sub [.var .local (ofString "op"), .const 95#64]]) (.return (.const 0)))
      .skip)
    (hnt : (evaluateHOLFiniteState s p_push).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s p_push).1 = none →
      (evaluateHOLFiniteState s p_push).2 = s) ∧
    ((evaluateHOLFiniteState s p_push).1 ≠ none →
      OpDispatchPost s (evaluateHOLFiniteState s p_push).1 (evaluateHOLFiniteState s p_push).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 128#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 128 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnA_one_word_bounded
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_push ⟨_, lookup_op_push⟩
      (fun t htop => ⟨opw - 95#64, evalList_sub_op_const t htop, push_arg_sub95_le_32 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem ite_log_sub160_walkA
    (h_op_log : OpLogBoundedAlignedSpec)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmRun s ∧ HeadMemAligned s)
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw)))
    (hlo : 160 ≤ opw.toNat)
    {p_log : ProgHOL 64}
    (hp_eq : p_log = .ite (.cmp .lower (.var .local (ofString "op")) (.const 165#64))
      (.seq (.call (some (none, none)) (ofString "op_log")
        [.op .sub [.var .local (ofString "op"), .const 160#64]]) (.return (.const 0)))
      .skip)
    (hnt : (evaluateHOLFiniteState s p_log).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s p_log).1 = none →
      (evaluateHOLFiniteState s p_log).2 = s) ∧
    ((evaluateHOLFiniteState s p_log).1 ≠ none →
      OpDispatchPost s (evaluateHOLFiniteState s p_log).1 (evaluateHOLFiniteState s p_log).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 165#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 165 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnA_one_word_bounded
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_log ⟨_, lookup_op_log_cutover⟩
      (fun t htop => ⟨opw - 160#64, evalList_sub_op_const t htop, log_arg_sub160_le_4 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem walk_group01_to_03 : DispatchSpecWalkA (binaryAt [0] dispatchCode) :=
  DispatchSpecWalkA.ite _
    (DispatchSpecWalkA.seq
      (DispatchSpecWalkA.ite _
        (opDispatchSpecGroupA01
          (opHandlerSpecA_of op_stop_spec) (opHandlerSpecA_of op_add_spec)
          (opHandlerSpecA_of op_mul_spec) (opHandlerSpecA_of op_sub_spec)
          (opHandlerSpecA_of op_div_spec) (opHandlerSpecA_of op_sdiv_spec)
          (opHandlerSpecA_of op_mod_spec) (opHandlerSpecA_of op_smod_spec)
          (opHandlerSpecA_of op_addmod_spec) (opHandlerSpecA_of op_mulmod_spec)
          (opHandlerSpecA_of op_exp_spec) (opHandlerSpecA_of op_signextend_spec))
        (opDispatchSpecGroupA02
          (opHandlerSpecA_of op_lt_spec) (opHandlerSpecA_of op_gt_spec)
          (opHandlerSpecA_of op_slt_spec) (opHandlerSpecA_of op_sgt_spec)
          (opHandlerSpecA_of op_eq_spec) (opHandlerSpecA_of op_iszero_spec)
          (opDispatchSpecGroupA03
            (opHandlerSpecA_of op_and_spec) (opHandlerSpecA_of op_or_spec)
            (opHandlerSpecA_of op_xor_spec) (opHandlerSpecA_of op_not_spec)
            (opHandlerSpecA_of op_byte_spec) (opHandlerSpecA_of op_shl_spec)
            (opHandlerSpecA_of op_shr_spec) (opHandlerSpecA_of op_sar_spec)
            (opHandlerSpecA_of op_clz_spec))))
      (DispatchSpecWalkA.raise _))
    DispatchSpecWalkA.skip

private theorem walk_group04_to_08 (hW : WorldAccountSpecs) (hext : ExtCodeOfHeadSpec) :
    DispatchSpecWalkA (binaryAt [1, 0] dispatchCode) :=
  DispatchSpecWalkA.ite _
    (DispatchSpecWalkA.seq
      (DispatchSpecWalkA.ite _
        (opDispatchSpecGroupA04
          op_keccak_aligned_spec (opHandlerSpecA_of op_address_spec)
          (opHandlerSpecA_of (op_balance_spec hW)) (opHandlerSpecA_of op_origin_spec)
          (opHandlerSpecA_of op_caller_spec) (opHandlerSpecA_of op_callvalue_spec)
          (opHandlerSpecA_of op_calldataload_spec) (opHandlerSpecA_of op_calldatasize_spec)
          op_calldatacopy_aligned_spec
          (opDispatchSpecGroupA05
            (opHandlerSpecA_of op_codesize_spec) op_codecopy_aligned_spec
            (opHandlerSpecA_of op_gasprice_spec) (opHandlerSpecA_of (op_extcodesize_spec hW))
            (op_extcodecopy_aligned_spec hext)
            (opHandlerSpecA_of op_returndatasize_spec) op_returndatacopy_aligned_spec
            (opHandlerSpecA_of (op_extcodehash_spec hW))))
        (opDispatchSpecGroupA06
          (opHandlerSpecA_of op_blockhash_spec) (opHandlerSpecA_of op_coinbase_spec)
          (opHandlerSpecA_of op_timestamp_spec) (opHandlerSpecA_of op_number_spec)
          (opHandlerSpecA_of op_prevrandao_spec) (opHandlerSpecA_of op_gaslimit_spec)
          (opHandlerSpecA_of op_chainid_spec) (opHandlerSpecA_of (op_selfbalance_spec hW))
          (opHandlerSpecA_of op_basefee_spec) (opHandlerSpecA_of op_blobhash_spec)
          (opHandlerSpecA_of op_blobbasefee_spec) (opHandlerSpecA_of op_slotnum_spec)
          (opDispatchSpecGroupA07
            (opHandlerSpecA_of op_pop_spec) op_mload_aligned_spec
            op_mstore_aligned_spec op_mstore8_aligned_spec
            (opHandlerSpecA_of (op_sload_spec hW)) (opHandlerSpecA_of (op_sstore_spec hW))
            (opDispatchSpecGroupA08_bounded
              (opHandlerSpecA_of op_jump_spec) (opHandlerSpecA_of op_jumpi_spec)
              (opHandlerSpecA_of op_pc_spec) (opHandlerSpecA_of op_msize_spec)
              (opHandlerSpecA_of op_gas_spec) (opHandlerSpecA_of op_jumpdest_spec)
              (opHandlerSpecA_of op_tload_spec) (opHandlerSpecA_of op_tstore_spec)
              op_mcopy_aligned_spec op_push_bounded_aligned_spec))))
      (DispatchSpecWalkA.raise _))
    DispatchSpecWalkA.skip

private theorem walk_after_log (hW : WorldAccountSpecs) (hrem : RemainingCallCreateLogAlignedSpecs) :
    DispatchSpecWalkA (binaryAt [1, 1, 1, 1] dispatchCode) :=
  DispatchSpecWalkA.seq
    (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn (opHandlerSpecA_of op_dupn_spec) _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.seq
      (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn (opHandlerSpecA_of op_swapn_spec) _) DispatchSpecWalkA.skip)
      (DispatchSpecWalkA.seq
        (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn (opHandlerSpecA_of op_exchange_spec) _) DispatchSpecWalkA.skip)
        (opDispatchSpecGroupA11
          hrem.op_create hrem.op_call hrem.op_callcode op_return_aligned_spec
          hrem.op_delegatecall hrem.op_create2 hrem.op_staticcall
          (opDispatchSpecGroupA12 op_revert_aligned_spec (opHandlerSpecA_of (op_selfdestruct_spec hW))))))

private theorem walk_dup_swap :
    DispatchSpecWalkA (binaryAt [1, 1, 0, 0, 1] dispatchCode) :=
  DispatchSpecWalkA.seq
    (DispatchSpecWalkA.ite _ (DispatchSpecWalkA.callReturn (opHandlerSpecA_of op_dup_spec) _) DispatchSpecWalkA.skip)
    (DispatchSpecWalkA.callReturn (opHandlerSpecA_of op_swap_spec) _)

private theorem dispatch_spine_decompose
    {p p0 p1 p2 p3 p4 : ProgHOL 64}
    (h0 : p = .seq p0 (.seq p1 (.seq p2 (.seq p3 p4)))) :
    p = .seq p0 (.seq p1 (.seq p2 (.seq p3 p4))) := h0

/-- Cutover aligned `op_dispatch` theorem: wires `Group05bEnv`, `Group06Stack` (including
bounded `op_push`), `StateAccountOps`, `Group08` (+ `op_extcodecopy` via `ExtCodeOfHeadSpec`),
and `Group09` (`op_return`, `op_revert`, `op_mcopy`), reducing `OpDispatchAlignedSpec` to
`WorldAccountSpecs`, `ExtCodeOfHeadSpec`, and `RemainingCallCreateLogAlignedSpecs` (80/87 closed). -/
theorem op_dispatch_aligned_spec_cutover
    (hW : WorldAccountSpecs)
    (hext : ExtCodeOfHeadSpec)
    (hrem : RemainingCallCreateLogAlignedSpecs) :
    OpDispatchAlignedSpec := by
  have hlk_disp : originalRuntimeCode.lookup (ofString "op_dispatch") =
      some ([(ofString "op", .one)], dispatchCode, .one) := lookup_op_dispatch
  refine ⟨_, _, _, hlk_disp, ?_⟩
  intro F s hcode hRun hex hnt
  obtain ⟨opw, hop⟩ := op_dispatch_param_word hex
  change OpDispatchPost s (evaluateHOLFiniteState s dispatchCode).1 (evaluateHOLFiniteState s dispatchCode).2
  let p0 := binaryAt [0] dispatchCode
  let p1 := binaryAt [1, 0] dispatchCode
  let p2 := binaryAt [1, 1, 0] dispatchCode
  let p3 := binaryAt [1, 1, 1, 0] dispatchCode
  let p4 := binaryAt [1, 1, 1, 1] dispatchCode
  have hspine : dispatchCode = .seq p0 (.seq p1 (.seq p2 (.seq p3 p4))) := rfl
  rw [hspine] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr0 : evaluateHOLFiniteState s p0 with ⟨r0, s1⟩
  simp only [hr0] at hnt ⊢
  cases r0 with
  | some _ =>
    have hw0 := walk_group01_to_03.run s hcode hRun (by rw [hr0]; exact hnt)
    rw [hr0] at hw0
    exact hw0.2 (by simp)
  | none =>
    have hs1 : s = s1 := by
      have hw0 := walk_group01_to_03.run s hcode hRun (by rw [hr0]; simp)
      rw [hr0] at hw0; exact (hw0.1 rfl).symm
    subst hs1
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s2⟩
    simp only [hr1] at hnt ⊢
    cases r1 with
    | some _ =>
      have hw1 := (walk_group04_to_08 hW hext).run s hcode hRun (by rw [hr1]; exact hnt)
      rw [hr1] at hw1
      exact hw1.2 (by simp)
    | none =>
      have hp1_shape : p1 = .ite (.cmp .lower (.var .local (ofString "op")) (.const 96#64))
          (.seq (binaryAt [1, 0, 0, 0] dispatchCode) (.raise (ofString "EvmErr") (.const 5)))
          .skip := rfl
      have hge96_pair : s2 = s ∧ 96 ≤ opw.toNat := by
        have h96 := ite_then_never_none_skip (k := 96#64) s hop
          (fun t => seq_raise_never_none t _ (ofString "EvmErr") (.const 5))
          (by rw [← hp1_shape, hr1])
        rwa [← hp1_shape, hr1] at h96
      obtain ⟨hs2, hge96⟩ := hge96_pair
      have hs2' : s = s2 := hs2.symm
      subst hs2'
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hr2 : evaluateHOLFiniteState s p2 with ⟨r2, s3⟩
      simp only [hr2] at hnt ⊢
      let p2_push := binaryAt [1, 1, 0, 0, 0] dispatchCode
      let p2_ds := binaryAt [1, 1, 0, 0, 1] dispatchCode
      have hp2_shape : p2 = .ite (.cmp .lower (.var .local (ofString "op")) (.const 160#64))
          (.seq p2_push p2_ds) .skip := rfl
      cases r2 with
      | some _ =>
        have hnt2 : (evaluateHOLFiniteState s p2).1 ≠ some .timeOut := by rw [hr2]; exact hnt
        have hgoal : OpDispatchPost s (evaluateHOLFiniteState s p2).1 (evaluateHOLFiniteState s p2).2 := by
          rw [hp2_shape, evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt2 hr2 ⊢
          dsimp only at hnt2 hr2 ⊢
          by_cases hlt160 : opw < 160#64
          · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            simp only [hlt160, ↓reduceIte, h10] at hnt2 hr2 ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hnt2 hr2 ⊢
            rcases hpush : evaluateHOLFiniteState s p2_push with ⟨rp, sp⟩
            simp only [hpush] at hnt2 hr2 ⊢
            cases rp with
            | some _ =>
              have hp := ite_push_sub95_walkA (p_push := p2_push)
                op_push_bounded_aligned_spec s hcode hRun hop hge96 rfl
                (by rw [hpush]; exact hnt2)
              rw [hpush] at hp
              exact hp.2 (by simp)
            | none =>
              have hp := ite_push_sub95_walkA (p_push := p2_push)
                op_push_bounded_aligned_spec s hcode hRun hop hge96 rfl
                (by rw [hpush]; simp)
              rw [hpush] at hp
              have hsp : s = sp := (hp.1 rfl).symm
              subst hsp
              dsimp only at hnt2 hr2 ⊢
              have hds := walk_dup_swap.run s hcode hRun hnt2
              exact hds.2 (by rw [hr2]; simp)
          · simp only [hlt160, ↓reduceIte] at hr2
            rw [evaluateHOLFiniteState_skip] at hr2
            cases hr2
        rwa [hr2] at hgoal
      | none =>
        have hp2_body_shape : ProgHOL.seq p2_push p2_ds =
            ProgHOL.seq p2_push (.seq (binaryAt [1, 1, 0, 0, 1, 0] dispatchCode)
              (.seq (.call (some (none, none)) (ofString "op_swap")
                [.op .sub [.var .local (ofString "op"), .const 143#64]]) (.return (.const 0)))) := rfl
        have hge160_pair : s3 = s ∧ 160 ≤ opw.toNat := by
          have h160 := ite_then_never_none_skip (k := 160#64) (thenBr := ProgHOL.seq p2_push p2_ds) s hop
            (fun t => by rw [hp2_body_shape]; exact body578_302_never_none t _ _ _ (.const 0))
            (by rw [← hp2_shape, hr2])
          rwa [← hp2_shape, hr2] at h160
        obtain ⟨hs3, hge160⟩ := hge160_pair
        have hs3' : s = s3 := hs3.symm
        subst hs3'
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hr3 : evaluateHOLFiniteState s p3 with ⟨r3, s4⟩
        simp only [hr3] at hnt ⊢
        cases r3 with
        | some _ =>
          have hlogw := ite_log_sub160_walkA (p_log := p3) hrem.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; exact hnt)
          rw [hr3] at hlogw
          exact hlogw.2 (by simp)
        | none =>
          have hlogw := ite_log_sub160_walkA (p_log := p3) hrem.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; simp)
          rw [hr3] at hlogw
          have hs4 : s = s4 := (hlogw.1 rfl).symm
          subst hs4
          dsimp only at hnt ⊢
          rcases hr4 : evaluateHOLFiniteState s p4 with ⟨r4, s5⟩
          cases r4 with
          | none =>
            exact opDispatchPost_other (by intro _ hv; cases hv) (by rintro ⟨_, hv⟩; cases hv)
          | some _ =>
            have hw4 := (walk_after_log hW hrem).run s hcode hRun hnt
            rw [hr4] at hw4
            exact hw4.2 (by simp)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
