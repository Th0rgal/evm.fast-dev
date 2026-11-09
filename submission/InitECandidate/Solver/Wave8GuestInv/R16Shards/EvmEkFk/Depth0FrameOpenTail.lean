import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4dSetCodeBounded

/-!
# Depth0 Frame-Open Tail (r26): top-level `set_code` contracts

Wraps the MsB4-series body-step (`set_code_bounded_body_step`) into the top-level
contracts consumed by the dispatch pipeline:
`funSpec_set_code_msgBounded` (FunSpec with entry `SetCodeReadyB`),
its `KeepsOn` corollary `fk_set_code_msgBounded`, and the `D0PreB`-level
Hoare call wrapper `hoare_d0PreB_call_set_code` (following the `MsB4c1`
`hoare_d0PreB_call_*` pattern).
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
  (IvlUnhit not_cellHits_of_disj memW_eq_of_ivlUnhit)
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-- Entry predicate for `set_code`: `EvmMsgReadyMsgBounded` plus three word params
`addr`, `code`, `code_len` with `code_len < 2^40` (the code-DB payload bound that
`set_code_bounded_body_step` preserves `CodeDbPayloadBoundedNz` under). -/
def SetCodeReadyB : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => EvmMsgReadyMsgBounded s ∧
    ∃ waddr wcode wcl : BitVec 64,
      s.locals.lookup (ofString "addr") = some (.val (.word waddr)) ∧
      s.locals.lookup (ofString "code") = some (.val (.word wcode)) ∧
      s.locals.lookup (ofString "code_len") = some (.val (.word wcl)) ∧
      wcl.toNat < 2 ^ 40

/-- `set_code(addr, code, code_len)` from a `SetCodeReadyB` entry: every resuming
outcome preserves `EvmMsgReadyMsgBounded`, establishes
`EvmStepCC ["heap_ptr", "journal_n", "scratch_ptr"]`, and preserves
`memW _ (globN s "ev" + 112)`. -/
theorem funSpec_set_code_msgBounded :
    FunSpec SetCodeReadyB
      (fun s r post => Resumes r →
        EvmMsgReadyMsgBounded post ∧ EvmStepCC setCodeGw s post ∧
          memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112))
      (ofString "set_code") := by
  refine ⟨_, _, _, lookup_set_code, fun {F} s hcode hP ⟨values, hl⟩ hnt hres => ?_⟩
  obtain ⟨hMB, waddr, wcode, wcl, haddr_l, hcode_l, hcl_l, hwcl⟩ := hP
  exact set_code_bounded_body_step s waddr wcode wcl hcode hMB haddr_l hcode_l hcl_l hwcl hnt hres

/-- `KeepsOn` corollary: `set_code` transitions `SetCodeReadyB` to
`EvmMsgReadyMsgBounded` on every resuming outcome. -/
theorem fk_set_code_msgBounded :
    KeepsOn SetCodeReadyB EvmMsgReadyMsgBounded (ofString "set_code") := by
  obtain ⟨ps, b, rs, hl, hsp⟩ := funSpec_set_code_msgBounded
  exact ⟨ps, b, rs, hl, fun s hc hP hex hnt hres => (hsp s hc hP hex hnt hres).1⟩

/-- Destination-free call of `set_code(e1, e2, e3)` inside a `D0PreB ∧ L` sequence,
yielding `D0CallPostB` (so it chains directly with `Hoare.seq` and
`hoare_d0PreB_seq_call`). The caller supplies, via `hargs`, that from every
entry state the three arguments evaluate to words with the third below `2^40`. -/
theorem hoare_d0PreB_call_set_code {gw : List String} {hp : Nat}
    {G : MlS → Option (ValueHOL 64)} {ch : List Ivl} {cells : List (Nat × Nat × Nat × Nat)}
    {L : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hL : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → L s → L t)
    (hsub : ∀ g ∈ setCodeGw, g ∈ gw)
    (e1 e2 e3 : ExpHOL 64)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      D0PreB gw hp G ch cells s → L s →
      ∃ waddr wcode wcl : BitVec 64,
        evalAt s e1 = some (.val (.word waddr)) ∧
        evalAt s e2 = some (.val (.word wcode)) ∧
        evalAt s e3 = some (.val (.word wcl)) ∧
        wcl.toNat < 2 ^ 40) :
    Hoare (fun s => D0PreB gw hp G ch cells s ∧ L s)
      (.call (some (none, none)) (ofString "set_code") [e1, e2, e3])
      (D0CallPostB gw hp G ch cells L) := by
  have hev : ofString "ev" ∉ setCodeGw.map ofString :=
    safeStepGlobals_setCode.not_mem_map (by decide)
  refine ⟨fun {F} s hcode ⟨hD, hLs⟩ hnt => ?_⟩
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hvals : evalListHOLFinite s
      (h := fun address => Classical.propDecidable (s.memaddrs address)) [e1, e2, e3] with
    _ | values
  · simp only [hvals]
    exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
  · simp only [hvals] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "set_code") values with
      _ | ⟨body', callee, ret'⟩
    · simp only [hl]
      exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hBe : EvmMsgReadyMsgBounded (callEntryStateHOLFinite s callee) :=
          localsFree_evmMsgReadyMsgBounded s callee (s.clock - 1) hD.1.1
        have hSe : StepFromCC gw hp G ch cells (callEntryStateHOLFinite s callee) :=
          localsFree_stepFromCC gw hp G ch cells s callee (s.clock - 1) hD.1.2
        obtain ⟨waddr, wcode, wcl, he1', he2', he3', hwcl⟩ := hargs s hD hLs
        obtain ⟨v1, v2, v3, he1, he2, he3, hc_a, hc_c, hc_l⟩ := callee_param_three s
          (ofString "set_code") (ofString "addr") (ofString "code") (ofString "code_len")
          .one .one .one _ _ (by rw [hcode]; exact lookup_set_code) e1 e2 e3
          values body' callee ret' hvals hl
        have hv1 : v1 = .val (.word waddr) := Option.some.inj (he1.symm.trans he1')
        have hv2 : v2 = .val (.word wcode) := Option.some.inj (he2.symm.trans he2')
        have hv3 : v3 = .val (.word wcl) := Option.some.inj (he3.symm.trans he3')
        have hEnt : SetCodeReadyB (callEntryStateHOLFinite s callee) := by
          refine ⟨hBe, waddr, wcode, wcl, ?_, ?_, ?_, hwcl⟩
          · rw [← hv1]; exact hc_a
          · rw [← hv2]; exact hc_c
          · rw [← hv3]; exact hc_l
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt ⊢
        have hQc (hsafe : res ≠ some .timeOut) (hres : Resumes res) :
            EvmMsgReadyMsgBounded post ∧ StepFromCC gw hp G ch cells post ∧
              post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") ∧
              memW post (globN s "ev" + 112) = memW s (globN s "ev" + 112) := by
          have hsp := FunSpec.at_lookup funSpec_set_code_msgBounded s hcode values body' callee
            ret' hl hEnt (by rw [hrun]; exact hsafe)
          rw [hrun] at hsp
          obtain ⟨hBp, hstep_c, h112_c⟩ := hsp hres
          have hSp := stepFromCC_of_evmStepCC hsub hSe hstep_c
          have hev_p : post.globals.lookup (ofString "ev") = s.globals.lookup (ofString "ev") :=
            (hstep_c.1.2.2.1 (ofString "ev") hev).symm
          exact ⟨hBp, hSp, hev_p, h112_c⟩
        cases res with
        | none =>
          exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            split
            · refine ⟨fun _ => ?_,
                fun h => absurd h (by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h)⟩
              obtain ⟨hBp, hSp, hev_p, h112_p⟩ := hQc (by simp) (Or.inl ⟨v, rfl⟩)
              have hBt : EvmMsgReadyMsgBounded { post with locals := s.locals } :=
                localsFree_evmMsgReadyMsgBounded post s.locals post.clock hBp
              have hSt : StepFromCC gw hp G ch cells { post with locals := s.locals } :=
                localsFree_stepFromCC gw hp G ch cells post s.locals post.clock hSp
              exact ⟨d0PreB_of_stepFromCC gw hp G ch cells hD hBt hSt rfl hev_p h112_p,
                hL s { post with locals := s.locals } rfl hLs⟩
            · exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
          | timeOut => simp at hnt
          | exception e v =>
            dsimp only
            refine ⟨(fun h => by cases h), fun hres => ?_⟩
            obtain ⟨hBp, hSp, _, _⟩ := hQc (by simp) hres
            exact ⟨localsFree_evmMsgReadyMsgBounded post _ post.clock hBp,
              localsFree_stepFromCC gw hp G ch cells post _ post.clock hSp⟩
          | error =>
            exact ⟨(fun h => by cases h), fun h => absurd h EvmFrameSpecs.not_resumes_error⟩
          | _ =>
            exact ⟨(fun h => by cases h),
              fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
