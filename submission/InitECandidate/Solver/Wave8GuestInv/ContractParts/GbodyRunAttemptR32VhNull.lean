import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkShard01HtabCopy
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers

/-! Wave 8 R32 (GbodyRunAttemptR32VhNull): the `run_attempt` bound in the
empty-witness-header-list case.

When the decoded witness header list is empty (`*(si+80) = 0`), `run_attempt`
calls `validate_headers(_, 0)`, reloads `nh = *(si+80) = 0` and throws
`BlockErr 3` before reaching any of the strong-guard callees. The only work
is to show that `validate_headers` at `n = 0` leaves memory unchanged: its
guard `n >+ 256` falls through, the two `alloc` calls write no memory, both
loops run zero iterations and the function returns. Hence the reloaded `nh`
is still `0` and the remaining program is never entered.

The result, `run_attempt_vhLenZero`, is the `VhNullCase` leaf of
`GbodyRunAttemptR32Empty` (stated here at the weaker guard `VhLenZero`, which
drops the unused `*(si+72) = 0` conjunct). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32VhNull

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32

/-! ### The compiled `validate_headers` body -/

/-- The part of `validate_headers` after `var i = 0`, with the two loop bodies abstracted. -/
def vhsTail (b1 b2 : ProgHOL 64) : ProgHOL 64 :=
  .seq
    (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
    (.seq
      (.assign .local (ofString "i") (.const 1#64))
      (.seq
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) b2)
        (.return (.rstruct [.var .local (ofString "hs"), .var .local (ofString "hashes")]))))

/-- The part of `validate_headers` after the `n >+ 256` guard. -/
def vhsAllocs (b1 b2 : ProgHOL 64) : ProgHOL 64 :=
  .decCall (ofString "hs") .one (ofString "alloc")
    [.op .add [.panop .mul [.var .local (ofString "n"), .const 8#64], .const 8#64]]
    (.decCall (ofString "hashes") .one (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "n"), .const 32#64], .const 32#64]]
      (.dec (ofString "i") .one (.const 0#64) (vhsTail b1 b2)))

/-- The compiled `validate_headers` body, with the two loop bodies abstracted. -/
def vhsProg (b1 b2 : ProgHOL 64) : ProgHOL 64 :=
  .seq
    (.ite (.cmp .lower (.const 256#64) (.var .local (ofString "n")))
      (.raise (ofString "BlockErr") (.const 1#64))
      .skip)
    (vhsAllocs b1 b2)

theorem validate_headers_body_eq :
    ∃ b1 b2 : ProgHOL 64,
      (sourceFunctionEntry Guest.Software.guestFn_validate_headers).2.2.1 = vhsProg b1 b2 := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 2
  · simp only [sourceFunctionEntry, Guest.Software.guestFn_validate_headers,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      Option.map, List.map]
    rfl

/-! ### Evaluation helpers -/

private theorem memW_congr_memory {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.memory = s.memory) (a : Nat) : memW t a = memW s a := by
  unfold memW; rw [h]

private theorem evalAt_add2_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2]) = some (.val (.word x))) :
    ∃ w1 w2 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧ x = w1 + w2 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev; dsimp only at hev
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp at hev
      simp only [valueWord, wordOpHOL, wordOp, List.foldr, add_zero, Option.some.injEq] at hev
      exact ⟨w1, w2, h1, h2, hev.symm⟩

/-- A returning `var x = alloc(arg); cont` run: the continuation runs from an arena-ready
state with the same memory and the other locals unchanged, and the final memory is the
continuation's final memory. -/
private theorem decCall_alloc_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (arg : ExpHOL 64) (cont : ProgHOL 64) (nv : BitVec 64) (v : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (harg : evalAt s arg = some (.val (.word nv)))
    (hrun : evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont) =
      (some (.returned v), post)) :
    ∃ next post' : PanSemStateFiniteExact 64 F,
      ArenaReady next ∧ next.memory = s.memory ∧
      (∀ k, k ≠ x → next.locals.lookup k = s.locals.lookup k) ∧
      evaluateHOLFiniteState next cont = (some (.returned v), post') ∧
      post.memory = post'.memory := by
  obtain ⟨hp, fp, sp, hhp, -⟩ := R13.arenaOK_globals s hA.2
  have hres : InitECandidate.Solver.Wave8Contracts.M12.Resumes
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1 := by
    rw [hrun]; exact Or.inl ⟨v, rfl⟩
  obtain ⟨clk, -, -, -, -, hAn, hr, hs⟩ :=
    R13Shards.step_decCall_alloc_resumes s x arg cont nv hp hcode hA hhp harg hres
  let next : PanSemStateFiniteExact 64 F := { s with
    locals := s.locals.update (x, .val (.word hp))
    globals := s.globals.update (ofString "heap_ptr",
      .val (.word ((hp + (nv + 7)) &&& ((0 : BitVec 64) - 8))))
    clock := clk }
  change ArenaReady next at hAn
  rw [hrun] at hr hs
  have hr' : (evaluateHOLFiniteState next cont).1 = some (.returned v) := hr.symm
  have hs' : post.memory = (evaluateHOLFiniteState next cont).2.memory := by
    have h := congrArg (fun t : PanSemStateFiniteExact 64 F => t.memory) hs
    exact h
  refine ⟨next, (evaluateHOLFiniteState next cont).2, hAn, rfl, ?_, Prod.ext hr' rfl, hs'⟩
  intro k hk
  simp [next, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]

private theorem while_lt_n_zero {F : Type} (t : PanSemStateFiniteExact 64 F) (b : ProgHOL 64)
    (wi : BitVec 64)
    (hti : t.locals.lookup (ofString "i") = some (.val (.word wi)))
    (htn : t.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (hwi : wi = 0#64 ∨ wi = 1#64) :
    evaluateHOLFiniteState t
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) b) =
      (none, t) := by
  rw [evaluateHOLFiniteState_while_total]
  have hc : evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))) =
      some (.val (.word 0#64)) := by
    rw [evalHOLFinite_eq_toExact]
    rcases hwi with rfl | rfl <;> simp [evalHOLExact, hti, htn, wordCmpHOL] <;> decide
  rw [hc]; simp

private theorem return_memory {F : Type} (t : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    (evaluateHOLFiniteState t (.return e)).2.memory = t.memory := by
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

/-- With `i = 0` and `n = 0`, the loops of `validate_headers` run zero iterations and the
rest of the body writes no memory, whatever its result. -/
private theorem vhsTail_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (b1 b2 : ProgHOL 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 0#64))) :
    (evaluateHOLFiniteState s (vhsTail b1 b2)).2.memory = s.memory := by
  unfold vhsTail
  rw [evaluateHOLFiniteState_seq_line780, while_lt_n_zero s b1 0#64 hi hn (Or.inl rfl)]
  dsimp only
  have hc1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 1#64) = some (.val (.word 1#64)) := by simp [evalHOLExact]
  have hassign :
      evaluateHOLFiniteState s (.assign .local (ofString "i") (.const 1#64)) =
        (none, setKvarHOLFinite .local (ofString "i") (.val (.word 1#64)) s) ∨
      evaluateHOLFiniteState s (.assign .local (ofString "i") (.const 1#64)) =
        (some .error, s) := by
    rw [evaluateHOLFiniteState_assign, hc1]
    dsimp only
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hassign with ha | ha
  · rw [evaluateHOLFiniteState_seq_line780, ha]
    dsimp only
    have hi' : (setKvarHOLFinite .local (ofString "i") (.val (.word 1#64)) s).locals.lookup
        (ofString "i") = some (.val (.word 1#64)) := by
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hn' : (setKvarHOLFinite .local (ofString "i") (.val (.word 1#64)) s).locals.lookup
        (ofString "n") = some (.val (.word 0#64)) := by
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
        show ofString "i" ≠ ofString "n" by decide]
    rw [evaluateHOLFiniteState_seq_line780,
      while_lt_n_zero _ b2 1#64 hi' hn' (Or.inr rfl)]
    dsimp only
    rw [return_memory]
    rfl
  · rw [evaluateHOLFiniteState_seq_line780, ha]

/-- `validate_headers` at `n = 0` returns without writing memory. -/
theorem vhsProg_n0_memory {F : Type} (s : PanSemStateFiniteExact 64 F) (b1 b2 : ProgHOL 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hA : ArenaReady s)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 0#64)))
    (hrun : evaluateHOLFiniteState s (vhsProg b1 b2) = (some (.returned v), post)) :
    post.memory = s.memory := by
  unfold vhsProg at hrun
  have hite : evaluateHOLFiniteState s
      (.ite (.cmp .lower (.const 256#64) (.var .local (ofString "n")))
        (.raise (ofString "BlockErr") (.const 1#64)) .skip) = (none, s) := by
    rw [evaluateHOLFiniteState_ite]
    have hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .lower (.const 256#64) (.var .local (ofString "n"))) =
        some (.val (.word 0#64)) := by
      simp [evalHOLExact, hn, wordCmpHOL]
    rw [hc]; simp [evaluateHOLFiniteState_skip]
  rw [evaluateHOLFiniteState_seq_line780, hite] at hrun
  dsimp only at hrun
  unfold vhsAllocs at hrun
  have harg1 : evalAt s
      (.op .add [.panop .mul [.var .local (ofString "n"), .const 8#64], .const 8#64]) =
      some (.val (.word 8#64)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn,
      valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
  obtain ⟨s1, p1, hA1, hm1, hl1, hrun1, hp1⟩ :=
    decCall_alloc_returned s (ofString "hs") _ _ 8#64 v post hcode hA harg1 hrun
  have hn1 : s1.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    rw [hl1 _ (by decide)]; exact hn
  have harg2 : evalAt s1
      (.op .add [.panop .mul [.var .local (ofString "n"), .const 32#64], .const 32#64]) =
      some (.val (.word 32#64)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, hn1,
      valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
  obtain ⟨s2, p2, hA2, hm2, hl2, hrun2, hp2⟩ :=
    decCall_alloc_returned s1 (ofString "hashes") _ _ 32#64 v p1 hA1.1.code hA1 harg2 hrun1
  have hn2 : s2.locals.lookup (ofString "n") = some (.val (.word 0#64)) := by
    rw [hl2 _ (by decide)]; exact hn1
  rw [evaluateHOLFiniteState_dec_total] at hrun2
  dsimp only at hrun2
  have hc0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.const 0#64) = some (.val (.word 0#64)) := by simp [evalHOLExact]
  rw [hc0] at hrun2
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)) : ValueHOL 64)) =
      true := by simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hrun2; rw [if_pos hsh] at hrun2
  have hp2' : (evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word 0#64)) s2)
      (vhsTail b1 b2)).2.memory = p2.memory :=
    congrArg (fun o : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F =>
      o.2.memory) hrun2
  have htail := vhsTail_memory (setVarHOLFinite (ofString "i") (.val (.word 0#64)) s2) b1 b2
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn2,
          show ofString "i" ≠ ofString "n" by decide])
  rw [hp1, hp2, ← hp2', htail]
  exact hm2.trans hm1

/-! ### The `run_attempt` prefix -/

/-- `run_attempt` entry guard of the empty-header-list case: the R32 input guard together
with a zero witness header count `*(si+80)`. -/
def VhLenZero {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  InputReadyR32 s ∧ memW s (locN s "si" + 80) = 0

/-- After `pl := *(si+0)`. -/
def VH_Pl {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si : BitVec 64, ArenaReady s ∧ w_si.toNat + 96 ≤ 2 ^ 64 ∧
    memW s (w_si.toNat + 80) = 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si))

/-- After `vh := validate_headers(*(si+72), *(si+80))`. -/
def VH_Vh {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w_si : BitVec 64, GuestInv s ∧ w_si.toNat + 96 ≤ 2 ^ 64 ∧
    memW s (w_si.toNat + 80) = 0 ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si))

/-- After `nh := *(si+80)`. -/
def VH_Nh {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "nh") = some (.val (.word 0#64))

theorem vh_entry_dec_pl {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn VH_Pl body K) :
    TerminatingProgBoundedOn VhLenZero
      (.dec (ofString "pl") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) body) K := by
  refine dec_eval_on (P := VhLenZero) (Q := VH_Pl) (ofString "pl") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) ?_ hbody
  intro F s v hP hev
  obtain ⟨⟨S, Nd, hIA⟩, hz⟩ := hP
  have hAs : ArenaReady s := hIA.1
  obtain ⟨a, w_pl, ha, rfl, -, -⟩ := R16Shards.evalAt_load_one_word hAs.1 hev
  obtain ⟨w_si, w0, hsi_ev, -, -⟩ := evalAt_add2_words ha
  have hlsi : s.locals.lookup (ofString "si") = some (.val (.word w_si)) := by
    simpa [evalAt, evalHOLExact] using hsi_ev
  have hloc_si : locN s "si" = w_si.toNat := by simp [locN, hlsi]
  rw [hloc_si] at hIA hz
  have hsi_rc := hIA.2.2.1 (w_si.toNat, 96) (by simp [runAttemptCells])
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hsi_lt : w_si.toNat + 96 ≤ 2 ^ 64 := by
    rcases hsi_rc.2.1 with ⟨-, h0⟩ | hin
    · simp at h0
    · unfold Inside at hin
      dsimp only at hin
      omega
  refine ⟨w_si, (arenaReady_with_locals s _ s.clock).2 hAs, hsi_lt, ?_, ?_⟩
  · exact (memW_congr_memory (t := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) s)
      (s := s) rfl _).trans hz
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "pl" ≠ ofString "si" by decide, hlsi]

theorem decCallResumeOn_validate_headers_n0 :
    DecCallResumeOn VH_Pl VH_Vh (ofString "vh") (ofString "validate_headers")
      [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
       .load .one (.op .add [.var .local (ofString "si"), .const 80#64])] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, hAs, hsi_lt, hz, hlsi⟩ := hP
  have hargs_ex := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs_ex
  simp only [evalListHOLExact] at hargs_ex
  rcases he1 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "si"), .const 72#64])) with _ | v1
  · rw [he1] at hargs_ex; simp at hargs_ex
  · rw [he1] at hargs_ex
    rcases he2 : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) with _ | v2
    · rw [he2] at hargs_ex; simp at hargs_ex
    · rw [he2] at hargs_ex
      simp only [Option.some.injEq] at hargs_ex
      subst values
      obtain ⟨a2, w_n, ha2, rfl, hn_mem, -⟩ := R16Shards.evalAt_load_one_word hAs.1 he2
      obtain ⟨w1, w80, hw1, hw80, ha2_eq⟩ := evalAt_add2_words ha2
      have hw1_eq : w1 = w_si := by
        have hl1 : state.locals.lookup (ofString "si") = some (.val (.word w1)) := by
          simpa [evalAt, evalHOLExact] using hw1
        exact (by simpa [hlsi] using hl1 : w_si = w1).symm
      have hw80_eq : w80 = 80#64 := by
        simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq] at hw80
        exact hw80.symm
      subst w1; subst w80
      have ha2_nat : a2.toNat = w_si.toNat + 80 := by
        rw [ha2_eq, BitVec.toNat_add]
        change (w_si.toNat + 80) % 2 ^ 64 = w_si.toNat + 80
        exact Nat.mod_eq_of_lt (by omega)
      rw [ha2_nat, hz] at hn_mem
      have hwn : w_n = 0#64 := BitVec.eq_of_toNat_eq hn_mem
      subst hwn
      have hpc := callee_param_two state (ofString "validate_headers")
        (ofString "arr") (ofString "n") .one .one _ _
        (by rw [hcode]; exact lookup_validate_headers_fn)
        (.load .one (.op .add [.var .local (ofString "si"), .const 72#64]))
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64]))
        v1 (.val (.word 0#64)) [v1, .val (.word 0#64)] body callee ret he1 he2 hargs hl
      have hb : body = (sourceFunctionEntry Guest.Software.guestFn_validate_headers).2.2.1 :=
        lookupCodeHOLFinite_installed_body state.code.lookup
          (ofString "validate_headers")
          (sourceFunctionEntry Guest.Software.guestFn_validate_headers).2.1
          (sourceFunctionEntry Guest.Software.guestFn_validate_headers).2.2.1 body
          (sourceFunctionEntry Guest.Software.guestFn_validate_headers).2.2.2 ret
          [v1, .val (.word 0#64)] callee
          (by rw [hcode]; exact lookup_validate_headers_fn) hl
      obtain ⟨b1, b2, hbody⟩ := validate_headers_body_eq
      rw [hb, hbody] at hrun
      have hA_entry : ArenaReady (callEntryStateHOLFinite state callee) :=
        (arenaReady_with_locals state callee (state.clock - 1)).2 hAs
      have hmem : post.memory = state.memory :=
        vhsProg_n0_memory (callEntryStateHOLFinite state callee) b1 b2 value post
          hcode hA_entry hpc.2.2 hrun
      have hG_post : GuestInv post := by
        have h := guestInv_evaluate (callEntryStateHOLFinite state callee) (vhsProg b1 b2)
          hA_entry.1
        rw [hrun] at h
        exact h
      refine ⟨w_si, guestInv_congr (s := post) rfl rfl rfl rfl hG_post, hsi_lt, ?_, ?_⟩
      · exact (memW_congr_memory (s := state) hmem _).trans hz
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlsi,
          show ofString "vh" ≠ ofString "si" by decide]

theorem vh_dec_nh {K : Nat} {body : ProgHOL 64}
    (hbody : TerminatingProgBoundedOn VH_Nh body K) :
    TerminatingProgBoundedOn VH_Vh
      (.dec (ofString "nh") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) body) K := by
  refine dec_eval_on (P := VH_Vh) (Q := VH_Nh) (ofString "nh") .one
    (.load .one (.op .add [.var .local (ofString "si"), .const 80#64])) ?_ hbody
  intro F s v hP hev
  obtain ⟨w_si, hG, hsi_lt, hz, hlsi⟩ := hP
  obtain ⟨a, w_nh, ha, rfl, hnh_mem, -⟩ := R16Shards.evalAt_load_one_word hG hev
  obtain ⟨w1, w80, hw1, hw80, ha_eq⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_si := by
    have hl1 : s.locals.lookup (ofString "si") = some (.val (.word w1)) := by
      simpa [evalAt, evalHOLExact] using hw1
    exact (by simpa [hlsi] using hl1 : w_si = w1).symm
  have hw80_eq : w80 = 80#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw80
    exact hw80.symm
  subst w1; subst w80
  have ha_nat : a.toNat = w_si.toNat + 80 := by
    rw [ha_eq, BitVec.toNat_add]
    change (w_si.toNat + 80) % 2 ^ 64 = w_si.toNat + 80
    exact Nat.mod_eq_of_lt (by omega)
  rw [ha_nat, hz] at hnh_mem
  have hwnh : w_nh = 0#64 := BitVec.eq_of_toNat_eq hnh_mem
  subst hwnh
  simp [VH_Nh, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

/-- With `nh = 0`, the `nh == 0` guard always throws: it never falls through. -/
theorem hoare_ite_nh_zero_throws :
    Hoare VH_Nh
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (fun r _ => r = none → False) := by
  apply Hoare.ite_fall (Q := fun _ => False)
  · exact ⟨fun s _ _ _ hr => absurd hr (raise_ne_none s _ _)⟩
  · refine Hoare.of_false fun s ⟨hP, hcond⟩ => ?_
    obtain ⟨w1, w2, hw1, hw2, hcw⟩ := evalAt_cmp s .equal
      (.var .local (ofString "nh")) (.const 0#64) 0#64 hcond
    have hw1_eq : w1 = 0#64 := by
      have hl1 : s.locals.lookup (ofString "nh") = some (.val (.word w1)) := by
        simpa [evalAt, evalHOLExact] using hw1
      have hP' : s.locals.lookup (ofString "nh") = some (.val (.word 0#64)) := hP
      exact (by simpa [hP'] using hl1 : (0#64 : BitVec 64) = w1).symm
    have hw2_eq : w2 = 0#64 := by
      simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
        HolWordLab.word.injEq] at hw2
      exact hw2.symm
    subst w1; subst w2
    simp [wordCmpHOL] at hcw

/-- The `run_attempt` prefix up to the `nh == 0` guard, over an arbitrary remainder: in the
empty-header-list case the guard throws, so the remainder is never entered. -/
theorem vh_prefix (rest : ProgHOL 64) :
    TerminatingProgBoundedOn VhLenZero
      (.dec (ofString "pl") .one
        (.load .one (.op .add [.var .local (ofString "si"), .const 0#64]))
        (.seq .skip
          (.decCall (ofString "vh") (.comb [.one, .one]) (ofString "validate_headers")
            [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
             .load .one (.op .add [.var .local (ofString "si"), .const 80#64])]
            (.dec (ofString "nh") .one
              (.load .one (.op .add [.var .local (ofString "si"), .const 80#64]))
              (.seq
                (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
                  (.raise (ofString "BlockErr") (.const 3#64))
                  .skip)
                rest)))))
      (0 + (K.«validate_headers» + (max 0 0 + 0) + 1)) := by
  have hrest : TerminatingProgBoundedOn
      (fun {F : Type} (_ : PanSemStateFiniteExact 64 F) => False) rest 0 :=
    fun _ _ hp => hp.elim
  have hite_nh0 : TerminatingProgBoundedOn VH_Nh
      (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
        (.raise (ofString "BlockErr") (.const 3#64))
        .skip)
      (max 0 0) :=
    TerminatingProgBoundedOn.ite_on
      (TerminatingProgBoundedOn.of_clock (P := VH_Nh) (fun s => clock_raise s _ _))
      (TerminatingProgBoundedOn.of_clock (P := VH_Nh) (fun s => clock_skip s))
  have hnh0_seq : TerminatingProgBoundedOn VH_Nh
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "nh")) (.const 0#64))
          (.raise (ofString "BlockErr") (.const 3#64))
          .skip)
        rest)
      (max 0 0 + 0) :=
    TerminatingProgBoundedOn.seq_hoare_trans (P := VH_Nh)
      (Q := fun {F : Type} (_ : PanSemStateFiniteExact 64 F) => False)
      hite_nh0 hoare_ite_nh_zero_throws hrest
  have hnh_dec : TerminatingProgBoundedOn VH_Vh _ _ :=
    vh_dec_nh hnh0_seq
  have hvhs_call : TerminatingProgBoundedOn VH_Pl _ _ :=
    TerminatingProgBoundedOn.decCall_on
      R11Adapters.«fb_validate_headers» (ofString "vh") (.comb [.one, .one])
      [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
       .load .one (.op .add [.var .local (ofString "si"), .const 80#64])]
      (callEntryOn_of_imp localsFree_guestInv
        (fun _ h => by obtain ⟨_, hA, _⟩ := h; exact hA.1) _
        [.load .one (.op .add [.var .local (ofString "si"), .const 72#64]),
         .load .one (.op .add [.var .local (ofString "si"), .const 80#64])])
      decCallResumeOn_validate_headers_n0
      hnh_dec
  have hskip_vhs : TerminatingProgBoundedOn VH_Pl _ _ :=
    TerminatingProgBoundedOn.seq_hoare (P := VH_Pl)
      (TerminatingProgBoundedOn.of_clock (P := VH_Pl) (fun s => clock_skip s))
      (Hoare.skip fun _ h _ => h)
      hvhs_call
  have hall : TerminatingProgBoundedOn VhLenZero _ _ := vh_entry_dec_pl hskip_vhs
  intro F s hc hp
  exact hall s hc hp

/-- The full `run_attempt` body is bounded by the `validate_headers` budget in the
empty-header-list case: it throws `BlockErr 3` right after the call. -/
theorem runAttemptFullProg_vhLenZero :
    TerminatingProgBoundedOn VhLenZero runAttemptFullProg (K.«validate_headers» + 1) := by
  intro F s hc hp
  unfold runAttemptFullProg
  exact TerminatingRunBounded.weaken (vh_prefix _ s hc hp) (by omega)

/-- **`hVh` leaf.** `run_attempt` meets its budget whenever the decoded witness header
list is empty. -/
theorem run_attempt_vhLenZero :
    TerminatingFunBoundedOn VhLenZero (ofString "run_attempt") K.«run_attempt» := by
  refine ⟨(sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.1,
    (sourceFunctionEntry Guest.Software.guestFn_run_attempt).2.2.2,
    R10Shards.Fast_GbodyC17ToC21.lookup_run_attempt_fn, ?_⟩
  rw [sourceFnBody_run_attempt_eq]
  intro F s hc hp
  exact TerminatingRunBounded.weaken (runAttemptFullProg_vhLenZero s hc hp)
    (by unfold K.«run_attempt»; omega)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32VhNull
