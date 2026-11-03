import InitECandidate.Solver.GuestBoundBlockTxBal
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_BitOps
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_SmodSar
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_Sha256
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_U256Core
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_StateHostLeaves
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_U256MulExp

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.FastGen

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod
open InitECandidate.Solver.Wave8GuestInv.FastBitOps
open InitECandidate.Solver.Wave8GuestInv.FastSmodSar
open InitECandidate.Solver.Wave8GuestInv.FastSha256
open InitECandidate.Solver.Wave8GuestInv.FastU256Core
open InitECandidate.Solver.Wave8GuestInv.FastStateHostLeaves
open InitECandidate.Solver.Wave8GuestInv.FastU256MulExp

noncomputable def expCounterGap (op : Cmp) (i : MlS) (limitExp : ExpHOL 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) limitExp with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_up_exp_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower)
    (i : MlS) (limitExp : ExpHOL 64) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hlim : expLocalsAvoided limitExp body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) limitExp) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp op (.var .local i) limitExp) body B (2 ^ 64)
    (expCounterGap op i limitExp)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [expCounterGap]
    split
    · rename_i a b _ _
      have := cmpRank_le op b
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s op _ _ word hw
    have hia : s.locals.lookup i = some (.val (.word a)) := by
      simpa [evalAt, evalHOLExact] using ha
    have hlim_s : @evalHOLExact 64 F _ s.toExact
        (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp =
        some (.val (.word b)) := by
      simpa [evalAt] using hb
    have hcmp : wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    have hi' := hstep (decClockHOLFinite s) a hia hflow
    have hflow' : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue :=
      hflow.elim Or.inl (fun h => Or.inr (Or.inr h))
    have hkeep : ∀ k, avoidsLocal k body = true →
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup k =
        s.locals.lookup k :=
      fun k hk => evaluate_avoidsLocal_flowing k body hk (decClockHOLFinite s) hflow'
    have hlim_eq : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        @evalHOLExact 64 F _ s.toExact
          (fun addr => Classical.propDecidable (s.memaddrs addr)) limitExp := by
      rw [← evalHOLFinite_eq_toExact, ← evalHOLFinite_eq_toExact]
      exact evalHOLFinite_eq_of_expLocalsAvoided _ s body hkeep limitExp hlim
    have hlim' : @evalHOLExact 64 F _
        (evaluateHOLFiniteState (decClockHOLFinite s) body).2.toExact
        (fun addr => Classical.propDecidable
          ((evaluateHOLFiniteState (decClockHOLFinite s) body).2.memaddrs addr)) limitExp =
        some (.val (.word b)) := hlim_eq.trans hlim_s
    have hsucc := cmpRank_succ op a b hlt
    simp only [expCounterGap, hi', hlim', hia, hlim_s]
    omega

def signedDownRank (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word w)) => w.toInt.toNat
  | _ => 0

theorem while_down_signed_guestInv (counter : MlS) {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hsub : CounterStep counter (-1) body) :
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .less (.const 0) (.var .local counter)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    (.cmp .less (.const 0) (.var .local counter)) body B (2 ^ 64)
    (signedDownRank counter)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    unfold signedDownRank
    split
    · rename_i w _
      have := BitVec.toInt_le (x := w)
      omega
    · omega
  · intro F s _ hs hact hflow
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨z, w, hz, hlw, hword⟩ := evalAt_cmp s .less _ _ word hw
    have hz0 : z = 0#64 := by simpa [evalAt, evalHOLExact] using hz.symm
    subst z
    have hlookup : s.locals.lookup counter = some (.val (.word w)) := by
      simpa [evalAt, evalHOLExact] using hlw
    have hcmp : wordCmpHOL .less 0#64 w = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt : (0 : Int) < w.toInt := by
      have hlt0 := cmpRank_lt .less (Or.inl rfl) 0#64 w hcmp
      have hc0 : cmpRank .less 0#64 = 2 ^ 63 := by decide
      rw [hc0] at hlt0
      unfold cmpRank at hlt0
      dsimp only at hlt0
      have hwlt := w.isLt
      have hw_pos : 0 < w.toNat ∧ w.toNat < 2 ^ 63 := by omega
      have hmsb : w.msb = false := BitVec.msb_eq_false_iff_two_mul_lt.mpr (by omega)
      rw [BitVec.toInt_eq_msb_cond, hmsb]
      simp; omega
    have hwmax := BitVec.toInt_le (x := w)
    have hnext : (w + (-1 : BitVec 64)).toInt = w.toInt - 1 := by
      have hm1 : (-1 : BitVec 64).toInt = -1 := by decide
      rw [BitVec.toInt_add, hm1]
      apply Int.bmod_eq_of_le <;> omega
    have heff := hsub (decClockHOLFinite s) w hlookup hflow
    simp only [signedDownRank, heff, hlookup, hnext]
    omega

theorem tailCall_guestInv' {fname : MlS} {B : Nat} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call none fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.tailCall_guestInv hf arguments

theorem while_counter_guestInv_step (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep : CounterStep i 1 body)
    (hnc : noTopContinue body = true)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) :=
  while_up_exp_guestInv op hop i (.var .local X) hbody hstep hX

open Lean Elab Tactic Meta in
def fgExactFbHyp : TacticM Unit := withMainContext do
  let goalType ← instantiateMVars (← getMainTarget)
  let args := goalType.getAppArgs
  if args.size < 2 then throwError "not TerminatingFunBoundedOn"
  let fnameExpr := args[1]!
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let hty ← instantiateMVars ldecl.type
    let hargs := hty.getAppArgs
    if hargs.size >= 2 && hargs[1]! == fnameExpr then
      let s ← saveState
      try
        let goal ← getMainGoal
        let rest ← goal.apply ldecl.toExpr
        if rest.isEmpty then
          replaceMainGoal []
          return
        restoreState s
      catch _ =>
        restoreState s
  let fnArgs := fnameExpr.getAppArgs
  if let some lastArg := fnArgs.back? then
    if let .lit (.strVal fnStr) := lastArg then
      let env ← getEnv
      let pfxList : List Name := [
        `InitECandidate.Solver.Wave8GuestInv.FastGen,
        `InitECandidate.Solver.Wave8GuestInv.P13.Callees,
        `InitECandidate.Solver.Wave8GuestInv.P13.DivMod,
        `InitECandidate.Solver.Wave8GuestInv.FastBitOps,
        `InitECandidate.Solver.Wave8GuestInv.FastSmodSar,
        `InitECandidate.Solver.Wave8GuestInv.FastSha256,
        `InitECandidate.Solver.Wave8GuestInv.FastU256Core,
        `InitECandidate.Solver.Wave8GuestInv.FastStateHostLeaves,
        `InitECandidate.Solver.Wave8GuestInv.FastU256MulExp
      ]
      for pfx in pfxList do
        let declName := pfx ++ Name.mkSimple s!"fb_{fnStr}"
        if env.contains declName then
          let s ← saveState
          try
            let e ← mkConstWithFreshMVarLevels declName
            let goal ← getMainGoal
            let rest ← goal.apply e
            if rest.isEmpty then
              replaceMainGoal []
              return
            restoreState s
          catch _ =>
            restoreState s
      let fbDecl := `InitECandidate.Solver.GuestBoundBlockTxBal ++ Name.mkSimple s!"funBounded_{fnStr}"
      if env.contains fbDecl then
        let s ← saveState
        try
          evalTactic (← `(tactic|
            exact TerminatingFunBoundedOn.of_unconditional
              (terminatingFunBounded_of_funBounded $(mkIdent fbDecl))))
          if (← getUnsolvedGoals).isEmpty then
            return
          restoreState s
        catch _ =>
          restoreState s
  throwError m!"no matching fb hypothesis for {fnameExpr}"

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| exact_fb_hyp) => fgExactFbHyp

open Lean Elab Tactic Meta in
partial def isStraightExpr (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some ``ProgHOL.call | some ``ProgHOL.decCall | some ``ProgHOL.while => false
  | some ``ProgHOL.seq =>
      let a := e.getAppArgs
      a.size >= 3 && isStraightExpr a[1]! && isStraightExpr a[2]!
  | some ``ProgHOL.ite =>
      let a := e.getAppArgs
      a.size >= 4 && isStraightExpr a[2]! && isStraightExpr a[3]!
  | some ``ProgHOL.dec =>
      let a := e.getAppArgs
      a.size >= 5 && isStraightExpr a[4]!
  | some _ => true
  | none => false

open Lean Elab Tactic Meta in
partial def fgWalkProg (allowOpen : Bool) : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let targs := tgt.getAppArgs
  if targs.size < 3 then
    if allowOpen then return else throwError m!"fgWalkProg: unexpected goal {tgt}"
  let prog0 ← instantiateMVars targs[1]!
  let prog ← if prog0.getAppFn.constName?.isSome then pure prog0 else whnfR prog0
  if isStraightExpr prog then
    let s0 ← saveState
    try
      evalTactic (← `(tactic| exact straightOn _ rfl))
      if (← getUnsolvedGoals).isEmpty then
        return
      restoreState s0
    catch _ =>
      restoreState s0
  let fnName := prog.getAppFn.constName?
  if fnName == some ``ProgHOL.seq then
    evalTactic (← `(tactic| apply TerminatingProgBoundedOn.seq_guestInv))
    let g1 :: g2 :: rest ← getUnsolvedGoals | throwError "fgWalkProg: seq goals"
    setGoals [g1]; fgWalkProg allowOpen; let gs1 ← getUnsolvedGoals
    setGoals [g2]; fgWalkProg allowOpen; let gs2 ← getUnsolvedGoals
    let rem ← rest.filterM (fun m => not <$> m.isAssigned)
    setGoals (gs1 ++ gs2 ++ rem)
  else if fnName == some ``ProgHOL.ite then
    evalTactic (← `(tactic| apply TerminatingProgBoundedOn.ite_on))
    let g1 :: g2 :: rest ← getUnsolvedGoals | throwError "fgWalkProg: ite goals"
    setGoals [g1]; fgWalkProg allowOpen; let gs1 ← getUnsolvedGoals
    setGoals [g2]; fgWalkProg allowOpen; let gs2 ← getUnsolvedGoals
    let rem ← rest.filterM (fun m => not <$> m.isAssigned)
    setGoals (gs1 ++ gs2 ++ rem)
  else if fnName == some ``ProgHOL.dec then
    evalTactic (← `(tactic| apply dec_guestInv))
    let g1 :: rest ← getUnsolvedGoals | throwError "fgWalkProg: dec goals"
    setGoals [g1]; fgWalkProg allowOpen; let gs1 ← getUnsolvedGoals
    let rem ← rest.filterM (fun m => not <$> m.isAssigned)
    setGoals (gs1 ++ rem)
  else if fnName == some ``ProgHOL.decCall then
    evalTactic (← `(tactic| apply decCall_guestInv'))
    let g1 :: g2 :: rest ← getUnsolvedGoals | throwError "fgWalkProg: decCall goals"
    setGoals [g1]; fgExactFbHyp
    setGoals [g2]; fgWalkProg allowOpen; let gs2 ← getUnsolvedGoals
    let rem ← rest.filterM (fun m => not <$> m.isAssigned)
    setGoals (gs2 ++ rem)
  else if fnName == some ``ProgHOL.call then
    let stCall ← saveState
    try
      evalTactic (← `(tactic| apply tailCall_guestInv'))
      let g1 :: rest ← getUnsolvedGoals | throwError "tailCall"
      setGoals [g1]; fgExactFbHyp
      let rem ← rest.filterM (fun m => not <$> m.isAssigned)
      setGoals rem
    catch _ =>
      restoreState stCall
      let stCall2 ← saveState
      try
        evalTactic (← `(tactic| apply call_guestInv'))
        let g1 :: rest ← getUnsolvedGoals | throwError "call"
        setGoals [g1]; fgExactFbHyp
        let rem ← rest.filterM (fun m => not <$> m.isAssigned)
        setGoals rem
      catch _ =>
        restoreState stCall2
        evalTactic (← `(tactic| apply callHandle_guestInv'))
        let g1 :: g2 :: rest ← getUnsolvedGoals | throwError "fgWalkProg: callHandle goals"
        setGoals [g1]; fgExactFbHyp
        setGoals [g2]; fgWalkProg allowOpen; let gs2 ← getUnsolvedGoals
        let rem ← rest.filterM (fun m => not <$> m.isAssigned)
        setGoals (gs2 ++ rem)
  else
    if allowOpen then
      evalTactic (← `(tactic|
        try dsimp only [
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
          List.map]))
      return
    else throwError m!"fgWalkProg: unhandled {prog}"

open Lean Elab Tactic Meta in
elab "fg_step_auto" : tactic => fgWalkProg false

open Lean Elab Tactic Meta in
elab "fg_step_loops" : tactic => fgWalkProg true

syntax "fg_unfold " num ident : tactic
macro_rules
  | `(tactic| fg_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         Option.map]))

syntax "fg_arith " ident : tactic
macro_rules
  | `(tactic| fg_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       first | omega | (try simp only [BitVec.toNat_ofNat, Nat.max_def, max_def]; (try split_ifs) <;> omega)))

end InitECandidate.Solver.Wave8GuestInv.FastGen
