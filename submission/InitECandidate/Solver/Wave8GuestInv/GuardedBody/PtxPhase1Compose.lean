import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Gas
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem bound_of_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s prog).2.clock = s.clock) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s _ _ _ => ⟨by have := h s; omega, by have := h s; omega⟩

theorem clock_raise {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals (try rfl)

theorem clock_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) : (evaluateHOLFiniteState s (.assign k n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (try dsimp only)
  all_goals (cases k <;> rfl)

theorem clock_skip {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s .skip).2.clock = s.clock := by simp

theorem clock_store {F : Type} (s : PanSemStateFiniteExact 64 F) (a v : ExpHOL 64) :
    (evaluateHOLFiniteState s (.store a v)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_store]
  repeat' split
  all_goals (try dsimp only)

theorem raise_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (n : MlS) (e : ExpHOL 64) :
    (evaluateHOLFiniteState s (.raise n e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_raise]
  repeat' split
  all_goals (try simp)
  all_goals (split_ifs <;> simp)

theorem bound_mono {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {b : Nat} (h : TerminatingProgBoundedOn P p b)
    (hi : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Q s → P s) :
    TerminatingProgBoundedOn Q p b := fun s hc hq => h s hc (hi s hq)

theorem stage_entry (n : Nat) (fn : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn (StageP n) GuestInv fn args :=
  fun s _ _ callee _ _ hP _ _ => guestInv_callEntry s callee hP.1.1.1.1.1

theorem Hoare.decCall_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' v bpost hcode hP hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem Hoare.callLocal_resume {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {args : List (ExpHOL 64)}
    (hres : DecCallResumeOn P Q name fname args) :
    Hoare P (.call (some (some (.local,name),none)) fname args) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hc hP hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_call] at hr ⊢
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · rw [ha] at hr; simp at hr
  · simp only [ha] at hr ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨body,callee,ret⟩
    · simp [hl] at hr
    · simp only [hl] at hr ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hr
      · simp only [hz,↓reduceIte] at hr ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res,post⟩
        simp only [hb] at hr ⊢
        cases res with
        | none => simp at hr
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hr ⊢
            split at hr
            · rename_i hsh
              rw [if_pos hsh]
              split at hr
              · rename_i hv
                rw [if_pos hv]
                exact hres s vs body callee ret v post hc hP ha hl hb
              · simp at hr
            · simp at hr
          | _ => simp at hr

def chainGuard : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "cid"))) (.const 0))
    (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "cid")))
        (.load .one (.op .add [.var .global (ofString "be"),.const 0])))
      (.raise (ofString "BlockErr") (.const 100)) .skip) .skip

theorem chainGuard_hoare : Hoare (StageP 0) chainGuard (fun r t => r = none → StageP 0 t) := by
  apply Hoare.ite
  · apply Hoare.ite
    · exact ⟨fun s _ _ _ hr => (raise_ne_none s _ _ hr).elim⟩
    · exact Hoare.skip (fun _ h _ => h.1.1)
    · exact fun _ _ hr => by cases hr
  · exact Hoare.skip (fun _ h _ => h.1)
  · exact fun _ _ hr => by cases hr

theorem chainGuard_bound : TerminatingProgBoundedOn (StageP 0) chainGuard 0 := by
  have hb : TerminatingProgBoundedOn (StageP 0) chainGuard (max (max 0 0) 0) := TerminatingProgBoundedOn.ite_on
    (TerminatingProgBoundedOn.ite_on (bound_of_clock (fun s => clock_raise s (ofString "BlockErr") (.const 100)))
      (bound_of_clock clock_skip)) (bound_of_clock clock_skip)
  exact @hb

def blobBranch : ProgHOL 64 :=
  .decCall (ofString "bgp") (.comb [.one,.one,.one,.one]) (ofString "calculate_blob_gas_price")
    [.load .one (.op .add [.var .global (ofString "be"),.const 96])]
    (.decCall (ofString "bgf") (.comb [.one,.one,.one,.one,.one]) (ofString "fee_mul")
      [.var .local (ofString "tx_blob_gas_used"),.var .local (ofString "bgp")]
      (.assign .local (ofString "blob_gas_fee")
        (.rstruct [.rfield 1 (.var .local (ofString "bgf")),.rfield 2 (.var .local (ofString "bgf")),
          .rfield 3 (.var .local (ofString "bgf")),.rfield 4 (.var .local (ofString "bgf"))])))

theorem blobBranch_hoare (h : PtxCallees) :
    Hoare (StageP 2) blobBranch (fun r t => r = none → StageP 2 t) := by
  apply Hoare.decCall_fall (names := stageNames 2) (by decide) (localsOnly_stage 2)
  · exact resume_scratch_stage h.wk_calculate_blob_gas_price
      (gs := [("u256_ws",640)]) (by unfold ScratchSet; decide) (fun _ => rfl) (by decide) (by decide)
      (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide) (by decide) _
  · apply Hoare.decCall_fall (names := stageNames 2) (by decide) (localsOnly_stage 2)
    · exact resume_ro_stage h.ro_fee_mul (by decide) _
    · apply Hoare.assign
      · intro F s v hP hv
        exact fun _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hP
      · exact fun _ _ hr => by cases hr

theorem blobBranch_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (StageP 2) blobBranch
      ((K.calculate_blob_gas_price + 1) + (K.fee_mul + 1)) := by
  have hb : TerminatingProgBoundedOn GuestInv blobBranch (K.calculate_blob_gas_price + (K.fee_mul + 0 + 1) + 1) :=
    TerminatingProgBoundedOn.decCall_guestInv h.fb_calculate_blob_gas_price
    (ofString "bgp") (.comb [.one,.one,.one,.one]) _
    (TerminatingProgBoundedOn.decCall_guestInv h.fb_fee_mul
      (ofString "bgf") (.comb [.one,.one,.one,.one,.one]) _
      (bound_of_clock (fun s => clock_assign s .local (ofString "blob_gas_fee")
        (.rstruct [.rfield 1 (.var .local (ofString "bgf")),.rfield 2 (.var .local (ofString "bgf")),
          .rfield 3 (.var .local (ofString "bgf")),.rfield 4 (.var .local (ofString "bgf"))]))))
  intro F s hc hp
  have hr := hb s hc hp.1.1.1.1.1
  simpa only [Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
