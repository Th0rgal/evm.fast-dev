import InitECandidate.Solver.Wave8GuestInv.LeafStatements

/-! Helpers adapted from:
* wave8/leaves-rlp-opus55 at 998817a20efa0796e7eb06992d98f332943646bc (RlpWalk/RlpCore):
  `fb_auto`, `fb_unfold`, `generalize_K`, `fb_arith`, `fb_prove` (using `assumption` for explicit
  callee hypotheses instead of `known_fb`).
* wave8/leaves-htab-opus55 at 174f22acf3eaf4c94a0eb3c472201bd72f94c9db (Counter.lean):
  `IncrBody`, `cmpRank`, `counterGap`, `while_counter_guestInv`, `incr_body`.
Calls use explicit hypotheses only; no lookup of sorried spec leaves. -/
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S03

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn (prog : ProgHOL 64) (hs : extStraightLine prog = true) :
    TerminatingProgBoundedOn GuestInv prog 0 := by
  intro F s _ _ _
  have hclk := clockPreserving_of_extStraightLine (F := F) prog hs s
  exact ⟨by omega, by omega⟩

theorem dec_guestInv (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {K : Nat} (hbody : TerminatingProgBoundedOn GuestInv body K) :
    TerminatingProgBoundedOn GuestInv (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape init hbody

theorem call_guestInv' {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv hf destination arguments

theorem decCall_guestInv' {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv hf name shape arguments hcont

theorem callHandle_guestInv' {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_guestInv hf destination exn var hh arguments

/-! ### Counted loops `while i < X { ... ; i = i + 1 }` (from `wave8/leaves-htab-opus55` `Counter.lean`) -/

theorem guestInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F) (hs : GuestInv s) :
    GuestInv (decClockHOLFinite s) :=
  guestInv_with_locals_clock s s.locals _ hs

/-- Bodies whose normal completion runs `c = c + 1` last, and which never yield `continue`. -/
inductive IncrBody (c : MlS) : ProgHOL 64 → Prop
  | incr : IncrBody c (.assign .local c (.op .add [.var .local c, .const 1]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (noCont : noTopContinue first = true)
      (rest : IncrBody c tail) : IncrBody c (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrBody c body) : IncrBody c (.dec name shape init body)
  | decCall (name : MlS) (shape : ShapeHOL) (fn : MlS) (args : List (ExpHOL 64))
      {cont : ProgHOL 64} (distinct : c ≠ name) (rest : IncrBody c cont) :
      IncrBody c (.decCall name shape fn args cont)

theorem IncrBody.run {c : MlS} {body : ProgHOL 64} (hb : IncrBody c body) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      state.locals.lookup c = some (.val (.word w)) →
      (evaluateHOLFiniteState state body).1 ≠ some .continue ∧
      ((evaluateHOLFiniteState state body).1 = none →
        (evaluateHOLFiniteState state body).2.locals.lookup c = some (.val (.word (w + 1)))) := by
  induction hb with
  | incr =>
    intro F state w atC
    have run : evaluateHOLFiniteState state
        (.assign .local c (.op .add [.var .local c, .const 1])) =
        (none, setVarHOLFinite c (.val (.word (w + 1))) state) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, atC, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    refine ⟨by simp, fun _ => ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid noCont rest ih =>
    intro F state w atC
    have frame := evaluate_avoidsLocal_flowing c first avoid state
    have noContinue := evaluate_noTopContinue first noCont state
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at frame noContinue
      dsimp only at frame noContinue
      cases result with
      | none =>
        dsimp only
        have kept := frame (Or.inl rfl)
        exact ih middle w (by rw [kept]; exact atC)
      | some r =>
        dsimp only
        exact ⟨noContinue, fun h => by simp at h⟩
  | dec name shape init distinct rest ih =>
    intro F state w atC
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact ⟨by simp, by simp⟩
    · rename_i val _
      split
      · have atInner : (setVarHOLFinite name val state).locals.lookup c =
            some (.val (.word w)) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, atC]
        obtain ⟨t1, t2⟩ := ih (setVarHOLFinite name val state) w atInner
        cases run : evaluateHOLFiniteState (setVarHOLFinite name val state) _ with
        | mk res post =>
          rw [run] at t1 t2
          dsimp only at t1 t2 ⊢
          refine ⟨t1, fun normal => ?_⟩
          rw [PanRunBounded.resVarEq_lookup, if_neg distinct]
          exact t2 normal
      · exact ⟨by simp, by simp⟩
  | @decCall name shape fn args cont distinct rest ih =>
    intro F state w atC
    have hcont : (evaluateHOLFiniteState state (.decCall name shape fn args cont)).1 ≠
        some .continue := by
      intro hc
      rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
      rw [hrun] at hc
      dsimp only at hc
      subst hc
      obtain ⟨_, resumed, inner, hloc, _, hcr, _⟩ :=
        decCall_flowing (Or.inr (Or.inr rfl)) hrun
      have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
      have := (ih resumed w atR).1
      rw [hcr] at this
      exact this rfl
    refine ⟨hcont, fun hnone => ?_⟩
    rcases hrun : evaluateHOLFiniteState state (.decCall name shape fn args cont) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨_, resumed, inner, hloc, _, hcr, hpost⟩ := decCall_flowing (Or.inl rfl) hrun
    have atR : resumed.locals.lookup c = some (.val (.word w)) := (hloc c distinct).trans atC
    have := (ih resumed w atR).2
    rw [hcr] at this
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact this rfl

/-- Order key of a comparison: the signed test compares sign-flipped words. -/
def cmpRank (op : Cmp) (a : BitVec 64) : Nat :=
  match op with
  | .less => (a.toNat + 2 ^ 63) % 2 ^ 64
  | _ => a.toNat

theorem cmpRank_lt (op : Cmp) (hop : op = .less ∨ op = .lower) (a b : BitVec 64)
    (h : Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b = true) : cmpRank op a < cmpRank op b := by
  have ha := a.isLt
  have hb := b.isLt
  rcases hop with rfl | rfl
  · simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess] at h
    simp only [cmpRank]
    split_ifs at h <;> simp_all <;> omega
  · simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] at h
    simp only [cmpRank]
    omega

theorem cmpRank_succ (op : Cmp) (a b : BitVec 64) (h : cmpRank op a < cmpRank op b) :
    cmpRank op (a + 1) = cmpRank op a + 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have hs : (a + 1).toNat = (a.toNat + 1) % 2 ^ 64 := by simp [BitVec.toNat_add]
  cases op <;> simp only [cmpRank] at h ⊢ <;> omega

theorem cmpRank_le (op : Cmp) (a : BitVec 64) : cmpRank op a < 2 ^ 64 := by
  have := a.isLt
  cases op <;> simp only [cmpRank] <;> omega

/-- The rank gap of the loop test at a state (`0` if a local is not a word). -/
def counterGap (op : Cmp) (i X : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup i, s.locals.lookup X with
  | some (.val (.word a)), some (.val (.word b)) => cmpRank op b - cmpRank op a
  | _, _ => 0

theorem while_counter_guestInv (op : Cmp) (hop : op = .less ∨ op = .lower) (i X : MlS)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B) (hinc : IncrBody i body)
    (hX : avoidsLocal X body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp op (.var .local i) (.var .local X)) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (counterGap op i X)
    (fun s hs => guestInv_decClock s hs) hbody ?_ ?_
  · intro F s _ _ _
    simp only [counterGap]
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
    simp only [evalAt, evalHOLExact] at ha hb
    have hia : s.locals.lookup i = some (.val (.word a)) := by simpa using ha
    have hXb : s.locals.lookup X = some (.val (.word b)) := by simpa using hb
    have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL op a b = true := by
      by_contra hc
      simp [hc] at hword
      exact hnz hword
    have hlt := cmpRank_lt op hop a b hcmp
    obtain ⟨hnc, hinc'⟩ := hinc.run (decClockHOLFinite s) a hia
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hnc
    have hi' := hinc' hnone
    have hX' := evaluate_avoidsLocal_flowing X body hX (decClockHOLFinite s)
      (Or.inl hnone)
    have hX'' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup X =
        some (.val (.word b)) := hX'.trans hXb
    have hsucc := cmpRank_succ op a b hlt
    simp only [counterGap, hi', hX'', hia, hXb]
    omega

open Lean Elab Tactic Meta in
/-- Close `TerminatingFunBoundedOn P (ofString "f") ?B` by the local hypothesis about the
syntactically same function name (adapted from `wave8/leaves-htab-opus55` `Base.lean`). -/
elab "callee_hyp" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``TerminatingFunBoundedOn 3 do throwError "callee_hyp: bad goal"
  let fn := g.getAppArgs[1]!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``TerminatingFunBoundedOn 3 && t.getAppArgs[1]! == fn then
      if ← isDefEq t g then
        (← getMainGoal).assign d.toExpr
        replaceMainGoal []
        return
  throwError "callee_hyp: no hypothesis for {fn}"

/-- Prove `IncrBody c body` structurally. -/
macro "incr_body" : tactic => `(tactic| repeat (first
  | exact IncrBody.incr
  | apply IncrBody.dec _ _ _ (by decide)
  | apply IncrBody.decCall _ _ _ _ (by decide)
  | apply IncrBody.seq _ rfl rfl))

syntax "fb_auto" : tactic
macro_rules
  | `(tactic| fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto
         · fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto
         · fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; first | callee_hyp | assumption)
      | (apply decCall_guestInv'
         · first | callee_hyp | assumption
         · fb_auto)
      | (apply callHandle_guestInv'
         · first | callee_hyp | assumption
         · fb_auto)
      | (apply TerminatingProgBoundedOn.tailCall_guestInv; first | callee_hyp | assumption)
      | (apply while_counter_guestInv .less (Or.inl rfl)
         · fb_auto
         · incr_body
         · rfl)
      | (apply while_counter_guestInv .lower (Or.inr rfl)
         · fb_auto
         · incr_body
         · rfl))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expFieldToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

open Lean Elab Tactic Meta in
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8GuestInv.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       try simp only [nat_max_eq]
       first | omega | (simp only [Nat.max_def, max_def]; (try split_ifs) <;> omega)))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

/-! ### 24 s03 leaves -/

theorem fb_bal_list_remove_idx
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy») :
    TerminatingFunBoundedOn GuestInv (ofString "bal_list_remove_idx") K.«bal_list_remove_idx» := by
  fb_prove 424 Guest.Software.guestFn_bal_list_remove_idx K.«bal_list_remove_idx»

theorem fb_bal_remove_change
    (h_bal_list_remove_idx : TerminatingFunBoundedOn GuestInv (ofString "bal_list_remove_idx") K.«bal_list_remove_idx»)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») :
    TerminatingFunBoundedOn GuestInv (ofString "bal_remove_change") K.«bal_remove_change» := by
  fb_prove 425 Guest.Software.guestFn_bal_remove_change K.«bal_remove_change»

theorem fb_ceil32
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat») :
    TerminatingFunBoundedOn GuestInv (ofString "ceil32") K.«ceil32» := by
  fb_prove 442 Guest.Software.guestFn_ceil32 K.«ceil32»

theorem fb_charge_gas :
    TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» := by
  fb_prove 448 Guest.Software.guestFn_charge_gas K.«charge_gas»

theorem fb_charge_state_gas
    (h_add_sat : TerminatingFunBoundedOn GuestInv (ofString "add_sat") K.«add_sat») :
    TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas» := by
  fb_prove 449 Guest.Software.guestFn_charge_state_gas K.«charge_state_gas»

theorem fb_create_finish
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas»)
    (h_charge_state_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_state_gas") K.«charge_state_gas»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_set_code : TerminatingFunBoundedOn GuestInv (ofString "set_code") K.«set_code»)
    (h_words_of : TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of») :
    TerminatingFunBoundedOn GuestInv (ofString "create_finish") K.«create_finish» := by
  fb_prove 589 Guest.Software.guestFn_create_finish K.«create_finish»

theorem fb_destroy_account
    (h_destroy_storage : TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage»)
    (h_set_account : TerminatingFunBoundedOn GuestInv (ofString "set_account") K.«set_account») :
    TerminatingFunBoundedOn GuestInv (ofString "destroy_account") K.«destroy_account» := by
  fb_prove 390 Guest.Software.guestFn_destroy_account K.«destroy_account»

theorem fb_frame_halt :
    TerminatingFunBoundedOn GuestInv (ofString "frame_halt") K.«frame_halt» := by
  fb_prove 586 Guest.Software.guestFn_frame_halt K.«frame_halt»

theorem fb_frame_mem_release :
    TerminatingFunBoundedOn GuestInv (ofString "frame_mem_release") K.«frame_mem_release» := by
  fb_prove 12 Guest.Software.guestFn_frame_mem_release K.«frame_mem_release»

theorem fb_frame_state_gas_used :
    TerminatingFunBoundedOn GuestInv (ofString "frame_state_gas_used") K.«frame_state_gas_used» := by
  fb_prove 451 Guest.Software.guestFn_frame_state_gas_used K.«frame_state_gas_used»

theorem fb_get_pre_tx_account
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (h_record_pre_state_read : TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read»)
    (h_ws_get_account_optional : TerminatingFunBoundedOn GuestInv (ofString "ws_get_account_optional") K.«ws_get_account_optional») :
    TerminatingFunBoundedOn GuestInv (ofString "get_pre_tx_account") K.«get_pre_tx_account» := by
  fb_prove 420 Guest.Software.guestFn_get_pre_tx_account K.«get_pre_tx_account»

theorem fb_idx_start_account
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_get_pre_tx_account : TerminatingFunBoundedOn GuestInv (ofString "get_pre_tx_account") K.«get_pre_tx_account»)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero»)
    (h_st_le64 : TerminatingFunBoundedOn GuestInv (ofString "st_le64") K.«st_le64») :
    TerminatingFunBoundedOn GuestInv (ofString "idx_start_account") K.«idx_start_account» := by
  fb_prove 422 Guest.Software.guestFn_idx_start_account K.«idx_start_account»

theorem fb_increment_nonce
    (h_acct_copy : TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_modify_state_commit : TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit») :
    TerminatingFunBoundedOn GuestInv (ofString "increment_nonce") K.«increment_nonce» := by
  fb_prove 398 Guest.Software.guestFn_increment_nonce K.«increment_nonce»

theorem fb_jdel
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_htab_del : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del»)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with») :
    TerminatingFunBoundedOn GuestInv (ofString "jdel") K.«jdel» := by
  fb_prove 357 Guest.Software.guestFn_jdel K.«jdel»

theorem fb_jset
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy»)
    (h_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with») :
    TerminatingFunBoundedOn GuestInv (ofString "jset") K.«jset» := by
  fb_prove 356 Guest.Software.guestFn_jset K.«jset»

theorem fb_merge_tx_into_block
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get»)
    (h_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item»)
    (h_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new»)
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_htab_union_into : TerminatingFunBoundedOn GuestInv (ofString "htab_union_into") K.«htab_union_into») :
    TerminatingFunBoundedOn GuestInv (ofString "merge_tx_into_block") K.«merge_tx_into_block» := by
  fb_prove 401 Guest.Software.guestFn_merge_tx_into_block K.«merge_tx_into_block»

theorem fb_modify_state_commit
    (h_acct_is_empty : TerminatingFunBoundedOn GuestInv (ofString "acct_is_empty") K.«acct_is_empty»)
    (h_destroy_account : TerminatingFunBoundedOn GuestInv (ofString "destroy_account") K.«destroy_account»)
    (h_set_account : TerminatingFunBoundedOn GuestInv (ofString "set_account") K.«set_account») :
    TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit» := by
  fb_prove 391 Guest.Software.guestFn_modify_state_commit K.«modify_state_commit»

theorem fb_msg_new
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero») :
    TerminatingFunBoundedOn GuestInv (ofString "msg_new") K.«msg_new» := by
  fb_prove 465 Guest.Software.guestFn_msg_new K.«msg_new»

theorem fb_remove_storage_write
    (h_bal_list_remove_idx : TerminatingFunBoundedOn GuestInv (ofString "bal_list_remove_idx") K.«bal_list_remove_idx»)
    (h_htab_del : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del»)
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») :
    TerminatingFunBoundedOn GuestInv (ofString "remove_storage_write") K.«remove_storage_write» := by
  fb_prove 426 Guest.Software.guestFn_remove_storage_write K.«remove_storage_write»

theorem fb_set_account
    (h_jset : TerminatingFunBoundedOn GuestInv (ofString "jset") K.«jset») :
    TerminatingFunBoundedOn GuestInv (ofString "set_account") K.«set_account» := by
  fb_prove 387 Guest.Software.guestFn_set_account K.«set_account»

theorem fb_set_code
    (h_acct_copy : TerminatingFunBoundedOn GuestInv (ofString "acct_copy") K.«acct_copy»)
    (h_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (h_get_account : TerminatingFunBoundedOn GuestInv (ofString "get_account") K.«get_account»)
    (h_jset : TerminatingFunBoundedOn GuestInv (ofString "jset") K.«jset»)
    (h_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (h_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (h_modify_state_commit : TerminatingFunBoundedOn GuestInv (ofString "modify_state_commit") K.«modify_state_commit») :
    TerminatingFunBoundedOn GuestInv (ofString "set_code") K.«set_code» := by
  fb_prove 399 Guest.Software.guestFn_set_code K.«set_code»

theorem fb_stor_lookup
    (h_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get») :
    TerminatingFunBoundedOn GuestInv (ofString "stor_lookup") K.«stor_lookup» := by
  fb_prove 377 Guest.Software.guestFn_stor_lookup K.«stor_lookup»

theorem fb_words_of
    (h_ceil32 : TerminatingFunBoundedOn GuestInv (ofString "ceil32") K.«ceil32») :
    TerminatingFunBoundedOn GuestInv (ofString "words_of") K.«words_of» := by
  fb_prove 443 Guest.Software.guestFn_words_of K.«words_of»

/-! ### exact statement checks -/

example : (type_of% @fb_bal_list_remove_idx) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_bal_list_remove_idx)) := rfl
example : (type_of% @fb_bal_remove_change) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_bal_list_remove_idx) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_bal_remove_change)) := rfl
example : (type_of% @fb_ceil32) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ceil32)) := rfl
example : (type_of% @fb_charge_gas) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas)) := rfl
example : (type_of% @fb_charge_state_gas) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_add_sat) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas)) := rfl
example : (type_of% @fb_create_finish) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_gas) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_charge_state_gas) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_code) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_create_finish)) := rfl
example : (type_of% @fb_destroy_account) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_destroy_storage) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_destroy_account)) := rfl
example : (type_of% @fb_frame_halt) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_frame_halt)) := rfl
example : (type_of% @fb_frame_mem_release) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_frame_mem_release)) := rfl
example : (type_of% @fb_frame_state_gas_used) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_frame_state_gas_used)) := rfl
example : (type_of% @fb_get_pre_tx_account) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_record_pre_state_read) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ws_get_account_optional) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_pre_tx_account)) := rfl
example : (type_of% @fb_idx_start_account) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_pre_tx_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_st_le64) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_idx_start_account)) := rfl
example : (type_of% @fb_increment_nonce) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_acct_copy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_modify_state_commit) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_increment_nonce)) := rfl
example : (type_of% @fb_jdel) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_del) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trap_with) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_jdel)) := rfl
example : (type_of% @fb_jset) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memcpy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_trap_with) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_jset)) := rfl
example : (type_of% @fb_merge_tx_into_block) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_item) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_new) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_set) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_union_into) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_merge_tx_into_block)) := rfl
example : (type_of% @fb_modify_state_commit) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_acct_is_empty) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_destroy_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_modify_state_commit)) := rfl
example : (type_of% @fb_msg_new) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memzero) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_msg_new)) := rfl
example : (type_of% @fb_remove_storage_write) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_bal_list_remove_idx) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_del) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_remove_storage_write)) := rfl
example : (type_of% @fb_set_account) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_jset) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_account)) := rfl
example : (type_of% @fb_set_code) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_acct_copy) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_alloc) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_get_account) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_jset) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_keccak256) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_memeq) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_modify_state_commit) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_set_code)) := rfl
example : (type_of% @fb_stor_lookup) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_htab_get) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_stor_lookup)) := rfl
example : (type_of% @fb_words_of) = ((type_of% @InitECandidate.Solver.Wave8GuestInv.fb_ceil32) → (type_of% @InitECandidate.Solver.Wave8GuestInv.fb_words_of)) := rfl

/-! ### axiom audit -/


end InitECandidate.Solver.Wave8Leaves.S03
