import InitECandidate.Solver.Wave8GuestInv.Shards.S14.Core

/-! Proof of `fb_merkleize_progressive` (`merkleize_progressive`, AST line 8115, index 188)
for Wave 8 shard s14 (`wave8/leaves-s14`).

Imports only the light cone via `campaign.leaves.s14.Core`.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Leaves.S14

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound

/-- Address-domain size (`heapEnd - sourceBase`), matching `Wave8GuestInv.domainBytes`
definitionally (`rfl`). -/
def domainBytes : Nat := heapEnd - sourceBase

/-- Abstract ordinary-memory domain hypothesis satisfied by `GuestInv`
(`s.memaddrs = ordinaryDomain`). -/
def OrdinaryMem (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → s.memaddrs = ordinaryDomain

private theorem addresses_bounds (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ base.toNat + 8 * n := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]
        · simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord]; omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

private theorem ordinaryDomain_bounds (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have := addresses_bounds _ _ x (by rw [hs]; decide) h
  rw [hs] at this
  have e1 : sourceBase = 2701131776 := by decide
  have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  omega

private theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat]
  have ha := a.isLt
  have : a.toNat / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

private theorem eval_add2_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (d i : MlS) (a : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i]) =
      some (.val (.word a))) :
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧ a = x + y := by
  simp only [evalHOLExact, evalListHOLExact] at he
  rcases hd : s.locals.lookup d with _ | vd <;> rcases hi : s.locals.lookup i with _ | vi <;>
    simp only [hd, hi] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vd with ⟨⟨x⟩⟩ | _ | _ <;> rcases vi with ⟨⟨y⟩⟩ | _ | _ <;>
      simp [valueIsWord] at he
    refine ⟨x, y, rfl, rfl, ?_⟩
    simp [valueWord, wordOpHOL, wordOp] at he
    exact he.symm

private theorem eval_load_one {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.load .one e) = some v) :
    ∃ w, v = .val w := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · simp only [memLoadHOLExact] at he
      split at he
      · exact ⟨_, (Option.some.inj he).symm⟩
      · simp at he
    · simp at he
  · simp at he

private theorem store_add_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hmem : s.memaddrs = ordinaryDomain) (d i : MlS) (v : ExpHOL 64)
    (hv : ∀ (h : DecidablePred s.memaddrs) (val : ValueHOL 64),
      @evalHOLExact 64 F _ s.toExact h v = some val → ∃ w, val = .val w)
    (h : (evaluateHOLFiniteState s (.store (.op .add [.var .local d, .var .local i]) v)).1 = none) :
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧
      sourceBase ≤ (x + y).toNat ∧ (x + y).toNat < heapEnd := by
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ :=
      eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hv (fun a => Classical.propDecidable (s.memaddrs a)) val hval
      split at h
      · rename_i mem hmem'
        have hdom : s.memaddrs (x + y) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem'
          by_contra hc
          simp [hc] at hmem'
        rw [hmem] at hdom
        have := ordinaryDomain_bounds _ hdom
        omega
      · simp at h
    · simp at h
  · simp at h

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem storeByte_add_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hmem : s.memaddrs = ordinaryDomain) (d i : MlS) (v : ExpHOL 64)
    (h : (evaluateHOLFiniteState s (.storeByte (.op .add [.var .local d, .var .local i]) v)).1 = none) :
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧
      sourceBase ≤ (x + y).toNat ∧ (x + y).toNat < heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ :=
      eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · split at h
      · rename_i mem hmem'
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (x + y)) := by
          by_contra hc
          revert hmem'
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hmem] at hdom
        have := ordinaryDomain_bounds _ hdom
        have := byteAlign_bounds (x + y)
        omega
      · simp at h
    · simp at h
  · simp at h

/-- Syntactic check that a program never exits with `some (.returned _)`. -/
def noReturn : ProgHOL 64 → Bool
  | .skip => true
  | .assign _ _ _ => true
  | .store _ _ => true
  | .storeByte _ _ => true
  | .seq p q => noReturn p && noReturn q
  | .ite _ p q => noReturn p && noReturn q
  | .dec _ _ _ p => noReturn p
  | .while _ p => noReturn p
  | .call (some (none, none)) _ _ => true
  | _ => false

theorem evaluate_noReturn (program : ProgHOL 64) (supported : noReturn program = true)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned v) := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store dst val =>
    rcases (evaluate_store_control_frame state dst val).1 with h | h <;> rw [h] <;> simp
  | storeByte dst val =>
    rcases (evaluate_storeByte_control_frame state dst val).1 with h | h <;> rw [h] <;> simp
  | seq first second =>
    have children : noReturn first = true ∧ noReturn second = true := by
      simpa only [shape, noReturn, Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noReturn first children.1 state v
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at one remaining
      cases result with
      | none => exact evaluate_noReturn second children.2 middle v
      | some _ => exact one
  | ite condition yes no =>
    have children : noReturn yes = true ∧ noReturn no = true := by
      simpa only [shape, noReturn, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturn no children.2 state v
      · exact evaluate_noReturn yes children.1 state v
    · simp
  | dec name kind initializer body =>
    have child : noReturn body = true := by simpa only [shape, noReturn] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noReturn body child _ v
      · simp
  | call info function arguments =>
    have hinfo : info = some (none, none) := by
      rcases info with _ | ⟨_ | _, _ | _⟩ <;> simp [shape, noReturn] at supported
      rfl
    subst hinfo
    rw [evaluateHOLFiniteState_call]
    dsimp only
    repeat' first | split | simp | simp_all
  | «while» condition body =>
    have child : noReturn body = true := by simpa only [shape, noReturn] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have bodyNR := evaluate_noReturn body child (decClockHOLFinite state) v
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining bodyNR
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact evaluate_noReturn (.while condition body) (by simp [noReturn, child]) middle v
            | some r =>
              cases r with
              | «continue» =>
                exact evaluate_noReturn (.while condition body) (by simp [noReturn, child]) middle v
              | returned u =>
                by_cases huv : u = v
                · subst huv; exact absurd rfl bodyNR
                · simp [huv]
              | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturn] at supported
termination_by (state.clock, sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

private theorem seq_returned_of_noReturn {F : Type} {s : PanSemStateFiniteExact 64 F}
    {key : MlS} {p q : ProgHOL 64} {v : ValueHOL 64}
    (hnr : noReturn p = true) (hav : avoidsLocal key p = true)
    (h : (evaluateHOLFiniteState s (.seq p q)).1 = some (.returned v)) :
    ∃ mid, evaluateHOLFiniteState s p = (none, mid) ∧
      mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧
      mid.locals.lookup key = s.locals.lookup key ∧
      (evaluateHOLFiniteState mid q).1 = some (.returned v) := by
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s p
  have hnr' := evaluate_noReturn p hnr s v
  have hav' := evaluate_avoidsLocal_flowing key p hav s
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hp : evaluateHOLFiniteState s p with ⟨r, mid⟩
  rw [hp] at h hmeta hnr' hav'
  cases r with
  | none =>
    exact ⟨mid, rfl, hmeta.1, hmeta.2.1, hav' (Or.inl rfl), h⟩
  | some r1 =>
    exact absurd h hnr'

private theorem dec_returned_keep {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name key : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {q : ProgHOL 64} {v : ValueHOL 64}
    (hne : name ≠ key)
    (h : (evaluateHOLFiniteState s (.dec name shape init q)).1 = some (.returned v)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧
      mid.locals.lookup key = s.locals.lookup key ∧
      (evaluateHOLFiniteState mid q).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i val _
    split at h
    · refine ⟨setVarHOLFinite name val s, rfl, rfl, ?_, h⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · simp at h

private theorem decCall_returned_keep {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name key fn : MlS} {shape : ShapeHOL} {args : List (ExpHOL 64)} {q : ProgHOL 64}
    {v : ValueHOL 64} (hne : name ≠ key)
    (h : (evaluateHOLFiniteState s (.decCall name shape fn args q)).1 = some (.returned v)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧
      mid.locals.lookup key = s.locals.lookup key ∧
      (evaluateHOLFiniteState mid q).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_decCall_total] at h
  cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => rw [hargs] at h; simp at h
  | some vs =>
    rw [hargs] at h
    dsimp only at h
    cases hl : lookupCodeHOLFinite s.code.lookup fn vs with
    | none => rw [hl] at h; simp at h
    | some installed =>
      obtain ⟨b, callee, rs⟩ := installed
      rw [hl] at h
      dsimp only at h
      split at h
      · simp at h
      · have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) b
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b with ⟨r1, bpost⟩
        rw [hb] at h hmeta
        dsimp only [fixClockHOLFinite] at h
        cases r1 with
        | none => simp at h
        | some r2 =>
          cases r2 with
          | returned w =>
            simp only [] at h
            split at h
            · let clk := if (callEntryStateHOLFinite s callee).clock < bpost.clock
                then (callEntryStateHOLFinite s callee).clock else bpost.clock
              let mid : PanSemStateFiniteExact 64 F :=
                setVarHOLFinite name w { bpost with locals := s.locals, clock := clk }
              refine ⟨mid, hmeta.1, hmeta.2.1, ?_, h⟩
              simp [mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
            · simp at h
          | _ => simp at h

private theorem while_first_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {first rest : ProgHOL 64}
    (hcond : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word 1#64)))
    (hctrl : (evaluateHOLFiniteState (decClockHOLFinite s) first).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) first).1 = some .error)
    (hw : (evaluateHOLFiniteState s (.while cond (.seq first rest))).1 = none) :
    (evaluateHOLFiniteState (decClockHOLFinite s) first).1 = none := by
  rcases hctrl with hnone | herr
  · exact hnone
  · exfalso
    rw [evaluateHOLFiniteState_while_fixClockRewrite, hcond] at hw
    dsimp only at hw
    have h1 : (1#64 : BitVec 64) ≠ 0 := by decide
    rw [if_pos h1] at hw
    split at hw
    · simp at hw
    · rw [evaluateHOLFiniteState_seq_line780] at hw
      rcases hf : evaluateHOLFiniteState (decClockHOLFinite s) first with ⟨rf, mf⟩
      rw [hf] at herr hw
      dsimp only at herr
      subst herr
      simp at hw

private theorem evalList_three_out {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (dst : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, .const 32#64] = some vs)
    (he1 : evalAt s e1 = some (.val (.word dst))) :
    ∃ v2, vs = [.val (.word dst), v2, .val (.word 32#64)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalAt at he1
  simp only [evalListHOLExact, he1] at hargs
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
  · rw [h2] at hargs; cases hargs
  · rw [h2] at hargs
    change (some [ValueHOL.val (.word dst), v2, .val (.word 32#64)] = some vs) at hargs
    injection hargs with hvs
    exact ⟨v2, hvs.symm⟩

private theorem three_arg_lookup_memcpy
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hlookup_fn : code (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one))
    {dst : BitVec 64} {v2 : ValueHOL 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code (ofString "memcpy")
      [.val (.word dst), v2, .val (.word 32#64)] = some (foundBody, locals, rs)) :
    foundBody = sourceFnBody Guest.Software.guestFn_memcpy ∧
      locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
  cases v2 with
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | val wl2 =>
    cases wl2 with
    | word src =>
      rw [pan_three_word_lookup code (ofString "memcpy") (ofString "dst") (ofString "src")
        (ofString "n") (sourceFnBody Guest.Software.guestFn_memcpy) dst src 32#64
        (by decide) (by decide) (by decide) hlookup_fn] at hfound
      cases hfound
      refine ⟨rfl, ?_, ?_⟩
      · have h12 : ofString "dst" ≠ ofString "src" := by decide
        have h13 : ofString "dst" ≠ ofString "n" := by decide
        simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h12, Ne.symm h13]
      · simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem memcpy32_normal_out_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hmem : s.memaddrs = ordinaryDomain)
    (outExp srcExp : ExpHOL 64) (dst : BitVec 64)
    (hout : evalAt s outExp = some (.val (.word dst)))
    (h : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy")
      [outExp, srcExp, .const 32#64])).1 = none) :
    sourceBase ≤ dst.toNat ∧ dst.toNat < heapEnd := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [outExp, srcExp, .const 32#64] with _ | vs
  · rw [hargs] at h; simp at h
  · rw [hargs] at h
    dsimp only at h
    obtain ⟨v2, rfl⟩ := evalList_three_out s outExp srcExp dst hargs hout
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy")
        [.val (.word dst), v2, .val (.word 32#64)] with _ | ⟨body', callee, rs⟩
    · rw [hl] at h; simp at h
    · rw [hl] at h
      dsimp only at h
      have hl' := hl
      rw [hcode] at hl'
      obtain ⟨rfl, hdstCallee, hnCallee⟩ :=
        three_arg_lookup_memcpy originalRuntimeCode.lookup
          GuestUniformClockBound.lookup_memcpy hl'
      split at h
      · simp at h
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨bres, bpost⟩
        rw [hb] at h
        have hret : ∃ v, bres = some (.returned v) := by
          cases bres with
          | none => simp at h
          | some r =>
            cases r with
            | returned v => exact ⟨v, rfl⟩
            | _ => simp at h
        obtain ⟨v, rfl⟩ := hret
        clear h
        have hb1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_memcpy)).1 = some (.returned v) := by
          rw [hb]
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
          List.map, Option.map] at hb1
        rw [evaluateHOLFiniteState_dec_total] at hb1
        have hc0 : @evalHOLExact 64 F _ (callEntryStateHOLFinite s callee).toExact
            (fun a => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs a))
            (.const 0#64) = some (.val (.word 0#64)) := rfl
        simp only [hc0, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hb1
        set s0 := setVarHOLFinite (ofString "i") (.val (.word 0#64))
          (callEntryStateHOLFinite s callee) with hs0
        have hs0_mem : s0.memaddrs = ordinaryDomain := hmem
        have hs0_dst : s0.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
          have hne : ofString "i" ≠ ofString "dst" := by decide
          simp [hs0, setVarHOLFinite, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update,
            FUPDATE, hne, hdstCallee]
        have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
          simp [hs0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 32#64)) := by
          have hne : ofString "i" ≠ ofString "n" := by decide
          simp [hs0, setVarHOLFinite, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update,
            FUPDATE, hne, hnCallee]
        obtain ⟨midIte, hiteRun, _, _, _, hrestRun⟩ :=
          seq_returned_of_noReturn (key := ofString "dst") rfl rfl hb1
        rw [evaluateHOLFiniteState_ite] at hiteRun
        split at hiteRun
        · split at hiteRun
          · -- Unaligned branch: `.skip` ran, so `midIte = s0`!
            simp [evaluateHOLFiniteState_skip] at hiteRun
            subst midIte
            obtain ⟨_, hloop8Run, _, _, _, _⟩ :=
              seq_returned_of_noReturn (key := ofString "dst") rfl rfl hrestRun
            have hcond8 : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n"))
                  (.op .add [.var .local (ofString "i"), .const 8#64])) =
                some (.val (.word 1#64)) := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, evalListHOLExact, hs0_n, hs0_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            have hsbNone := while_first_none hcond8
              (evaluate_storeByte_control_frame (decClockHOLFinite s0) _ _).1
              (by rw [hloop8Run])
            obtain ⟨x, y, hx, hy, hlo, hhi⟩ := storeByte_add_bounds (decClockHOLFinite s0) hs0_mem
              (ofString "dst") (ofString "i") _ hsbNone
            have hxd : x = dst := by
              change s0.locals.lookup (ofString "dst") = _ at hx
              rw [hs0_dst] at hx
              injection hx with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            have hy0 : y = 0#64 := by
              change s0.locals.lookup (ofString "i") = _ at hy
              rw [hs0_i] at hy
              injection hy with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            subst hxd; subst hy0
            simpa using And.intro hlo hhi
          · -- Aligned branch: `seq w32 w8` ran with `.1 = none`!
            rw [evaluateHOLFiniteState_seq_line780] at hiteRun
            rcases hw : evaluateHOLFiniteState s0 _ with ⟨rw32, mw32⟩
            rw [hw] at hiteRun
            have hw32None : rw32 = none := by
              cases rw32 with
              | none => rfl
              | some _ => simp at hiteRun
            subst rw32
            have hcond32 : evalHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
                (.cmp .notLower (.var .local (ofString "n"))
                  (.op .add [.var .local (ofString "i"), .const 32#64])) =
                some (.val (.word 1#64)) := by
              rw [evalHOLFinite_eq_toExact]
              simp [evalHOLExact, evalListHOLExact, hs0_n, hs0_i, valueIsWord, valueWord,
                wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            have hstNone := while_first_none hcond32
              (evaluate_store_control_frame (decClockHOLFinite s0) _ _).1
              (by rw [hw])
            obtain ⟨x, y, hx, hy, hlo, hhi⟩ := store_add_bounds (decClockHOLFinite s0) hs0_mem
              (ofString "dst") (ofString "i") _
              (fun hdec val hval => eval_load_one (decClockHOLFinite s0) (h := hdec) _ val hval)
              hstNone
            have hxd : x = dst := by
              change s0.locals.lookup (ofString "dst") = _ at hx
              rw [hs0_dst] at hx
              injection hx with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            have hy0 : y = 0#64 := by
              change s0.locals.lookup (ofString "i") = _ at hy
              rw [hs0_i] at hy
              injection hy with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
            subst hxd; subst hy0
            simpa using And.intro hlo hhi
        · simp at hiteRun

private theorem lookup_merkleize :
    originalRuntimeCode.lookup (ofString "merkleize") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "limit", .one),
          (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_merkleize, .one) :=
  lookup_of_guestAst_getElem 186 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_merkleize) rfl

private theorem pan_four_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name p1 p2 p3 p4 : MlS) (body : ProgHOL width) (w1 w2 w3 w4 : BitVec width)
    (hp12 : p1 ≠ p2) (hp13 : p1 ≠ p3) (hp14 : p1 ≠ p4)
    (hp23 : p2 ≠ p3) (hp24 : p2 ≠ p4) (hp34 : p3 ≠ p4)
    (lookup : code name = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update
          (p3, .val (.word w3))).update (p4, .val (.word w4)), .one) := by
  have raw : lookupCodeHOLExact code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] =
      some (body,
        (fun key =>
          if key = p4 then some (.val (.word w4))
          else if key = p3 then some (.val (.word w3))
          else if key = p2 then some (.val (.word w2))
          else if key = p1 then some (.val (.word w1))
          else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, hp12, hp13, hp14, hp23, hp24, hp34]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases h4 : key = p4
    · subst key
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have hb4 := Ne.symm h4
      by_cases h3 : key = p3
      · subst key
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, hp34, Ne.symm hp34]
      · have hb3 := Ne.symm h3
        by_cases h2 : key = p2
        · subst key
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty,
            hp24, Ne.symm hp24, hp23, Ne.symm hp23]
        · have hb2 := Ne.symm h2
          by_cases h1 : key = p1
          · subst key
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty,
              hp14, Ne.symm hp14, hp13, Ne.symm hp13, hp12, Ne.symm hp12]
          · have hb1 := Ne.symm h1
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty,
              h1, h2, h3, h4, hb1, hb2, hb3, hb4]

private theorem four_arg_lookup_merkleize
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hlookup_fn : code (ofString "merkleize") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "limit", .one),
          (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_merkleize, .one))
    {v1 v2 v3 : ValueHOL 64} {dst : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code (ofString "merkleize")
      [v1, v2, v3, .val (.word dst)] = some (foundBody, locals, rs)) :
    foundBody = sourceFnBody Guest.Software.guestFn_merkleize ∧
      locals.lookup (ofString "out") = some (.val (.word dst)) := by
  have nonWordNone : ∀ v1' v2' v3',
      (shapeOfHOLExact v1' ≠ .one ∨ shapeOfHOLExact v2' ≠ .one ∨ shapeOfHOLExact v3' ≠ .one) →
      PanSemStateFiniteExact.lookupCodeHOLFinite code (ofString "merkleize")
        [v1', v2', v3', .val (.word dst)] = none := by
    intro v1' v2' v3' hbad
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rfl
    · rename_i _ _ _ raw
      rcases hbad with h1 | h2 | h3
      · simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
        cases hv : shapeOfHOLExact v1' <;> simp_all [shapeEqHOL]
      · simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
        cases hv : shapeOfHOLExact v2' <;> simp_all [shapeEqHOL]
      · simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
        cases hv : shapeOfHOLExact v3' <;> simp_all [shapeEqHOL]
  rcases v1 with ⟨⟨w1⟩⟩ | s1 | ⟨_, s1⟩
  · rcases v2 with ⟨⟨w2⟩⟩ | s2 | ⟨_, s2⟩
    · rcases v3 with ⟨⟨w3⟩⟩ | s3 | ⟨_, s3⟩
      · rw [pan_four_word_lookup code (ofString "merkleize") (ofString "p") (ofString "n")
          (ofString "limit") (ofString "out") (sourceFnBody Guest.Software.guestFn_merkleize)
          w1 w2 w3 dst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hlookup_fn] at hfound
        cases hfound
        refine ⟨rfl, ?_⟩
        simp [HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [nonWordNone _ _ _ (Or.inr (Or.inr (by simp [shapeOfHOLExact])))] at hfound; cases hfound
      · rw [nonWordNone _ _ _ (Or.inr (Or.inr (by simp [shapeOfHOLExact])))] at hfound; cases hfound
    · rw [nonWordNone _ _ _ (Or.inr (Or.inl (by simp [shapeOfHOLExact])))] at hfound; cases hfound
    · rw [nonWordNone _ _ _ (Or.inr (Or.inl (by simp [shapeOfHOLExact])))] at hfound; cases hfound
  · rw [nonWordNone _ _ _ (Or.inl (by simp [shapeOfHOLExact]))] at hfound; cases hfound
  · rw [nonWordNone _ _ _ (Or.inl (by simp [shapeOfHOLExact]))] at hfound; cases hfound

private theorem evalList_four_last {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 e4 : ExpHOL 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, e3, e4] = some vs) :
    ∃ v1 v2 v3 v4, evalAt s e4 = some v4 ∧ vs = [v1, v2, v3, v4] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs; cases hargs
  · rw [h1] at hargs
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hargs; cases hargs
    · rw [h2] at hargs
      rcases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · rw [h3] at hargs; cases hargs
      · rw [h3] at hargs
        rcases h4 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e4 with _ | v4
        · rw [h4] at hargs; cases hargs
        · rw [h4] at hargs
          change (some [v1, v2, v3, v4] = some vs) at hargs
          injection hargs with hvs
          exact ⟨v1, v2, v3, v4, h4, hvs.symm⟩

private theorem eval_roots_k_slot {F : Type} (s : PanSemStateFiniteExact 64 F)
    (roots k : MlS) (v4 : ValueHOL 64)
    (h4 : evalAt s (.op .add [.var .local roots, .panop .mul [.var .local k, .const 32#64]]) = some v4) :
    ∃ r wk : BitVec 64, s.locals.lookup roots = some (.val (.word r)) ∧
      s.locals.lookup k = some (.val (.word wk)) ∧
      v4 = .val (.word (r + wk * 32#64)) := by
  unfold evalAt at h4
  simp only [evalHOLExact, evalListHOLExact] at h4
  rcases hr : s.locals.lookup roots with _ | vr <;> simp only [hr] at h4
  · simp at h4
  · rcases hk : s.locals.lookup k with _ | vk <;> simp only [hk] at h4
    · simp at h4
    · rcases vr with ⟨⟨r⟩⟩ | _ | _ <;> rcases vk with ⟨⟨wk⟩⟩ | _ | _ <;>
        simp [valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp] at h4
      exact ⟨r, wk, rfl, rfl, h4.symm⟩

private theorem seq_ite_skip_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {key : MlS} {cond : ExpHOL 64} {yes q : ProgHOL 64} {v : ValueHOL 64}
    (hav : avoidsLocal key yes = true)
    (h : (evaluateHOLFiniteState s (.seq (.ite cond yes .skip) q)).1 = some (.returned v)) :
    (evaluateHOLFiniteState s yes).1 = some (.returned v) ∨
      ∃ mid : PanSemStateFiniteExact 64 F,
        mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧
        mid.locals.lookup key = s.locals.lookup key ∧
        (evaluateHOLFiniteState mid q).1 = some (.returned v) := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at h
  split at h
  · split at h
    · simp [evaluateHOLFiniteState_skip] at h
      exact Or.inr ⟨s, rfl, rfl, rfl, h⟩
    · have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata s yes
      have hav' := evaluate_avoidsLocal_flowing key yes hav s
      rcases hy : evaluateHOLFiniteState s yes with ⟨ry, my⟩
      rw [hy] at h hmeta hav'
      cases ry with
      | none => exact Or.inr ⟨my, hmeta.1, hmeta.2.1, hav' (Or.inl rfl), h⟩
      | some r => exact Or.inl h
  · simp at h

private theorem merkleize_call_out_bounds {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hmem : s.memaddrs = ordinaryDomain)
    (e1 e2 e3 : ExpHOL 64) (roots k : MlS)
    (h : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "merkleize")
      [e1, e2, e3, .op .add [.var .local roots, .panop .mul [.var .local k, .const 32#64]]])).1 = none) :
    ∃ r wk : BitVec 64, s.locals.lookup roots = some (.val (.word r)) ∧
      s.locals.lookup k = some (.val (.word wk)) ∧
      sourceBase ≤ (r + wk * 32#64).toNat ∧ (r + wk * 32#64).toNat < heapEnd := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, e2, e3, .op .add [.var .local roots, .panop .mul [.var .local k, .const 32#64]]] with _ | vs
  · rw [hargs] at h; simp at h
  · rw [hargs] at h
    dsimp only at h
    obtain ⟨v1, v2, v3, v4, hv4, rfl⟩ := evalList_four_last s e1 e2 e3 _ hargs
    obtain ⟨r, wk, hroots, hk, rfl⟩ := eval_roots_k_slot s roots k v4 hv4
    refine ⟨r, wk, hroots, hk, ?_⟩
    set dst := r + wk * 32#64
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "merkleize")
        [v1, v2, v3, .val (.word dst)] with _ | ⟨body', callee, rs⟩
    · rw [hl] at h; simp at h
    · rw [hl] at h
      dsimp only at h
      have hl' := hl
      rw [hcode] at hl'
      obtain ⟨rfl, houtCallee⟩ :=
        four_arg_lookup_merkleize originalRuntimeCode.lookup lookup_merkleize hl'
      split at h
      · simp at h
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_merkleize) with ⟨bres, bpost⟩
        rw [hb] at h
        have hret : ∃ v, bres = some (.returned v) := by
          cases bres with
          | none => simp at h
          | some r1 =>
            cases r1 with
            | returned v => exact ⟨v, rfl⟩
            | _ => simp at h
        obtain ⟨v, rfl⟩ := hret
        clear h
        have hb1 : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_merkleize)).1 = some (.returned v) := by
          rw [hb]
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_merkleize,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
          List.map, Option.map] at hb1
        have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
        have hce_mem : (callEntryStateHOLFinite s callee).memaddrs = ordinaryDomain := hmem
        have hce_out : (callEntryStateHOLFinite s callee).locals.lookup (ofString "out") =
            some (.val (.word dst)) := houtCallee
        obtain ⟨s1, hc1, hm1, ho1, hr1⟩ := decCall_returned_keep (key := ofString "out") (by decide) hb1
        obtain ⟨s2, hc2, hm2, ho2, hr2⟩ := decCall_returned_keep (key := ofString "out") (by decide) hr1
        obtain ⟨s3, hc3, hm3, ho3, hr3⟩ := decCall_returned_keep (key := ofString "out") (by decide) hr2
        have s3_code : s3.code = originalRuntimeCode := hc3.trans (hc2.trans (hc1.trans hce_code))
        have s3_mem : s3.memaddrs = ordinaryDomain := hm3.trans (hm2.trans (hm1.trans hce_mem))
        have s3_out : s3.locals.lookup (ofString "out") = some (.val (.word dst)) :=
          ho3.trans (ho2.trans (ho1.trans hce_out))
        rcases seq_ite_skip_returned (key := ofString "out") rfl hr3 with hyes | ⟨s4, hc4, hm4, ho4, hr4⟩
        · obtain ⟨_, hmc, _, _, _, _⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hyes
          exact memcpy32_normal_out_bounds s3 s3_code s3_mem
            (.var .local (ofString "out")) _ dst
            (by simp [evalAt, evalHOLExact, s3_out]) (by rw [hmc])
        · have s4_code : s4.code = originalRuntimeCode := hc4.trans s3_code
          have s4_mem : s4.memaddrs = ordinaryDomain := hm4.trans s3_mem
          have s4_out : s4.locals.lookup (ofString "out") = some (.val (.word dst)) :=
            ho4.trans s3_out
          obtain ⟨s5, hc5, hm5, ho5, hr5⟩ := decCall_returned_keep (key := ofString "out") (by decide) hr4
          obtain ⟨s6, hc6, hm6, ho6, hr6⟩ := dec_returned_keep (key := ofString "out") (by decide) hr5
          obtain ⟨s7, hc7, hm7, ho7, hr7⟩ := decCall_returned_keep (key := ofString "out") (by decide) hr6
          obtain ⟨s8, _, hc8, hm8, ho8, hr8⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hr7
          obtain ⟨s9, _, hc9, hm9, ho9, hr9⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hr8
          obtain ⟨s10, hc10, hm10, ho10, hr10⟩ := dec_returned_keep (key := ofString "out") (by decide) hr9
          obtain ⟨s11, _, hc11, hm11, ho11, hr11⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hr10
          obtain ⟨s12, hc12, hm12, ho12, hr12⟩ := dec_returned_keep (key := ofString "out") (by decide) hr11
          obtain ⟨s13, _, hc13, hm13, ho13, hr13⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hr12
          obtain ⟨_, hmc, _, _, _, _⟩ :=
            seq_returned_of_noReturn (key := ofString "out") rfl rfl hr13
          have s13_code : s13.code = originalRuntimeCode :=
            hc13.trans (hc12.trans (hc11.trans (hc10.trans (hc9.trans (hc8.trans (hc7.trans (hc6.trans (hc5.trans s4_code))))))))
          have s13_mem : s13.memaddrs = ordinaryDomain :=
            hm13.trans (hm12.trans (hm11.trans (hm10.trans (hm9.trans (hm8.trans (hm7.trans (hm6.trans (hm5.trans s4_mem))))))))
          have s13_out : s13.locals.lookup (ofString "out") = some (.val (.word dst)) :=
            ho13.trans (ho12.trans (ho11.trans (ho10.trans (ho9.trans (ho8.trans (ho7.trans (ho6.trans (ho5.trans s4_out))))))))
          exact memcpy32_normal_out_bounds s13 s13_code s13_mem
            (.var .local (ofString "out")) _ dst
            (by simp [evalAt, evalHOLExact, s13_out]) (by rw [hmc])

/-- Byte-granularity remaining-heap rank for `roots + k * 32`. -/
def slotRank (a : BitVec 64) : Nat :=
  min (heapEnd - a.toNat) (domainBytes + 64)

theorem slotRank_le (a : BitVec 64) : slotRank a ≤ domainBytes + 64 :=
  Nat.min_le_right _ _

theorem slotRank_step (a : BitVec 64) (hlo : sourceBase ≤ a.toNat) (hhi : a.toNat < heapEnd) :
    slotRank (a + 32#64) < slotRank a := by
  have he1 : sourceBase = 2701131776 := by decide
  have he2 : heapEnd = 33806089704 := by decide
  have hdb : domainBytes = heapEnd - sourceBase := rfl
  have hfit : a.toNat + 32 < 2 ^ 64 := by omega
  have hadd : (a + 32#64).toNat = a.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt]
    · rfl
    · simpa using hfit
  unfold slotRank
  rw [hadd]
  omega

/-- State rank for Loop #0 of `merkleize_progressive`: `slotRank (roots + k * 32)`. -/
def progressiveWalkRank (roots k : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup roots, s.locals.lookup k with
  | some (.val (.word r)), some (.val (.word wk)) => slotRank (r + wk * 32#64)
  | _, _ => 0

theorem progressiveWalkRank_le (roots k : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    progressiveWalkRank roots k s ≤ domainBytes + 64 := by
  unfold progressiveWalkRank
  split
  · exact slotRank_le _
  · omega

/-- Loop #0 of `merkleize_progressive`: calls `merkleize(..., roots + k * 32)` and increments `k`. -/
theorem while_progressive_walk {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (hMem : OrdinaryMem P)
    {cond cntInit iteCond e1 e2 e3 offRhs sizeRhs : ExpHOL 64}
    {cnt off size roots k : MlS}
    (hcnt_roots : cnt ≠ roots) (hcnt_k : cnt ≠ k)
    (hoff_roots : off ≠ roots) (hoff_k : off ≠ k)
    (hsize_roots : size ≠ roots) (hsize_k : size ≠ k)
    (hroots_k : roots ≠ k)
    {K_m : Nat} (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_m) :
    TerminatingProgBoundedOn P
      (.while cond
        (.dec cnt .one cntInit
          (.seq (.ite iteCond (.assign .local cnt (.var .local size)) .skip)
            (.seq (.call (some (none, none)) (ofString "merkleize")
                [e1, e2, e3, .op .add [.var .local roots, .panop .mul [.var .local k, .const 32#64]]])
              (.seq (.assign .local off offRhs)
                (.seq (.assign .local size sizeRhs)
                  (.assign .local k (.op .add [.var .local k, .const 1#64]))))))))
      (((domainBytes + 64) + 1) * ((K_m + 1) + 1)) := by
  let tailAssigns : ProgHOL 64 :=
    .seq (.assign .local off offRhs)
      (.seq (.assign .local size sizeRhs)
        (.assign .local k (.op .add [.var .local k, .const 1#64])))
  let mcall : ProgHOL 64 :=
    .call (some (none, none)) (ofString "merkleize")
      [e1, e2, e3, .op .add [.var .local roots, .panop .mul [.var .local k, .const 32#64]]]
  let preIte : ProgHOL 64 := .ite iteCond (.assign .local cnt (.var .local size)) .skip
  let body : ProgHOL 64 := .dec cnt .one cntInit (.seq preIte (.seq mcall tailAssigns))
  have hb : TerminatingProgBoundedOn P body (K_m + 1) :=
    TerminatingProgBoundedOn.weaken'
      (dec_meta hP cnt .one cntInit
        (seq_meta hP (straightOn preIte rfl)
          (seq_meta hP (call_meta hP h_merkleize) (straightOn tailAssigns rfl))))
      (by omega)
  apply TerminatingProgBoundedOn.while_rank (progressiveWalkRank roots k)
    (fun s hs => metadataInv_decClock hP s hs) hb
  · intro F s _ _ _
    exact progressiveWalkRank_le roots k s
  · intro F s hcode hs _ hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
    have hncBody : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .continue :=
      evaluate_noTopContinue body rfl (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hncBody
    rcases hbodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, post⟩
    rw [hbodyRun] at hnone
    dsimp only at hnone
    subst hnone
    obtain ⟨vcnt, inner1, hrun1, hloc1⟩ := dec_flowing (Or.inl rfl) hbodyRun
    set s1 := setVarHOLFinite cnt vcnt (decClockHOLFinite s)
    have hs1_code : s1.code = originalRuntimeCode := hcode
    have hs1_mem : s1.memaddrs = ordinaryDomain := hMem s hs
    have hmetaIte := PanRunBounded.evaluateHOLFiniteState_metadata s1 preIte
    have havIteR := evaluate_avoidsLocal_flowing roots preIte
      (by simp [preIte, avoidsLocal, hcnt_roots]) s1
    have havIteK := evaluate_avoidsLocal_flowing k preIte
      (by simp [preIte, avoidsLocal, hcnt_k]) s1
    rw [evaluateHOLFiniteState_seq_line780] at hrun1
    rcases hiteRun : evaluateHOLFiniteState s1 preIte with ⟨rite, s2⟩
    rw [hiteRun] at hrun1 hmetaIte havIteR havIteK
    cases rite with
    | some _ => simp at hrun1
    | none =>
      dsimp only at hrun1
      have hs2_code : s2.code = originalRuntimeCode := hmetaIte.1.trans hs1_code
      have hs2_mem : s2.memaddrs = ordinaryDomain := hmetaIte.2.1.trans hs1_mem
      have hmetaM := PanRunBounded.evaluateHOLFiniteState_metadata s2 mcall
      have havMR := evaluate_avoidsLocal_flowing roots mcall rfl s2
      have havMK := evaluate_avoidsLocal_flowing k mcall rfl s2
      rw [evaluateHOLFiniteState_seq_line780] at hrun1
      rcases hmRun : evaluateHOLFiniteState s2 mcall with ⟨rm, s3⟩
      rw [hmRun] at hrun1 hmetaM havMR havMK
      cases rm with
      | some _ => simp at hrun1
      | none =>
        dsimp only at hrun1
        obtain ⟨r, wk, hs2_roots, hs2_k, hlo, hhi⟩ :=
          merkleize_call_out_bounds s2 hs2_code hs2_mem e1 e2 e3 roots k (by rw [hmRun])
        have hs_roots : s.locals.lookup roots = some (.val (.word r)) := by
          have h1 := (havIteR (Or.inl rfl)).symm.trans hs2_roots
          simpa [s1, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hcnt_roots] using h1
        have hs_k : s.locals.lookup k = some (.val (.word wk)) := by
          have h1 := (havIteK (Or.inl rfl)).symm.trans hs2_k
          simpa [s1, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            hcnt_k] using h1
        have hs3_roots : s3.locals.lookup roots = some (.val (.word r)) :=
          (havMR (Or.inl rfl)).trans hs2_roots
        have hs3_k : s3.locals.lookup k = some (.val (.word wk)) :=
          (havMK (Or.inl rfl)).trans hs2_k
        have hincK : IncrBody k tailAssigns :=
          IncrBody.seq _ (by simp [avoidsLocal, hoff_k]) rfl
            (IncrBody.seq _ (by simp [avoidsLocal, hsize_k]) rfl IncrBody.incr)
        have hpost_k_inner : inner1.locals.lookup k = some (.val (.word (wk + 1#64))) := by
          have h2 := (hincK.run s3 wk hs3_k).2 (by rw [hrun1])
          rw [hrun1] at h2
          exact h2
        have havTailR := evaluate_avoidsLocal_flowing roots tailAssigns
          (by simp [tailAssigns, avoidsLocal, hoff_roots, hsize_roots, Ne.symm hroots_k]) s3
        have hpost_roots_inner : inner1.locals.lookup roots = some (.val (.word r)) := by
          rw [hrun1] at havTailR
          exact (havTailR (Or.inl rfl)).trans hs3_roots
        have hpost_roots : post.locals.lookup roots = some (.val (.word r)) := by
          rw [hloc1, PanRunBounded.resVarEq_lookup, if_neg hcnt_roots.symm, hpost_roots_inner]
        have hpost_k : post.locals.lookup k = some (.val (.word (wk + 1#64))) := by
          rw [hloc1, PanRunBounded.resVarEq_lookup, if_neg hcnt_k.symm, hpost_k_inner]
        unfold progressiveWalkRank
        change (match post.locals.lookup roots, post.locals.lookup k with
            | some (.val (.word r)), some (.val (.word wk)) => slotRank (r + wk * 32#64)
            | _, _ => 0) <
          (match s.locals.lookup roots, s.locals.lookup k with
            | some (.val (.word r)), some (.val (.word wk)) => slotRank (r + wk * 32#64)
            | _, _ => 0)
        rw [hpost_roots, hpost_k, hs_roots, hs_k]
        dsimp only
        have hmul : r + (wk + 1#64) * 32#64 = (r + wk * 32#64) + 32#64 := by
          rw [BitVec.add_mul, BitVec.one_mul, BitVec.add_assoc]
        rw [hmul]
        exact slotRank_step (r + wk * 32#64) hlo hhi

/-- State rank for a decrementing `while (k != 0)` loop. -/
def decCounterRank (k : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup k with
  | some (.val (.word wk)) => wk.toNat
  | _ => 0

theorem decCounterRank_le (k : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    decCounterRank k s ≤ 2 ^ 64 := by
  unfold decCounterRank
  split
  · rename_i wk _
    have := wk.isLt
    omega
  · omega

/-- Loop #1 of `merkleize_progressive`: `while (k != 0) { k := k - 1; rest }`. -/
theorem while_dec_counter {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (k : MlS) {rest : ProgHOL 64} {B : Nat}
    (hrest : TerminatingProgBoundedOn P rest B)
    (havoid : avoidsLocal k rest = true)
    (hnoCont : noTopContinue rest = true) :
    TerminatingProgBoundedOn P
      (.while (.cmp .notEqual (.var .local k) (.const 0#64))
        (.seq (.assign .local k (.op .sub [.var .local k, .const 1#64])) rest))
      ((2 ^ 64 + 1) * (B + 1)) := by
  let decAssign : ProgHOL 64 := .assign .local k (.op .sub [.var .local k, .const 1#64])
  let body : ProgHOL 64 := .seq decAssign rest
  have hb : TerminatingProgBoundedOn P body B :=
    TerminatingProgBoundedOn.weaken' (seq_meta hP (straightOn decAssign rfl) hrest) (by omega)
  apply TerminatingProgBoundedOn.while_rank (decCounterRank k)
    (fun s hs => metadataInv_decClock hP s hs) hb
  · intro F s _ _ _
    exact decCounterRank_le k s
  · intro F s _ hs hact hflow
    refine ⟨metadataInv_evaluate hP _ _ (metadataInv_decClock hP s hs), ?_⟩
    obtain ⟨word, hw, hnz⟩ := hact
    change evalAt s _ = _ at hw
    obtain ⟨wk, z, hk, hz, hword⟩ := evalAt_cmp s .notEqual _ _ word hw
    simp only [evalAt, evalHOLExact] at hk hz
    have hz0 : z = 0#64 := by
      injection hz with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
    subst z
    have hs_k : s.locals.lookup k = some (.val (.word wk)) := by simpa using hk
    have hwk_ne : wk ≠ 0#64 := by
      intro h0
      subst h0
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hword
      exact hnz hword
    have hwk_pos : 0 < wk.toNat := by
      by_contra hle
      apply hwk_ne
      apply BitVec.eq_of_toNat_eq
      simp
      omega
    have hncBody : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 ≠ some .continue :=
      evaluate_noTopContinue body (by simp [body, decAssign, noTopContinue, hnoCont])
        (decClockHOLFinite s)
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
      rcases hflow with h | h
      · exact h
      · exact absurd h hncBody
    rcases hbodyRun : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, post⟩
    rw [hbodyRun] at hnone
    dsimp only at hnone
    subst hnone
    have hdecRun : evaluateHOLFiniteState (decClockHOLFinite s) decAssign =
        (none, setVarHOLFinite k (.val (.word (wk - 1#64))) (decClockHOLFinite s)) := by
      have hkDec : (decClockHOLFinite s).locals.lookup k = some (.val (.word wk)) := hs_k
      simp [decAssign, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hkDec,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    have hseq := hbodyRun
    dsimp only [body] at hseq
    rw [evaluateHOLFiniteState_seq_line780, hdecRun] at hseq
    dsimp only at hseq
    have havR := evaluate_avoidsLocal_flowing k rest havoid
      (setVarHOLFinite k (.val (.word (wk - 1#64))) (decClockHOLFinite s))
    rw [hseq] at havR
    have hpost_k : post.locals.lookup k = some (.val (.word (wk - 1#64))) := by
      rw [havR (Or.inl rfl)]
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    unfold decCounterRank
    change (match post.locals.lookup k with | some (.val (.word w)) => w.toNat | _ => 0) <
      (match s.locals.lookup k with | some (.val (.word w)) => w.toNat | _ => 0)
    rw [hpost_k, hs_k]
    dsimp only
    have hsub : (wk - 1#64).toNat = wk.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le]
      · rfl
      · rw [BitVec.le_def]; exact hwk_pos
    omega

theorem fb_merkleize_progressive_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : MetadataInv P) (hMem : OrdinaryMem P)
    {K_heap_mark K_alloc K_merkleize K_memzero K_sha256_pair K_memcpy K_heap_release : Nat}
    (h_heap_mark : TerminatingFunBoundedOn P (ofString "heap_mark") K_heap_mark)
    (h_alloc : TerminatingFunBoundedOn P (ofString "alloc") K_alloc)
    (h_merkleize : TerminatingFunBoundedOn P (ofString "merkleize") K_merkleize)
    (h_memzero : TerminatingFunBoundedOn P (ofString "memzero") K_memzero)
    (h_sha256_pair : TerminatingFunBoundedOn P (ofString "sha256_pair") K_sha256_pair)
    (h_memcpy : TerminatingFunBoundedOn P (ofString "memcpy") K_memcpy)
    (h_heap_release : TerminatingFunBoundedOn P (ofString "heap_release") K_heap_release) :
    TerminatingFunBoundedOn P (ofString "merkleize_progressive")
      ((K_heap_mark + 1) + (K_alloc + 1) + (K_alloc + 1) +
        ((domainBytes + 64) + 1) * ((K_merkleize + 1) + 1) +
        (K_memzero + 1) +
        (2 ^ 64 + 1) * ((K_sha256_pair + 1) + 1) +
        (K_memcpy + 1) + (K_heap_release + 1)) := by
  fb_unfold 188 Guest.Software.guestFn_merkleize_progressive
  apply TerminatingProgBoundedOn.weaken'
  · apply decCall_meta hP
    · exact h_heap_mark
    · apply decCall_meta hP
      · exact h_alloc
      · apply decCall_meta hP
        · exact h_alloc
        · apply dec_meta hP
          apply dec_meta hP
          apply dec_meta hP
          apply seq_meta hP
          · exact while_progressive_walk hP hMem (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) h_merkleize
          · apply seq_meta hP
            · exact call_meta hP h_memzero
            · apply seq_meta hP
              · exact while_dec_counter hP (ofString "k") (call_meta hP h_sha256_pair) rfl rfl
              · fb_auto hP
  · fb_arith

end InitECandidate.Solver.Wave8Leaves.S14

