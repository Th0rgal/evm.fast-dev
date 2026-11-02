import InitECandidate.Solver.Wave8GuestInv.Deliveries.M05.WorldLemmas

/-! `wk_extract_deposit_data`: relational world step for `extract_deposit_data`
(`Guest/SoftwareAst.lean:32212`, AST index 841) with output region `[(locN s "out", 192)]`.

Execution structure:
1. If `n != 576`, raises `BlockErr 60` (state unchanged).
2. Saves `mark := heap_mark()` (`= globN s "heap_ptr"`), runs read-only checks
   (`is_zero_bytes`, `ld_be64` -> `bswap64`) updating only local variables, and restores
   `heap_release(mark)` (assigning `heap_ptr` back to its identical value `s.globals["heap_ptr"]`).
3. If `ok == 0`, raises `BlockErr 61` (globals/memory unchanged).
4. Runs five sequential `memcpy` calls into `[out, out + 48)`, `[out + 48, out + 80)`,
   `[out + 80, out + 88)`, `[out + 88, out + 184)`, `[out + 184, out + 192)`.
   Each `memcpy(dst, src, k)` (`k > 0`) that completes normally writes only inside `[dst, dst + k)`
   without wraparound (`dst + k ≤ heapEnd`), hence `ByteRegionEffect s post [(locN s "out", 192)]`,
   which lifts to `WorldStep` by `ByteRegionEffect.to_worldStep_R`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8Contracts.M05

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ### 1. Read-only helpers for `heap_mark`, `is_zero_bytes`, `bswap64`, `ld_be64` -/

private theorem ro_heap_mark : ReadOnlyFn (ofString "heap_mark") :=
  readOnlyFn_of_guestAst 8 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_mark rfl
    (ReadOnlyProg.ret _)

private theorem ro_is_zero_bytes : ReadOnlyFn (ofString "is_zero_bytes") :=
  readOnlyFn_of_guestAst 19 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_zero_bytes rfl
    (ReadOnlyProg.dec _ _ _
      (ReadOnlyProg.seq
        (ReadOnlyProg.while_loop _
          (ReadOnlyProg.seq
            (ReadOnlyProg.ite _ (ReadOnlyProg.ret _) ReadOnlyProg.skip)
            (ReadOnlyProg.assign_local _ _)))
        (ReadOnlyProg.ret _)))

private theorem ro_bswap64 : ReadOnlyFn (ofString "bswap64") :=
  readOnlyFn_of_guestAst 23 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bswap64 rfl
    (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _)
      (ReadOnlyProg.seq (ReadOnlyProg.assign_local _ _)
        (ReadOnlyProg.ret _)))

private theorem ro_ld_be64 : ReadOnlyFn (ofString "ld_be64") :=
  readOnlyFn_of_guestAst 24 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ld_be64 rfl
    (ReadOnlyProg.seq
      (ReadOnlyProg.ite _ (ReadOnlyProg.tailCall ro_bswap64 _) ReadOnlyProg.skip)
      (ReadOnlyProg.ret _))

/-! ### 2. Exact effect of `heap_mark` and `heap_release(mark)` -/

private theorem lookup_heap_mark :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

private theorem lookup_heap_release :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

private theorem global_heap_ptr_word {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hw : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hw)) ∧
        hw.toNat = globN s "heap_ptr" := by
  have hpos : 0 < globN s "heap_ptr" := by
    have hsb := hA.1
    rw [sourceBase_val] at hsb
    omega
  unfold globN at hpos ⊢
  split at hpos
  · rename_i w hw; exact ⟨w, hw, rfl⟩
  · omega

private theorem fupdate_same_lookup {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (k : α) (v : β) (hk : m.lookup k = some v) :
    m.update (k, v) = m := by
  cases m with
  | mk f hf =>
    have hk' : f k = some v := hk
    have hfun : FUPDATE f (k, v) = f := by
      funext x
      by_cases hx : x = k
      · subst hx
        simp [FUPDATE, hk']
      · rw [FUPDATE]
        simp [Ne.symm hx]
    simp only [HolFiniteMapExact.update, hfun]

private theorem call_heap_release_noop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hglob : s.globals.lookup (ofString "heap_ptr") = some (.val (.word hw)))
    (hmark : s.locals.lookup (ofString "mark") = some (.val (.word hw)))
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])).1 ≠
      some .timeOut) :
    let rp := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
    rp.2 = { s with locals := rp.2.locals, clock := rp.2.clock } := by
  intro rp
  dsimp only [rp]
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "mark")] = some [.val (.word hw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hmark]
  rw [hargs] at hnt ⊢
  dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "heap_release") [.val (.word hw)] with
    _ | ⟨body', callee, ret'⟩
  · cases s; rfl
  · simp only [hl] at hnt ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · simp only [hz, ↓reduceIte] at hnt ⊢
      have hlook' : s.code.lookup (ofString "heap_release") =
          some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) := by
        rw [hcode]; exact lookup_heap_release
      have hcallee := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "heap_release")
        [.val (.word hw)] body' callee ret' hl
      simp only [lookupCodeHOLExact, hlook'] at hcallee
      split at hcallee
      · injection hcallee with h_tup
        injection h_tup with hb_eq h_rest
        injection h_rest with hc_eq hr_eq
        subst hb_eq hr_eq
        have hm_callee : callee.lookup (ofString "m") = some (.val (.word hw)) := by
          rw [← hc_eq]; rfl
        let entry := callEntryStateHOLFinite s callee
        have hm_entry : entry.locals.lookup (ofString "m") = some (.val (.word hw)) := hm_callee
        have hg_entry : entry.globals = s.globals := rfl
        have hbody_eval : evaluateHOLFiniteState (s.callEntryStateHOLFinite callee)
            (sourceFnBody Guest.Software.guestFn_heap_release) =
            (some (.returned (.val (.word 0))), (s.callEntryStateHOLFinite callee).emptyLocalsHOLFinite) := by
          dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_release,
            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
          have hev : @evalHOLExact 64 F _ entry.toExact
              (fun a => Classical.propDecidable (entry.memaddrs a)) (.var .local (ofString "m")) =
              some (.val (.word hw)) := by
            simp [evalHOLExact, hm_entry]
          rw [hev]
          dsimp only
          have hvalid : entry.isValidValueHOLFinite .global (ofString "heap_ptr")
              (.val (.word hw)) = true := by
            simp [PanSemStateFiniteExact.isValidValueHOLFinite,
              lookupKvarHOLExact, hg_entry, hglob, shapeOfHOLExact, shapeEqHOL]
          rw [hvalid]
          simp only [↓reduceIte, setKvarHOLFinite, setGlobalHOLFinite]
          have hupd : entry.globals.update (ofString "heap_ptr", .val (.word hw)) = entry.globals :=
            fupdate_same_lookup entry.globals (ofString "heap_ptr") (.val (.word hw))
              (by rw [hg_entry]; exact hglob)
          have hentry_id : (let __src := entry;
              { locals := __src.locals,
                globals := __src.globals.update (ofString "heap_ptr", .val (.word hw)),
                structs := __src.structs, code := __src.code, eshapes := __src.eshapes,
                memory := __src.memory, memaddrs := __src.memaddrs, shMemaddrs := __src.shMemaddrs,
                clock := __src.clock, be := __src.be, ffi := __src.ffi,
                baseAddr := __src.baseAddr, topAddr := __src.topAddr }) = entry := by
            dsimp only; rw [hupd]
          rw [hentry_id, evaluateHOLFiniteState_return]
          have hc0 : @evalHOLExact 64 F _ entry.toExact
              (fun a => Classical.propDecidable (entry.memaddrs a)) (.const (0 : BitVec 64)) =
              some (.val (.word 0)) := rfl
          dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0 ⊢
          rw [hc0]
          dsimp only
          simp [shapeOfHOLExact, entry]
        rw [hbody_eval]
        simp [shapeOfHOLExact, shapeEqHOL, callEntryStateHOLFinite, emptyLocalsHOLFinite]
      · simp at hcallee

/-! ### 3. `memcpy` write-region theorem (`ByteRegionEffect` + `Inside` on normal return) -/

private theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

private def noBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq a b => noBreak a && noBreak b
  | .ite _ a b => noBreak a && noBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreak {F : Type} (p : ProgHOL 64) (hp : noBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreak] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreak] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreak b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreak a = true ∧ noBreak b = true := by
      simpa [shape, noBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreak b hab.2 s
      · exact evaluate_noBreak a hab.1 s
    · simp
  | _ => simp [shape, noBreak] at hp

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem evaluate_noReturnOrRaise {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) :
    ¬ Resumes (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact not_resumes_error
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · exact not_resumes_error
      · exact not_resumes_error
    · exact not_resumes_error
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaise a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaise b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaise b hab.2 s
      · exact evaluate_noReturnOrRaise a hab.1 s
    · exact not_resumes_error
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaise body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaise (.while cond body) (by simpa [noReturnOrRaise] using hb) mid
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def MemcpyStepInv {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst0 n0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteRegionEffect s0 s [(dst0.toNat, n0.toNat)] ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

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
  have e1 := sourceBase_val
  have e2 := heapEnd_val
  omega

private theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have hal := panByteAlign_toNat64 a
  omega

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (d i : MlS) (x y a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i]) =
      some (.val (.word a))) :
    a = x + y := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  exact he.symm

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (d i : MlS) (x y c a : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y)))
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i, .const c]) =
      some (.val (.word a))) :
    a = x + y + c := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp] at he
  rw [← he, BitVec.add_assoc]

private theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.load .one e) = some val) :
    ∃ w : BitVec 64, val = .val (.word w) := by
  simp only [evalHOLExact] at he
  rcases hev : @evalHOLExact 64 F _ s.toExact h e with _ | ev
  · simp [hev] at he
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [hev, memLoadHOLExact] at he
      split at he
      · rcases hm : s.memory addr with ⟨w⟩
        rw [hm] at he
        split at he
        · injection he with hval
          exact ⟨w, hval.symm⟩
        · simp at he
      · simp at he
    · simp [hev] at he
    · simp [hev] at he

private theorem eval_notLower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (n0 iw k w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const k])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ (n0 < iw + k) := by
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by
    rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he
  exact hw he.symm

private theorem eval_lower_true {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (n0 iw w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    iw < n0 := by
  simp [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_contra hge
  simp [hge] at he
  exact hw he.symm

private theorem eval_lower_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (n0 iw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (he : @evalHOLExact 64 F _ s.toExact h
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word 0))) :
    n0.toNat ≤ iw.toNat := by
  simp only [evalHOLExact, hn, hi, Compiler.Encoders.Asm.wordCmpHOL] at he
  by_cases hlt : iw < n0
  · simp [hlt] at he
  · rw [BitVec.lt_def] at hlt; omega

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (_hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (dst0 + iw).toNat = dst0.toNat + iw.toNat ∧
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  have hS := sourceBase_val
  have hH := heapEnd_val
  have hdlt := dst0.isLt
  have hilt := iw.isLt
  have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢
    rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat :=
      BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, rfl, by omega, hdlo, by omega⟩

private theorem store_word_step0 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dst0 iw : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one srcExp)) = (none, post)) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ heapEnd ∧
    ByteRegionEffect s post [((dst0 + iw).toNat, 8)] ∧ post.locals = s.locals ∧ GuestInv post := by
  have hdom_pair : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ heapEnd := by
    have hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        (.load .one srcExp))).1 = none := by rw [hrun]
    rw [evaluateHOLFiniteState_store] at hnone
    split at hnone
    · rename_i address haddr
      have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
      subst ha
      split at hnone
      · rename_i val hval
        obtain ⟨w, rfl⟩ := eval_load_one_word s (h := fun a => Classical.propDecidable (s.memaddrs a))
          srcExp val hval
        split at hnone
        · rename_i mem hmem
          have hdom : s.memaddrs (dst0 + iw) := by
            simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
            by_contra hc; simp [hc] at hmem
          rw [hG.memaddrs] at hdom
          exact ordinaryDomain_bounds _ hdom
        · simp at hnone
      · simp at hnone
    · simp at hnone
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word hG.memaddrs hrun
    (fun v hv => eval_load_one_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) srcExp v hv)
    (fun addr haddr _ => by
      have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw addr hdst hi haddr
      subst ha
      exact ⟨((dst0 + iw).toNat, 8), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩)
  have hGp : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hG
  exact ⟨hdom_pair.1, hdom_pair.2, heff, hloc, hGp⟩

private theorem store_word_step_off {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dst0 iw c : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (srcExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        (.load .one srcExp)) = (none, post)) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 8 ≤ heapEnd ∧
    ByteRegionEffect s post [((dst0 + iw + c).toNat, 8)] ∧ post.locals = s.locals ∧ GuestInv post := by
  have hdom_pair : sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 8 ≤ heapEnd := by
    have hnone : (evaluateHOLFiniteState s
      (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        (.load .one srcExp))).1 = none := by rw [hrun]
    rw [evaluateHOLFiniteState_store] at hnone
    split at hnone
    · rename_i address haddr
      have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
      subst ha
      split at hnone
      · rename_i val hval
        obtain ⟨w, rfl⟩ := eval_load_one_word s (h := fun a => Classical.propDecidable (s.memaddrs a))
          srcExp val hval
        split at hnone
        · rename_i mem hmem
          have hdom : s.memaddrs (dst0 + iw + c) := by
            simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
            by_contra hc; simp [hc] at hmem
          rw [hG.memaddrs] at hdom
          exact ordinaryDomain_bounds _ hdom
        · simp at hnone
      · simp at hnone
    · simp at hnone
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word hG.memaddrs hrun
    (fun v hv => eval_load_one_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) srcExp v hv)
    (fun addr haddr _ => by
      have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw c addr hdst hi haddr
      subst ha
      exact ⟨((dst0 + iw + c).toNat, 8), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩)
  have hGp : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hG
  exact ⟨hdom_pair.1, hdom_pair.2, heff, hloc, hGp⟩

private theorem storeByte_step0 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dst0 iw : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        vExp) = (none, post)) :
    sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 1 ≤ heapEnd ∧
    ByteRegionEffect s post [((dst0 + iw).toNat, 1)] ∧ post.locals = s.locals ∧ GuestInv post := by
  have hdom_pair : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 1 ≤ heapEnd := by
    have hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
        vExp)).1 = none := by rw [hrun]
    rw [evaluateHOLFiniteState_storeByte] at hnone
    split at hnone
    · rename_i address haddr
      have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw address hdst hi haddr
      subst ha
      split at hnone
      · split at hnone
        · rename_i mem hmem
          have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw)) := by
            by_contra hc
            unfold panMemStoreByteWord8HOL at hmem
            dsimp only at hmem
            simp [hc] at hmem
          rw [hG.memaddrs] at hdom
          have hb := ordinaryDomain_bounds _ hdom
          have hal := byteAlign_bounds (dst0 + iw)
          omega
        · simp at hnone
      · simp at hnone
    · simp at hnone
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_storeByte hrun
    (fun addr haddr _ => by
      have ha := eval_add2_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw addr hdst hi haddr
      subst ha
      exact ⟨((dst0 + iw).toNat, 1), List.mem_singleton.2 rfl, le_refl _, by omega⟩)
  have hGp : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hG
  exact ⟨hdom_pair.1, hdom_pair.2, heff, hloc, hGp⟩

private theorem storeByte_step_off {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dst0 iw c : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (vExp : ExpHOL 64)
    (hrun : evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        vExp) = (none, post)) :
    sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 1 ≤ heapEnd ∧
    ByteRegionEffect s post [((dst0 + iw + c).toNat, 1)] ∧ post.locals = s.locals ∧ GuestInv post := by
  have hdom_pair : sourceBase ≤ (dst0 + iw + c).toNat ∧ (dst0 + iw + c).toNat + 1 ≤ heapEnd := by
    have hnone : (evaluateHOLFiniteState s
      (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const c])
        vExp)).1 = none := by rw [hrun]
    rw [evaluateHOLFiniteState_storeByte] at hnone
    split at hnone
    · rename_i address haddr
      have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw c address hdst hi haddr
      subst ha
      split at hnone
      · split at hnone
        · rename_i mem hmem
          have hdom : s.memaddrs (panByteAlignHOL (width := 64) (dst0 + iw + c)) := by
            by_contra hc
            unfold panMemStoreByteWord8HOL at hmem
            dsimp only at hmem
            simp [hc] at hmem
          rw [hG.memaddrs] at hdom
          have hb := ordinaryDomain_bounds _ hdom
          have hal := byteAlign_bounds (dst0 + iw + c)
          omega
        · simp at hnone
      · simp at hnone
    · simp at hnone
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_storeByte hrun
    (fun addr haddr _ => by
      have ha := eval_add3_locals s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (ofString "dst") (ofString "i") dst0 iw c addr hdst hi haddr
      subst ha
      exact ⟨((dst0 + iw + c).toNat, 1), List.mem_singleton.2 rfl, le_refl _, by omega⟩)
  have hGp : GuestInv post :=
    guestInv_congr heff.code heff.memaddrs heff.shMemaddrs heff.baseAddr hG
  exact ⟨hdom_pair.1, hdom_pair.2, heff, hloc, hGp⟩

private theorem setVar_lookup_ne {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

private theorem assign_i_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dst0 n0 iw k : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) = (none, post)) :
    ByteRegionEffect s post [(dst0.toNat, n0.toNat)] ∧
    post.code = s.code ∧ GuestInv post ∧
    post.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
    post.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
    post.locals.lookup (ofString "i") = some (.val (.word (iw + k))) := by
  rw [evaluateHOLFiniteState_assign] at hrun
  have hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const k]) = some (.val (.word (iw + k))) := by
    simp [evalHOLExact, evalListHOLExact, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [hev] at hrun
  dsimp only at hrun
  have hval : s.isValidValueHOLFinite .local (ofString "i") (.val (.word (iw + k))) = true := by
    simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hi,
      shapeOfHOLExact, shapeEqHOL]
  rw [hval] at hrun
  simp only [↓reduceIte, Prod.mk.injEq] at hrun
  obtain ⟨_, rfl⟩ := hrun
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩,
    rfl, guestInv_setVar _ _ s hG, ?_, ?_, ?_⟩
  · rw [show setKvarHOLFinite .local (ofString "i") (.val (.word (iw + k))) s =
        setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s from rfl,
      setVar_lookup_ne s (ofString "i") (ofString "dst") _ (by decide), hdst]
  · rw [show setKvarHOLFinite .local (ofString "i") (.val (.word (iw + k))) s =
        setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s from rfl,
      setVar_lookup_ne s (ofString "i") (ofString "n") _ (by decide), hn]
  · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem seq_eq_none {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.seq a b) = (none, post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none, mid) ∧ evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s a with ⟨r, mid⟩
  rw [hr] at h
  cases r with
  | none => exact ⟨mid, rfl, h⟩
  | some _ => simp at h

private theorem while_memcpy_inv {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreak body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      MemcpyStepInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      evaluateHOLFiniteState (decClockHOLFinite s) body = (none, post) →
      MemcpyStepInv s0 dst0 n0 post)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : MemcpyStepInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    MemcpyStepInv s0 dst0 n0 post ∧
      @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
        some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0
        simp at hrun
        subst hrun
        exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nb := evaluate_noBreak body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid := hbody s mid cw hinv hcond hnz hbr
            have hmk : mid.clock ≤ k := by
              change mid.clock ≤ s.clock - 1 at rem; omega
            exact ih mid hmk hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hz
        have hcw0 : cw = 0 := Classical.not_not.mp hz
        subst hcw0
        simp at hrun
        subst hrun
        exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem memcpy_step_loop1 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyStepInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0)
    (hrun : evaluateHOLFiniteState (decClockHOLFinite s)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8])
            (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 8])))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16])
              (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 16])))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24])
                (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 24])))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32])))))) =
      (none, post)) :
    MemcpyStepInv s0 dst0 n0 post := by
  obtain ⟨hc, hG, heff0, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a)) n0 iw 32 w hn hi hcond hw
  have hGd := guestInv_decClock s hG
  have heff_d : ByteRegionEffect s0 (decClockHOLFinite s) [(dst0.toNat, n0.toNat)] :=
    heff0.with_locals_clock s.locals (s.clock - 1)
  obtain ⟨s1, hr1, hrest1⟩ := seq_eq_none hrun
  obtain ⟨s2, hr2, hrest2⟩ := seq_eq_none hrest1
  obtain ⟨s3, hr3, hrest3⟩ := seq_eq_none hrest2
  obtain ⟨s4, hr4, hr5⟩ := seq_eq_none hrest3
  obtain ⟨hd0_lo, _, he1, hl1, hG1⟩ := store_word_step0 hGd dst0 iw hdst hi _ hr1
  obtain ⟨_, _, he2, hl2, hG2⟩ := store_word_step_off hG1 dst0 iw 8 (hl1 ▸ hdst) (hl1 ▸ hi) _ hr2
  obtain ⟨_, _, he3, hl3, hG3⟩ := store_word_step_off hG2 dst0 iw 16 (hl2 ▸ hl1 ▸ hdst) (hl2 ▸ hl1 ▸ hi) _ hr3
  obtain ⟨_, hd24_hi, he4, hl4, hG4⟩ := store_word_step_off hG3 dst0 iw 24
    (hl3 ▸ hl2 ▸ hl1 ▸ hdst) (hl3 ▸ hl2 ▸ hl1 ▸ hi) _ hr4
  have hH := heapEnd_val
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by have := (store_word_step0 hGd dst0 iw hdst hi _ hr1).2.1; change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have h8_hi := (store_word_step_off hG1 dst0 iw 8 (hl1 ▸ hdst) (hl1 ▸ hi) _ hr2).2.1
    rw [a8] at h8_hi
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have h16_hi := (store_word_step_off hG2 dst0 iw 16 (hl2 ▸ hl1 ▸ hdst) (hl2 ▸ hl1 ▸ hi) _ hr3).2.1
    rw [a16] at h16_hi
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0_lo, ?_⟩; rw [a24] at hd24_hi; change (dst0 + iw).toNat + 32 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hik32 : (32 : BitVec 64).toNat = 32 := rfl
  rw [hik32] at hik_eq
  have hm1 : ByteRegionEffect (decClockHOLFinite s) s1 [(dst0.toNat, n0.toNat)] :=
    he1.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm2 : ByteRegionEffect s1 s2 [(dst0.toNat, n0.toNat)] :=
    he2.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm3 : ByteRegionEffect s2 s3 [(dst0.toNat, n0.toNat)] :=
    he3.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm4 : ByteRegionEffect s3 s4 [(dst0.toNat, n0.toNat)] :=
    he4.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  obtain ⟨hm5, _, hG5, hdst5, hn5, hi5⟩ := assign_i_step hG4 dst0 n0 iw 32
    (hl4 ▸ hl3 ▸ hl2 ▸ hl1 ▸ hdst) (hl4 ▸ hl3 ▸ hl2 ▸ hl1 ▸ hn) (hl4 ▸ hl3 ▸ hl2 ▸ hl1 ▸ hi) hr5
  exact ⟨hG5.code, hG5, ((((heff_d.trans hm1).trans hm2).trans hm3).trans hm4).trans hm5,
    hdst5, hn5, iw + 32, hi5, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem memcpy_step_loop2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyStepInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0)
    (hrun : evaluateHOLFiniteState (decClockHOLFinite s)
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))) =
      (none, post)) :
    MemcpyStepInv s0 dst0 n0 post := by
  obtain ⟨_, hG, heff0, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a)) n0 iw 8 w hn hi hcond hw
  have hGd := guestInv_decClock s hG
  have heff_d : ByteRegionEffect s0 (decClockHOLFinite s) [(dst0.toNat, n0.toNat)] :=
    heff0.with_locals_clock s.locals (s.clock - 1)
  obtain ⟨s1, hr1, hr2⟩ := seq_eq_none hrun
  obtain ⟨hd0_lo, hd0_hi, he1, hl1, hG1⟩ := store_word_step0 hGd dst0 iw hdst hi _ hr1
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hik8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [hik8] at hik_eq
  have hm1 : ByteRegionEffect (decClockHOLFinite s) s1 [(dst0.toNat, n0.toNat)] :=
    he1.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  obtain ⟨hm2, _, hG2, hdst2, hn2, hi2⟩ := assign_i_step hG1 dst0 n0 iw 8
    (hl1 ▸ hdst) (hl1 ▸ hn) (hl1 ▸ hi) hr2
  exact ⟨hG2.code, hG2, (heff_d.trans hm1).trans hm2,
    hdst2, hn2, iw + 8, hi2, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem memcpy_step_loop3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyStepInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0)
    (hrun : evaluateHOLFiniteState (decClockHOLFinite s)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1])
            (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 1])))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2])
              (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 2])))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3])
                (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 3])))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4])
                  (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 4])))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5])
                    (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 5])))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6])
                      (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 6])))
                    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7])
                        (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i"), .const 7])))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))))))))) =
      (none, post)) :
    MemcpyStepInv s0 dst0 n0 post := by
  obtain ⟨_, hG, heff0, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hnl := eval_notLower_true s (h := fun a => Classical.propDecidable (s.memaddrs a)) n0 iw 8 w hn hi hcond hw
  have hGd := guestInv_decClock s hG
  have heff_d : ByteRegionEffect s0 (decClockHOLFinite s) [(dst0.toNat, n0.toNat)] :=
    heff0.with_locals_clock s.locals (s.clock - 1)
  have hH := heapEnd_val
  obtain ⟨s1, hr0, hrest1⟩ := seq_eq_none hrun
  obtain ⟨s2, hr1, hrest2⟩ := seq_eq_none hrest1
  obtain ⟨s3, hr2, hrest3⟩ := seq_eq_none hrest2
  obtain ⟨s4, hr3, hrest4⟩ := seq_eq_none hrest3
  obtain ⟨s5, hr4, hrest5⟩ := seq_eq_none hrest4
  obtain ⟨s6, hr5, hrest6⟩ := seq_eq_none hrest5
  obtain ⟨s7, hr6, hrest7⟩ := seq_eq_none hrest6
  obtain ⟨s8, hr7, hr8⟩ := seq_eq_none hrest7
  obtain ⟨hd0_lo, _, he0, hl1, hG1⟩ := storeByte_step0 hGd dst0 iw hdst hi _ hr0
  have hd1 := hl1 ▸ hdst; have hi1 := hl1 ▸ hi; have hn1 := hl1 ▸ hn
  obtain ⟨_, _, he1, hl2, hG2⟩ := storeByte_step_off hG1 dst0 iw 1 hd1 hi1 _ hr1
  have hd2 := hl2 ▸ hd1; have hi2 := hl2 ▸ hi1; have hn2 := hl2 ▸ hn1
  obtain ⟨_, _, he2, hl3, hG3⟩ := storeByte_step_off hG2 dst0 iw 2 hd2 hi2 _ hr2
  have hd3 := hl3 ▸ hd2; have hi3 := hl3 ▸ hi2; have hn3 := hl3 ▸ hn2
  obtain ⟨_, _, he3, hl4, hG4⟩ := storeByte_step_off hG3 dst0 iw 3 hd3 hi3 _ hr3
  have hd4 := hl4 ▸ hd3; have hi4 := hl4 ▸ hi3; have hn4 := hl4 ▸ hn3
  obtain ⟨_, _, he4, hl5, hG5⟩ := storeByte_step_off hG4 dst0 iw 4 hd4 hi4 _ hr4
  have hd5 := hl5 ▸ hd4; have hi5 := hl5 ▸ hi4; have hn5 := hl5 ▸ hn4
  obtain ⟨_, _, he5, hl6, hG6⟩ := storeByte_step_off hG5 dst0 iw 5 hd5 hi5 _ hr5
  have hd6 := hl6 ▸ hd5; have hi6 := hl6 ▸ hi5; have hn6 := hl6 ▸ hn5
  obtain ⟨_, _, he6, hl7, hG7⟩ := storeByte_step_off hG6 dst0 iw 6 hd6 hi6 _ hr6
  have hd7 := hl7 ▸ hd6; have hi7 := hl7 ▸ hi6; have hn7 := hl7 ▸ hn6
  obtain ⟨_, hb7_hi, he7, hl8, hG8⟩ := storeByte_step_off hG7 dst0 iw 7 hd7 hi7 _ hr7
  have hd8 := hl8 ▸ hd7; have hi8 := hl8 ▸ hi7; have hn8 := hl8 ▸ hn7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by have := (storeByte_step0 hGd dst0 iw hdst hi _ hr0).2.1; change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 := by
    have := (storeByte_step_off hG1 dst0 iw 1 hd1 hi1 _ hr1).2.1; rw [a1] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 := by
    have := (storeByte_step_off hG2 dst0 iw 2 hd2 hi2 _ hr2).2.1; rw [a2] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 := by
    have := (storeByte_step_off hG3 dst0 iw 3 hd3 hi3 _ hr3).2.1; rw [a3] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 := by
    have := (storeByte_step_off hG4 dst0 iw 4 hd4 hi4 _ hr4).2.1; rw [a4] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 := by
    have := (storeByte_step_off hG5 dst0 iw 5 hd5 hi5 _ hr5).2.1; rw [a5] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 := by
    have := (storeByte_step_off hG6 dst0 iw 6 hd6 hi6 _ hr6).2.1; rw [a6] at this
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨hd0_lo, ?_⟩; rw [a7] at hb7_hi; change (dst0 + iw).toNat + 8 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hik8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [hik8] at hik_eq
  have hm0 : ByteRegionEffect (decClockHOLFinite s) s1 [(dst0.toNat, n0.toNat)] :=
    he0.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm1 : ByteRegionEffect s1 s2 [(dst0.toNat, n0.toNat)] :=
    he1.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm2 : ByteRegionEffect s2 s3 [(dst0.toNat, n0.toNat)] :=
    he2.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm3 : ByteRegionEffect s3 s4 [(dst0.toNat, n0.toNat)] :=
    he3.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm4 : ByteRegionEffect s4 s5 [(dst0.toNat, n0.toNat)] :=
    he4.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm5 : ByteRegionEffect s5 s6 [(dst0.toNat, n0.toNat)] :=
    he5.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm6 : ByteRegionEffect s6 s7 [(dst0.toNat, n0.toNat)] :=
    he6.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  have hm7 : ByteRegionEffect s7 s8 [(dst0.toNat, n0.toNat)] :=
    he7.mono fun x hx => by rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  obtain ⟨hm8, _, hG9, hdst9, hn9, hi9⟩ := assign_i_step hG8 dst0 n0 iw 8 hd8 hn8 hi8 hr8
  exact ⟨hG9.code, hG9,
    ((((((((heff_d.trans hm0).trans hm1).trans hm2).trans hm3).trans hm4).trans hm5).trans hm6).trans hm7).trans hm8,
    hdst9, hn9, iw + 8, hi9, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem memcpy_step_loop4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : MemcpyStepInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0)
    (hrun : evaluateHOLFiniteState (decClockHOLFinite s)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) =
      (none, post)) :
    MemcpyStepInv s0 dst0 n0 post := by
  obtain ⟨_, hG, heff0, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  have hlt := eval_lower_true s (h := fun a => Classical.propDecidable (s.memaddrs a)) n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  have hGd := guestInv_decClock s hG
  have heff_d : ByteRegionEffect s0 (decClockHOLFinite s) [(dst0.toNat, n0.toNat)] :=
    heff0.with_locals_clock s.locals (s.clock - 1)
  obtain ⟨s1, hr1, hr2⟩ := seq_eq_none hrun
  obtain ⟨hd0_lo, hd0_hi, he1, hl1, hG1⟩ := storeByte_step0 hGd dst0 iw hdst hi _ hr1
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hm1 : ByteRegionEffect (decClockHOLFinite s) s1 [(dst0.toNat, n0.toNat)] :=
    he1.mono fun x hx => by
      rw [List.mem_singleton.1 hx]; exact ⟨_, List.mem_singleton.2 rfl, by omega, by omega⟩
  obtain ⟨hm2, _, hG2, hdst2, hn2, hi2⟩ := assign_i_step hG1 dst0 n0 iw 1
    (hl1 ▸ hdst) (hl1 ▸ hn) (hl1 ▸ hi) hr2
  exact ⟨hG2.code, hG2, (heff_d.trans hm1).trans hm2,
    hdst2, hn2, iw + 1, hi2, hle_ik, fun _ => ⟨hdlo, hdhi⟩⟩

private theorem memcpy_body_effect {F : Type} {entry post : PanSemStateFiniteExact 64 F}
    {dst0 n0 : BitVec 64} {v : ValueHOL 64}
    (hcode : entry.code = originalRuntimeCode) (hG : GuestInv entry)
    (hdst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : entry.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hn_pos : 0 < n0.toNat)
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) =
      (some (.returned v), post)) :
    ByteRegionEffect entry post [(dst0.toNat, n0.toNat)] ∧
    sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  have hc0 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
      (.const (0 : BitVec 64)) = some (.val (.word 0)) := rfl
  dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0 hrun
  rw [hc0] at hrun
  dsimp only at hrun
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only [OfNat.ofNat, BitVec.ofNat] at hsh0
  rw [hsh0, if_pos rfl] at hrun
  set s1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) entry with hs1
  dsimp only [BitVec.ofNat] at hs1
  have hinv1 : MemcpyStepInv entry dst0 n0 s1 := by
    refine ⟨hcode, guestInv_setVar _ _ entry hG,
      (ByteRegionEffect.refl entry _).with_locals_clock s1.locals entry.clock,
      ?_, ?_, 0, ?_, Nat.zero_le _, fun h => by simp at h⟩
    · rw [hs1, setVar_lookup_ne entry (ofString "i") (ofString "dst") _ (by decide), hdst]
    · rw [hs1, setVar_lookup_ne entry (ofString "i") (ofString "n") _ (by decide), hn]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [← hs1, evaluateHOLFiniteState_seq_line780] at hrun
  set iteProg : ProgHOL 64 := .ite _ _ .skip
  have hite_nrr : noReturnOrRaise iteProg = true := rfl
  rcases hite : evaluateHOLFiniteState s1 iteProg with ⟨r_ite, s2⟩
  rw [hite] at hrun
  cases r_ite with
  | some r_ite =>
    exfalso
    have hnr := evaluate_noReturnOrRaise iteProg hite_nrr s1
    rw [hite] at hnr
    injection hrun with h1 _
    exact hnr (Or.inl ⟨v, h1⟩)
  | none =>
    dsimp only at hrun
    have hinv2 : MemcpyStepInv entry dst0 n0 s2 := by
      dsimp only [iteProg] at hite
      rw [evaluateHOLFiniteState_ite] at hite
      split at hite
      · split at hite
        · rw [evaluateHOLFiniteState_skip] at hite
          injection hite with _ hs2; rw [← hs2]; exact hinv1
        · obtain ⟨m1, hw1, hw2⟩ := seq_eq_none hite
          have hm1 := (while_memcpy_inv _ _ rfl rfl memcpy_step_loop1 s1.clock s1 m1 le_rfl hinv1 hw1).1
          exact (while_memcpy_inv _ _ rfl rfl memcpy_step_loop2 m1.clock m1 s2 le_rfl hm1 hw2).1
      · simp at hite
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    set loop3 : ProgHOL 64 := .while _ _
    have hl3_nrr : noReturnOrRaise loop3 = true := rfl
    rcases hw3 : evaluateHOLFiniteState s2 loop3 with ⟨rw3, s3⟩
    rw [hw3] at hrun
    cases rw3 with
    | some _ =>
      exfalso
      have hnr := evaluate_noReturnOrRaise loop3 hl3_nrr s2
      rw [hw3] at hnr
      injection hrun with h1 _
      exact hnr (Or.inl ⟨v, h1⟩)
    | none =>
      dsimp only at hrun
      have hinv3 := (while_memcpy_inv _ _ rfl rfl memcpy_step_loop3 s2.clock s2 s3 le_rfl hinv2 hw3).1
      rw [evaluateHOLFiniteState_seq_line780] at hrun
      set loop4 : ProgHOL 64 := .while _ _
      have hl4_nrr : noReturnOrRaise loop4 = true := rfl
      rcases hw4 : evaluateHOLFiniteState s3 loop4 with ⟨rw4, s4⟩
      rw [hw4] at hrun
      cases rw4 with
      | some _ =>
        exfalso
        have hnr := evaluate_noReturnOrRaise loop4 hl4_nrr s3
        rw [hw4] at hnr
        injection hrun with h1 _
        exact hnr (Or.inl ⟨v, h1⟩)
      | none =>
        dsimp only at hrun
        obtain ⟨⟨_, _, heff4, _, hn4, iw, hi4, hle4, hdom4⟩, hcond4⟩ :=
          while_memcpy_inv _ _ rfl rfl memcpy_step_loop4 s3.clock s3 s4 le_rfl hinv3 hw4
        have hge4 := eval_lower_false s4 (h := fun a => Classical.propDecidable (s4.memaddrs a)) n0 iw hn4 hi4 hcond4
        have hi_eq : iw.toNat = n0.toNat := by omega
        obtain ⟨hdlo, hdhi⟩ := hdom4 (by omega)
        rw [hi_eq] at hdhi
        rw [evaluateHOLFiniteState_return] at hrun
        have hc0' : @evalHOLExact 64 F _ s4.toExact
            (fun a => Classical.propDecidable (s4.memaddrs a)) (.const (0 : BitVec 64)) =
            some (.val (.word 0)) := rfl
        dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0' hrun
        rw [hc0'] at hrun
        dsimp only at hrun
        have hsz0 : sizeOfShapeWithContextHOL s4.structs
            (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)))) ≤ 32 := by
          simp [shapeOfHOLExact]
        dsimp only [BitVec.ofNat] at hsz0
        rw [if_pos hsz0] at hrun
        injection hrun with _ hpost
        subst hpost
        exact ⟨heff4.with_locals_clock _ s4.clock, hdlo, hdhi⟩

/-! ### 4. Call-level `memcpy` combinator on sub-slices of `(out0.toNat, 192)` -/

private theorem memcpy_body_not_resumes_exn {F : Type} {entry post : PanSemStateFiniteExact 64 F}
    {e : MlS} {v : ValueHOL 64}
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memcpy) =
      (some (.exception e v), post))
    (hres : Resumes (some (.exception e v))) : False := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hrun
  rw [evaluateHOLFiniteState_dec_total] at hrun
  dsimp only at hrun
  have hc0 : @evalHOLExact 64 F _ entry.toExact
      (fun a => Classical.propDecidable (entry.memaddrs a)) (.const (0 : BitVec 64)) =
      some (.val (.word 0)) := rfl
  dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0 hrun
  rw [hc0] at hrun
  dsimp only at hrun
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only [OfNat.ofNat, BitVec.ofNat] at hsh0
  rw [hsh0, if_pos rfl] at hrun
  set m_s1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) entry with hms1
  dsimp only [BitVec.ofNat] at hms1
  rw [← hms1, evaluateHOLFiniteState_seq_line780] at hrun
  set pA : ProgHOL 64 := .ite _ _ .skip
  rcases hrA : evaluateHOLFiniteState m_s1 pA with ⟨rA, m_s2⟩
  rw [hrA] at hrun
  cases rA with
  | some x =>
    have hnrA := evaluate_noReturnOrRaise pA rfl m_s1
    rw [hrA] at hnrA
    dsimp only at hrun hnrA
    injection hrun with h1 _
    rw [h1] at hnrA
    exact hnrA hres
  | none =>
    dsimp only at hrun
    rw [evaluateHOLFiniteState_seq_line780] at hrun
    set pB : ProgHOL 64 := .while _ _
    rcases hrB : evaluateHOLFiniteState m_s2 pB with ⟨rB, m_s3⟩
    rw [hrB] at hrun
    cases rB with
    | some x =>
      have hnrB := evaluate_noReturnOrRaise pB rfl m_s2
      rw [hrB] at hnrB
      dsimp only at hrun hnrB
      injection hrun with h1 _
      rw [h1] at hnrB
      exact hnrB hres
    | none =>
      dsimp only at hrun
      rw [evaluateHOLFiniteState_seq_line780] at hrun
      set pC : ProgHOL 64 := .while _ _
      rcases hrC : evaluateHOLFiniteState m_s3 pC with ⟨rC, m_s4⟩
      rw [hrC] at hrun
      cases rC with
      | some x =>
        have hnrC := evaluate_noReturnOrRaise pC rfl m_s3
        rw [hrC] at hnrC
        dsimp only at hrun hnrC
        injection hrun with h1 _
        rw [h1] at hnrC
        exact hnrC hres
      | none =>
        dsimp only at hrun
        rw [evaluateHOLFiniteState_return] at hrun
        have hc0' : @evalHOLExact 64 F _ m_s4.toExact
            (fun a => Classical.propDecidable (m_s4.memaddrs a)) (.const (0 : BitVec 64)) =
            some (.val (.word 0)) := rfl
        dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0' hrun
        rw [hc0'] at hrun
        dsimp only at hrun
        injection hrun with h1 _
        split at h1 <;> simp at h1

private theorem call_memcpy_subregion {F : Type} {s : PanSemStateFiniteExact 64 F}
    {out0 : BitVec 64} {dstExp srcExp : ExpHOL 64} {off len : Nat}
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hdst_eval : ∀ d : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word d)) → d = out0 + BitVec.ofNat 64 off)
    (hlen_pos : 0 < len) (hsub : off + len ≤ 192)
    (hprev : 0 < off → sourceBase ≤ out0.toNat ∧ out0.toNat + off ≤ heapEnd)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [dstExp, srcExp, .const (BitVec.ofNat 64 len)])).1 ≠ some .timeOut) :
    let rp := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memcpy")
        [dstExp, srcExp, .const (BitVec.ofNat 64 len)])
    (rp.1 = none →
      ByteRegionEffect s rp.2 [(out0.toNat, 192)] ∧
      rp.2.code = originalRuntimeCode ∧ GuestInv rp.2 ∧
      rp.2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      sourceBase ≤ out0.toNat ∧ out0.toNat + (off + len) ≤ heapEnd) ∧
    (Resumes rp.1 → False) := by
  intro rp
  dsimp only [rp]
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, srcExp, .const (BitVec.ofNat 64 len)] with _ | values
  · exact ⟨fun h => by simp at h, not_resumes_error⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") values with
      _ | ⟨body', callee, ret'⟩
    · exact ⟨fun h => by simp at h, not_resumes_error⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hlook' : s.code.lookup (ofString "memcpy") =
            some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
              sourceFnBody Guest.Software.guestFn_memcpy, .one) := by
          rw [hcode]; exact lookup_memcpy
        have hcallee := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "memcpy")
          values body' callee ret' hl
        simp only [lookupCodeHOLExact, hlook'] at hcallee
        split at hcallee
        · injection hcallee with h_tup
          injection h_tup with hb_eq h_rest
          injection h_rest with hc_eq hr_eq
          subst hb_eq hr_eq
          simp only [evalListHOLFinite, evalListHOLExact] at hargs
          rcases hd_ev : @evalHOLExact 64 F _ s.toExact
              (fun a => Classical.propDecidable (s.memaddrs a)) dstExp with _ | dv
          · simp [hd_ev] at hargs
          · rcases hs_ev : @evalHOLExact 64 F _ s.toExact
                (fun a => Classical.propDecidable (s.memaddrs a)) srcExp with _ | sv
            · simp [hd_ev, hs_ev] at hargs
            · have hn_ev : @evalHOLExact 64 F _ s.toExact
                  (fun a => Classical.propDecidable (s.memaddrs a))
                  (.const (BitVec.ofNat 64 len)) = some (.val (.word (BitVec.ofNat 64 len))) := rfl
              simp only [hd_ev, hs_ev, hn_ev, Option.some.injEq] at hargs
              subst hargs
              rename_i hall_mc
              have hdv_word : ∃ dst0 : BitVec 64, dv = .val (.word dst0) := by
                rcases dv with ⟨⟨w⟩⟩ | _ | _
                · exact ⟨w, rfl⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hall_mc
                · simp [shapeOfHOLExact, shapeEqHOL] at hall_mc
              obtain ⟨dst0, rfl⟩ := hdv_word
              have hdst_eq := hdst_eval dst0 hd_ev
              have hc_dst : callee.lookup (ofString "dst") = some (.val (.word dst0)) := by
                rw [← hc_eq]
                have hne1 : ofString "dst" ≠ ofString "n" := by decide
                have hne2 : ofString "dst" ≠ ofString "src" := by decide
                simp [List.foldl, hne1, hne2]
              have hc_n : callee.lookup (ofString "n") =
                  some (.val (.word (BitVec.ofNat 64 len))) := by
                rw [← hc_eq]
                simp [List.foldl]
              let entry := callEntryStateHOLFinite s callee
              have hentry_G : GuestInv entry := guestInv_callEntry s callee hG
              have hentry_code : entry.code = originalRuntimeCode := hcode
              rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
                  (sourceFnBody Guest.Software.guestFn_memcpy) with ⟨res, bpost⟩
              simp only [hrun] at hnt ⊢
              cases res with
              | none =>
                exact ⟨fun h => by simp at h, not_resumes_error⟩
              | some r =>
                cases r with
                | returned v =>
                  dsimp only
                  have hlen_lt : len < 2 ^ 64 := by omega
                  have hlen_nat : (BitVec.ofNat 64 len).toNat = len :=
                    Nat.mod_eq_of_lt hlen_lt
                  obtain ⟨heff_b, hdlo, hdhi⟩ := memcpy_body_effect
                    (entry := entry) (post := bpost) (dst0 := dst0) (n0 := BitVec.ofNat 64 len)
                    hentry_code hentry_G hc_dst hc_n (by rw [hlen_nat]; exact hlen_pos) hrun
                  rw [hlen_nat] at heff_b hdhi
                  have hH := heapEnd_val
                  have hd_unwrap : dst0.toNat = out0.toNat + off ∧
                      sourceBase ≤ out0.toNat ∧ out0.toNat + (off + len) ≤ heapEnd := by
                    subst hdst_eq
                    by_cases hoff0 : off = 0
                    · subst hoff0
                      have hadd0 : out0 + BitVec.ofNat 64 0 = out0 := BitVec.add_zero out0
                      rw [hadd0] at hdlo hdhi ⊢
                      exact ⟨by omega, hdlo, by omega⟩
                    · obtain ⟨holo, hohi⟩ := hprev (by omega)
                      have hoff_lt : off < 2 ^ 64 := by omega
                      have hoff_nat : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt hoff_lt
                      have hadd : (out0 + BitVec.ofNat 64 off).toNat = out0.toNat + off := by
                        rw [BitVec.toNat_add_of_lt]
                        · rw [hoff_nat]
                        · rw [hoff_nat]; omega
                      exact ⟨hadd, holo, by omega⟩
                  obtain ⟨hd_nat, holo, hohi⟩ := hd_unwrap
                  have heff_entry : ByteRegionEffect s entry [(out0.toNat, 192)] :=
                    (ByteRegionEffect.refl s _).with_locals_clock callee (s.clock - 1)
                  have heff_b192 : ByteRegionEffect entry bpost [(out0.toNat, 192)] :=
                    heff_b.mono fun x hx => by
                      rw [List.mem_singleton.1 hx]
                      exact ⟨(out0.toNat, 192), List.mem_singleton.2 rfl,
                        by dsimp only; omega, by dsimp only; omega⟩
                  split
                  · refine ⟨fun _ => ?_, fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
                    have hGp := guestInv_with_locals_clock bpost s.locals bpost.clock
                      (guestInv_congr heff_b192.code heff_b192.memaddrs heff_b192.shMemaddrs
                        heff_b192.baseAddr hentry_G)
                    exact ⟨(heff_entry.trans heff_b192).with_locals_clock s.locals bpost.clock,
                      hGp.code, hGp, hout, holo, hohi⟩
                  · exact ⟨fun h => by simp at h, not_resumes_error⟩
                | exception e v =>
                  exact ⟨fun h => by simp at h,
                    fun hres => memcpy_body_not_resumes_exn hrun hres⟩
                | timeOut => exact absurd rfl hnt
                | «break» => exact ⟨fun h => by simp at h, not_resumes_error⟩
                | «continue» => exact ⟨fun h => by simp at h, not_resumes_error⟩
                | error => exact ⟨fun h => by simp at h, not_resumes_error⟩
                | finalFfi _ =>
                  exact ⟨fun h => by simp at h,
                    fun h => by rcases h with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        · simp at hcallee

/-! ### 5. Composable read-only prefix combinators and `wk_extract_deposit_data` -/

private theorem lookup_extract_deposit_data :
    originalRuntimeCode.lookup (ofString "extract_deposit_data") =
      some ([(ofString "data", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_extract_deposit_data, .one) :=
  lookup_of_guestAst_getElem 841 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extract_deposit_data) rfl

/-- Invariant carried across the read-only validation prefix after `mark := heap_mark()`:
`GuestInv`, `mark = hw`, `out = out_init`, `heap_ptr = hw`, and `ByteRegionEffect` holds on any
resuming continuation. -/
private def EddCheckCont {F : Type} (s_init : PanSemStateFiniteExact 64 F) (hw : BitVec 64)
    (prog : ProgHOL 64) : Prop :=
  ∀ s : PanSemStateFiniteExact 64 F,
    s.code = originalRuntimeCode → GuestInv s →
    s.globals = s_init.globals →
    s.locals.lookup (ofString "mark") = some (.val (.word hw)) →
    s.locals.lookup (ofString "out") = s_init.locals.lookup (ofString "out") →
    (evaluateHOLFiniteState s prog).1 ≠ some .timeOut →
    Resumes (evaluateHOLFiniteState s prog).1 →
    ByteRegionEffect s (evaluateHOLFiniteState s prog).2 [(locN s_init "out", 192)]

private theorem edd_dec {F : Type} {s_init : PanSemStateFiniteExact 64 F} {hw : BitVec 64}
    {name : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hnm_mark : ofString "mark" ≠ name) (hnm_out : ofString "out" ≠ name)
    (hbody : EddCheckCont s_init hw body) :
    EddCheckCont s_init hw (.dec name sh init body) := by
  intro s hcode hG hglob hmark hout hnt hres
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  revert hnt hres
  split <;> intro hnt hres
  · exfalso; exact not_resumes_error hres
  · rename_i v hv
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsh, ↓reduceIte] at hnt hres ⊢
      let s' := setVarHOLFinite name v s
      have hb := hbody s' hcode (guestInv_setVar name v s hG) hglob
        (by rw [setVar_lookup_ne s name _ v hnm_mark]; exact hmark)
        (by rw [setVar_lookup_ne s name _ v hnm_out]; exact hout)
        hnt hres
      exact (((ByteRegionEffect.refl s _).with_locals_clock s'.locals s.clock).trans hb).with_locals_clock
        ((s'.evaluateHOLFiniteState body).2.locals.resVarEq (name, s.locals.lookup name))
        (s'.evaluateHOLFiniteState body).2.clock
    · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
      exfalso; exact not_resumes_error hres

private theorem edd_decCall_ro {F : Type} {s_init : PanSemStateFiniteExact 64 F} {hw : BitVec 64}
    {fname name : MlS} {sh : ShapeHOL} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : ReadOnlyFn fname)
    (hnm_mark : ofString "mark" ≠ name) (hnm_out : ofString "out" ≠ name)
    (hcont : EddCheckCont s_init hw cont) :
    EddCheckCont s_init hw (.decCall name sh fname args cont) := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  intro s hcode hG hglob hmark hout hnt hres
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · have hargs' : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) args = none := hargs
    simp [evalListHOLFinite, hargs'] at hres
    exact absurd hres not_resumes_error
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · simp [hl] at hres; exact absurd hres not_resumes_error
    · simp only [hl] at hnt hres ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
          ret ret' values callee (by rw [hcode]; exact hlook) hl
        subst hsame
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hres ⊢
        have hentryEq : callEntryStateHOLFinite s callee =
            { s with locals := callee, clock := (callEntryStateHOLFinite s callee).clock } := by
          cases s; rfl
        cases res with
        | none => exfalso; exact not_resumes_error hres
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hnt hres ⊢
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh &&
                shapeEqHOL (shapeOfHOLExact v) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt hres ⊢
              have hro := hspec (callEntryStateHOLFinite s callee) hcode
                (guestInv_callEntry s callee hG) (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨v, rfl⟩)
              rw [hrun] at hro
              dsimp only at hro
              have hpost : post = { s with locals := post.locals, clock := post.clock } :=
                state_trans_locals_clock hentryEq hro
              let postCaller : PanSemStateFiniteExact 64 F :=
                { post with locals := s.locals }
              let cstate := setVarHOLFinite name v postCaller
              have hpostC : postCaller = { s with locals := s.locals, clock := post.clock } :=
                state_eq_with_locals_clock hpost s.locals post.clock
              have hGc : GuestInv cstate := by
                have hGp : GuestInv post := by
                  have := guestInv_evaluate (callEntryStateHOLFinite s callee) body'
                    (guestInv_callEntry s callee hG)
                  rw [hrun] at this; exact this
                exact guestInv_setVar name v postCaller
                  (guestInv_with_locals_clock post s.locals post.clock hGp)
              have hc_glob : cstate.globals = s_init.globals := by
                change post.globals = s_init.globals
                have : post.globals = s.globals := by rw [hpost]
                exact this.trans hglob
              have hc_mark : cstate.locals.lookup (ofString "mark") = some (.val (.word hw)) := by
                rw [setVar_lookup_ne postCaller name _ v hnm_mark]; exact hmark
              have hc_out : cstate.locals.lookup (ofString "out") =
                  s_init.locals.lookup (ofString "out") := by
                rw [setVar_lookup_ne postCaller name _ v hnm_out]; exact hout
              have heff1 : ByteRegionEffect s cstate [(locN s_init "out", 192)] := by
                have : ByteRegionEffect s { s with locals := cstate.locals, clock := post.clock }
                    [(locN s_init "out", 192)] :=
                  (ByteRegionEffect.refl s _).with_locals_clock cstate.locals post.clock
                have heq_cs : cstate = { s with locals := cstate.locals, clock := post.clock } := by
                  dsimp only [cstate]; rw [hpostC]; cases s; rfl
                rwa [← heq_cs] at this
              exact (heff1.trans (hcont cstate hGc.code hGc hc_glob hc_mark hc_out hnt hres)).with_locals_clock
                ((cstate.evaluateHOLFiniteState cont).2.locals.resVarEq (name, s.locals.lookup name))
                (cstate.evaluateHOLFiniteState cont).2.clock
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte] at hres
              exfalso; exact not_resumes_error hres
          | exception e v =>
            have hro := hspec (callEntryStateHOLFinite s callee) hcode
              (guestInv_callEntry s callee hG) (by rw [hrun]; simp) (by rw [hrun]; exact hres)
            rw [hrun] at hro
            dsimp only at hro
            have hpost : post = { s with locals := post.locals, clock := post.clock } :=
              state_trans_locals_clock hentryEq hro
            have hpostE := state_eq_with_locals_clock hpost post.emptyLocalsHOLFinite.locals post.clock
            have : ByteRegionEffect s { s with locals := post.emptyLocalsHOLFinite.locals, clock := post.clock }
                [(locN s_init "out", 192)] :=
              (ByteRegionEffect.refl s _).with_locals_clock post.emptyLocalsHOLFinite.locals post.clock
            have hpostE' : post.emptyLocalsHOLFinite =
                { s with locals := post.emptyLocalsHOLFinite.locals, clock := post.clock } := by
              simpa [emptyLocalsHOLFinite] using hpostE
            dsimp only
            rwa [← hpostE'] at this
          | timeOut => simp at hnt
          | «break» => exfalso; exact not_resumes_error hres
          | «continue» => exfalso; exact not_resumes_error hres
          | error => exfalso; exact not_resumes_error hres
          | finalFfi _ =>
            exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem edd_seq_ro {F : Type} {s_init : PanSemStateFiniteExact 64 F} {hw : BitVec 64}
    {a b : ProgHOL 64}
    (ha : ReadOnlyProg a)
    (ham : avoidsLocal (ofString "mark") a = true)
    (hao : avoidsLocal (ofString "out") a = true)
    (hb : EddCheckCont s_init hw b) :
    EddCheckCont s_init hw (.seq a b) := by
  intro s hcode hG hglob hmark hout hnt hres
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s a).1
  have hGm := guestInv_evaluate s a hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hr1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  simp only [hr1] at hmeta hGm hnt hres ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have ha_eq := ha s hcode hG (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at ha_eq
    dsimp only at ha_eq hnt hres ⊢
    have hmid_glob : mid.globals = s_init.globals := by
      have : mid.globals = s.globals := by rw [ha_eq]
      exact this.trans hglob
    have hmid_mark : mid.locals.lookup (ofString "mark") = some (.val (.word hw)) := by
      have hm := evaluate_avoidsLocal_flowing (ofString "mark") a ham s (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at hm; exact hm.trans hmark
    have hmid_out : mid.locals.lookup (ofString "out") = s_init.locals.lookup (ofString "out") := by
      have ho := evaluate_avoidsLocal_flowing (ofString "out") a hao s (by rw [hr1]; exact Or.inl rfl)
      rw [hr1] at ho; exact ho.trans hout
    have heff1 : ByteRegionEffect s mid [(locN s_init "out", 192)] := by
      have : ByteRegionEffect s { s with locals := mid.locals, clock := mid.clock }
          [(locN s_init "out", 192)] :=
        (ByteRegionEffect.refl s _).with_locals_clock mid.locals mid.clock
      rwa [← ha_eq] at this
    exact heff1.trans (hb mid (hmeta.trans hcode) hGm hmid_glob hmid_mark hmid_out hnt hres)
  | some r =>
    have ha_eq := ha s hcode hG (by rw [hr1]; exact hnt)
      (by rw [hr1]; exact Or.inr (Or.inr (Or.inr hres)))
    rw [hr1] at ha_eq
    dsimp only at ha_eq ⊢
    have : ByteRegionEffect s { s with locals := mid.locals, clock := mid.clock }
        [(locN s_init "out", 192)] :=
      (ByteRegionEffect.refl s _).with_locals_clock mid.locals mid.clock
    rwa [← ha_eq] at this

private theorem edd_tail {F : Type} (s_init : PanSemStateFiniteExact 64 F) (hw : BitVec 64)
    (hhp_init : s_init.globals.lookup (ofString "heap_ptr") = some (.val (.word hw))) :
    EddCheckCont s_init hw
      (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.seq (.ite (.cmp .equal (.var .local (ofString "ok")) (.const 0))
            (.raise (ofString "BlockErr") (.const 61)) .skip)
          (.seq (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "out"),
               .op .add [.var .local (ofString "data"), .const 192], .const 48])
            (.seq (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "out"), .const 48],
                 .op .add [.var .local (ofString "data"), .const 288], .const 32])
              (.seq (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "out"), .const 80],
                   .op .add [.var .local (ofString "data"), .const 352], .const 8])
                (.seq (.call (some (none, none)) (ofString "memcpy")
                    [.op .add [.var .local (ofString "out"), .const 88],
                     .op .add [.var .local (ofString "data"), .const 416], .const 96])
                  (.seq (.call (some (none, none)) (ofString "memcpy")
                      [.op .add [.var .local (ofString "out"), .const 184],
                       .op .add [.var .local (ofString "data"), .const 544], .const 8])
                    (.return (.const 0))))))))) := by
  intro s hcode hG hglob hmark hout hnt hres
  -- 1. `heap_release(mark)`:
  have hmeta1 := (PanRunBounded.evaluateHOLFiniteState_metadata s
    (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])).1
  have hG1 := guestInv_evaluate s
    (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hr_rel : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) with
    ⟨r_rel, m0⟩
  simp only [hr_rel] at hmeta1 hG1 hnt hres ⊢
  change m0.code = s.code at hmeta1
  have hrel_eq : m0 = { s with locals := m0.locals, clock := m0.clock } := by
    have := call_heap_release_noop s hw hcode (by rw [hglob]; exact hhp_init) hmark
      (by rw [hr_rel]; cases r_rel <;> simp; simpa using hnt)
    rw [hr_rel] at this; exact this
  have heff0 : ByteRegionEffect s m0 [(locN s_init "out", 192)] := by
    have : ByteRegionEffect s { s with locals := m0.locals, clock := m0.clock }
        [(locN s_init "out", 192)] :=
      (ByteRegionEffect.refl s _).with_locals_clock m0.locals m0.clock
    rwa [← hrel_eq] at this
  cases r_rel with
  | some _ => exact heff0
  | none =>
    dsimp only at hnt hres ⊢
    have hout_m0 : m0.locals.lookup (ofString "out") = s_init.locals.lookup (ofString "out") := by
      have hav := evaluate_avoidsLocal_flowing (ofString "out")
        (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
        rfl s (by rw [hr_rel]; exact Or.inl rfl)
      rw [hr_rel] at hav; exact hav.trans hout
    -- 2. `if ok == 0 { raise BlockErr 61 } else skip`:
    set pOk : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "ok")) (.const 0))
        (.raise (ofString "BlockErr") (.const 61)) .skip
    have hro_ok : ReadOnlyProg pOk :=
      ReadOnlyProg.ite _ (ReadOnlyProg.raise _ _) ReadOnlyProg.skip
    have hmeta2 := (PanRunBounded.evaluateHOLFiniteState_metadata m0 pOk).1
    have hG2 := guestInv_evaluate m0 pOk hG1
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hr_ok : evaluateHOLFiniteState m0 pOk with ⟨r_ok, c0⟩
    simp only [hr_ok] at hmeta2 hG2 hnt hres ⊢
    change c0.code = m0.code at hmeta2
    cases r_ok with
    | some _ =>
      have hok_eq := hro_ok m0 (hmeta1.trans hcode) hG1
        (by rw [hr_ok]; exact hnt) (by rw [hr_ok]; exact Or.inr (Or.inr (Or.inr hres)))
      rw [hr_ok] at hok_eq
      have heff_ok : ByteRegionEffect m0 c0 [(locN s_init "out", 192)] := by
        have : ByteRegionEffect m0 { m0 with locals := c0.locals, clock := c0.clock }
            [(locN s_init "out", 192)] :=
          (ByteRegionEffect.refl m0 _).with_locals_clock c0.locals c0.clock
        rwa [← hok_eq] at this
      exact heff0.trans heff_ok
    | none =>
      dsimp only at hnt hres ⊢
      have hok_eq := hro_ok m0 (hmeta1.trans hcode) hG1
        (by rw [hr_ok]; simp) (by rw [hr_ok]; exact Or.inl rfl)
      rw [hr_ok] at hok_eq
      have heff_ok : ByteRegionEffect m0 c0 [(locN s_init "out", 192)] := by
        have : ByteRegionEffect m0 { m0 with locals := c0.locals, clock := c0.clock }
            [(locN s_init "out", 192)] :=
          (ByteRegionEffect.refl m0 _).with_locals_clock c0.locals c0.clock
        rwa [← hok_eq] at this
      have hout_c0 : c0.locals.lookup (ofString "out") = s_init.locals.lookup (ofString "out") := by
        have hav := evaluate_avoidsLocal_flowing (ofString "out") pOk rfl m0
          (by rw [hr_ok]; exact Or.inl rfl)
        rw [hr_ok] at hav; exact hav.trans hout_m0
      have hc0_code : c0.code = originalRuntimeCode := hG2.code
      -- Extract `out0 : BitVec 64` from the first `memcpy` call!
      -- If `c0["out"]` is not a `.val (.word out0)`, `evalListHOLFinite` on `[.var .local "out", ...]`
      -- either fails (`error`) or fails shape check (`error`), which cannot satisfy `Resumes`!
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      set mc1 : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "out"), .op .add [.var .local (ofString "data"), .const 192], .const 48]
      have hout_word : (evaluateHOLFiniteState c0 mc1).1 = none →
          ∃ out0 : BitVec 64,
            c0.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
              out0.toNat = locN s_init "out" := by
        intro hmc1_none
        dsimp only [mc1] at hmc1_none
        rw [evaluateHOLFiniteState_call] at hmc1_none
        rcases ha1 : evalListHOLFinite c0
            (h := fun a => Classical.propDecidable (c0.memaddrs a))
            [.var .local (ofString "out"),
             .op .add [.var .local (ofString "data"), .const 192],
             .const 48] with _ | vals1
        · rw [ha1] at hmc1_none; simp at hmc1_none
        · simp only [ha1] at hmc1_none
          rcases hl1 : lookupCodeHOLFinite c0.code.lookup (ofString "memcpy") vals1 with
            _ | ⟨b1, cal1, r1⟩
          · simp [hl1] at hmc1_none
          · have hlk1 := lookupCodeHOLFinite_eq_some c0.code.lookup (ofString "memcpy")
              vals1 b1 cal1 r1 hl1
            have hlook_c0 : c0.code.lookup (ofString "memcpy") =
                some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
                  sourceFnBody Guest.Software.guestFn_memcpy, .one) := by
              rw [hc0_code]; exact lookup_memcpy
            simp only [lookupCodeHOLExact, hlook_c0] at hlk1
            simp only [evalListHOLFinite, evalListHOLExact, evalHOLExact] at ha1
            rcases ho_v : c0.locals.lookup (ofString "out") with _ | ov
            · simp [ho_v] at ha1
            · rcases ov with ⟨⟨w⟩⟩ | _ | _
              · refine ⟨w, rfl, ?_⟩
                have hs_out : s_init.locals.lookup (ofString "out") = some (.val (.word w)) :=
                  hout_c0.symm.trans ho_v
                simp [locN, hs_out]
              · simp only [ho_v] at ha1
                split at ha1
                · rename_i v0 vs0 hhead _
                  injection hhead with hv0
                  subst hv0
                  injection ha1 with hvals1
                  subst hvals1
                  cases vs0 with
                  | nil => simp at hlk1
                  | cons s_arg tl2 =>
                    cases tl2 with
                    | nil => simp at hlk1
                    | cons n_arg tl3 =>
                      cases tl3 with
                      | nil => simp [shapeOfHOLExact, shapeEqHOL] at hlk1
                      | cons _ _ => simp at hlk1
                · simp at ha1
              · simp only [ho_v] at ha1
                split at ha1
                · rename_i v0 vs0 hhead _
                  injection hhead with hv0
                  subst hv0
                  injection ha1 with hvals1
                  subst hvals1
                  cases vs0 with
                  | nil => simp at hlk1
                  | cons s_arg tl2 =>
                    cases tl2 with
                    | nil => simp at hlk1
                    | cons n_arg tl3 =>
                      cases tl3 with
                      | nil => simp [shapeOfHOLExact, shapeEqHOL] at hlk1
                      | cons _ _ => simp at hlk1
                · simp at ha1
      rcases hr_mc1 : evaluateHOLFiniteState c0 mc1 with ⟨r_mc1, c1⟩
      simp only [hr_mc1] at hnt hres ⊢
      cases r_mc1 with
      | some r_m =>
        exfalso
        dsimp only at hnt hres
        have hnt_mc1 : (evaluateHOLFiniteState c0 mc1).1 ≠ some .timeOut := by
          rw [hr_mc1]; exact hnt
        rcases ho_v : c0.locals.lookup (ofString "out") with _ | ov
        · dsimp only [mc1] at hr_mc1
          rw [evaluateHOLFiniteState_call] at hr_mc1
          have ha1 : evalListHOLFinite c0
              (h := fun a => Classical.propDecidable (c0.memaddrs a))
              [.var .local (ofString "out"),
               .op .add [.var .local (ofString "data"), .const 192],
               .const 48] = none := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ho_v]
          rw [ha1] at hr_mc1; dsimp only at hr_mc1
          injection hr_mc1 with hr_eq _
          injection hr_eq with hr_eq'; subst hr_eq'; exact not_resumes_error hres
        · rcases ov with ⟨⟨out0⟩⟩ | _ | _
          · have hsub1 := (call_memcpy_subregion (s := c0)
              (dstExp := .var .local (ofString "out"))
              (srcExp := .op .add [.var .local (ofString "data"), .const 192])
              (off := 0) (len := 48) hc0_code hG2 ho_v
              (fun d hd => by
                simp [evalHOLExact, ho_v] at hd
                have hadd0 : out0 + BitVec.ofNat 64 0 = out0 := BitVec.add_zero out0
                rw [hadd0]
                exact hd.symm)
              (by omega) (by omega) (fun h => by omega)
              hnt_mc1).2
            change Resumes (evaluateHOLFiniteState c0 mc1).1 → False at hsub1
            rw [hr_mc1] at hsub1
            exact hsub1 hres
          · dsimp only [mc1] at hr_mc1
            rw [evaluateHOLFiniteState_call] at hr_mc1
            rcases ha1 : evalListHOLFinite c0
                (h := fun a => Classical.propDecidable (c0.memaddrs a))
                [.var .local (ofString "out"),
                 .op .add [.var .local (ofString "data"), .const 192],
                 .const 48] with _ | vals1
            · rw [ha1] at hr_mc1; dsimp only at hr_mc1
              injection hr_mc1 with hr_eq _; injection hr_eq with hr_eq'; subst hr_eq'
              exact not_resumes_error hres
            · rw [ha1] at hr_mc1; dsimp only at hr_mc1
              have hl1 : lookupCodeHOLFinite c0.code.lookup (ofString "memcpy") vals1 = none := by
                rw [lookupCodeHOLFinite_eq_none_iff]
                have hlook_c0 : c0.code.lookup (ofString "memcpy") =
                    some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
                      sourceFnBody Guest.Software.guestFn_memcpy, .one) := by
                  rw [hc0_code]; exact lookup_memcpy
                simp only [evalListHOLFinite, evalListHOLExact, evalHOLExact, ho_v] at ha1
                split at ha1
                · rename_i v0 vs0 hhead _
                  injection hhead with hv0; subst hv0
                  injection ha1 with hvals1; subst hvals1
                  cases vs0 with
                  | nil => simp [lookupCodeHOLExact, hlook_c0]
                  | cons s_arg tl2 =>
                    cases tl2 with
                    | nil => simp [lookupCodeHOLExact, hlook_c0]
                    | cons n_arg tl3 =>
                      cases tl3 with
                      | nil => simp [lookupCodeHOLExact, hlook_c0, shapeOfHOLExact, shapeEqHOL]
                      | cons _ _ => simp [lookupCodeHOLExact, hlook_c0]
                · simp at ha1
              rw [hl1] at hr_mc1; dsimp only at hr_mc1
              injection hr_mc1 with hr_eq _; injection hr_eq with hr_eq'; subst hr_eq'
              exact not_resumes_error hres
          · dsimp only [mc1] at hr_mc1
            rw [evaluateHOLFiniteState_call] at hr_mc1
            rcases ha1 : evalListHOLFinite c0
                (h := fun a => Classical.propDecidable (c0.memaddrs a))
                [.var .local (ofString "out"),
                 .op .add [.var .local (ofString "data"), .const 192],
                 .const 48] with _ | vals1
            · rw [ha1] at hr_mc1; dsimp only at hr_mc1
              injection hr_mc1 with hr_eq _; injection hr_eq with hr_eq'; subst hr_eq'
              exact not_resumes_error hres
            · rw [ha1] at hr_mc1; dsimp only at hr_mc1
              have hl1 : lookupCodeHOLFinite c0.code.lookup (ofString "memcpy") vals1 = none := by
                rw [lookupCodeHOLFinite_eq_none_iff]
                have hlook_c0 : c0.code.lookup (ofString "memcpy") =
                    some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
                      sourceFnBody Guest.Software.guestFn_memcpy, .one) := by
                  rw [hc0_code]; exact lookup_memcpy
                simp only [evalListHOLFinite, evalListHOLExact, evalHOLExact, ho_v] at ha1
                split at ha1
                · rename_i v0 vs0 hhead _
                  injection hhead with hv0; subst hv0
                  injection ha1 with hvals1; subst hvals1
                  cases vs0 with
                  | nil => simp [lookupCodeHOLExact, hlook_c0]
                  | cons s_arg tl2 =>
                    cases tl2 with
                    | nil => simp [lookupCodeHOLExact, hlook_c0]
                    | cons n_arg tl3 =>
                      cases tl3 with
                      | nil => simp [lookupCodeHOLExact, hlook_c0, shapeOfHOLExact, shapeEqHOL]
                      | cons _ _ => simp [lookupCodeHOLExact, hlook_c0]
                · simp at ha1
              rw [hl1] at hr_mc1; dsimp only at hr_mc1
              injection hr_mc1 with hr_eq _; injection hr_eq with hr_eq'; subst hr_eq'
              exact not_resumes_error hres
      | none =>
        dsimp only at hnt hres ⊢
        obtain ⟨out0, hout0_c0, hout0_nat⟩ := hout_word (by rw [hr_mc1])
        rw [← hout0_nat]
        have hs1 := call_memcpy_subregion (s := c0)
          (dstExp := .var .local (ofString "out"))
          (srcExp := .op .add [.var .local (ofString "data"), .const 192])
          (off := 0) (len := 48) hc0_code hG2 hout0_c0
          (fun d hd => by
            simp [evalHOLExact, hout0_c0] at hd
            have hadd0 : out0 + BitVec.ofNat 64 0 = out0 := BitVec.add_zero out0
            rw [hadd0]
            exact hd.symm)
          (by omega) (by omega) (fun h => by omega)
          (by change (evaluateHOLFiniteState c0 mc1).1 ≠ some .timeOut; rw [hr_mc1]; simp)
        dsimp only [OfNat.ofNat, BitVec.ofNat] at hs1
        dsimp only [mc1, OfNat.ofNat, BitVec.ofNat] at hr_mc1
        rw [hr_mc1] at hs1
        obtain ⟨heff_mc1, hc1_code, hGc1, hout_c1, holo1, hohi1⟩ := hs1.1 rfl
        have eval_out_add : ∀ {st : PanSemStateFiniteExact 64 F} (c d : BitVec 64),
            st.locals.lookup (ofString "out") = some (.val (.word out0)) →
            @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
              (.op .add [.var .local (ofString "out"), .const c]) = some (.val (.word d)) →
            d = out0 + c := by
          intro st c d ho hd
          simp [evalHOLExact, evalListHOLExact, ho, valueIsWord, valueWord, wordOpHOL, wordOp] at hd
          exact hd.symm
        -- mc2: off = 48, len = 32
        rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
        set mc2 : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "out"), .const 48],
           .op .add [.var .local (ofString "data"), .const 288], .const 32]
        rcases hr_mc2 : evaluateHOLFiniteState c1 mc2 with ⟨r_mc2, c2⟩
        simp only [hr_mc2] at hnt hres ⊢
        have hs2 := call_memcpy_subregion (s := c1)
          (dstExp := .op .add [.var .local (ofString "out"), .const 48])
          (srcExp := .op .add [.var .local (ofString "data"), .const 288])
          (off := 48) (len := 32) hc1_code hGc1 hout_c1
          (fun d hd => eval_out_add 48 d hout_c1 hd)
          (by omega) (by omega) (fun _ => ⟨holo1, hohi1⟩)
          (by change (evaluateHOLFiniteState c1 mc2).1 ≠ some .timeOut
              rw [hr_mc2]; cases r_mc2 <;> [simp; exact hnt])
        dsimp only [OfNat.ofNat, BitVec.ofNat] at hs2
        dsimp only [mc2, OfNat.ofNat, BitVec.ofNat] at hr_mc2
        rw [hr_mc2] at hs2
        cases r_mc2 with
        | some _ => dsimp only at hres; exfalso; exact hs2.2 hres
        | none =>
          dsimp only at hnt hres ⊢
          obtain ⟨heff_mc2, hc2_code, hGc2, hout_c2, holo2, hohi2⟩ := hs2.1 rfl
          -- mc3: off = 80, len = 8
          rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
          set mc3 : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "out"), .const 80],
             .op .add [.var .local (ofString "data"), .const 352], .const 8]
          rcases hr_mc3 : evaluateHOLFiniteState c2 mc3 with ⟨r_mc3, c3⟩
          simp only [hr_mc3] at hnt hres ⊢
          have hs3 := call_memcpy_subregion (s := c2)
            (dstExp := .op .add [.var .local (ofString "out"), .const 80])
            (srcExp := .op .add [.var .local (ofString "data"), .const 352])
            (off := 80) (len := 8) hc2_code hGc2 hout_c2
            (fun d hd => eval_out_add 80 d hout_c2 hd)
            (by omega) (by omega) (fun _ => ⟨holo2, hohi2⟩)
            (by change (evaluateHOLFiniteState c2 mc3).1 ≠ some .timeOut
                rw [hr_mc3]; cases r_mc3 <;> [simp; exact hnt])
          dsimp only [OfNat.ofNat, BitVec.ofNat] at hs3
          dsimp only [mc3, OfNat.ofNat, BitVec.ofNat] at hr_mc3
          rw [hr_mc3] at hs3
          cases r_mc3 with
          | some _ => dsimp only at hres; exfalso; exact hs3.2 hres
          | none =>
            dsimp only at hnt hres ⊢
            obtain ⟨heff_mc3, hc3_code, hGc3, hout_c3, holo3, hohi3⟩ := hs3.1 rfl
            -- mc4: off = 88, len = 96
            rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
            set mc4 : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "out"), .const 88],
               .op .add [.var .local (ofString "data"), .const 416], .const 96]
            rcases hr_mc4 : evaluateHOLFiniteState c3 mc4 with ⟨r_mc4, c4⟩
            simp only [hr_mc4] at hnt hres ⊢
            have hs4 := call_memcpy_subregion (s := c3)
              (dstExp := .op .add [.var .local (ofString "out"), .const 88])
              (srcExp := .op .add [.var .local (ofString "data"), .const 416])
              (off := 88) (len := 96) hc3_code hGc3 hout_c3
              (fun d hd => eval_out_add 88 d hout_c3 hd)
              (by omega) (by omega) (fun _ => ⟨holo3, hohi3⟩)
              (by change (evaluateHOLFiniteState c3 mc4).1 ≠ some .timeOut
                  rw [hr_mc4]; cases r_mc4 <;> [simp; exact hnt])
            dsimp only [OfNat.ofNat, BitVec.ofNat] at hs4
            dsimp only [mc4, OfNat.ofNat, BitVec.ofNat] at hr_mc4
            rw [hr_mc4] at hs4
            cases r_mc4 with
            | some _ => dsimp only at hres; exfalso; exact hs4.2 hres
            | none =>
              dsimp only at hnt hres ⊢
              obtain ⟨heff_mc4, hc4_code, hGc4, hout_c4, holo4, hohi4⟩ := hs4.1 rfl
              -- mc5: off = 184, len = 8
              rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
              set mc5 : ProgHOL 64 := .call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "out"), .const 184],
                 .op .add [.var .local (ofString "data"), .const 544], .const 8]
              rcases hr_mc5 : evaluateHOLFiniteState c4 mc5 with ⟨r_mc5, c5⟩
              simp only [hr_mc5] at hnt hres ⊢
              have hs5 := call_memcpy_subregion (s := c4)
                (dstExp := .op .add [.var .local (ofString "out"), .const 184])
                (srcExp := .op .add [.var .local (ofString "data"), .const 544])
                (off := 184) (len := 8) hc4_code hGc4 hout_c4
                (fun d hd => eval_out_add 184 d hout_c4 hd)
                (by omega) (by omega) (fun _ => ⟨holo4, hohi4⟩)
                (by change (evaluateHOLFiniteState c4 mc5).1 ≠ some .timeOut
                    rw [hr_mc5]; cases r_mc5 <;> [simp; exact hnt])
              dsimp only [OfNat.ofNat, BitVec.ofNat] at hs5
              dsimp only [mc5, OfNat.ofNat, BitVec.ofNat] at hr_mc5
              rw [hr_mc5] at hs5
              cases r_mc5 with
              | some _ => dsimp only at hres; exfalso; exact hs5.2 hres
              | none =>
                dsimp only at hnt hres ⊢
                obtain ⟨heff_mc5, _, _, _, _, _⟩ := hs5.1 rfl
                -- Final `return 0`:
                rw [evaluateHOLFiniteState_return]
                have hc0_ev : @evalHOLExact 64 F _ c5.toExact
                    (fun a => Classical.propDecidable (c5.memaddrs a)) (.const (0 : BitVec 64)) =
                    some (.val (.word 0)) := rfl
                dsimp only [OfNat.ofNat, BitVec.ofNat] at hc0_ev ⊢
                rw [hc0_ev]
                dsimp only
                simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL, Nat.reduceLeDiff, ↓reduceIte]
                have heff_ret : ByteRegionEffect c5
                    c5.emptyLocalsHOLFinite [(out0.toNat, 192)] :=
                  (ByteRegionEffect.refl c5 _).with_locals_clock c5.emptyLocalsHOLFinite.locals c5.clock
                rw [← hout0_nat] at heff0 heff_ok
                exact ((((((heff0.trans heff_ok).trans heff_mc1).trans heff_mc2).trans
                  heff_mc3).trans heff_mc4).trans heff_mc5).trans heff_ret

private theorem seq_ro_before {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b : ProgHOL 64}
    (ha : ReadOnlyProg a)
    (hb : ∀ mid : PanSemStateFiniteExact 64 F,
      mid.code = originalRuntimeCode → GuestInv mid →
      mid = { s with locals := mid.locals, clock := mid.clock } →
      (evaluateHOLFiniteState s a).1 = none →
      (evaluateHOLFiniteState s a).2 = mid →
      (evaluateHOLFiniteState mid b).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState mid b).1 →
      ByteRegionEffect mid (evaluateHOLFiniteState mid b).2 [(locN s "out", 192)])
    (hcode : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s (.seq a b)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.seq a b)).1) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq a b)).2 [(locN s "out", 192)] := by
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s a).1
  have hGm := guestInv_evaluate s a hG
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hr1 : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  simp only [hr1] at hmeta hGm hnt hres ⊢
  change mid.code = s.code at hmeta
  cases r1 with
  | none =>
    have ha_eq := ha s hcode hG (by rw [hr1]; simp) (by rw [hr1]; exact Or.inl rfl)
    rw [hr1] at ha_eq
    dsimp only at ha_eq hnt hres ⊢
    have heff1 : ByteRegionEffect s mid [(locN s "out", 192)] := by
      have : ByteRegionEffect s { s with locals := mid.locals, clock := mid.clock } [(locN s "out", 192)] :=
        (ByteRegionEffect.refl s _).with_locals_clock mid.locals mid.clock
      rwa [← ha_eq] at this
    exact heff1.trans (hb mid (hmeta.trans hcode) hGm ha_eq (by rw [hr1]) (by rw [hr1]) hnt hres)
  | some r =>
    have ha_eq := ha s hcode hG (by rw [hr1]; exact hnt)
      (by rw [hr1]; exact Or.inr (Or.inr (Or.inr hres)))
    rw [hr1] at ha_eq
    dsimp only at ha_eq ⊢
    have : ByteRegionEffect s { s with locals := mid.locals, clock := mid.clock } [(locN s "out", 192)] :=
      (ByteRegionEffect.refl s _).with_locals_clock mid.locals mid.clock
    rwa [← ha_eq] at this

/-- `extract_deposit_data` (AST line 32212): relational world step with output region. -/
theorem «wk_extract_deposit_data» :
    WorldKeeps WorldOK (fun s => [(locN s "out", 192)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "extract_deposit_data") := by
  refine ⟨_, _, _, lookup_extract_deposit_data, ?_⟩
  intro F s hcode hW _hlookup hnt hres
  apply ByteRegionEffect.to_worldStep_R hW
  obtain ⟨hG, hA⟩ := hW.1
  obtain ⟨hw, hglob_hp, _⟩ := global_heap_ptr_word s hA
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_extract_deposit_data,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt hres ⊢
  refine seq_ro_before
    (ReadOnlyProg.ite _ (ReadOnlyProg.raise _ _) ReadOnlyProg.skip)
    (fun s1 hc1 hG1 hs1eq ha1none ha1post hnt1 hres1 => ?_) hcode hG hnt hres
  have hout_s1 : s1.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
    have hav := evaluate_avoidsLocal_flowing (ofString "out") _ rfl s (Or.inl ha1none)
    rw [ha1post] at hav; exact hav
  have hglob_s1 : s1.globals = s.globals := by rw [hs1eq]
  have hhp_s1 : s1.globals.lookup (ofString "heap_ptr") = some (.val (.word hw)) := by
    rw [hglob_s1]; exact hglob_hp
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt1 hres1 ⊢
  have hargs_hm : evalListHOLFinite s1
      (h := fun a => Classical.propDecidable (s1.memaddrs a)) [] = some [] := rfl
  rw [hargs_hm] at hnt1 hres1 ⊢
  dsimp only at hnt1 hres1 ⊢
  rcases hl_hm : lookupCodeHOLFinite s1.code.lookup (ofString "heap_mark") [] with
    _ | ⟨body_hm, callee_hm, ret_hm⟩
  · simp [hl_hm] at hres1; exact absurd hres1 not_resumes_error
  · simp only [hl_hm] at hnt1 hres1 ⊢
    by_cases hz1 : s1.clock = 0
    · simp [hz1] at hnt1
    · simp only [hz1, ↓reduceIte] at hnt1 hres1 ⊢
      have hlook_hm : s1.code.lookup (ofString "heap_mark") =
          some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) := by
        rw [hc1]; exact lookup_heap_mark
      have hcal_hm := lookupCodeHOLFinite_eq_some s1.code.lookup (ofString "heap_mark")
        [] body_hm callee_hm ret_hm hl_hm
      simp only [lookupCodeHOLExact, hlook_hm] at hcal_hm
      split at hcal_hm
      · injection hcal_hm with h_tup
        injection h_tup with hb_eq h_rest
        injection h_rest with _ hr_eq
        subst hb_eq hr_eq
        let entry_hm := callEntryStateHOLFinite s1 callee_hm
        have hm_eval : evaluateHOLFiniteState entry_hm
            (sourceFnBody Guest.Software.guestFn_heap_mark) =
            (some (.returned (.val (.word hw))), entry_hm.emptyLocalsHOLFinite) := by
          dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_mark,
            InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
            InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
          rw [evaluateHOLFiniteState_return]
          have hev : @evalHOLExact 64 F _ entry_hm.toExact
              (fun a => Classical.propDecidable (entry_hm.memaddrs a))
              (.var .global (ofString "heap_ptr")) = some (.val (.word hw)) := by
            simp [evalHOLExact, entry_hm, callEntryStateHOLFinite, hhp_s1]
          rw [hev]
          simp [shapeOfHOLExact]
        rw [hm_eval] at hnt1 hres1 ⊢
        have hsh_hm : (shapeEqHOL (shapeOfHOLExact (.val (.word hw))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hw))) .one) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        simp only [hsh_hm, ↓reduceIte] at hnt1 hres1 ⊢
        set s2 := setVarHOLFinite (ofString "mark") (.val (.word hw))
          { entry_hm.emptyLocalsHOLFinite with locals := s1.locals } with hs2
        have hG2 : GuestInv s2 :=
          guestInv_setVar _ _ _ (guestInv_with_locals_clock entry_hm s1.locals
            entry_hm.clock (guestInv_callEntry s1 callee_hm hG1))
        have heff_12 : ByteRegionEffect s1 s2 [(locN s "out", 192)] :=
          (ByteRegionEffect.refl s1 _).with_locals_clock s2.locals entry_hm.clock
        have hmark_s2 : s2.locals.lookup (ofString "mark") = some (.val (.word hw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hout_s2 : s2.locals.lookup (ofString "out") = s.locals.lookup (ofString "out") := by
          rw [hs2, setVar_lookup_ne _ (ofString "mark") (ofString "out") _ (by decide)]
          exact hout_s1
        set contProg : ProgHOL 64 := .dec (ofString "ok") _ _ _
        change ByteRegionEffect s1
          { (evaluateHOLFiniteState s2 contProg).2 with
            locals := (evaluateHOLFiniteState s2 contProg).2.locals.resVarEq
              (ofString "mark", s1.locals.lookup (ofString "mark")) } [(locN s "out", 192)]
        have hcont_all : EddCheckCont s hw contProg := by
          dsimp only [contProg]
          refine edd_dec (by decide) (by decide) ?_
          refine edd_decCall_ro ro_is_zero_bytes (by decide) (by decide) ?_
          refine edd_dec (by decide) (by decide) ?_
          refine edd_decCall_ro ro_ld_be64 (by decide) (by decide) ?_
          refine edd_seq_ro (ReadOnlyProg.call_local ro_is_zero_bytes _ _) rfl rfl ?_
          refine edd_seq_ro (ReadOnlyProg.ite _ (ReadOnlyProg.assign_local _ _) ReadOnlyProg.skip) rfl rfl ?_
          repeat' (first
            | refine edd_seq_ro (ReadOnlyProg.call_local ro_is_zero_bytes _ _) rfl rfl ?_
            | refine edd_seq_ro (ReadOnlyProg.call_local ro_ld_be64 _ _) rfl rfl ?_
            | refine edd_seq_ro (ReadOnlyProg.ite _ (ReadOnlyProg.assign_local _ _) ReadOnlyProg.skip) rfl rfl ?_)
          exact edd_tail s hw hglob_hp
        exact (heff_12.trans (hcont_all s2 hG2.code hG2 hglob_s1 hmark_s2 hout_s2 hnt1 hres1)).with_locals_clock
          ((evaluateHOLFiniteState s2 contProg).2.locals.resVarEq
            (ofString "mark", s1.locals.lookup (ofString "mark")))
          (evaluateHOLFiniteState s2 contProg).2.clock
      · simp at hcal_hm

end InitECandidate.Solver.Wave8Contracts.M05
