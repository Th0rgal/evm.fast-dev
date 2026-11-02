import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.GuestTrapOutcomes
import Guest.SoftwareAst

/-! `dm_encode_withdrawal_rlp`: `encode_withdrawal_rlp` resumes only if `(wd, 1)` lies in the
memory domain (`[sourceBase, heapEnd)`).

AST index 838 (`Guest/SoftwareAst.lean:32114`):
`decCall "buf" .one "alloc" [64]`
`  (dec "p" .one (buf + 9)`
`    (decCall "w" .one "rlp_encode_word" [p, loadByte(wd) | ...]`
`      ...))`
`alloc` either returns a word or calls `trap_with(1)` (which never resumes).
After `alloc` returns and `p` is declared, evaluating the arguments of `rlp_encode_word` evaluates
`loadByte(wd)`, which succeeds only when `panByteAlignHOL wd ∈ s.memaddrs = ordinaryDomain`,
forcing `sourceBase ≤ wd < heapEnd`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.M21

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

private def Resumes (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

private def ResumesInDomain (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Ivl) (fname : MlS) :
    Prop :=
  FunSpec GuestInv (fun s r _ => Resumes r → 0 < (R s).2 → Inside (R s) sourceBase heapEnd) fname

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

private theorem not_resumes_error : ¬ Resumes (some .error) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem not_resumes_timeOut : ¬ Resumes (some .timeOut) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem not_resumes_finalFfi {ev} :
    ¬ Resumes (some (.finalFfi ev)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h

private theorem call_trap_with_not_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (args : List (ExpHOL 64)) :
    ¬ Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "trap_with") args)).1 := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, ret'⟩
    · exact not_resumes_error
    · dsimp only
      split
      · exact not_resumes_timeOut
      · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "trap_with")
          _ _ _ _ _ vals callee (by rw [hcode]; exact lookup_trap_with) hl
        subst hsame
        have htr := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite s callee)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, post⟩
        rw [hrun] at htr
        obtain ⟨hnn, hnr, hne⟩ := htr
        dsimp only at hnn hnr hne ⊢
        cases res with
        | none => exact absurd rfl hnn
        | some r =>
          cases r with
          | returned v => exact absurd rfl (hnr v)
          | timeOut => exact not_resumes_timeOut
          | «break» => exact not_resumes_error
          | «continue» => exact not_resumes_error
          | error => exact not_resumes_error
          | exception e v =>
            rintro (⟨w, hw⟩ | ⟨e', w, hew, hntrap⟩)
            · simp at hw
            · injection hew with hew
              injection hew with he1 _
              exact hne e' v hntrap (by rw [he1])
          | finalFfi _ => exact not_resumes_finalFfi

private theorem ite_trap_with_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (cond : ExpHOL 64) (args : List (ExpHOL 64))
    (r : Option (PanSemResultExact 64)) (m : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (.ite cond (.call (some (none, none)) (ofString "trap_with") args) .skip) = (r, m)) :
    r = none ∨ ¬ Resumes r := by
  rw [evaluateHOLFiniteState_ite] at hr
  split at hr
  · split at hr
    · rw [evaluateHOLFiniteState_skip] at hr
      injection hr with hr _
      exact Or.inl hr.symm
    · have htr := call_trap_with_not_resumes s hcode args
      rw [hr] at htr
      exact Or.inr htr
  · injection hr with hr _
    subst hr
    exact Or.inr not_resumes_error

private theorem alloc_resumes_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1) :
    ∃ w, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 = some (.returned w) := by
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_alloc,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; exact absurd h not_resumes_error
  · rename_i pv _
    split
    · set s1 := setVarHOLFinite (ofString "p") pv s
      rw [evaluateHOLFiniteState_seq_line780]
      have hm1 := (PanRunBounded.evaluateHOLFiniteState_metadata s1
        (.ite (.cmp .lower (.op .sub [.const (BitVec.ofNat 64 2952790016), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const (BitVec.ofNat 64 1)])
          .skip)).1
      rcases hr1 : evaluateHOLFiniteState s1 _ with ⟨r1, m1⟩
      rw [hr1] at hm1
      have hm1c : m1.code = originalRuntimeCode := hm1.trans hcode
      cases r1 with
      | some x =>
        rcases ite_trap_with_step s1 hcode _ _ (some x) m1 hr1 with h | h
        · simp at h
        · intro hr; exact absurd hr h
      | none =>
        dsimp only
        rw [evaluateHOLFiniteState_dec_total]
        dsimp only
        split
        · intro h; exact absurd h not_resumes_error
        · rename_i qv _
          split
          · set s2 := setVarHOLFinite (ofString "q") qv m1
            rw [evaluateHOLFiniteState_seq_line780]
            rcases hr2 : evaluateHOLFiniteState s2 _ with ⟨r2, m2⟩
            cases r2 with
            | some x =>
              rcases ite_trap_with_step s2 hm1c _ _ (some x) m2 hr2 with h | h
              · simp at h
              · intro hr; exact absurd hr h
            | none =>
              dsimp only
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · intro h; exact absurd h not_resumes_error
              · split
                · dsimp only
                  rw [evaluateHOLFiniteState_return]
                  split
                  · intro h; exact absurd h not_resumes_error
                  · split
                    · rename_i retv _ _
                      intro _; exact ⟨retv, rfl⟩
                    · intro h; exact absurd h not_resumes_error
                · intro h; exact absurd h not_resumes_error
          · intro h; exact absurd h not_resumes_error
    · intro h; exact absurd h not_resumes_error

private theorem eval_or_head_some {F : Type} (s : PanSemStateFiniteExact 64 F)
    [h : DecidablePred s.memaddrs] (e1 : ExpHOL 64) (es : List (ExpHOL 64)) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.op .or (e1 :: es)) = some v) :
    ∃ v1, @evalHOLExact 64 F _ s.toExact h e1 = some v1 := by
  simp only [evalHOLExact, evalListHOLExact] at he
  rcases h1 : @evalHOLExact 64 F _ s.toExact h e1 with _ | v1
  · simp [h1] at he
  · exact ⟨v1, rfl⟩

private theorem eval_loadByte_local_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hG : GuestInv s) (name : String) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.loadByte (.var .local (ofString name))) = some v) :
    sourceBase ≤ locN s name ∧ locN s name < heapEnd := by
  simp only [evalHOLExact] at he
  rcases hl : s.locals.lookup (ofString name) with _ | lv
  · simp [hl] at he
  · simp only [hl] at he
    rcases lv with x | _ | _
    · cases x with
      | word w =>
        simp only [panMemLoadByteHOL] at he
        have hdom : s.memaddrs (panByteAlignHOL w) := by
          by_contra hc
          simp [hc] at he
        rw [hG.memaddrs] at hdom
        have hb := ordinaryDomain_bounds _ hdom
        have ha := byteAlign_bounds w
        have hloc : locN s name = w.toNat := by simp [locN, hl]
        rw [hloc]
        omega
    · simp at he
    · simp at he

private theorem locN_setVar_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String) (m : MlS)
    (v : ValueHOL 64) (h : ofString n ≠ m) : locN (setVarHOLFinite m v t) n = locN t n := by
  have hl : (t.locals.update (m, v)).lookup (ofString n) = t.locals.lookup (ofString n) := by
    simp [HolFiniteMapExact.update, FUPDATE, Ne.symm h]
  simp only [locN, setVarHOLFinite, hl]

private theorem evalList2_inv {F : Type} (s : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64)
    (vs : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = some vs) :
    ∃ v1 v2,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some v2 := by
  unfold evalListHOLFinite at h
  simp only [evalListHOLExact] at h
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [h1] at h
  · simp only [h1] at h
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [h2] at h
    · exact ⟨v1, v2, rfl, rfl⟩

theorem lookup_encode_withdrawal_rlp :
    originalRuntimeCode.lookup (ofString "encode_withdrawal_rlp") =
      some ([(ofString "wd", .one)], sourceFnBody Guest.Software.guestFn_encode_withdrawal_rlp,
        .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 838 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_withdrawal_rlp) rfl

/-- `encode_withdrawal_rlp` (AST index 838, line 32114): resumes only on an in-domain record (`loadByte(wd)`). -/
theorem «dm_encode_withdrawal_rlp» :
    ResumesInDomain (fun s => (locN s "wd", 1)) (ofString "encode_withdrawal_rlp") := by
  refine ⟨_, _, _, lookup_encode_withdrawal_rlp, ?_⟩
  intro F s hcode hG _ _ hres _
  revert hres
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_encode_withdrawal_rlp,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.const (BitVec.ofNat 64 64)] with _ | values
  · intro h; exact absurd h not_resumes_error
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") values with _ | ⟨body', callee, rs⟩
    · intro h; exact absurd h not_resumes_error
    · dsimp only
      split
      · intro h; exact absurd h not_resumes_timeOut
      · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc")
          _ _ _ _ _ values callee (by rw [hcode]; exact lookup_alloc) hl
        subst hsame
        have hGa : GuestInv (callEntryStateHOLFinite s callee) :=
          guestInv_with_locals_clock s callee (s.clock - 1) hG
        have hGp0 := guestInv_evaluate (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_alloc) hGa
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
            (sourceFnBody Guest.Software.guestFn_alloc) with ⟨res, st⟩
        rw [hrun] at hGp0
        dsimp only at hGp0 ⊢
        cases res with
        | none => intro h; exact absurd h not_resumes_error
        | some r =>
          cases r with
          | returned bufv =>
            dsimp only
            split
            · set s1 := setVarHOLFinite (ofString "buf") bufv { st with locals := s.locals } with hs1
              have hGs1 : GuestInv s1 := guestInv_with_locals_clock st s1.locals st.clock hGp0
              have hwd1 : locN s1 "wd" = locN s "wd" := by
                rw [hs1, locN_setVar_ne _ "wd" (ofString "buf") bufv (by decide)]
                rfl
              rw [evaluateHOLFiniteState_dec_total]
              dsimp only
              split
              · intro h; exact absurd h not_resumes_error
              · rename_i pv _
                split
                · set s2 := setVarHOLFinite (ofString "p") pv s1 with hs2
                  have hGs2 : GuestInv s2 := guestInv_with_locals_clock s1 s2.locals s1.clock hGs1
                  have hwd2 : locN s2 "wd" = locN s "wd" := by
                    rw [hs2, locN_setVar_ne _ "wd" (ofString "p") pv (by decide), hwd1]
                  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
                  split
                  · intro h; exact absurd h not_resumes_error
                  · rename_i vals2 hargs2
                    intro _
                    obtain ⟨_, vor, _, hor⟩ := evalList2_inv s2 _ _ vals2 hargs2
                    obtain ⟨vlb, hlb⟩ := eval_or_head_some s2
                      (h := fun a => Classical.propDecidable (s2.memaddrs a)) _ _ vor hor
                    have hdom := eval_loadByte_local_domain s2 hGs2 "wd" vlb hlb
                    rw [hwd2] at hdom
                    exact ⟨hdom.1, by omega⟩
                · intro h; exact absurd h not_resumes_error
            · intro h; exact absurd h not_resumes_error
          | timeOut => intro h; exact absurd h not_resumes_timeOut
          | «break» => intro h; exact absurd h not_resumes_error
          | «continue» => intro h; exact absurd h not_resumes_error
          | error => intro h; exact absurd h not_resumes_error
          | exception e v =>
            intro hres
            have halloc := alloc_resumes_returned (callEntryStateHOLFinite s callee) hcode
              (by rw [hrun]; exact hres)
            rw [hrun] at halloc
            rcases halloc with ⟨_, h⟩
            simp at h
          | finalFfi _ => intro h; exact absurd h not_resumes_finalFfi

end InitECandidate.Solver.Wave8GuestInv.M21
