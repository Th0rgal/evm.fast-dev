import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.WorldFrame
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers

/-! Execution frames for contract micro-shard m13 (`wave8/contracts-m13`):
1. `LocFrame` / `FunLocFrame` for local-only callees and control flow.
2. `ByteFrame` for byte-level bounded writers (`wk_u256_to_be_min`).
3. `WFrame` for arena-preserving (`heap_ptr` / `scratch_ptr`) functions writing only into
   freshly allocated heap/scratch or untyped global scratch buffers (`ws_*`, `validate_headers`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.M13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 0. General `GuestInv` & `be` preservation across `evaluateHOLFiniteState` -/

theorem evaluateHOLFiniteState_guestInv_be {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) (hG : GuestInv s) :
    GuestInv (evaluateHOLFiniteState s p).2 ∧ (evaluateHOLFiniteState s p).2.be = s.be := by
  have inv := evaluateInvariantsHOLFinite p
    (PanPropsEvalStateFiniteExact.ofPanSemFinite s)
    (evaluateHOLFiniteState s p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite (evaluateHOLFiniteState s p).2)
    (by simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite])
  exact ⟨⟨inv.2.2.2.2.2.2.1.trans hG.code, inv.1.trans hG.memaddrs,
          inv.2.1.trans hG.shMemaddrs, inv.2.2.2.2.1.trans hG.baseAddr⟩, inv.2.2.1⟩

/-! ## 1. `LocFrame` and `locOnlyW` -/

def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *; rw [h2]; rw [h1]

theorem LocFrame.locals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    LocFrame s { t with locals := L } := by
  unfold LocFrame at *; rw [h]

theorem LocFrame.setVar {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (x : MlS) (v : ValueHOL 64) :
    LocFrame s (setVarHOLFinite x v t) := h.locals _

theorem LocFrame.emptyLocals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : LocFrame s (emptyLocalsHOLFinite t) := h.locals _

theorem LocFrame.memory {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : t.memory = s.memory := by
  unfold LocFrame at h; rw [h]

theorem LocFrame.globals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : t.globals = s.globals := by
  unfold LocFrame at h; rw [h]

theorem LocFrame.code {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : t.code = s.code := by
  unfold LocFrame at h; rw [h]

theorem LocFrame.be {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : t.be = s.be := by
  unfold LocFrame at h; rw [h]

theorem LocFrame.arenaReady {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) (hAR : ArenaReady s) : ArenaReady t := by
  have hg : t.globals = s.globals := h.globals
  have hgN : ∀ nm, globN t nm = globN s nm := fun nm => by simp [globN, hg]
  refine ⟨⟨by unfold LocFrame at h; rw [h]; exact hAR.1.code,
           by unfold LocFrame at h; rw [h]; exact hAR.1.memaddrs,
           by unfold LocFrame at h; rw [h]; exact hAR.1.shMemaddrs,
           by unfold LocFrame at h; rw [h]; exact hAR.1.baseAddr⟩, ?_⟩
  exact arenaOK_congr hg hAR.2

def locOnlyW : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnlyW body
  | .seq first second => locOnlyW first && locOnlyW second
  | .ite _ yes no => locOnlyW yes && locOnlyW no
  | .while _ body => locOnlyW body
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrameW_eval {F : Type} (p : ProgHOL 64) (hp : locOnlyW p = true)
    (s : PanSemStateFiniteExact 64 F) : LocFrame s (evaluateHOLFiniteState s p).2 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | assign kind _ _ =>
    cases kind with
    | global => simp [shape, locOnlyW] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact LocFrame.refl s
    · split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | dec name sh init body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact LocFrame.refl s
    · rename_i val _
      split
      · have ih := locFrameW_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢; dsimp only; rw [ih]; rfl
      · exact LocFrame.refl s
  | seq first second =>
    have h12 : locOnlyW first = true ∧ locOnlyW second = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrameW_eval first h12.1 s
    have hle0 := evaluateHOLFiniteState_clock_le s first
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1 hle0
    dsimp only at ih1 hle0 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrameW_eval second h12.2 mid)
    | some _ => exact ih1
  | ite cond yes no =>
    have h12 : locOnlyW yes = true ∧ locOnlyW no = true := by
      simpa [shape, locOnlyW, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact locFrameW_eval no h12.2 s
      · exact locFrameW_eval yes h12.1 s
    · exact LocFrame.refl s
  | «while» cond body =>
    have hb : locOnlyW body = true := by simpa [shape, locOnlyW] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := locFrameW_eval body hb (decClockHOLFinite s)
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 hrem
          dsimp only at ih1 hrem
          have hlt : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at hrem; omega
          have h0 : LocFrame s mid := by
            unfold LocFrame at ih1 ⊢; rw [ih1]; rfl
          cases r1 with
          | none =>
            exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
          | some res =>
            cases res with
            | «continue» =>
              exact h0.trans (locFrameW_eval (.while cond body) (by simpa [locOnlyW] using hb) mid)
            | _ => exact h0
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | _ => simp [shape, locOnlyW] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    try simp only [decClockHOLFinite, setVarHOLFinite]
    try simp only [Prod.lex_def, true_and]
    try (rw [hr1] at hle0; dsimp only at hle0)
    omega

def FunLocFrame (fname : MlS) : Prop :=
  ∃ params body ret,
    originalRuntimeCode.lookup fname = some (params, body, ret) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      LocFrame s (evaluateHOLFiniteState s body).2

theorem funLocFrame_of_locOnlyW (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hlo : locOnlyW (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = true) :
    FunLocFrame (ofString (extractFn d).name) :=
  ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd,
    fun s _ => locFrameW_eval _ hlo s⟩

theorem locFrame_call_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {fname : MlS} (hf : FunLocFrame fname)
    (dest : Option (VarKind × MlS))
    (hdest : ∀ k n, dest = some (k, n) → k = .local)
    (args : List (ExpHOL 64)) :
    LocFrame s (evaluateHOLFiniteState s (.call (some (dest, none)) fname args)).2 := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  rw [evaluateHOLFiniteState_call]
  split
  · exact LocFrame.refl s
  · rename_i values _
    split
    · exact LocFrame.refl s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hsame
      split
      · rfl
      · dsimp only
        have hb := hbody (callEntryStateHOLFinite s callee) hcode
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨r, post⟩
        rw [hrun] at hb
        have hb' : LocFrame s post := by
          unfold LocFrame at hb ⊢; dsimp only at hb; rw [hb]; rfl
        rcases r with _ | r
        · exact hb'
        · cases r with
          | returned v =>
            dsimp only
            split
            · rcases dest with _ | ⟨k, n⟩
              · exact hb'.locals _
              · have hk := hdest k n rfl; subst hk
                dsimp only; split
                · exact hb'.locals _
                · exact hb'
            · exact hb'
          | timeOut => exact hb'.emptyLocals
          | «break» => exact hb'
          | «continue» => exact hb'
          | _ => exact hb'.emptyLocals

theorem locFrame_tailCall {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {fname : MlS} (hf : FunLocFrame fname)
    (args : List (ExpHOL 64)) :
    LocFrame s (evaluateHOLFiniteState s (.call none fname args)).2 := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  rw [evaluateHOLFiniteState_call]
  split
  · exact LocFrame.refl s
  · rename_i values _
    split
    · exact LocFrame.refl s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hsame
      split
      · rfl
      · dsimp only
        have hb := hbody (callEntryStateHOLFinite s callee) hcode
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨r, post⟩
        rw [hrun] at hb
        have hb' : LocFrame s post := by
          unfold LocFrame at hb ⊢; dsimp only at hb; rw [hb]; rfl
        rcases r with _ | r
        · exact hb'
        · cases r with
          | returned v =>
            dsimp only; split
            · exact hb'.emptyLocals
            · exact hb'
          | timeOut => exact hb'.emptyLocals
          | «break» => exact hb'
          | «continue» => exact hb'
          | _ => exact hb'.emptyLocals

theorem locFrame_decCall {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hcode : s.code = originalRuntimeCode) {fname : MlS} (hf : FunLocFrame fname)
    (name : MlS) (sh : ShapeHOL) (args : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hcont : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      LocFrame t (evaluateHOLFiniteState t cont).2) :
    LocFrame s (evaluateHOLFiniteState s (.decCall name sh fname args cont)).2 := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact LocFrame.refl s
  · rename_i values _
    split
    · exact LocFrame.refl s
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hsame
      split
      · rfl
      · dsimp only
        have hb := hbody (callEntryStateHOLFinite s callee) hcode
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨r, post⟩
        rw [hrun] at hb
        have hb' : LocFrame s post := by
          unfold LocFrame at hb ⊢; dsimp only at hb; rw [hb]; rfl
        have hpcode : post.code = originalRuntimeCode := hb'.code.trans hcode
        rcases r with _ | r
        · exact hb'
        · cases r with
          | returned v =>
            dsimp only; split
            · have hc := hcont (setVarHOLFinite name v { post with locals := s.locals }) hpcode
              exact ((hb'.locals _).setVar _ _).trans hc |>.locals _
            · exact hb'
          | timeOut => exact hb'.emptyLocals
          | «break» => exact hb'
          | «continue» => exact hb'
          | _ => exact hb'.emptyLocals

theorem locFrame_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (ha : LocFrame s (evaluateHOLFiniteState s a).2)
    (hb : ∀ m : PanSemStateFiniteExact 64 F, LocFrame s m →
      LocFrame m (evaluateHOLFiniteState m b).2) :
    LocFrame s (evaluateHOLFiniteState s (.seq a b)).2 := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
  rw [hr] at ha
  cases r1 with
  | none => exact ha.trans (hb mid ha)
  | some _ => exact ha

theorem locFrame_dec {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hb : ∀ val, LocFrame (setVarHOLFinite name val s)
      (evaluateHOLFiniteState (setVarHOLFinite name val s) body).2) :
    LocFrame s (evaluateHOLFiniteState s (.dec name sh init body)).2 := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact LocFrame.refl s
  · rename_i val _
    split
    · exact ((LocFrame.refl s).setVar name val).trans (hb val) |>.locals _
    · exact LocFrame.refl s

theorem locFrame_ite {F : Type} {s : PanSemStateFiniteExact 64 F}
    (cond : ExpHOL 64) {yes no : ProgHOL 64}
    (hy : LocFrame s (evaluateHOLFiniteState s yes).2)
    (hn : LocFrame s (evaluateHOLFiniteState s no).2) :
    LocFrame s (evaluateHOLFiniteState s (.ite cond yes no)).2 := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · exact LocFrame.refl s

theorem locFrame_while {F : Type} (cond : ExpHOL 64) {body : ProgHOL 64}
    (hb : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      LocFrame t (evaluateHOLFiniteState t body).2)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    LocFrame s (evaluateHOLFiniteState s (.while cond body)).2 := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · rfl
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have ih1 := hb (decClockHOLFinite s) hcode
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
        rw [hbr] at ih1 hrem
        dsimp only at ih1 hrem
        have hlt : mid.clock < s.clock := by
          change mid.clock ≤ s.clock - 1 at hrem; omega
        have h0 : LocFrame s mid := by
          unfold LocFrame at ih1 ⊢; rw [ih1]; rfl
        have hmcode : mid.code = originalRuntimeCode := h0.code.trans hcode
        cases r1 with
        | none => exact h0.trans (locFrame_while cond hb mid hmcode)
        | some res =>
          cases res with
          | «continue» => exact h0.trans (locFrame_while cond hb mid hmcode)
          | _ => exact h0
    · exact LocFrame.refl s
  · exact LocFrame.refl s
termination_by s.clock

-- Note: avoid `macro` declarations in modules importing `Guest.SoftwareAst`, as `macro`
-- triggers Lean's bytecode interpreter module initialization on imported AST constants.

/-! ## 2. Address no-wrap from `ordinaryDomain` & byte alignment -/

theorem mls_ne {a b : MlS} (h : (a == b) = false) : a ≠ b := by
  intro heq; subst heq; simp at h

theorem add_no_wrap_of_memaddrs (base off : BitVec 64)
    (hoff : off.toNat < sourceBase)
    (hdom : ordinaryDomain (panByteAlignHOL (base + off))) :
    base.toNat + off.toNat < 2 ^ 64 ∧ (base + off).toNat = base.toNat + off.toNat ∧ base ≠ 0 := by
  rw [ordinaryDomain_iff] at hdom
  have hal := panByteAlign_toNat64 (base + off)
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
  have hsb : sourceBase = 2701131776 := rfl
  have hb_lt := base.isLt
  have ho_lt := off.isLt
  have hnw : base.toNat + off.toNat < 2 ^ 64 := by
    by_contra hge
    have hmod : (base + off).toNat = base.toNat + off.toNat - 2 ^ 64 := by
      rw [BitVec.toNat_add]; omega
    omega
  have heq : (base + off).toNat = base.toNat + off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnw]
  refine ⟨hnw, heq, ?_⟩
  rintro rfl
  have : (0 : BitVec 64).toNat = 0 := rfl
  omega

theorem memB_eq_memByteAt {F : Type} (s : PanSemStateFiniteExact 64 F) (a : Nat) :
    memB s a = (memByteAt s.memory s.be (BitVec.ofNat 64 a)).toNat := by
  unfold memB memByteAt memWordAt
  cases s.memory (panByteAlignHOL (BitVec.ofNat 64 a)) with
  | word w => rfl

/-! ## 3. `ByteFrame`: byte-exact frame for `wk_u256_to_be_min` -/

def ByteFrame (R : List Ivl) {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with memory := t.memory, locals := t.locals, clock := t.clock } ∧
  (∀ x : BitVec 64, t.memory x ≠ s.memory x → s.memaddrs x ∧ ∃ r ∈ R, CellHits x.toNat r) ∧
  (∀ a : Nat, a < 2 ^ 64 → memB t a ≠ memB s a → ∃ r ∈ R, InIvl a r)

theorem ByteFrame.refl (R : List Ivl) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ByteFrame R s s :=
  ⟨by cases s; rfl, fun _ h => False.elim (h rfl), fun _ _ h => False.elim (h rfl)⟩

theorem ByteFrame.of_locFrame (R : List Ivl) {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrame s t) : ByteFrame R s t := by
  refine ⟨by unfold LocFrame at h; rw [h],
   fun _ hne => False.elim (hne (by rw [h.memory])),
   fun a _ hne => False.elim (hne ?_)⟩
  unfold memB
  rw [h.memory, h.be]

theorem ByteFrame.trans {R : List Ivl} {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : ByteFrame R s t) (h2 : ByteFrame R t u) : ByteFrame R s u := by
  refine ⟨by rw [h2.1]; rw [h1.1], fun x hne => ?_, fun a ha hne => ?_⟩
  · by_cases htu : u.memory x = t.memory x
    · rw [htu] at hne; exact h1.2.1 x hne
    · have hdom_eq : t.memaddrs = s.memaddrs := by rw [h1.1]
      rw [← hdom_eq]; exact h2.2.1 x htu
  · by_cases htu : memB u a = memB t a
    · rw [htu] at hne; exact h1.2.2 a ha hne
    · exact h2.2.2 a ha htu

theorem ByteFrame.locals {R : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrame R s t) (L : HolFiniteMapExact MlS (ValueHOL 64)) :
    ByteFrame R s { t with locals := L } :=
  ⟨by rw [h.1], h.2.1, h.2.2⟩

theorem ByteFrame.setVar {R : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrame R s t) (x : MlS) (v : ValueHOL 64) :
    ByteFrame R s (setVarHOLFinite x v t) := h.locals _

theorem ByteFrame.emptyLocals {R : List Ivl} {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : ByteFrame R s t) : ByteFrame R s (emptyLocalsHOLFinite t) := h.locals _

theorem byteFrame_storeByte {R : List Ivl} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst src : ExpHOL 64)
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
        some (.val (.word addr)) →
      s.memaddrs (panByteAlignHOL addr) →
      ∃ r ∈ R, InIvl addr.toNat r) :
    ByteFrame R s (evaluateHOLFiniteState s (.storeByte dst src)).2 := by
  by_cases hev_dst : ∃ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
        some (.val (.word addr))
  · obtain ⟨addr, hdst⟩ := hev_dst
    by_cases hev_src : ∃ val : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) src =
          some (.val (.word val))
    · obtain ⟨val, hsrc⟩ := hev_src
      by_cases hdom : s.memaddrs (panByteAlignHOL addr)
      · obtain ⟨r_ivl, hr_in, hin_r⟩ := hin addr hdst hdom
        obtain ⟨mem', heval, _, hdiff_byte, hdiff_word⟩ := evaluate_storeByte_word hdst hsrc hdom
        rw [heval]; dsimp only
        refine ⟨rfl, fun x hne => ?_, fun a ha_lt hne_b => ?_⟩
        · by_cases hx : x = panByteAlignHOL addr
          · subst hx
            have hal := panByteAlign_toNat64 addr
            obtain ⟨hl, hr⟩ := hin_r
            exact ⟨hdom, r_ivl, hr_in, by omega, by omega⟩
          · exact False.elim (hne (hdiff_word x hx))
        · simp only [memB_eq_memByteAt] at hne_b
          by_cases ha_eq : BitVec.ofNat 64 a = addr
          · have ha_nat : a = addr.toNat := by
              have := congrArg BitVec.toNat ha_eq
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha_lt] at this
            rw [ha_nat]; exact ⟨r_ivl, hr_in, hin_r⟩
          · exact False.elim (hne_b (congrArg UInt8.toNat (hdiff_byte (BitVec.ofNat 64 a) ha_eq)))
      · rw [evaluateHOLFiniteState_storeByte]
        simp only [hdst, hsrc]
        unfold panMemStoreByteWord8HOL; dsimp only
        cases s.memory (panByteAlignHOL addr) with
        | word cell =>
          simp only [hdom, ↓reduceIte]
          exact ByteFrame.refl R s
    · rw [evaluateHOLFiniteState_storeByte]
      simp only [hdst]
      split
      · rename_i val hsrc
        exact False.elim (hev_src ⟨val, hsrc⟩)
      · exact ByteFrame.refl R s
  · rw [evaluateHOLFiniteState_storeByte]
    split
    · rename_i addr hdst
      exact False.elim (hev_dst ⟨addr, hdst⟩)
    · exact ByteFrame.refl R s

theorem worldStep_of_byteFrame {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hWOK : WorldOK s) (hBF : ByteFrame (R s) s post) :
    WorldStep R [] stdKeep NoExtra s r post := by
  have heff : ByteRegionEffect s post (R s ++ ([] : List Ivl)) := by
    simp only [List.append_nil]
    refine ⟨by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1],
      ?_, ?_, ?_⟩
    · intro a hna
      by_contra hne
      exact hna (hBF.2.1 a hne).1
    · intro a hno
      by_contra hne
      obtain ⟨_, ri, hri, hch⟩ := hBF.2.1 a hne
      exact hno ri hri hch
    · intro b hb hno
      by_contra hne
      obtain ⟨ri, hri, hin⟩ := hBF.2.2 b hb hne
      exact hno ri hri hin
  exact ByteRegionEffect.to_worldStep (extra := fun {F} _ => []) hWOK (fun _ hx => by cases hx) heff

end InitECandidate.Solver.Wave8GuestInv.M13
