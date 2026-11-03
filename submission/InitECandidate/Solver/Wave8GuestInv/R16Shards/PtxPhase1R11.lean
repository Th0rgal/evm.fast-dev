import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers

/-! R11 Phase 1 validation cut (`ptxPhase1_cut`) for `gbody_process_transaction`. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R13Shards

namespace PtxP1

theorem lookup_encode_transaction : originalRuntimeCode.lookup (ofString "encode_transaction") =
    some ((sourceFunctionEntry Guest.Software.guestFn_encode_transaction).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 329 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_transaction) rfl

theorem lookup_alloc : originalRuntimeCode.lookup (ofString "alloc") =
    some ((sourceFunctionEntry Guest.Software.guestFn_alloc).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_min : originalRuntimeCode.lookup (ofString "min") =
    some ((sourceFunctionEntry Guest.Software.guestFn_min).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 31 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_min) rfl

theorem lookup_recover_sender_with_chain_id :
    originalRuntimeCode.lookup (ofString "recover_sender_with_chain_id") =
      some ((sourceFunctionEntry Guest.Software.guestFn_recover_sender_with_chain_id).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 343 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_recover_sender_with_chain_id) rfl

theorem lookupCodeHOLFinite_installed_shape
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (parameters : List (MlS × ShapeHOL)) (body foundBody : ProgHOL 64)
    (returnShape foundShape : ShapeHOL) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (installed : code name = some (parameters, body, returnShape))
    (found : lookupCodeHOLFinite code name values = some (foundBody, locals, foundShape)) :
    foundShape = returnShape := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at found
  split at found
  · cases found
  · rename_i exactBody exactLocals exactShape raw
    have same : exactShape = returnShape := by
      simp only [lookupCodeHOLExact, installed] at raw
      split at raw
      · exact ((Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).2).symm
      · cases raw
    have equal := Option.some.inj found
    exact ((Prod.mk.inj (Prod.mk.inj equal).2).2).symm.trans same

theorem funSpec_at_lookup {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop} {fname : MlS}
    (hf : FunSpec Pc Qc fname) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hcode : state.code = originalRuntimeCode) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hl : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret'))
    (hPc : Pc (callEntryStateHOLFinite state callee))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1 ≠
      some .timeOut) :
    Qc (callEntryStateHOLFinite state callee)
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').1
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body').2 := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  have hret := lookupCodeHOLFinite_installed_shape state.code.lookup fname params body body'
    ret ret' values callee (by rw [hcode]; exact hlook) hl
  subst hsame
  subst hret
  exact hspec _ hcode hPc ⟨values, by simpa only [hcode, callEntryStateHOLFinite] using hl⟩ hnt

theorem shape_one_word {v : ValueHOL 64} (h : shapeOfHOLExact v = .one) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · exact ⟨w, rfl⟩
  · simp [shapeOfHOLExact] at h
  · simp [shapeOfHOLExact] at h

theorem shape_pair_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a), .val (.word b)] := by
  rw [shapeEqHOL_eq_true] at h
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · simp [shapeOfHOLExact] at h
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at h
    rcases fs with _ | ⟨v0, _ | ⟨v1, _ | vs⟩⟩
    · simp at h
    · simp at h
    · simp only [List.map, List.cons.injEq] at h
      obtain ⟨h0, h1, _⟩ := h
      obtain ⟨a, rfl⟩ := shape_one_word h0
      obtain ⟨b, rfl⟩ := shape_one_word h1
      exact ⟨a, b, rfl⟩
    · simp at h
  · simp [shapeOfHOLExact] at h

theorem params_one_value {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p : MlS) (sh : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh)], body, ret)) (e : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v, evalAt s e = some v ∧ callee.lookup p = some v := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases he : evalAt s e with _ | v
  · simp only [evalListHOLExact, he] at ha'; cases ha'
  · exact ⟨v, rfl, (R16Shards.callee_param_one_exp s fname p sh body ret hi e v vs body' callee ret' he ha hl).2⟩

theorem params_two_values {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p q : MlS) (sh1 sh2 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh1), (q, sh2)], body, ret)) (e1 e2 : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v1 v2, evalAt s e1 = some v1 ∧ evalAt s e2 = some v2 ∧
      callee.lookup p = some v1 ∧ callee.lookup q = some v2 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalListHOLExact, h1] at ha'; cases ha'
  rcases h2 : evalAt s e2 with _ | v2
  · simp only [evalListHOLExact, h1, h2] at ha'; cases ha'
  have hp := R16Shards.callee_param_two s fname p q sh1 sh2 body ret hi e1 e2 v1 v2 vs body' callee ret' h1 h2 ha hl
  exact ⟨v1, v2, rfl, rfl, hp.2⟩

theorem params_three_values {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p q r : MlS) (sh1 sh2 sh3 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p, sh1), (q, sh2), (r, sh3)], body, ret)) (e1 e2 e3 : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v1 v2 v3, evalAt s e1 = some v1 ∧ evalAt s e2 = some v2 ∧ evalAt s e3 = some v3 ∧
      callee.lookup p = some v1 ∧ callee.lookup q = some v2 ∧ callee.lookup r = some v3 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalListHOLExact, h1] at ha'; cases ha'
  rcases h2 : evalAt s e2 with _ | v2
  · simp only [evalListHOLExact, h1, h2] at ha'; cases ha'
  rcases h3 : evalAt s e3 with _ | v3
  · simp only [evalListHOLExact, h1, h2, h3] at ha'; cases ha'
  have hp := R16Shards.callee_param_three s fname p q r sh1 sh2 sh3 body ret hi e1 e2 e3 v1 v2 v3 vs body' callee ret' h1 h2 h3 ha hl
  exact ⟨v1, v2, v3, rfl, rfl, rfl, hp.1, hp.2.1, hp.2.2⟩

theorem bound_of_clock {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState s prog).2.clock = s.clock) :
    TerminatingProgBoundedOn P prog 0 :=
  fun s _ _ _ => ⟨by have := h s; omega, by have := h s; omega⟩

theorem clock_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) : (evaluateHOLFiniteState s (.assign k n e)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (try dsimp only)
  all_goals (cases k <;> rfl)

theorem clock_skip {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s .skip).2.clock = s.clock := by simp

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

def DecCallResumeShapeOn (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (name : MlS) (shape : ShapeHOL)
    (fname : MlS) (arguments : List (ExpHOL 64)) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
    state.code = originalRuntimeCode → P state →
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      arguments = some values →
    lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
    evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
      (some (.returned value), post) →
    shapeEqHOL (shapeOfHOLExact value) shape = true →
    Q (setVarHOLFinite name value { post with locals := state.locals })

theorem decCall_shape_bound
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn Pc fname B)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hentry : CallEntryOn P Pc fname arguments)
    (hres : DecCallResumeShapeOn P Q name shape fname arguments)
    (hcont : TerminatingProgBoundedOn Q continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hf
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        have hresQ := hres state values body' callee ret'
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals }
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresInv : Q resumed := hresQ value post hcode hP hargs hl hrun (Bool.and_eq_true_iff.mp hsh).1
              have hcb := hcont resumed hresCode hresInv hnt
              obtain ⟨hsc, hkc⟩ := hcb
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

/-! ### R11 `TxReadyStrong` & `TxAccessListAt` Preservation -/

theorem worldOK_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd) : WorldOK s :=
  ⟨hA, S, (worldTyped_iff_with s S).2 ⟨Nd, hW⟩⟩

theorem txEnv_of_ready {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) : TxEnv s :=
  ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.2.2.1, h.2.2.2.1, h.1.2.2.2.2, h.2.1⟩

theorem txReadyStrong_of_parts {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd) (hT : TxAccessListOK s S Nd) :
    TxReadyStrong s :=
  ⟨⟨worldOK_of_parts hA hW, hE.bo_nz, hE.bo24, hE.bo32, hE.idx_lt⟩,
    hE.jcap_nz, hE.bo40, hE.bo72, S, Nd, hW, hT⟩

theorem txReadyStrong_txValid {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) : TxValid s := by
  obtain ⟨_, _, _, hT⟩ := h.2.2.2.2
  exact hT.1

theorem txValidAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k tx : Nat)
    (h : TxValidAt s tx) : TxValidAt { s with locals := locals, clock := k } tx := by
  obtain ⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩ := h
  exact ⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩

theorem txValid_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (h : TxValid s) : TxValid { s with locals := locals, clock := k } := by
  have he := locN_congr s locals k "tx" ht
  unfold TxValid at h ⊢
  rw [he]
  exact txValidAt_with_locals s locals k _ h

theorem txAccessListAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {S Nd : List Nat} {tx : Nat}
    (h : TxAccessListAt s S Nd tx) :
    TxAccessListAt { s with locals := locals, clock := k } S Nd tx :=
  ⟨txValidAt_with_locals s locals k tx h.1, h.2.1, h.2.2⟩

theorem txAccessListOK_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {S Nd : List Nat}
    (htx_lu : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (h : TxAccessListOK s S Nd) :
    TxAccessListOK { s with locals := locals, clock := k } S Nd := by
  have ht := locN_congr s locals k "tx" htx_lu
  unfold TxAccessListOK at h ⊢
  rw [ht]
  exact txAccessListAt_with_locals s locals k h

theorem txReadyStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (ht : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx"))
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index"))
    (h : TxReadyStrong s) : TxReadyStrong { s with locals := locals, clock := k } := by
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2
  exact txReadyStrong_of_parts
    ((arenaReady_with_locals s locals k).mpr h.1.1.1)
    (txEnv_with_locals s locals k hi (txEnv_of_ready h))
    ((R13Shards.worldTypedWith_with_locals s locals k S Nd).mpr hW)
    (txAccessListOK_with_locals s locals k ht hT)

theorem txAccessListAt_congr_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaOK s) (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {S Nd S' Nd' : List Nat} {tx : Nat}
    (htx : TxAccessListAt s S Nd tx)
    (htx_disj' : IvlsDisj [(tx, 384)] (worldOwned post S' Nd'))
    (hrecs_disj' : 0 < memW s (tx + 216) →
      IvlsDisj [(memW s (tx + 208), 24 * memW s (tx + 216))] (worldOwned post S' Nd'))
    (htx_u : R13Shards.IvlUnhit s post (tx, 384))
    (hrecs_u : 0 < memW s (tx + 216) →
      R13Shards.IvlUnhit s post (memW s (tx + 208), 24 * memW s (tx + 216))) :
    TxAccessListAt post S' Nd' tx := by
  obtain ⟨⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩, _, hrecs_fn⟩ := htx
  have htx8 : tx % 8 = 0 := hw.1
  have htx_hi : tx + 384 ≤ 2 ^ 64 := (R13Shards.ivl_allocated_bound hAs (Or.inl hin)).2
  have hm : ∀ off, off % 8 = 0 → off + 8 ≤ 384 → memW post (tx + off) = memW s (tx + off) :=
    fun off _ _ => R13Shards.memW_eq_of_ivlUnhit htx_u (by omega) htx_hi ⟨by omega, by omega⟩
  have e0 : memW post tx = memW s tx := by simpa using hm 0 (by omega) (by omega)
  have e200 := hm 200 (by omega) (by omega)
  have e208 := hm 208 (by omega) (by omega)
  have e216 := hm 216 (by omega) (by omega)
  have e264 := hm 264 (by omega) (by omega)
  have e272 := hm 272 (by omega) (by omega)
  have e280 := hm 280 (by omega) (by omega)
  have hsl_eq : txAccessSlots post tx = txAccessSlots s tx := by
    unfold txAccessSlots
    rw [e216, e208]
    by_cases hpos : 0 < memW s (tx + 216)
    · have hr_w := hw208 hpos
      have hr8 : (memW s (tx + 208)) % 8 = 0 := hr_w.1
      have hr_hi : memW s (tx + 208) + 24 * memW s (tx + 216) ≤ 2 ^ 64 :=
        (R13Shards.ivl_allocated_bound hAs (Or.inl (hrecs_fn hpos).1)).2
      apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      exact R13Shards.memW_eq_of_ivlUnhit (hrecs_u hpos) (by omega) hr_hi ⟨by dsimp; omega, by dsimp; omega⟩
    · have hz : memW s (tx + 216) = 0 := by omega
      simp [hz]
  refine ⟨?_, htx_disj', ?_⟩
  · unfold TxValidAt
    rw [e0, e200, e208, e216, e264, e272, e280, hsl_eq]
    exact ⟨R13Shards.wordsOK_transfer hgS hgP hw, ⟨hin.1, hin.2.trans hhp⟩,
      h0, h200, h216, hsl, h264, h280,
      fun hp => R13Shards.wordsOK_transfer hgS hgP (hw208 hp),
      fun hp => R13Shards.wordsOK_transfer hgS hgP (hw272 hp)⟩
  · rw [e216, e208]
    intro hpos
    exact ⟨⟨(hrecs_fn hpos).1.1, (hrecs_fn hpos).1.2.trans hhp⟩, hrecs_disj' hpos⟩

theorem txAccessListOK_survives_step {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {S Nd S' Nd' : List Nat} {R : List Ivl}
    (hW : WorldTypedWith s S Nd)
    (hR0 : ∀ i ∈ R, i.2 = 0 → i.1 % 8 = 0)
    (hog : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hfr : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (htx : TxAccessListOK s S Nd)
    (htx_R : ∀ r ∈ R, Disj (locN s "tx", 384) r)
    (hrecs_R : 0 < memW s (locN s "tx" + 216) →
      ∀ r ∈ R, Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) r)
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (htx_lu : locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx")) :
    TxAccessListOK { post with locals := locals } S' Nd' := by
  have htx8 : (locN s "tx") % 8 = 0 := htx.1.1.1
  have htx_in : Inside (locN s "tx", 384) sourceBase (globN s "heap_ptr") := htx.1.2.1
  have htx_ow : ∀ j ∈ worldOwned s S Nd, Disj (locN s "tx", 384) j :=
    fun j hj => htx.2.1 _ (by simp) j hj
  obtain ⟨_, htx_ow', htx_u⟩ :=
    R13Shards.heap_ivl_survives_step hAs.2 hhp (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr
      htx8 (by omega) htx_in htx_ow htx_R
  have hrecs_surv : ∀ hpos : 0 < memW s (locN s "tx" + 216),
      (∀ o ∈ worldOwned post S' Nd', Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) o) ∧
      R13Shards.IvlUnhit s post (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hpos
    have hr_w := htx.1.2.2.2.2.2.2.2.2.1 hpos
    have hr_fn := htx.2.2 hpos
    obtain ⟨_, hr_ow', hr_u⟩ :=
      R13Shards.heap_ivl_survives_step hAs.2 hhp (R13Shards.worldOwned_zero_aligned hW) hR0 hog hfr
        hr_w.1 (by omega) hr_fn.1 (fun j hj => hr_fn.2 _ (by simp) j hj) (hrecs_R hpos)
    exact ⟨hr_ow', hr_u⟩
  have hAt_post : TxAccessListAt post S' Nd' (locN s "tx") :=
    txAccessListAt_congr_unhit hAs.2 hAs.1 hgP hhp htx
      (fun i hi o ho => by simp only [List.mem_singleton] at hi; subst hi; exact htx_ow' o ho)
      (fun hpos i hi o ho => by simp only [List.mem_singleton] at hi; subst hi; exact (hrecs_surv hpos).1 o ho)
      htx_u (fun hpos => (hrecs_surv hpos).2)
  have ht_loc : locN { post with locals := locals } "tx" = locN s "tx" :=
    locN_congr s locals post.clock "tx" htx_lu
  unfold TxAccessListOK
  rw [ht_loc]
  exact txAccessListAt_with_locals post locals post.clock hAt_post

theorem bo_mem_typed {F : Type} {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hn : globN s "bo" ≠ 0) : (globN s "bo", 88) ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hn]⟩

theorem bufferRegion_mem_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    {gn : String × Nat} (hgn : gn ∈ globalBuffers) :
    bufferRegion s gn ∈ fixedObjects s := by
  unfold fixedObjects
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  exact List.mem_map.2 ⟨gn, hgn, rfl⟩

theorem heap_ivl_disj_bufferRegion_le {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {i : Ivl}
    (hd : ∀ j ∈ worldOwned s S Nd, Disj i j)
    (gn : String × Nat) (hgn : gn ∈ globalBuffers) (n : Nat) (hle : n ≤ gn.2) :
    Disj i (bufferRegion s (gn.1, n)) := by
  have hd0 := hd (bufferRegion s gn)
    (List.mem_append_left _ (List.mem_append_right _ (bufferRegion_mem_fixedObjects s hgn)))
  by_cases hz : globN s gn.1 = 0
  · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
  · simp only [bufferRegion, hz, ↓reduceIte] at hd0 ⊢
    unfold Disj at hd0 ⊢; dsimp only at hd0 ⊢; omega

theorem bufferRegion_zero_aligned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (sz : Nat) (hsz : sz ≠ 0) :
    (bufferRegion s (g, sz)).2 = 0 → (bufferRegion s (g, sz)).1 % 8 = 0 := by
  intro hz
  unfold bufferRegion at hz ⊢
  dsimp only at hz ⊢
  by_cases hg0 : globN s g = 0
  · simp [hg0]
  · rw [if_neg hg0] at hz; exact absurd hz hsz

def ScratchSpec (gs : List (String × Nat × Nat)) : Prop :=
  ∀ e ∈ gs, (e.1, e.2.1) ∈ globalBuffers ∧ e.1 ∉ typedRecords.map Prod.fst ∧
    0 < e.2.2 ∧ e.2.2 ≤ e.2.1

theorem txReadyStrong_worldStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post)
    (hA : ArenaReady s) (hE : TxEnv s)
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd) (hT : TxAccessListOK s S Nd)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hR0 : ∀ i ∈ R s, i.2 = 0 → i.1 % 8 = 0)
    (hRt : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (htx_R : ∀ i ∈ R s, Disj (locN s "tx", 384) i)
    (hrecs_R : 0 < memW s (locN s "tx" + 216) →
      ∀ i ∈ R s, Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) i) :
    TxReadyStrong { post with locals := s.locals } := by
  obtain ⟨S', Nd', _, hW', hgrow, hframe, _⟩ := hstep.2.2.2.2 S Nd hW hRt
  have hE' := R13Shards.txEnv_preserved_by_worldStep hstep hbo_gw hjcap_gw hbo_keep hoffs
    (fun i hi => hRt i hi _ (bo_mem_typed hE.bo_nz))
    (R13Shards.bo_words hW.2.2.1 hE.bo_nz).2.1 hR0 hE (locals := s.locals) rfl
  have hT' := txAccessListOK_survives_step hA hstep.1.1 hstep.2.1 hW hR0 hgrow hframe hT
    htx_R hrecs_R (locals := s.locals) rfl
  exact txReadyStrong_of_parts
    ((arenaReady_with_locals post s.locals post.clock).mpr hstep.1) hE'
    ((R13Shards.worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hW') hT'

theorem txReadyStrong_scratchStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q s r post) (h : TxReadyStrong s)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    TxReadyStrong { post with locals := s.locals } := by
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2
  have hrSafe : IvlsDisj (R s) (worldTypedIvls s S Nd) := by
    intro i hi j hj
    rw [hR] at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, hnu, _, hle⟩ := hgs e he
    exact bufferRegion_disj_le hW (e.1, e.2.1) hgb hnu e.2.2 hle j hj
  apply txReadyStrong_worldStep hstep h.1.1.1 (txEnv_of_ready h) hW hT
    hbo_gw hjcap_gw hbo_keep hoffs ?_ hrSafe ?_ ?_
  · intro i hi hz
    rw [hR] at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    exact bufferRegion_zero_aligned s e.1 e.2.2 (by have := (hgs e he).2.2.1; omega) hz
  · intro i hi
    rw [hR] at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, _, _, hle⟩ := hgs e he
    exact heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj)
      (e.1, e.2.1) hgb e.2.2 hle
  · intro hpos i hi
    rw [hR] at hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    obtain ⟨hgb, _, _, hle⟩ := hgs e he
    exact heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hpos).2 _ (by simp) j hj)
      (e.1, e.2.1) hgb e.2.2 hle

/-! ### Phase 1 Stores (`bo+24` array and `bal_index := index + 1`) -/

def encArray {F : Type} (s : PanSemStateFiniteExact 64 F) : Ivl :=
  (memW s (globN s "bo" + 24), 16 * memW s (globN s "bo" + 80) + 16)

theorem encArray_mem_block {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hE : TxEnv s) : encArray s ∈ blockOutObjects s := by
  unfold encArray blockOutObjects
  simp [hE.bo_nz, hE.bo24]

theorem encArray_mem_fixed {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hE : TxEnv s) : encArray s ∈ fixedObjects s :=
  List.mem_append_left _ (List.mem_append_right _ (encArray_mem_block hE))

theorem encArray_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hF : FixedTyped s) (hE : TxEnv s) : Allocated s (encArray s) ∧ WordsOK s (encArray s) :=
  (hF.1 _ (encArray_mem_fixed hE)).resolve_left (by simp [encArray])

theorem store_encArray_world {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    WorldTypedWith { s with memory := mem' } S Nd ∧
    worldOwned { s with memory := mem' } S Nd = worldOwned s S Nd ∧
    TxEnv { s with memory := mem' } := by
  obtain ⟨hgbs, hbo_pw, hgb_rest, hjr_rest, hbo_bal⟩ := R13Shards.fixedObjects_disj_parts hW.2.2.1
  obtain ⟨hc40, hc72, hbo_eq⟩ := R13Shards.blockOutObjects_eq_list hE hW.1
  have hbo_len : (blockOutObjects s).length = 7 := by rw [hbo_eq]; rfl
  have h0_lt : 0 < (blockOutObjects s).length := by omega
  have h0_eq : (blockOutObjects s)[0] = encArray s := by
    simp [hbo_eq, encArray, hE.bo_nz, hE.bo24]
  have harr_bo : encArray s ∈ blockOutObjects s := encArray_mem_block hE
  have harr_fix : encArray s ∈ fixedObjects s := encArray_mem_fixed hE
  have hbo_gbs : (globN s "bo", 88) ∈ (globalBuffers.map fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)) :=
    List.mem_map.2 ⟨("bo", 88), by decide, by simp [hE.bo_nz]⟩
  have hbo_disj_arr : Disj (globN s "bo", 88) (encArray s) :=
    hgb_rest _ hbo_gbs _ (List.mem_append_left _ (List.mem_append_right _ harr_bo))
  have hbo_hi := (R13Shards.ivl_allocated_bound hA.2 (R13Shards.bo_words hW.2.2.1 hE.bo_nz).1).2
  have hbo_idx_disj : ∀ (j : Nat) (hj : j < (blockOutObjects s).length), 0 < j →
      Disj (blockOutObjects s)[j] (encArray s) := by
    intro j hj hgt
    have hget := List.pairwise_iff_getElem.1 hbo_pw
    exact R13Shards.disj_symm (h0_eq ▸ hget 0 j h0_lt hj hgt)
  apply R13Shards.worldTypedWith_single_store_of_disj hA hE hW hx
  · intro t ht i hi
    exact R13Shards.disj_of_inside_right hin (((hW.1.2.1 t ht).2 i hi).2 _ harr_fix)
  · intro hn
    refine R13Shards.disj_of_inside_right hin (hgb_rest _ ?_ _ (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("ws", 40), by decide, by simp [hn]⟩
  · intro hn
    refine R13Shards.disj_of_inside_right hin (hgb_rest _ ?_ _ (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("bs", 80), by decide, by simp [hn]⟩
  · intro hn
    refine R13Shards.disj_of_inside_right hin (hgb_rest _ ?_ _ (List.mem_append_left _ (List.mem_append_right _ harr_bo)))
    exact List.mem_map.2 ⟨("ts", 72), by decide, by simp [hn]⟩
  · intro hn
    refine R13Shards.disj_of_inside_right hin (hjr_rest _ ?_ _ (List.mem_append_left _ harr_bo))
    simp [hn]
  · have hj3 : 3 < (blockOutObjects s).length := by omega
    have h3_eq : (blockOutObjects s)[3] = (memW s (globN s "bo" + 40), 24) := by simp [hbo_eq]
    exact R13Shards.disj_of_inside_right hin (h3_eq ▸ hbo_idx_disj 3 hj3 (by omega))
  · have hj5 : 5 < (blockOutObjects s).length := by omega
    have h5_eq : (blockOutObjects s)[5] = (memW s (globN s "bo" + 72), 24) := by simp [hbo_eq]
    exact R13Shards.disj_of_inside_right hin (h5_eq ▸ hbo_idx_disj 5 hj5 (by omega))
  · intro i hi
    exact R13Shards.disj_of_inside_right hin (R13Shards.disj_symm (hbo_bal _ harr_bo i hi))
  · intro o ho
    exact R13Shards.disj_of_inside_right hin (((hW.2.2.2.2.1 o ho).2 _ harr_fix))
  · intro k hk heq
    have htonat := congrArg BitVec.toNat heq
    dsimp only at hbo_hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    have hk_lt : globN s "bo" + k < 2 ^ 64 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk_lt] at htonat
    have hd_x := R13Shards.disj_of_inside_right hin hbo_disj_arr
    rcases hd_x with h0 | h0 | hd1 | hd2
    · simp at h0
    · simp at h0
    · dsimp only at hd1
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · dsimp only at hd2
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact hm

theorem txReadyStrong_store_encArray {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2))
    {mem' : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem' a = s.memory a) :
    TxReadyStrong { s with memory := mem' } := by
  let post : PanSemStateFiniteExact 64 F := { s with memory := mem' }
  have hA := h.1.1.1
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2
  obtain ⟨hW', how, hE'⟩ := store_encArray_world hA (txEnv_of_ready h) hW hx hin hm
  have hAp : ArenaReady post := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have harr : encArray s ∈ worldOwned s S Nd :=
    List.mem_append_left _ (List.mem_append_right _ (encArray_mem_fixed (txEnv_of_ready h)))
  have hu : R13Shards.IvlUnhit s post (locN s "tx", 384) :=
    R13Shards.ivlUnhit_single hm (by simp) (R13Shards.disj_of_inside_right hin (hT.2.1 _ (by simp) _ harr))
  have hur : 0 < memW s (locN s "tx" + 216) →
      R13Shards.IvlUnhit s post (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hn
    have hr := hT.2.2 hn
    exact R13Shards.ivlUnhit_single hm (by dsimp; omega) (R13Shards.disj_of_inside_right hin (hr.2 _ (by simp) _ harr))
  have hAt' := txAccessListAt_congr_unhit (post := post) hA.2 hA.1 hAp.1 le_rfl hT
    (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2) hu hur
  exact txReadyStrong_of_parts hAp hE' hW' hAt'

theorem txReadyStrong_assign_bal_index {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) (w : BitVec 64) :
    TxReadyStrong (setKvarHOLFinite .global (ofString "bal_index") (.val (.word w)) s) := by
  let post := setGlobalHOLFinite (ofString "bal_index") (.val (.word w)) s
  change TxReadyStrong post
  obtain ⟨S, Nd, hW, hT⟩ := h.2.2.2.2
  obtain ⟨hA', hW', how⟩ := R16Shards.worldTypedWith_setGlobal_untracked
    (gname := ofString "bal_index") (w := w)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    h.1.1.1 hW
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := by
    simp [post, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "bal_index" ≠ ofString "heap_ptr" from by decide]
  have hbo : globN post "bo" = globN s "bo" := by
    simp [post, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "bal_index" ≠ ofString "bo" from by decide]
  have hj : globN post "journal_cap" = globN s "journal_cap" := by
    simp [post, globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "bal_index" ≠ ofString "journal_cap" from by decide]
  have hT' : TxAccessListOK post S Nd := by
    obtain ⟨⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩, hd_tx, hr_fn⟩ := hT
    refine ⟨⟨hw, by rw [hhp]; exact hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩,
      by change IvlsDisj [(locN s "tx", 384)] (worldOwned post S Nd); rw [how]; exact hd_tx,
      fun hp => ⟨by rw [hhp]; exact (hr_fn hp).1,
        by change IvlsDisj [(memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))] (worldOwned post S Nd); rw [how]; exact (hr_fn hp).2⟩⟩
  have hE := txEnv_of_ready h
  have hE' : TxEnv post := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbo]; exact hE.bo_nz
    · change memW s (globN post "bo" + 24) ≠ 0; rw [hbo]; exact hE.bo24
    · change memW s (globN post "bo" + 32) ≠ 0; rw [hbo]; exact hE.bo32
    · change memW s (globN post "bo" + 40) ≠ 0; rw [hbo]; exact hE.bo40
    · change memW s (globN post "bo" + 72) ≠ 0; rw [hbo]; exact hE.bo72
    · change locN s "index" < memW s (globN post "bo" + 80); rw [hbo]; exact hE.idx_lt
    · rw [hj]; exact hE.jcap_nz
  exact txReadyStrong_of_parts hA' hE' hW' hT'

def encDst (off : Bool) : ExpHOL 64 :=
  .op .add ([.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
    .panop .mul [.var .local (ofString "index"), .const 16]] ++ if off then [.const 8] else [])

theorem encDst0_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64}
    (hx : evalAt s (encDst false) = some (.val (.word x))) :
    Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
  have hE := txEnv_of_ready h
  obtain ⟨S, Nd, hW, _⟩ := h.2.2.2.2
  have hhi := (R13Shards.ivl_allocated_bound h.1.1.1.2 (encArray_words hW.2.2.1 hE).1).2
  dsimp only [encArray] at hhi ⊢
  change evalAt s (.op .add
    [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
      .panop .mul [.var .local (ofString "index"), .const 16]]) = _ at hx
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
    rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
  rw [hld] at hx
  rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
  · simp [hidx_v] at hx
  rcases vidx with widx | _ | _
  · cases widx with
    | word idx_bv =>
      simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hE.idx_lt
      have hx' : x = abase + (idx_bv * 16#64 + 0) := hx.symm
      have hx_nat : x.toNat = abase.toNat + idx_bv.toNat * 16 := by
        rw [hx']
        simp only [BitVec.toNat_add, BitVec.toNat_mul]
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hz0]
        norm_num only [BitVec.toNat_ofNat] at *
        omega
      unfold Inside; dsimp only; omega
  · simp [hidx_v, valueIsWord] at hx
  · simp [hidx_v, valueIsWord] at hx

theorem encDst8_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64}
    (hx : evalAt s (encDst true) = some (.val (.word x))) :
    Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
  have hE := txEnv_of_ready h
  obtain ⟨S, Nd, hW, _⟩ := h.2.2.2.2
  have hhi := (R13Shards.ivl_allocated_bound h.1.1.1.2 (encArray_words hW.2.2.1 hE).1).2
  dsimp only [encArray] at hhi ⊢
  change evalAt s (.op .add
    [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
      .panop .mul [.var .local (ofString "index"), .const 16], .const 8]) = _ at hx
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
    rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
  rw [hld] at hx
  rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
  · simp [hidx_v] at hx
  rcases vidx with widx | _ | _
  · cases widx with
    | word idx_bv =>
      simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hE.idx_lt
      have hx' : x = abase + (idx_bv * 16#64 + (8#64 + 0)) := hx.symm
      have hx_nat : x.toNat = abase.toNat + idx_bv.toNat * 16 + 8 := by
        rw [hx']
        simp only [BitVec.toNat_add, BitVec.toNat_mul]
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hz0]
        norm_num only [BitVec.toNat_ofNat] at *
        omega
      unfold Inside; dsimp only; omega
  · simp [hidx_v, valueIsWord] at hx
  · simp [hidx_v, valueIsWord] at hx

def EncReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s ∧ ∃ a b : BitVec 64,
    s.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)])

theorem store_encSlot (off : Bool) :
    Hoare EncReady (.store (encDst off) (.rfield (if off then 1 else 0) (.var .local (ofString "enc"))))
      (fun r t => r = none → EncReady t) := by
  refine R13Shards.Hoare.store_fall fun s x v mem' h hx hv hst => ?_
  obtain ⟨a, b, he⟩ := h.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hmem⟩ := R13Shards.panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  have hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
    cases off
    · exact encDst0_inside h.1 hx
    · exact encDst8_inside h.1 hx
  exact ⟨txReadyStrong_store_encArray h.1 hdom hin hmem, a, b, he⟩

/-! ### Phase 1 Stage Ladder (`StageP 0..4`) -/

def SenderOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  Inside (locN s "sender", 24) sourceBase (globN s "heap_ptr") ∧
  WordsOK s (locN s "sender", 24)

theorem senderOK_grows {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) (hg' : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hl : locN post "sender" = locN s "sender") (h : SenderOK s) : SenderOK post := by
  unfold SenderOK
  rw [hl]
  exact ⟨⟨h.1.1, h.1.2.trans hhp⟩, R13Shards.wordsOK_transfer hg hg' h.2⟩

def IntrinsicOK {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ a b c : BitVec 64, s.locals.lookup (ofString "intrinsic") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c)]) ∧ a.toNat ≤ 16777216

def StageP (n : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => TxReadyStrong s ∧ (0 < n → SenderOK s) ∧ (1 < n → IntrinsicOK s) ∧
    (2 < n → locN s "regular_budget" ≤ 16777216) ∧ (3 < n → locN s "mgas" ≤ 16777216)

def stageNames (n : Nat) : List String :=
  ["tx", "index"] ++ (if 0 < n then ["sender"] else []) ++
    (if 1 < n then ["intrinsic"] else []) ++ (if 2 < n then ["regular_budget"] else []) ++
    (if 3 < n then ["mgas"] else [])

theorem localsOnly_stage (n : Nat) : LocalsOnly (stageNames n) (StageP n) := by
  intro F s locals k hl h
  have ht := hl "tx" (by simp [stageNames])
  have hi := hl "index" (by simp [stageNames])
  refine ⟨txReadyStrong_with_locals s locals k ht hi h.1, ?_, ?_, ?_, ?_⟩
  · intro hn
    have hs := hl "sender" (by simp [stageNames, hn])
    have he := locN_congr s locals k "sender" hs
    unfold SenderOK; rw [he]; exact h.2.1 hn
  · intro hn
    have hs := hl "intrinsic" (by simp [stageNames, hn])
    unfold IntrinsicOK; simp only [hs]; exact h.2.2.1 hn
  · intro hn
    have hs := hl "regular_budget" (by simp [stageNames, hn])
    rw [locN_congr s locals k "regular_budget" hs]; exact h.2.2.2.1 hn
  · intro hn
    have hs := hl "mgas" (by simp [stageNames, hn])
    rw [locN_congr s locals k "mgas" hs]; exact h.2.2.2.2 hn

theorem stage0 {F : Type} {s : PanSemStateFiniteExact 64 F} (h : TxReadyStrong s) : StageP 0 s :=
  ⟨h, by omega, by omega, by omega, by omega⟩

theorem stage4_validated {F : Type} {s : PanSemStateFiniteExact 64 F} (h : StageP 4 s) :
    PtxValidated s := ⟨h.1, (h.2.1 (by omega)).1, (h.2.1 (by omega)).2, h.2.2.2.2 (by omega)⟩

theorem stage_entry (n : Nat) (fn : MlS) (args : List (ExpHOL 64)) :
    CallEntryOn (StageP n) GuestInv fn args :=
  fun s _ _ callee _ _ hP _ _ => guestInv_callEntry s callee hP.1.1.1.1.1

theorem stage_grows {F : Type} {s post : PanSemStateFiniteExact 64 F} {n : Nat}
    (h : StageP n s) (hr : TxReadyStrong post)
    (hl : post.locals = s.locals) (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr") : StageP n post := by
  have hloc : ∀ k, locN post k = locN s k := by intro k; simp only [locN, hl]
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · intro hn
    exact senderOK_grows h.1.1.1.1.1 hr.1.1.1.1 hhp (hloc "sender") (h.2.1 hn)
  · intro hn
    unfold IntrinsicOK; rw [hl]; exact h.2.2.1 hn
  · intro hn; rw [hloc]; exact h.2.2.2.1 hn
  · intro hn; rw [hloc]; exact h.2.2.2.2 hn

theorem stage_after_readOnly {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {n : Nat}
    (h : StageP n s)
    (hr : post = { callEntryStateHOLFinite s callee with locals := post.locals, clock := post.clock }) :
    StageP n { post with locals := s.locals } := by
  have he : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [hr]; rfl
  rw [he]
  exact localsOnly_stage n s s.locals post.clock (fun _ _ => rfl) h

theorem resume_ro_stage {fname name : MlS} {n : Nat}
    (hro : ReadOnlyFn fname) (hne : ∀ k ∈ stageNames n, ofString k ≠ name)
    (args : List (ExpHOL 64)) : DecCallResumeOn (StageP n) (StageP n) name fname args := by
  intro F s vs body callee ret v post hc hP _ hl hrun
  have hspec := funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hrun]; simp)
  rw [hrun] at hspec
  have hro' := hspec (Or.inl ⟨v, rfl⟩)
  exact LocalsOnly.setVar (localsOnly_stage n) hne v _ (stage_after_readOnly hP hro')

theorem worldOK_callEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WorldOK s) (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    WorldOK (callEntryStateHOLFinite s callee) :=
  localsFree_worldOK s callee (s.clock - 1) h

theorem stage_after_scratchStep {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {r : Option (PanSemResultExact 64)}
    (hstep : WorldStep R gw keep Q (callEntryStateHOLFinite s callee) r post) (h : StageP n s)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : R (callEntryStateHOLFinite s callee) = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep) :
    StageP n { post with locals := s.locals } := by
  have hs : WorldStep (fun _ => R (callEntryStateHOLFinite s callee)) gw keep NoExtra s r post :=
    R13Shards.worldStep_with_locals hstep s.locals s.clock
  apply stage_grows h
    (txReadyStrong_scratchStep hs h.1 hgs hR hbo_gw hjcap_gw hbo_keep hoffs) rfl
  exact hstep.2.1

theorem resume_scratch_stage {fname name : MlS} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hwk : WorldKeeps WorldOK R gw keep Q fname)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (hne : ∀ k ∈ stageNames n, ofString k ≠ name)
    (args : List (ExpHOL 64)) : DecCallResumeOn (StageP n) (StageP n) name fname args := by
  intro F s vs body callee ret v post hc hP _ hl hrun
  have hs := funSpec_at_lookup hwk s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hrun]; simp)
  rw [hrun] at hs
  have hs' := hs (Or.inl ⟨v, rfl⟩)
  apply LocalsOnly.setVar (localsOnly_stage n) hne v
  exact stage_after_scratchStep hs' hP hgs (hR _) hbo_gw hjcap_gw hbo_keep hoffs

theorem hoare_call_scratch_stage {fname : MlS} {n : Nat}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)} {boKeep : List Nat}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    (hwk : WorldKeeps WorldOK R gw keep Q fname)
    {gs : List (String × Nat × Nat)} (hgs : ScratchSpec gs)
    (hR : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), R s = gs.map (fun e => bufferRegion s (e.1, e.2.2)))
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjcap_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbo_keep : ("bo", boKeep) ∈ keep)
    (hoffs : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat), k ∈ boKeep)
    (args : List (ExpHOL 64)) :
    Hoare (StageP n) (.call (some (none, none)) fname args) (fun r t => r = none → StageP n t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hP _ hl hb
  have hs := funSpec_at_lookup hwk s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hs
  exact stage_after_scratchStep (hs (Or.inl ⟨v, rfl⟩)) hP hgs (hR _)
    hbo_gw hjcap_gw hbo_keep hoffs

/-! ### Phase 1 Transitions (`encode_transaction`, `alloc(24)`, `recover_sender`, `validate_transaction`, `min`) -/

theorem resume_encode (h : PtxCallees) :
    DecCallResumeShapeOn TxReadyStrong EncReady (ofString "enc") (.comb [.one, .one])
      (ofString "encode_transaction") [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hP ha hl hb hsh
  obtain ⟨tv, he, ht⟩ := params_one_value s (ofString "encode_transaction") (ofString "tx")
    .one _ (.comb [.one, .one]) (by rw [hc]; exact lookup_encode_transaction)
    (.var .local (ofString "tx")) vs body callee ret ha hl
  have htx : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := ht.trans he.symm
  have hV := txValid_with_locals s callee (s.clock - 1) htx (txReadyStrong_txValid hP)
  have hs := funSpec_at_lookup h.wk_encode_transaction s hc vs body callee ret hl
    ⟨worldOK_callEntry hP.1.1 callee, hV⟩ (by rw [hb]; simp)
  rw [hb] at hs
  have hstage := stage_after_scratchStep (hs (Or.inl ⟨v, rfl⟩)) (stage0 hP)
    (gs := []) (by simp [ScratchSpec]) rfl (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
  have hready := txReadyStrong_with_locals { post with locals := s.locals }
    (s.locals.update (ofString "enc", v)) post.clock
    (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "enc" ≠ ofString "tx" from by decide])
    (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "enc" ≠ ofString "index" from by decide]) hstage.1
  obtain ⟨a, b, rfl⟩ := shape_pair_words hsh
  refine ⟨hready, a, b, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

def SenderAllocated {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s ∧ SenderOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListOK s S Nd ∧
    (∀ j ∈ worldTypedIvls s S Nd, Disj (locN s "sender", 24) j) ∧
    Disj (locN s "tx", 384) (locN s "sender", 24) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (locN s "sender", 24))

theorem resume_alloc_sender (h : PtxCallees) :
    DecCallResumeOn (StageP 0) SenderAllocated (ofString "sender") (ofString "alloc") [.const 24] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨nv, he, hn⟩ := params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact lookup_alloc) (.const 24) vs body callee ret ha hl
  have hnv : nv = .val (.word (24#64)) := by simpa [evalAt, evalHOLExact] using he.symm
  subst nv
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = 24 := by simp [locN, callEntryStateHOLFinite, hn]
  have hrt := funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hP.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hrt
  obtain ⟨w, hv, _, _, hfb⟩ := hrt v rfl
  subst v
  rw [hcn] at hfb
  change FreshBlock (callEntryStateHOLFinite s callee) post w.toNat 24 at hfb
  have hpFresh : globN s "heap_ptr" ≤ w.toNat := hfb.2.1.1
  have hs := funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hs
  have hstep := hs (Or.inl ⟨.val (.word w), rfl⟩)
  have hsready := stage_after_scratchStep hstep hP (gs := []) (by simp [ScratchSpec]) rfl
    (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
  obtain ⟨S, Nd, hW, hT⟩ := hP.1.2.2.2.2
  obtain ⟨S', Nd', _, hW', hog, hfr, hret⟩ := hstep.2.2.2.2 S Nd
    ((R13Shards.worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  obtain ⟨w', heq, hav⟩ := hret (.val (.word w)) rfl
  have hww : w' = w := by cases heq; rfl
  subst w'
  dsimp only at hav
  rw [hcn] at hav
  change IvlsDisj [(w.toNat, 24)] (worldOwned post S' Nd') at hav
  have hT' := txAccessListOK_survives_step hP.1.1.1.1 hstep.1.1 hstep.2.1 hW
    (R := []) (by simp) hog hfr hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨_, _, hu⟩ := R13Shards.heap_ivl_survives_step hP.1.1.1.1.2 hstep.2.1
    (R13Shards.worldOwned_zero_aligned hW) (R := []) (by simp) hog hfr hT.1.1.1 (by simp)
    hT.1.2.1 (fun j hj => hT.2.1 _ (by simp) j hj) (by simp)
  have hhi := (R13Shards.ivl_allocated_bound hP.1.1.1.1.2 (Or.inl hT.1.2.1)).2
  have hm208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    R13Shards.memW_eq_of_ivlUnhit hu (by have := hT.1.1.1; omega) hhi ⟨by omega, by omega⟩
  have hm216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    R13Shards.memW_eq_of_ivlUnhit hu (by have := hT.1.1.1; omega) hhi ⟨by omega, by omega⟩
  let resumed := setVarHOLFinite (ofString "sender") (.val (.word w)) { post with locals := s.locals }
  have htx : resumed.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "sender" ≠ ofString "tx" from by decide]
  have hidx : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "sender" ≠ ofString "index" from by decide]
  have hsender : locN resumed "sender" = w.toNat := by
    simp [resumed, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have htxN : locN resumed "tx" = locN s "tx" := locN_congr s resumed.locals post.clock "tx" htx
  have hrdy : TxReadyStrong resumed := txReadyStrong_with_locals { post with locals := s.locals }
    resumed.locals post.clock htx hidx hsready.1
  refine ⟨hrdy, ?_, S', Nd', ?_, ?_, ?_, ?_, ?_⟩
  · unfold SenderOK
    rw [hsender]
    exact ⟨⟨hP.1.1.1.1.2.1.trans hpFresh, hfb.2.1.2⟩, hfb.2.2⟩
  · exact (R13Shards.worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hW'
  · exact txAccessListOK_with_locals { post with locals := s.locals } resumed.locals post.clock htx hT'
  · rw [hsender]
    intro j hj
    exact hav _ (by simp) j (R13Shards.worldTypedIvls_sub_worldOwned hj)
  · rw [htxN, hsender]
    exact Or.inr (Or.inr (Or.inl (hT.1.2.1.2.trans hpFresh)))
  · rw [htxN, hsender]
    change 0 < memW post (locN s "tx" + 216) →
      Disj (memW post (locN s "tx" + 208), 24 * memW post (locN s "tx" + 216)) (w.toNat, 24)
    rw [hm208, hm216]
    intro hn
    exact Or.inr (Or.inr (Or.inl ((hT.2.2 hn).1.2.trans hpFresh)))

def recoverArgs : List (ExpHOL 64) := [.var .local (ofString "tx"),
  .load .one (.op .add [.var .global (ofString "be"), .const 0]), .var .local (ofString "sender")]

theorem hoare_recover_sender (h : PtxCallees) :
    Hoare SenderAllocated (.call (some (none, none)) (ofString "recover_sender_with_chain_id") recoverArgs)
      (fun r t => r = none → StageP 1 t) := by
  apply R13Shards.Hoare.call0_resume
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨v1, _, v3, he1, _, he3, hp, _, hr⟩ := params_three_values s
    (ofString "recover_sender_with_chain_id") (ofString "tx") (ofString "chain_id") (ofString "out20")
    .one .one .one _ .one (by rw [hc]; exact lookup_recover_sender_with_chain_id)
    (.var .local (ofString "tx"))
    (.load .one (.op .add [.var .global (ofString "be"), .const 0])) (.var .local (ofString "sender"))
    vs body callee ret ha hl
  have htx_cal : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := hp.trans he1.symm
  have hout : locN (callEntryStateHOLFinite s callee) "out20" = locN s "sender" := by
    simp only [locN, callEntryStateHOLFinite, hr, show s.locals.lookup (ofString "sender") = some v3 from he3]
  have hV_cal := txValid_with_locals s callee (s.clock - 1) htx_cal (txReadyStrong_txValid hP.1)
  have hspec := funSpec_at_lookup h.wk_recover_sender_with_chain_id s hc vs body callee ret hl
    ⟨worldOK_callEntry hP.1.1.1 callee, hV_cal⟩ (by rw [hb]; simp)
  rw [hb] at hspec
  have hstep := hspec (Or.inl ⟨v, rfl⟩)
  have hs := R13Shards.worldStep_with_locals hstep s.locals s.clock
  change WorldStep (fun _ => [(locN (callEntryStateHOLFinite s callee) "out20", 20),
    bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)]) _ _ _ s _ post at hs
  rw [hout] at hs
  obtain ⟨S, Nd, hW, hT, hTyped, hTx, hRecs⟩ := hP.2.2
  have hA := hP.1.1.1.1
  have hin : Inside (locN s "sender", 20) (locN s "sender") (locN s "sender" + 24) := ⟨le_rfl, by omega⟩
  have hRT : IvlsDisj [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)] (worldTypedIvls s S Nd) := by
    intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact R13Shards.disj_of_inside_left hin (hTyped j hj)
    · exact bufferRegion_disj_le hW ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hW ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hW ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  have hR0 : ∀ i ∈ [(locN s "sender", 20), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("u256_ws", 640)], i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · simp
    · exact bufferRegion_zero_aligned s "keccak_pad" 136 (by decide)
    · exact bufferRegion_zero_aligned s "keccak_st" 200 (by decide)
    · exact bufferRegion_zero_aligned s "u256_ws" 640 (by decide)
  have hReady : TxReadyStrong { post with locals := s.locals } := by
    apply txReadyStrong_worldStep hs hA (txEnv_of_ready hP.1) hW hT
      (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide)
      hR0 hRT
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin hTx
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => hT.2.1 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
    · intro hn i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact R13Shards.disj_of_inside_right hin (hRecs hn)
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("keccak_pad", 136) (by decide) 136 le_rfl
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("keccak_st", 200) (by decide) 200 le_rfl
      · exact heap_ivl_disj_bufferRegion_le (fun j hj => (hT.2.2 hn).2 _ (by simp) j hj) ("u256_ws", 640) (by decide) 640 le_rfl
  have hSender := senderOK_grows hA.1 hReady.1.1.1.1 hs.2.1 rfl hP.2.1
  exact ⟨hReady, fun _ => hSender, by omega, by omega, by omega⟩

theorem resume_validate (h : PtxCallees) :
    DecCallResumeOn (StageP 1) (StageP 2) (ofString "intrinsic") (ofString "validate_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  have hkeep := resume_ro_stage (n := 1) h.ro_validate_transaction
    (name := ofString "intrinsic") (by decide) _ s vs body callee ret v post hc hP ha hl hb
  have hs := funSpec_at_lookup h.rv_validate_transaction s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨a, b, c, hv, hle⟩ := hs v rfl
  subst v
  refine ⟨hkeep.1, fun _ => hkeep.2.1 (by omega), ?_, by omega, by omega⟩
  intro _
  exact ⟨a, b, c, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hle⟩

def regularBudgetExp : ExpHOL 64 :=
  .op .sub [.const 16777216, .rfield 0 (.var .local (ofString "intrinsic"))]

theorem declare_regular_budget_aux {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (cap : BitVec 64) (hc : cap.toNat = 16777216) (hP : StageP 2 s)
    (he : evalAt s (.op .sub [.const cap, .rfield 0 (.var .local (ofString "intrinsic"))]) = some v) :
    StageP 3 (setVarHOLFinite (ofString "regular_budget") v s) := by
  obtain ⟨a, b, c, hi, hle⟩ := hP.2.2.1 (by omega)
  have hv : v = .val (.word (cap - a)) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hi, valueIsWord, valueWord, wordOpHOL, wordOp] using he.symm
  subst v
  have hkeep := LocalsOnly.setVar (localsOnly_stage 2) (name := ofString "regular_budget")
    (by decide) (.val (.word (cap - a))) s hP
  refine ⟨hkeep.1, (fun _ => hkeep.2.1 (by omega)), (fun _ => hkeep.2.2.1 (by omega)), ?_, by omega⟩
  intro _
  rw [locN_setVar_same]
  have ha : a ≤ cap := by change a.toNat ≤ cap.toNat; omega
  rw [BitVec.toNat_sub_of_le ha]
  omega

theorem declare_regular_budget {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hP : StageP 2 s) (he : evalAt s regularBudgetExp = some v) :
    StageP 3 (setVarHOLFinite (ofString "regular_budget") v s) :=
  declare_regular_budget_aux s v (16777216#64) rfl hP he

theorem resume_min (h : PtxCallees) :
    DecCallResumeOn (StageP 3) (StageP 4) (ofString "mgas") (ofString "min")
      [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨v1, _, he1, _, hpa, _⟩ := params_two_values s (ofString "min") (ofString "a") (ofString "b")
    .one .one _ .one (by rw [hc]; exact lookup_min)
    (.var .local (ofString "regular_budget")) (.var .local (ofString "execution_gas")) vs body callee ret ha hl
  have hca : locN (callEntryStateHOLFinite s callee) "a" = locN s "regular_budget" := by
    simp only [locN, callEntryStateHOLFinite, hpa,
      show s.locals.lookup (ofString "regular_budget") = some v1 from he1]
  have hkeep := resume_ro_stage (n := 3) h.ro_min (name := ofString "mgas") (by decide) _
    s vs body callee ret v post hc hP ha hl hb
  have hs := funSpec_at_lookup h.rv_min s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨w, hv, hle⟩ := hs v rfl
  subst v
  refine ⟨hkeep.1, (fun _ => hkeep.2.1 (by omega)), (fun _ => hkeep.2.2.1 (by omega)),
    (fun _ => hkeep.2.2.2.1 (by omega)), ?_⟩
  intro _
  rw [locN_setVar_same]
  change w.toNat ≤ locN (callEntryStateHOLFinite s callee) "a" at hle
  rw [hca] at hle
  exact hle.trans (hP.2.2.2.1 (by omega))

def chainGuard : ProgHOL 64 :=
  .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "cid"))) (.const 0))
    (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "cid")))
        (.load .one (.op .add [.var .global (ofString "be"), .const 0])))
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
  .decCall (ofString "bgp") (.comb [.one, .one, .one, .one]) (ofString "calculate_blob_gas_price")
    [.load .one (.op .add [.var .global (ofString "be"), .const 96])]
    (.decCall (ofString "bgf") (.comb [.one, .one, .one, .one, .one]) (ofString "fee_mul")
      [.var .local (ofString "tx_blob_gas_used"), .var .local (ofString "bgp")]
      (.assign .local (ofString "blob_gas_fee")
        (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
          .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))])))

theorem blobBranch_hoare (h : PtxCallees) :
    Hoare (StageP 2) blobBranch (fun r t => r = none → StageP 2 t) := by
  apply R13Shards.Hoare.decCall_fall (names := stageNames 2) (by decide) (localsOnly_stage 2)
  · exact resume_scratch_stage h.wk_calculate_blob_gas_price
      (gs := [("u256_ws", 640, 640)]) (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
  · apply R13Shards.Hoare.decCall_fall (names := stageNames 2) (by decide) (localsOnly_stage 2)
    · exact resume_ro_stage h.ro_fee_mul (by decide) _
    · apply Hoare.assign
      · intro F s v hP _
        exact fun _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hP
      · exact fun _ _ hr => by cases hr

theorem blobBranch_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (StageP 2) blobBranch
      ((K.calculate_blob_gas_price + 1) + (K.fee_mul + 1)) := by
  have hb : TerminatingProgBoundedOn GuestInv blobBranch (K.calculate_blob_gas_price + (K.fee_mul + 0 + 1) + 1) :=
    TerminatingProgBoundedOn.decCall_guestInv h.fb_calculate_blob_gas_price
    (ofString "bgp") (.comb [.one, .one, .one, .one]) _
    (TerminatingProgBoundedOn.decCall_guestInv h.fb_fee_mul
      (ofString "bgf") (.comb [.one, .one, .one, .one, .one]) _
      (bound_of_clock (fun s => clock_assign s .local (ofString "blob_gas_fee")
        (.rstruct [.rfield 1 (.var .local (ofString "bgf")), .rfield 2 (.var .local (ofString "bgf")),
          .rfield 3 (.var .local (ofString "bgf")), .rfield 4 (.var .local (ofString "bgf"))]))))
  intro F s hc hp
  have hr := hb s hc hp.1.1.1.1.1
  simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

def phase1Budget (b : Nat) : Nat := ((K.state_fresh_tx + 1) + (((0) + (((K.encode_transaction) + (((0) + (((0) + (((0) + (((K.tx_chain_id) + (((0) + (((K.alloc) + (((K.recover_sender_with_chain_id + 1) + (((0) + (((K.validate_transaction) + (((0) + (((K.check_transaction) + (((0) + (((K.calculate_total_blob_gas) + (((K.get_account) + (((0) + (((max ((K.calculate_blob_gas_price + 1) + (K.fee_mul + 1)) 0) + (((K.fee_mul) + (((K.min) + (((K.increment_nonce + 1) + (((K.u256_sub + 1) + (((K.u256_sub + 1) + (((K.set_account_balance + 1) + (((0) + (b))))))))))) + 1)) + 1)))))) + 1)) + 1)))) + 1)))) + 1)))))) + 1)))) + 1)))))))) + 1)))))

theorem eval_is_word_op {F : Type} {s : PanSemStateFiniteExact 64 F} {bop : BinOp}
    {es : List (ExpHOL 64)} {v : ValueHOL 64} (h : evalAt s (.op bop es) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalAt, evalHOLExact] at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, _, rfl⟩ := h
      exact ⟨w, rfl⟩
    · cases h
  · cases h

theorem hoare_assign_bal_index :
    Hoare (StageP 0)
      (.assign .global (ofString "bal_index") (.op .add [.var .local (ofString "index"), .const 1#64]))
      (fun r t => r = none → StageP 0 t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  revert hr
  split
  · simp
  · rename_i v hv
    split
    · intro _
      obtain ⟨w, rfl⟩ := eval_is_word_op hv
      exact stage0 (txReadyStrong_assign_bal_index hP.1 w)
    · simp

end PtxP1

theorem ptxPhase1_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidated tail b) :
    TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 tail) (ptxCost1 + b) := by
  open PtxP1 in
  have hb : TerminatingProgBoundedOn (StageP 0) (ptxPhase1 tail) (phase1Budget b) := by
    unfold phase1Budget ptxPhase1 ptxCode
    simp only [sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
      Option.map_none, Option.map_some, List.map_cons, List.map_nil, spinePlug]
    -- 0: refresh transaction state.
    refine R13Shards.seq_bound_trans (Q := StageP 0) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_state_fresh_tx none [])
      (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact hoare_call_scratch_stage h.wk_state_fresh_tx (gs := []) (by simp [ScratchSpec])
        (fun _ => rfl) (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
        (by simp) (by decide) []
    -- 1: record the transaction index (`bal_index := index + 1`).
    refine R13Shards.seq_bound_trans (Q := StageP 0) (bound_of_clock (fun s => clock_assign s _ _ _))
      hoare_assign_bal_index ?_
    -- 2: obtain the pair used by the two output-array stores.
    refine decCall_shape_bound (Q := EncReady) h.fb_encode_transaction _ _ _ (stage_entry 0 _ _) ?_ ?_
    · intro F s vs body callee ret v post hc hp ha hl hr hsh
      exact resume_encode h s vs body callee ret v post hc hp.1 ha hl hr hsh
    -- 3--5: output encoding and resume the invariant without the temporary pair.
    refine R13Shards.seq_bound_trans (Q := EncReady) (bound_of_clock (fun s => R13Shards.clock_store s _ _)) (store_encSlot false) ?_
    refine R13Shards.seq_bound_trans (Q := EncReady) (bound_of_clock (fun s => R13Shards.clock_store s _ _)) (store_encSlot true) ?_
    refine R13Shards.seq_bound_trans (Q := StageP 0) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => stage0 hp.1)) ?_
    -- 6--7: chain-id lookup and rejecting guard.
    refine TerminatingProgBoundedOn.decCall_on h.fb_tx_chain_id _ _ _ (stage_entry 0 _ _)
      (resume_ro_stage h.ro_tx_chain_id (by decide) _) ?_
    refine R13Shards.seq_bound_trans (Q := StageP 0) chainGuard_bound chainGuard_hoare ?_
    -- 8--10: fresh sender buffer and recovery.
    refine TerminatingProgBoundedOn.decCall_on (Q := SenderAllocated) h.fb_alloc _ _ _ (stage_entry 0 _ _)
      (resume_alloc_sender h) ?_
    refine R13Shards.seq_bound_trans (Q := StageP 1) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_recover_sender_with_chain_id none _)
      (fun _ hp => hp.1.1.1.1.1)) (hoare_recover_sender h) ?_
    refine R13Shards.seq_bound_trans (Q := StageP 1) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
    -- 11--13: validation supplies the intrinsic-gas bound.
    refine TerminatingProgBoundedOn.decCall_on h.fb_validate_transaction _ _ _ (stage_entry 1 _ _)
      (resume_validate h) ?_
    refine R13Shards.seq_bound_trans (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
    -- 14--19: fee checks, account lookup, and the blob-fee local.
    refine TerminatingProgBoundedOn.decCall_on (Q := StageP 2) h.fb_check_transaction _ _ _ (stage_entry 2 _ _) ?_ ?_
    · exact resume_scratch_stage h.wk_check_transaction
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
    refine R13Shards.seq_bound_trans (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_calculate_total_blob_gas _ _ _ (stage_entry 2 _ _)
      (resume_ro_stage h.ro_calculate_total_blob_gas (by decide) _) ?_
    refine TerminatingProgBoundedOn.decCall_on (Q := StageP 2) h.fb_get_account _ _ _ (stage_entry 2 _ _) ?_ ?_
    · exact resume_scratch_stage h.wk_get_account
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
    refine R13Shards.seq_bound_trans (Q := StageP 2) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => hp)) ?_
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
    -- 20: the optional blob-fee calculation.
    refine R13Shards.seq_bound_trans (Q := StageP 2) (TerminatingProgBoundedOn.ite_on (blobBranch_bound h) (bound_of_clock clock_skip)) ?_ ?_
    · exact Hoare.ite (Hoare.mono (blobBranch_hoare h) (fun _ hp => hp.1))
        (Hoare.skip (fun _ hp _ => hp.1)) (fun _ _ hr => by cases hr)
    -- 21--25: arithmetic locals and the bounded regular gas budget.
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.decCall_on h.fb_fee_mul _ _ _ (stage_entry 2 _ _)
      (resume_ro_stage h.ro_fee_mul (by decide) _) ?_
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 2) _ (by decide) _ _ ?_
    refine R13Shards.dec_bound_trans declare_regular_budget ?_
    -- 26--29: min caps message gas; the world update preserves it.
    refine TerminatingProgBoundedOn.decCall_on h.fb_min _ _ _ (stage_entry 3 _ _) (resume_min h) ?_
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 4) _ (by decide) _ _ ?_
    refine R13Shards.seq_bound_trans (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_increment_nonce none _)
      (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact hoare_call_scratch_stage h.wk_increment_nonce
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) _
    refine TerminatingProgBoundedOn.dec_onLocals (localsOnly_stage 4) _ (by decide) _ _ ?_
    -- 30--33: subtract the fees, write the balance, and enter the caller's tail.
    refine R13Shards.seq_bound_trans (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub (some (.local, ofString "bal")) _)
      (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact R13Shards.Hoare.callLocal_resume (resume_ro_stage h.ro_u256_sub (by decide) _)
    refine R13Shards.seq_bound_trans (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub (some (.local, ofString "bal")) _)
      (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact R13Shards.Hoare.callLocal_resume (resume_ro_stage h.ro_u256_sub (by decide) _)
    refine R13Shards.seq_bound_trans (Q := StageP 4) (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_set_account_balance none _)
      (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact hoare_call_scratch_stage h.wk_set_account_balance
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) _
    exact R13Shards.seq_bound_trans (Q := PtxValidated) (bound_of_clock clock_skip) (Hoare.skip (fun _ hp _ => stage4_validated hp)) htail
  have he : PtxP1.phase1Budget b = ptxCost1 + b := by
    simp only [PtxP1.phase1Budget, ptxCost1, Nat.add_zero, Nat.zero_add, Nat.max_zero,
      Nat.add_comm, Nat.add_left_comm]
  rw [he] at hb
  intro F s hc hp
  exact hb s hc (PtxP1.stage0 hp)

end InitECandidate.Solver.Wave8GuestInv.R16Shards
