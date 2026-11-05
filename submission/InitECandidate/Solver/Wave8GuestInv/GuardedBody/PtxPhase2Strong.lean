import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup

/-- Shape information needed by the untyped stores of Phase 2. `price` is
the four-word fee value, whereas `mgas` and `reservoir` are scalar words. -/
structure PtxPhase2LocalShapes {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  scalar : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String),
    ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))
  price : ∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])
  enc : ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
    some (.rStruct [.val (.word a), .val (.word b)])
  intrinsic : ∃ a b c : BitVec 64, s.locals.lookup (ofString "intrinsic") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c)])

/-- A nonzero numeric local projection rules out the default-value cases. -/
theorem phase1_word_of_locN_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {name : String} (hn : locN s name ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)) := by
  cases hl : s.locals.lookup (ofString name) with
  | none => simp [locN, hl] at hn
  | some v =>
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · exact ⟨w, rfl⟩
    · simp [locN, hl] at hn
    · simp [locN, hl] at hn

theorem phase1_txReadyStrong_tx_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : TxReadyStrong s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "tx") = some (.val (.word w)) := by
  apply phase1_word_of_locN_ne_zero
  have hb := (R16Shards.PtxP1.txReadyStrong_txValid hp).2.1.1
  change InitE.sourceBase ≤ locN s "tx" at hb
  have hs : 0 < InitE.sourceBase := by decide
  omega

theorem phase1_index_word_of_add {F : Type} {s : PanSemStateFiniteExact 64 F}
    {v : ValueHOL 64}
    (he : evalAt s (.op .add [.var .local (ofString "index"), .const 1#64]) = some v) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "index") = some (.val (.word w)) := by
  cases hl : s.locals.lookup (ofString "index") with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl] at he
  | some value =>
    rcases value with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · exact ⟨w, rfl⟩
    · simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord] at he
    · simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord] at he

theorem phase1_assign_bal_index_shapes :
    Hoare (R16Shards.PtxP1.StageP 0)
      (.assign .global (ofString "bal_index")
        (.op .add [.var .local (ofString "index"), .const 1#64]))
      (fun r s => r = none → R16Shards.PtxP1.StageP 0 s ∧
        ∀ n ∈ (["tx", "index"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hstage := R16Shards.PtxP1.hoare_assign_bal_index.run s hc hp hnt hr
  refine ⟨hstage, ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  revert hr
  split
  · simp
  · rename_i v hv
    split
    · intro _ n hn
      obtain ⟨w, rfl⟩ := R16Shards.PtxP1.eval_is_word_op hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · simpa [setKvarHOLFinite, setGlobalHOLFinite] using phase1_txReadyStrong_tx_word hp.1
      · simpa [setKvarHOLFinite, setGlobalHOLFinite] using phase1_index_word_of_add hv
    · simp

/-- R11 entry interface for the strengthened Phase 2 proof. -/
def PtxValidatedStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxValidated s ∧ PtxPhase2LocalShapes s

theorem ptxValidatedStrong_mgas {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxValidatedStrong s) :
    ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)) ∧
      w.toNat ≤ 16777216 := by
  obtain ⟨w, hw⟩ := h.2.scalar "mgas" (by simp)
  refine ⟨w, hw, ?_⟩
  have hb := h.1.2.2.2
  simpa [locN, hw] using hb

theorem ptxValidatedStrong_price_length {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxValidatedStrong s) {v : ValueHOL 64}
    (hv : s.locals.lookup (ofString "price") = some v) :
    (flattenHOL v).length = 4 := by
  obtain ⟨a, b, c, d, hp⟩ := h.2.price
  rw [hp] at hv
  cases hv
  simp [flattenHOL]

theorem ptxPhase2LocalShapes_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (h : PtxPhase2LocalShapes s) :
    PtxPhase2LocalShapes { s with locals := locals, clock := clock } := by
  constructor
  · intro name hn
    obtain ⟨w, hw⟩ := h.scalar name hn
    refine ⟨w, ?_⟩
    change locals.lookup (ofString name) = _
    rw [hl name (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)]
    exact hw
  · simpa only [hl "price" (by simp)] using h.price
  · simpa only [hl "enc" (by simp)] using h.enc
  · simpa only [hl "intrinsic" (by simp)] using h.intrinsic

/-- Preserve the scalar witness produced by `min`, which the original
Phase 1 stage predicate retained only through its numeric projection. -/
theorem phase1_resume_min_word (h : PtxCallees) :
    DecCallResumeOn (R16Shards.PtxP1.StageP 3)
      (fun s => R16Shards.PtxP1.StageP 4 s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
      (ofString "mgas") (ofString "min")
      [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  have hstage := R16Shards.PtxP1.resume_min h s vs body callee ret v post hc hP ha hl hb
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.rv_min s hc vs body callee ret hl
    (guestInv_callEntry s callee hP.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hs
  obtain ⟨w, hv, _⟩ := hs v rfl
  subst v
  refine ⟨hstage, w, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Shape facts concern only caller locals and therefore survive calls whose
memory/world postconditions are proved separately. -/
theorem ptxPhase2LocalShapes_restore {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : PtxPhase2LocalShapes s) :
    PtxPhase2LocalShapes { post with locals := s.locals } := by
  exact ⟨h.scalar, h.price, h.enc, h.intrinsic⟩

theorem ptxPhase2LocalShapes_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PtxPhase2LocalShapes s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    PtxPhase2LocalShapes (setVarHOLFinite name v s) := by
  apply ptxPhase2LocalShapes_with_locals s _ s.clock _ h
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- The scalar gas witness survives the caller-local restoration at every
subsequent call, including the balance-return assignment. -/
theorem phase1_mgas_word_resume {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (h : ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
    (name : MlS) (v : ValueHOL 64) (hne : name ≠ ofString "mgas") :
    ∃ w : BitVec 64,
      (setVarHOLFinite name v { post with locals := s.locals }).locals.lookup (ofString "mgas") =
        some (.val (.word w)) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hw⟩

/-- Retain the scalar pointer returned by sender allocation instead of keeping
only its numeric projection in the allocated-buffer predicate. -/
theorem phase1_resume_alloc_sender_word (h : PtxCallees) :
    DecCallResumeOn (R16Shards.PtxP1.StageP 0)
      (fun s => R16Shards.PtxP1.SenderAllocated s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "sender") = some (.val (.word w)))
      (ofString "sender") (ofString "alloc") [.const 24] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hallocated := R16Shards.PtxP1.resume_alloc_sender h s vs body callee ret v post
    hc hp ha hl hb
  have hrt := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hrt
  obtain ⟨w, hv, _⟩ := hrt v rfl
  subst v
  refine ⟨hallocated, w, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem phase1_resume_encode_shapes (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => TxReadyStrong s ∧ ∀ n ∈ (["tx", "index"] : List String),
        ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
      (fun s => R16Shards.PtxP1.EncReady s ∧ ∀ n ∈ (["tx", "index"] : List String),
        ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
      (ofString "enc") (.comb [.one, .one]) (ofString "encode_transaction")
      [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  refine ⟨R16Shards.PtxP1.resume_encode h s vs body callee ret v post hc hp.1 ha hl hb hsh, ?_⟩
  intro n hn
  have hne : ofString "enc" ≠ ofString n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl <;> decide
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hp.2 n hn

theorem phase1_store_encSlot_shapes (off : Bool) :
    Hoare (fun s => R16Shards.PtxP1.EncReady s ∧
      ∀ n ∈ (["tx", "index"] : List String),
        ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
      (.store (R16Shards.PtxP1.encDst off)
        (.rfield (if off then 1 else 0) (.var .local (ofString "enc"))))
      (fun r s => r = none → R16Shards.PtxP1.EncReady s ∧
        ∀ n ∈ (["tx", "index"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) := by
  have hs : Hoare
      (fun s => ∀ n ∈ (["tx", "index"] : List String),
        ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
      (.store (R16Shards.PtxP1.encDst off)
        (.rfield (if off then 1 else 0) (.var .local (ofString "enc"))))
      (fun r s => r = none → ∀ n ∈ (["tx", "index"] : List String),
        ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) := by
    apply Hoare.store_fall
    intro F s x v mem hp hx hv hst
    exact hp
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨(R16Shards.PtxP1.store_encSlot off).run s hc hp.1 hnt hr,
    hs.run s hc hp.2 hnt hr⟩

theorem phase1_chainGuard_keeps
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) :
    Hoare P R16Shards.PtxP1.chainGuard (fun r s => r = none → P s) := by
  apply Hoare.ite
  · apply Hoare.ite
    · exact ⟨fun s _ _ _ hr => (R16Shards.PtxP1.raise_ne_none s _ _ hr).elim⟩
    · exact Hoare.skip (fun _ hp _ => hp.1.1)
    · exact fun _ _ hr => by cases hr
  · exact Hoare.skip (fun _ hp _ => hp.1)
  · exact fun _ _ hr => by cases hr

theorem phase1_resume_chain_id_shapes (h : PtxCallees) :
    DecCallResumeOn
      (fun s => R16Shards.PtxP1.StageP 0 s ∧
        (∀ n ∈ (["tx", "index"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (fun s => R16Shards.PtxP1.StageP 0 s ∧
        (∀ n ∈ (["tx", "index"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (ofString "cid") (ofString "tx_chain_id") [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  refine ⟨R16Shards.PtxP1.resume_ro_stage h.ro_tx_chain_id (by decide) _
    s vs body callee ret v post hc hp.1 ha hl hb, ?_, ?_⟩
  · intro n hn
    have hne : ofString "cid" ≠ ofString n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> decide
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hp.2.1 n hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "cid" ≠ ofString "enc" from by decide] using hp.2.2

theorem phase1_resume_alloc_sender_shapes (h : PtxCallees) :
    DecCallResumeOn
      (fun s => R16Shards.PtxP1.StageP 0 s ∧
        (∀ n ∈ (["tx", "index"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (fun s => R16Shards.PtxP1.SenderAllocated s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (ofString "sender") (ofString "alloc") [.const 24] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hs := phase1_resume_alloc_sender_word h s vs body callee ret v post hc hp.1 ha hl hb
  refine ⟨hs.1, ?_, ?_⟩
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "sender" ≠ ofString "tx" from by decide] using hp.2.1 "tx" (by simp)
    · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "sender" ≠ ofString "index" from by decide] using hp.2.1 "index" (by simp)
    · exact hs.2
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "sender" ≠ ofString "enc" from by decide] using hp.2.2

/-- Calls with discarded return values restore every caller-local witness. -/
theorem phase1_call0_word (name fn : MlS) (args : List (ExpHOL 64)) :
    Hoare (fun s => ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w)))
      (.call (some (none, none)) fn args)
      (fun r s => r = none → ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w))) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hb
  exact hp

theorem phase1_recover_sender_word (h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.SenderAllocated s ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "sender") = some (.val (.word w)))
      (.call (some (none, none)) (ofString "recover_sender_with_chain_id") R16Shards.PtxP1.recoverArgs)
      (fun r s => r = none → R16Shards.PtxP1.StageP 1 s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "sender") = some (.val (.word w))) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨(R16Shards.PtxP1.hoare_recover_sender h).run s hc hp.1 hnt hr,
    (phase1_call0_word (ofString "sender") _ _).run s hc hp.2 hnt hr⟩

/-- Frame all pre-price witnesses through sender recovery at once. -/
theorem phase1_recover_sender_shapes (h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.SenderAllocated s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (.call (some (none, none)) (ofString "recover_sender_with_chain_id") R16Shards.PtxP1.recoverArgs)
      (fun r s => r = none → R16Shards.PtxP1.StageP 1 s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)])) := by
  have hkeep : Hoare
      (fun s => (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (.call (some (none, none)) (ofString "recover_sender_with_chain_id") R16Shards.PtxP1.recoverArgs)
      (fun r s => r = none →
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)])) := by
    apply Hoare.call0_resume
    intro F s vs body callee ret v post hc hp ha hl hb
    exact hp
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨(R16Shards.PtxP1.hoare_recover_sender h).run s hc hp.1 hnt hr,
    hkeep.run s hc hp.2 hnt hr⟩

theorem phase1_shape_four_words {v : ValueHOL 64}
    (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ a b c d : BitVec 64, v = .rStruct
      [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
  rw [shapeEqHOL_eq_true] at h
  rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
  · simp [shapeOfHOLExact] at h
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at h
    rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | vs⟩⟩⟩⟩ <;>
      simp at h
    obtain ⟨h0, h1, h2, h3⟩ := h
    obtain ⟨a, rfl⟩ := R16Shards.PtxP1.shape_one_word h0
    obtain ⟨b, rfl⟩ := R16Shards.PtxP1.shape_one_word h1
    obtain ⟨c, rfl⟩ := R16Shards.PtxP1.shape_one_word h2
    obtain ⟨d, rfl⟩ := R16Shards.PtxP1.shape_one_word h3
    exact ⟨a, b, c, d, rfl⟩
  · simp [shapeOfHOLExact] at h

/-- Use the declared return shape at the price-producing call to retain the
four words needed by the later store. -/
theorem phase1_resume_price_shape
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hres : DecCallResumeOn P Q (ofString "price") (ofString "check_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")]) :
    R16Shards.PtxP1.DecCallResumeShapeOn P
      (fun s => Q s ∧ ∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
        some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
      (ofString "price") (.comb [.one, .one, .one, .one]) (ofString "check_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hq := hres s vs body callee ret v post hc hp ha hl hb
  obtain ⟨a, b, c, d, rfl⟩ := phase1_shape_four_words hsh
  refine ⟨hq, a, b, c, d, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

theorem phase1_resume_check_price (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn (R16Shards.PtxP1.StageP 2)
      (fun s => R16Shards.PtxP1.StageP 2 s ∧
        ∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
          some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
      (ofString "price") (.comb [.one, .one, .one, .one]) (ofString "check_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")] := by
  apply phase1_resume_price_shape
  exact R16Shards.PtxP1.resume_scratch_stage h.wk_check_transaction
    (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64),
      ("sk_buf", 64, 52), ("u256_ws", 640, 640)])
    (by unfold R16Shards.PtxP1.ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _

/-- Local information accumulated before `mgas` and `reservoir` are declared. -/
def PtxPhase1ShapePrefix {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ name ∈ (["tx", "index", "sender"] : List String),
    ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
  (∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)])) ∧
  (∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
    some (.rStruct [.val (.word a), .val (.word b)])) ∧
  (∃ a b c : BitVec 64, s.locals.lookup (ofString "intrinsic") =
    some (.rStruct [.val (.word a), .val (.word b), .val (.word c)]))

theorem phase1_shapePrefix_resume {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxPhase1ShapePrefix s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["tx", "index", "sender", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    PtxPhase1ShapePrefix (setVarHOLFinite name v { post with locals := s.locals }) := by
  have hk : ∀ n ∈ (["tx", "index", "sender", "price", "enc", "intrinsic"] : List String),
      (setVarHOLFinite name v { post with locals := s.locals }).locals.lookup (ofString n) =
        s.locals.lookup (ofString n) := by
    intro n hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hk n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)]
    exact hp.1 n hn
  · simpa only [hk "price" (by simp)] using hp.2.1
  · simpa only [hk "enc" (by simp)] using hp.2.2.1
  · simpa only [hk "intrinsic" (by simp)] using hp.2.2.2

theorem phase1_prefix_localsOnly :
    LocalsOnly ["tx", "index", "sender", "price", "enc", "intrinsic"] PtxPhase1ShapePrefix := by
  intro F s locals k hl hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    change ∃ w : BitVec 64, locals.lookup (ofString n) = some (.val (.word w))
    rw [hl n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)]
    exact hp.1 n hn
  · simpa only [hl "price" (by simp)] using hp.2.1
  · simpa only [hl "enc" (by simp)] using hp.2.2.1
  · simpa only [hl "intrinsic" (by simp)] using hp.2.2.2

theorem phase1_blobBranch_prefix :
    Hoare PtxPhase1ShapePrefix R16Shards.PtxP1.blobBranch
      (fun r s => r = none → PtxPhase1ShapePrefix s) := by
  apply Hoare.decCall_fall (names := ["tx", "index", "sender", "price", "enc", "intrinsic"])
    (by decide) phase1_prefix_localsOnly
  · intro F s vs body callee ret v post hc hp ha hl hb
    exact phase1_shapePrefix_resume s post hp _ v (by decide)
  · apply Hoare.decCall_fall (names := ["tx", "index", "sender", "price", "enc", "intrinsic"])
      (by decide) phase1_prefix_localsOnly
    · intro F s vs body callee ret v post hc hp ha hl hb
      exact phase1_shapePrefix_resume s post hp _ v (by decide)
    · apply Hoare.assign
      · intro F s v hp _
        exact fun _ => LocalsOnly.setVar phase1_prefix_localsOnly (by decide) v s hp
      · exact fun _ _ hr => by cases hr

theorem phase1_blobBranch_stage_prefix (h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      R16Shards.PtxP1.blobBranch
      (fun r s => r = none → R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨(R16Shards.PtxP1.blobBranch_hoare h).run s hc hp.1 hnt hr,
    phase1_blobBranch_prefix.run s hc hp.2 hnt hr⟩

theorem phase1_stage_prefix_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (stage : Nat) (name : MlS) (v : ValueHOL 64)
    (hs : ∀ n ∈ R16Shards.PtxP1.stageNames stage, ofString n ≠ name)
    (hp : ∀ n ∈ (["tx", "index", "sender", "price", "enc", "intrinsic"] : List String), ofString n ≠ name)
    (h : R16Shards.PtxP1.StageP stage s ∧ PtxPhase1ShapePrefix s) :
    R16Shards.PtxP1.StageP stage (setVarHOLFinite name v s) ∧
      PtxPhase1ShapePrefix (setVarHOLFinite name v s) := by
  exact ⟨LocalsOnly.setVar (R16Shards.PtxP1.localsOnly_stage stage) hs v s h.1,
    LocalsOnly.setVar phase1_prefix_localsOnly hp v s h.2⟩

theorem phase1_resume_frame_prefix
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fn : MlS} {args : List (ExpHOL 64)}
    (hr : DecCallResumeOn P Q name fn args)
    (hne : ∀ n ∈ (["tx", "index", "sender", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    DecCallResumeOn (fun s => P s ∧ PtxPhase1ShapePrefix s)
      (fun s => Q s ∧ PtxPhase1ShapePrefix s) name fn args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  exact ⟨hr s vs body callee ret v post hc hp.1 ha hl hb,
    phase1_shapePrefix_resume s post hp.2 name v hne⟩

theorem phase1_resume_blob_gas_prefix (h : PtxCallees) :
    DecCallResumeOn (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (ofString "tx_blob_gas_used") (ofString "calculate_total_blob_gas")
      [.var .local (ofString "tx")] := by
  apply phase1_resume_frame_prefix
  · exact R16Shards.PtxP1.resume_ro_stage h.ro_calculate_total_blob_gas (by decide) _
  · decide

theorem phase1_resume_account_prefix (h : PtxCallees) :
    DecCallResumeOn (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (ofString "acct") (ofString "get_account") [.var .local (ofString "sender")] := by
  apply phase1_resume_frame_prefix
  · exact R16Shards.PtxP1.resume_scratch_stage h.wk_get_account
      (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)])
      (by unfold R16Shards.PtxP1.ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
  · decide

theorem phase1_resume_fee_prefix (h : PtxCallees) :
    DecCallResumeOn (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (ofString "egf") (ofString "fee_mul")
      [.var .local (ofString "gas"), .var .local (ofString "price")] := by
  apply phase1_resume_frame_prefix
  · exact R16Shards.PtxP1.resume_ro_stage h.ro_fee_mul (by decide) _
  · decide

/-- The validation stage already retains the complete intrinsic triple. -/
theorem phase1_shapePrefix_of_stage2 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hstage : R16Shards.PtxP1.StageP 2 s)
    (hscalar : ∀ n ∈ (["tx", "index", "sender"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
    (hprice : ∃ a b c d : BitVec 64, s.locals.lookup (ofString "price") =
      some (.rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)]))
    (henc : ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
      some (.rStruct [.val (.word a), .val (.word b)])) :
    PtxPhase1ShapePrefix s := by
  obtain ⟨a, b, c, hi, _⟩ := hstage.2.2.1 (by omega)
  exact ⟨hscalar, hprice, henc, a, b, c, hi⟩

/-- Preserve the pre-price witnesses across validation, which updates only
`intrinsic` in the restored caller locals. -/
theorem phase1_resume_validate_shapes (h : PtxCallees) :
    DecCallResumeOn
      (fun s => R16Shards.PtxP1.StageP 1 s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (fun s => R16Shards.PtxP1.StageP 2 s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (ofString "intrinsic") (ofString "validate_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  refine ⟨R16Shards.PtxP1.resume_validate h s vs body callee ret v post hc hp.1 ha hl hb, ?_, ?_⟩
  · intro n hn
    have hne : ofString "intrinsic" ≠ ofString n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hp.2.1 n hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "intrinsic" ≠ ofString "enc" from by decide] using hp.2.2

theorem phase1_resume_check_prefix (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => R16Shards.PtxP1.StageP 2 s ∧
        (∀ n ∈ (["tx", "index", "sender"] : List String),
          ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))) ∧
        ∃ a b : BitVec 64, s.locals.lookup (ofString "enc") =
          some (.rStruct [.val (.word a), .val (.word b)]))
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (ofString "price") (.comb [.one, .one, .one, .one]) (ofString "check_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "sender")] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hprice := phase1_resume_check_price h s vs body callee ret v post hc hp.1 ha hl hb hsh
  refine ⟨hprice.1, phase1_shapePrefix_of_stage2 hprice.1 ?_ hprice.2 ?_⟩
  · intro n hn
    have hne : ofString "price" ≠ ofString n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl <;> decide
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne] using hp.2.1 n hn
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "price" ≠ ofString "enc" from by decide] using hp.2.2

theorem phase1_declare_regular_budget_shapes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64) (hp : R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
    (he : evalAt s R16Shards.PtxP1.regularBudgetExp = some v) :
    R16Shards.PtxP1.StageP 3 (setVarHOLFinite (ofString "regular_budget") v s) ∧
      PtxPhase1ShapePrefix (setVarHOLFinite (ofString "regular_budget") v s) := by
  exact ⟨R16Shards.PtxP1.declare_regular_budget s v hp.1 he,
    phase1_shapePrefix_resume s s hp.2 (ofString "regular_budget") v (by decide)⟩

theorem phase1_resume_min_shapes (h : PtxCallees) :
    DecCallResumeOn (fun s => R16Shards.PtxP1.StageP 3 s ∧ PtxPhase1ShapePrefix s)
      (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase1ShapePrefix s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
      (ofString "mgas") (ofString "min")
      [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hm := phase1_resume_min_word h s vs body callee ret v post hc hp.1 ha hl hb
  exact ⟨hm.1, phase1_shapePrefix_resume s post hp.2 (ofString "mgas") v (by decide), hm.2⟩

/-- Assemble all Phase 2 shapes when the arithmetic reservoir declaration
succeeds. This step uses expression semantics, not the default-zero `locN`. -/
theorem phase1_reservoir_shapes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hprefix : PtxPhase1ShapePrefix s)
    (hgas : ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w)))
    (hfees : ∀ n ∈ (["gas", "tx_blob_gas_used"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)))
    (v : ValueHOL 64)
    (he : evalAt s (.op .sub [.var .local (ofString "execution_gas"),
      .var .local (ofString "mgas")]) = some v) :
    PtxPhase2LocalShapes (setVarHOLFinite (ofString "reservoir") v s) := by
  obtain ⟨w, rfl⟩ := R16Shards.PtxP1.eval_is_word_op he
  have hkeep : ∀ name : String, ofString name ≠ ofString "reservoir" →
      (setVarHOLFinite (ofString "reservoir") (.val (.word w)) s).locals.lookup (ofString name) =
        s.locals.lookup (ofString name) := by
    intro name hn
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm hn]
  constructor
  · intro name hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [hkeep "tx" (by decide)] using hprefix.1 "tx" (by simp)
    · simpa only [hkeep "index" (by decide)] using hprefix.1 "index" (by simp)
    · simpa only [hkeep "sender" (by decide)] using hprefix.1 "sender" (by simp)
    · simpa only [hkeep "mgas" (by decide)] using hgas
    · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
    · simpa only [hkeep "gas" (by decide)] using hfees "gas" (by simp)
    · simpa only [hkeep "tx_blob_gas_used" (by decide)] using hfees "tx_blob_gas_used" (by simp)
  · simpa only [hkeep "price" (by decide)] using hprefix.2.1
  · simpa only [hkeep "enc" (by decide)] using hprefix.2.2.1
  · simpa only [hkeep "intrinsic" (by decide)] using hprefix.2.2.2

/-- Combine independent world and local-shape postconditions for a statement. -/
theorem phase1_hoare_frame_shapes
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {p : ProgHOL 64}
    (hw : Hoare P p (fun r s => r = none → Q s))
    (hs : Hoare PtxPhase2LocalShapes p (fun r s => r = none → PtxPhase2LocalShapes s)) :
    Hoare (fun s => P s ∧ PtxPhase2LocalShapes s) p
      (fun r s => r = none → Q s ∧ PtxPhase2LocalShapes s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨hw.run s hc hp.1 hnt hr, hs.run s hc hp.2 hnt hr⟩

theorem phase1_call0_shapes (fn : MlS) (args : List (ExpHOL 64)) :
    Hoare PtxPhase2LocalShapes (.call (some (none, none)) fn args)
      (fun r s => r = none → PtxPhase2LocalShapes s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hb
  exact ptxPhase2LocalShapes_restore s post hp

theorem phase1_call_balance_shapes (fn : MlS) (args : List (ExpHOL 64)) :
    Hoare PtxPhase2LocalShapes (.call (some (some (.local, ofString "bal"), none)) fn args)
      (fun r s => r = none → PtxPhase2LocalShapes s) := by
  apply Hoare.callLocal_resume
  intro F s vs body callee ret v post hc hp ha hl hb
  exact ptxPhase2LocalShapes_set_other _ (ptxPhase2LocalShapes_restore s post hp)
    (ofString "bal") v (by decide)

/-- The final Phase 1 stage plus retained shapes is exactly the strengthened
entry needed at the Phase 2 boundary. -/
theorem phase1_stage4_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hw : R16Shards.PtxP1.StageP 4 s) (hs : PtxPhase2LocalShapes s) :
    PtxValidatedStrong s :=
  ⟨R16Shards.PtxP1.stage4_validated hw, hs⟩

/-- Bounded composition of the regular-budget, min, and reservoir segment.
The continuation receives all local shapes and the final numeric stage. -/
def PtxFeeWords {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ n ∈ (["gas", "tx_blob_gas_used"] : List String),
    ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w))

theorem phase1_feeWords_resume {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxFeeWords s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["gas", "tx_blob_gas_used"] : List String), ofString n ≠ name) :
    PtxFeeWords (setVarHOLFinite name v { post with locals := s.locals }) := by
  intro n hn
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)] using hp n hn

theorem phase1_gas_segment_strong (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s) ∧ PtxFeeWords s)
      (.dec (ofString "regular_budget") .one R16Shards.PtxP1.regularBudgetExp
        (.decCall (ofString "mgas") .one (ofString "min")
          [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")]
          (.dec (ofString "reservoir") .one
            (.op .sub [.var .local (ofString "execution_gas"), .var .local (ofString "mgas")]) tail)))
      (K.min + b + 1) := by
  apply dec_bound_trans (Q := fun s => (R16Shards.PtxP1.StageP 3 s ∧ PtxPhase1ShapePrefix s) ∧ PtxFeeWords s)
    (fun s v hp he => ⟨phase1_declare_regular_budget_shapes s v hp.1 he,
      phase1_feeWords_resume s s hp.2 _ v (by decide)⟩)
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => (R16Shards.PtxP1.StageP 4 s ∧ PtxPhase1ShapePrefix s ∧
      ∃ w : BitVec 64, s.locals.lookup (ofString "mgas") = some (.val (.word w))) ∧ PtxFeeWords s) h.fb_min
  · intro F s vs body callee ret hc hp ha hl
    exact R16Shards.PtxP1.stage_entry 3 _ _ s vs body callee ret hc hp.1.1 ha hl
  · intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨phase1_resume_min_shapes h s vs body callee ret v post hc hp.1 ha hl hb,
      phase1_feeWords_resume s post hp.2 _ v (by decide)⟩
  · apply dec_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
    · intro F s v hp he
      exact ⟨LocalsOnly.setVar (R16Shards.PtxP1.localsOnly_stage 4) (by decide) v s hp.1.1,
        phase1_reservoir_shapes s hp.1.2.1 hp.1.2.2 hp.2 v he⟩
    · exact htail

theorem phase1_nonce_shapes (h : PtxCallees) :
    Hoare (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "sender")])
      (fun r s => r = none → R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · exact R16Shards.PtxP1.hoare_call_scratch_stage h.wk_increment_nonce
      (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
      (by unfold R16Shards.PtxP1.ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) _
  · exact phase1_call0_shapes _ _

theorem phase1_sub_balance_shapes (h : PtxCallees) (args : List (ExpHOL 64)) :
    Hoare (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub") args)
      (fun r s => r = none → R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · exact Hoare.callLocal_resume (R16Shards.PtxP1.resume_ro_stage h.ro_u256_sub (by decide) _)
  · exact phase1_call_balance_shapes _ _

theorem phase1_set_balance_shapes (h : PtxCallees) (args : List (ExpHOL 64)) :
    Hoare (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.call (some (none, none)) (ofString "set_account_balance") args)
      (fun r s => r = none → R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) := by
  apply phase1_hoare_frame_shapes
  · exact R16Shards.PtxP1.hoare_call_scratch_stage h.wk_set_account_balance
      (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52)])
      (by unfold R16Shards.PtxP1.ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
      (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) _
  · exact phase1_call0_shapes _ _

theorem phase1_set_balance_tail_strong (h : PtxCallees) (args : List (ExpHOL 64))
    {tail : ProgHOL 64} {b : Nat} (htail : TerminatingProgBoundedOn PtxValidatedStrong tail b) :
    TerminatingProgBoundedOn (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (none, none)) (ofString "set_account_balance") args) (.seq .skip tail))
      ((K.set_account_balance + 1) + (0 + b)) := by
  apply seq_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_set_account_balance none args s hc hp.1.1.1.1.1.1
  · exact phase1_set_balance_shapes h args
  · apply seq_bound_trans (Q := PtxValidatedStrong)
    · intro F s hc hp
      exact R16Shards.PtxP1.bound_of_clock (P := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
        (fun s => R16Shards.PtxP1.clock_skip s) s hc hp
    · exact Hoare.skip (fun _ hp _ => phase1_stage4_strong hp.1 hp.2)
    · exact htail

theorem phase1_sub_balance_tail_strong (h : PtxCallees) (args : List (ExpHOL 64))
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub") args) tail)
      ((K.u256_sub + 1) + b) := by
  apply seq_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_u256_sub
      (some (.local, ofString "bal")) args s hc hp.1.1.1.1.1.1
  · exact phase1_sub_balance_shapes h args
  · exact htail

theorem phase1_nonce_balance_decl_strong (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (.seq (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "sender")])
        (.dec (ofString "bal") (.comb [.one, .one, .one, .one])
          (.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "acct"), .const 8])) tail))
      ((K.increment_nonce + 1) + b) := by
  apply seq_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
  · intro F s hc hp
    exact TerminatingProgBoundedOn.call_guestInv h.fb_increment_nonce none _ s hc hp.1.1.1.1.1.1
  · exact phase1_nonce_shapes h
  · apply dec_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
    · intro F s v hp he
      exact ⟨LocalsOnly.setVar (R16Shards.PtxP1.localsOnly_stage 4) (by decide) v s hp.1,
        ptxPhase2LocalShapes_set_other s hp.2 _ v (by decide)⟩
    · exact htail

/-- The complete Phase 1 suffix after the reservoir declaration. -/
def phase1BalanceSuffix (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "increment_nonce") [.var .local (ofString "sender")])
    (.dec (ofString "bal") (.comb [.one, .one, .one, .one])
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "acct"), .const 8]))
      (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub")
        [.var .local (ofString "bal"), .var .local (ofString "effective_gas_fee")])
        (.seq (.call (some (some (.local, ofString "bal"), none)) (ofString "u256_sub")
          [.var .local (ofString "bal"), .var .local (ofString "blob_gas_fee")])
          (.seq (.call (some (none, none)) (ofString "set_account_balance")
            [.var .local (ofString "sender"), .var .local (ofString "bal")]) (.seq .skip tail)))))

theorem phase1_balance_suffix_strong (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedStrong tail b) :
    TerminatingProgBoundedOn (fun s => R16Shards.PtxP1.StageP 4 s ∧ PtxPhase2LocalShapes s)
      (phase1BalanceSuffix tail)
      ((K.increment_nonce + 1) + ((K.u256_sub + 1) + ((K.u256_sub + 1) +
        ((K.set_account_balance + 1) + (0 + b))))) := by
  unfold phase1BalanceSuffix
  apply phase1_nonce_balance_decl_strong h
  apply phase1_sub_balance_tail_strong h
  apply phase1_sub_balance_tail_strong h
  exact phase1_set_balance_tail_strong h _ htail

def PtxLocalShapeMap (xs : List (String × ShapeHOL))
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ x ∈ xs, ∃ v, s.locals.lookup (ofString x.1) = some v ∧ shapeOfHOLExact v = x.2

theorem ptxLocalShapeMap_resume {F : Type} (s post : PanSemStateFiniteExact 64 F)
    {xs : List (String × ShapeHOL)} (hp : PtxLocalShapeMap xs s)
    (name : String) (v : ValueHOL 64)
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name) :
    PtxLocalShapeMap xs (setVarHOLFinite (ofString name) v { post with locals := s.locals }) := by
  intro x hx
  simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm (hne x hx)] using hp x hx

theorem ptxLocalShapeMap_add {F : Type} (s post : PanSemStateFiniteExact 64 F)
    {xs : List (String × ShapeHOL)} (hp : PtxLocalShapeMap xs s)
    (name : String) (sh : ShapeHOL) (v : ValueHOL 64)
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (hsh : shapeOfHOLExact v = sh) :
    PtxLocalShapeMap ((name, sh) :: xs)
      (setVarHOLFinite (ofString name) v { post with locals := s.locals }) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨v, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hsh⟩
  · exact ptxLocalShapeMap_resume s post hp name v hne x hx

theorem phase1_call_shape_map
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {xs : List (String × ShapeHOL)} {fn : MlS} {B b : Nat}
    (hf : TerminatingFunBoundedOn Pc fn B) (name : String) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) {tail : ProgHOL 64}
    (he : CallEntryOn P Pc fn args)
    (hr : R16Shards.PtxP1.DecCallResumeShapeOn P Q (ofString name) sh fn args)
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (ht : TerminatingProgBoundedOn (fun s => Q s ∧ PtxLocalShapeMap ((name, sh) :: xs) s) tail b) :
    TerminatingProgBoundedOn (fun s => P s ∧ PtxLocalShapeMap xs s)
      (.decCall (ofString name) sh fn args tail) (B + b + 1) := by
  apply R16Shards.PtxP1.decCall_shape_bound (Q := fun s => Q s ∧ PtxLocalShapeMap ((name, sh) :: xs) s) hf _ _ _
  · intro F s vs body callee ret hc hp ha hl
    exact he s vs body callee ret hc hp.1 ha hl
  · intro F s vs body callee ret v post hc hp ha hl hb hsh
    exact ⟨hr s vs body callee ret v post hc hp.1 ha hl hb hsh,
      ptxLocalShapeMap_add s post hp.2 name sh v hne (by simpa only [shapeEqHOL_eq_true] using hsh)⟩
  · exact ht

theorem phase1_dec_shape_map
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {xs : List (String × ShapeHOL)} (name : String) (sh : ShapeHOL)
    (e : ExpHOL 64) {tail : ProgHOL 64} {b : Nat}
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, P s →
      evalAt s e = some v → Q (setVarHOLFinite (ofString name) v s))
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (ht : TerminatingProgBoundedOn (fun s => Q s ∧ PtxLocalShapeMap ((name, sh) :: xs) s) tail b) :
    TerminatingProgBoundedOn (fun s => P s ∧ PtxLocalShapeMap xs s)
      (.dec (ofString name) sh e tail) b := by
  intro F s hc hp hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split <;> intro hnt
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · revert hnt
    split <;> intro hnt
    · rename_i v hv hs
      simpa only [setVarHOLFinite] using ht (setVarHOLFinite (ofString name) v s) hc ⟨he s v hp.1 hv,
        ptxLocalShapeMap_add s s hp.2 name sh v hne (by symm; simpa only [shapeEqHOL_eq_true] using hs)⟩ hnt
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem phase1_map_localsOnly (xs : List (String × ShapeHOL)) :
    LocalsOnly (xs.map Prod.fst) (PtxLocalShapeMap xs) := by
  intro F s ls k hl hp x hx
  change ∃ v, ls.lookup (ofString x.1) = some v ∧ shapeOfHOLExact v = x.2
  rw [hl x.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)]
  exact hp x hx

theorem phase1_frame_map {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {xs : List (String × ShapeHOL)}
    (hw : Hoare P p (fun r s => r = none → Q s))
    (hm : Hoare (PtxLocalShapeMap xs) p (fun r s => r = none → PtxLocalShapeMap xs s)) :
    Hoare (fun s => P s ∧ PtxLocalShapeMap xs s) p
      (fun r s => r = none → Q s ∧ PtxLocalShapeMap xs s) := by
  exact ⟨fun s hc hp hn hr => ⟨hw.run s hc hp.1 hn hr, hm.run s hc hp.2 hn hr⟩⟩

theorem phase1_map_store (xs : List (String × ShapeHOL)) (a v : ExpHOL 64) :
    Hoare (PtxLocalShapeMap xs) (.store a v) (fun r s => r = none → PtxLocalShapeMap xs s) := by
  exact Hoare.store_fall (fun _ _ _ _ hp _ _ _ => hp)

theorem phase1_map_call0 (xs : List (String × ShapeHOL)) (fn : MlS) (args : List (ExpHOL 64)) :
    Hoare (PtxLocalShapeMap xs) (.call (some (none, none)) fn args)
      (fun r s => r = none → PtxLocalShapeMap xs s) := by
  exact Hoare.call0_resume (fun _ _ _ _ _ _ _ _ hp _ _ _ => hp)

theorem phase1_map_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    {xs : List (String × ShapeHOL)} (hp : PtxLocalShapeMap xs s)
    (hs : ∀ n ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String),
      (n, ShapeHOL.one) ∈ xs)
    (hprice : ("price", ShapeHOL.comb [.one, .one, .one, .one]) ∈ xs)
    (henc : ("enc", ShapeHOL.comb [.one, .one]) ∈ xs)
    (hi : ("intrinsic", ShapeHOL.comb [.one, .one, .one]) ∈ xs) :
    PtxPhase2LocalShapes s := by
  constructor
  · intro n hn
    obtain ⟨v, hv, hsh⟩ := hp _ (hs n hn)
    obtain ⟨w, rfl⟩ := R16Shards.PtxP1.shape_one_word hsh
    exact ⟨w, hv⟩
  · obtain ⟨v, hv, hsh⟩ := hp _ hprice
    obtain ⟨a, b, c, d, rfl⟩ := phase1_shape_four_words (v := v) (by simpa only [shapeEqHOL_eq_true] using hsh)
    exact ⟨a, b, c, d, hv⟩
  · obtain ⟨v, hv, hsh⟩ := hp _ henc
    obtain ⟨a, b, rfl⟩ := R16Shards.PtxP1.shape_pair_words (v := v) (by simpa only [shapeEqHOL_eq_true] using hsh)
    exact ⟨a, b, hv⟩
  · obtain ⟨v, hv, hsh⟩ := hp _ hi
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · simp [shapeOfHOLExact] at hsh
    · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
      rcases fs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | vs⟩⟩⟩ <;> simp at hsh
      obtain ⟨h0, h1, h2⟩ := hsh
      obtain ⟨a, rfl⟩ := R16Shards.PtxP1.shape_one_word h0
      obtain ⟨b, rfl⟩ := R16Shards.PtxP1.shape_one_word h1
      obtain ⟨c, rfl⟩ := R16Shards.PtxP1.shape_one_word h2
      exact ⟨a, b, c, hv⟩
    · simp [shapeOfHOLExact] at hsh

theorem phase1_call_keep_map
    {P Pc Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {xs : List (String × ShapeHOL)} {fn : MlS} {B b : Nat}
    (hf : TerminatingFunBoundedOn Pc fn B) (name : String) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) {tail : ProgHOL 64}
    (he : CallEntryOn P Pc fn args) (hr : DecCallResumeOn P Q (ofString name) fn args)
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (ht : TerminatingProgBoundedOn (fun s => Q s ∧ PtxLocalShapeMap xs s) tail b) :
    TerminatingProgBoundedOn (fun s => P s ∧ PtxLocalShapeMap xs s)
      (.decCall (ofString name) sh fn args tail) (B + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := fun s => Q s ∧ PtxLocalShapeMap xs s) hf
  · intro F s vs body callee ret hc hp ha hl
    exact he s vs body callee ret hc hp.1 ha hl
  · intro F s vs body callee ret v post hc hp ha hl hb
    exact ⟨hr s vs body callee ret v post hc hp.1 ha hl hb,
      ptxLocalShapeMap_resume s post hp.2 name v hne⟩
  · exact ht

theorem phase1_dec_keep_map
    {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {xs : List (String × ShapeHOL)} (name : String) (sh : ShapeHOL)
    (e : ExpHOL 64) {tail : ProgHOL 64} {b : Nat}
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v, P s →
      evalAt s e = some v → Q (setVarHOLFinite (ofString name) v s))
    (hne : ∀ x ∈ xs, ofString x.1 ≠ ofString name)
    (ht : TerminatingProgBoundedOn (fun s => Q s ∧ PtxLocalShapeMap xs s) tail b) :
    TerminatingProgBoundedOn (fun s => P s ∧ PtxLocalShapeMap xs s)
      (.dec (ofString name) sh e tail) b := by
  apply dec_bound_trans (Q := fun s => Q s ∧ PtxLocalShapeMap xs s)
  · intro F s v hp hv
    exact ⟨he s v hp.1 hv, ptxLocalShapeMap_resume s s hp.2 name v hne⟩
  · exact ht

theorem ptxPhase1_cut_strong (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedStrong tail b) :
    TerminatingProgBoundedOn TxReadyStrong (ptxPhase1 tail) (ptxCost1 + b) := by
  open R16Shards.PtxP1 in
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
    refine seq_bound_trans (Q := StageP 0)
      (bound_mono (TerminatingProgBoundedOn.call_guestInv h.fb_state_fresh_tx none [])
        (fun _ hp => hp.1.1.1.1.1)) ?_ ?_
    · exact hoare_call_scratch_stage h.wk_state_fresh_tx (gs := []) (by simp [ScratchSpec])
        (fun _ => rfl) (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
        (by simp) (by decide) []
    refine seq_bound_trans
      (Q := fun s => StageP 0 s ∧ PtxLocalShapeMap [("tx", .one), ("index", .one)] s)
      (bound_of_clock (fun s => clock_assign s _ _ _)) ?_ ?_
    · refine ⟨fun s hc hp hn hr => ?_⟩
      have hh := phase1_assign_bal_index_shapes.run s hc hp hn hr
      refine ⟨hh.1, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · obtain ⟨w, hw⟩ := hh.2 "tx" (by simp)
        exact ⟨_, hw, by simp [shapeOfHOLExact]⟩
      · obtain ⟨w, hw⟩ := hh.2 "index" (by simp)
        exact ⟨_, hw, by simp [shapeOfHOLExact]⟩
    refine phase1_call_shape_map (Q := EncReady) h.fb_encode_transaction _ _ _ (stage_entry 0 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb hs
      exact resume_encode h s vs body callee ret v post hc hp.1 ha hl hb hs
    refine seq_bound_trans ?_ (phase1_frame_map (store_encSlot false) (phase1_map_store _ _ _)) ?_
    · intro F s hc hp
      intro hn
      rw [clock_store]
      exact ⟨by omega, le_rfl⟩
    refine seq_bound_trans ?_ (phase1_frame_map (store_encSlot true) (phase1_map_store _ _ _)) ?_
    · intro F s hc hp
      intro hn
      rw [clock_store]
      exact ⟨by omega, le_rfl⟩
    apply seq_bound_trans (Q := fun s => StageP 0 s ∧ PtxLocalShapeMap [("enc", .comb [.one, .one]), ("tx", .one), ("index", .one)] s)
    · intro F s hc hp
      intro hn
      rw [clock_skip]
      exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => ⟨stage0 hp.1.1, hp.2⟩)
    refine phase1_call_keep_map h.fb_tx_chain_id _ _ _ (stage_entry 0 _ _)
      (resume_ro_stage h.ro_tx_chain_id (by decide) _) (by decide) ?_
    refine seq_bound_trans ?_ (phase1_frame_map chainGuard_hoare (phase1_chainGuard_keeps _)) ?_
    · intro F s hc hp
      exact chainGuard_bound s hc hp.1
    refine phase1_call_shape_map (Q := SenderAllocated) h.fb_alloc _ _ _ (stage_entry 0 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact resume_alloc_sender h s vs body callee ret v post hc hp ha hl hb
    refine seq_bound_trans ?_ (phase1_frame_map (hoare_recover_sender h) (phase1_map_call0 _ _ _)) ?_
    · intro F s hc hp
      exact TerminatingProgBoundedOn.call_guestInv h.fb_recover_sender_with_chain_id none _ s hc hp.1.1.1.1.1.1
    apply seq_bound_trans (Q := fun s => StageP 1 s ∧ PtxLocalShapeMap _ s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_call_shape_map (Q := StageP 2) h.fb_validate_transaction _ _ _ (stage_entry 1 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact resume_validate h s vs body callee ret v post hc hp ha hl hb
    apply seq_bound_trans (Q := fun s => StageP 2 s ∧ PtxLocalShapeMap _ s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_dec_shape_map (Q := StageP 2) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp) (by decide) ?_
    refine phase1_call_shape_map (Q := StageP 2) h.fb_check_transaction _ _ _ (stage_entry 2 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact resume_scratch_stage h.wk_check_transaction
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64), ("sk_buf", 64, 52), ("u256_ws", 640, 640)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
        s vs body callee ret v post hc hp ha hl hb
    apply seq_bound_trans (Q := fun s => StageP 2 s ∧ PtxLocalShapeMap _ s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_call_shape_map (Q := StageP 2) h.fb_calculate_total_blob_gas _ _ _ (stage_entry 2 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact resume_ro_stage h.ro_calculate_total_blob_gas (by decide) _ s vs body callee ret v post hc hp ha hl hb
    refine phase1_call_keep_map (Q := StageP 2) h.fb_get_account _ _ _ (stage_entry 2 _ _) ?_ (by decide) ?_
    · exact resume_scratch_stage h.wk_get_account
        (gs := [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)])
        (by unfold ScratchSpec; decide) (fun _ => rfl) (by decide) (by decide)
        (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by simp) (by decide) (by decide) _
    apply seq_bound_trans (Q := fun s => StageP 2 s ∧ PtxLocalShapeMap _ s)
    · intro F s hc hp hn
      rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · exact Hoare.skip (fun _ hp _ => hp)
    refine phase1_dec_keep_map (Q := StageP 2) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp) (by decide) ?_
    apply seq_bound_trans (Q := fun s => StageP 2 s ∧ PtxLocalShapeMap _ s)
    · apply TerminatingProgBoundedOn.ite_on
      · intro F s hc hp
        exact blobBranch_bound h s hc hp.1
      · intro F s hc hp hn
        rw [clock_skip]; exact ⟨by omega, le_rfl⟩
    · apply Hoare.ite
      · apply Hoare.mono (phase1_frame_map (blobBranch_hoare h) ?_) (fun _ hp => hp.1)
        apply Hoare.decCall_fall (by decide) (phase1_map_localsOnly _)
        · intro F s vs body callee ret v post hc hp ha hl hb
          exact ptxLocalShapeMap_resume s post hp _ v (by decide)
        · apply Hoare.decCall_fall (by decide) (phase1_map_localsOnly _)
          · intro F s vs body callee ret v post hc hp ha hl hb
            exact ptxLocalShapeMap_resume s post hp _ v (by decide)
          · apply Hoare.assign
            · intro F s v hp _ _
              exact LocalsOnly.setVar (phase1_map_localsOnly _) (by decide) v s hp
            · exact fun _ _ hr => by cases hr
      · exact Hoare.skip (fun _ hp _ => hp.1)
      · exact fun _ _ hr => by cases hr
    refine phase1_dec_shape_map (Q := StageP 2) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp) (by decide) ?_
    refine phase1_call_keep_map h.fb_fee_mul _ _ _ (stage_entry 2 _ _)
      (resume_ro_stage h.ro_fee_mul (by decide) _) (by decide) ?_
    refine phase1_dec_keep_map (Q := StageP 2) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp) (by decide) ?_
    refine phase1_dec_keep_map (Q := StageP 2) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 2) (by decide) v s hp) (by decide) ?_
    refine phase1_dec_keep_map (Q := StageP 3) _ _ _ declare_regular_budget (by decide) ?_
    refine phase1_call_shape_map (Q := StageP 4) h.fb_min _ _ _ (stage_entry 3 _ _) ?_ (by decide) ?_
    · intro F s vs body callee ret v post hc hp ha hl hb _
      exact resume_min h s vs body callee ret v post hc hp ha hl hb
    refine phase1_dec_shape_map (Q := StageP 4) _ _ _
      (fun s v hp _ => LocalsOnly.setVar (localsOnly_stage 4) (by decide) v s hp) (by decide) ?_
    apply bound_mono (phase1_balance_suffix_strong h htail)
    intro F s hp
    refine ⟨hp.1, phase1_map_strong hp.2 ?_ (by simp) (by simp) (by simp)⟩
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have he : R16Shards.PtxP1.phase1Budget b = ptxCost1 + b := by
    simp only [R16Shards.PtxP1.phase1Budget, ptxCost1, Nat.add_zero, Nat.zero_add, Nat.max_zero,
      Nat.add_comm, Nat.add_left_comm]
  rw [he] at hb
  intro F s hc hp
  exact hb s hc (R16Shards.PtxP1.stage0 hp)
def phase1GasSuffix (tail : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "regular_budget") .one R16Shards.PtxP1.regularBudgetExp
    (.decCall (ofString "mgas") .one (ofString "min")
      [.var .local (ofString "regular_budget"), .var .local (ofString "execution_gas")]
      (.dec (ofString "reservoir") .one
        (.op .sub [.var .local (ofString "execution_gas"), .var .local (ofString "mgas")])
        (phase1BalanceSuffix tail)))

theorem phase1_gas_suffix_strong (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn PtxValidatedStrong tail b) :
    TerminatingProgBoundedOn
      (fun s => (R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s) ∧ PtxFeeWords s)
      (phase1GasSuffix tail)
      (K.min + ((K.increment_nonce + 1) + ((K.u256_sub + 1) + ((K.u256_sub + 1) +
        ((K.set_account_balance + 1) + (0 + b))))) + 1) := by
  exact phase1_gas_segment_strong h (phase1_balance_suffix_strong h htail)

def phase1FeeSegment (tail : ProgHOL 64) : ProgHOL 64 :=
  .dec (ofString "gas") .one
    (.load .one (.op .add [.var .local (ofString "tx"), .const 144]))
    (.decCall (ofString "egf") (.comb [.one, .one, .one, .one, .one]) (ofString "fee_mul")
      [.var .local (ofString "gas"), .var .local (ofString "price")]
      (.dec (ofString "effective_gas_fee") (.comb [.one, .one, .one, .one])
        (.rstruct [.rfield 1 (.var .local (ofString "egf")), .rfield 2 (.var .local (ofString "egf")),
          .rfield 3 (.var .local (ofString "egf")), .rfield 4 (.var .local (ofString "egf"))])
        (.dec (ofString "execution_gas") .one
          (.op .sub [.var .local (ofString "gas"), .var .local (ofString "intrinsic_gas")]) tail)))

theorem phase1_fee_segment_strong (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s) tail b) :
    TerminatingProgBoundedOn
      (fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      (phase1FeeSegment tail) (K.fee_mul + b + 1) := by
  unfold phase1FeeSegment
  apply dec_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
  · intro F s v hp he
    exact phase1_stage_prefix_set_other s 2 _ v (by decide) (by decide) hp
  · apply TerminatingProgBoundedOn.decCall_on
      (Q := fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s) h.fb_fee_mul
    · intro F s vs body callee ret hc hp ha hl
      exact R16Shards.PtxP1.stage_entry 2 _ _ s vs body callee ret hc hp.1 ha hl
    · exact phase1_resume_fee_prefix h
    · apply dec_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
      · intro F s v hp he
        exact phase1_stage_prefix_set_other s 2 _ v (by decide) (by decide) hp
      · apply dec_bound_trans (Q := fun s => R16Shards.PtxP1.StageP 2 s ∧ PtxPhase1ShapePrefix s)
        · intro F s v hp he
          exact phase1_stage_prefix_set_other s 2 _ v (by decide) (by decide) hp
        · exact htail

/-- Definitionally the local-shape interface consumed by the R16 Phase 3/4
composition, kept here without a dependency on the downstream shard. -/
def PtxPhase4ShapesFromPhase2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    (∀ name ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used"] : List String),
      ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w))) ∧
    (∃ v, s.locals.lookup (ofString "price") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one, .one]) ∧
    (∃ v, s.locals.lookup (ofString "intrinsic") = some v ∧
      shapeOfHOLExact v = .comb [.one, .one, .one])

theorem ptxPhase2LocalShapes_phase4 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : PtxPhase2LocalShapes s) : PtxPhase4ShapesFromPhase2 s := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    apply h.scalar n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
    tauto
  · obtain ⟨a, b, c, d, hp⟩ := h.price
    exact ⟨_, hp, by simp [shapeOfHOLExact]⟩
  · obtain ⟨a, b, c, hi⟩ := h.intrinsic
    exact ⟨_, hi, by simp [shapeOfHOLExact]⟩

theorem ptxPhase2LocalShapes_localsOnly :
    LocalsOnly ["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used",
      "price", "enc", "intrinsic"] PtxPhase2LocalShapes :=
  ptxPhase2LocalShapes_with_locals

/-- Shape frame for the first Phase 2 call, whose fresh transaction environment
is assigned to `te`. The callee may alter memory, but restores caller locals. -/
theorem phase2_te_new_shapes (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn PtxValidatedStrong
      (fun s => PtxValidatedStrong s ∧
        ∃ w : BitVec 64, s.locals.lookup (ofString "te") = some (.val (.word w)))
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hstage : R16Shards.PtxP1.StageP 0 s := R16Shards.PtxP1.stage0 hp.1.1
  have hworld := R16Shards.PtxP1.resume_scratch_stage h.wk_te_new
    (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) (fun _ => rfl)
    (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by simp) (by decide) (n := 0) (name := ofString "te") (by decide) []
    s vs body callee ret v post hc hstage ha hl hb
  have hspec := R16Shards.PtxP1.funSpec_at_lookup h.wk_te_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hspec
  have hh := (hspec (Or.inl ⟨v, rfl⟩)).2.1
  change globN s "heap_ptr" ≤ globN post "heap_ptr" at hh
  obtain ⟨w, rfl⟩ := R16Shards.PtxP1.shape_one_word
    (by simpa only [shapeEqHOL_eq_true] using hsh)
  have hs := ptxPhase2LocalShapes_set_other _ (ptxPhase2LocalShapes_restore s post hp.2)
    (ofString "te") (.val (.word w)) (by decide)
  have hlu : ∀ n ∈ (["sender", "mgas"] : List String),
      locN (setVarHOLFinite (ofString "te") (.val (.word w)) { post with locals := s.locals }) n = locN s n := by
    intro n hn
    have hne : ofString "te" ≠ ofString n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> decide
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  refine ⟨⟨⟨hworld.1, ?_, ?_, ?_⟩, hs⟩, w, ?_⟩
  · rw [hlu "sender" (by simp)]
    exact ⟨hp.1.2.1.1, hp.1.2.1.2.trans hh⟩
  · rw [hlu "sender" (by simp)]
    exact wordsOK_transfer hp.1.1.1.1.1.1 hworld.1.1.1.1.1 hp.1.2.2.1
  · rw [hlu "mgas" (by simp)]
    exact hp.1.2.2.2
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- First Phase 2 allocation, including its initialized extent and separation
from the live world. These facts are needed by the following six stores. -/
def PtxTeAllocated : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxValidatedStrong s ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "te") = some (.val (.word w))) ∧
    Inside (locN s "te", 200) InitE.sourceBase (globN s "heap_ptr") ∧
    locN s "te" % 8 = 0 ∧ WordsOK s (locN s "te", 200) ∧
    (∀ k, k < 25 → memW s (locN s "te" + 8 * k) = 0) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd)

theorem phase2_resume_te_new (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn PtxValidatedStrong PtxTeAllocated
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hs := phase2_te_new_shapes h s vs body callee ret v post hc hp ha hl hb hsh
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_te_new s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, rfl, hAp, hag, hf, hz⟩ := hr v rfl
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_te_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨_, rfl⟩)
  obtain ⟨S, hWT⟩ := hp.1.1.1.1.2
  obtain ⟨Nd, hW⟩ := (worldTyped_iff_with s S).mp hWT
  have hWe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', _, hW', _, _, hex⟩ := step.2.2.2.2 S Nd hWe (by simp [IvlsDisj])
  obtain ⟨w', heq, hav⟩ := hex _ rfl
  have heq' : w = w' := by simpa using heq
  subst w'
  have hloc : locN (setVarHOLFinite (ofString "te") (.val (.word w)) { post with locals := s.locals }) "te" = w.toNat := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨hs.1, hs.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc]
    exact ⟨Nat.le_trans hp.1.1.1.1.1.2.1 hf.2.1.1, hf.2.1.2⟩
  · rw [hloc]; exact hf.1
  · rw [hloc]
    change WordsOK post (w.toNat, 200)
    exact hf.2.2
  · rw [hloc]; exact hz
  · refine ⟨S', Nd', ?_, ?_⟩
    · exact (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW'
    · rw [hloc]; exact hav

theorem phase2_te_new_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxTeAllocated tail b) :
    TerminatingProgBoundedOn PtxValidatedStrong
      (.decCall (ofString "te") .one (ofString "te_new") [] tail) (K.te_new + b + 1) := by
  apply R16Shards.PtxP1.decCall_shape_bound h.fb_te_new
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · exact phase2_resume_te_new h
  · exact ht

/-- Scalar message-building stores write exactly one word, including when the
stored value is zero. Numeric projections alone cannot establish this fact. -/
theorem phase2_scalar_store_length {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : PtxPhase2LocalShapes s) (name : String)
    (hn : name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String))
    {v : ValueHOL 64} (he : evalAt s (.var .local (ofString name)) = some v) :
    (flattenHOL v).length = 1 := by
  obtain ⟨w, hw⟩ := hs.scalar name hn
  have hv : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using he.symm
  subst v
  simp [flattenHOL]

theorem phase2_price_store_length {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hs : PtxPhase2LocalShapes s) {v : ValueHOL 64}
    (he : evalAt s (.var .local (ofString "price")) = some v) :
    (flattenHOL v).length = 4 := by
  obtain ⟨a, b, c, d, hw⟩ := hs.price
  have hv : v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
    simpa [evalAt, evalHOLExact, hw] using he.symm
  subst v
  simp [flattenHOL]

theorem phase2_store_preserves_shapes (addr value : ExpHOL 64) :
    Hoare PtxPhase2LocalShapes (.store addr value)
      (fun r s => r = none → PtxPhase2LocalShapes s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hm
  exact ⟨hp.scalar, hp.price, hp.enc, hp.intrinsic⟩

/-- The fresh transaction environment is non-null, and each of its 25 word
slots fits entirely in the allocated heap extent. -/
theorem phase2_te_slots {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeAllocated s) :
    locN s "te" ≠ 0 ∧ ∀ k, k < 25 →
      Inside (locN s "te" + 8 * k, 8) InitE.sourceBase (globN s "heap_ptr") := by
  have hi := hp.2.2.1
  have hb : 0 < InitE.sourceBase := by decide
  constructor
  · have := hi.1; omega
  · intro k hk
    obtain ⟨hlo, hhi⟩ := hi
    constructor <;> dsimp at * <;> omega

/-- Fresh allocation also separates the transaction environment from arbitrary
caller heap buffers. World ownership alone does not include every live buffer. -/
theorem phase2_te_new_separates (h : PtxCallees)
    (p len : Nat) :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => PtxValidatedStrong s ∧ Inside (p, len) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => PtxTeAllocated s ∧ Disj (p, len) (locN s "te", 200))
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hte := phase2_resume_te_new h s vs body callee ret v post hc hp.1 ha hl hb hsh
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_te_new s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, rfl, _, _, hf, _⟩ := hr v rfl
  refine ⟨hte, Or.inr (Or.inr (Or.inl ?_))⟩
  have hloc : locN (setVarHOLFinite (ofString "te") (.val (.word w)) { post with locals := s.locals }) "te" = w.toNat := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  change p + len ≤ _
  rw [hloc]
  exact hp.2.2.trans hf.2.1.1

/-- Restrict the constructor's separation to a store contained in `te`.
This supplies the frame premise for preserving any live caller buffer. -/
theorem phase2_te_store_separation {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p len x n : Nat} (hd : Disj (p, len) (locN s "te", 200))
    (hx : Inside (x, n) (locN s "te") (locN s "te" + 200)) :
    Disj (p, len) (x, n) :=
  disj_of_inside_right hx hd

/-- Transaction validity survives a disjoint single-word heap store once the
world frame has been established. The access-list record array is framed
separately from the transaction header. -/
theorem phase2_store_txReadyStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : TxReadyStrong s) {S Nd : List Nat}
    (hT : TxAccessListAt s S Nd (locN s "tx"))
    {x : BitVec 64} {mem : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (hW : WorldTypedWith { s with memory := mem } S Nd)
    (how : worldOwned { s with memory := mem } S Nd = worldOwned s S Nd)
    (hE : TxEnv { s with memory := mem })
    (htx : Disj (locN s "tx", 384) (x.toNat, 8))
    (hrec : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (x.toNat, 8)) :
    TxReadyStrong { s with memory := mem } := by
  have hA := hp.1.1.1
  have hAp : ArenaReady { s with memory := mem } :=
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) htx
  have hur : 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s { s with memory := mem }
        (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hn
    exact ivlUnhit_single hm (by dsimp; omega) (hrec hn)
  have hT' := R16Shards.PtxP1.txAccessListAt_congr_unhit
    (post := { s with memory := mem }) hA.2 hA.1 hAp.1 le_rfl hT
    (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2) hu hur
  exact R16Shards.PtxP1.txReadyStrong_of_parts hAp hE hW hT'

/-- Lift the transaction frame to the actual Phase 2 entry invariant. Sender
allocation and gas bounds are unaffected by a memory-only update. -/
theorem phase2_store_validatedStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxValidatedStrong s) {S Nd : List Nat}
    (hT : TxAccessListAt s S Nd (locN s "tx"))
    {x : BitVec 64} {mem : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (hW : WorldTypedWith { s with memory := mem } S Nd)
    (how : worldOwned { s with memory := mem } S Nd = worldOwned s S Nd)
    (hE : TxEnv { s with memory := mem })
    (htx : Disj (locN s "tx", 384) (x.toNat, 8))
    (hrec : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (x.toNat, 8)) :
    PtxValidatedStrong { s with memory := mem } := by
  have ht := phase2_store_txReadyStrong hp.1.1 hT hm hW how hE htx hrec
  refine ⟨⟨ht, hp.1.2.1, ?_, hp.1.2.2.2⟩, ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1.1 ht.1.1.1.1 hp.1.2.2.1
  · exact ⟨hp.2.scalar, hp.2.price, hp.2.enc, hp.2.intrinsic⟩

/-- Keep the transaction environment's allocated extent and world separation
after a framed store. Zero-initialization is intentionally consumed by stores. -/
def PtxTeLive : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxValidatedStrong s ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "te") = some (.val (.word w))) ∧
    Inside (locN s "te", 200) InitE.sourceBase (globN s "heap_ptr") ∧
    locN s "te" % 8 = 0 ∧ WordsOK s (locN s "te", 200) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd)

theorem phase2_teAllocated_live {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeAllocated s) : PtxTeLive s :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.2⟩

theorem phase2_teLive_memory {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeLive s) {mem : BitVec 64 → HolWordLab 64}
    (hv : PtxValidatedStrong { s with memory := mem })
    (hw : ∀ S Nd, WorldTypedWith s S Nd →
      WorldTypedWith { s with memory := mem } S Nd ∧
        worldOwned { s with memory := mem } S Nd = worldOwned s S Nd) :
    PtxTeLive { s with memory := mem } := by
  refine ⟨hv, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1.1.1 hv.1.1.1.1.1.1 hp.2.2.2.2.1
  · obtain ⟨S, Nd, hW, hd⟩ := hp.2.2.2.2.2
    obtain ⟨hW', heq⟩ := hw S Nd hW
    exact ⟨S, Nd, hW', by rw [heq]; exact hd⟩

/-- A single-word store in a buffer disjoint from all world-owned objects
leaves every world-owned interval untouched. -/
theorem phase2_store_world_unhit {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    {p len : Nat} (hd : IvlsDisj [(p, len)] (worldOwned s S Nd))
    {x : BitVec 64} (hx : Inside (x.toNat, 8) p (p + len))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    ∀ i ∈ worldOwned s S Nd, IvlUnhit s { s with memory := mem } i := by
  intro i hi
  exact ivlUnhit_single hm (worldOwned_zero_aligned hW i hi)
    (disj_of_inside_right hx (disj_symm (hd (p, len) (by simp) i hi)))

/-- In particular, the block-output header is untouched by a disjoint store;
its six transaction-environment fields can therefore be transported together. -/
theorem phase2_store_txEnv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd) {p len : Nat}
    (hd : IvlsDisj [(p, len)] (worldOwned s S Nd))
    {x : BitVec 64} (hx : Inside (x.toNat, 8) p (p + len))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    TxEnv { s with memory := mem } := by
  have hfix : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa only [hE.bo_nz, if_false] using
      typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by simp [typedRecords])
  have how : (globN s "bo", 88) ∈ worldOwned s S Nd :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hfix)))
  have hu := phase2_store_world_unhit hW hd hx hm _ how
  have hb := bo_words hW.2.2.1 hE.bo_nz
  have hhi := (ivl_allocated_bound hA.2 hb.1).2
  have hk : ∀ k, k % 8 = 0 → k + 8 ≤ 88 →
      memW { s with memory := mem } (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hkal hk
    exact memW_eq_of_ivlUnhit hu (by have := hb.2.1; omega) hhi
      ⟨by dsimp; omega, by dsimp; omega⟩
  refine ⟨hE.bo_nz, ?_, ?_, ?_, ?_, ?_, hE.jcap_nz⟩
  · change memW { s with memory := mem } (globN s "bo" + 24) ≠ 0
    rw [hk 24 (by omega) (by omega)]; exact hE.bo24
  · change memW { s with memory := mem } (globN s "bo" + 32) ≠ 0
    rw [hk 32 (by omega) (by omega)]; exact hE.bo32
  · change memW { s with memory := mem } (globN s "bo" + 40) ≠ 0
    rw [hk 40 (by omega) (by omega)]; exact hE.bo40
  · change memW { s with memory := mem } (globN s "bo" + 72) ≠ 0
    rw [hk 72 (by omega) (by omega)]; exact hE.bo72
  · change locN s "index" < memW { s with memory := mem } (globN s "bo" + 80)
    rw [hk 80 (by omega) (by omega)]; exact hE.idx_lt

/-- Complete single-word store frame for Phase 2: world ownership and the
two live transaction buffers suffice to preserve the validated strong state. -/
theorem phase2_store_validated_outside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxValidatedStrong s) {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd)
    (hT : TxAccessListAt s S Nd (locN s "tx"))
    {blk : Ivl} (hd : ∀ o ∈ worldOwned s S Nd, Disj blk o)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) blk.1 (blk.1 + blk.2))
    (htx : Disj (locN s "tx", 384) blk)
    (hrec : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) blk)
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxValidatedStrong { s with memory := mem } ∧
    WorldTypedWith { s with memory := mem } S Nd ∧
    worldOwned { s with memory := mem } S Nd = worldOwned s S Nd := by
  obtain ⟨hW', how, hE'⟩ := store_outside_worldOwned
    hp.1.1.1.1.1 (R16Shards.PtxP1.txEnv_of_ready hp.1.1) hW hd hx hin hm
  exact ⟨phase2_store_validatedStrong hp hT hm hW' how hE'
    (disj_of_inside_right hin htx)
    (fun hn => disj_of_inside_right hin (hrec hn)), hW', how⟩

/-- A store in the live transaction environment preserves its allocation and
world separation as well as the validated transaction. The access-list witness
is supplied for the same world that separates the environment. -/
theorem phase2_teLive_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeLive s)
    (hT : ∀ S Nd, WorldTypedWith s S Nd →
      IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd) →
      TxAccessListAt s S Nd (locN s "tx"))
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200))
    (htx : Disj (locN s "tx", 384) (locN s "te", 200))
    (hrec : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (locN s "te", 200))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxTeLive { s with memory := mem } := by
  obtain ⟨S, Nd, hW, hd⟩ := hp.2.2.2.2.2
  obtain ⟨hv, hW', how⟩ := phase2_store_validated_outside hp.1 hW (hT S Nd hW hd)
    (blk := (locN s "te", 200)) (fun o ho => hd _ (by simp) o ho)
    hx hin htx hrec hm
  refine ⟨hv, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_, S, Nd, hW', ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1.1.1 hv.1.1.1.1.1.1 hp.2.2.2.2.1
  · rw [how]
    exact hd

/-- Store-ready environment: transaction and environment separation use the
same world witness, so successive stores need no witness reconciliation. -/
def PtxTeStoreReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PtxTeLive s ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd) ∧
      Disj (locN s "tx", 384) (locN s "te", 200) ∧
      (0 < memW s (locN s "tx" + 216) →
        Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
          (locN s "te", 200))

theorem phase2_teStoreReady_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxTeStoreReady { s with memory := mem } := by
  obtain ⟨hl, S, Nd, hW, hT, hd, htx, hrec⟩ := hp
  obtain ⟨hv, hW', how⟩ := phase2_store_validated_outside hl.1 hW hT
    (blk := (locN s "te", 200)) (fun o ho => hd _ (by simp) o ho)
    hx hin htx hrec hm
  have hA := hl.1.1.1.1.1.1
  have hAp := hv.1.1.1.1.1
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hin htx)
  have hur : 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s { s with memory := mem }
        (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hn
    exact ivlUnhit_single hm (by dsimp; omega) (disj_of_inside_right hin (hrec hn))
  have hT' := R16Shards.PtxP1.txAccessListAt_congr_unhit
    (post := { s with memory := mem }) hA.2 hA.1 hAp.1 le_rfl hT
    (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2) hu hur
  have hd' : IvlsDisj [(locN s "te", 200)] (worldOwned { s with memory := mem } S Nd) := by
    rw [how]; exact hd
  have hl' : PtxTeLive { s with memory := mem } :=
    ⟨hv, hl.2.1, hl.2.2.1, hl.2.2.2.1,
      wordsOK_transfer hA.1 hAp.1 hl.2.2.2.2.1, S, Nd, hW', hd'⟩
  have htwords := hT.1.1
  have hthi := (ivl_allocated_bound hA.2 (Or.inl hT.1.2.1)).2
  have heq : ∀ k, k % 8 = 0 → k + 8 ≤ 384 →
      memW { s with memory := mem } (locN s "tx" + k) = memW s (locN s "tx" + k) := by
    intro k hk hle
    exact memW_eq_of_ivlUnhit hu (by have := htwords.1; omega) hthi
      ⟨by dsimp; omega, by dsimp; omega⟩
  refine ⟨hl', S, Nd, hW', hT', hd', htx, ?_⟩
  change 0 < memW { s with memory := mem } (locN s "tx" + 216) →
    Disj (memW { s with memory := mem } (locN s "tx" + 208),
      24 * memW { s with memory := mem } (locN s "tx" + 216)) (locN s "te", 200)
  simpa only [heq 216 (by decide) (by decide), heq 208 (by decide) (by decide)] using hrec

/-- Every aligned word offset of the live environment denotes an allocated
address, without modular wraparound. -/
theorem phase2_teLive_slot {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeLive s) (k : Nat) (hk : k < 25) :
    let x := BitVec.ofNat 64 (locN s "te" + 8 * k)
    x.toNat = locN s "te" + 8 * k ∧ s.memaddrs x ∧
      Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200) := by
  have hA := hp.1.1.1.1.1.1
  have hhi := (ivl_allocated_bound hA.2 (Or.inl hp.2.2.1)).2
  have hlt : locN s "te" + 8 * k < 2 ^ 64 := by dsimp at hhi; omega
  have heq : (BitVec.ofNat 64 (locN s "te" + 8 * k)).toNat = locN s "te" + 8 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨heq, ?_, ?_⟩
  · rw [hA.1.memaddrs]
    apply (ordinaryDomain_iff _).mpr
    rw [heq]
    have hlo := hp.2.2.1.1
    have hal := hp.2.2.2.1
    constructor
    · omega
    · constructor
      · exact Nat.le_trans hlo (by omega)
      · have hbound := hA.2
        have hinside := hp.2.2.1
        unfold Inside at hinside
        rcases hbound with ⟨_, _, _, _⟩
        unfold heapLimit at *
        have : InitE.scratchStart ≤ InitE.heapEnd := by decide
        omega
  · rw [heq]
    constructor <;> dsimp <;> omega

/-- Instantiation of the store frame at a concrete environment word slot.
The slot lemma discharges both address validity and extent containment. -/
theorem phase2_teStoreReady_slot_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) (k : Nat) (hk : k < 25)
    {mem : BitVec 64 → HolWordLab 64}
    (hm : ∀ a, a ≠ BitVec.ofNat 64 (locN s "te" + 8 * k) → mem a = s.memory a) :
    PtxTeStoreReady { s with memory := mem } := by
  obtain ⟨_, hx, hin⟩ := phase2_teLive_slot hp.1 k hk
  exact phase2_teStoreReady_store hp hx hin hm

/-- Program-level scalar store rule for the environment initialization. -/
theorem phase2_teStoreReady_scalar_hoare (addr : ExpHOL 64) (name : String)
    (hn : name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String))
    (ha : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64),
      PtxTeStoreReady s → evalAt s addr = some (.val (.word x)) →
      Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200)) :
    Hoare PtxTeStoreReady (.store addr (.var .local (ofString name)))
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.2.scalar name hn
  have he : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  subst v
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact phase2_teStoreReady_store hp hdom (ha s x hp hx) hmem

theorem phase2_teStoreReady_base_scalar (name : String)
    (hn : name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String)) :
    Hoare PtxTeStoreReady
      (.store (.var .local (ofString "te")) (.var .local (ofString name)))
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply phase2_teStoreReady_scalar_hoare _ name hn
  intro F s x hp hx
  obtain ⟨w, hw⟩ := hp.1.2.1
  have he : x = w := by simpa [evalAt, evalHOLExact, hw] using hx.symm
  subst x
  have hl : locN s "te" = w.toNat := by simp [locN, hw]
  rw [hl]
  constructor <;> dsimp <;> omega

theorem phase2_te_offset_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeLive s) (off : Nat) (hoff : off + 8 ≤ 200)
    {x : BitVec 64}
    (hx : evalAt s (.op .add [.var .local (ofString "te"), .const off]) = some (.val (.word x))) :
    Inside (x.toNat, 8) (locN s "te") (locN s "te" + 200) := by
  obtain ⟨w, hw⟩ := hp.2.1
  have hl : locN s "te" = w.toNat := by simp [locN, hw]
  have hhi := (ivl_allocated_bound hp.1.1.1.1.1.1.2 (Or.inl hp.2.2.1)).2
  have he : x = w + BitVec.ofNat 64 off := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr] using hx.symm
  have ho : off < 2 ^ 64 := by omega
  have hn : x.toNat = w.toNat + off := by
    rw [he, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho,
      Nat.mod_eq_of_lt (by dsimp at hhi; rw [hl] at hhi; omega)]
  rw [hn, hl]
  constructor <;> dsimp <;> omega

theorem phase2_teStoreReady_offset_scalar (off : Nat) (hoff : off + 8 ≤ 200)
    (name : String)
    (hn : name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used"] : List String)) :
    Hoare PtxTeStoreReady
      (.store (.op .add [.var .local (ofString "te"), .const off]) (.var .local (ofString name)))
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply phase2_teStoreReady_scalar_hoare _ name hn
  intro F s x hp hx
  exact phase2_te_offset_inside hp.1 off hoff hx

/-- Consecutive word writes preserve the store-ready invariant when all writes
fit in the environment. This covers the four-word price store. -/
theorem phase2_teStoreReady_words {F : Type} (ws : List (HolWordLab 64))
    {s : PanSemStateFiniteExact 64 F} (hp : PtxTeStoreReady s)
    (k : Nat) (hk : k + ws.length ≤ 25)
    {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "te" + 8 * k)) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxTeStoreReady { s with memory := mem } := by
  induction ws generalizing s k mem with
  | nil =>
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst mem
    exact hp
  | cons w ws ih =>
    have hk' : k < 25 := by simp only [List.length_cons] at hk; omega
    have hslot := phase2_teLive_slot hp.1 k hk'
    let x := BitVec.ofNat 64 (locN s "te" + 8 * k)
    let mem1 := fun a => if a = x then w else s.memory a
    have hp1 : PtxTeStoreReady { s with memory := mem1 } :=
      phase2_teStoreReady_slot_store hp k hk' (fun a ha => if_neg ha)
    have he : x + BitVec.ofNat 64 8 = BitVec.ofNat 64 (locN s "te" + 8 * (k + 1)) := by
      simp only [x, ← BitVec.ofNat_add]
      congr 1
    simp only [panMemStoresHOL, panMemStoreHOL, hslot.2.1, ↓reduceIte] at hst
    apply ih hp1 (k + 1) (by simp only [List.length_cons] at hk; omega)
    change @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "te" + 8 * (k + 1))) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem
    change @panMemStoresHOL 64 _ (x + BitVec.ofNat 64 8) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem at hst
    rw [he] at hst
    exact hst

/-- Four-word price initialization, using consecutive-word preservation. -/
theorem phase2_teStoreReady_price_hoare (addr : ExpHOL 64) (k : Nat)
    (hk : k + 4 ≤ 25)
    (ha : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64),
      PtxTeStoreReady s → evalAt s addr = some (.val (.word x)) →
      x = BitVec.ofNat 64 (locN s "te" + 8 * k)) :
    Hoare PtxTeStoreReady (.store addr (.var .local (ofString "price")))
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨a, b, c, d, hw⟩ := hp.1.1.2.price
  have he : v = .rStruct [.val (.word a), .val (.word b), .val (.word c), .val (.word d)] := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  subst v
  rw [ha s x hp hx] at hst
  exact phase2_teStoreReady_words [.word a, .word b, .word c, .word d] hp k
    (by simpa using hk) (by simpa [flattenHOL] using hst)

theorem phase2_teStoreReady_offset_price (k : Nat) (hk : k + 4 ≤ 25) :
    Hoare PtxTeStoreReady
      (.store (.op .add [.var .local (ofString "te"), .const (8 * k)])
        (.var .local (ofString "price")))
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply phase2_teStoreReady_price_hoare _ k hk
  intro F s x hp hx
  obtain ⟨w, hw⟩ := hp.1.2.1
  have hl : locN s "te" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  simp [he, hl, BitVec.ofNat_add]

/-- The constructor's fresh-block separation and surviving access list share
one world witness, obtained from a single application of its world contract. -/
theorem phase2_te_new_joint_world (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn PtxValidatedStrong
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  obtain ⟨w, rfl⟩ := R16Shards.PtxP1.shape_one_word
    (by simpa only [shapeEqHOL_eq_true] using hsh)
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_te_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨_, rfl⟩)
  obtain ⟨S, Nd, hW, hT⟩ := hp.1.1.2.2.2.2
  have hWe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hex⟩ := step.2.2.2.2 S Nd hWe (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hp.1.1.1.1.1
    step.1.1 step.2.1 hW (R := []) (by simp) hgrow hframe hT (by simp) (by simp)
    (locals := s.locals) (by rfl)
  obtain ⟨w', heq, hav⟩ := hex _ rfl
  have heq' : w = w' := by simpa using heq
  subst w'
  let out := setVarHOLFinite (ofString "te") (.val (.word w)) { post with locals := s.locals }
  have htx : locN out "tx" = locN s "tx" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "te" ≠ ofString "tx" from by decide]
  have hte : locN out "te" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
  · change TxAccessListAt out S' Nd' (locN out "tx")
    rw [htx]
    exact R16Shards.PtxP1.txAccessListAt_with_locals _ _ _ hTp
  · change IvlsDisj [(locN out "te", 200)] (worldOwned post S' Nd')
    rw [hte]
    exact hav

/-- The transaction header is an existing heap buffer, hence is disjoint from
the fresh environment returned by the constructor. -/
theorem phase2_te_new_tx_separation (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn PtxValidatedStrong
      (fun s => Disj (locN s "tx", 384) (locN s "te", 200))
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have ht := R16Shards.PtxP1.txReadyStrong_txValid hp.1.1
  have hs := phase2_te_new_separates h (locN s "tx") 384
    s vs body callee ret v post hc ⟨hp, ht.2.1⟩ ha hl hb hsh
  have htx : locN (setVarHOLFinite (ofString "te") v { post with locals := s.locals }) "tx" =
      locN s "tx" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "te" ≠ ofString "tx" from by decide]
  rw [htx]
  exact hs.2

/-- The constructor preserves every aligned word of the transaction header,
including the access-list pointer and count used to frame its record buffer. -/
theorem phase2_te_new_header_words (h : PtxCallees) (k value : Nat)
    (hk : k % 8 = 0) (hkle : k + 8 ≤ 384) :
    R16Shards.PtxP1.DecCallResumeShapeOn
      (fun s => PtxValidatedStrong s ∧ memW s (locN s "tx" + k) = value)
      (fun s => memW s (locN s "tx" + k) = value)
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_te_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT⟩ := hp.1.1.1.2.2.2.2
  have hWe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', _, _, hgrow, hframe, _⟩ := step.2.2.2.2 S Nd hWe (by simp [IvlsDisj])
  have hA := hp.1.1.1.1.1.1
  obtain ⟨_, _, hu⟩ := heap_ivl_survives_step (s := s) (post := post)
    hA.2 step.2.1 (worldOwned_zero_aligned hW) (R := []) (by simp) hgrow hframe
    hT.1.1.1 (by simp) hT.1.2.1 (fun j hj => hT.2.1 _ (by simp) j hj) (by simp)
  have he := memW_eq_of_ivlUnhit hu (a := locN s "tx" + k)
    (by have := hT.1.1.1; omega)
    (ivl_allocated_bound hA.2 (Or.inl hT.1.2.1)).2
    ⟨by dsimp; omega, by dsimp; omega⟩
  have htx : locN (setVarHOLFinite (ofString "te") v { post with locals := s.locals }) "tx" = locN s "tx" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "te" ≠ ofString "tx" from by decide]
  rw [htx]
  exact he.trans hp.2

/-- The constructor establishes the full invariant needed by all environment
initialization stores, including separation from the access-list records. -/
theorem phase2_resume_te_storeReady (h : PtxCallees) :
    R16Shards.PtxP1.DecCallResumeShapeOn PtxValidatedStrong PtxTeStoreReady
      (ofString "te") .one (ofString "te_new") [] := by
  intro F s vs body callee ret v post hc hp ha hl hb hsh
  have hal := phase2_resume_te_new h s vs body callee ret v post hc hp ha hl hb hsh
  obtain ⟨S, Nd, hW, hT, hd⟩ := phase2_te_new_joint_world h
    s vs body callee ret v post hc hp ha hl hb hsh
  have htx := phase2_te_new_tx_separation h s vs body callee ret v post hc hp ha hl hb hsh
  have h208 := phase2_te_new_header_words h 208 (memW s (locN s "tx" + 208))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb hsh
  have h216 := phase2_te_new_header_words h 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb hsh
  refine ⟨phase2_teAllocated_live hal, S, Nd, hW, hT, hd, htx, ?_⟩
  rw [h208, h216]
  intro hn
  obtain ⟨S0, Nd0, hW0, hT0⟩ := hp.1.1.2.2.2.2
  have hs := phase2_te_new_separates h (memW s (locN s "tx" + 208))
    (24 * memW s (locN s "tx" + 216))
    s vs body callee ret v post hc ⟨hp, (hT0.2.2 hn).1⟩ ha hl hb hsh
  exact hs.2

theorem phase2_te_new_storeReady_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxTeStoreReady tail b) :
    TerminatingProgBoundedOn PtxValidatedStrong
      (.decCall (ofString "te") .one (ofString "te_new") [] tail) (K.te_new + b + 1) := by
  apply R16Shards.PtxP1.decCall_shape_bound h.fb_te_new
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · exact phase2_resume_te_storeReady h
  · exact ht

/-- Store any fixed-width expression at an aligned environment offset. This
also handles the transaction-header loads in the initialization sequence. -/
theorem phase2_teStoreReady_expr_store (src : ExpHOL 64) (k n : Nat)
    (hk : k + n ≤ 25)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxTeStoreReady s → evalAt s src = some v → (flattenHOL v).length = n) :
    Hoare PtxTeStoreReady
      (.store (.op .add [.var .local (ofString "te"), .const (8 * k)]) src)
      (fun r s => r = none → PtxTeStoreReady s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.2.1
  have hl : locN s "te" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "te" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact phase2_teStoreReady_words (flattenHOL v) hp k (by rw [hlen s v hp hv]; exact hk) hst

theorem phase2_load_one_length {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr : ExpHOL 64) (v : ValueHOL 64) (h : evalAt s (.load .one addr) = some v) :
    (flattenHOL v).length = 1 := by
  simp [evalAt, evalHOLExact] at h
  split at h
  · simp [memLoadHOLExact] at h
    rcases h with ⟨_, rfl⟩
    simp [flattenHOL]
  · cases h

theorem phase2_load_quad_length {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr : ExpHOL 64) (v : ValueHOL 64)
    (h : evalAt s (.load (.comb [.one, .one, .one, .one]) addr) = some v) :
    (flattenHOL v).length = 4 := by
  simp only [evalAt, evalHOLExact, isWfShapeExactHOL, isWfShapesExactHOL,
    Bool.and_true, ↓reduceIte] at h
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addr
    with _ | va
  · simp [ha] at h
  rcases va with ⟨wa⟩ | _ | _
  · cases wa with
    | word a =>
      simp only [ha, memLoadHOLExact, memLoadsHOLExact] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      simp [flattenHOL]
  · simp [ha] at h
  · simp [ha] at h

/-- The six initialization stores, exactly the spine between `te_new` and
the access-list count declaration. -/
def phase2_teStores (tail : ProgHOL 64) : ProgHOL 64 :=
  spinePlug 6 (spineAt 35 ptxCode) tail

theorem phase2_teStores_bound {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxTeStoreReady tail b) :
    TerminatingProgBoundedOn PtxTeStoreReady (phase2_teStores tail) b := by
  have hs (addr src : ExpHOL 64) : TerminatingProgBoundedOn PtxTeStoreReady (.store addr src) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  unfold phase2_teStores
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  change TerminatingProgBoundedOn PtxTeStoreReady
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 0]) (.var .local (ofString "sender")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 8])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 16])
      (.load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "tx"), .const 160])))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 48]) (.var .local (ofString "price")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 80]) (.var .local (ofString "mgas")))
    (.seq (.store (.op .add [.var .local (ofString "te"), .const 88]) (.var .local (ofString "reservoir"))) tail)))))) b
  have seq0 {a t : ProgHOL 64} (ha : TerminatingProgBoundedOn PtxTeStoreReady a 0)
      (hh : Hoare PtxTeStoreReady a (fun r s => r = none → PtxTeStoreReady s))
      (ht : TerminatingProgBoundedOn PtxTeStoreReady t b) :
      TerminatingProgBoundedOn PtxTeStoreReady (.seq a t) b := by
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans ha hh ht s hc hp
  apply seq0 (hs _ _) (phase2_teStoreReady_offset_scalar 0 (by decide) "sender" (by simp))
  apply seq0 (hs _ _) (phase2_teStoreReady_expr_store _ 1 1 (by decide)
    (fun s v _ hv => phase2_load_one_length s _ v hv))
  apply seq0 (hs _ _) (phase2_teStoreReady_expr_store _ 2 4 (by decide)
    (fun s v _ hv => phase2_load_quad_length s _ v hv))
  apply seq0 (hs _ _) (phase2_teStoreReady_offset_price 6 (by decide))
  apply seq0 (hs _ _) (phase2_teStoreReady_offset_scalar 80 (by decide) "mgas" (by simp))
  apply seq0 (hs _ _) (phase2_teStoreReady_offset_scalar 88 (by decide) "reservoir" (by simp))
  exact ht

/-- Bounded constructor and six-store prefix of Phase 2. -/
theorem phase2_tePrefix_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxTeStoreReady tail b) :
    TerminatingProgBoundedOn PtxValidatedStrong
      (spinePlug 7 (spineAt 34 ptxCode) tail) (K.te_new + b + 1) := by
  have he : spinePlug 7 (spineAt 34 ptxCode) tail =
      .decCall (ofString "te") .one (ofString "te_new") [] (phase2_teStores tail) := by
    simp only [phase2_teStores, ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  rw [he]
  apply phase2_te_new_storeReady_bound h
  exact phase2_teStores_bound ht

/-- Frame the validated state through access-list bookkeeping locals. -/
theorem phase2_validated_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used",
      "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : PtxValidatedStrong s) : PtxValidatedStrong { s with locals := locals, clock := clock } := by
  have hs := locN_congr s locals clock "sender" (hl "sender" (by simp))
  have hm := locN_congr s locals clock "mgas" (hl "mgas" (by simp))
  refine ⟨⟨R16Shards.PtxP1.txReadyStrong_with_locals s locals clock
    (hl "tx" (by simp)) (hl "index" (by simp)) hp.1.1, ?_, ?_, ?_⟩,
    ptxPhase2LocalShapes_with_locals s locals clock hl hp.2⟩
  · rw [hs]; exact hp.1.2.1
  · rw [hs]; exact hp.1.2.2.1
  · rw [hm]; exact hp.1.2.2.2

theorem phase2_teStoreReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["te", "tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used",
      "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : PtxTeStoreReady s) : PtxTeStoreReady { s with locals := locals, clock := clock } := by
  have hte := locN_congr s locals clock "te" (hl "te" (by simp))
  have htx := locN_congr s locals clock "tx" (hl "tx" (by simp))
  have hv := phase2_validated_with_locals s locals clock
    (fun name hn => hl name (List.mem_cons_of_mem _ hn)) hp.1.1
  have hshape : ∃ w : BitVec 64, locals.lookup (ofString "te") = some (.val (.word w)) := by
    rw [hl "te" (by simp)]; exact hp.1.2.1
  obtain ⟨S, Nd, hW, hT, hd, hdt, hdr⟩ := hp.2
  have hW' := (worldTypedWith_with_locals s locals clock S Nd).mpr hW
  have hd' : IvlsDisj [(locN { s with locals := locals, clock := clock } "te", 200)]
      (worldOwned { s with locals := locals, clock := clock } S Nd) := by
    rw [hte]; exact hd
  refine ⟨⟨hv, hshape, ?_, ?_, ?_, S, Nd, hW', hd'⟩, S, Nd, hW', ?_, hd', ?_, ?_⟩
  · rw [hte]; exact hp.1.2.2.1
  · rw [hte]; exact hp.1.2.2.2.1
  · rw [hte]; exact hp.1.2.2.2.2.1
  · rw [htx]; exact R16Shards.PtxP1.txAccessListAt_with_locals s locals clock hT
  · rw [htx, hte]; exact hdt
  · rw [htx, hte]; exact hdr

theorem phase2_teStoreReady_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxTeStoreReady s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["te", "tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used",
      "price", "enc", "intrinsic"] : List String), ofString n ≠ name) :
    PtxTeStoreReady (setVarHOLFinite name v s) := by
  apply phase2_teStoreReady_with_locals s _ s.clock _ hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- Initialize the access-list count without losing the environment frame. -/
theorem phase2_nal_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxTeStoreReady s) :
    let post := setVarHOLFinite (ofString "nal") (.val (.word 0)) s
    PtxTeStoreReady post ∧ locN post "nal" = 0 ∧
      post.locals.lookup (ofString "nal") = some (.val (.word 0)) := by
  refine ⟨phase2_teStoreReady_set_other s hp _ _ (by decide), ?_, ?_⟩
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Read-only calls preserve the initialized environment and its live buffers. -/
theorem phase2_resume_ro_teStoreReady {fname name : MlS}
    (hro : ReadOnlyFn fname)
    (hne : ∀ n ∈ (["te", "tx", "index", "sender", "mgas", "reservoir", "gas", "tx_blob_gas_used",
      "price", "enc", "intrinsic"] : List String), ofString n ≠ name)
    (args : List (ExpHOL 64)) :
    DecCallResumeOn PtxTeStoreReady PtxTeStoreReady name fname args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have hrestore : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [he]; rfl
  apply phase2_teStoreReady_set_other _ _ name v hne
  rw [hrestore]
  exact phase2_teStoreReady_with_locals s s.locals post.clock (fun _ _ => rfl) hp

theorem phase2_resume_has_access_list (h : PtxCallees) :
    DecCallResumeOn PtxTeStoreReady PtxTeStoreReady (ofString "hal")
      (ofString "tx_has_access_list") [.var .local (ofString "tx")] :=
  phase2_resume_ro_teStoreReady h.ro_tx_has_access_list (by decide) _

/-- Loading the transaction's access-list count changes only its bookkeeping local. -/
theorem phase2_nal_set_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxTeStoreReady s) (w : BitVec 64) :
    let post := setVarHOLFinite (ofString "nal") (.val (.word w)) s
    PtxTeStoreReady post ∧ locN post "nal" = w.toNat ∧
      post.locals.lookup (ofString "nal") = some (.val (.word w)) := by
  refine ⟨phase2_teStoreReady_set_other s hp _ _ (by decide), ?_, ?_⟩
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Either outcome of the access-list test preserves the environment frame. -/
theorem phase2_nal_assign_hoare (e : ExpHOL 64) :
    Hoare PtxTeStoreReady (.assign .local (ofString "nal") e)
      (fun r t => r = none → PtxTeStoreReady t) := by
  apply Hoare.assign
  · intro F s v hp _ _
    exact phase2_teStoreReady_set_other s hp _ v (by decide)
  · intro F s hp hr
    simp at hr

/-- The conditional count update preserves the environment on both branches. -/
theorem phase2_nal_cond_hoare (cond e : ExpHOL 64) :
    Hoare PtxTeStoreReady (.ite cond (.assign .local (ofString "nal") e) .skip)
      (fun r t => r = none → PtxTeStoreReady t) := by
  apply Hoare.ite
  · refine ⟨fun s hc hp hn => ?_⟩
    exact (phase2_nal_assign_hoare e).run s hc hp.1 hn
  · exact Hoare.skip (fun s hp _ => hp.1)
  · intro F s hp hr
    simp at hr

/-- Decoder bounds retained by the store-ready invariant control both copy loops. -/
theorem phase2_access_counts_lt {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s) :
    memW s (locN s "tx" + 216) < 2 ^ 32 ∧ txAccessSlots s (locN s "tx") < 2 ^ 32 := by
  obtain ⟨S, Nd, _, ht, _⟩ := hp.2
  exact ⟨ht.1.2.2.2.2.1, ht.1.2.2.2.2.2.1⟩

/-- The address-array size cannot wrap, including its extra first entry. -/
theorem phase2_address_array_size {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxTeStoreReady s)
    (hn : locN s "nal" = 0 ∨ locN s "nal" = memW s (locN s "tx" + 216)) :
    locN s "nal" < 2 ^ 32 ∧ (locN s "nal" + 1) * 8 < 2 ^ 64 := by
  have hc := (phase2_access_counts_lt hp).1
  rcases hn with hn | hn <;> rw [hn] <;> constructor <;> omega

/-- Count information required at the address-array allocation cut. -/
def PtxAccessCountReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxTeStoreReady s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word w))) ∧
  (locN s "nal" = 0 ∨ locN s "nal" = memW s (locN s "tx" + 216))

theorem phase2_accessCountReady_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxTeStoreReady s) :
    PtxAccessCountReady (setVarHOLFinite (ofString "nal") (.val (.word 0)) s) := by
  obtain ⟨hr, hn, hw⟩ := phase2_nal_zero s hp
  exact ⟨hr, ⟨0, hw⟩, Or.inl hn⟩

theorem phase2_accessCountReady_loaded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxTeStoreReady s) (w : BitVec 64)
    (hw : w.toNat = memW s (locN s "tx" + 216)) :
    PtxAccessCountReady (setVarHOLFinite (ofString "nal") (.val (.word w)) s) := by
  obtain ⟨hr, hn, hl⟩ := phase2_nal_set_word s hp w
  refine ⟨hr, ⟨w, hl⟩, Or.inr ?_⟩
  rw [hn, hw]
  simp [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "nal" ≠ ofString "tx" by decide]

theorem phase2_accessCountReady_size {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAccessCountReady s) :
    locN s "nal" < 2 ^ 32 ∧ (locN s "nal" + 1) * 8 < 2 ^ 64 :=
  phase2_address_array_size hp.1 hp.2.2

/-- Count readiness is stable under fresh bookkeeping locals and clock changes. -/
theorem phase2_accessCountReady_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["nal", "te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : PtxAccessCountReady s) :
    PtxAccessCountReady { s with locals := locals, clock := clock } := by
  refine ⟨phase2_teStoreReady_with_locals s locals clock
    (fun name hn => hl name (List.mem_cons_of_mem _ hn)) hp.1, ?_, ?_⟩
  · exact (hl "nal" (by simp)) ▸ hp.2.1
  · have hn := locN_congr s locals clock "nal" (hl "nal" (by simp))
    have ht := locN_congr s locals clock "tx" (hl "tx" (by simp))
    rw [hn, ht]
    exact hp.2.2

theorem phase2_resume_has_access_list_count (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady PtxAccessCountReady (ofString "hal")
      (ofString "tx_has_access_list") [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.ro_tx_has_access_list
    s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have hrestore : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by rw [he]; rfl
  have hp' : PtxAccessCountReady { post with locals := s.locals } := by
    rw [hrestore]
    exact phase2_accessCountReady_with_locals s s.locals post.clock (fun _ _ => rfl) hp
  apply phase2_accessCountReady_with_locals _ _ _ _ hp'
  intro name hn
  have hne : ofString name ≠ ofString "hal" := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst name <;> decide
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm hne]

/-- A count expression with the header's value establishes count readiness. -/
theorem phase2_count_assign_hoare (e : ExpHOL 64)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxAccessCountReady s → evalAt s e = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "tx" + 216)) :
    Hoare PtxAccessCountReady (.assign .local (ofString "nal") e)
      (fun r t => r = none → PtxAccessCountReady t) := by
  apply Hoare.assign
  · intro F s v hp hv _
    obtain ⟨w, rfl, hw⟩ := he s v hp hv
    exact phase2_accessCountReady_loaded s hp.1 w hw
  · intro F s hp hr
    simp at hr

theorem phase2_count_cond_hoare (cond e : ExpHOL 64)
    (he : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxAccessCountReady s → evalAt s e = some v →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "tx" + 216)) :
    Hoare PtxAccessCountReady (.ite cond (.assign .local (ofString "nal") e) .skip)
      (fun r t => r = none → PtxAccessCountReady t) := by
  apply Hoare.ite
  · refine ⟨fun s hc hp hn => ?_⟩
    exact (phase2_count_assign_hoare e he).run s hc hp.1 hn
  · exact Hoare.skip (fun s hp _ => hp.1)
  · intro F s hp hr
    simp at hr

/-- The concrete transaction count load has the value used by count readiness. -/
theorem phase2_count_load {F : Type} (s : PanSemStateFiniteExact 64 F)
    (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "tx"), .const 216])) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s (locN s "tx" + 216) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : s.locals.lookup (ofString "tx") with _ | u
  · simp [hl] at h
  rcases u with ⟨x⟩ | _ | _
  · cases x with
    | word x =>
      simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
      rcases hm : s.memory (x + 216#64) with ⟨y⟩
      refine ⟨y, by rw [← h.2, hm], ?_⟩
      have hadd : BitVec.ofNat 64 (x.toNat + 216) = x + 216#64 := by
        simp [BitVec.ofNat_add]
      simp only [locN, memW, hl, hadd, hm]
  · simp [hl, valueIsWord] at h
  · simp [hl, valueIsWord] at h

/-- Concrete count setup reaches the allocation cut with bounded count data. -/
theorem phase2_countPrefix_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAccessCountReady tail b) :
    TerminatingProgBoundedOn PtxTeStoreReady
      (spinePlug 3 (spineAt 41 ptxCode) tail) (K.tx_has_access_list + b + 1) := by
  simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
  change TerminatingProgBoundedOn PtxTeStoreReady
    (.dec (ofString "nal") .one (.const 0)
      (.decCall (ofString "hal") .one (ofString "tx_has_access_list")
        [.var .local (ofString "tx")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
          (.assign .local (ofString "nal")
            (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))) .skip) tail))) _
  apply dec_bound_trans (Q := PtxAccessCountReady)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact phase2_accessCountReady_zero s hp
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxAccessCountReady) h.fb_tx_has_access_list
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1
  · exact phase2_resume_has_access_list_count h
  · have hi := phase2_count_cond_hoare
      (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
      (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))
      (fun s v _ he => phase2_count_load s v he)
    have hb0 : TerminatingProgBoundedOn PtxAccessCountReady
        (.ite (.cmp .notEqual (.var .local (ofString "hal")) (.const 0))
          (.assign .local (ofString "nal")
            (.load .one (.op .add [.var .local (ofString "tx"), .const 216]))) .skip) 0 := by
      intro F s hc hp hn
      simp only [evaluateHOLFiniteState_ite]
      split
      · split <;> simp only [clock_assign, clock_skip, Nat.zero_add] <;> exact ⟨le_rfl, le_rfl⟩
      · exact ⟨le_rfl, le_rfl⟩
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hb0 hi ht s hc hp

/-- Constructor, initialization stores, and count setup compose at the first
access-list allocation, retaining the strong Phase 1 locals throughout. -/
theorem phase2_allocationEntry_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAccessCountReady tail b) :
    TerminatingProgBoundedOn PtxValidatedStrong
      (spinePlug 10 (spineAt 34 ptxCode) tail)
      (K.te_new + (K.tx_has_access_list + b + 1) + 1) := by
  have he : spinePlug 10 (spineAt 34 ptxCode) tail =
      spinePlug 7 (spineAt 34 ptxCode) (spinePlug 3 (spineAt 41 ptxCode) tail) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction]
    rfl
  rw [he]
  apply phase2_tePrefix_bound h
  exact phase2_countPrefix_bound h ht

/-- The actual address-array allocation expression computes its natural size
without either addition or multiplication wrapping. -/
theorem phase2_address_alloc_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAccessCountReady s) :
    ∃ w : BitVec 64,
      evalAt s (.panop .mul
        [.op .add [.var .local (ofString "nal"), .const 1], .const 8]) =
          some (.val (.word w)) ∧
      w.toNat = (locN s "nal" + 1) * 8 ∧ w.toNat % 8 = 0 ∧ 0 < w.toNat := by
  obtain ⟨n, hn⟩ := hp.2.1
  have hl : locN s "nal" = n.toNat := by simp [locN, hn]
  have hb := phase2_accessCountReady_size hp
  have ha : n.toNat + 1 < 2 ^ 64 := by rw [hl] at hb; omega
  have hm : (n.toNat + 1) * 8 < 2 ^ 64 := by simpa only [hl] using hb.2
  refine ⟨(n + 1) * 8, ?_, ?_, ?_, ?_⟩
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr]
  all_goals
    simp only [BitVec.toNat_mul, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 by decide,
      show (8 : BitVec 64).toNat = 8 by decide,
      Nat.reducePow, Nat.reduceMod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm, hl]
    omega

/-- The allocator contract yields the full, unwrapped address-array block. -/
theorem phase2_address_alloc_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : PtxAccessCountReady s)
    (ha : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) [.panop .mul
      [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hb : (callEntryStateHOLFinite s callee).evaluateHOLFiniteState body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat ((locN s "nal" + 1) * 8) := by
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _, _⟩ := phase2_address_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = (locN s "nal" + 1) * 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1.1.1.1.1)
    (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, hv, _, _, hf⟩ := hr v rfl
  refine ⟨w, hv, ?_⟩
  simpa only [hcn] using hf

/-- A fresh allocation is separate from the live environment, transaction
header, and every nonempty access-list record array. -/
theorem phase2_fresh_separation {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (p size : Nat)
    (hp : PtxAccessCountReady s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post p size) :
    Disj (locN s "te", 200) (p, size) ∧
    Disj (locN s "tx", 384) (p, size) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (p, size)) := by
  have hstart : globN s "heap_ptr" ≤ p := hf.2.1.1
  obtain ⟨S, Nd, _, ht, _⟩ := hp.1.2
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr (Or.inr (Or.inl ?_)), ?_⟩
  · exact hp.1.1.2.2.1.2.trans hstart
  · exact ht.1.2.1.2.trans hstart
  · intro hn
    exact Or.inr (Or.inr (Or.inl ((ht.2.2 hn).1.2.trans hstart)))

/-- Allocation preserves a common world witness for the transaction and the
live environment, including every environment word. -/
theorem phase2_alloc_joint_world (h : PtxCallees) (args : List (ExpHOL 64)) :
    DecCallResumeOn PtxAccessCountReady
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
      (ofString "al_addrs") (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨_, rfl⟩)
  obtain ⟨S, Nd, hW, hT, hd, _⟩ := hp.1.2
  have hWe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', _, hW', hgrow, hframe, _⟩ := step.2.2.2.2 S Nd hWe (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hp.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  have hte := heap_ivl_survives_step hp.1.1.1.1.1.1.1.1.2 step.2.1
    (worldOwned_zero_aligned hW) (R := []) (by simp) hgrow hframe
    hp.1.1.2.2.2.1 (by norm_num) hp.1.1.2.2.1
    (fun j hj => hd _ (by simp) j hj) (by simp)
  let out := setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }
  have htx : locN out "tx" = locN s "tx" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "tx" by decide]
  have htel : locN out "te" = locN s "te" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "te" by decide]
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
  · change TxAccessListAt out S' Nd' (locN out "tx")
    rw [htx]
    exact R16Shards.PtxP1.txAccessListAt_with_locals _ _ _ hTp
  · change IvlsDisj [(locN out "te", 200)] (worldOwned post S' Nd')
    rw [htel]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte.2.1 j hj

/-- Allocation preserves the transaction header values used by both copy loops. -/
theorem phase2_alloc_header_words (h : PtxCallees) (args : List (ExpHOL 64))
    (k value : Nat) (hk : k % 8 = 0) (hkle : k + 8 ≤ 384) :
    DecCallResumeOn
      (fun s => PtxAccessCountReady s ∧ memW s (locN s "tx" + k) = value)
      (fun s => memW s (locN s "tx" + k) = value)
      (ofString "al_addrs") (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, _⟩ := hp.1.1.2
  have hWe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW
  obtain ⟨S', Nd', _, _, hgrow, hframe, _⟩ := step.2.2.2.2 S Nd hWe (by simp [IvlsDisj])
  have hA := hp.1.1.1.1.1.1.1.1.1
  obtain ⟨_, _, hu⟩ := heap_ivl_survives_step (s := s) (post := post)
    hA.2 step.2.1 (worldOwned_zero_aligned hW) (R := []) (by simp) hgrow hframe
    hT.1.1.1 (by simp) hT.1.2.1 (fun j hj => hT.2.1 _ (by simp) j hj) (by simp)
  have he := memW_eq_of_ivlUnhit hu (a := locN s "tx" + k)
    (by have := hT.1.1.1; omega)
    (ivl_allocated_bound hA.2 (Or.inl hT.1.2.1)).2
    ⟨by dsimp; omega, by dsimp; omega⟩
  have htx : locN (setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }) "tx" =
      locN s "tx" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "tx" by decide]
  rw [htx]
  exact he.trans hp.2

/-- The count's word witness and its zero-or-header relation survive allocation. -/
theorem phase2_alloc_count_relation (h : PtxCallees) (args : List (ExpHOL 64)) :
    DecCallResumeOn PtxAccessCountReady
      (fun s => (∃ w : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word w))) ∧
        (locN s "nal" = 0 ∨ locN s "nal" = memW s (locN s "tx" + 216)))
      (ofString "al_addrs") (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hm := phase2_alloc_header_words h args 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  have hn : (setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }).locals.lookup
      (ofString "nal") = s.locals.lookup (ofString "nal") := by
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "nal" by decide]
  refine ⟨?_, ?_⟩
  · rw [hn]
    exact hp.2.1
  · have hloc : locN (setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }) "nal" =
        locN s "nal" := by simp only [locN, hn]
    rw [hloc, hm]
    exact hp.2.2

/-- Allocation retains the validated transaction, sender buffer, gas bound,
and all Phase 1 local shapes. -/
theorem phase2_alloc_validated (h : PtxCallees) (args : List (ExpHOL 64)) :
    DecCallResumeOn PtxValidatedStrong PtxValidatedStrong
      (ofString "al_addrs") (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hstage : R16Shards.PtxP1.StageP 0 s := R16Shards.PtxP1.stage0 hp.1.1
  have hworld := R16Shards.PtxP1.resume_scratch_stage h.wk_alloc
    (gs := []) (by simp [R16Shards.PtxP1.ScratchSpec]) (fun _ => rfl)
    (by decide) (by decide) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by simp) (by decide) (n := 0) (name := ofString "al_addrs") (by decide) args
    s vs body callee ret v post hc hstage ha hl hb
  have hspec := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hspec
  have hh := (hspec (Or.inl ⟨v, rfl⟩)).2.1
  change globN s "heap_ptr" ≤ globN post "heap_ptr" at hh
  have hs := ptxPhase2LocalShapes_set_other _ (ptxPhase2LocalShapes_restore s post hp.2)
    (ofString "al_addrs") v (by decide)
  have hlu : ∀ n ∈ (["sender", "mgas"] : List String),
      locN (setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }) n = locN s n := by
    intro n hn
    have hne : ofString "al_addrs" ≠ ofString n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> decide
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  refine ⟨⟨hworld.1, ?_, ?_, ?_⟩, hs⟩
  · rw [hlu "sender" (by simp)]
    exact ⟨hp.1.2.1.1, hp.1.2.1.2.trans hh⟩
  · rw [hlu "sender" (by simp)]
    exact wordsOK_transfer hp.1.1.1.1.1.1 hworld.1.1.1.1.1 hp.1.2.2.1
  · rw [hlu "mgas" (by simp)]
    exact hp.1.2.2.2

/-- Assemble the complete count-ready invariant after address allocation. -/
theorem phase2_alloc_accessCountReady (h : PtxCallees) (args : List (ExpHOL 64)) :
    DecCallResumeOn PtxAccessCountReady PtxAccessCountReady
      (ofString "al_addrs") (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hv := phase2_alloc_validated h args s vs body callee ret v post hc hp.1.1.1 ha hl hb
  obtain ⟨S, Nd, hW, hT, hd⟩ := phase2_alloc_joint_world h args s vs body callee ret v post hc hp ha hl hb
  have hn := phase2_alloc_count_relation h args s vs body callee ret v post hc hp ha hl hb
  have h208 := phase2_alloc_header_words h args 208 (memW s (locN s "tx" + 208))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  have h216 := phase2_alloc_header_words h args 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hh := (hw (Or.inl ⟨v, rfl⟩)).2.1
  let out := setVarHOLFinite (ofString "al_addrs") v { post with locals := s.locals }
  have hlocal (name : String) (hne : ofString "al_addrs" ≠ ofString name) :
      out.locals.lookup (ofString name) = s.locals.lookup (ofString name) := by
    simp [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
  have hte : locN out "te" = locN s "te" := by simp only [locN, hlocal "te" (by decide)]
  have htx : locN out "tx" = locN s "tx" := by simp only [locN, hlocal "tx" (by decide)]
  have hshape : ∃ w : BitVec 64, out.locals.lookup (ofString "te") = some (.val (.word w)) := by
    rw [hlocal "te" (by decide)]
    exact hp.1.1.2.1
  have hinside : Inside (locN out "te", 200) InitE.sourceBase (globN out "heap_ptr") := by
    rw [hte]
    exact ⟨hp.1.1.2.2.1.1, hp.1.1.2.2.1.2.trans hh⟩
  have halign : locN out "te" % 8 = 0 := by rw [hte]; exact hp.1.1.2.2.2.1
  have hwords : WordsOK out (locN out "te", 200) := by
    rw [hte]
    exact wordsOK_transfer hp.1.1.1.1.1.1.1.1.1 hv.1.1.1.1.1.1 hp.1.1.2.2.2.2.1
  refine ⟨⟨⟨hv, hshape, hinside, halign, hwords, S, Nd, hW, hd⟩,
    S, Nd, hW, hT, hd, ?_, ?_⟩, hn⟩
  · change Disj (locN out "tx", 384) (locN out "te", 200)
    rw [htx, hte]
    exact hp.1.2.choose_spec.choose_spec.2.2.2.1
  · rw [h216, h208]
    change 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (locN out "te", 200)
    rw [hte]
    exact hp.1.2.choose_spec.choose_spec.2.2.2.2

/-- The concrete address allocation is bounded and preserves count readiness. -/
theorem phase2_address_alloc_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAccessCountReady tail b) :
    TerminatingProgBoundedOn PtxAccessCountReady
      (.decCall (ofString "al_addrs") .one (ofString "alloc")
        [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxAccessCountReady) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1
  · exact phase2_alloc_accessCountReady h _
  · exact ht

/-- The first address allocation returns a word pointer to its entire live
array, alongside the preserved count-ready invariant. -/
theorem phase2_address_alloc_live (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady
      (fun s => PtxAccessCountReady s ∧
        (∃ w : BitVec 64, s.locals.lookup (ofString "al_addrs") = some (.val (.word w))) ∧
        Inside (locN s "al_addrs", (locN s "nal" + 1) * 8) InitE.sourceBase (globN s "heap_ptr") ∧
        locN s "al_addrs" % 8 = 0 ∧
        WordsOK s (locN s "al_addrs", (locN s "nal" + 1) * 8))
      (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := phase2_alloc_accessCountReady h _ s vs body callee ret v post hc hp ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_address_alloc_fresh h s vs body callee ret v post hc hp ha hl hb
  have hround : ((locN s "nal" + 1) * 8 + 7) / 8 * 8 = (locN s "nal" + 1) * 8 := by omega
  simp only [FreshBlock, hround] at hf
  let out := setVarHOLFinite (ofString "al_addrs") (.val (.word w)) { post with locals := s.locals }
  have hpointer : locN out "al_addrs" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nal" = locN s "nal" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "nal" by decide]
  refine ⟨hr, ⟨w, ?_⟩, ?_, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · change Inside (locN out "al_addrs", (locN out "nal" + 1) * 8) InitE.sourceBase (globN post "heap_ptr")
    rw [hpointer, hcount]
    exact ⟨hp.1.1.1.1.1.1.1.1.2.1.trans hf.2.1.1, hf.2.1.2⟩
  · change locN out "al_addrs" % 8 = 0
    rw [hpointer]
    exact hf.1
  · change WordsOK post (locN out "al_addrs", (locN out "nal" + 1) * 8)
    rw [hpointer, hcount]
    exact hf.2.2

/-- The allocated address array remains separate from all live input buffers
when expressed in the resumed caller's locals and memory. -/
theorem phase2_address_alloc_separated (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady
      (fun s =>
        Disj (locN s "te", 200) (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
        Disj (locN s "tx", 384) (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
        (0 < memW s (locN s "tx" + 216) →
          Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
            (locN s "al_addrs", (locN s "nal" + 1) * 8)))
      (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have h208 := phase2_alloc_header_words h _ 208 (memW s (locN s "tx" + 208))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  have h216 := phase2_alloc_header_words h _ 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_address_alloc_fresh h s vs body callee ret v post hc hp ha hl hb
  have hd := phase2_fresh_separation s post callee w.toNat ((locN s "nal" + 1) * 8) hp hf
  rw [h208, h216]
  simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "al_addrs" ≠ ofString "te" by decide,
    show ofString "al_addrs" ≠ ofString "tx" by decide,
    show ofString "al_addrs" ≠ ofString "nal" by decide] using hd

/-- The allocator's returned block is outside the same world that owns the
preserved transaction access list. -/
theorem phase2_address_alloc_world (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)] (worldOwned s S Nd) ∧
        IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
      (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _, _⟩ := phase2_address_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = (locN s "nal" + 1) * 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, hdte, _⟩ := hp.1.2
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hte := heap_ivl_survives_step hp.1.1.1.1.1.1.1.1.2 step.2.1
    (worldOwned_zero_aligned hW) (R := []) (by simp) hgrow hframe
    hp.1.1.2.2.2.1 (by norm_num) hp.1.1.2.2.1
    (fun j hj => hdte _ (by simp) j hj) (by simp)
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hp.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨w, rfl, hav⟩ := hret v rfl
  dsimp only at hav
  rw [hcn] at hav
  have hround : ((locN s "nal" + 1) * 8 + 7) / 8 * 8 = (locN s "nal" + 1) * 8 := by omega
  rw [hround] at hav
  let out := setVarHOLFinite (ofString "al_addrs") (.val (.word w)) { post with locals := s.locals }
  have htx : locN out "tx" = locN s "tx" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "tx" by decide]
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_, ?_⟩
  · change TxAccessListAt out S' Nd' (locN out "tx")
    rw [htx]
    exact R16Shards.PtxP1.txAccessListAt_with_locals _ _ _ hTp
  · change IvlsDisj [(locN out "al_addrs", (locN out "nal" + 1) * 8)] (worldOwned post S' Nd')
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_addrs" ≠ ofString "nal" by decide] using hav
  · change IvlsDisj [(locN out "te", 200)] (worldOwned post S' Nd')
    have htel : locN out "te" = locN s "te" := by
      simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "al_addrs" ≠ ofString "te" by decide]
    rw [htel]
    intro i hi j hj
    simp only [List.mem_singleton] at hi
    subst i
    exact hte.2.1 j hj

/-- Address-array storage and input separation available before initialization. -/
def PtxAddressReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAccessCountReady s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "al_addrs") = some (.val (.word w))) ∧
  Inside (locN s "al_addrs", (locN s "nal" + 1) * 8) InitE.sourceBase (globN s "heap_ptr") ∧
  locN s "al_addrs" % 8 = 0 ∧
  WordsOK s (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
  Disj (locN s "te", 200) (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
  Disj (locN s "tx", 384) (locN s "al_addrs", (locN s "nal" + 1) * 8) ∧
  (0 < memW s (locN s "tx" + 216) →
    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_addrs", (locN s "nal" + 1) * 8)) ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)] (worldOwned s S Nd)

/-- Assemble the allocation facts into the address initialization invariant. -/
theorem phase2_address_alloc_ready (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady PtxAddressReady
      (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  obtain ⟨hc', hw, hin, halign, hwords⟩ :=
    phase2_address_alloc_live h s vs body callee ret v post hc hp ha hl hb
  obtain ⟨hte, htx, hrec⟩ :=
    phase2_address_alloc_separated h s vs body callee ret v post hc hp ha hl hb
  obtain ⟨S, Nd, hW, hT, hd, _⟩ :=
    phase2_address_alloc_world h s vs body callee ret v post hc hp ha hl hb
  exact ⟨hc', hw, hin, halign, hwords, hte, htx, hrec, S, Nd, hW, hT, hd⟩

/-- A single word written inside the address array preserves the validated
transaction and the array's world witness. -/
theorem phase2_address_store_validated {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxValidatedStrong { s with memory := mem } ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧
      WorldTypedWith { s with memory := mem } S Nd ∧
      worldOwned { s with memory := mem } S Nd = worldOwned s S Nd := by
  have hv0 := hp.1.1.1.1
  obtain ⟨_, _, _, _, _, _, htx, hrec, S, Nd, hW, hT, hd⟩ := hp
  obtain ⟨hv, hW', how⟩ := phase2_store_validated_outside hv0 hW hT
    (blk := (locN s "al_addrs", (locN s "nal" + 1) * 8))
    (fun o ho => hd _ (by simp) o ho) hx hin htx hrec hm
  exact ⟨hv, S, Nd, hW, hW', how⟩

/-- Address-array writes leave the transaction header unchanged. -/
theorem phase2_address_store_header {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (k : Nat) (hk : k % 8 = 0) (hkle : k + 8 ≤ 384) :
    memW { s with memory := mem } (locN s "tx" + k) = memW s (locN s "tx" + k) := by
  have hA := hp.1.1.1.1.1.1.1.1.1
  obtain ⟨S, Nd, _, hT, _⟩ := hp.1.1.2
  have htx := hp.2.2.2.2.2.2.1
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hin htx)
  exact memW_eq_of_ivlUnhit hu (by have := hT.1.1.1; omega)
    (ivl_allocated_bound hA.2 (Or.inl hT.1.2.1)).2
    ⟨by dsimp; omega, by dsimp; omega⟩

/-- The transaction access-list witness survives a word store into the
separate address array, with the same world witness. -/
theorem phase2_address_store_txAccess {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    ∃ S Nd, WorldTypedWith { s with memory := mem } S Nd ∧
      TxAccessListAt { s with memory := mem } S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)]
        (worldOwned { s with memory := mem } S Nd) := by
  have hv0 := hp.1.1.1.1
  have hA := hp.1.1.1.1.1.1.1.1.1
  obtain ⟨_, _, _, _, _, _, htx, hrec, S, Nd, hW, hT, hd⟩ := hp
  obtain ⟨hv, hW', how⟩ := phase2_store_validated_outside hv0 hW hT
    (blk := (locN s "al_addrs", (locN s "nal" + 1) * 8))
    (fun o ho => hd _ (by simp) o ho) hx hin htx hrec hm
  have hAp := hv.1.1.1.1.1
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hin htx)
  have hur : 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s { s with memory := mem }
        (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hn
    exact ivlUnhit_single hm (by dsimp; omega) (disj_of_inside_right hin (hrec hn))
  refine ⟨S, Nd, hW', ?_, ?_⟩
  · exact R16Shards.PtxP1.txAccessListAt_congr_unhit
      hA.2 hA.1 hAp.1 le_rfl hT
      (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2) hu hur
  · rw [how]
    exact hd

/-- Address-array stores preserve the live environment's complete contents. -/
theorem phase2_address_store_te_unhit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    IvlUnhit s { s with memory := mem } (locN s "te", 200) := by
  exact ivlUnhit_single hm (by simp)
    (disj_of_inside_right hin hp.2.2.2.2.2.1)

/-- Address-array writes preserve the count relation that controls loop entry. -/
theorem phase2_address_store_count {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    let post : PanSemStateFiniteExact 64 F := { s with memory := mem }
    (∃ w : BitVec 64, post.locals.lookup (ofString "nal") = some (.val (.word w))) ∧
      (locN post "nal" = 0 ∨ locN post "nal" = memW post (locN post "tx" + 216)) := by
  have he := phase2_address_store_header hp hin hm 216 (by decide) (by decide)
  refine ⟨hp.1.2.1, ?_⟩
  change locN s "nal" = 0 ∨ locN s "nal" = memW { s with memory := mem } (locN s "tx" + 216)
  rw [he]
  exact hp.1.2.2

/-- A store into the address buffer preserves its word extent and separation
from the transaction's nonempty access-list record array. -/
theorem phase2_address_store_spatial {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    let post : PanSemStateFiniteExact 64 F := { s with memory := mem }
    WordsOK post (locN post "al_addrs", (locN post "nal" + 1) * 8) ∧
    (0 < memW post (locN post "tx" + 216) →
      Disj (memW post (locN post "tx" + 208), 24 * memW post (locN post "tx" + 216))
        (locN post "al_addrs", (locN post "nal" + 1) * 8)) := by
  obtain ⟨hv, _⟩ := phase2_address_store_validated hp hx hin hm
  refine ⟨?_, ?_⟩
  · exact wordsOK_transfer hp.1.1.1.1.1.1.1.1.1.1 hv.1.1.1.1.1.1 hp.2.2.2.2.1
  · change 0 < memW { s with memory := mem } (locN s "tx" + 216) →
      Disj (memW { s with memory := mem } (locN s "tx" + 208),
        24 * memW { s with memory := mem } (locN s "tx" + 216))
        (locN s "al_addrs", (locN s "nal" + 1) * 8)
    simpa only [phase2_address_store_header hp hin hm 216 (by decide) (by decide),
      phase2_address_store_header hp hin hm 208 (by decide) (by decide)] using hp.2.2.2.2.2.2.2.1

/-- Assemble address-buffer store preservation once the environment's
store-ready invariant has been transported. -/
theorem phase2_address_store_ready_of_teReady {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (hte : PtxTeStoreReady { s with memory := mem }) :
    PtxAddressReady { s with memory := mem } := by
  obtain ⟨hnw, hn⟩ := phase2_address_store_count hp hin hm
  obtain ⟨hw, hr⟩ := phase2_address_store_spatial hp hx hin hm
  obtain ⟨S, Nd, hW, hT, hd⟩ := phase2_address_store_txAccess hp hx hin hm
  exact ⟨⟨hte, hnw, hn⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hw,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hr, S, Nd, hW, hT, hd⟩

/-- A shared world witness for both buffers suffices to preserve the complete
environment invariant across an address-buffer store. -/
theorem phase2_address_store_teReady_joint {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hT : TxAccessListAt s S Nd (locN s "tx"))
    (hd : IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)] (worldOwned s S Nd))
    (hte : IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxTeStoreReady { s with memory := mem } := by
  have hl := hp.1.1.1
  have hA := hl.1.1.1.1.1.1
  have htx := hp.2.2.2.2.2.2.1
  have hrec := hp.2.2.2.2.2.2.2.1
  obtain ⟨hv, hW', how⟩ := phase2_store_validated_outside hl.1 hW hT
    (blk := (locN s "al_addrs", (locN s "nal" + 1) * 8))
    (fun o ho => hd _ (by simp) o ho) hx hin htx hrec hm
  have hAp := hv.1.1.1.1.1
  have hu : IvlUnhit s { s with memory := mem } (locN s "tx", 384) :=
    ivlUnhit_single hm (by simp) (disj_of_inside_right hin htx)
  have hur : 0 < memW s (locN s "tx" + 216) →
      IvlUnhit s { s with memory := mem }
        (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) := by
    intro hn
    exact ivlUnhit_single hm (by dsimp; omega) (disj_of_inside_right hin (hrec hn))
  have hT' := R16Shards.PtxP1.txAccessListAt_congr_unhit
    (post := { s with memory := mem }) hA.2 hA.1 hAp.1 le_rfl hT
    (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2) hu hur
  have hte' : IvlsDisj [(locN s "te", 200)] (worldOwned { s with memory := mem } S Nd) := by
    rw [how]; exact hte
  have hl' : PtxTeLive { s with memory := mem } :=
    ⟨hv, hl.2.1, hl.2.2.1, hl.2.2.2.1,
      wordsOK_transfer hA.1 hAp.1 hl.2.2.2.2.1, S, Nd, hW', hte'⟩
  obtain ⟨S0, Nd0, _, _, _, htt, hrr⟩ := hp.1.1.2
  refine ⟨hl', S, Nd, hW', hT', hte', htt, ?_⟩
  change 0 < memW { s with memory := mem } (locN s "tx" + 216) →
    Disj (memW { s with memory := mem } (locN s "tx" + 208),
      24 * memW { s with memory := mem } (locN s "tx" + 216)) (locN s "te", 200)
  simpa only [phase2_address_store_header hp hin hm 216 (by decide) (by decide),
    phase2_address_store_header hp hin hm 208 (by decide) (by decide)] using hrr

/-- The address invariant is stable under a store when both scratch buffers
are disjoint from the same transaction world. -/
theorem phase2_address_store_ready_joint {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {S Nd : List Nat} (hW : WorldTypedWith s S Nd)
    (hT : TxAccessListAt s S Nd (locN s "tx"))
    (hd : IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)] (worldOwned s S Nd))
    (hte : IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd))
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxAddressReady { s with memory := mem } ∧
    WorldTypedWith { s with memory := mem } S Nd ∧
    IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)]
      (worldOwned { s with memory := mem } S Nd) ∧
    IvlsDisj [(locN s "te", 200)] (worldOwned { s with memory := mem } S Nd) := by
  have hte' := phase2_address_store_teReady_joint hp hW hT hd hte hx hin hm
  have hr := phase2_address_store_ready_of_teReady hp hx hin hm hte'
  obtain ⟨_, hW', how⟩ := phase2_store_validated_outside hp.1.1.1.1 hW hT
    (blk := (locN s "al_addrs", (locN s "nal" + 1) * 8))
    (fun o ho => hd _ (by simp) o ho) hx hin
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hm
  exact ⟨hr, hW', by rw [how]; exact hd, by rw [how]; exact hte⟩

/-- Keep the two buffer separations attached to one world throughout Phase 2. -/
def PtxAddressJoint {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAddressReady s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
    TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "al_addrs", (locN s "nal" + 1) * 8)] (worldOwned s S Nd) ∧
    IvlsDisj [(locN s "te", 200)] (worldOwned s S Nd)

theorem phase2_address_alloc_joint (h : PtxCallees) :
    DecCallResumeOn PtxAccessCountReady PtxAddressJoint
      (ofString "al_addrs") (ofString "alloc")
      [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  exact ⟨phase2_address_alloc_ready h s vs body callee ret v post hc hp ha hl hb,
    phase2_address_alloc_world h s vs body callee ret v post hc hp ha hl hb⟩

/-- Address stores preserve the shared witness, including access-list ownership. -/
theorem phase2_address_joint_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressJoint s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxAddressJoint { s with memory := mem } := by
  obtain ⟨hp, S, Nd, hW, hT, hd, hte⟩ := hp
  obtain ⟨hr, hW', hd', hte'⟩ :=
    phase2_address_store_ready_joint hp hW hT hd hte hx hin hm
  obtain ⟨hv, _, how⟩ := phase2_store_validated_outside hp.1.1.1.1 hW hT
    (blk := (locN s "al_addrs", (locN s "nal" + 1) * 8))
    (fun o ho => hd _ (by simp) o ho) hx hin
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hm
  refine ⟨hr, S, Nd, hW', ?_, hd', hte'⟩
  exact R16Shards.PtxP1.txAccessListAt_congr_unhit
    hp.1.1.1.1.1.1.1.1.1.2 hp.1.1.1.1.1.1.1.1.1.1 hv.1.1.1.1.1.1 le_rfl hT
    (by rw [how]; exact hT.2.1) (fun hn => by rw [how]; exact (hT.2.2 hn).2)
    (ivlUnhit_single hm (by simp) (disj_of_inside_right hin hp.2.2.2.2.2.2.1))
    (fun hn => ivlUnhit_single hm (by dsimp; omega)
      (disj_of_inside_right hin (hp.2.2.2.2.2.2.2.1 hn)))

/-- Initialization of the address array with the sender preserves its world. -/
theorem phase2_address_init_hoare :
    Hoare PtxAddressJoint
      (.store (.var .local (ofString "al_addrs")) (.var .local (ofString "sender")))
      (fun r s => r = none → PtxAddressJoint s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.1.1.1.2.scalar "sender" (by simp)
  have he : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  subst v
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  apply phase2_address_joint_store hp hdom _ hmem
  obtain ⟨a, ha⟩ := hp.1.2.1
  have he : x = a := by simpa [evalAt, evalHOLExact, ha] using hx.symm
  subst x
  have hl : locN s "al_addrs" = a.toNat := by simp [locN, ha]
  rw [hl]
  constructor <;> dsimp <;> omega

/-- Any scalar store whose destination lies in the address array retains the
joint invariant; this is also the store rule for the access-list copy loop. -/
theorem phase2_address_store_hoare (addr src : ExpHOL 64)
    (hs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxAddressJoint s → evalAt s src = some v → ∃ w : BitVec 64, v = .val (.word w))
    (ha : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64),
      PtxAddressJoint s → evalAt s addr = some (.val (.word x)) →
      Inside (x.toNat, 8) (locN s "al_addrs")
        (locN s "al_addrs" + (locN s "nal" + 1) * 8)) :
    Hoare PtxAddressJoint (.store addr src) (fun r s => r = none → PtxAddressJoint s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, rfl⟩ := hs s v hp hv
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact phase2_address_joint_store hp hdom (ha s x hp hx) hmem

/-- Loop-local declarations and clock changes preserve the joint buffer world. -/
theorem phase2_address_joint_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["al_addrs", "nal", "te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : PtxAddressJoint s) : PtxAddressJoint { s with locals := locals, clock := clock } := by
  have ha := locN_congr s locals clock "al_addrs" (hl "al_addrs" (by simp))
  have hn := locN_congr s locals clock "nal" (hl "nal" (by simp))
  have he := locN_congr s locals clock "te" (hl "te" (by simp))
  have ht := locN_congr s locals clock "tx" (hl "tx" (by simp))
  have hc := phase2_accessCountReady_with_locals s locals clock
    (fun name hm => hl name (List.mem_cons_of_mem _ hm)) hp.1.1
  obtain ⟨hp, S, Nd, hW, hT, hd, hte⟩ := hp
  have hW' := (worldTypedWith_with_locals s locals clock S Nd).mpr hW
  have hT' := R16Shards.PtxP1.txAccessListAt_with_locals s locals clock hT
  refine ⟨⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, S, Nd, hW', ?_, ?_⟩,
    S, Nd, hW', ?_, ?_, ?_⟩
  · exact (hl "al_addrs" (by simp)) ▸ hp.2.1
  · rw [ha, hn]; exact hp.2.2.1
  · rw [ha]; exact hp.2.2.2.1
  · rw [ha, hn]; exact hp.2.2.2.2.1
  · rw [he, ha, hn]; exact hp.2.2.2.2.2.1
  · rw [ht, ha, hn]; exact hp.2.2.2.2.2.2.1
  · rw [ht, ha, hn]; exact hp.2.2.2.2.2.2.2.1
  · rw [ht]; exact hT'
  · rw [ha, hn]; exact hd
  · rw [ht]; exact hT'
  · rw [ha, hn]; exact hd
  · rw [he]; exact hte

/-- The allocation continuation receives the persistent joint world. -/
theorem phase2_address_alloc_joint_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAddressJoint tail b) :
    TerminatingProgBoundedOn PtxAccessCountReady
      (.decCall (ofString "al_addrs") .one (ofString "alloc")
        [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxAddressJoint) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1.1.1.1
  · exact phase2_address_alloc_joint h
  · exact ht

/-- Allocation and sender initialization expose the joint invariant to the
access-list continuation without consuming any extra store clock. -/
theorem phase2_address_initialized_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAddressJoint tail b) :
    TerminatingProgBoundedOn PtxAccessCountReady
      (.decCall (ofString "al_addrs") .one (ofString "alloc")
        [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]]
        (.seq (.store (.var .local (ofString "al_addrs")) (.var .local (ofString "sender"))) tail))
      (K.alloc + b + 1) := by
  apply phase2_address_alloc_joint_bound h
  have hs : TerminatingProgBoundedOn PtxAddressJoint
      (.store (.var .local (ofString "al_addrs")) (.var .local (ofString "sender"))) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  intro F s hc hp
  simpa only [Nat.zero_add] using seq_bound_trans hs phase2_address_init_hoare ht s hc hp

/-- Each copy-loop destination, including the final access-list entry, is a
nonwrapping word slot within the allocated address array. -/
theorem phase2_address_copy_slot {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressJoint s) (i : Nat) (hi : i < locN s "nal") :
    let x := BitVec.ofNat 64 (locN s "al_addrs" + 8 * (i + 1))
    x.toNat = locN s "al_addrs" + 8 * (i + 1) ∧
      Inside (x.toNat, 8) (locN s "al_addrs")
        (locN s "al_addrs" + (locN s "nal" + 1) * 8) := by
  have hA := hp.1.1.1.1.1.1.1.1.1.1
  have hb := (ivl_allocated_bound hA.2 (Or.inl hp.1.2.2.1)).2
  have hlt : locN s "al_addrs" + 8 * (i + 1) < 2 ^ 64 := by
    dsimp at hb
    omega
  have he : (BitVec.ofNat 64 (locN s "al_addrs" + 8 * (i + 1))).toNat =
      locN s "al_addrs" + 8 * (i + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨he, ?_⟩
  rw [he]
  constructor <;> dsimp <;> omega

/-- A successful word store at a copy-loop slot preserves both buffer frames
and the input access-list witness. -/
theorem phase2_address_copy_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressJoint s) (i : Nat) (hi : i < locN s "nal")
    (w : HolWordLab 64) {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "al_addrs" + 8 * (i + 1)))
      [w] s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxAddressJoint { s with memory := mem } := by
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec hst
  exact phase2_address_joint_store hp hdom (phase2_address_copy_slot hp i hi).2 hmem

/-- Updating a loop-local variable leaves the persistent joint world intact. -/
theorem phase2_address_joint_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressJoint s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["al_addrs", "nal", "te", "tx", "index", "sender", "mgas", "reservoir", "gas",
      "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String), ofString n ≠ name) :
    PtxAddressJoint (setVarHOLFinite name v s) := by
  apply phase2_address_joint_with_locals s _ s.clock _ hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- The actual initial address is the block beneficiary loaded from `be + 32`. -/
theorem phase2_address_beneficiary_hoare :
    Hoare PtxAddressJoint
      (.store (.var .local (ofString "al_addrs"))
        (.load .one (.op .add [.var .global (ofString "be"), .const 32])))
      (fun r s => r = none → PtxAddressJoint s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec hst
  apply phase2_address_joint_store hp hdom _ hmem
  obtain ⟨a, ha⟩ := hp.1.2.1
  have he : x = a := by simpa [evalAt, evalHOLExact, ha] using hx.symm
  subst x
  have hl : locN s "al_addrs" = a.toNat := by simp [locN, ha]
  rw [hl]
  constructor <;> dsimp <;> omega

/-- The AST-matching allocation/beneficiary prefix passes its joint world to
the access-list loops. -/
theorem phase2_address_beneficiary_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxAddressJoint tail b) :
    TerminatingProgBoundedOn PtxAccessCountReady
      (.decCall (ofString "al_addrs") .one (ofString "alloc")
        [.panop .mul [.op .add [.var .local (ofString "nal"), .const 1], .const 8]]
        (.seq (.store (.var .local (ofString "al_addrs"))
          (.load .one (.op .add [.var .global (ofString "be"), .const 32]))) tail))
      (K.alloc + b + 1) := by
  apply phase2_address_alloc_joint_bound h
  have hs : TerminatingProgBoundedOn PtxAddressJoint
      (.store (.var .local (ofString "al_addrs"))
        (.load .one (.op .add [.var .global (ofString "be"), .const 32]))) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  intro F s hc hp
  simpa only [Nat.zero_add] using seq_bound_trans hs phase2_address_beneficiary_hoare ht s hc hp

/-- The address-copy loop retains scalar counters alongside its shared world. -/
def PtxAddressCopyInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAddressJoint s ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word w))) ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "nkeys") = some (.val (.word w))) ∧
    locN s "i" ≤ locN s "nal"

theorem phase2_address_copy_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressJoint s) :
    PtxAddressCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "nkeys") (.val (.word 0)) s)) := by
  have hkeys := phase2_address_joint_set_other s hp (ofString "nkeys") (.val (.word 0)) (by decide)
  have hi := phase2_address_joint_set_other _ hkeys (ofString "i") (.val (.word 0)) (by decide)
  refine ⟨hi, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Copying an address preserves the scalar loop counters and their bound. -/
theorem phase2_address_copy_inv_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s) (hi : locN s "i" < locN s "nal")
    (w : HolWordLab 64) {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _
      (BitVec.ofNat 64 (locN s "al_addrs" + 8 * (locN s "i" + 1)))
      [w] s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxAddressCopyInv { s with memory := mem } := by
  exact ⟨phase2_address_copy_store hp.1 (locN s "i") hi w hst, hp.2⟩

/-- Updating the key counter with a scalar preserves the address-copy invariant. -/
theorem phase2_address_copy_set_nkeys {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) (w : BitVec 64) :
    PtxAddressCopyInv (setVarHOLFinite (ofString "nkeys") (.val (.word w)) s) := by
  refine ⟨phase2_address_joint_set_other s hp.1 _ _ (by decide), ?_, ⟨w, ?_⟩, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "i" by decide] using hp.2.1
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "i" by decide,
      show ofString "nkeys" ≠ ofString "nal" by decide] using hp.2.2.2

/-- The guarded index increment preserves the loop bound and advances exactly
one step without word wraparound. -/
theorem phase2_address_copy_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) (hi : locN s "i" < locN s "nal") :
    let post := setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s
    PtxAddressCopyInv post ∧ locN post "i" = locN s "i" + 1 := by
  obtain ⟨n, hn⟩ := hp.1.1.1.2.1
  have hnlt : locN s "nal" < 2 ^ 64 := by
    simpa [locN, hn] using n.isLt
  have hlt : locN s "i" + 1 < 2 ^ 64 := by omega
  have he : (BitVec.ofNat 64 (locN s "i" + 1)).toNat = locN s "i" + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hidx : locN (setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) "i" = locN s "i" + 1 := by
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using he
  refine ⟨⟨phase2_address_joint_set_other s hp.1 _ _ (by decide),
    ⟨BitVec.ofNat 64 (locN s "i" + 1), by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ?_, ?_⟩, hidx⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.2.2.1
  · rw [hidx]
    have hnal : locN (setVarHOLFinite (ofString "i")
        (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) "nal" = locN s "nal" := by
      simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "nal" by decide]
    rw [hnal]
    omega

/-- The AST key-count assignment preserves the address-copy invariant. -/
theorem phase2_address_copy_nkeys_hoare :
    Hoare PtxAddressCopyInv
      (.assign .local (ofString "nkeys")
        (.op .add [.var .local (ofString "nkeys"),
          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, rfl⟩ := R16Shards.PtxP1.eval_is_word_op he
    exact fun _ => phase2_address_copy_set_nkeys s hp w
  · exact fun _ _ hr => by cases hr

/-- The AST increment preserves the guarded copy invariant. -/
theorem phase2_address_copy_increment_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, hw⟩ := hp.1.2.1
    have hv : v = .val (.word (w + 1)) := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
        valueWord, wordOpHOL, wordOp] using he.symm
    subst v
    have hwN : locN s "i" = w.toNat := by simp [locN, hw]
    have hadd : w + 1 = BitVec.ofNat 64 (locN s "i" + 1) := by
      rw [hwN]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd]
    exact fun _ => (phase2_address_copy_increment s hp.1 hp.2).1
  · exact fun _ _ hr => by cases hr

/-- The key-count assignment also retains the strict guard needed by the
following index increment. -/
theorem phase2_address_copy_nkeys_guard_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.assign .local (ofString "nkeys")
        (.op .add [.var .local (ofString "nkeys"),
          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, rfl⟩ := R16Shards.PtxP1.eval_is_word_op he
    intro _
    refine ⟨phase2_address_copy_set_nkeys s hp.1 w, ?_⟩
    simpa [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "i" by decide,
      show ofString "nkeys" ≠ ofString "nal" by decide] using hp.2
  · exact fun _ _ hr => by cases hr

/-- The two assignments at the end of the copy body preserve its invariant. -/
theorem phase2_address_copy_updates_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.seq
        (.assign .local (ofString "nkeys")
          (.op .add [.var .local (ofString "nkeys"),
            .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  exact Hoare.seq_fall phase2_address_copy_nkeys_guard_hoare
    phase2_address_copy_increment_hoare

/-- Declaring the current access-list record preserves the guarded copy state. -/
theorem phase2_address_copy_set_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") (v : ValueHOL 64) :
    PtxAddressCopyInv (setVarHOLFinite (ofString "acc") v s) ∧
      locN (setVarHOLFinite (ofString "acc") v s) "i" <
        locN (setVarHOLFinite (ofString "acc") v s) "nal" := by
  have hi : locN (setVarHOLFinite (ofString "acc") v s) "i" = locN s "i" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide]
  have hn : locN (setVarHOLFinite (ofString "acc") v s) "nal" = locN s "nal" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "nal" by decide]
  refine ⟨⟨phase2_address_joint_set_other s hp.1.1 _ v (by decide), ?_, ?_, ?_⟩, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide] using hp.1.2.1
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "nkeys" by decide] using hp.1.2.2.1
  · rw [hi, hn]; exact hp.1.2.2.2
  · rw [hi, hn]; exact hp.2

/-- Word arithmetic for the copy destination agrees with its natural slot. -/
theorem phase2_address_copy_word_addr {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s) (a i : BitVec 64)
    (ha : s.locals.lookup (ofString "al_addrs") = some (.val (.word a)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) :
    a + (i + 1) * 8 = BitVec.ofNat 64 (locN s "al_addrs" + 8 * (locN s "i" + 1)) := by
  have han : locN s "al_addrs" = a.toNat := by simp [locN, ha]
  have hin : locN s "i" = i.toNat := by simp [locN, hi]
  rw [han, hin]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.add_mod, Nat.mul_mod, Nat.mul_comm]

/-- The AST address store preserves the joint witness and the strict loop guard. -/
theorem phase2_address_copy_store_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.store (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
        (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨a, ha⟩ := hp.1.1.1.2.1
  obtain ⟨i, hi⟩ := hp.1.2.1
  have he : x = a + (i + 1) * 8 := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hi,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using hx.symm
  rw [he, phase2_address_copy_word_addr hp.1 a i ha hi] at hst
  exact ⟨phase2_address_copy_inv_store hp.1 hp.2 w hst, hp.2⟩

/-- The store and both counter updates compose inside the record declaration. -/
theorem phase2_address_copy_inner_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.seq
        (.store (.op .add [.var .local (ofString "al_addrs"),
          .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
          (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
        (.seq
          (.assign .local (ofString "nkeys")
            (.op .add [.var .local (ofString "nkeys"),
              .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  exact Hoare.seq_fall phase2_address_copy_store_hoare phase2_address_copy_updates_hoare

/-- The copy invariant survives scope restoration and clock changes. -/
theorem phase2_address_copy_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ name ∈ (["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
      "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      locals.lookup (ofString name) = s.locals.lookup (ofString name))
    (hp : PtxAddressCopyInv s) :
    PtxAddressCopyInv { s with locals := locals, clock := clock } := by
  refine ⟨phase2_address_joint_with_locals s locals clock
    (fun name hm => hl name (by simp only [List.mem_cons] at hm ⊢; tauto)) hp.1, ?_, ?_, ?_⟩
  · exact (hl "i" (by simp)) ▸ hp.2.1
  · exact (hl "nkeys" (by simp)) ▸ hp.2.2.1
  · rw [locN_congr s locals clock "i" (hl "i" (by simp)),
      locN_congr s locals clock "nal" (hl "nal" (by simp))]
    exact hp.2.2.2

/-- The complete address-copy body preserves the joint copy invariant. -/
theorem phase2_address_copy_body_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal")
      (.dec (ofString "acc") .one
        (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
          .panop .mul [.var .local (ofString "i"), .const 24]])
        (.seq
          (.store (.op .add [.var .local (ofString "al_addrs"),
            .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
            (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
          (.seq
            (.assign .local (ofString "nkeys")
              (.op .add [.var .local (ofString "nkeys"),
                .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  apply Hoare.dec (names := ["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
    "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"])
    (P' := fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") (by decide)
  · intro F s v hp _
    exact phase2_address_copy_set_acc s hp v
  · exact phase2_address_copy_inner_hoare
  · intro F r s locals hl hp hr
    exact phase2_address_copy_with_locals s locals s.clock hl (hp hr)
  · exact fun _ _ hr => by cases hr

/-- Allocation bounds keep both copy counters in the nonnegative signed range. -/
theorem phase2_address_copy_signed_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s) :
    locN s "i" < 2 ^ 63 ∧ locN s "nal" < 2 ^ 63 := by
  have hj := hp.1
  have hA := hj.1.1.1.1.1.1.1.1.1.1
  have hb := (ivl_allocated_bound hA.2 (Or.inl hj.1.2.2.1)).2
  have hi := hp.2.2.2
  dsimp at hb
  constructor <;> omega

/-- A true signed AST comparison yields the natural copy-loop guard. -/
theorem phase2_address_copy_guard {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s) (w : BitVec 64)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nal"))) = some (.val (.word w)))
    (hnz : w ≠ 0) : locN s "i" < locN s "nal" := by
  obtain ⟨i, hi⟩ := hp.2.1
  obtain ⟨n, hn⟩ := hp.1.1.1.2.1
  obtain ⟨hib, hnb⟩ := phase2_address_copy_signed_bounds hp
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nal" = n.toNat := by simp [locN, hn]
  rw [hil] at hib ⊢
  rw [hnl] at hnb ⊢
  have hc : Compiler.Encoders.Asm.wordCmpHOL .less i n = true := by
    by_contra hc
    simp [evalAt, evalHOLExact, hi, hn, hc] at he
    exact hnz he.symm
  norm_num at hib hnb
  simpa [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
    hib, hnb] using hc

/-- A false copy-loop comparison identifies the completed address count. -/
theorem phase2_address_copy_exit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s)
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nal"))) = some (.val (.word 0))) :
    locN s "i" = locN s "nal" := by
  obtain ⟨i, hi⟩ := hp.2.1
  obtain ⟨n, hn⟩ := hp.1.1.1.2.1
  obtain ⟨hib, hnb⟩ := phase2_address_copy_signed_bounds hp
  have hil : locN s "i" = i.toNat := by simp [locN, hi]
  have hnl : locN s "nal" = n.toNat := by simp [locN, hn]
  rw [hil] at hib
  rw [hnl] at hnb
  norm_num at hib hnb
  have hnot : ¬ i.toNat < n.toNat := by
    simpa [evalAt, evalHOLExact, hi, hn, Compiler.Encoders.Asm.wordCmpHOL,
      Compiler.Encoders.Asm.holAsmSignedLess, hib, hnb] using he
  have hle := hp.2.2.2
  rw [hil, hnl] at hle ⊢
  omega

/-- Guarded copy-body preservation lifts to the whole loop. -/
theorem phase2_address_copy_while_hoare {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") body
      (fun r s => r = none → PtxAddressCopyInv s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxAddressCopyInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" = locN s "nal") := by
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s
    (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxAddressCopyInv st →
      evaluateHOLFiniteState st
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) =
          (none, post) → PtxAddressCopyInv post ∧ locN post "i" = locN post "nal" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd : PtxAddressCopyInv (decClockHOLFinite st) :=
            phase2_address_copy_with_locals st st.locals (st.clock - 1) (by intros; rfl) hp
          have hg := phase2_address_copy_guard hp w hw hnz
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨hd, hg⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r =>
            cases r <;> simp_all
      · rename_i hz
        have hwz : w = 0 := by simpa using hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, phase2_address_copy_exit hp (by simpa [evalAt, hwz] using hw)⟩
    · simp at he

/-- The actual address-copy loop retains the joint world through completion. -/
theorem phase2_address_copy_loop_hoare :
    Hoare PtxAddressCopyInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        (.dec (ofString "acc") .one
          (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
            .panop .mul [.var .local (ofString "i"), .const 24]])
          (.seq
            (.store (.op .add [.var .local (ofString "al_addrs"),
              .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
              (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
            (.seq
              (.assign .local (ofString "nkeys")
                (.op .add [.var .local (ofString "nkeys"),
                  .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))))
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" = locN s "nal") := by
  exact phase2_address_copy_while_hoare phase2_address_copy_body_hoare (by decide) (by decide)

/-- Every successful copy-body execution advances its counter exactly once. -/
theorem phase2_address_copy_body_incr :
    IncrBody (ofString "i")
      (.dec (ofString "acc") .one
        (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
          .panop .mul [.var .local (ofString "i"), .const 24]])
        (.seq
          (.store (.op .add [.var .local (ofString "al_addrs"),
            .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
            (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
          (.seq
            (.assign .local (ofString "nkeys")
              (.op .add [.var .local (ofString "nkeys"),
                .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1]))))) := by
  ptx_incr

/-- Sequencing clock-neutral fragments remains clock-neutral. -/
theorem phase2_clock_seq {p q : ProgHOL 64}
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s p).2.clock = s.clock)
    (hq : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s q).2.clock = s.clock)
    {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.seq p q)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState]
  rcases he : evaluateHOLFiniteState s p with ⟨r, t⟩
  have ht := hp s
  rw [he] at ht
  cases r <;> simp_all

/-- A local declaration around a clock-neutral body is clock-neutral. -/
theorem phase2_clock_dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64)
    {body : ProgHOL 64}
    (hb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s body).2.clock = s.clock)
    {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.dec name shape init body)).2.clock = s.clock := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · dsimp only
      simpa [setVarHOLFinite] using hb (setVarHOLFinite name _ s)
    · rfl

/-- The actual copy body consumes no clock ticks. -/
theorem phase2_address_copy_body_clock {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s
      (.dec (ofString "acc") .one
        (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
          .panop .mul [.var .local (ofString "i"), .const 24]])
        (.seq
          (.store (.op .add [.var .local (ofString "al_addrs"),
            .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
            (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
          (.seq
            (.assign .local (ofString "nkeys")
              (.op .add [.var .local (ofString "nkeys"),
                .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))))).2.clock = s.clock := by
  apply phase2_clock_dec
  intro F t
  apply phase2_clock_seq
  · intro F u; exact clock_store u _ _
  · intro F u
    exact phase2_clock_seq (fun v => clock_assign v _ _ _) (fun v => clock_assign v _ _ _) u

/-- A clock-neutral guarded copy body terminates by its increasing index. -/
theorem phase2_address_copy_while_bound {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal") body
      (fun r s => r = none → PtxAddressCopyInv s))
    (hclock : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s body).2.clock = s.clock)
    (hinc : IncrBody (ofString "i") body) :
    TerminatingProgBoundedOn PtxAddressCopyInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      ((2 ^ 63 + 1) * (0 + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "i")
  · intro F s hp
    exact phase2_address_copy_with_locals s s.locals (s.clock - 1) (by intros; rfl) hp
  · intro F s hc hp hn
    rw [hclock]
    exact ⟨by omega, le_rfl⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := phase2_address_copy_guard hp w hw hnz
    have hd : PtxAddressCopyInv (decClockHOLFinite s) :=
      phase2_address_copy_with_locals s s.locals (s.clock - 1) (by intros; rfl) hp
    obtain ⟨i, hi⟩ := hp.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
    have hnone := hf.resolve_right hnc
    have hpost := hb.run (decClockHOLFinite s) hc ⟨hd, hg⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hil : locN s "i" = i.toNat := by simp [locN, hi]
    have hilt := (phase2_address_copy_signed_bounds hp).1
    have hpl := (phase2_address_copy_signed_bounds hpost).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "i" =
        (i.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hil] at hilt ⊢
    rw [hpn]
    have hmod : (i.toNat + 1) % 2 ^ 64 = i.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at *
    omega

/-- The actual address-copy loop has a uniform terminating clock bound. -/
theorem phase2_address_copy_loop_bound :
    TerminatingProgBoundedOn PtxAddressCopyInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        (.dec (ofString "acc") .one
          (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
            .panop .mul [.var .local (ofString "i"), .const 24]])
          (.seq
            (.store (.op .add [.var .local (ofString "al_addrs"),
              .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
              (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
            (.seq
              (.assign .local (ofString "nkeys")
                (.op .add [.var .local (ofString "nkeys"),
                  .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))))
      (2 ^ 63 + 1) := by
  intro F s hc hp
  simpa only [Nat.zero_add, Nat.mul_one] using
    phase2_address_copy_while_bound phase2_address_copy_body_hoare
      phase2_address_copy_body_clock phase2_address_copy_body_incr s hc hp

/-- Resetting the outer index prepares another pass over the access list. -/
theorem phase2_address_copy_reset {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) :
    PtxAddressCopyInv (setVarHOLFinite (ofString "i") (.val (.word 0)) s) := by
  refine ⟨phase2_address_joint_set_other s hp.1 _ _ (by decide), ⟨0, ?_⟩, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.2.2.1
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The AST reset preserves the shared witness before the key-copy pass. -/
theorem phase2_address_copy_reset_hoare :
    Hoare PtxAddressCopyInv
      (.assign .local (ofString "i") (.const 0))
      (fun r s => r = none → PtxAddressCopyInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hv : v = .val (.word 0) := by
      simpa [evalHOLExact] using he.symm
    subst v
    exact fun _ => phase2_address_copy_reset s hp
  · exact fun _ _ hr => by cases hr

/-- Key-copy scratch declarations preserve the address pass's shared witness. -/
theorem phase2_address_copy_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
      "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    PtxAddressCopyInv (setVarHOLFinite name v s) := by
  apply phase2_address_copy_with_locals s _ s.clock _ hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- Evaluate the actual key-allocation size, retaining its word modulus. -/
theorem phase2_key_alloc_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) :
    ∃ w : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52],
        .const 8]) = some (.val (.word w)) ∧
      w.toNat = (locN s "nkeys" * 52 + 8) % 2 ^ 64 := by
  obtain ⟨n, hn⟩ := hp.2.2.1
  refine ⟨n * 52 + 8, ?_, ?_⟩
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      wordOpHOL, wordOp, panOpHOL]
  · simp [locN, hn, BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod, Nat.mul_mod]

/-- A bounded cumulative count removes the key-allocation word modulus. -/
theorem phase2_key_alloc_size_nonwrapping {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) (hb : locN s "nkeys" * 52 + 8 < 2 ^ 64) :
    ∃ w : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52],
        .const 8]) = some (.val (.word w)) ∧
      w.toNat = locN s "nkeys" * 52 + 8 ∧
      locN s "nkeys" * 52 ≤ (w.toNat + 7) / 8 * 8 := by
  obtain ⟨w, he, hw⟩ := phase2_key_alloc_size s hp
  rw [Nat.mod_eq_of_lt hb] at hw
  refine ⟨w, he, hw, ?_⟩
  rw [hw]
  omega

/-- The shared input witness bounds the total number of storage keys. -/
theorem phase2_address_copy_total_keys {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s) : txAccessSlots s (locN s "tx") < 2 ^ 32 := by
  obtain ⟨S, Nd, hW, hT, hd, he⟩ := hp.1.2
  exact hT.1.2.2.2.2.2.1

/-- Relating the accumulated count to the input total suffices for allocation. -/
theorem phase2_key_alloc_count_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCopyInv s)
    (hk : locN s "nkeys" ≤ txAccessSlots s (locN s "tx")) :
    locN s "nkeys" * 52 + 8 < 2 ^ 64 := by
  have ht := phase2_address_copy_total_keys hp
  omega

/-- Natural cumulative key count for the first `count` access-list records. -/
def phase2_key_prefix {F : Type} (s : PanSemStateFiniteExact 64 F) (count : Nat) : Nat :=
  ((List.range count).map
    (fun i => memW s (memW s (locN s "tx" + 208) + 24 * i + 16))).sum

/-- Advancing the prefix adds exactly the current record's key count. -/
theorem phase2_key_prefix_succ {F : Type} (s : PanSemStateFiniteExact 64 F) (i : Nat) :
    phase2_key_prefix s (i + 1) = phase2_key_prefix s i +
      memW s (memW s (locN s "tx" + 208) + 24 * i + 16) := by
  simp [phase2_key_prefix, List.range_succ, List.map_append, List.sum_append]

/-- Every processed prefix is bounded by the transaction's total key count. -/
theorem phase2_key_prefix_le_total {F : Type} (s : PanSemStateFiniteExact 64 F)
    {i : Nat} (hi : i ≤ memW s (locN s "tx" + 216)) :
    phase2_key_prefix s i ≤ txAccessSlots s (locN s "tx") := by
  have hm : ∀ j k, j ≤ k → phase2_key_prefix s j ≤ phase2_key_prefix s k := by
    intro j k hjk
    induction hjk with
    | refl => exact Nat.le_refl _
    | @step k hk ih =>
      rw [phase2_key_prefix_succ]
      exact Nat.le_trans ih (Nat.le_add_right _ _)
  exact hm i _ hi

/-- Counting-pass invariant connecting the machine accumulator to a natural prefix. -/
def PtxAddressCountInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAddressCopyInv s ∧
  locN s "nal" = memW s (locN s "tx" + 216) ∧
  locN s "nkeys" = phase2_key_prefix s (locN s "i")

/-- The counting invariant supplies the previously conditional allocation bound. -/
theorem phase2_address_count_alloc_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) : locN s "nkeys" * 52 + 8 < 2 ^ 64 := by
  apply phase2_key_alloc_count_bound hp.1
  rw [hp.2.2]
  apply phase2_key_prefix_le_total
  rw [← hp.2.1]
  exact hp.1.2.2.2

/-- Zeroing the counters establishes the strengthened positive-branch invariant. -/
theorem phase2_address_count_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressJoint s) (hn : locN s "nal" ≠ 0) :
    PtxAddressCountInv (setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "nkeys") (.val (.word 0)) s)) := by
  have he : locN s "nal" = memW s (locN s "tx" + 216) :=
    hp.1.1.2.2.resolve_left hn
  refine ⟨phase2_address_copy_init s hp, ?_, ?_⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nal" by decide,
      show ofString "nkeys" ≠ ofString "nal" by decide,
      show ofString "i" ≠ ofString "tx" by decide,
      show ofString "nkeys" ≠ ofString "tx" by decide] using he
  · simp [locN, phase2_key_prefix, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Only the key-count fields of the processed records determine the prefix. -/
theorem phase2_key_prefix_congr {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (i : Nat)
    (hfields : ∀ j, j < i →
      memW t (memW t (locN t "tx" + 208) + 24 * j + 16) =
      memW s (memW s (locN s "tx" + 208) + 24 * j + 16)) :
    phase2_key_prefix t i = phase2_key_prefix s i := by
  unfold phase2_key_prefix
  congr 1
  apply List.map_congr_left
  intro j hj
  exact hfields j (List.mem_range.mp hj)

/-- The strengthened counting invariant discharges the actual allocation expression. -/
theorem phase2_address_count_alloc_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) :
    ∃ w : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52],
        .const 8]) = some (.val (.word w)) ∧
      w.toNat = locN s "nkeys" * 52 + 8 ∧
      locN s "nkeys" * 52 ≤ (w.toNat + 7) / 8 * 8 := by
  exact phase2_key_alloc_size_nonwrapping s hp.1 (phase2_address_count_alloc_bound hp)

/-- Transfer the strengthened invariant across a step preserving count fields. -/
theorem phase2_address_count_frame {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (ht : PtxAddressCopyInv t)
    (hi : locN t "i" = locN s "i")
    (hn : locN t "nkeys" = locN s "nkeys")
    (ha : locN t "nal" = locN s "nal")
    (hc : memW t (locN t "tx" + 216) = memW s (locN s "tx" + 216))
    (hf : ∀ j, j < locN s "i" →
      memW t (memW t (locN t "tx" + 208) + 24 * j + 16) =
      memW s (memW s (locN s "tx" + 208) + 24 * j + 16)) :
    PtxAddressCountInv t := by
  refine ⟨ht, ?_, ?_⟩
  · rw [ha, hc]
    exact hp.2.1
  · rw [hn, hi, phase2_key_prefix_congr s t _ hf]
    exact hp.2.2

/-- The next cumulative count is small enough that the machine addition cannot wrap. -/
theorem phase2_address_count_next_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) (hi : locN s "i" < locN s "nal") :
    locN s "nkeys" +
      memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) < 2 ^ 32 := by
  rw [hp.2.2, ← phase2_key_prefix_succ]
  have hb := phase2_key_prefix_le_total s
    (i := locN s "i" + 1) (by rw [← hp.2.1]; omega)
  exact lt_of_le_of_lt hb (phase2_address_copy_total_keys hp.1)

/-- Scope and clock changes preserve the cumulative count when protected locals agree. -/
theorem phase2_address_count_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hp : PtxAddressCountInv s)
    (hl : ∀ n ∈ (["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
      "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      ls.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxAddressCountInv { s with locals := ls, clock := clock } := by
  apply phase2_address_count_frame s _ hp
    (phase2_address_copy_with_locals s ls clock hl hp.1)
  · simp [locN, hl "i" (by simp)]
  · simp [locN, hl "nkeys" (by simp)]
  · simp [locN, hl "nal" (by simp)]
  · simp [memW, locN, hl "tx" (by simp)]
  · intro j hj
    simp [memW, locN, hl "tx" (by simp)]

/-- Address-buffer writes leave every access-record key-count field unchanged. -/
theorem phase2_address_store_key_field {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressReady s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (j : Nat) (hj : j < memW s (locN s "tx" + 216)) :
    memW { s with memory := mem } (memW s (locN s "tx" + 208) + 24 * j + 16) =
      memW s (memW s (locN s "tx" + 208) + 24 * j + 16) := by
  have hn : 0 < memW s (locN s "tx" + 216) := by omega
  obtain ⟨S, Nd, hW, hT, hd⟩ := hp.2.2.2.2.2.2.2.2
  have hwords := hT.1.2.2.2.2.2.2.2.2.1 hn
  have hA := hp.1.1.1.1.1.1.1.1.1
  have hu : IvlUnhit s { s with memory := mem }
      (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) :=
    ivlUnhit_single hm (by dsimp; omega)
      (disj_of_inside_right hin (hp.2.2.2.2.2.2.2.1 hn))
  apply memW_eq_of_ivlUnhit hu
  · have ha := hwords.1
    omega
  · exact (ivl_allocated_bound hA.2 (Or.inl (hT.2.2 hn).1)).2
  · constructor <;> dsimp <;> omega

/-- A successful address-copy store preserves the full cumulative-count invariant. -/
theorem phase2_address_count_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxAddressCountInv { s with memory := mem } := by
  apply phase2_address_count_frame s _ hp
    ⟨phase2_address_joint_store hp.1.1 hx hin hm, hp.1.2⟩ rfl rfl rfl
  · exact phase2_address_store_header hp.1.1.1 hin hm 216 (by decide) (by decide)
  · intro j hj
    change memW { s with memory := mem }
      (memW { s with memory := mem } (locN s "tx" + 208) + 24 * j + 16) = _
    rw [phase2_address_store_header hp.1.1.1 hin hm 208 (by decide) (by decide)]
    apply phase2_address_store_key_field hp.1.1.1 hin hm j
    have hi := hp.1.2.2.2
    rw [hp.2.1] at hi
    omega

/-- After adding the current record count, advancing the index restores the
counting invariant. The intervening key assignment changes no input fields. -/
theorem phase2_address_count_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCopyInv s) (hi : locN s "i" < locN s "nal")
    (hn : locN s "nal" = memW s (locN s "tx" + 216))
    (hk : locN s "nkeys" = phase2_key_prefix s (locN s "i" + 1)) :
    PtxAddressCountInv (setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) := by
  obtain ⟨hcopy, hidx⟩ := phase2_address_copy_increment s hp hi
  refine ⟨hcopy, ?_, ?_⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nal" by decide,
      show ofString "i" ≠ ofString "tx" by decide] using hn
  · rw [hidx]
    simpa [phase2_key_prefix, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nkeys" by decide,
      show ofString "i" ≠ ofString "tx" by decide] using hk

/-- Installing the nonwrapping sum establishes the next-prefix equality used
by the subsequent index increment. -/
theorem phase2_address_count_add {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" < locN s "nal") :
    let post := setVarHOLFinite (ofString "nkeys")
      (.val (.word (BitVec.ofNat 64 (locN s "nkeys" +
        memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))))) s
    PtxAddressCopyInv post ∧ locN post "i" < locN post "nal" ∧
      locN post "nal" = memW post (locN post "tx" + 216) ∧
      locN post "nkeys" = phase2_key_prefix post (locN post "i" + 1) := by
  have hb := phase2_address_count_next_bound hp hi
  have hlt : locN s "nkeys" +
      memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) < 2 ^ 64 := by omega
  refine ⟨phase2_address_copy_set_nkeys s hp.1 _, ?_, ?_, ?_⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "i" by decide,
      show ofString "nkeys" ≠ ofString "nal" by decide] using hi
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "nal" by decide,
      show ofString "nkeys" ≠ ofString "tx" by decide] using hp.2.1
  · have he := phase2_key_prefix_succ s (locN s "i")
    rw [← hp.2.2] at he
    simp [phase2_key_prefix, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "nkeys" ≠ ofString "i" by decide,
      show ofString "nkeys" ≠ ofString "tx" by decide,
      BitVec.toNat_ofNat]
    change (locN s "nkeys" + memW s (memW s (locN s "tx" + 208) +
      24 * locN s "i" + 16)) % 2 ^ 64 = phase2_key_prefix s (locN s "i" + 1)
    rw [Nat.mod_eq_of_lt hlt]
    exact he.symm

/-- On normal counting-loop exit the accumulator is the full input key count. -/
theorem phase2_address_count_exit_total {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) (hi : locN s "i" = locN s "nal") :
    locN s "nkeys" = txAccessSlots s (locN s "tx") := by
  rw [hp.2.2, hi, hp.2.1]
  rfl

/-- The actual index assignment closes the next-prefix counting step. -/
theorem phase2_address_count_increment_hoare :
    Hoare (fun s => PtxAddressCopyInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "nal" = memW s (locN s "tx" + 216) ∧
      locN s "nkeys" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i")
        (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxAddressCountInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, hw⟩ := hp.1.2.1
    have hv : v = .val (.word (w + 1)) := by
      simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord,
        valueWord, wordOpHOL, wordOp] using he.symm
    subst v
    have hwN : locN s "i" = w.toNat := by simp [locN, hw]
    have hadd : w + 1 = BitVec.ofNat 64 (locN s "i" + 1) := by
      rw [hwN]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd]
    exact fun _ => phase2_address_count_advance s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  · exact fun _ _ hr => by cases hr

/-- Scratch declarations preserve the strengthened counting invariant. -/
theorem phase2_address_count_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
      "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"] : List String),
      ofString n ≠ name) :
    PtxAddressCountInv (setVarHOLFinite name v s) := by
  apply phase2_address_count_with_locals s _ s.clock hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- The concrete address store retains the strengthened invariant and guard. -/
theorem phase2_address_count_store_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal")
      (.store (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
        (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" < locN s "nal") := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨a, ha⟩ := hp.1.1.1.1.2.1
  obtain ⟨i, hi⟩ := hp.1.1.2.1
  have he : x = a + (i + 1) * 8 := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hi,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using hx.symm
  have hslot := (phase2_address_copy_slot hp.1.1.1 (locN s "i") hp.2).2
  rw [← phase2_address_copy_word_addr hp.1.1 a i ha hi, ← he] at hslot
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec hst
  exact ⟨phase2_address_count_store hp.1 hdom hslot hmem, hp.2⟩

/-- A false machine loop guard identifies the completed natural key count. -/
theorem phase2_address_count_guard_exit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s)
    (hg : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nal"))) = some (.val (.word 0))) :
    locN s "i" = locN s "nal" ∧
      locN s "nkeys" = txAccessSlots s (locN s "tx") := by
  have hi := phase2_address_copy_exit hp.1 hg
  exact ⟨hi, phase2_address_count_exit_total hp hi⟩

/-- Successful scalar record loads expose the natural memory projection. -/
theorem phase2_count_load_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (k : BitVec 64) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString name), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW s (locN s name + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : s.locals.lookup (ofString name) with _ | u
  · simp [hl] at h
  rcases u with ⟨x⟩ | _ | _
  · cases x with
    | word x =>
      simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
      rcases hm : s.memory (x + k) with ⟨y⟩
      refine ⟨y, by rw [← h.2, hm], ?_⟩
      have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by rw [BitVec.add_def]
      simp only [locN, memW, hl, hadd, hm]
  · simp [hl, valueIsWord] at h
  · simp [hl, valueIsWord] at h

/-- Identify the word computed by the concrete key-count addition. -/
theorem phase2_count_add_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (v : ValueHOL 64)
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (he : evalAt s (.op .add [.var .local (ofString "nkeys"),
      .load .one (.op .add [.var .local (ofString "acc"), .const 16])]) = some v) :
    v = .val (.word (BitVec.ofNat 64 (locN s "nkeys" +
      memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)))) := by
  obtain ⟨n, hn⟩ := hp.1.2.2.1
  cases hl : evalAt s (.load .one (.op .add [.var .local (ofString "acc"), .const 16])) with
  | none =>
    unfold evalAt at hl
    simp only [evalHOLExact, evalListHOLExact] at hl
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he
    rw [hl] at he
    simp at he
  | some u =>
    obtain ⟨w, rfl, hw⟩ := phase2_count_load_local s "acc" 16 u hl
    unfold evalAt at hl
    simp only [evalHOLExact, evalListHOLExact] at hl
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he
    rw [hl] at he
    have hv : v = .val (.word (n + w)) := by
      simpa [hn,
        valueIsWord, valueWord, wordOpHOL, wordOp] using he.symm
    rw [hv]
    congr 2
    rw [BitVec.add_def]
    congr 1
    have hnn : locN s "nkeys" = n.toNat := by simp [locN, hn]
    simpa [ha, hnn] using congrArg (fun k => n.toNat + k) hw

/-- The key-count assignment establishes the next-prefix intermediate state. -/
theorem phase2_address_count_nkeys_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.assign .local (ofString "nkeys")
        (.op .add [.var .local (ofString "nkeys"),
          .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
      (fun r s => r = none → PtxAddressCopyInv s ∧ locN s "i" < locN s "nal" ∧
        locN s "nal" = memW s (locN s "tx" + 216) ∧
        locN s "nkeys" = phase2_key_prefix s (locN s "i" + 1)) := by
  apply Hoare.assign
  · intro F s v hp he
    rw [phase2_count_add_eval s hp.1 v hp.2.2 he]
    exact fun _ => phase2_address_count_add s hp.1 hp.2.1
  · exact fun _ _ hr => by cases hr

/-- The two concrete counter assignments restore the strengthened invariant. -/
theorem phase2_address_count_updates_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.seq
        (.assign .local (ofString "nkeys")
          (.op .add [.var .local (ofString "nkeys"),
            .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
        (.assign .local (ofString "i")
          (.op .add [.var .local (ofString "i"), .const 1])))
      (fun r s => r = none → PtxAddressCountInv s) := by
  exact Hoare.seq_fall phase2_address_count_nkeys_hoare
    phase2_address_count_increment_hoare

/-- The current record pointer is a nonwrapping natural address. -/
theorem phase2_address_count_record_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) (hi : locN s "i" < locN s "nal") :
    memW s (locN s "tx" + 208) + 24 * locN s "i" + 24 ≤ 2 ^ 64 := by
  have hn : 0 < memW s (locN s "tx" + 216) := by rw [← hp.2.1]; omega
  obtain ⟨S, Nd, hW, hT, hd, hte⟩ := hp.1.1.2
  have hA := hp.1.1.1.1.1.1.1.1.1.1.1.1
  have hb := (ivl_allocated_bound hA.2 (Or.inl (hT.2.2 hn).1)).2
  rw [hp.2.1] at hi
  dsimp at hb
  omega

/-- The record initializer evaluates to the exact natural record address. -/
theorem phase2_count_acc_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" < locN s "nal")
    (v : ValueHOL 64)
    (he : evalAt s (.op .add
      [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
       .panop .mul [.var .local (ofString "i"), .const 24]]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      w.toNat = memW s (locN s "tx" + 208) + 24 * locN s "i" := by
  obtain ⟨i, hiw⟩ := hp.1.2.1
  cases hl : evalAt s (.load .one (.op .add [.var .local (ofString "tx"), .const 208])) with
  | none =>
    unfold evalAt at hl
    simp only [evalHOLExact, evalListHOLExact] at hl
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he
    rw [hl] at he
    simp at he
  | some u =>
    obtain ⟨a, rfl, ha⟩ := phase2_count_load_local s "tx" 208 u hl
    unfold evalAt at hl
    simp only [evalHOLExact, evalListHOLExact] at hl
    simp only [evalAt, evalHOLExact, evalListHOLExact] at he
    rw [hl] at he
    have hv : v = .val (.word (a + i * 24)) := by
      simpa [hiw, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using he.symm
    refine ⟨a + i * 24, hv, ?_⟩
    have hin : locN s "i" = i.toNat := by simp [locN, hiw]
    have han : a.toNat = memW s (locN s "tx" + 208) := by simpa using ha
    have hb := phase2_address_count_record_bound hp hi
    have hlt : memW s (locN s "tx" + 208) + 24 * locN s "i" < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    rw [show (24 : BitVec 64).toNat = 24 from rfl]
    rw [Nat.add_mod_mod, han, ← hin, Nat.mul_comm (locN s "i") 24]
    exact Nat.mod_eq_of_lt hlt

/-- Address-buffer writes preserve the exact current-record pointer relation. -/
theorem phase2_address_count_store_acc {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountInv s) {x : BitVec 64}
    (hin : Inside (x.toNat, 8) (locN s "al_addrs")
      (locN s "al_addrs" + (locN s "nal" + 1) * 8))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a)
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") :
    locN { s with memory := mem } "acc" =
      memW { s with memory := mem } (locN { s with memory := mem } "tx" + 208) +
        24 * locN { s with memory := mem } "i" := by
  change locN s "acc" = memW { s with memory := mem } (locN s "tx" + 208) +
    24 * locN s "i"
  rw [phase2_address_store_header hp.1.1.1 hin hm 208 (by decide) (by decide)]
  exact ha

/-- Declaring the current record establishes the exact pointer relation. -/
theorem phase2_address_count_declare_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" < locN s "nal")
    (v : ValueHOL 64)
    (he : evalAt s (.op .add
      [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
       .panop .mul [.var .local (ofString "i"), .const 24]]) = some v) :
    let post := setVarHOLFinite (ofString "acc") v s
    PtxAddressCountInv post ∧ locN post "i" < locN post "nal" ∧
      locN post "acc" = memW post (locN post "tx" + 208) + 24 * locN post "i" := by
  obtain ⟨w, rfl, hw⟩ := phase2_count_acc_eval s hp hi v he
  refine ⟨phase2_address_count_set_other s hp _ _ (by decide), ?_, ?_⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide,
      show ofString "acc" ≠ ofString "nal" by decide] using hi
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide,
      show ofString "acc" ≠ ofString "tx" by decide] using hw

/-- Strengthening the counting invariant retains the established loop clock bound. -/
theorem phase2_address_count_loop_bound :
    TerminatingProgBoundedOn PtxAddressCountInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        (.dec (ofString "acc") .one
          (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
            .panop .mul [.var .local (ofString "i"), .const 24]])
          (.seq
            (.store (.op .add [.var .local (ofString "al_addrs"),
              .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
              (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
            (.seq
              (.assign .local (ofString "nkeys")
                (.op .add [.var .local (ofString "nkeys"),
                  .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))))
      (2 ^ 63 + 1) := by
  intro F s hc hp
  exact phase2_address_copy_loop_bound s hc hp.1

/-- The concrete copy store also retains the current-record relation. -/
theorem phase2_address_count_store_record_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.store (.op .add [.var .local (ofString "al_addrs"),
        .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
        (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
        locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  have hlen := phase2_load_one_length s _ v hv
  have hex : ∃ w, flattenHOL v = [w] := by
    cases hs : flattenHOL v with
    | nil => simp [hs] at hlen
    | cons w ws =>
      cases ws with
      | nil => exact ⟨w, rfl⟩
      | cons a rest => simp [hs] at hlen
  obtain ⟨w, hw⟩ := hex
  rw [hw] at hst
  obtain ⟨a, ha⟩ := hp.1.1.1.1.2.1
  obtain ⟨i, hi⟩ := hp.1.1.2.1
  have he : x = a + (i + 1) * 8 := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, ha, hi,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using hx.symm
  have hslot := (phase2_address_copy_slot hp.1.1.1 (locN s "i") hp.2.1).2
  rw [← phase2_address_copy_word_addr hp.1.1 a i ha hi, ← he] at hslot
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec hst
  exact ⟨phase2_address_count_store hp.1 hdom hslot hmem, hp.2.1,
    phase2_address_count_store_acc hp.1 hslot hmem hp.2.2⟩

/-- The address store and both counter updates preserve the cumulative count. -/
theorem phase2_address_count_inner_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.seq
        (.store (.op .add [.var .local (ofString "al_addrs"),
          .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
          (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
        (.seq
          (.assign .local (ofString "nkeys")
            (.op .add [.var .local (ofString "nkeys"),
              .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
          (.assign .local (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r s => r = none → PtxAddressCountInv s) := by
  exact Hoare.seq_fall phase2_address_count_store_record_hoare
    phase2_address_count_updates_hoare

/-- The complete counting/address-copy body preserves the strengthened invariant. -/
theorem phase2_address_count_body_hoare :
    Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal")
      (.dec (ofString "acc") .one
        (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
          .panop .mul [.var .local (ofString "i"), .const 24]])
        (.seq
          (.store (.op .add [.var .local (ofString "al_addrs"),
            .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
            (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
          (.seq
            (.assign .local (ofString "nkeys")
              (.op .add [.var .local (ofString "nkeys"),
                .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
            (.assign .local (ofString "i")
              (.op .add [.var .local (ofString "i"), .const 1])))))
      (fun r s => r = none → PtxAddressCountInv s) := by
  apply Hoare.dec (names := ["i", "nkeys", "al_addrs", "nal", "te", "tx", "index", "sender",
    "mgas", "reservoir", "gas", "tx_blob_gas_used", "price", "enc", "intrinsic"])
    (P' := fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal" ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") (by decide)
  · intro F s v hp he
    exact phase2_address_count_declare_acc s hp.1 hp.2 v he
  · exact phase2_address_count_inner_hoare
  · intro F r s locals hl hp hr
    exact phase2_address_count_with_locals s locals s.clock (hp hr) hl
  · exact fun _ _ hr => by cases hr

/-- Counting-body preservation lifts to the complete guarded loop. -/
theorem phase2_address_count_while_hoare {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxAddressCountInv s ∧ locN s "i" < locN s "nal") body
      (fun r s => r = none → PtxAddressCountInv s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxAddressCountInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" = locN s "nal") := by
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s
    (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxAddressCountInv st →
      evaluateHOLFiniteState st
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) =
          (none, post) → PtxAddressCountInv post ∧ locN post "i" = locN post "nal" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd : PtxAddressCountInv (decClockHOLFinite st) :=
            phase2_address_count_with_locals st st.locals (st.clock - 1) hp (by intros; rfl)
          have hg := phase2_address_copy_guard hp.1 w hw hnz
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨hd, hg⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        have hwz : w = 0 := by simpa using hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, phase2_address_copy_exit hp.1 (by simpa [evalAt, hwz] using hw)⟩
    · simp at he

/-- The key-copy pass retains the completed total while restarting its outer index. -/
theorem phase2_key_pass_reset {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" = locN s "nal") :
    let post := setVarHOLFinite (ofString "i") (.val (.word 0)) s
    PtxAddressCopyInv post ∧
      locN post "nkeys" = txAccessSlots post (locN post "tx") := by
  refine ⟨phase2_address_copy_reset s hp.1, ?_⟩
  have ht := phase2_address_count_exit_total hp hi
  simpa [txAccessSlots, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "i" ≠ ofString "nkeys" by decide,
    show ofString "i" ≠ ofString "tx" by decide] using ht

/-- The concrete address-copy loop retains the cumulative key count at exit. -/
theorem phase2_address_count_loop_hoare :
    Hoare PtxAddressCountInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        (.dec (ofString "acc") .one
          (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
            .panop .mul [.var .local (ofString "i"), .const 24]])
          (.seq
            (.store (.op .add [.var .local (ofString "al_addrs"),
              .panop .mul [.op .add [.var .local (ofString "i"), .const 1], .const 8]])
              (.load .one (.op .add [.var .local (ofString "acc"), .const 0])))
            (.seq
              (.assign .local (ofString "nkeys")
                (.op .add [.var .local (ofString "nkeys"),
                  .load .one (.op .add [.var .local (ofString "acc"), .const 16])]))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))))
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" = locN s "nal") := by
  exact phase2_address_count_while_hoare phase2_address_count_body_hoare
    (by decide) (by decide)

/-- Each packed key record lies inside the rounded key allocation. -/
theorem phase2_key_record_inside (base count k : Nat) (hk : k < count) :
    Inside (base + 52 * k, 52) base
      (base + (count * 52 + 8 + 7) / 8 * 8) := by
  constructor <;> dsimp <;> omega

/-- At counting-loop exit the allocation expression uses the full transaction total. -/
theorem phase2_key_alloc_exit_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" = locN s "nal") :
    ∃ w : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52],
        .const 8]) = some (.val (.word w)) ∧
      w.toNat = txAccessSlots s (locN s "tx") * 52 + 8 ∧
      ∀ base k, k < txAccessSlots s (locN s "tx") →
        Inside (base + 52 * k, 52) base (base + (w.toNat + 7) / 8 * 8) := by
  obtain ⟨w, he, hw, _⟩ := phase2_address_count_alloc_size s hp
  have ht := phase2_address_count_exit_total hp hi
  rw [ht] at hw
  refine ⟨w, he, hw, ?_⟩
  intro base k hk
  rw [hw]
  exact phase2_key_record_inside base _ k hk

/-- The storage-key byte allocation evaluates without machine-word wraparound. -/
theorem phase2_storage_keys_alloc_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) :
    ∃ w : BitVec 64,
      evalAt s (.panop .mul [.var .local (ofString "nkeys"), .const 32]) =
        some (.val (.word w)) ∧
      w.toNat = locN s "nkeys" * 32 ∧
      (w.toNat + 7) / 8 * 8 = locN s "nkeys" * 32 := by
  obtain ⟨n, hn⟩ := hp.1.2.2.1
  have hb := phase2_address_count_alloc_bound hp
  have hnN : locN s "nkeys" = n.toNat := by simp [locN, hn]
  have hlt : n.toNat * 32 < 2 ^ 64 := by rw [hnN] at hb; omega
  refine ⟨n * 32, ?_, ?_, ?_⟩
  · simp [evalAt, evalHOLExact, evalListHOLExact, hn, valueIsWord, valueWord,
      panOpHOL]
  · change n.toNat * 32 % 2 ^ 64 = locN s "nkeys" * 32
    rw [Nat.mod_eq_of_lt hlt, hnN]
  · simp only [BitVec.toNat_mul]
    change (n.toNat * 32 % 2 ^ 64 + 7) / 8 * 8 = locN s "nkeys" * 32
    rw [Nat.mod_eq_of_lt hlt, hnN]
    omega

/-- The storage-key allocation covers each complete 32-byte copy at loop exit. -/
theorem phase2_storage_keys_exit_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s) (hi : locN s "i" = locN s "nal") :
    ∃ w : BitVec 64,
      evalAt s (.panop .mul [.var .local (ofString "nkeys"), .const 32]) =
        some (.val (.word w)) ∧
      w.toNat = txAccessSlots s (locN s "tx") * 32 ∧
      ∀ base k, k < txAccessSlots s (locN s "tx") →
        Inside (base + 32 * k, 32) base (base + (w.toNat + 7) / 8 * 8) := by
  obtain ⟨w, he, hw, hr⟩ := phase2_storage_keys_alloc_size s hp
  have ht := phase2_address_count_exit_total hp hi
  rw [ht] at hw hr
  refine ⟨w, he, hw, ?_⟩
  intro base k hk
  rw [hr]
  constructor <;> dsimp <;> omega

/-- An inner-loop key index, offset by its record prefix, is below the total. -/
theorem phase2_key_copy_index_lt_total {F : Type} (s : PanSemStateFiniteExact 64 F)
    {i j : Nat} (hi : i < memW s (locN s "tx" + 216))
    (hj : j < memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    phase2_key_prefix s i + j < txAccessSlots s (locN s "tx") := by
  have hp := phase2_key_prefix_le_total s (i := i + 1) (by omega)
  rw [phase2_key_prefix_succ] at hp
  omega

/-- Both concrete memcpy destinations fit in the packed key allocation. -/
theorem phase2_key_copy_destinations (base count k : Nat) (hk : k < count) :
    Inside (base + 52 * k, 20) base
      (base + (count * 52 + 8 + 7) / 8 * 8) ∧
    Inside (base + 52 * k + 20, 32) base
      (base + (count * 52 + 8 + 7) / 8 * 8) := by
  obtain ⟨hl, hu⟩ := phase2_key_record_inside base count k hk
  dsimp at hl hu
  constructor <;> constructor <;> dsimp <;> omega

/-- The storage-key allocator returns the full nonwrapping byte buffer. -/
theorem phase2_storage_keys_alloc_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : PtxAddressCountInv s)
    (ha : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.var .local (ofString "nkeys"), .const 32]] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hb : (callEntryStateHOLFinite s callee).evaluateHOLFiniteState body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat (locN s "nkeys" * 32) := by
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_storage_keys_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 32 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hready.1.1.1.1.1.1.1.1)
    (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, hv, _, _, hf⟩ := hr v rfl
  exact ⟨w, hv, by simpa only [hcn] using hf⟩

/-- Every storage-key destination stays below the fresh allocation's heap frontier. -/
theorem phase2_storage_keys_fresh_slot {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {base count k : Nat}
    (hf : FreshBlock s post base (count * 32)) (hk : k < count) :
    Inside (base + 32 * k, 32) (globN s "heap_ptr") (globN post "heap_ptr") := by
  obtain ⟨_, hlo, _⟩ := hf
  rcases hlo with ⟨hl, hu⟩
  dsimp at hl hu
  constructor <;> dsimp <;> omega

/-- Caller restoration retains the complete live storage-key buffer. -/
theorem phase2_storage_keys_alloc_live (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s =>
        (∃ w : BitVec 64, s.locals.lookup (ofString "storage_keys") = some (.val (.word w))) ∧
        Inside (locN s "storage_keys", locN s "nkeys" * 32)
          InitE.sourceBase (globN s "heap_ptr") ∧
        locN s "storage_keys" % 8 = 0 ∧
        WordsOK s (locN s "storage_keys", locN s "nkeys" * 32))
      (ofString "storage_keys") (ofString "alloc")
      [.panop .mul [.var .local (ofString "nkeys"), .const 32]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_storage_keys_alloc_fresh h s vs body callee ret v post
    hc hp ha hl hb
  have hround : (locN s "nkeys" * 32 + 7) / 8 * 8 = locN s "nkeys" * 32 := by omega
  simp only [FreshBlock, hround] at hf
  let out := setVarHOLFinite (ofString "storage_keys") (.val (.word w))
    { post with locals := s.locals }
  have hptr : locN out "storage_keys" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nkeys" = locN s "nkeys" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "storage_keys" ≠ ofString "nkeys" by decide]
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  refine ⟨⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ?_, ?_, ?_⟩
  · change Inside (locN out "storage_keys", locN out "nkeys" * 32)
      InitE.sourceBase (globN post "heap_ptr")
    rw [hptr, hcount]
    exact ⟨hready.1.1.1.1.1.1.1.1.2.1.trans hf.2.1.1, hf.2.1.2⟩
  · change locN out "storage_keys" % 8 = 0
    rw [hptr]
    exact hf.1
  · change WordsOK post (locN out "storage_keys", locN out "nkeys" * 32)
    rw [hptr, hcount]
    exact hf.2.2

/-- A live storage-key buffer supplies the four words required by each key copy. -/
theorem phase2_storage_keys_slot_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base count k : Nat} (hw : WordsOK s (base, count * 32)) (hk : k < count) :
    WordsOK s (base + 32 * k, 32) := by
  rcases hw with ⟨hal, _, hw⟩
  refine ⟨by dsimp; omega, by simp, ?_⟩
  intro j hj
  have h := hw (4 * k + j) (by dsimp at hj ⊢; omega)
  convert h using 1 <;> dsimp <;> omega

/-- Fresh storage-key memory is disjoint from the existing address array. -/
theorem phase2_storage_keys_address_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (base : Nat)
    (hp : PtxAddressCountInv s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post base (locN s "nkeys" * 32)) :
    Disj (locN s "al_addrs", (locN s "nal" + 1) * 8)
      (base, locN s "nkeys" * 32) := by
  have hready : PtxAddressReady s := hp.1.1.1
  have hstart : globN s "heap_ptr" ≤ base := hf.2.1.1
  exact Or.inr (Or.inr (Or.inl (hready.2.2.1.2.trans hstart)))

/-- Fresh storage-key memory cannot overlap the live transaction inputs. -/
theorem phase2_storage_keys_input_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (base : Nat)
    (hp : PtxAddressCountInv s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post base (locN s "nkeys" * 32)) :
    Disj (locN s "te", 200) (base, locN s "nkeys" * 32) ∧
    Disj (locN s "tx", 384) (base, locN s "nkeys" * 32) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (base, locN s "nkeys" * 32)) := by
  exact phase2_fresh_separation s post callee base _ hp.1.1.1.1 hf

/-- Separation of the storage-key buffer applies to each individual copy destination. -/
theorem phase2_storage_keys_slot_disjoint {base count k : Nat} {input : Ivl}
    (hd : Disj input (base, count * 32)) (hk : k < count) :
    Disj input (base + 32 * k, 32) := by
  rcases hd with hz | hz | hleft | hright
  · exact Or.inl hz
  · dsimp at hz
    omega
  · exact Or.inr (Or.inr (Or.inl (by dsimp at hleft ⊢; omega)))
  · exact Or.inr (Or.inr (Or.inr (by dsimp at hright ⊢; omega)))

/-- A bounded packed-key destination has a nonwrapping machine address. -/
theorem phase2_key_destination_nonwrapping (base count k : Nat) (hk : k < count)
    (hb : base + (count * 52 + 8 + 7) / 8 * 8 ≤ 2 ^ 64) :
    (BitVec.ofNat 64 (base + 52 * k)).toNat = base + 52 * k ∧
    (BitVec.ofNat 64 (base + 52 * k + 20)).toNat = base + 52 * k + 20 := by
  obtain ⟨_, hu⟩ := phase2_key_record_inside base count k hk
  dsimp at hu
  constructor <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Storage-key allocation retains a joint world and transaction witness. -/
theorem phase2_storage_keys_alloc_world (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "storage_keys", locN s "nkeys" * 32)] (worldOwned s S Nd))
      (ofString "storage_keys") (ofString "alloc")
      [.panop .mul [.var .local (ofString "nkeys"), .const 32]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_storage_keys_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 32 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hready.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, _⟩ := hready.1.2
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hready.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨w, rfl, hav⟩ := hret v rfl
  dsimp only at hav
  rw [hcn] at hav
  have hround : (locN s "nkeys" * 32 + 7) / 8 * 8 = locN s "nkeys" * 32 := by omega
  rw [hround] at hav
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
  · have ht := R16Shards.PtxP1.txAccessListAt_with_locals post
      (setVarHOLFinite (ofString "storage_keys") (.val (.word w)) { post with locals := s.locals }).locals
      post.clock hTp
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "storage_keys" ≠ ofString "tx" by decide] using ht
  · change IvlsDisj [(locN (setVarHOLFinite (ofString "storage_keys") (.val (.word w))
        { post with locals := s.locals }) "storage_keys",
        locN (setVarHOLFinite (ofString "storage_keys") (.val (.word w))
          { post with locals := s.locals }) "nkeys" * 32)] (worldOwned post S' Nd')
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "storage_keys" ≠ ofString "nkeys" by decide] using hav

/-- Copy calls preserving the memory domain retain validity of every key destination. -/
theorem phase2_storage_keys_words_frame {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {base count : Nat}
    (hw : WordsOK s (base, count * 32))
    (hd : ∀ a, s.memaddrs a → post.memaddrs a) :
    WordsOK post (base, count * 32) := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  intro k hk
  obtain ⟨w, ha, _⟩ := hw.2.2 k hk
  cases hm : post.memory (BitVec.ofNat 64 (base + 8 * k)) with
  | word v => exact ⟨v, hd _ ha, hm⟩

/-- The concrete 52-byte packed-record allocation returns the entire requested buffer. -/
theorem phase2_packed_keys_alloc_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : PtxAddressCountInv s)
    (ha : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hb : (callEntryStateHOLFinite s callee).evaluateHOLFiniteState body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat (locN s "nkeys" * 52 + 8) := by
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_address_count_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hready.1.1.1.1.1.1.1.1)
    (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, hv, _, _, hf⟩ := hr v rfl
  exact ⟨w, hv, by simpa only [hcn] using hf⟩

/-- Storage allocation simultaneously provides writable memory and world separation. -/
theorem phase2_storage_keys_alloc_ready (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s =>
        WordsOK s (locN s "storage_keys", locN s "nkeys" * 32) ∧
        Inside (locN s "storage_keys", locN s "nkeys" * 32)
          InitE.sourceBase (globN s "heap_ptr") ∧
        ∃ S Nd, WorldTypedWith s S Nd ∧
          TxAccessListAt s S Nd (locN s "tx") ∧
          IvlsDisj [(locN s "storage_keys", locN s "nkeys" * 32)] (worldOwned s S Nd))
      (ofString "storage_keys") (ofString "alloc")
      [.panop .mul [.var .local (ofString "nkeys"), .const 32]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hlive := phase2_storage_keys_alloc_live h s vs body callee ret v post hc hp ha hl hb
  have hworld := phase2_storage_keys_alloc_world h s vs body callee ret v post hc hp ha hl hb
  exact ⟨hlive.2.2.2, hlive.2.1, hworld⟩

/-- A completed record's inner pass advances the flattened index to the next prefix. -/
theorem phase2_key_copy_record_done {F : Type} (s : PanSemStateFiniteExact 64 F)
    (i j k : Nat)
    (hk : k = phase2_key_prefix s i + j)
    (hj : j = memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    k = phase2_key_prefix s (i + 1) := by
  rw [phase2_key_prefix_succ, hk, hj]

/-- Incrementing both copy indices retains their prefix relation. -/
theorem phase2_key_copy_index_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (i j k : Nat) (hk : k = phase2_key_prefix s i + j) :
    k + 1 = phase2_key_prefix s i + (j + 1) := by
  omega

/-- At outer-loop exit, the flattened copy index equals the allocated key count. -/
theorem phase2_key_copy_exit_count {F : Type} (s : PanSemStateFiniteExact 64 F)
    (i k : Nat) (hi : i = memW s (locN s "tx" + 216))
    (hk : k = phase2_key_prefix s i)
    (hn : locN s "nkeys" = txAccessSlots s (locN s "tx")) :
    k = locN s "nkeys" := by
  rw [hk, hi, hn]
  rfl

/-- The actual packed-key pointer retains its rounded live extent after return. -/
theorem phase2_packed_keys_alloc_live (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s =>
        (∃ w : BitVec 64, s.locals.lookup (ofString "al_keys") = some (.val (.word w))) ∧
        Inside (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
          InitE.sourceBase (globN s "heap_ptr") ∧
        locN s "al_keys" % 8 = 0 ∧
        WordsOK s (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_packed_keys_alloc_fresh h s vs body callee ret v post
    hc hp ha hl hb
  let out := setVarHOLFinite (ofString "al_keys") (.val (.word w))
    { post with locals := s.locals }
  have hptr : locN out "al_keys" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nkeys" = locN s "nkeys" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide]
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  refine ⟨⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ?_, ?_, ?_⟩
  · change Inside (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
      InitE.sourceBase (globN post "heap_ptr")
    rw [hptr, hcount]
    exact ⟨hready.1.1.1.1.1.1.1.1.2.1.trans hf.2.1.1, hf.2.1.2⟩
  · change locN out "al_keys" % 8 = 0
    rw [hptr]
    exact hf.1
  · change WordsOK post (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
    rw [hptr, hcount]
    exact hf.2.2

/-- Even unaligned packed-record bytes have valid containing word cells. -/
theorem phase2_packed_key_byte_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base count k offset : Nat}
    (hw : WordsOK s (base, (count * 52 + 8 + 7) / 8 * 8))
    (hk : k < count) (ho : offset < 52) :
    WordAt s ((base + 52 * k + offset) / 8 * 8) := by
  have hal := hw.1
  have hidx : (52 * k + offset) / 8 < ((count * 52 + 8 + 7) / 8 * 8) / 8 := by
    omega
  have hword := hw.2.2 ((52 * k + offset) / 8) hidx
  have heq : (base + 52 * k + offset) / 8 * 8 =
      base + 8 * ((52 * k + offset) / 8) := by
    dsimp at hal
    omega
  rw [heq]
  exact hword

/-- The concrete packed allocation shares a world witness with the input transaction. -/
theorem phase2_packed_keys_alloc_world_joint (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
          (worldOwned s S Nd))
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_address_count_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hready.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, _⟩ := hready.1.2
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hready.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨w, rfl, hav⟩ := hret v rfl
  dsimp only at hav
  rw [hcn] at hav
  let out := setVarHOLFinite (ofString "al_keys") (.val (.word w)) { post with locals := s.locals }
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
  · have ht := R16Shards.PtxP1.txAccessListAt_with_locals post out.locals post.clock hTp
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "tx" by decide] using ht
  · change IvlsDisj [(locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned post S' Nd')
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide] using hav

/-- Packed-key allocation preserves a shared world/access-list witness. -/
theorem phase2_packed_keys_alloc_world (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s => ∃ S Nd, WorldTypedWith s S Nd ∧
        TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
          (worldOwned s S Nd))
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_address_count_alloc_size s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hready.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, _⟩ := hready.1.2
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hready.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨w, rfl, hav⟩ := hret v rfl
  dsimp only at hav
  rw [hcn] at hav
  refine ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
  · have ht := R16Shards.PtxP1.txAccessListAt_with_locals post
      (setVarHOLFinite (ofString "al_keys") (.val (.word w)) { post with locals := s.locals }).locals
      post.clock hTp
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "tx" by decide] using ht
  · change IvlsDisj [(locN (setVarHOLFinite (ofString "al_keys") (.val (.word w))
        { post with locals := s.locals }) "al_keys",
        (locN (setVarHOLFinite (ofString "al_keys") (.val (.word w))
          { post with locals := s.locals }) "nkeys" * 52 + 8 + 7) / 8 * 8)] (worldOwned post S' Nd')
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide] using hav

/-- Both memcpy ranges in a packed key record have valid backing word cells. -/
theorem phase2_packed_copy_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base count k : Nat}
    (hw : WordsOK s (base, (count * 52 + 8 + 7) / 8 * 8)) (hk : k < count) :
    (∀ j, j < 20 → WordAt s ((base + 52 * k + j) / 8 * 8)) ∧
    (∀ j, j < 32 → WordAt s ((base + 52 * k + 20 + j) / 8 * 8)) := by
  constructor
  · intro j hj
    exact phase2_packed_key_byte_word hw hk (by omega)
  · intro j hj
    have h := phase2_packed_key_byte_word hw hk (offset := 20 + j) (by omega)
    simpa only [Nat.add_assoc] using h

/-- Packed allocation combines live backing memory with a shared input/world witness. -/
def PtxPackedKeysReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ w : BitVec 64, s.locals.lookup (ofString "al_keys") = some (.val (.word w))) ∧
  Inside (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
    InitE.sourceBase (globN s "heap_ptr") ∧
  locN s "al_keys" % 8 = 0 ∧
  WordsOK s (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd)

theorem phase2_packed_keys_alloc_ready (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv PtxPackedKeysReady
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hlive := phase2_packed_keys_alloc_live h s vs body callee ret v post hc hp ha hl hb
  have hw := phase2_packed_keys_alloc_world h s vs body callee ret v post hc hp ha hl hb
  exact ⟨hlive.1, hlive.2.1, hlive.2.2.1, hlive.2.2.2, hw⟩

/-- The concrete allocation composes with any continuation on packed-buffer readiness. -/
theorem phase2_packed_keys_alloc_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxPackedKeysReady tail b) :
    TerminatingProgBoundedOn PtxAddressCountInv
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxPackedKeysReady) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hready : PtxAccessCountReady s := hp.1.1.1.1
    exact guestInv_callEntry s callee hready.1.1.1.1.1.1.1.1.1
  · exact phase2_packed_keys_alloc_ready h
  · exact ht

/-- Framing the access-record key counts preserves the nested copy-index relation. -/
theorem phase2_key_copy_index_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (i j k : Nat)
    (hk : k = phase2_key_prefix s i + j)
    (hm : ∀ n, n < i →
      memW post (memW post (locN post "tx" + 208) + 24 * n + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * n + 16)) :
    k = phase2_key_prefix post i + j := by
  rw [phase2_key_prefix_congr s post i hm]
  exact hk

/-- The entire rounded packed allocation is separate from the live address array. -/
theorem phase2_packed_keys_address_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (base : Nat)
    (hp : PtxAddressCountInv s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post base (locN s "nkeys" * 52 + 8)) :
    Disj (locN s "al_addrs", (locN s "nal" + 1) * 8)
      (base, (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) := by
  have hready : PtxAddressReady s := hp.1.1.1
  have hstart : globN s "heap_ptr" ≤ base := hf.2.1.1
  exact Or.inr (Or.inr (Or.inl (hready.2.2.1.2.trans hstart)))

/-- Packed-buffer readiness depends only on its pointer, count and transaction locals. -/
theorem phase2_packed_keys_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hp : PtxPackedKeysReady s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedKeysReady { s with locals := locals, clock := clock } := by
  have ha : locN { s with locals := locals, clock := clock } "al_keys" = locN s "al_keys" := by
    simp [locN, hl "al_keys" (by simp)]
  have hn : locN { s with locals := locals, clock := clock } "nkeys" = locN s "nkeys" := by
    simp [locN, hl "nkeys" (by simp)]
  have ht : locN { s with locals := locals, clock := clock } "tx" = locN s "tx" := by
    simp [locN, hl "tx" (by simp)]
  obtain ⟨hs, hi, hal, hw, S, Nd, hW, hT, hd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, S, Nd, ?_, ?_, ?_⟩
  · simpa only [hl "al_keys" (by simp)] using hs
  · rw [ha, hn]; exact hi
  · rw [ha]; exact hal
  · rw [ha, hn]; exact hw
  · exact (worldTypedWith_with_locals s locals clock S Nd).mpr hW
  · rw [ht]
    exact R16Shards.PtxP1.txAccessListAt_with_locals s locals clock hT
  · rw [ha, hn]; exact hd

/-- Loop-counter declarations preserve the packed allocation facts. -/
theorem phase2_packed_keys_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedKeysReady s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String), ofString n ≠ name) :
    PtxPackedKeysReady (setVarHOLFinite name v s) := by
  apply phase2_packed_keys_with_locals s _ s.clock hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- Resetting the flattened copy index preserves the packed buffer and starts at prefix zero. -/
theorem phase2_packed_keys_copy_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedKeysReady s) :
    let post := setVarHOLFinite (ofString "k") (.val (.word 0)) s
    PtxPackedKeysReady post ∧ locN post "k" = phase2_key_prefix post 0 := by
  refine ⟨phase2_packed_keys_set_other s hp _ _ (by decide), ?_⟩
  simp [locN, phase2_key_prefix, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The inner copy pass relates its flattened index to the current record prefix. -/
def PtxPackedCopyIndex {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedKeysReady s ∧
  locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
  locN s "i" < memW s (locN s "tx" + 216) ∧
  locN s "j" < memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) ∧
  locN s "k" = phase2_key_prefix s (locN s "i") + locN s "j"

/-- A guarded inner iteration addresses an allocated packed record. -/
theorem phase2_packed_copy_index_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) : locN s "k" < locN s "nkeys" := by
  rw [hp.2.2.2.2, hp.2.1]
  exact phase2_key_copy_index_lt_total s hp.2.2.1 hp.2.2.2.1

/-- Both concrete copy destinations have backing words under the inner-loop invariant. -/
theorem phase2_packed_copy_index_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    (∀ j, j < 20 → WordAt s ((locN s "al_keys" + 52 * locN s "k" + j) / 8 * 8)) ∧
    (∀ j, j < 32 → WordAt s ((locN s "al_keys" + 52 * locN s "k" + 20 + j) / 8 * 8)) := by
  exact phase2_packed_copy_words hp.1.2.2.2.1 (phase2_packed_copy_index_bound hp)

/-- Both concrete copy ranges lie inside the packed buffer under the same invariant. -/
theorem phase2_packed_copy_index_destinations {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    Inside (locN s "al_keys" + 52 * locN s "k", 20) (locN s "al_keys")
      (locN s "al_keys" + (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    Inside (locN s "al_keys" + 52 * locN s "k" + 20, 32) (locN s "al_keys")
      (locN s "al_keys" + (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) := by
  exact phase2_key_copy_destinations _ _ _ (phase2_packed_copy_index_bound hp)

/-- The nested copy indices identify a valid allocated record under both guards. -/
theorem phase2_packed_copy_guard_bound {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hn : locN s "nkeys" = txAccessSlots s (locN s "tx"))
    (hk : locN s "k" = phase2_key_prefix s (locN s "i") + locN s "j")
    (hi : locN s "i" < memW s (locN s "tx" + 216))
    (hj : locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN s "k" < locN s "nkeys" := by
  rw [hn, hk]
  exact phase2_key_copy_index_lt_total s hi hj

/-- Rounded packed-key memory remains above all existing transaction inputs. -/
theorem phase2_packed_keys_input_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (base : Nat)
    (hp : PtxAddressCountInv s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post base (locN s "nkeys" * 52 + 8)) :
    let size := (locN s "nkeys" * 52 + 8 + 7) / 8 * 8
    Disj (locN s "te", 200) (base, size) ∧
    Disj (locN s "tx", 384) (base, size) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (base, size)) := by
  have hr : PtxAccessCountReady s := hp.1.1.1.1
  have hstart : globN s "heap_ptr" ≤ base := hf.2.1.1
  obtain ⟨S, Nd, _, ht, _⟩ := hr.1.2
  refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr (Or.inr (Or.inl ?_)), ?_⟩
  · exact hr.1.1.2.2.1.2.trans hstart
  · exact ht.1.2.1.2.trans hstart
  · intro hn
    exact Or.inr (Or.inr (Or.inl ((ht.2.2 hn).1.2.trans hstart)))

/-- Both inner counters can be incremented without wrapping a machine word. -/
theorem phase2_packed_copy_counter_bounds {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    locN s "k" + 1 < 2 ^ 64 ∧ locN s "j" + 1 < 2 ^ 64 := by
  obtain ⟨S, Nd, _, hT, _⟩ := hp.1.2.2.2.2
  have ht : txAccessSlots s (locN s "tx") < 2 ^ 32 := hT.1.2.2.2.2.2.1
  have hk := phase2_packed_copy_index_bound hp
  have hn := hp.2.1
  have hj := hp.2.2.2.2
  constructor <;> omega

/-- The concrete counter words agree with the natural successor indices. -/
theorem phase2_packed_copy_counter_successors {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    (BitVec.ofNat 64 (locN s "k") + 1).toNat = locN s "k" + 1 ∧
    (BitVec.ofNat 64 (locN s "j") + 1).toNat = locN s "j" + 1 := by
  obtain ⟨hk, hj⟩ := phase2_packed_copy_counter_bounds hp
  constructor
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (locN s "k" % 2 ^ 64 + 1) % 2 ^ 64 = locN s "k" + 1
    rw [Nat.mod_eq_of_lt (show locN s "k" < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    change (locN s "j" % 2 ^ 64 + 1) % 2 ^ 64 = locN s "j" + 1
    rw [Nat.mod_eq_of_lt (show locN s "j" < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj]

/-- The flattened copy counter remains below the signed-comparison boundary. -/
theorem phase2_packed_copy_counter_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) : locN s "k" + 1 < 2 ^ 63 := by
  have hk := phase2_packed_copy_index_bound hp
  obtain ⟨S, Nd, _, ht, _⟩ := hp.1.2.2.2.2
  have hn : txAccessSlots s (locN s "tx") < 2 ^ 32 := ht.1.2.2.2.2.2.1
  rw [hp.2.1] at hk
  omega

/-- World-owned objects are separate from both writes of a guarded packed copy. -/
theorem phase2_packed_copy_world_destinations {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      ∀ input ∈ worldOwned s S Nd,
        Disj input (locN s "al_keys" + 52 * locN s "k", 20) ∧
        Disj input (locN s "al_keys" + 52 * locN s "k" + 20, 32) := by
  obtain ⟨S, Nd, hW, hT, hd⟩ := hp.1.2.2.2.2
  refine ⟨S, Nd, hW, hT, ?_⟩
  intro input hin
  have hsep := hd (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
    (by simp) input hin
  have hr := phase2_packed_copy_index_destinations hp
  exact ⟨disj_of_inside_right hr.1 (disj_symm hsep),
    disj_of_inside_right hr.2 (disj_symm hsep)⟩

/-- Backing cells touched by packed copies remain inside the rounded allocation. -/
theorem phase2_packed_copy_cell_inside (base count k offset : Nat)
    (hal : base % 8 = 0) (hk : k < count) (ho : offset < 52) :
    Inside ((base + 52 * k + offset) / 8 * 8, 8) base
      (base + (count * 52 + 8 + 7) / 8 * 8) := by
  constructor <;> dsimp <;> omega

/-- Copying bytes cannot invalidate packed-buffer backing words when the domain is retained. -/
theorem phase2_packed_keys_words_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (base count : Nat)
    (hw : WordsOK s (base, (count * 52 + 8 + 7) / 8 * 8))
    (hd : ∀ a, s.memaddrs a → post.memaddrs a) :
    WordsOK post (base, (count * 52 + 8 + 7) / 8 * 8) := by
  refine ⟨hw.1, hw.2.1, ?_⟩
  intro k hk
  obtain ⟨w, ha, _⟩ := hw.2.2 k hk
  cases hm : post.memory (BitVec.ofNat 64 (base + 8 * k)) with
  | word v => exact ⟨v, hd _ ha, hm⟩

/-- Successful evaluation of a bounded scalar increment gives its exact natural successor. -/
theorem phase2_copy_increment_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String) (v : ValueHOL 64) (hb : locN s name + 1 < 2 ^ 64)
    (he : evalAt s (.op .add [.var .local (ofString name), .const 1]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = locN s name + 1 := by
  cases hl : s.locals.lookup (ofString name) with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl] at he
  | some u =>
    rcases u with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · have hv : v = .val (.word (w + 1)) := by
        simpa [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord, valueWord,
          wordOpHOL, wordOp] using he.symm
      refine ⟨w + 1, hv, ?_⟩
      have hn : locN s name = w.toNat := by simp [locN, hl]
      rw [hn] at hb ⊢
      change (w.toNat + 1) % 2 ^ 64 = w.toNat + 1
      exact Nat.mod_eq_of_lt hb
    · simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord] at he
    · simp [evalAt, evalHOLExact, evalListHOLExact, hl, valueIsWord] at he

/-- The flattened-counter assignment retains the packed allocation facts. -/
theorem phase2_packed_copy_increment_k_hoare :
    Hoare PtxPackedCopyIndex
      (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
      (fun r s => r = none → PtxPackedKeysReady s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v
      (phase2_packed_copy_counter_bounds hp).1 he
    exact fun _ => phase2_packed_keys_set_other s hp.1 _ _ (by decide)
  · exact fun _ _ hr => by cases hr

/-- Even the full backing cells of unaligned packed writes avoid world-owned objects. -/
theorem phase2_packed_copy_world_cells {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      ∀ input ∈ worldOwned s S Nd, ∀ offset, offset < 52 →
        Disj input ((locN s "al_keys" + 52 * locN s "k" + offset) / 8 * 8, 8) := by
  obtain ⟨S, Nd, hW, hT, hd⟩ := hp.1.2.2.2.2
  refine ⟨S, Nd, hW, hT, ?_⟩
  intro input hin offset ho
  have hsep := hd (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
    (by simp) input hin
  exact disj_of_inside_right
    (phase2_packed_copy_cell_inside _ _ _ offset hp.1.2.2.1
      (phase2_packed_copy_index_bound hp) ho) (disj_symm hsep)

/-- Copy effects that preserve transaction counts retain the guarded index relation. -/
theorem phase2_packed_copy_index_preserved {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["nkeys", "i", "j", "k"] : List String), locN post n = locN s n)
    (ht : txAccessSlots post (locN post "tx") = txAccessSlots s (locN s "tx"))
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
      memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex post := by
  have hi := hl "i" (by simp)
  have hj := hl "j" (by simp)
  have hk := hl "k" (by simp)
  have hn := hl "nkeys" (by simp)
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · rw [hn, ht]; exact hp.2.1
  · rw [hi, hc]; exact hp.2.2.1
  · rw [hj, hi, hm]; exact hp.2.2.2.1
  · rw [hk, hi, hj]
    have he := phase2_key_prefix_congr s post (locN s "i") (fun i _ => hm i)
    rw [he]
    exact hp.2.2.2.2

/-- Updating both inner counters retains their exact flattened-prefix relation. -/
theorem phase2_packed_copy_update_indices {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) :
    let post := setVarHOLFinite (ofString "j")
      (.val (.word (BitVec.ofNat 64 (locN s "j" + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) s)
    PtxPackedKeysReady post ∧
      locN post "k" = phase2_key_prefix post (locN post "i") + locN post "j" := by
  dsimp only
  have hready := phase2_packed_keys_set_other s hp.1 (ofString "k")
    (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) (by decide)
  refine ⟨phase2_packed_keys_set_other _ hready (ofString "j") _ (by decide), ?_⟩
  obtain ⟨hk, hj⟩ := phase2_packed_copy_counter_bounds hp
  have hrel := hp.2.2.2.2
  change locN s "k" + 1 < 18446744073709551616 at hk
  change locN s "j" + 1 < 18446744073709551616 at hj
  simp only [locN] at hk hj
  simpa [phase2_key_prefix, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "j" ≠ ofString "k" by decide,
    show ofString "j" ≠ ofString "i" by decide,
    show ofString "k" ≠ ofString "i" by decide,
    show ofString "j" ≠ ofString "tx" by decide,
    show ofString "k" ≠ ofString "tx" by decide,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hj, Nat.add_assoc]
    using (show locN s "k" + 1 = phase2_key_prefix s (locN s "i") + (locN s "j" + 1) by omega)

/-- The next inner index stays within the current record's key count. -/
theorem phase2_packed_copy_next_inner_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) :
    locN s "j" + 1 ≤ memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) ∧
    locN s "k" + 1 ≤ locN s "nkeys" := by
  have hj := hp.2.2.2.1
  have hk := phase2_packed_copy_index_bound hp
  omega

/-- A concrete bounded counter assignment preserves readiness and exposes its exact value. -/
theorem phase2_packed_counter_assign (name : String) (old : Nat)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String), ofString n ≠ ofString name)
    (hb : old + 1 < 2 ^ 64) :
    Hoare (fun s => PtxPackedKeysReady s ∧ locN s name = old)
      (.assign .local (ofString name) (.op .add [.var .local (ofString name), .const 1]))
      (fun r s => r = none → PtxPackedKeysReady s ∧ locN s name = old + 1) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s name v (by rw [hp.2]; exact hb) he
    intro _
    refine ⟨phase2_packed_keys_set_other s hp.1 _ _ hne, ?_⟩
    simpa [locN, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      using hw.trans (by rw [hp.2])
  · exact fun _ _ hr => by cases hr

/-- The concrete paired counter sequence preserves packed-buffer readiness. -/
theorem phase2_packed_counter_sequence :
    Hoare PtxPackedKeysReady
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedKeysReady s) := by
  apply Hoare.seq_fall
  · apply Hoare.assign
    · intro F s v hp he
      exact fun _ => phase2_packed_keys_set_other s hp _ _ (by decide)
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      exact fun _ => phase2_packed_keys_set_other s hp _ _ (by decide)
    · exact fun _ _ hr => by cases hr

/-- Restoring unchanged copy locals preserves the guarded copy predicate. -/
theorem phase2_packed_copy_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hp : PtxPackedCopyIndex s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedCopyIndex { s with locals := locals, clock := clock } := by
  have ht : locN { s with locals := locals, clock := clock } "tx" = locN s "tx" := by
    simp [locN, hl "tx" (by simp)]
  apply phase2_packed_copy_index_preserved s _ hp
  · apply phase2_packed_keys_with_locals s locals clock hp.1
    intro n hn
    exact hl n (by simp at hn ⊢; tauto)
  · intro n hn
    have he := hl n (by simp only [List.mem_cons, List.mem_singleton] at hn ⊢; tauto)
    simp [locN, he]
  · rw [ht]; rfl
  · rw [ht]; rfl
  · intro i; rw [ht]; rfl

/-- Scratch declarations around copy calls preserve the guarded index predicate. -/
theorem phase2_packed_copy_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      ofString n ≠ name) :
    PtxPackedCopyIndex (setVarHOLFinite name v s) := by
  apply phase2_packed_copy_with_locals s _ s.clock hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- A scratch assignment preserves all guarded packed-copy facts. -/
theorem phase2_packed_copy_scratch_hoare (name : MlS) (e : ExpHOL 64)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      ofString n ≠ name) :
    Hoare PtxPackedCopyIndex (.assign .local name e)
      (fun r s => r = none → PtxPackedCopyIndex s) := by
  apply Hoare.assign
  · intro F s v hp he
    exact fun _ => phase2_packed_copy_set_other s hp name v hne
  · exact fun _ _ hr => by cases hr

/-- Evaluate the concrete packed address-copy destination from its scalar locals. -/
theorem phase2_packed_destination_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base k : BitVec 64)
    (ha : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k))) :
    evalAt s (.op .add [.var .local (ofString "al_keys"),
      .panop .mul [.var .local (ofString "k"), .const 52]]) =
      some (.val (.word (base + k * 52))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, hk, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL]

/-- The allocated packed destination agrees with the evaluated machine pointer without wrapping. -/
theorem phase2_packed_destination_toNat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) (base k : BitVec 64)
    (ha : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    (base + k * 52).toNat = locN s "al_keys" + 52 * locN s "k" := by
  have hin := hp.1.2.1.2
  have hslot := (phase2_packed_copy_index_destinations hp).1.2
  dsimp at hin hslot
  have hlt : locN s "al_keys" + 52 * locN s "k" < 2 ^ 64 := by omega
  have han : locN s "al_keys" = base.toNat := by simp [locN, ha]
  have hkn : locN s "k" = k.toNat := by simp [locN, hk]
  rw [han, hkn] at hlt ⊢
  rw [BitVec.toNat_add, BitVec.toNat_mul]
  change (base.toNat + k.toNat * 52 % 2 ^ 64) % 2 ^ 64 = base.toNat + 52 * k.toNat
  rw [Nat.add_mod_mod, Nat.mul_comm k.toNat 52, Nat.mod_eq_of_lt hlt]

/-- Evaluate the second memcpy destination, including the address-prefix offset. -/
theorem phase2_packed_key_destination_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base k : BitVec 64)
    (ha : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k))) :
    evalAt s (.op .add [.var .local (ofString "al_keys"),
      .panop .mul [.var .local (ofString "k"), .const 52], .const 20]) =
      some (.val (.word (base + k * 52 + 20))) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, ha, hk, valueIsWord, valueWord,
    wordOpHOL, wordOp, panOpHOL, BitVec.add_assoc]

/-- The second memcpy pointer also denotes its exact nonwrapping natural address. -/
theorem phase2_packed_key_destination_toNat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) (base k : BitVec 64)
    (ha : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    (base + k * 52 + 20).toNat = locN s "al_keys" + 52 * locN s "k" + 20 := by
  have hd := phase2_packed_destination_toNat s hp base k ha hk hb
  have hin := hp.1.2.1.2
  have hslot := (phase2_packed_copy_index_destinations hp).2.2
  dsimp at hin hslot
  have hlt : locN s "al_keys" + 52 * locN s "k" + 20 < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, hd]
  change (locN s "al_keys" + 52 * locN s "k" + 20) % 2 ^ 64 = _
  exact Nat.mod_eq_of_lt hlt

/-- The storage-key half of a packed record also has a nonwrapping pointer. -/
theorem phase2_packed_storage_destination_toNat {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) (base k : BitVec 64)
    (ha : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    (base + k * 52 + 20).toNat = locN s "al_keys" + 52 * locN s "k" + 20 := by
  exact phase2_packed_key_destination_toNat s hp base k ha hk hb

/-- Framing the access-list header and record counts preserves the total key count. -/
theorem phase2_packed_copy_total_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    txAccessSlots post (locN post "tx") = txAccessSlots s (locN s "tx") := by
  change phase2_key_prefix post (memW post (locN post "tx" + 216)) =
    phase2_key_prefix s (memW s (locN s "tx" + 216))
  rw [hc]
  exact phase2_key_prefix_congr s post _ hm

/-- Inclusive inner-loop invariant, valid both before an iteration and at loop exit. -/
def PtxPackedInnerInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedKeysReady s ∧
  locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
  locN s "i" < memW s (locN s "tx" + 216) ∧
  locN s "j" ≤ memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) ∧
  locN s "k" = phase2_key_prefix s (locN s "i") + locN s "j"

theorem phase2_packed_inner_of_guarded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedCopyIndex s) : PtxPackedInnerInv s :=
  ⟨hp.1, hp.2.1, hp.2.2.1, Nat.le_of_lt hp.2.2.2.1, hp.2.2.2.2⟩

theorem phase2_packed_inner_guarded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedInnerInv s)
    (hg : locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    PtxPackedCopyIndex s :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hg, hp.2.2.2.2⟩

/-- On inner-loop exit the flattened index is exactly the next record prefix. -/
theorem phase2_packed_inner_exit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedInnerInv s)
    (hg : ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN s "j" = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) ∧
    locN s "k" = phase2_key_prefix s (locN s "i" + 1) := by
  have hj := hp.2.2.2.1
  have he : locN s "j" = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by omega
  refine ⟨he, ?_⟩
  rw [phase2_key_prefix_succ, ← he]
  exact hp.2.2.2.2

/-- At the last record's inner-loop exit every packed key has been counted. -/
theorem phase2_packed_last_inner_exit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedInnerInv s)
    (hlast : locN s "i" + 1 = memW s (locN s "tx" + 216))
    (hg : ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN s "k" = locN s "nkeys" := by
  have hexit := (phase2_packed_inner_exit hp hg).2
  rw [hlast] at hexit
  change locN s "k" = txAccessSlots s (locN s "tx") at hexit
  exact hexit.trans (hp.2.1.symm)

/-- Only live access-list records need framing to preserve the guarded copy indices. -/
theorem phase2_packed_copy_live_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["nkeys", "i", "j", "k"] : List String), locN post n = locN s n)
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex post := by
  have hi := hl "i" (by simp)
  have hj := hl "j" (by simp)
  have hk := hl "k" (by simp)
  have hn := hl "nkeys" (by simp)
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · rw [hn, phase2_packed_copy_total_frame s post hc hm]; exact hp.2.1
  · rw [hi, hc]; exact hp.2.2.1
  · rw [hj, hi, hm _ hp.2.2.1]; exact hp.2.2.2.1
  · rw [hk, hi, hj]
    rw [phase2_key_prefix_congr s post (locN s "i")
      (fun i h => hm i (Nat.lt_trans h hp.2.2.1))]
    exact hp.2.2.2.2

/-- Both counter updates re-establish the inclusive inner invariant. -/
theorem phase2_packed_inner_update_indices {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedCopyIndex s) :
    let post := setVarHOLFinite (ofString "j")
      (.val (.word (BitVec.ofNat 64 (locN s "j" + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) s)
    PtxPackedInnerInv post := by
  have hr := phase2_packed_copy_update_indices s hp
  have hb := phase2_packed_copy_next_inner_bound hp
  have hj := (phase2_packed_copy_counter_bounds hp).2
  change locN s "j" + 1 < 18446744073709551616 at hj
  simp only [locN] at hj
  have hji : ofString "j" ≠ ofString "i" := by decide
  have hki : ofString "k" ≠ ofString "i" := by decide
  have hjt : ofString "j" ≠ ofString "tx" := by decide
  have hkt : ofString "k" ≠ ofString "tx" := by decide
  have hjn : ofString "j" ≠ ofString "nkeys" := by decide
  have hkn : ofString "k" ≠ ofString "nkeys" := by decide
  dsimp only
  refine ⟨hr.1, ?_, ?_, ?_, hr.2⟩
  · simpa [txAccessSlots, locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      hjn, hkn, hjt, hkt]
      using hp.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      hji, hki, hjt, hkt]
      using hp.2.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      hji, hki, hjt, hkt, Nat.mod_eq_of_lt hj] using hb.1

/-- Header and live-record framing also preserves the inclusive loop invariant. -/
theorem phase2_packed_inner_live_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedInnerInv s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["nkeys", "i", "j", "k"] : List String), locN post n = locN s n)
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedInnerInv post := by
  have hi := hl "i" (by simp)
  have hj := hl "j" (by simp)
  have hk := hl "k" (by simp)
  have hn := hl "nkeys" (by simp)
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · rw [hn, phase2_packed_copy_total_frame s post hc hm]; exact hp.2.1
  · rw [hi, hc]; exact hp.2.2.1
  · rw [hj, hi, hm _ hp.2.2.1]; exact hp.2.2.2.1
  · rw [hk, hi, hj]
    rw [phase2_key_prefix_congr s post (locN s "i")
      (fun i h => hm i (Nat.lt_trans h hp.2.2.1))]
    exact hp.2.2.2.2

/-- Outer copy-loop invariant at record boundaries. -/
def PtxPackedOuterInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedKeysReady s ∧
  locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
  locN s "i" ≤ memW s (locN s "tx" + 216) ∧
  locN s "k" = phase2_key_prefix s (locN s "i")

/-- A fresh inner pass starts at the current outer prefix. -/
theorem phase2_packed_outer_enter {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedOuterInv s)
    (hi : locN s "i" < memW s (locN s "tx" + 216))
    (hj : locN s "j" = 0) : PtxPackedInnerInv s := by
  refine ⟨hp.1, hp.2.1, hi, ?_, ?_⟩
  · rw [hj]; exact Nat.zero_le _
  · simpa [hj] using hp.2.2.2

/-- The outer guard's false branch identifies the final flattened key count. -/
theorem phase2_packed_outer_exit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedOuterInv s)
    (hg : ¬ locN s "i" < memW s (locN s "tx" + 216)) :
    locN s "i" = memW s (locN s "tx" + 216) ∧ locN s "k" = locN s "nkeys" := by
  have hi : locN s "i" = memW s (locN s "tx" + 216) := by
    have := hp.2.2.1
    omega
  refine ⟨hi, ?_⟩
  have hk := hp.2.2.2
  rw [hi] at hk
  change locN s "k" = txAccessSlots s (locN s "tx") at hk
  exact hk.trans hp.2.1.symm

/-- Completing an inner pass and advancing the record restores the outer invariant. -/
theorem phase2_packed_outer_advance {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedInnerInv s)
    (hg : ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
    (hb : locN s "i" + 1 < 2 ^ 64) :
    PtxPackedOuterInv (setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) := by
  have hx := (phase2_packed_inner_exit hp hg).2
  have hi := hp.2.2.1
  have hit : ofString "i" ≠ ofString "tx" := by decide
  have hin : ofString "i" ≠ ofString "nkeys" := by decide
  have hik : ofString "i" ≠ ofString "k" := by decide
  change locN s "i" + 1 < 18446744073709551616 at hb
  simp only [locN] at hb
  refine ⟨phase2_packed_keys_set_other s hp.1 _ _ (by decide), ?_, ?_, ?_⟩
  · simpa [txAccessSlots, locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hit, hin] using hp.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hit, Nat.mod_eq_of_lt hb] using (Nat.succ_le_of_lt hi)
  · simpa [phase2_key_prefix, locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hit, hik, Nat.mod_eq_of_lt hb] using hx

/-- The outer prefix invariant survives changes that frame all live key-count fields. -/
theorem phase2_packed_outer_live_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedOuterInv s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["nkeys", "i", "k"] : List String), locN post n = locN s n)
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedOuterInv post := by
  have hi := hl "i" (by simp)
  have hk := hl "k" (by simp)
  have hn := hl "nkeys" (by simp)
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [hn, phase2_packed_copy_total_frame s post hc hm]; exact hp.2.1
  · rw [hi, hc]; exact hp.2.2.1
  · rw [hk, hi]
    rw [phase2_key_prefix_congr s post (locN s "i")
      (fun i h => hm i (Nat.lt_of_lt_of_le h hp.2.2.1))]
    exact hp.2.2.2

/-- Zeroed copy counters establish the outer invariant after allocation. -/
theorem phase2_packed_outer_init {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hr : PtxPackedKeysReady s)
    (hn : locN s "nkeys" = txAccessSlots s (locN s "tx"))
    (hi : locN s "i" = 0) (hk : locN s "k" = 0) :
    PtxPackedOuterInv s := by
  refine ⟨hr, hn, ?_, ?_⟩
  · rw [hi]; exact Nat.zero_le _
  · simp [hi, hk, phase2_key_prefix]

/-- Resetting the inner counter establishes the next record's inclusive invariant. -/
theorem phase2_packed_inner_reset {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterInv s)
    (hi : locN s "i" < memW s (locN s "tx" + 216)) :
    PtxPackedInnerInv (setVarHOLFinite (ofString "j") (.val (.word 0)) s) := by
  have hjt : ofString "j" ≠ ofString "tx" := by decide
  have hji : ofString "j" ≠ ofString "i" := by decide
  have hjn : ofString "j" ≠ ofString "nkeys" := by decide
  have hjk : ofString "j" ≠ ofString "k" := by decide
  refine ⟨phase2_packed_keys_set_other s hp.1 _ _ (by decide), ?_, ?_, ?_, ?_⟩
  · simpa [txAccessSlots, locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hjt, hjn] using hp.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hjt, hji] using hi
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [phase2_key_prefix, locN, memW, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, hjt, hji, hjk] using hp.2.2.2

/-- The concrete outer increment restores the record-boundary invariant. -/
theorem phase2_packed_outer_increment_hoare :
    Hoare (fun s => PtxPackedInnerInv s ∧
      ¬ locN s "j" < memW s
        (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) ∧
      locN s "i" + 1 < 2 ^ 64)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxPackedOuterInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hp.2.2 he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp.2.2]
    subst w
    exact fun _ => phase2_packed_outer_advance s hp.1 hp.2.1 hp.2.2
  · exact fun _ _ hr => by cases hr

/-- The concrete inner counter reset prepares the next key-copy pass. -/
theorem phase2_packed_inner_reset_hoare :
    Hoare (fun s => PtxPackedOuterInv s ∧
      locN s "i" < memW s (locN s "tx" + 216))
      (.assign .local (ofString "j") (.const 0))
      (fun r s => r = none → PtxPackedInnerInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hv : v = .val (.word 0) := by
      simpa [evalAt, evalHOLExact] using he.symm
    subst v
    intro _
    exact phase2_packed_inner_reset s hp.1 hp.2
  · exact fun _ _ hr => by cases hr

/-- Preserving the transaction header and record interval preserves each live count. -/
theorem phase2_packed_record_counts_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (ht : locN post "tx" = locN s "tx")
    (hh : ∀ off, off < 384 → memW post (locN s "tx" + off) = memW s (locN s "tx" + off))
    (hr : ∀ off, off < 24 * memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + off) =
        memW s (memW s (locN s "tx" + 208) + off)) :
    ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16) := by
  intro i hi
  rw [ht, hh 208 (by omega)]
  simpa only [Nat.add_assoc] using hr (24 * i + 16) (by omega)

/-- The live outer guard itself rules out overflow of the record increment. -/
theorem phase2_packed_outer_successor_bound {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedInnerInv s) : locN s "i" + 1 < 2 ^ 64 := by
  have hi := hp.2.2.1
  have hm : memW s (locN s "tx" + 216) < 2 ^ 64 := by
    unfold memW
    exact BitVec.isLt _
  omega

/-- No additional arithmetic premise is needed for the concrete record increment. -/
theorem phase2_packed_outer_increment_exit_hoare :
    Hoare (fun s => PtxPackedInnerInv s ∧
      ¬ locN s "j" < memW s
        (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxPackedOuterInv s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hb := phase2_packed_outer_successor_bound hp.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    exact fun _ => phase2_packed_outer_advance s hp.1 hp.2 hb
  · exact fun _ _ hr => by cases hr

/-- Interval framing supplies all scalar memory premises of the copy invariant. -/
theorem phase2_packed_copy_intervals_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["tx", "nkeys", "i", "j", "k"] : List String),
      locN post n = locN s n)
    (hh : ∀ off, off < 384 → memW post (locN s "tx" + off) = memW s (locN s "tx" + off))
    (hm : ∀ off, off < 24 * memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + off) =
        memW s (memW s (locN s "tx" + 208) + off)) :
    PtxPackedCopyIndex post := by
  have ht := hl "tx" (by simp)
  apply phase2_packed_copy_live_frame s post hp hr
  · intro n hn
    exact hl n (List.mem_cons_of_mem _ hn)
  · rw [ht]; exact hh 216 (by omega)
  · exact phase2_packed_record_counts_frame s post ht hh hm

/-- A copy frame preserves a complete word disjoint from both its write and fresh regions. -/
theorem phase2_copy_frame_word {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len p : Nat) (fresh : Ivl)
    (hf : FrameOutside s post [(dst, len)] fresh)
    (hp : p < 2 ^ 64)
    (hd : ¬ CellHits p (dst, len)) (hn : ¬ CellHits p fresh) :
    memW post p = memW s p := by
  have he : (BitVec.ofNat 64 p).toNat = p := by
    exact Nat.mod_eq_of_lt hp
  have hm := hf (BitVec.ofNat 64 p)
    (by intro i hi; simp only [List.mem_singleton] at hi; subst i; simpa only [he] using hd)
    (by simpa only [he] using hn)
  simp only [memW, hm]

/-- The actual paired assignments restore the inclusive inner-loop invariant. -/
theorem phase2_packed_inner_counters_hoare :
    Hoare PtxPackedCopyIndex
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedInnerInv s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, PtxPackedCopyIndex before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp).1
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v hb he
      have heq : w = BitVec.ofNat 64 (locN s "k" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨s, hp, rfl⟩
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      obtain ⟨before, hp, rfl⟩ := hp
      have hj : locN (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) "j" =
          locN before "j" := by
        simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "k" ≠ ofString "j" by decide]
      have hb := (phase2_packed_copy_counter_bounds hp).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => phase2_packed_inner_update_indices before hp
    · exact fun _ _ hr => by cases hr

/-- A copy frame preserves every word in a protected interval. -/
theorem phase2_copy_frame_interval {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len base size : Nat) (fresh : Ivl)
    (hf : FrameOutside s post [(dst, len)] fresh)
    (hb : base + size ≤ 2 ^ 64)
    (hd : ∀ off, off < size → ¬ CellHits (base + off) (dst, len))
    (hn : ∀ off, off < size → ¬ CellHits (base + off) fresh) :
    ∀ off, off < size → memW post (base + off) = memW s (base + off) := by
  intro off ho
  exact phase2_copy_frame_word s post dst len (base + off) fresh hf
    (by omega) (hd off ho) (hn off ho)

/-- A complete word inside a disjoint protected interval is untouched by a copy. -/
theorem phase2_copy_protected_cell (base size p dst len : Nat)
    (hlen : 0 < len)
    (hp : base ≤ p ∧ p + 8 ≤ base + size)
    (hd : Disj (base, size) (dst, len)) :
    ¬ CellHits p (dst, len) := by
  simp only [Disj] at hd
  simp only [CellHits]
  omega

/-- Compose the two copy-call preservation obligations with the verified counters. -/
theorem phase2_packed_inner_body_of_copies
    (addressCopy keyCopy : ProgHOL 64)
    (ha : Hoare PtxPackedCopyIndex addressCopy
      (fun r s => r = none → PtxPackedCopyIndex s))
    (hk : Hoare PtxPackedCopyIndex keyCopy
      (fun r s => r = none → PtxPackedCopyIndex s)) :
    Hoare PtxPackedCopyIndex
      (.seq addressCopy (.seq keyCopy (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedInnerInv s) := by
  apply Hoare.seq_fall (R := PtxPackedCopyIndex)
  · exact ha
  · apply Hoare.seq_fall (R := PtxPackedCopyIndex)
    · exact hk
    · exact phase2_packed_inner_counters_hoare

/-- Disjoint intervals protect aligned complete words against a copy frame. -/
theorem phase2_copy_frame_disjoint_word {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len p : Nat) (region fresh : Ivl)
    (hf : FrameOutside s post [(dst, len)] fresh)
    (hp : p < 2 ^ 64) (ha : p % 8 = 0)
    (hin : region.1 ≤ p ∧ p + 8 ≤ region.1 + region.2)
    (hd : Disj region (dst, len)) (hn : Disj region fresh)
    (hz : len = 0 → dst % 8 = 0)
    (hfresh : fresh.2 = 0 → fresh.1 % 8 = 0) :
    memW post p = memW s p := by
  apply phase2_copy_frame_word s post dst len p fresh hf hp
  · exact not_cellHits_of_disj ha hz hin hd
  · exact not_cellHits_of_disj ha hfresh hin hn

/-- A copy disjoint from the transaction header preserves its access-list metadata. -/
theorem phase2_copy_frame_tx_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (tx dst len : Nat) (fresh : Ivl)
    (hf : FrameOutside s post [(dst, len)] fresh)
    (hb : tx + 384 ≤ 2 ^ 64) (ha : tx % 8 = 0)
    (hd : Disj (tx, 384) (dst, len)) (hn : Disj (tx, 384) fresh)
    (hz : len = 0 → dst % 8 = 0)
    (hfresh : fresh.2 = 0 → fresh.1 % 8 = 0) :
    memW post (tx + 208) = memW s (tx + 208) ∧
    memW post (tx + 216) = memW s (tx + 216) := by
  constructor
  · exact phase2_copy_frame_disjoint_word s post dst len (tx + 208) (tx, 384) fresh hf
      (by omega) (by omega) (by constructor <;> dsimp <;> omega) hd hn hz hfresh
  · exact phase2_copy_frame_disjoint_word s post dst len (tx + 216) (tx, 384) fresh hf
      (by omega) (by omega) (by constructor <;> dsimp <;> omega) hd hn hz hfresh

/-- Copying outside the record array preserves its live key-count words. -/
theorem phase2_copy_frame_record_counts {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len base count : Nat) (fresh : Ivl)
    (hf : FrameOutside s post [(dst, len)] fresh)
    (hb : base + 24 * count ≤ 2 ^ 64) (ha : base % 8 = 0)
    (hd : Disj (base, 24 * count) (dst, len))
    (hn : Disj (base, 24 * count) fresh)
    (hz : len = 0 → dst % 8 = 0)
    (hfresh : fresh.2 = 0 → fresh.1 % 8 = 0) :
    ∀ i, i < count → memW post (base + 24 * i + 16) = memW s (base + 24 * i + 16) := by
  intro i hi
  apply phase2_copy_frame_disjoint_word s post dst len _ (base, 24 * count) fresh hf
  · omega
  · omega
  · dsimp; constructor <;> omega
  · exact hd
  · exact hn
  · exact hz
  · exact hfresh

/-- A disjoint copy preserves the two transaction fields used by the nested loops. -/
theorem phase2_copy_frame_tx_headers {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len : Nat)
    (hf : FrameOutside s post [(dst, len)] (0, 0))
    (hlen : 0 < len)
    (hb : locN s "tx" + 384 ≤ 2 ^ 64)
    (hd : Disj (locN s "tx", 384) (dst, len)) :
    memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
    memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) := by
  have hword : ∀ off, off + 8 ≤ 384 →
      memW post (locN s "tx" + off) = memW s (locN s "tx" + off) := by
    intro off ho
    apply phase2_copy_frame_word s post dst len _ (0, 0) hf (by omega)
    · exact phase2_copy_protected_cell _ _ _ _ _ hlen ⟨by omega, by omega⟩ hd
    · simp [CellHits]
  exact ⟨hword 208 (by decide), hword 216 (by decide)⟩

/-- Preserved metadata and record count words suffice to preserve the total. -/
theorem phase2_copy_total_of_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (ht : locN post "tx" = locN s "tx")
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    txAccessSlots post (locN post "tx") = txAccessSlots s (locN s "tx") := by
  apply phase2_packed_copy_total_frame s post
  · rw [ht]; exact hh.2
  · intro i hi; rw [ht, hh.1]; exact hm i hi

/-- Only the two header words and live record counts are needed to frame copy indices. -/
theorem phase2_packed_copy_metadata_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["tx", "nkeys", "i", "j", "k"] : List String),
      locN post n = locN s n)
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex post := by
  have ht := hl "tx" (by simp)
  apply phase2_packed_copy_live_frame s post hp hr
  · intro n hn
    exact hl n (List.mem_cons_of_mem _ hn)
  · rw [ht]; exact hh.2
  · intro i hi
    rw [ht, hh.1]
    exact hm i hi

/-- A nonallocating copy outside the input regions preserves the guarded indices. -/
theorem phase2_packed_copy_frame_preserves {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst len : Nat)
    (hp : PtxPackedCopyIndex s) (hr : PtxPackedKeysReady post)
    (hl : ∀ n ∈ (["tx", "nkeys", "i", "j", "k"] : List String), locN post n = locN s n)
    (hf : FrameOutside s post [(dst, len)] (0, 0)) (hlen : 0 < len)
    (htb : locN s "tx" + 384 ≤ 2 ^ 64)
    (htd : Disj (locN s "tx", 384) (dst, len))
    (hab : memW s (locN s "tx" + 208) + 24 * memW s (locN s "tx" + 216) ≤ 2 ^ 64)
    (haa : memW s (locN s "tx" + 208) % 8 = 0)
    (had : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len)) :
    PtxPackedCopyIndex post := by
  have ht := hl "tx" (by simp)
  have hh := phase2_copy_frame_tx_headers s post dst len hf hlen htb htd
  have hm := phase2_copy_frame_record_counts s post dst len
    (memW s (locN s "tx" + 208)) (memW s (locN s "tx" + 216)) (0, 0)
    hf hab haa had (by simp [Disj]) (by omega) (by simp)
  apply phase2_packed_copy_live_frame s post hp hr
  · intro n hn; exact hl n (List.mem_cons_of_mem _ hn)
  · rw [ht]; exact hh.2
  · intro i hi; rw [ht, hh.1]; exact hm i hi

/-- Extract an unchanged word directly from the full world-step frame. -/
theorem phase2_world_frame_word {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl) (fresh : Ivl) (p : Nat)
    (hf : FrameOutside s post keep fresh) (hp : p < 2 ^ 64)
    (hk : ∀ region ∈ keep, ¬ CellHits p region)
    (hn : ¬ CellHits p fresh) : memW post p = memW s p := by
  have he : (BitVec.ofNat 64 p).toNat = p := Nat.mod_eq_of_lt hp
  have hm := hf (BitVec.ofNat 64 p)
    (by simpa only [he] using hk) (by simpa only [he] using hn)
  simp only [memW, hm]

/-- Consecutive nonallocating copy frames combine into the union of their write regions. -/
theorem phase2_copy_frames_compose {F : Type}
    (s middle post : PanSemStateFiniteExact 64 F) (first second : List Ivl)
    (hfirst : FrameOutside s middle first (0, 0))
    (hsecond : FrameOutside middle post second (0, 0)) :
    FrameOutside s post (first ++ second) (0, 0) := by
  intro a ha hn
  have h1 : ∀ region ∈ first, ¬ CellHits a.toNat region := by
    intro region hr
    exact ha region (List.mem_append_left _ hr)
  have h2 : ∀ region ∈ second, ¬ CellHits a.toNat region := by
    intro region hr
    exact ha region (List.mem_append_right _ hr)
  exact (hsecond a h2 hn).trans (hfirst a h1 hn)

/-- Full world frames preserve live record counts when every permitted write is disjoint. -/
theorem phase2_world_frame_record_counts {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (keep : List Ivl) (fresh : Ivl)
    (base count : Nat) (hf : FrameOutside s post keep fresh)
    (hb : base + 24 * count ≤ 2 ^ 64) (ha : base % 8 = 0)
    (hk : ∀ region ∈ keep, Disj (base, 24 * count) region)
    (hz : ∀ region ∈ keep, region.2 = 0 → region.1 % 8 = 0)
    (hn : Disj (base, 24 * count) fresh)
    (hzero : fresh.2 = 0 → fresh.1 % 8 = 0) :
    ∀ i, i < count → memW post (base + 24 * i + 16) = memW s (base + 24 * i + 16) := by
  intro i hi
  have hal : (base + 24 * i + 16) % 8 = 0 := by omega
  have hin : base ≤ base + 24 * i + 16 ∧ base + 24 * i + 16 + 8 ≤ base + 24 * count := by
    constructor <;> omega
  apply phase2_world_frame_word s post keep fresh _ hf (by omega)
  · intro region hr
    exact not_cellHits_of_disj hal (hz region hr) hin (hk region hr)
  · exact not_cellHits_of_disj hal hzero hin hn

/-- Allocated input words are outside both arena regions in a world-step frame. -/
theorem phase2_world_frame_heap_word {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (old R : List Ivl) (p : Nat)
    (ha : ArenaOK s)
    (hin : Inside (p, 8) InitE.sourceBase (globN s "heap_ptr"))
    (hf : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (ho : ∀ region ∈ old, ¬ CellHits p region)
    (hr : ∀ region ∈ R, ¬ CellHits p region) :
    memW post p = memW s p := by
  have hsep : heapLimit ≤ InitE.scratchStart := by decide
  obtain ⟨_, hhp, hfm, hsc, _⟩ := ha
  have hp : p < 2 ^ 64 := by
    have hlim : heapLimit < 2 ^ 64 := by decide
    unfold Inside at hin
    dsimp at hin
    omega
  apply phase2_world_frame_word s post _ _ p hf hp
  · intro region hm
    rcases List.mem_append.1 hm with hm | hm
    · rcases List.mem_append.1 hm with hm | hm
      · exact ho region hm
      · exact hr region hm
    · simp only [List.mem_singleton] at hm
      subst region
      unfold CellHits freeGap Inside at *
      dsimp at *
      omega
  · unfold CellHits heapFree Inside at *
    dsimp at *
    omega

/-- Arena-aware world framing preserves every live record count in an allocated array. -/
theorem phase2_world_frame_heap_counts {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (old R : List Ivl) (base count : Nat)
    (ha : ArenaOK s)
    (hin : Inside (base, 24 * count) InitE.sourceBase (globN s "heap_ptr"))
    (hf : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (ho : ∀ i, i < count → ∀ region ∈ old, ¬ CellHits (base + 24 * i + 16) region)
    (hr : ∀ i, i < count → ∀ region ∈ R, ¬ CellHits (base + 24 * i + 16) region) :
    ∀ i, i < count → memW post (base + 24 * i + 16) = memW s (base + 24 * i + 16) := by
  intro i hi
  apply phase2_world_frame_heap_word s post old R _ ha ?_ hf (ho i hi) (hr i hi)
  unfold Inside at hin ⊢
  dsimp at hin ⊢
  constructor <;> omega

/-- Reassemble packed readiness after a copy from its domain and world guarantees. -/
theorem phase2_packed_ready_after_copy {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedKeysReady s)
    (hl : ∀ n ∈ (["al_keys", "nkeys"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hd : ∀ a, s.memaddrs a → post.memaddrs a)
    (hw : ∃ S Nd, WorldTypedWith post S Nd ∧ TxAccessListAt post S Nd (locN post "tx") ∧
      IvlsDisj [(locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned post S Nd)) : PtxPackedKeysReady post := by
  have ha : locN post "al_keys" = locN s "al_keys" := by
    simp [locN, hl "al_keys" (by simp)]
  have hn : locN post "nkeys" = locN s "nkeys" := by
    simp [locN, hl "nkeys" (by simp)]
  refine ⟨?_, ?_, ?_, ?_, hw⟩
  · simpa only [hl "al_keys" (by simp)] using hp.1
  · rw [ha, hn]
    exact ⟨hp.2.1.1, hp.2.1.2.trans hh⟩
  · rw [ha]; exact hp.2.2.1
  · rw [ha, hn]
    exact phase2_packed_keys_words_frame s post _ _ hp.2.2.2.1 hd

/-- A complete header word inherits the arena exclusions of its allocated header. -/
theorem phase2_world_frame_heap_header {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (old R : List Ivl) (tx off : Nat)
    (ha : ArenaOK s) (hin : Inside (tx, 384) InitE.sourceBase (globN s "heap_ptr"))
    (hoff : off + 8 ≤ 384)
    (hf : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (ho : ∀ region ∈ old, ¬ CellHits (tx + off) region)
    (hr : ∀ region ∈ R, ¬ CellHits (tx + off) region) :
    memW post (tx + off) = memW s (tx + off) := by
  apply phase2_world_frame_heap_word s post old R _ ha ?_ hf ho hr
  unfold Inside at hin ⊢
  dsimp at hin ⊢
  constructor <;> omega

/-- Spatial separation discharges the remaining exclusions in the full world frame. -/
theorem phase2_world_frame_heap_disjoint {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (old R : List Ivl) (b : Ivl) (p : Nat)
    (ha : ArenaOK s) (hin : Inside b InitE.sourceBase (globN s "heap_ptr"))
    (hp : b.1 ≤ p ∧ p + 8 ≤ b.1 + b.2) (hal : p % 8 = 0)
    (hf : FrameOutside s post (old ++ R ++ [freeGap s]) (heapFree s))
    (ho : ∀ region ∈ old, Disj b region)
    (hr : ∀ region ∈ R, Disj b region)
    (hozero : ∀ region ∈ old, region.2 = 0 → region.1 % 8 = 0)
    (hrzero : ∀ region ∈ R, region.2 = 0 → region.1 % 8 = 0) :
    memW post p = memW s p := by
  refine phase2_world_frame_heap_word s post old R p ha ?_ hf ?_ ?_
  · unfold Inside at hin ⊢
    dsimp
    constructor <;> omega
  · intro region hm
    exact not_cellHits_of_disj hal (hozero region hm) hp (ho region hm)
  · intro region hm
    exact not_cellHits_of_disj hal (hrzero region hm) hp (hr region hm)

/-- Reassemble the guarded copy invariant from domain, world, and input-frame guarantees. -/
theorem phase2_packed_copy_reassemble {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hd : ∀ a, s.memaddrs a → post.memaddrs a)
    (hw : ∃ S Nd, WorldTypedWith post S Nd ∧ TxAccessListAt post S Nd (locN post "tx") ∧
      IvlsDisj [(locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned post S Nd))
    (hc : memW post (locN post "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW post (locN post "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex post := by
  have hr : PtxPackedKeysReady post := by
    apply phase2_packed_ready_after_copy s post hp.1 _ hh hd hw
    intro n hn
    exact hl n (by simp at hn ⊢; tauto)
  apply phase2_packed_copy_live_frame s post hp hr _ hc hm
  intro n hn
  have he := hl n (by simp at hn ⊢; tauto)
  simp [locN, he]

/-- Empty global-write contracts, as used by memcpy, fix the heap boundary exactly. -/
theorem phase2_copy_globals_heap_eq {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hg : GlobalsKept [] s post) :
    globN post "heap_ptr" = globN s "heap_ptr" := by
  have he := hg (ofString "heap_ptr") (by simp)
  simp only [globN, he]

/-- The joint transaction witness supplies the world exclusions for header words. -/
theorem phase2_tx_header_world_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (R : List Ivl)
    (tx off : Nat) (ha : ArenaOK s) (hw : WorldTypedWith s S Nd)
    (ht : TxAccessListAt s S Nd tx) (hoff : off + 8 ≤ 384) (ho8 : off % 8 = 0)
    (hf : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hr : ∀ region ∈ R, Disj (tx, 384) region)
    (hz : ∀ region ∈ R, region.2 = 0 → region.1 % 8 = 0) :
    memW post (tx + off) = memW s (tx + off) := by
  have htx8 : tx % 8 = 0 := ht.1.1.1
  exact phase2_world_frame_heap_disjoint s post (worldOwned s S Nd) R (tx, 384)
    (tx + off) ha ht.1.2.1 (by constructor <;> dsimp <;> omega)
    (by omega) hf (ht.2.1 _ (by simp)) hr (worldOwned_zero_aligned hw) hz

/-- Empty global-write contracts discharge the heap premise when rebuilding readiness. -/
theorem phase2_packed_ready_globals_kept {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedKeysReady s)
    (hl : ∀ n ∈ (["al_keys", "nkeys"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hg : GlobalsKept [] s post)
    (hd : ∀ a, s.memaddrs a → post.memaddrs a)
    (hw : ∃ S Nd, WorldTypedWith post S Nd ∧ TxAccessListAt post S Nd (locN post "tx") ∧
      IvlsDisj [(locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned post S Nd)) : PtxPackedKeysReady post := by
  apply phase2_packed_ready_after_copy s post hp hl _ hd hw
  rw [phase2_copy_globals_heap_eq s post hg]

/-- The supplied memcpy contract guarantees an unchanged heap pointer on resumption. -/
theorem phase2_memcpy_heap_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r → globN post "heap_ptr" = globN s "heap_ptr")
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := h.wk_memcpy
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr
  have step := hs s hc hp he hn hr
  exact phase2_copy_globals_heap_eq s _ step.2.2.1

/-- The joint transaction witness protects each live access-list count word. -/
theorem phase2_tx_count_world_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (R : List Ivl)
    (tx i : Nat) (ha : ArenaOK s) (hw : WorldTypedWith s S Nd)
    (ht : TxAccessListAt s S Nd tx) (hi : i < memW s (tx + 216))
    (hf : FrameOutside s post (worldOwned s S Nd ++ R ++ [freeGap s]) (heapFree s))
    (hr : ∀ region ∈ R,
      Disj (memW s (tx + 208), 24 * memW s (tx + 216)) region)
    (hz : ∀ region ∈ R, region.2 = 0 → region.1 % 8 = 0) :
    memW post (memW s (tx + 208) + 24 * i + 16) =
      memW s (memW s (tx + 208) + 24 * i + 16) := by
  have hpos : 0 < memW s (tx + 216) := by omega
  have hin := (ht.2.2 hpos).1
  have hsep := (ht.2.2 hpos).2
  have hal : memW s (tx + 208) % 8 = 0 :=
    (ht.1.2.2.2.2.2.2.2.2.1 hpos).1
  exact phase2_world_frame_heap_disjoint s post (worldOwned s S Nd) R
    (memW s (tx + 208), 24 * memW s (tx + 216))
    (memW s (tx + 208) + 24 * i + 16) ha hin
    (by constructor <;> dsimp <;> omega) (by omega) hf
    (hsep _ (by simp)) hr (worldOwned_zero_aligned hw) hz

/-- The supplied copy contract preserves every global, not just the heap boundary. -/
theorem phase2_memcpy_globals_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r → GlobalsKept [] s post)
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := h.wk_memcpy
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr
  exact (hs s hc hp he hn hr).2.2.1

/-- Extract the world witness and memory frame supplied by the concrete memcpy contract. -/
theorem phase2_memcpy_world_frame_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r →
        ∀ S Nd, WorldTypedWith s S Nd →
          IvlsDisj [(locN s "dst", locN s "n")] (worldTypedIvls s S Nd) →
          ∃ S' Nd', WorldTypedWith post S' Nd' ∧
            OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
            FrameOutside s post
              (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s])
              (heapFree s))
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := h.wk_memcpy
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr S Nd hw hd
  have step := hs s hc hp he hn hr
  obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := step.2.2.2.2 S Nd hw hd
  exact ⟨S', Nd', hw', hg, hf⟩

/-- Preserve a live record count using the actual memcpy world-step contract. -/
theorem phase2_memcpy_step_count {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (r : Option (PanSemResultExact 64))
    (S Nd : List Nat) (tx i : Nat) (ha : ArenaOK s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd tx)
    (hi : i < memW s (tx + 216))
    (step : WorldStep (fun s => [(locN s "dst", locN s "n")]) []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])] NoExtra s r post)
    (hworld : IvlsDisj [(locN s "dst", locN s "n")] (worldTypedIvls s S Nd))
    (hrec : Disj (memW s (tx + 208), 24 * memW s (tx + 216))
      (locN s "dst", locN s "n")) (hn : 0 < locN s "n") :
    memW post (memW s (tx + 208) + 24 * i + 16) =
      memW s (memW s (tx + 208) + 24 * i + 16) := by
  obtain ⟨S', Nd', _, _, _, hf, _⟩ := step.2.2.2.2 S Nd hw hworld
  apply phase2_tx_count_world_frame s post S Nd _ tx i ha hw ht hi hf
  · intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hrec
  · intro region hm hz
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at hz
    omega

/-- Specialize a memcpy world frame to the two access-list header fields. -/
theorem phase2_memcpy_frame_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (tx : Nat)
    (ha : ArenaOK s) (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd tx)
    (hf : FrameOutside s post
      (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s]) (heapFree s))
    (hd : Disj (tx, 384) (locN s "dst", locN s "n")) (hn : 0 < locN s "n") :
    memW post (tx + 208) = memW s (tx + 208) ∧
    memW post (tx + 216) = memW s (tx + 216) := by
  have hr : ∀ region ∈ [(locN s "dst", locN s "n")], Disj (tx, 384) region := by
    intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hd
  have hz : ∀ region ∈ [(locN s "dst", locN s "n")], region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at he
    omega
  constructor
  · exact phase2_tx_header_world_frame s post S Nd _ tx 208 ha hw ht (by decide) (by decide) hf hr hz
  · exact phase2_tx_header_world_frame s post S Nd _ tx 216 ha hw ht (by decide) (by decide) hf hr hz

/-- A memcpy world frame preserves the guarded indices once readiness is restored. -/
theorem phase2_memcpy_frame_guarded {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat)
    (hp : PtxPackedCopyIndex s) (hr : PtxPackedKeysReady post)
    (ha : ArenaOK s) (hw : WorldTypedWith s S Nd)
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hl : ∀ n ∈ (["tx", "nkeys", "i", "j", "k"] : List String), locN post n = locN s n)
    (hf : FrameOutside s post
      (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s]) (heapFree s))
    (hd : Disj (locN s "tx", 384) (locN s "dst", locN s "n"))
    (hc : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "dst", locN s "n")) (hn : 0 < locN s "n") :
    PtxPackedCopyIndex post := by
  apply phase2_packed_copy_metadata_frame s post hp hr hl
  · exact phase2_memcpy_frame_metadata s post S Nd _ ha hw ht hf hd hn
  · intro i hi
    apply phase2_tx_count_world_frame s post S Nd _ _ i ha hw ht hi hf
    · intro region hm
      simp only [List.mem_singleton] at hm
      subst region
      exact hc
    · intro region hm hz
      simp only [List.mem_singleton] at hm
      subst region
      dsimp at hz
      omega

/-- Combine copy domain, global, world, and frame guarantees into the guarded invariant. -/
theorem phase2_memcpy_restore_guarded {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd : List Nat)
    (hp : PtxPackedCopyIndex s) (ha : ArenaOK s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hg : GlobalsKept [] s post) (hm : ∀ a, s.memaddrs a → post.memaddrs a)
    (hpost : ∃ S' Nd', WorldTypedWith post S' Nd' ∧ TxAccessListAt post S' Nd' (locN post "tx") ∧
      IvlsDisj [(locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned post S' Nd'))
    (hf : FrameOutside s post
      (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s]) (heapFree s))
    (hd : Disj (locN s "tx", 384) (locN s "dst", locN s "n"))
    (hc : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "dst", locN s "n")) (hn : 0 < locN s "n") :
    PtxPackedCopyIndex post := by
  have hr : PtxPackedKeysReady post := by
    apply phase2_packed_ready_globals_kept s post hp.1 _ hg hm hpost
    intro n hmem
    exact hl n (by simp at hmem ⊢; tauto)
  apply phase2_memcpy_frame_guarded s post S Nd hp hr ha hw ht _ hf hd hc hn
  intro n hmem
  have he := hl n (by simp at hmem ⊢; tauto)
  simp [locN, he]

/-- Separation from the packed buffer implies separation from both concrete copy destinations. -/
theorem phase2_packed_copy_input_disjoint (input : Ivl) (base count k : Nat)
    (hk : k < count)
    (hd : Disj input (base, (count * 52 + 8 + 7) / 8 * 8)) :
    Disj input (base + 52 * k, 20) ∧
    Disj input (base + 52 * k + 20, 32) := by
  obtain ⟨ha, hb⟩ := phase2_key_copy_destinations base count k hk
  exact ⟨disj_of_inside_right ha hd, disj_of_inside_right hb hd⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
