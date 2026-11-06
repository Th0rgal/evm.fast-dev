import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.TeNewSupport
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase34R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount

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

/-- Guarded indices specialize packed-buffer separation to either concrete copy call. -/
theorem phase2_packed_guarded_input_disjoint {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s) (input : Ivl)
    (hd : Disj input
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    Disj input (locN s "al_keys" + 52 * locN s "k", 20) ∧
    Disj input (locN s "al_keys" + 52 * locN s "k" + 20, 32) := by
  exact phase2_packed_copy_input_disjoint input _ _ _
    (phase2_packed_copy_index_bound hp) hd

/-- Input separation needed by both memcpy calls follows from two buffer-level facts. -/
theorem phase2_packed_copy_input_regions {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (ht : Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hr : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    ∀ region ∈ [(locN s "al_keys" + 52 * locN s "k", 20),
      (locN s "al_keys" + 52 * locN s "k" + 20, 32)],
      Disj (locN s "tx", 384) region ∧
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) region := by
  have ha := phase2_packed_guarded_input_disjoint s hp _ ht
  have hb := phase2_packed_guarded_input_disjoint s hp _ hr
  intro region hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨ha.1, hb.1⟩
  · exact ⟨ha.2, hb.2⟩

/-- Previously allocated packed storage stays separate from a growing world. -/
theorem phase2_packed_owned_growth {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (old new : List Ivl) (buffer : Ivl)
    (hin : Inside buffer InitE.sourceBase (globN s "heap_ptr"))
    (hg : OwnedGrows s post old new) (hd : IvlsDisj [buffer] old) :
    IvlsDisj [buffer] new := by
  intro b hb o ho
  simp only [List.mem_singleton] at hb
  subst b
  rcases hg o ho with rfl | ⟨j, hj, hsub⟩ | hfresh
  · exact disj_zero_right buffer
  · exact disj_of_inside_right hsub (hd buffer (by simp) j hj)
  · have hbefore : buffer.1 + buffer.2 ≤ o.1 := by
      exact hin.2.trans hfresh.1
    exact Or.inr (Or.inr (Or.inl hbefore))

/-- Both copy destinations retain the same world and transaction ownership witness. -/
theorem phase2_packed_memcpy_owned_separation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s) :
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "al_keys" + 52 * locN s "k", 20),
        (locN s "al_keys" + 52 * locN s "k" + 20, 32)] (worldOwned s S Nd) := by
  obtain ⟨S, Nd, hw, ht, hd⟩ := hp.1.2.2.2.2
  refine ⟨S, Nd, hw, ht, ?_⟩
  intro dest hdest region hregion
  have hb := hd (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
    (by simp) region hregion
  have hs := phase2_packed_guarded_input_disjoint s hp region (disj_symm hb)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdest
  rcases hdest with rfl | rfl
  · exact disj_symm hs.1
  · exact disj_symm hs.2

/-- Owned-region separation also excludes every typed world interval. -/
theorem phase2_packed_typed_of_owned {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S Nd : List Nat) (writes : List Ivl)
    (hd : IvlsDisj writes (worldOwned s S Nd)) :
    IvlsDisj writes (worldTypedIvls s S Nd) := by
  intro dest hdest region hregion
  exact hd dest hdest region (worldTypedIvls_sub_worldOwned hregion)

/-- Reconstruct packed readiness using ownership growth instead of post-state separation. -/
theorem phase2_packed_ready_owned_growth {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat)
    (hp : PtxPackedKeysReady s)
    (hl : ∀ n ∈ (["al_keys", "nkeys"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hg : GlobalsKept [] s post) (hm : ∀ a, s.memaddrs a → post.memaddrs a)
    (hw : WorldTypedWith post S' Nd') (ht : TxAccessListAt post S' Nd' (locN post "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hgrow : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd')) :
    PtxPackedKeysReady post := by
  apply phase2_packed_ready_globals_kept s post hp hl hg hm
  refine ⟨S', Nd', hw, ht, ?_⟩
  have ha : locN post "al_keys" = locN s "al_keys" := by
    simp [locN, hl "al_keys" (by simp)]
  have hn : locN post "nkeys" = locN s "nkeys" := by
    simp [locN, hl "nkeys" (by simp)]
  rw [ha, hn]
  exact phase2_packed_owned_growth s post _ _ _ hp.2.1 hgrow hsep

/-- The supplied memcpy function contract preserves live transaction count words. -/
theorem phase2_memcpy_count_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r →
        ∀ S Nd tx i, ArenaOK s → WorldTypedWith s S Nd →
          TxAccessListAt s S Nd tx → i < memW s (tx + 216) →
          IvlsDisj [(locN s "dst", locN s "n")] (worldTypedIvls s S Nd) →
          Disj (memW s (tx + 208), 24 * memW s (tx + 216))
            (locN s "dst", locN s "n") → 0 < locN s "n" →
          memW post (memW s (tx + 208) + 24 * i + 16) =
            memW s (memW s (tx + 208) + 24 * i + 16))
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := h.wk_memcpy
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr S Nd tx i ha hw ht hi hd hrec hlen
  exact phase2_memcpy_step_count s _ _ S Nd tx i ha hw ht hi
    (hs s hc hp he hn hr) hd hrec hlen

/-- Fresh packed allocation separates its entire rounded extent from transaction inputs. -/
theorem phase2_packed_alloc_input_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (base : Nat)
    (hp : PtxAddressCountInv s)
    (hf : FreshBlock (callEntryStateHOLFinite s callee) post base (locN s "nkeys" * 52 + 8)) :
    Disj (locN s "tx", 384) (base, (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    (0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (base, (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) := by
  have hready : PtxAccessCountReady s := hp.1.1.1.1
  obtain ⟨S, Nd, _, ht, _⟩ := hready.1.2
  have hstart : globN s "heap_ptr" ≤ base := hf.2.1.1
  refine ⟨Or.inr (Or.inr (Or.inl (ht.1.2.1.2.trans hstart))), ?_⟩
  intro hn
  exact Or.inr (Or.inr (Or.inl ((ht.2.2 hn).1.2.trans hstart)))

/-- The actual memcpy contract preserves aligned transaction header fields. -/
theorem phase2_memcpy_header_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r →
        ∀ S Nd tx off, ArenaOK s → WorldTypedWith s S Nd →
          TxAccessListAt s S Nd tx → off + 8 ≤ 384 → off % 8 = 0 →
          IvlsDisj [(locN s "dst", locN s "n")] (worldTypedIvls s S Nd) →
          Disj (tx, 384) (locN s "dst", locN s "n") → 0 < locN s "n" →
          memW post (tx + off) = memW s (tx + off))
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := h.wk_memcpy
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr S Nd tx off ha hw ht hoff ho8 hd htx hlen
  have step := hs s hc hp he hn hr
  obtain ⟨S', Nd', _, _, _, hf, _⟩ := step.2.2.2.2 S Nd hw hd
  apply phase2_tx_header_world_frame s _ S Nd _ tx off ha hw ht hoff ho8 hf
  · intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact htx
  · intro region hm hz
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at hz
    omega

/-- A guarded copy always has a live record array, so conditional input separation applies. -/
theorem phase2_packed_guarded_record_separation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hsep : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys" + 52 * locN s "k", 20) ∧
    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys" + 52 * locN s "k" + 20, 32) := by
  apply phase2_packed_guarded_input_disjoint s hp
  apply hsep
  have hi := hp.2.2.1
  omega

/-- Buffer/input separation persists when the copy preserves its scalar metadata. -/
theorem phase2_packed_input_separation_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String), locN post n = locN s n)
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (ht : Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hr : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    Disj (locN post "tx", 384)
      (locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    Disj (memW post (locN post "tx" + 208), 24 * memW post (locN post "tx" + 216))
      (locN post "al_keys", (locN post "nkeys" * 52 + 8 + 7) / 8 * 8) := by
  rw [hl "tx" (by simp), hl "al_keys" (by simp), hl "nkeys" (by simp), hh.1, hh.2]
  exact ⟨ht, hr⟩

/-- A positive-length copy preserves the transaction witness under its world-frame guarantees. -/
theorem phase2_memcpy_tx_survives {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat)
    (ha : ArenaReady s) (hp : GuestInv post) (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post
      (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s]) (heapFree s))
    (hd : Disj (locN s "tx", 384) (locN s "dst", locN s "n"))
    (hr : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (locN s "dst", locN s "n"))
    (hn : 0 < locN s "n")
    (hl : post.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx")) :
    TxAccessListAt post S' Nd' (locN post "tx") := by
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" :=
    (phase2_copy_globals_heap_eq s post hg).symm.le
  apply R16Shards.PtxP1.txAccessListOK_survives_step ha hp hh hw _ ho hf ht _ _ hl
  · intro region hm hz
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at hz
    omega
  · intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hd
  · intro hpos region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hr hpos

/-- Bind the three evaluated arguments at the concrete memcpy entry. -/
theorem phase2_memcpy_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src len : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret)) :
    ∃ d v n, evalAt s dst = some d ∧ evalAt s src = some v ∧ evalAt s len = some n ∧
      callee.lookup (ofString "dst") = some d ∧
      callee.lookup (ofString "src") = some v ∧ callee.lookup (ofString "n") = some n := by
  apply R16Shards.PtxP1.params_three_values s (ofString "memcpy")
    (ofString "dst") (ofString "src") (ofString "n") .one .one .one
    (sourceFunctionEntry Guest.Software.guestFn_memcpy).2.2.1
    (sourceFunctionEntry Guest.Software.guestFn_memcpy).2.2.2 _
    dst src len vs body callee ret ha hl
  rw [hc]
  change originalRuntimeCode.lookup (ofString "memcpy") =
    some (sourceFunctionEntry Guest.Software.guestFn_memcpy).2
  exact originalRuntimeCode_lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

/-- One memcpy frame preserves both fields used to locate the access-list records. -/
theorem phase2_memcpy_access_metadata_contract (h : PtxCallees) :
    FunSpec WorldOK
      (fun s r post => Resumes r →
        ∀ S Nd tx, ArenaOK s → WorldTypedWith s S Nd →
          TxAccessListAt s S Nd tx →
          IvlsDisj [(locN s "dst", locN s "n")] (worldTypedIvls s S Nd) →
          Disj (tx, 384) (locN s "dst", locN s "n") → 0 < locN s "n" →
          memW post (tx + 208) = memW s (tx + 208) ∧
          memW post (tx + 216) = memW s (tx + 216))
      (ofString "memcpy") := by
  obtain ⟨params, body, ret, hl, hs⟩ := phase2_memcpy_header_contract h
  refine ⟨params, body, ret, hl, ?_⟩
  intro F s hc hp he hn hr S Nd tx ha hw ht hd htx hlen
  exact ⟨hs s hc hp he hn hr S Nd tx 208 ha hw ht (by decide) (by decide) hd htx hlen,
    hs s hc hp he hn hr S Nd tx 216 ha hw ht (by decide) (by decide) hd htx hlen⟩

/-- Word-valued copy arguments determine the concrete destination and length at entry. -/
theorem phase2_memcpy_entry_destination {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src len : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (d n : BitVec 64) (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (hd : evalAt s dst = some (.val (.word d)))
    (hn : evalAt s len = some (.val (.word n))) :
    locN { s with locals := callee, clock := s.clock - 1 } "dst" = d.toNat ∧
    locN { s with locals := callee, clock := s.clock - 1 } "n" = n.toNat := by
  obtain ⟨dv, sv, nv, heD, _, heN, hcD, _, hcN⟩ :=
    phase2_memcpy_arguments s dst src len vs body callee ret hc ha hl
  rw [hd] at heD
  rw [hn] at heN
  cases heD
  cases heN
  simp [locN, hcD, hcN]

/-- Successful word-valued memcpy arguments determine the callee's numeric parameters. -/
theorem phase2_memcpy_word_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst src len : ExpHOL 64) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (d v n : BitVec 64) (hc : s.code = originalRuntimeCode)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (hd : evalAt s dst = some (.val (.word d)))
    (hv : evalAt s src = some (.val (.word v)))
    (hn : evalAt s len = some (.val (.word n))) :
    locN (callEntryStateHOLFinite s callee) "dst" = d.toNat ∧
    locN (callEntryStateHOLFinite s callee) "src" = v.toNat ∧
    locN (callEntryStateHOLFinite s callee) "n" = n.toNat := by
  obtain ⟨d', v', n', hd', hv', hn', hpd, hpv, hpn⟩ :=
    phase2_memcpy_arguments s dst src len vs body callee ret hc ha hl
  rw [hd] at hd'
  rw [hv] at hv'
  rw [hn] at hn'
  cases hd'
  cases hv'
  cases hn'
  simp [locN, callEntryStateHOLFinite, hpd, hpv, hpn]

/-- Copy framing restores packed readiness and the transaction witness together. -/
theorem phase2_packed_ready_memcpy_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat)
    (hready : PtxPackedKeysReady s) (ha : ArenaReady s) (hp : GuestInv post)
    (hg : GlobalsKept [] s post) (hm : ∀ a, s.memaddrs a → post.memaddrs a)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post
      (worldOwned s S Nd ++ [(locN s "dst", locN s "n")] ++ [freeGap s]) (heapFree s))
    (hd : Disj (locN s "tx", 384) (locN s "dst", locN s "n"))
    (hr : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
        (locN s "dst", locN s "n"))
    (hn : 0 < locN s "n")
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String),
      post.locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedKeysReady post := by
  have ht' := phase2_memcpy_tx_survives s post S Nd S' Nd' ha hp hg hw ht ho hf
    hd hr hn (hl "tx" (by simp))
  apply phase2_packed_ready_owned_growth s post S Nd S' Nd' hready _ hg hm hw' ht' hs ho
  intro n hn
  exact hl n (by simp only [List.mem_cons] at hn ⊢; tauto)

/-- A callee's memory frame transfers unchanged to the restored caller state. -/
theorem phase2_memcpy_restore_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (keep : List Ivl) (fresh : Ivl)
    (hf : FrameOutside (callEntryStateHOLFinite s callee) post keep fresh) :
    FrameOutside s { post with locals := s.locals } keep fresh := by
  intro a hk hn
  exact hf a hk hn

/-- Domain preservation at memcpy entry transfers to the restored caller state. -/
theorem phase2_memcpy_restore_domain {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hd : ∀ a, (callEntryStateHOLFinite s callee).memaddrs a → post.memaddrs a) :
    ∀ a, s.memaddrs a → ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F).memaddrs a := by
  intro a ha
  exact hd a ha

/-- Restoring caller locals retains the callee's global-preservation guarantee. -/
theorem phase2_memcpy_restore_globals {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hg : GlobalsKept [] (callEntryStateHOLFinite s callee) post) :
    GlobalsKept [] s { post with locals := s.locals } := by
  intro k hk
  exact hg k hk

/-- Restoring caller locals leaves every caller numeric local unchanged. -/
theorem phase2_memcpy_restore_locals {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (name : String) :
    locN ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) name =
      locN s name := by
  rfl

/-- Apply header preservation to a concrete, resuming memcpy evaluation. -/
theorem phase2_memcpy_eval_headers (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat) (tx : Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (ht : TxAccessListAt (callEntryStateHOLFinite s callee) S Nd tx)
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hsep : Disj (tx, 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    memW post (tx + 208) = memW s (tx + 208) ∧
    memW post (tx + 216) = memW s (tx + 216) := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup (phase2_memcpy_access_metadata_contract h)
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  exact hs hr S Nd tx ha hw ht hd hsep hlen

/-- A resuming concrete copy supplies a shared post-world and restored-caller frame. -/
theorem phase2_memcpy_eval_world_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd)) :
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧
      OwnedGrows (callEntryStateHOLFinite s callee) post
        (worldOwned (callEntryStateHOLFinite s callee) S Nd) (worldOwned post S' Nd') ∧
      FrameOutside s { post with locals := s.locals }
        (worldOwned (callEntryStateHOLFinite s callee) S Nd ++
          [(locN (callEntryStateHOLFinite s callee) "dst",
            locN (callEntryStateHOLFinite s callee) "n")] ++
          [freeGap (callEntryStateHOLFinite s callee)])
        (heapFree (callEntryStateHOLFinite s callee)) := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup (phase2_memcpy_world_frame_contract h)
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  obtain ⟨S', Nd', hw', ho, hf⟩ := hs hr S Nd hw hd
  exact ⟨S', Nd', hw', ho, phase2_memcpy_restore_frame s post callee _ _ hf⟩

/-- Apply the concrete memcpy global guarantee after restoring caller locals. -/
theorem phase2_memcpy_eval_globals (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee)) :
    GlobalsKept [] s { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup (phase2_memcpy_globals_contract h)
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  exact phase2_memcpy_restore_globals s post callee (hs hr)

/-- Guest invariants discharge the memory-domain premise of packed-copy restoration. -/
theorem phase2_memcpy_domain_of_guestInv {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hs : GuestInv s) (hp : GuestInv post) :
    ∀ a, s.memaddrs a → post.memaddrs a := by
  intro a ha
  rw [hp.memaddrs, ← hs.memaddrs]
  exact ha

/-- A concrete resuming memcpy produces an arena-ready post-state. -/
theorem phase2_memcpy_eval_arena (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee)) :
    ArenaReady post := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  exact (hs hr).1

/-- A concrete resuming copy supplies the invariant, domain and global guarantees together. -/
theorem phase2_memcpy_eval_state (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee)) (hi : GuestInv s) :
    GuestInv post ∧ GlobalsKept [] s { post with locals := s.locals } ∧
      (∀ a, s.memaddrs a → post.memaddrs a) := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  exact ⟨step.1.1, phase2_memcpy_restore_globals s post callee step.2.2.1,
    phase2_memcpy_domain_of_guestInv s post hi step.1.1⟩

/-- Concrete memcpy evaluation preserves every live count in the caller's record array. -/
theorem phase2_memcpy_eval_counts (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat) (tx : Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (ht : TxAccessListAt (callEntryStateHOLFinite s callee) S Nd tx)
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hsep : Disj (memW s (tx + 208), 24 * memW s (tx + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    ∀ i, i < memW s (tx + 216) →
      memW post (memW s (tx + 208) + 24 * i + 16) =
        memW s (memW s (tx + 208) + 24 * i + 16) := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup (phase2_memcpy_count_contract h)
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  intro i hi
  exact hs hr S Nd tx i ha hw ht hi hd hsep hlen

/-- Header and live-count preservation restore guarded indices in the caller state. -/
theorem phase2_packed_copy_restore_indices {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s)
    (hr : PtxPackedKeysReady { post with locals := s.locals })
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  apply phase2_packed_copy_live_frame s _ hp hr
  · intro n hn
    rfl
  · exact hh.2
  · intro i hi
    change memW post (memW post (locN s "tx" + 208) + 24 * i + 16) = _
    rw [hh.1]
    exact hm i hi

/-- The concrete copy metadata contracts restore the guarded caller indices. -/
theorem phase2_memcpy_eval_guarded (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (ht : TxAccessListAt (callEntryStateHOLFinite s callee) S Nd (locN s "tx"))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n")
    (hindex : PtxPackedCopyIndex s)
    (hready : PtxPackedKeysReady { post with locals := s.locals }) :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  apply phase2_packed_copy_metadata_frame s _ hindex hready (fun _ _ => rfl)
  · exact phase2_memcpy_eval_headers h s post vs body callee ret r S Nd (locN s "tx")
      hc hl he hn hr hp ha hw ht hd htx hlen
  · exact phase2_memcpy_eval_counts h s post vs body callee ret r S Nd (locN s "tx")
      hc hl he hn hr hp ha hw ht hd hrec hlen

/-- Retain input separation alongside guarded indices for the second copy call. -/
def PtxPackedSeparatedCopy {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedCopyIndex s ∧
  Disj (locN s "tx", 384)
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
  Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

/-- Restoring metadata retains all spatial premises needed by the next copy. -/
theorem phase2_packed_separated_restore {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (hp : PtxPackedSeparatedCopy s)
    (hr : PtxPackedKeysReady { post with locals := s.locals })
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  refine ⟨phase2_packed_copy_restore_indices s post hp.1 hr hh hm, ?_⟩
  exact phase2_packed_input_separation_frame s _ (fun _ _ => rfl) hh hp.2.1 hp.2.2

/-- Restored caller metadata carries buffer separation to the next copy. -/
theorem phase2_packed_restore_input_separation {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (ht : Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hr : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)) :
    let out := { post with locals := s.locals }
    Disj (locN out "tx", 384)
      (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    Disj (memW out (locN out "tx" + 208), 24 * memW out (locN out "tx" + 216))
      (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8) := by
  exact phase2_packed_input_separation_frame s _ (fun _ _ => rfl) hh ht hr

/-- Restore packed readiness across a copy with its evaluated destination and length. -/
theorem phase2_packed_ready_restored_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat) (dst len : Nat)
    (hp : PtxPackedKeysReady s) (ha : ArenaReady s) (hpost : GuestInv post)
    (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ [(dst, len)] ++ [freeGap s]) (heapFree s))
    (htx : Disj (locN s "tx", 384) (dst, len))
    (hrec : 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len))
    (hlen : 0 < len) :
    PtxPackedKeysReady { post with locals := s.locals } := by
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" :=
    (phase2_copy_globals_heap_eq s post hg).symm.le
  have hz : ∀ region ∈ ([(dst, len)] : List Ivl), region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at he
    omega
  have ht' := R16Shards.PtxP1.txAccessListOK_survives_step ha hpost hh hw hz ho hf ht
    (by simpa only [List.mem_singleton, forall_eq] using htx)
    (by simpa only [List.mem_singleton, forall_eq] using hrec)
    (locals := s.locals) rfl
  apply phase2_packed_ready_owned_growth s { post with locals := s.locals }
    S Nd S' Nd' hp (fun _ _ => rfl) hg
    (phase2_memcpy_domain_of_guestInv s post ha.1 hpost)
    ((worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw') ht' hs
  exact ho

/-- A copy's world frame and metadata preservation restore the full guarded invariant. -/
theorem phase2_packed_guarded_restored_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat) (dst len : Nat)
    (hp : PtxPackedCopyIndex s) (ha : ArenaReady s) (hpost : GuestInv post)
    (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ [(dst, len)] ++ [freeGap s]) (heapFree s))
    (htx : Disj (locN s "tx", 384) (dst, len))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len))
    (hlen : 0 < len)
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) ∧
      memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216))
    (hm : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16)) :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  have hready := phase2_packed_ready_restored_frame s post S Nd S' Nd' dst len
    hp.1 ha hpost hg hw hw' ht hs ho hf htx (fun _ => hrec) hlen
  exact phase2_packed_copy_restore_indices s post hp hready hh hm

/-- Concrete copy evaluation restores caller readiness without a post-state witness premise. -/
theorem phase2_memcpy_eval_ready (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hready : PtxPackedKeysReady s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedKeysReady { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe hd
  exact phase2_packed_ready_restored_frame s post S Nd S' Nd' _ _ hready ha
    step.1.1 step.2.2.1 hw hw' ht hsep ho hf htx (fun _ => hrec) hlen

/-- A separated positive copy frame alone supplies the metadata needed for guarded restoration. -/
theorem phase2_packed_guarded_of_copy_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat) (dst len : Nat)
    (hp : PtxPackedCopyIndex s) (ha : ArenaReady s) (hpost : GuestInv post)
    (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ [(dst, len)] ++ [freeGap s]) (heapFree s))
    (htx : Disj (locN s "tx", 384) (dst, len))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len))
    (hlen : 0 < len) :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  have hz : ∀ region ∈ ([(dst, len)] : List Ivl), region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at he
    omega
  have htx' : ∀ region ∈ ([(dst, len)] : List Ivl), Disj (locN s "tx", 384) region := by
    simpa only [List.mem_singleton, forall_eq] using htx
  have hrec' : ∀ region ∈ ([(dst, len)] : List Ivl),
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) region := by
    simpa only [List.mem_singleton, forall_eq] using hrec
  apply phase2_packed_guarded_restored_frame s post S Nd S' Nd' dst len hp ha hpost hg
    hw hw' ht hs ho hf htx hrec hlen
  · exact ⟨phase2_tx_header_world_frame s post S Nd _ _ 208 ha.2 hw ht
      (by decide) (by decide) hf htx' hz,
      phase2_tx_header_world_frame s post S Nd _ _ 216 ha.2 hw ht
      (by decide) (by decide) hf htx' hz⟩
  · intro i hi
    exact phase2_tx_count_world_frame s post S Nd _ _ i ha.2 hw ht hi hf hrec' hz

/-- Scratch declarations retain the strengthened spatial copy invariant. -/
theorem phase2_packed_separated_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hp : PtxPackedSeparatedCopy s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "j", "k"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedSeparatedCopy { s with locals := locals, clock := clock } := by
  refine ⟨phase2_packed_copy_with_locals s locals clock hp.1 hl, ?_⟩
  have ht : locN { s with locals := locals, clock := clock } "tx" = locN s "tx" := by
    simp [locN, hl "tx" (by simp)]
  have ha : locN { s with locals := locals, clock := clock } "al_keys" = locN s "al_keys" := by
    simp [locN, hl "al_keys" (by simp)]
  have hn : locN { s with locals := locals, clock := clock } "nkeys" = locN s "nkeys" := by
    simp [locN, hl "nkeys" (by simp)]
  simpa only [ht, ha, hn, memW] using hp.2

/-- A concrete resuming copy preserves guarded indices using only pre-state spatial facts. -/
theorem phase2_memcpy_eval_preserves (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedCopyIndex s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe hd
  exact phase2_packed_guarded_of_copy_frame s post S Nd S' Nd' _ _ hi ha
    step.1.1 step.2.2.1 hw hw' ht hsep ho hf htx hrec hlen

/-- Concrete memcpy preserves guarded indices without assuming post-copy readiness. -/
theorem phase2_memcpy_eval_guarded_from_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hindex : PtxPackedCopyIndex s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedCopyIndex { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe hd
  exact phase2_packed_guarded_of_copy_frame s post S Nd S' Nd' _ _ hindex ha
    step.1.1 step.2.2.1 hw hw' ht hsep ho hf htx hrec hlen

/-- A copy frame preserves the strengthened invariant, including the next call's separation. -/
theorem phase2_packed_separated_of_copy_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat) (dst len : Nat)
    (hp : PtxPackedSeparatedCopy s) (ha : ArenaReady s) (hpost : GuestInv post)
    (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ [(dst, len)] ++ [freeGap s]) (heapFree s))
    (htx : Disj (locN s "tx", 384) (dst, len))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len))
    (hlen : 0 < len) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  refine ⟨phase2_packed_guarded_of_copy_frame s post S Nd S' Nd' dst len hp.1 ha
    hpost hg hw hw' ht hs ho hf htx hrec hlen, ?_⟩
  have hz : ∀ region ∈ ([(dst, len)] : List Ivl), region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at he
    omega
  have htx' : ∀ region ∈ ([(dst, len)] : List Ivl), Disj (locN s "tx", 384) region := by
    simpa only [List.mem_singleton, forall_eq] using htx
  apply phase2_packed_restore_input_separation s post _ hp.2.1 hp.2.2
  exact ⟨phase2_tx_header_world_frame s post S Nd _ _ 208 ha.2 hw ht
    (by decide) (by decide) hf htx' hz,
    phase2_tx_header_world_frame s post S Nd _ _ 216 ha.2 hw ht
    (by decide) (by decide) hf htx' hz⟩

/-- A resuming copy preserves guarded indices and input separation for the following copy. -/
theorem phase2_memcpy_eval_separated (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe hd
  exact phase2_packed_separated_of_copy_frame s post S Nd S' Nd' _ _ hi ha
    step.1.1 step.2.2.1 hw hw' ht hsep ho hf htx hrec hlen

/-- Concrete memcpy retains the separation needed by the following copy. -/
theorem phase2_memcpy_eval_separated_from_frame (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hindex : PtxPackedSeparatedCopy s)
    (hw : WorldTypedWith s S Nd) (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hsep : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe hd
  exact phase2_packed_separated_of_copy_frame s post S Nd S' Nd' _ _ hindex ha
    step.1.1 step.2.2.1 hw hw' ht hsep ho hf htx hrec hlen

/-- Both calls and readiness restoration use one common pre-copy world witness. -/
theorem phase2_packed_copy_joint_witness {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedCopyIndex s) :
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned s S Nd) ∧
      IvlsDisj [(locN s "al_keys" + 52 * locN s "k", 20),
        (locN s "al_keys" + 52 * locN s "k" + 20, 32)] (worldTypedIvls s S Nd) := by
  obtain ⟨S, Nd, hw, ht, hd⟩ := hp.1.2.2.2.2
  refine ⟨S, Nd, hw, ht, hd, phase2_packed_typed_of_owned s S Nd _ ?_⟩
  intro dest hdest region hregion
  have hb := hd (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
    (by simp) region hregion
  have hs := phase2_packed_guarded_input_disjoint s hp region (disj_symm hb)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdest
  rcases hdest with rfl | rfl
  · exact disj_symm hs.1
  · exact disj_symm hs.2

/-- Either packed copy destination has all spatial premises under one world witness. -/
theorem phase2_packed_copy_spatial_premises {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedSeparatedCopy s)
    (dest : Ivl)
    (hdest : dest ∈ [(locN s "al_keys" + 52 * locN s "k", 20),
      (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned s S Nd) ∧
      IvlsDisj [dest] (worldTypedIvls s S Nd) ∧
      Disj (locN s "tx", 384) dest ∧
      Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) dest ∧
      0 < dest.2 := by
  obtain ⟨S, Nd, hw, ht, hs, hd⟩ := phase2_packed_copy_joint_witness s hp.1
  refine ⟨S, Nd, hw, ht, hs, ?_, ?_⟩
  · intro region hm other ho
    simp only [List.mem_singleton] at hm
    subst region
    exact hd dest hdest other ho
  · have htx := phase2_packed_guarded_input_disjoint s hp.1 _ hp.2.1
    have hrec := phase2_packed_guarded_input_disjoint s hp.1 _ hp.2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdest
    rcases hdest with rfl | rfl
    · exact ⟨htx.1, hrec.1, by change 0 < (20 : Nat); decide⟩
    · exact ⟨htx.2, hrec.2, by change 0 < (32 : Nat); decide⟩

/-- Either concrete packed destination preserves the separated caller invariant. -/
theorem phase2_memcpy_packed_eval (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
        [(locN s "al_keys" + 52 * locN s "k", 20),
         (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  obtain ⟨S, Nd, hw, ht, hs, hd, htx, hrec, hlen⟩ :=
    phase2_packed_copy_spatial_premises s hi _ hdest
  exact phase2_memcpy_eval_separated h s post vs body callee ret r S Nd
    hc hl he hn hr hp ha hi hw ht hs hd htx hrec hlen

/-- Either concrete packed copy preserves the invariant without external spatial premises. -/
theorem phase2_memcpy_eval_packed_destination (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  obtain ⟨S, Nd, hw, ht, hs, hd, htx, hrec, hlen⟩ :=
    phase2_packed_copy_spatial_premises s hi _ hdest
  exact phase2_memcpy_eval_separated h s post vs body callee ret r S Nd hc hl he hn hr
    hp ha hi hw ht hs hd htx hrec hlen

/-- Evaluated word arguments connect either packed destination to copy preservation. -/
theorem phase2_memcpy_packed_word_eval (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d v n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hd : evalAt s dst = some (.val (.word d)))
    (hv : evalAt s src = some (.val (.word v)))
    (hnum : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  obtain ⟨hdst, _, hlen⟩ := phase2_memcpy_word_arguments s dst src len vs body callee ret
    d v n hc hargs hl hd hv hnum
  apply phase2_memcpy_packed_eval h s post vs body callee ret r hc hl he hn hr hp ha hi
  rw [hdst, hlen]
  exact hpair

/-- Evaluated caller arguments suffice to preserve either packed-copy destination. -/
theorem phase2_memcpy_packed_arguments_preserve (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hd : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hd hlen
  apply phase2_memcpy_eval_packed_destination h s post vs body callee ret r hc hl he hn hr hp ha hi
  change (locN { s with locals := callee, clock := s.clock - 1 } "dst",
    locN { s with locals := callee, clock := s.clock - 1 } "n") ∈ _
  rw [hentry.1, hentry.2]
  exact hpair

/-- The concrete 20-byte address copy preserves the separated packed invariant. -/
theorem phase2_packed_address_copy_eval (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (src : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (base k : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hbase : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  apply phase2_memcpy_packed_arguments_preserve h s post _ src (.const 20) vs body callee ret r
    (base + k * 52) 20 hc hargs hl he hn hr hp ha hi
    (phase2_packed_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact])
  rw [phase2_packed_destination_toNat s hi.1 base k hbase hk hb]
  simp

/-- The concrete 32-byte key copy preserves the separated packed invariant. -/
theorem phase2_packed_key_copy_eval (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (src : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (base k : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hbase : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  apply phase2_memcpy_packed_arguments_preserve h s post _ src (.const 32) vs body callee ret r
    (base + k * 52 + 20) 32 hc hargs hl he hn hr hp ha hi
    (phase2_packed_key_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact])
  rw [phase2_packed_key_destination_toNat s hi.1 base k hbase hk hb]
  simp

/-- The concrete 32-byte storage-key copy preserves the separated packed invariant. -/
theorem phase2_packed_storage_copy_eval (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (src : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (base k : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.var .local (ofString "al_keys"),
        .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hbase : s.locals.lookup (ofString "al_keys") = some (.val (.word base)))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    PtxPackedSeparatedCopy { post with locals := s.locals } := by
  apply phase2_memcpy_packed_arguments_preserve h s post _ src (.const 32) vs body callee ret r
    (base + k * 52 + 20) 32 hc hargs hl he hn hr hp ha hi
    (phase2_packed_key_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact])
  rw [phase2_packed_key_destination_toNat s hi.1 base k hbase hk hb]
  simp

/-- The inclusive inner-loop invariant retains separation for the next guarded iteration. -/
def PtxPackedSeparatedInner {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedInnerInv s ∧
  Disj (locN s "tx", 384)
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
  Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

/-- Advancing both copy counters preserves input separation and the inclusive loop invariant. -/
theorem phase2_packed_separated_counters {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedSeparatedCopy s) :
    let post := setVarHOLFinite (ofString "j")
      (.val (.word (BitVec.ofNat 64 (locN s "j" + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) s)
    PtxPackedSeparatedInner post := by
  dsimp only
  refine ⟨phase2_packed_inner_update_indices s hp.1, ?_⟩
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "j" ≠ ofString "tx" from by decide,
    show ofString "k" ≠ ofString "tx" from by decide,
    show ofString "j" ≠ ofString "al_keys" from by decide,
    show ofString "k" ≠ ofString "al_keys" from by decide,
    show ofString "j" ≠ ofString "nkeys" from by decide,
    show ofString "k" ≠ ofString "nkeys" from by decide] using hp.2

/-- Call-level preservation for the concrete packed storage-key copy. -/
theorem phase2_packed_storage_copy_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedSeparatedCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  exact phase2_packed_storage_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) hp.1.1 hp.2.1 hbase hk hp.2.2.2

/-- A true inner guard recovers all premises for the next pair of copies. -/
theorem phase2_packed_separated_inner_guarded {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxPackedSeparatedInner s)
    (hg : locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    PtxPackedSeparatedCopy s :=
  ⟨phase2_packed_inner_guarded hp.1 hg, hp.2⟩

/-- A false inner guard fixes the flattened index while retaining both input separations. -/
theorem phase2_packed_separated_inner_exit {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxPackedSeparatedInner s)
    (hg : ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN s "k" = phase2_key_prefix s (locN s "i" + 1) ∧
    Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) :=
  ⟨(phase2_packed_inner_exit hp.1 hg).2, hp.2⟩

/-- Call-level preservation for the concrete packed address copy. -/
theorem phase2_packed_address_copy_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedSeparatedCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  exact phase2_packed_address_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) hp.1.1 hp.2.1 hbase hk hp.2.2.2

/-- The resuming copy retains arena readiness and the heap bound for the next call. -/
theorem phase2_memcpy_eval_next_arena (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    ArenaReady { post with locals := s.locals } ∧
      globN { post with locals := s.locals } "heap_ptr" ≤ 2 ^ 64 := by
  have ha := phase2_memcpy_eval_arena h s post vs body callee ret r hc hl he hn hr hp
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret r hc hl he hn hr hp
  refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr ha, ?_⟩
  rw [phase2_copy_globals_heap_eq s _ hg]
  exact hb

/-- The concrete counter statements retain the strengthened inner invariant. -/
theorem phase2_packed_separated_counters_hoare :
    Hoare PtxPackedSeparatedCopy
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedSeparatedInner s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, PtxPackedSeparatedCopy before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.1).1
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
      have hb := (phase2_packed_copy_counter_bounds hp.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => phase2_packed_separated_counters before hp
    · exact fun _ _ hr => by cases hr

/-- Restored copy calls preserve scalar witnesses and the heap bound needed by sequencing. -/
theorem phase2_memcpy_next_scalar_facts {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (names : List String)
    (hw : ∀ n ∈ names, ∃ w : BitVec 64,
      s.locals.lookup (ofString n) = some (.val (.word w)))
    (hg : GlobalsKept [] s { post with locals := s.locals })
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    (∀ n ∈ names, ∃ w : BitVec 64,
      ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F).locals.lookup
        (ofString n) = some (.val (.word w))) ∧
      globN { post with locals := s.locals } "heap_ptr" ≤ 2 ^ 64 := by
  refine ⟨hw, ?_⟩
  rw [phase2_copy_globals_heap_eq s _ hg]
  exact hb

/-- Packed readiness supplies world typing once arena readiness has been restored. -/
theorem phase2_packed_ready_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (ha : ArenaReady s) (hp : PtxPackedKeysReady s) : WorldOK s := by
  obtain ⟨S, Nd, hw, _, _⟩ := hp.2.2.2.2
  exact ⟨ha, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw⟩⟩

/-- Copy postconditions recover the complete precondition of the following packed call. -/
theorem phase2_packed_next_call_pre {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (ha : ArenaReady { post with locals := s.locals })
    (hp : PtxPackedSeparatedCopy { post with locals := s.locals })
    (hk : ∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hg : GlobalsKept [] s { post with locals := s.locals })
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    let out := { post with locals := s.locals }
    WorldOK out ∧ PtxPackedSeparatedCopy out ∧
      (∃ k : BitVec 64, out.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN out "heap_ptr" ≤ 2 ^ 64 := by
  refine ⟨phase2_packed_ready_worldOK _ ha hp.1.1, hp, hk, ?_⟩
  rw [phase2_copy_globals_heap_eq s _ hg]
  exact hb

/-- The address copy retains the entire precondition needed by the storage-key call. -/
theorem phase2_packed_address_copy_next_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → WorldOK t ∧ PtxPackedSeparatedCopy t ∧
        (∃ k : BitVec 64, t.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        globN t "heap_ptr" ≤ 2 ^ 64) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1 callee
  have hcopy := phase2_packed_address_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1 hp.2.1 hbase hk hp.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  exact phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.2.2.2

/-- The two concrete packed-copy calls compose without a post-state readiness assumption. -/
theorem phase2_packed_copy_pair_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32]))
      (fun r t => r = none → PtxPackedSeparatedCopy t) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_next_hoare h addressSrc)
    (phase2_packed_storage_copy_hoare h keySrc)

/-- The concrete copy pair followed by both increments establishes the inclusive invariant. -/
theorem phase2_packed_pair_counters_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32]))
        (.seq
          (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
          (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))
      (fun r t => r = none → PtxPackedSeparatedInner t) := by
  exact Hoare.seq_fall (phase2_packed_copy_pair_hoare h addressSrc keySrc)
    phase2_packed_separated_counters_hoare

/-- The storage-key copy retains the world and scalar facts needed for iteration. -/
theorem phase2_packed_storage_copy_next_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → WorldOK t ∧ PtxPackedSeparatedCopy t ∧
        (∃ k : BitVec 64, t.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        globN t "heap_ptr" ≤ 2 ^ 64) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1 callee
  have hcopy := phase2_packed_storage_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1 hp.2.1 hbase hk hp.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  exact phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.2.2.2

/-- Right-associated copy statements and increments establish the inner invariant. -/
theorem phase2_packed_copy_body_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r t => r = none → PtxPackedSeparatedInner t) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_next_hoare h addressSrc)
    (Hoare.seq_fall (phase2_packed_storage_copy_hoare h keySrc)
      phase2_packed_separated_counters_hoare)

/-- Right-associated source-order composition of the copy calls and counter updates. -/
theorem phase2_packed_copy_source_body_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r t => r = none → PtxPackedSeparatedInner t) := by
  exact phase2_packed_copy_body_hoare h addressSrc keySrc

/-- Counter updates preserve the world and establish word witnesses for the next guard. -/
theorem phase2_packed_counters_iteration_state {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hw : WorldOK s)
    (hp : PtxPackedSeparatedCopy s) (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    let post := setVarHOLFinite (ofString "j")
      (.val (.word (BitVec.ofNat 64 (locN s "j" + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) s)
    WorldOK post ∧ PtxPackedSeparatedInner post ∧
      (∃ k : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      (∃ j : BitVec 64, post.locals.lookup (ofString "j") = some (.val (.word j))) ∧
      globN post "heap_ptr" ≤ 2 ^ 64 := by
  dsimp only
  refine ⟨?_, phase2_packed_separated_counters s hp, ?_, ?_, hb⟩
  · obtain ⟨ha, S, ht⟩ := hw
    exact ⟨(arenaReady_with_locals s _ s.clock).mpr ha, S,
      (worldTyped_with_locals s _ s.clock S).mpr ht⟩
  · refine ⟨BitVec.ofNat 64 (locN s "k" + 1), ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "k" from by decide]
  · refine ⟨BitVec.ofNat 64 (locN s "j" + 1), ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- Counter updates retain world readiness and install word witnesses for both counters. -/
theorem phase2_packed_counter_state {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedSeparatedCopy s) (ha : ArenaReady s)
    (hb : globN s "heap_ptr" ≤ 2 ^ 64) :
    let post := setVarHOLFinite (ofString "j")
      (.val (.word (BitVec.ofNat 64 (locN s "j" + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word (BitVec.ofNat 64 (locN s "k" + 1)))) s)
    WorldOK post ∧ PtxPackedSeparatedInner post ∧
      (∃ k : BitVec 64, post.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      (∃ j : BitVec 64, post.locals.lookup (ofString "j") = some (.val (.word j))) ∧
      globN post "heap_ptr" ≤ 2 ^ 64 := by
  dsimp only
  have hi := phase2_packed_separated_counters s hp
  refine ⟨phase2_packed_ready_worldOK _ ?_ hi.1.1, hi, ?_, ?_, hb⟩
  · exact (arenaReady_with_locals s _ s.clock).mpr ha
  · refine ⟨BitVec.ofNat 64 (locN s "k" + 1), ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "k" from by decide]
  · refine ⟨BitVec.ofNat 64 (locN s "j" + 1), ?_⟩
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

/-- The inclusive iteration state supplies the complete copy precondition under its guard. -/
theorem phase2_packed_iteration_guard_pre {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hp : WorldOK s ∧ PtxPackedSeparatedInner s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
    (hg : locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64 := by
  exact ⟨hp.1, phase2_packed_separated_inner_guarded hp.2.1 hg,
    hp.2.2.1, hp.2.2.2.2⟩

/-- The copy pair preserves all premises needed before the counter updates. -/
theorem phase2_packed_copy_pair_next_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32]))
      (fun r t => r = none → WorldOK t ∧ PtxPackedSeparatedCopy t ∧
        (∃ k : BitVec 64, t.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        globN t "heap_ptr" ≤ 2 ^ 64) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_next_hoare h addressSrc)
    (phase2_packed_storage_copy_next_hoare h keySrc)

/-- Counter execution restores the world, word witnesses and bound needed by iteration. -/
theorem phase2_packed_counters_full_hoare :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → WorldOK s ∧ PtxPackedSeparatedInner s ∧
        (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
        globN s "heap_ptr" ≤ 2 ^ 64) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, WorldOK before ∧
    PtxPackedSeparatedCopy before ∧ globN before "heap_ptr" ≤ 2 ^ 64 ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.2.1.1).1
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v hb he
      have heq : w = BitVec.ofNat 64 (locN s "k" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨s, hp.1, hp.2.1, hp.2.2.2, rfl⟩
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      obtain ⟨before, hw, hp, hbound, rfl⟩ := hp
      have hj : locN (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) "j" =
          locN before "j" := by
        simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "k" ≠ ofString "j" by decide]
      have hb := (phase2_packed_copy_counter_bounds hp.1).2
      obtain ⟨w, rfl, hew⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hew, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => phase2_packed_counters_iteration_state before hw hp hbound
    · exact fun _ _ hr => by cases hr

/-- Counter statements preserve the complete state needed for another inner iteration. -/
theorem phase2_packed_counters_next_hoare :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → WorldOK s ∧ PtxPackedSeparatedInner s ∧
        (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
        globN s "heap_ptr" ≤ 2 ^ 64) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, ArenaReady before ∧
    PtxPackedSeparatedCopy before ∧ globN before "heap_ptr" ≤ 2 ^ 64 ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.2.1.1).1
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "k" v hb he
      have heq : w = BitVec.ofNat 64 (locN s "k" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨s, hp.1.1, hp.2.1, hp.2.2.2, rfl⟩
    · exact fun _ _ hr => by cases hr
  · apply Hoare.assign
    · intro F s v hp he
      obtain ⟨before, ha, hp, hbound, rfl⟩ := hp
      have hj : locN (setVarHOLFinite (ofString "k")
          (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before) "j" =
          locN before "j" := by
        simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          show ofString "k" ≠ ofString "j" by decide]
      have hb := (phase2_packed_copy_counter_bounds hp.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => phase2_packed_counter_state before hp ha hbound
    · exact fun _ _ hr => by cases hr

/-- The source-ordered copy body restores the complete inclusive iteration state. -/
theorem phase2_packed_body_iteration_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ PtxPackedSeparatedCopy s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → WorldOK s ∧ PtxPackedSeparatedInner s ∧
        (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
        (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
        globN s "heap_ptr" ≤ 2 ^ 64) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_next_hoare h addressSrc)
    (Hoare.seq_fall (phase2_packed_storage_copy_next_hoare h keySrc)
      phase2_packed_counters_full_hoare)

/-- Decrementing the loop clock preserves the complete inclusive iteration state. -/
theorem phase2_packed_iteration_decClock {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hp : WorldOK s ∧ PtxPackedSeparatedInner s ∧
      (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
      (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
      globN s "heap_ptr" ≤ 2 ^ 64) :
    WorldOK (decClockHOLFinite s) ∧ PtxPackedSeparatedInner (decClockHOLFinite s) ∧
      (∃ k : BitVec 64, (decClockHOLFinite s).locals.lookup (ofString "k") = some (.val (.word k))) ∧
      (∃ j : BitVec 64, (decClockHOLFinite s).locals.lookup (ofString "j") = some (.val (.word j))) ∧
      globN (decClockHOLFinite s) "heap_ptr" ≤ 2 ^ 64 := by
  have hready := phase2_packed_keys_with_locals s s.locals (s.clock - 1)
    hp.2.1.1.1 (by intros; rfl)
  have hi : PtxPackedSeparatedInner (decClockHOLFinite s) :=
    ⟨⟨hready, hp.2.1.1.2⟩, hp.2.1.2⟩
  exact ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s s.locals (s.clock - 1)).mpr hp.1.1) hready,
    hi, hp.2.2⟩

/-- Complete state carried across the packed inner loop. -/
def PtxPackedIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ PtxPackedSeparatedInner s ∧
    (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
    (∃ j : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word j))) ∧
    globN s "heap_ptr" ≤ 2 ^ 64

/-- Clock induction for the packed inner loop, with explicit guard interpretation. -/
theorem phase2_packed_iteration_while {guard : ExpHOL 64} {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxPackedIteration s ∧ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) body
      (fun r s => r = none → PtxPackedIteration s))
    (hg : ∀ {F} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      PtxPackedIteration s → evalAt s guard = some (.val (.word w)) →
      (w ≠ 0 ↔ locN s "j" < memW s
        (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedIteration (.while guard body)
      (fun r s => r = none → PtxPackedIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedIteration post ∧ locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := hg st w hp (by simpa [evalAt] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_iteration_decClock st hp
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨hd, hguard.mp hnz⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_separated_inner_exit hp.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-- The concrete copy body discharges the body premise of inner-loop induction. -/
theorem phase2_packed_iteration_guarded_body (h : PtxCallees)
    (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => PtxPackedIteration s ∧ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedIteration s) := by
  refine ⟨fun {F} s hc hp hn => ?_⟩
  exact (phase2_packed_body_iteration_hoare h addressSrc keySrc).run s hc
    (phase2_packed_iteration_guard_pre s hp.1 hp.2) hn

/-- Signed comparison agrees with the natural inner-loop bound for small words. -/
theorem phase2_packed_guard_word_compare {F : Type}
    (s : PanSemStateFiniteExact 64 F) (rhs : ExpHOL 64) (j n w : BitVec 64)
    (hj : s.locals.lookup (ofString "j") = some (.val (.word j)))
    (hn : evalAt s rhs = some (.val (.word n)))
    (hjb : j.toNat < 2 ^ 63) (hnb : n.toNat < 2 ^ 63)
    (he : evalAt s (.cmp .less (.var .local (ofString "j")) rhs) =
      some (.val (.word w))) :
    w ≠ 0 ↔ locN s "j" < n.toNat := by
  have hjv : locN s "j" = j.toNat := by simp [locN, hj]
  rw [hjv]
  norm_num at hjb hnb
  have hn' := hn
  unfold evalAt at hn'
  simp only [evalAt, evalHOLExact, hj, hn'] at he
  by_cases hlt : j.toNat < n.toNat
  · have hc : Compiler.Encoders.Asm.wordCmpHOL .less j n = true := by
      simpa [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
        hjb, hnb] using hlt
    simp [hc] at he
    subst w
    simp [hlt]
  · have hc : Compiler.Encoders.Asm.wordCmpHOL .less j n = false := by
      simp [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
        hjb, hnb, hlt]
    simp [hc] at he
    subst w
    simp [hlt]

/-- Both operands of the inner comparison stay in the nonnegative signed range. -/
theorem phase2_packed_inner_signed_bounds {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxPackedInnerInv s) :
    locN s "j" < 2 ^ 63 ∧
      memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) < 2 ^ 63 := by
  obtain ⟨S, Nd, _, ht, _⟩ := hp.1.2.2.2.2
  have hn : txAccessSlots s (locN s "tx") < 2 ^ 32 := ht.1.2.2.2.2.2.1
  have hprefix := phase2_key_prefix_le_total s
    (i := locN s "i" + 1) (by have hi := hp.2.2.1; omega)
  rw [phase2_key_prefix_succ] at hprefix
  have hj := hp.2.2.2.1
  constructor <;> omega

/-- Interpret the concrete record-count comparison using the current record pointer. -/
theorem phase2_packed_inner_guard_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hp : PtxPackedIteration s)
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (he : evalAt s (.cmp .less (.var .local (ofString "j"))
      (.load .one (.op .add [.var .local (ofString "acc"), .const 16]))) =
      some (.val (.word w))) :
    w ≠ 0 ↔ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
  obtain ⟨j, hj⟩ := hp.2.2.2.1
  have hb := phase2_packed_inner_signed_bounds hp.2.1.1
  cases hl : evalAt s (.load .one (.op .add [.var .local (ofString "acc"), .const 16])) with
  | none =>
    unfold evalAt at hl
    simp only [evalHOLExact] at hl
    simp only [evalAt, evalHOLExact, hj, hl] at he
    simp at he
  | some v =>
    obtain ⟨n, rfl, hn⟩ := phase2_count_load_local s "acc" 16 v hl
    have hn' : n.toNat = memW s
        (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
      simpa only [ha, show (16 : BitVec 64).toNat = 16 by decide] using hn
    have hjb : j.toNat < 2 ^ 63 := by simpa [locN, hj] using hb.1
    have hnb : n.toNat < 2 ^ 63 := by rw [hn']; exact hb.2
    simpa only [hn'] using phase2_packed_guard_word_compare s _ j n w hj hl hjb hnb he

/-- Framing the record-array pointer suffices to retain the caller's record scratch pointer. -/
theorem phase2_packed_acc_restored {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (hh : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208)) :
    locN {post with locals := s.locals} "acc" =
      memW {post with locals := s.locals} (locN {post with locals := s.locals} "tx" + 208) +
        24 * locN {post with locals := s.locals} "i" := by
  change locN s "acc" = memW post (locN s "tx" + 208) + 24 * locN s "i"
  rw [hh]
  exact ha

/-- Inner counter updates do not change the current record scratch pointer relation. -/
theorem phase2_packed_acc_counters {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (k j : ValueHOL 64) :
    let post := setVarHOLFinite (ofString "j") j (setVarHOLFinite (ofString "k") k s)
    locN post "acc" = memW post (locN post "tx" + 208) + 24 * locN post "i" := by
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "j" ≠ ofString "acc" by decide,
    show ofString "k" ≠ ofString "acc" by decide,
    show ofString "j" ≠ ofString "tx" by decide,
    show ofString "k" ≠ ofString "tx" by decide,
    show ofString "j" ≠ ofString "i" by decide,
    show ofString "k" ≠ ofString "i" by decide] using ha

/-- A concrete framed memcpy retains the current-record relation after caller restoration. -/
theorem phase2_memcpy_eval_acc (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (ht : TxAccessListAt (callEntryStateHOLFinite s callee) S Nd (locN s "tx"))
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hsep : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n")
    (hacc : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") :
    locN {post with locals := s.locals} "acc" =
      memW {post with locals := s.locals} (locN {post with locals := s.locals} "tx" + 208) +
        24 * locN {post with locals := s.locals} "i" := by
  exact phase2_packed_acc_restored s post hacc
    (phase2_memcpy_eval_headers h s post vs body callee ret r S Nd (locN s "tx")
      hc hl he hn hr hp ha hw ht hd hsep hlen).1

/-- Either packed-copy destination preserves the record pointer without external spatial witnesses. -/
theorem phase2_memcpy_packed_acc (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
        [(locN s "al_keys" + 52 * locN s "k", 20),
         (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hacc : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") :
    locN {post with locals := s.locals} "acc" =
      memW {post with locals := s.locals} (locN {post with locals := s.locals} "tx" + 208) +
        24 * locN {post with locals := s.locals} "i" := by
  obtain ⟨S, Nd, hw, ht, _, hd, htx, _, hlen⟩ :=
    phase2_packed_copy_spatial_premises s hi _ hdest
  exact phase2_memcpy_eval_acc h s post vs body callee ret r S Nd hc hl he hn hr hp
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr ha).2
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw)
    (R16Shards.PtxP1.txAccessListAt_with_locals s callee (s.clock - 1) ht)
    hd htx hlen hacc

/-- Evaluated packed-copy arguments retain the record pointer used by the next guard. -/
theorem phase2_memcpy_packed_arguments_acc (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hd : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hacc : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") :
    locN {post with locals := s.locals} "acc" =
      memW {post with locals := s.locals} (locN {post with locals := s.locals} "tx" + 208) +
        24 * locN {post with locals := s.locals} "i" := by
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hd hlen
  apply phase2_memcpy_packed_acc h s post vs body callee ret r hc hl he hn hr hp ha hi
    _ hacc
  change (locN { s with locals := callee, clock := s.clock - 1 } "dst",
    locN { s with locals := callee, clock := s.clock - 1 } "n") ∈ _
  rw [hentry.1, hentry.2]
  exact hpair

/-- Copy-call state including the record pointer needed by the concrete guard. -/
def PtxPackedAccCopy {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (WorldOK s ∧ PtxPackedSeparatedCopy s ∧
    (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
    globN s "heap_ptr" ≤ 2 ^ 64) ∧
  locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i"

/-- The address memcpy preserves the complete concrete-guard copy state. -/
theorem phase2_packed_address_copy_acc_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedAccCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedAccCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1.1 callee
  have hcopy := phase2_packed_address_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1.1 hp.1.2.1 hbase hk hp.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  refine ⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.1.2.2.2, ?_⟩
  apply phase2_memcpy_packed_arguments_acc h s post _ src (.const 20) vs body callee ret
    (some (.returned v)) (base + k * 52) 20 hc hargs hl he (by simp)
    (by simp [Resumes]) hentry hp.1.1.1 hp.1.2.1
    (phase2_packed_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) _ hp.2
  rw [phase2_packed_destination_toNat s hp.1.2.1.1 base k hbase hk hp.1.2.2.2]
  simp

/-- The storage-key memcpy preserves the complete concrete-guard copy state. -/
theorem phase2_packed_storage_copy_acc_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedAccCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedAccCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1.1 callee
  have hcopy := phase2_packed_storage_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1.1 hp.1.2.1 hbase hk hp.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  refine ⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.1.2.2.2, ?_⟩
  apply phase2_memcpy_packed_arguments_acc h s post _ src (.const 32) vs body callee ret
    (some (.returned v)) (base + k * 52 + 20) 32 hc hargs hl he (by simp)
    (by simp [Resumes]) hentry hp.1.1.1 hp.1.2.1
    (phase2_packed_key_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) _ hp.2
  rw [phase2_packed_key_destination_toNat s hp.1.2.1.1 base k hbase hk hp.1.2.2.2]
  simp

/-- Inclusive inner-loop state with the concrete record-pointer relation. -/
def PtxPackedAccIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedIteration s ∧
    locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i"

/-- Both counter assignments retain the concrete record-pointer relation. -/
theorem phase2_packed_counters_acc_hoare :
    Hoare PtxPackedAccCopy
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedAccIteration s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, PtxPackedAccCopy before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.1.2.1.1).1
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
      have hb := (phase2_packed_copy_counter_bounds hp.1.2.1.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨phase2_packed_counters_iteration_state before hp.1.1 hp.1.2.1
        hp.1.2.2.2, phase2_packed_acc_counters before hp.2 _ _⟩
    · exact fun _ _ hr => by cases hr

/-- The source-order inner body preserves the strengthened concrete iteration state. -/
theorem phase2_packed_body_acc_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare PtxPackedAccCopy
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedAccIteration s) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_acc_hoare h addressSrc)
    (Hoare.seq_fall (phase2_packed_storage_copy_acc_hoare h keySrc)
      phase2_packed_counters_acc_hoare)

/-- Clock induction with the concrete record-count guard and strengthened invariant. -/
theorem phase2_packed_acc_while {body : ProgHOL 64}
    (hb : Hoare PtxPackedAccCopy body (fun r s => r = none → PtxPackedAccIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedAccIteration
      (.while (.cmp .less (.var .local (ofString "j"))
        (.load .one (.op .add [.var .local (ofString "acc"), .const 16]))) body)
      (fun r s => r = none → PtxPackedAccIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j"))
    (.load .one (.op .add [.var .local (ofString "acc"), .const 16]))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedAccIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedAccIteration post ∧ locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_inner_guard_eval st w hp.1 hp.2
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd : PtxPackedAccIteration (decClockHOLFinite st) :=
            ⟨phase2_packed_iteration_decClock st hp.1, hp.2⟩
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_separated_inner_exit hp.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-- The packed copy loop closes with its concrete guard and both concrete copy destinations. -/
theorem phase2_packed_inner_acc_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare PtxPackedAccIteration
      (.while (.cmp .less (.var .local (ofString "j"))
        (.load .one (.op .add [.var .local (ofString "acc"), .const 16])))
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "al_keys"),
                .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
            (.seq
              (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))))
      (fun r s => r = none → PtxPackedAccIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  exact phase2_packed_acc_while (phase2_packed_body_acc_hoare h addressSrc keySrc) rfl rfl

/-- The flattened-prefix exit equation recovers the exhausted inner guard. -/
theorem phase2_packed_acc_exit_guard {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxPackedAccIteration s)
    (hk : locN s "k" = phase2_key_prefix s (locN s "i" + 1)) :
    ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
  have he := hp.1.2.1.1.2.2.2.2
  rw [phase2_key_prefix_succ] at hk
  omega

/-- Outer iteration state retaining the copy separation and scalar witnesses. -/
def PtxPackedOuterIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ PtxPackedOuterInv s ∧
    Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
    (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
    (∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i))) ∧
    globN s "heap_ptr" ≤ 2 ^ 64

/-- Advancing the outer counter preserves all resources for the next record. -/
theorem phase2_packed_outer_iteration_advance {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedAccIteration s)
    (hk : locN s "k" = phase2_key_prefix s (locN s "i" + 1)) :
    PtxPackedOuterIteration (setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) := by
  have hi := hp.1.2.1.1
  have hout := phase2_packed_outer_advance s hi (phase2_packed_acc_exit_guard hp hk)
    (phase2_packed_outer_successor_bound hi)
  refine ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s _ s.clock).mpr hp.1.1.1) hout.1, hout, ?_, ?_, ?_, ?_, hp.1.2.2.2.2⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "tx" by decide,
      show ofString "i" ≠ ofString "al_keys" by decide,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.1.2.1.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "tx" by decide,
      show ofString "i" ≠ ofString "al_keys" by decide,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.1.2.1.2.2
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "k" by decide] using hp.1.2.2.1
  · exact ⟨BitVec.ofNat 64 (locN s "i" + 1),
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

/-- The actual outer increment consumes the strengthened inner-loop exit. -/
theorem phase2_packed_outer_iteration_increment_hoare :
    Hoare (fun s => PtxPackedAccIteration s ∧
      locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxPackedOuterIteration s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hb := phase2_packed_outer_successor_bound hp.1.1.2.1.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    exact fun _ => phase2_packed_outer_iteration_advance s hp.1 hp.2
  · exact fun _ _ hr => by cases hr

/-- Resetting the key index prepares the strengthened inner loop for a live record. -/
theorem phase2_packed_outer_iteration_reset {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedOuterIteration s)
    (hi : locN s "i" < memW s (locN s "tx" + 216))
    (ha : locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i") :
    PtxPackedAccIteration (setVarHOLFinite (ofString "j") (.val (.word 0)) s) := by
  have hin := phase2_packed_inner_reset s hp.2.1 hi
  have hsep : PtxPackedSeparatedInner (setVarHOLFinite (ofString "j") (.val (.word 0)) s) := by
    refine ⟨hin, ?_, ?_⟩
    · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "j" ≠ ofString "tx" by decide,
        show ofString "j" ≠ ofString "al_keys" by decide,
        show ofString "j" ≠ ofString "nkeys" by decide] using hp.2.2.1
    · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "j" ≠ ofString "tx" by decide,
        show ofString "j" ≠ ofString "al_keys" by decide,
        show ofString "j" ≠ ofString "nkeys" by decide] using hp.2.2.2.1
  refine ⟨⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s _ s.clock).mpr hp.1.1) hin.1,
    hsep, ?_, ?_, hp.2.2.2.2.2.2⟩, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "k" by decide] using hp.2.2.2.2.1
  · exact ⟨0, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "acc" by decide,
      show ofString "j" ≠ ofString "tx" by decide,
      show ofString "j" ≠ ofString "i" by decide] using ha

/-- The source reset statement establishes all strengthened inner-loop premises. -/
theorem phase2_packed_outer_iteration_reset_hoare :
    Hoare (fun s => PtxPackedOuterIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.assign .local (ofString "j") (.const 0))
      (fun r s => r = none → PtxPackedAccIteration s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact fun _ => phase2_packed_outer_iteration_reset s hp.1 hp.2.1 hp.2.2
  · exact fun _ _ hr => by cases hr

/-- Clock decrement preserves all resources of the outer packing iteration. -/
theorem phase2_packed_outer_iteration_decClock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedOuterIteration s) :
    PtxPackedOuterIteration (decClockHOLFinite s) := by
  have hr := phase2_packed_keys_with_locals s s.locals (s.clock - 1)
    hp.2.1.1 (by intros; rfl)
  exact ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s s.locals (s.clock - 1)).mpr hp.1.1) hr,
    ⟨hr, hp.2.1.2⟩, hp.2.2⟩

/-- Outer packing-loop induction retains separation and identifies the total packed count. -/
theorem phase2_packed_outer_iteration_while {guard : ExpHOL 64} {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxPackedOuterIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) body
      (fun r s => r = none → PtxPackedOuterIteration s))
    (hg : ∀ {F} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      PtxPackedOuterIteration s → evalAt s guard = some (.val (.word w)) →
      (w ≠ 0 ↔ locN s "i" < memW s (locN s "tx" + 216)))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedOuterIteration (.while guard body)
      (fun r s => r = none → PtxPackedOuterIteration s ∧ locN s "k" = locN s "nkeys") := by
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedOuterIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedOuterIteration post ∧ locN post "k" = locN post "nkeys" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := hg st w hp (by simpa [evalAt] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_outer_iteration_decClock st hp
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨hd, hguard.mp hnz⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_outer_exit hp.2.1
          (fun hlt => hz (hguard.mpr hlt))).2⟩
    · simp at he

/-- A live outer record lies wholly in the allocated access-list interval. -/
theorem phase2_packed_outer_record_bound {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxPackedOuterIteration s)
    (hi : locN s "i" < memW s (locN s "tx" + 216)) :
    memW s (locN s "tx" + 208) + 24 * locN s "i" + 24 ≤ 2 ^ 64 := by
  obtain ⟨S, Nd, _, ht, _⟩ := hp.2.1.1.2.2.2.2
  have hn : 0 < memW s (locN s "tx" + 216) := by omega
  have hb := (ivl_allocated_bound hp.1.1.2 (Or.inl (ht.2.2 hn).1)).2
  dsimp at hb
  omega

/-- The outer record initializer evaluates without address wraparound. -/
theorem phase2_packed_outer_acc_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (hi : locN s "i" < memW s (locN s "tx" + 216))
    (v : ValueHOL 64)
    (he : evalAt s (.op .add
      [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
       .panop .mul [.var .local (ofString "i"), .const 24]]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      w.toNat = memW s (locN s "tx" + 208) + 24 * locN s "i" := by
  obtain ⟨i, hiw⟩ := hp.2.2.2.2.2.1
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
    have hb := phase2_packed_outer_record_bound hp hi
    have hlt : memW s (locN s "tx" + 208) + 24 * locN s "i" < 2 ^ 64 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_mul]
    rw [show (24 : BitVec 64).toNat = 24 from rfl]
    rw [Nat.add_mod_mod, han, ← hin, Nat.mul_comm (locN s "i") 24]
    exact Nat.mod_eq_of_lt hlt

/-- Declaring the current record preserves all live outer-loop resources. -/
theorem phase2_packed_outer_set_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (v : ValueHOL 64) :
    PtxPackedOuterIteration (setVarHOLFinite (ofString "acc") v s) := by
  have hr := phase2_packed_keys_set_other s hp.2.1.1 (ofString "acc") v (by decide)
  have hout : PtxPackedOuterInv (setVarHOLFinite (ofString "acc") v s) := by
    refine ⟨hr, ?_⟩
    simpa [locN, memW, txAccessSlots, phase2_key_prefix, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "tx" by decide,
      show ofString "acc" ≠ ofString "nkeys" by decide,
      show ofString "acc" ≠ ofString "i" by decide,
      show ofString "acc" ≠ ofString "k" by decide] using hp.2.1.2
  refine ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s _ s.clock).mpr hp.1.1) hr, hout, ?_⟩
  simpa [locN, memW, globN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "acc" ≠ ofString "tx" by decide,
    show ofString "acc" ≠ ofString "al_keys" by decide,
    show ofString "acc" ≠ ofString "nkeys" by decide,
    show ofString "acc" ≠ ofString "i" by decide,
    show ofString "acc" ≠ ofString "k" by decide] using hp.2.2

/-- Record declaration establishes exactly the precondition of the inner reset. -/
theorem phase2_packed_outer_declare_acc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (hi : locN s "i" < memW s (locN s "tx" + 216))
    (v : ValueHOL 64)
    (he : evalAt s (.op .add
      [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
       .panop .mul [.var .local (ofString "i"), .const 24]]) = some v) :
    let post := setVarHOLFinite (ofString "acc") v s
    PtxPackedOuterIteration post ∧
      locN post "i" < memW post (locN post "tx" + 216) ∧
      locN post "acc" = memW post (locN post "tx" + 208) + 24 * locN post "i" := by
  obtain ⟨w, rfl, hw⟩ := phase2_packed_outer_acc_eval s hp hi v he
  refine ⟨phase2_packed_outer_set_acc s hp _, ?_, ?_⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide,
      show ofString "acc" ≠ ofString "tx" by decide] using hi
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc" ≠ ofString "i" by decide,
      show ofString "acc" ≠ ofString "tx" by decide] using hw

/-- Restoring a declaration scope preserves the complete outer packing state. -/
theorem phase2_packed_outer_iteration_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (hp : PtxPackedOuterIteration s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedOuterIteration {s with locals := locals, clock := clock} := by
  have hr := phase2_packed_keys_with_locals s locals clock hp.2.1.1
    (fun n hn => hl n (by simp only [List.mem_cons, List.mem_singleton] at hn ⊢; tauto))
  have he : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k"] : List String),
      locN {s with locals := locals, clock := clock} n = locN s n := by
    intro n hn
    simp [locN, hl n hn]
  have hout : PtxPackedOuterInv {s with locals := locals, clock := clock} := by
    refine ⟨hr, ?_⟩
    simpa only [he "nkeys" (by simp), he "i" (by simp), he "k" (by simp),
      txAccessSlots, phase2_key_prefix, he "tx" (by simp), memW] using hp.2.1.2
  refine ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s locals clock).mpr hp.1.1) hr, hout, ?_, ?_, ?_, ?_, hp.2.2.2.2.2.2⟩
  · simpa only [he "tx" (by simp), he "al_keys" (by simp), he "nkeys" (by simp)] using hp.2.2.1
  · simpa only [he "tx" (by simp), he "al_keys" (by simp), he "nkeys" (by simp), memW] using hp.2.2.2.1
  · simpa only [hl "k" (by simp)] using hp.2.2.2.2.1
  · simpa only [hl "i" (by simp)] using hp.2.2.2.2.2.1

/-- A record pass composes the reset, strengthened inner loop, and outer increment. -/
theorem phase2_packed_record_pass_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare (fun s => PtxPackedOuterIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc" = memW s (locN s "tx" + 208) + 24 * locN s "i")
      (.seq (.assign .local (ofString "j") (.const 0))
        (.seq
          (.while (.cmp .less (.var .local (ofString "j"))
            (.load .one (.op .add [.var .local (ofString "acc"), .const 16])))
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.op .add [.var .local (ofString "al_keys"),
                  .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
              (.seq
                (.call (some (none, none)) (ofString "memcpy")
                  [.op .add [.var .local (ofString "al_keys"),
                    .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
                (.seq
                  (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))))
      (fun r s => r = none → PtxPackedOuterIteration s) := by
  exact Hoare.seq_fall phase2_packed_outer_iteration_reset_hoare
    (Hoare.seq_fall (phase2_packed_inner_acc_hoare h addressSrc keySrc)
      phase2_packed_outer_iteration_increment_hoare)

/-- The source loop caches the current record count in `ns`. -/
def PtxPackedNsIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedIteration s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
    locN s "ns" = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)

/-- Interpret the actual source guard, which compares against the cached `ns` word. -/
theorem phase2_packed_ns_guard_eval {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hp : PtxPackedNsIteration s)
    (he : evalAt s (.cmp .less (.var .local (ofString "j"))
      (.var .local (ofString "ns"))) = some (.val (.word w))) :
    w ≠ 0 ↔ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
  obtain ⟨j, hj⟩ := hp.1.2.2.2.1
  obtain ⟨n, hn⟩ := hp.2.1
  have hb := phase2_packed_inner_signed_bounds hp.1.2.1.1
  have hnat : n.toNat = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
    simpa [locN, hn] using hp.2.2
  have hjb : j.toNat < 2 ^ 63 := by simpa [locN, hj] using hb.1
  have hnb : n.toNat < 2 ^ 63 := by rw [hnat]; exact hb.2
  simpa only [hnat] using phase2_packed_guard_word_compare s _ j n w hj
    (by simp [evalAt, evalHOLExact, hn]) hjb hnb he

/-- The cached source guard is unchanged by the loop clock decrement. -/
theorem phase2_packed_ns_iteration_decClock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedNsIteration s) :
    PtxPackedNsIteration (decClockHOLFinite s) :=
  ⟨phase2_packed_iteration_decClock s hp.1, hp.2⟩

/-- Packed memcpy preserves the cached count used by the actual source guard. -/
theorem phase2_memcpy_packed_ns (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
        [(locN s "al_keys" + 52 * locN s "k", 20),
         (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hns : locN s "ns" = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN {post with locals := s.locals} "ns" =
      memW {post with locals := s.locals}
        (memW {post with locals := s.locals} (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
  obtain ⟨S, Nd, hw, ht, _, hd, htx, hrec, hlen⟩ :=
    phase2_packed_copy_spatial_premises s hi _ hdest
  have hae := ((arenaReady_with_locals s callee (s.clock - 1)).mpr ha).2
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  have hte := R16Shards.PtxP1.txAccessListAt_with_locals s callee (s.clock - 1) ht
  have hh := phase2_memcpy_eval_headers h s post vs body callee ret r S Nd (locN s "tx")
    hc hl he hn hr hp hae hwe hte hd htx hlen
  have hm := phase2_memcpy_eval_counts h s post vs body callee ret r S Nd (locN s "tx")
    hc hl he hn hr hp hae hwe hte hd hrec hlen
  change locN s "ns" = memW post (memW post (locN s "tx" + 208) + 24 * locN s "i" + 16)
  rw [hh.1, hm (locN s "i") hi.1.2.2.1]
  exact hns

/-- Evaluated destination arguments suffice to retain the cached source-loop count. -/
theorem phase2_memcpy_packed_arguments_ns (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hd : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hns : locN s "ns" = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    locN {post with locals := s.locals} "ns" =
      memW {post with locals := s.locals}
        (memW {post with locals := s.locals} (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hd hlen
  apply phase2_memcpy_packed_ns h s post vs body callee ret r hc hl he hn hr hp ha hi _ hns
  change (locN {s with locals := callee, clock := s.clock - 1} "dst",
    locN {s with locals := callee, clock := s.clock - 1} "n") ∈ _
  rw [hentry.1, hentry.2]
  exact hpair

/-- Copy state carrying the cached source count and its word witness. -/
def PtxPackedNsCopy {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (WorldOK s ∧ PtxPackedSeparatedCopy s ∧
    (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
    globN s "heap_ptr" ≤ 2 ^ 64) ∧
  (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
  locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)

/-- The address copy preserves the source loop's cached count. -/
theorem phase2_packed_address_copy_ns_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedNsCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedNsCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1.1 callee
  have hcopy := phase2_packed_address_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1.1 hp.1.2.1 hbase hk hp.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  refine ⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.1.2.2.2, hp.2.1, ?_⟩
  apply phase2_memcpy_packed_arguments_ns h s post _ src (.const 20) vs body callee ret
    (some (.returned v)) (base + k * 52) 20 hc hargs hl he (by simp)
    (by simp [Resumes]) hentry hp.1.1.1 hp.1.2.1
    (phase2_packed_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) _ hp.2.2
  rw [phase2_packed_destination_toNat s hp.1.2.1.1 base k hbase hk hp.1.2.2.2]
  simp

/-- The storage-key copy preserves the source loop's cached count. -/
theorem phase2_packed_storage_copy_ns_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedNsCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedNsCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hp.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1.1 callee
  have hcopy := phase2_packed_storage_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hp.1.1.1 hp.1.2.1 hbase hk hp.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  refine ⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hp.1.2.2.2, hp.2.1, ?_⟩
  apply phase2_memcpy_packed_arguments_ns h s post _ src (.const 32) vs body callee ret
    (some (.returned v)) (base + k * 52 + 20) 32 hc hargs hl he (by simp)
    (by simp [Resumes]) hentry hp.1.1.1 hp.1.2.1
    (phase2_packed_key_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) _ hp.2.2
  rw [phase2_packed_key_destination_toNat s hp.1.2.1.1 base k hbase hk hp.1.2.2.2]
  simp

/-- Counter updates preserve the cached `ns` word and its record-count equation. -/
theorem phase2_packed_ns_counters {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedNsCopy s) (k j : ValueHOL 64) :
    let post := setVarHOLFinite (ofString "j") j (setVarHOLFinite (ofString "k") k s)
    (∃ n : BitVec 64, post.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
    locN post "ns" = memW post (memW post (locN post "tx" + 208) + 24 * locN post "i" + 16) := by
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "j" ≠ ofString "ns" by decide,
    show ofString "k" ≠ ofString "ns" by decide,
    show ofString "j" ≠ ofString "tx" by decide,
    show ofString "k" ≠ ofString "tx" by decide,
    show ofString "j" ≠ ofString "i" by decide,
    show ofString "k" ≠ ofString "i" by decide] using hp.2

/-- The source counter pair restores the cached-count iteration invariant. -/
theorem phase2_packed_counters_ns_hoare :
    Hoare PtxPackedNsCopy
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedNsIteration s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, PtxPackedNsCopy before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.1.2.1.1).1
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
      have hb := (phase2_packed_copy_counter_bounds hp.1.2.1.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨phase2_packed_counters_iteration_state before hp.1.1 hp.1.2.1
        hp.1.2.2.2, phase2_packed_ns_counters before hp _ _⟩
    · exact fun _ _ hr => by cases hr

/-- Both copies and both counters preserve the actual source-loop invariant. -/
theorem phase2_packed_body_ns_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare PtxPackedNsCopy
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedNsIteration s) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_ns_hoare h addressSrc)
    (Hoare.seq_fall (phase2_packed_storage_copy_ns_hoare h keySrc)
      phase2_packed_counters_ns_hoare)

/-- Clock induction for the actual source guard `j < ns`. -/
theorem phase2_packed_ns_while {body : ProgHOL 64}
    (hb : Hoare PtxPackedNsCopy body (fun r s => r = none → PtxPackedNsIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedNsIteration
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      (fun r s => r = none → PtxPackedNsIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedNsIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedNsIteration post ∧ locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_ns_guard_eval st w hp (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_ns_iteration_decClock st hp
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_separated_inner_exit hp.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-- The source inner packing loop preserves the cached count and completes the record prefix. -/
theorem phase2_packed_inner_ns_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare PtxPackedNsIteration
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns")))
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
          (.seq
            (.call (some (none, none)) (ofString "memcpy")
              [.op .add [.var .local (ofString "al_keys"),
                .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
            (.seq
              (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))))
      (fun r s => r = none → PtxPackedNsIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  exact phase2_packed_ns_while (phase2_packed_body_ns_hoare h addressSrc keySrc) rfl rfl

/-- The source inner-loop exit supplies the complete next-record state. -/
theorem phase2_packed_ns_outer_advance {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedNsIteration s)
    (hk : locN s "k" = phase2_key_prefix s (locN s "i" + 1)) :
    PtxPackedOuterIteration (setVarHOLFinite (ofString "i")
      (.val (.word (BitVec.ofNat 64 (locN s "i" + 1)))) s) := by
  have hi := hp.1.2.1.1
  have hex : ¬ locN s "j" < memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
    have he := hi.2.2.2.2
    rw [phase2_key_prefix_succ] at hk
    omega
  have hout := phase2_packed_outer_advance s hi hex (phase2_packed_outer_successor_bound hi)
  refine ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s _ s.clock).mpr hp.1.1.1) hout.1, hout, ?_, ?_, ?_, ?_, hp.1.2.2.2.2⟩
  · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "tx" by decide,
      show ofString "i" ≠ ofString "al_keys" by decide,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.1.2.1.2.1
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "tx" by decide,
      show ofString "i" ≠ ofString "al_keys" by decide,
      show ofString "i" ≠ ofString "nkeys" by decide] using hp.1.2.1.2.2
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "k" by decide] using hp.1.2.2.1
  · exact ⟨BitVec.ofNat 64 (locN s "i" + 1),
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

/-- The source outer increment consumes the cached-count inner-loop exit. -/
theorem phase2_packed_ns_outer_increment_hoare :
    Hoare (fun s => PtxPackedNsIteration s ∧
      locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxPackedOuterIteration s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hb := phase2_packed_outer_successor_bound hp.1.1.2.1.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    exact fun _ => phase2_packed_ns_outer_advance s hp.1 hp.2
  · exact fun _ _ hr => by cases hr

/-- Resetting `j` establishes the actual cached-count inner invariant. -/
theorem phase2_packed_ns_reset {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedOuterIteration s)
    (hi : locN s "i" < memW s (locN s "tx" + 216))
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n)))
    (he : locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) :
    PtxPackedNsIteration (setVarHOLFinite (ofString "j") (.val (.word 0)) s) := by
  have hin := phase2_packed_inner_reset s hp.2.1 hi
  have hsep : PtxPackedSeparatedInner (setVarHOLFinite (ofString "j") (.val (.word 0)) s) := by
    refine ⟨hin, ?_, ?_⟩
    · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "j" ≠ ofString "tx" by decide,
        show ofString "j" ≠ ofString "al_keys" by decide,
        show ofString "j" ≠ ofString "nkeys" by decide] using hp.2.2.1
    · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "j" ≠ ofString "tx" by decide,
        show ofString "j" ≠ ofString "al_keys" by decide,
        show ofString "j" ≠ ofString "nkeys" by decide] using hp.2.2.2.1
  refine ⟨⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals s _ s.clock).mpr hp.1.1) hin.1,
    hsep, ?_, ?_, hp.2.2.2.2.2.2⟩, ?_, ?_⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "k" by decide] using hp.2.2.2.2.1
  · exact ⟨0, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "ns" by decide] using hn
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "j" ≠ ofString "ns" by decide,
      show ofString "j" ≠ ofString "tx" by decide,
      show ofString "j" ≠ ofString "i" by decide] using he

/-- Scratch declarations frame all fields of the outer iteration invariant. -/
theorem phase2_packed_outer_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k"] : List String), ofString n ≠ name) :
    PtxPackedOuterIteration (setVarHOLFinite name v s) := by
  apply phase2_packed_outer_iteration_with_locals s _ s.clock hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- The actual `acc2` declaration establishes the source record address. -/
theorem phase2_packed_outer_declare_acc2 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (hi : locN s "i" < memW s (locN s "tx" + 216))
    (v : ValueHOL 64)
    (he : evalAt s (.op .add
      [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
       .panop .mul [.var .local (ofString "i"), .const 24]]) = some v) :
    let post := setVarHOLFinite (ofString "acc2") v s
    PtxPackedOuterIteration post ∧
      locN post "i" < memW post (locN post "tx" + 216) ∧
      locN post "acc2" = memW post (locN post "tx" + 208) + 24 * locN post "i" := by
  obtain ⟨w, rfl, hw⟩ := phase2_packed_outer_acc_eval s hp hi v he
  refine ⟨phase2_packed_outer_set_other s hp _ _ (by decide), ?_, ?_⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc2" ≠ ofString "i" by decide,
      show ofString "acc2" ≠ ofString "tx" by decide] using hi
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "acc2" ≠ ofString "i" by decide,
      show ofString "acc2" ≠ ofString "tx" by decide] using hw

/-- Loading `ns` from `acc2` establishes the cached-count precondition. -/
theorem phase2_packed_outer_declare_ns {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedOuterIteration s) (hi : locN s "i" < memW s (locN s "tx" + 216))
    (ha : locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
    (v : ValueHOL 64)
    (he : evalAt s (.load .one (.op .add [.var .local (ofString "acc2"), .const 16])) = some v) :
    let post := setVarHOLFinite (ofString "ns") v s
    PtxPackedOuterIteration post ∧
      locN post "i" < memW post (locN post "tx" + 216) ∧
      (∃ n : BitVec 64, post.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
      locN post "ns" = memW post
        (memW post (locN post "tx" + 208) + 24 * locN post "i" + 16) := by
  obtain ⟨n, rfl, hn⟩ := phase2_count_load_local s "acc2" 16 v he
  have hnat : n.toNat = memW s
      (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16) := by
    simpa only [ha, show (16 : BitVec 64).toNat = 16 by decide] using hn
  refine ⟨phase2_packed_outer_set_other s hp _ _ (by decide), ?_, ⟨n, ?_⟩, ?_⟩
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "ns" ≠ ofString "i" by decide,
      show ofString "ns" ≠ ofString "tx" by decide] using hi
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "ns" ≠ ofString "i" by decide,
      show ofString "ns" ≠ ofString "tx" by decide] using hnat

/-- The source-order inner loop followed by the record increment. -/
def phase2_packed_source_inner_tail : ProgHOL 64 :=
  .seq
    (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns")))
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]],
           .load .one (.op .add [.var .local (ofString "acc2"), .const 0]), .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20],
             .op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
               .panop .mul [.var .local (ofString "j"), .const 32]], .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))))))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))

theorem phase2_packed_source_inner_tail_hoare (h : PtxCallees) :
    Hoare PtxPackedNsIteration phase2_packed_source_inner_tail
      (fun r s => r = none → PtxPackedOuterIteration s) := by
  exact Hoare.seq_fall (phase2_packed_inner_ns_hoare h _ _)
    phase2_packed_ns_outer_increment_hoare

/-- The actual nested declarations and copy loop form a complete outer record body. -/
def phase2_packed_source_outer_body : ProgHOL 64 :=
  .dec (ofString "acc2") .one
    (.op .add [.load .one (.op .add [.var .local (ofString "tx"), .const 208]),
      .panop .mul [.var .local (ofString "i"), .const 24]])
    (.dec (ofString "ns") .one
      (.load .one (.op .add [.var .local (ofString "acc2"), .const 16]))
      (.dec (ofString "j") .one (.const 0) phase2_packed_source_inner_tail))

theorem phase2_packed_source_outer_body_hoare (h : PtxCallees) :
    Hoare (fun s => PtxPackedOuterIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      (fun r s => r = none → PtxPackedOuterIteration s) := by
  unfold phase2_packed_source_outer_body
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k"])
    (P' := fun s => PtxPackedOuterIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i") (by decide)
  · intro F s v hp he
    exact phase2_packed_outer_declare_acc2 s hp.1 hp.2 v he
  · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k"])
      (P' := fun s => PtxPackedOuterIteration s ∧
        locN s "i" < memW s (locN s "tx" + 216) ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
        locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) (by decide)
    · intro F s v hp he
      exact phase2_packed_outer_declare_ns s hp.1 hp.2.1 hp.2.2 v he
    · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k"])
        (P' := PtxPackedNsIteration) (by decide)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        exact phase2_packed_ns_reset s hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
      · exact phase2_packed_source_inner_tail_hoare h
      · intro F r s locals hl hp hr
        exact phase2_packed_outer_iteration_with_locals s locals s.clock (hp hr) hl
      · exact fun _ _ hr => by cases hr
    · intro F r s locals hl hp hr
      exact phase2_packed_outer_iteration_with_locals s locals s.clock (hp hr) hl
    · exact fun _ _ hr => by cases hr
  · intro F r s locals hl hp hr
    exact phase2_packed_outer_iteration_with_locals s locals s.clock (hp hr) hl
  · exact fun _ _ hr => by cases hr

/-- The outer counter and record count fit the signed comparison range. -/
theorem phase2_packed_outer_signed_bounds {F : Type}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxPackedOuterIteration s) :
    locN s "i" < 2 ^ 63 ∧ memW s (locN s "tx" + 216) < 2 ^ 63 := by
  obtain ⟨S, Nd, _, ht, _⟩ := hp.2.1.1.2.2.2.2
  have hn : memW s (locN s "tx" + 216) < 2 ^ 32 := ht.1.2.2.2.2.1
  have hi := hp.2.1.2.2.1
  constructor <;> omega

/-- Interpret the actual outer guard when `nal` caches the transaction record count. -/
theorem phase2_packed_outer_nal_guard {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hp : PtxPackedOuterIteration s)
    (hn : ∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n)))
    (heq : locN s "nal" = memW s (locN s "tx" + 216))
    (he : evalAt s (.cmp .less (.var .local (ofString "i"))
      (.var .local (ofString "nal"))) = some (.val (.word w))) :
    w ≠ 0 ↔ locN s "i" < memW s (locN s "tx" + 216) := by
  obtain ⟨i, hi⟩ := hp.2.2.2.2.2.1
  obtain ⟨n, hn⟩ := hn
  have hiv : locN s "i" = i.toNat := by simp [locN, hi]
  have hnv : n.toNat = memW s (locN s "tx" + 216) := by simpa [locN, hn] using heq
  have hb := phase2_packed_outer_signed_bounds hp
  have hib : i.toNat < 2 ^ 63 := by rw [← hiv]; exact hb.1
  have hnb : n.toNat < 2 ^ 63 := by rw [hnv]; exact hb.2
  rw [hiv, ← hnv]
  norm_num at hib hnb
  simp only [evalAt, evalHOLExact, hi, hn] at he
  by_cases hlt : i.toNat < n.toNat
  · have hc : Compiler.Encoders.Asm.wordCmpHOL .less i n = true := by
      simpa [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
        hib, hnb] using hlt
    simp [hc] at he
    subst w
    simp [hlt]
  · have hc : Compiler.Encoders.Asm.wordCmpHOL .less i n = false := by
      simp [Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess,
        hib, hnb, hlt]
    simp [hc] at he
    subst w
    simp [hlt]

/-- The actual outer guard needs the cached access-list count as well as packing resources. -/
def PtxPackedNalIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedOuterIteration s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
    locN s "nal" = memW s (locN s "tx" + 216)

theorem phase2_packed_nal_iteration_decClock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hp : PtxPackedNalIteration s) :
    PtxPackedNalIteration (decClockHOLFinite s) :=
  ⟨phase2_packed_outer_iteration_decClock s hp.1, hp.2⟩

/-- Clock induction for the source `i < nal` loop, with an explicit cached-count
preservation obligation on its body. -/
theorem phase2_packed_nal_while {body : ProgHOL 64}
    (hb : Hoare (fun s => PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) body
      (fun r s => r = none → PtxPackedNalIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedNalIteration
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → PtxPackedNalIteration s ∧ locN s "k" = locN s "nkeys") := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))
  change Hoare PtxPackedNalIteration (.while guard body) _
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedNalIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedNalIteration post ∧ locN post "k" = locN post "nkeys" from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_outer_nal_guard st w hp.1 hp.2.1 hp.2.2
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_nal_iteration_decClock st hp
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨hd, hguard.mp hnz⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_outer_exit hp.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).2⟩
    · simp at he

/-- Restore declaration scopes without losing the cached outer count. -/
theorem phase2_packed_nal_iteration_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (hp : PtxPackedNalIteration s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k", "nal"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxPackedNalIteration { s with locals := locals, clock := clock } := by
  refine ⟨phase2_packed_outer_iteration_with_locals s locals clock hp.1 ?_, ?_, ?_⟩
  · intro n hn
    apply hl n
    simp only [List.mem_cons, List.mem_singleton] at hn ⊢
    tauto
  · simpa only [hl "nal" (by simp)] using hp.2.1
  · simpa only [locN, memW, hl "nal" (by simp), hl "tx" (by simp)] using hp.2.2

/-- Scratch declarations preserve the cached outer count. -/
theorem phase2_packed_nal_set_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedNalIteration s) (name : MlS) (v : ValueHOL 64)
    (hne : ∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k", "nal"] : List String),
      ofString n ≠ name) :
    PtxPackedNalIteration (setVarHOLFinite name v s) := by
  apply phase2_packed_nal_iteration_with_locals s _ s.clock hp
  intro n hn
  simp [HolFiniteMapExact.update, FUPDATE, Ne.symm (hne n hn)]

/-- A packed copy retains the cached record count used by the outer loop. -/
theorem phase2_memcpy_packed_nal (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64))
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
        [(locN s "al_keys" + 52 * locN s "k", 20),
         (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hnal : locN s "nal" = memW s (locN s "tx" + 216)) :
    locN {post with locals := s.locals} "nal" =
      memW {post with locals := s.locals} (locN s "tx" + 216) := by
  obtain ⟨S, Nd, hw, ht, _, hd, htx, _, hlen⟩ :=
    phase2_packed_copy_spatial_premises s hi _ hdest
  have hae := ((arenaReady_with_locals s callee (s.clock - 1)).mpr ha).2
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  have hte := R16Shards.PtxP1.txAccessListAt_with_locals s callee (s.clock - 1) ht
  have hh := phase2_memcpy_eval_headers h s post vs body callee ret r S Nd (locN s "tx")
    hc hl he hn hr hp hae hwe hte hd htx hlen
  change locN s "nal" = memW post (locN s "tx" + 216)
  rw [hh.2]
  exact hnal

/-- Destination evaluation discharges the outer cached-count copy frame. -/
theorem phase2_memcpy_packed_arguments_nal (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedSeparatedCopy s)
    (hd : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)])
    (hnal : locN s "nal" = memW s (locN s "tx" + 216)) :
    locN {post with locals := s.locals} "nal" =
      memW {post with locals := s.locals} (locN s "tx" + 216) := by
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hd hlen
  apply phase2_memcpy_packed_nal h s post vs body callee ret r hc hl he hn hr hp ha hi _ hnal
  change (locN {s with locals := callee, clock := s.clock - 1} "dst",
    locN {s with locals := callee, clock := s.clock - 1} "n") ∈ _
  rw [hentry.1, hentry.2]
  exact hpair

/-- Copy state retaining both source-loop cached counts. -/
def PtxPackedNsNalCopy {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedNsCopy s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
    locN s "nal" = memW s (locN s "tx" + 216)

/-- The concrete address copy retains both cached loop bounds. -/
theorem phase2_packed_address_copy_ns_nal_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedNsNalCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedNsNalCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  have hs := hp.1
  obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hs.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hs.1.1 callee
  have hcopy := phase2_packed_address_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hs.1.1.1 hs.1.2.1 hbase hk hs.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hs.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  have hd := phase2_packed_destination_eval s base k hbase hk
  have hlen : evalAt s (.const 20) = some (.val (.word (20 : BitVec 64))) := by
    simp [evalAt, evalHOLExact]
  have hpair : ((base + k * 52).toNat, (20 : BitVec 64).toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)] := by
    rw [phase2_packed_destination_toNat s hs.1.2.1.1 base k hbase hk hs.1.2.2.2]
    simp
  refine ⟨⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hs.1.2.2.2,
    hs.2.1, ?_⟩, hp.2.1, ?_⟩
  · exact phase2_memcpy_packed_arguments_ns h s post _ src (.const 20) vs body callee ret
      (some (.returned v)) (base + k * 52) 20 hc hargs hl he (by simp)
      (by simp [Resumes]) hentry hs.1.1.1 hs.1.2.1 hd hlen hpair hs.2.2
  · exact phase2_memcpy_packed_arguments_nal h s post _ src (.const 20) vs body callee ret
      (some (.returned v)) (base + k * 52) 20 hc hargs hl he (by simp)
      (by simp [Resumes]) hentry hs.1.1.1 hs.1.2.1 hd hlen hpair hp.2.2

/-- The concrete storage-key copy retains both cached loop bounds. -/
theorem phase2_packed_storage_copy_ns_nal_hoare (h : PtxCallees) (src : ExpHOL 64) :
    Hoare PtxPackedNsNalCopy
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedNsNalCopy t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  have hs := hp.1
  obtain ⟨base, hbase⟩ := hs.1.2.1.1.1.1
  obtain ⟨k, hk⟩ := hs.1.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hs.1.1 callee
  have hcopy := phase2_packed_storage_copy_eval h s post src vs body callee ret
    (some (.returned v)) base k hc hargs hl he (by simp) (by simp [Resumes])
    hentry hs.1.1.1 hs.1.2.1 hbase hk hs.1.2.2.2
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hs.1.2.2.2
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  have hd := phase2_packed_key_destination_eval s base k hbase hk
  have hlen : evalAt s (.const 32) = some (.val (.word (32 : BitVec 64))) := by
    simp [evalAt, evalHOLExact]
  have hpair : ((base + k * 52 + 20).toNat, (32 : BitVec 64).toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)] := by
    rw [phase2_packed_key_destination_toNat s hs.1.2.1.1 base k hbase hk hs.1.2.2.2]
    simp
  refine ⟨⟨phase2_packed_next_call_pre s post harena.1 hcopy ⟨k, hk⟩ hg hs.1.2.2.2,
    hs.2.1, ?_⟩, hp.2.1, ?_⟩
  · exact phase2_memcpy_packed_arguments_ns h s post _ src (.const 32) vs body callee ret
      (some (.returned v)) (base + k * 52 + 20) 32 hc hargs hl he (by simp)
      (by simp [Resumes]) hentry hs.1.1.1 hs.1.2.1 hd hlen hpair hs.2.2
  · exact phase2_memcpy_packed_arguments_nal h s post _ src (.const 32) vs body callee ret
      (some (.returned v)) (base + k * 52 + 20) 32 hc hargs hl he (by simp)
      (by simp [Resumes]) hentry hs.1.1.1 hs.1.2.1 hd hlen hpair hp.2.2

/-- Inner iteration retaining the outer cached count. -/
def PtxPackedNsNalIteration {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedNsIteration s ∧
    (∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
    locN s "nal" = memW s (locN s "tx" + 216)

theorem phase2_packed_nal_counters {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedNsNalCopy s) (k j : ValueHOL 64) :
    let post := setVarHOLFinite (ofString "j") j (setVarHOLFinite (ofString "k") k s)
    (∃ n : BitVec 64, post.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
    locN post "nal" = memW post (locN post "tx" + 216) := by
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "j" ≠ ofString "nal" by decide,
    show ofString "k" ≠ ofString "nal" by decide,
    show ofString "j" ≠ ofString "tx" by decide,
    show ofString "k" ≠ ofString "tx" by decide] using hp.2

/-- Both counter assignments preserve the two cached loop bounds. -/
theorem phase2_packed_counters_ns_nal_hoare :
    Hoare PtxPackedNsNalCopy
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedNsNalIteration s) := by
  apply Hoare.seq_fall (R := fun s => ∃ before, PtxPackedNsNalCopy before ∧
    s = setVarHOLFinite (ofString "k")
      (.val (.word (BitVec.ofNat 64 (locN before "k" + 1)))) before)
  · apply Hoare.assign
    · intro F s v hp he
      have hb := (phase2_packed_copy_counter_bounds hp.1.1.2.1.1).1
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
      have hb := (phase2_packed_copy_counter_bounds hp.1.1.2.1.1).2
      obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval _ "j" v (by rw [hj]; exact hb) he
      have heq : w = BitVec.ofNat 64 (locN before "j" + 1) := by
        apply BitVec.eq_of_toNat_eq
        rw [hw, hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      subst w
      exact fun _ => ⟨⟨phase2_packed_counters_iteration_state before hp.1.1.1 hp.1.1.2.1
        hp.1.1.2.2.2, phase2_packed_ns_counters before hp.1 _ _⟩,
        phase2_packed_nal_counters before hp _ _⟩
    · exact fun _ _ hr => by cases hr

/-- Both copies and counters retain both cached loop bounds. -/
theorem phase2_packed_body_ns_nal_hoare (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    Hoare PtxPackedNsNalCopy
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedNsNalIteration s) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_ns_nal_hoare h addressSrc)
    (Hoare.seq_fall (phase2_packed_storage_copy_ns_nal_hoare h keySrc)
      phase2_packed_counters_ns_nal_hoare)

/-- The inner clock induction carries the outer cached bound through every copy. -/
theorem phase2_packed_ns_nal_while {body : ProgHOL 64}
    (hb : Hoare PtxPackedNsNalCopy body (fun r s => r = none → PtxPackedNsNalIteration s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare PtxPackedNsNalIteration
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      (fun r s => r = none → PtxPackedNsNalIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode → PtxPackedNsNalIteration st →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      PtxPackedNsNalIteration post ∧ locN post "k" = phase2_key_prefix post (locN post "i" + 1) from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_ns_guard_eval st w hp.1 (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_ns_iteration_decClock st hp.1
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩, hp.2⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            apply ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨hp, (phase2_packed_separated_inner_exit hp.1.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩
    · simp at he

/-- The outer increment retains the cached record bound after inner completion. -/
theorem phase2_packed_ns_nal_outer_increment_hoare :
    Hoare (fun s => PtxPackedNsNalIteration s ∧
      locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
      (fun r s => r = none → PtxPackedNalIteration s) := by
  apply Hoare.assign
  · intro F s v hp he
    have hb := phase2_packed_outer_successor_bound hp.1.1.1.2.1.1
    obtain ⟨w, rfl, hw⟩ := phase2_copy_increment_eval s "i" v hb he
    have heq : w = BitVec.ofNat 64 (locN s "i" + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    subst w
    intro _
    refine ⟨phase2_packed_ns_outer_advance s hp.1.1 hp.2, ?_⟩
    simpa [locN, memW, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "i" ≠ ofString "nal" by decide,
      show ofString "i" ≠ ofString "tx" by decide] using hp.1.2
  · exact fun _ _ hr => by cases hr

/-- The concrete inner loop and record increment retain the outer cached bound. -/
theorem phase2_packed_source_inner_tail_nal_hoare (h : PtxCallees) :
    Hoare PtxPackedNsNalIteration phase2_packed_source_inner_tail
      (fun r s => r = none → PtxPackedNalIteration s) := by
  exact Hoare.seq_fall
    (phase2_packed_ns_nal_while (phase2_packed_body_ns_nal_hoare h _ _) rfl rfl)
    phase2_packed_ns_nal_outer_increment_hoare

/-- The source record body preserves the cached outer-loop invariant. -/
theorem phase2_packed_source_outer_body_nal_hoare (h : PtxCallees) :
    Hoare (fun s => PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      (fun r s => r = none → PtxPackedNalIteration s) := by
  unfold phase2_packed_source_outer_body
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
    (P' := fun s => PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i") (by decide)
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.1.1 hp.2 v he
    exact ⟨phase2_packed_nal_set_other s hp.1 _ _ (by decide), hd.2⟩
  · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
      (P' := fun s => PtxPackedNalIteration s ∧
        locN s "i" < memW s (locN s "tx" + 216) ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
        locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) (by decide)
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.1.1 hp.2.1 hp.2.2 v he
      exact ⟨phase2_packed_nal_set_other s hp.1 _ _ (by decide), hd.2⟩
    · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
        (P' := PtxPackedNsNalIteration) (by decide)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        refine ⟨phase2_packed_ns_reset s hp.1.1 hp.2.1 hp.2.2.1 hp.2.2.2, ?_⟩
        exact (phase2_packed_nal_set_other s hp.1 (ofString "j") (.val (.word 0)) (by decide)).2
      · exact phase2_packed_source_inner_tail_nal_hoare h
      · intro F r s locals hl hp hr
        exact phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr) hl
      · exact fun _ _ hr => by cases hr
    · intro F r s locals hl hp hr
      exact phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr) hl
    · exact fun _ _ hr => by cases hr
  · intro F r s locals hl hp hr
    exact phase2_packed_nal_iteration_with_locals s locals s.clock (hp hr) hl
  · exact fun _ _ hr => by cases hr

/-- The actual packing loop completes all records while retaining its resources. -/
theorem phase2_packed_source_outer_loop_hoare (h : PtxCallees) :
    Hoare PtxPackedNalIteration
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → PtxPackedNalIteration s ∧ locN s "k" = locN s "nkeys") := by
  exact phase2_packed_nal_while (phase2_packed_source_outer_body_nal_hoare h) rfl rfl

/-- Zeroed counters establish the record-boundary invariant from allocated keys. -/
theorem phase2_packed_outer_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedKeysReady s)
    (hn : locN s "nkeys" = txAccessSlots s (locN s "tx"))
    (hi : locN s "i" = 0) (hk : locN s "k" = 0) :
    PtxPackedOuterInv s := by
  refine ⟨hp, hn, ?_, ?_⟩
  · rw [hi]; exact Nat.zero_le _
  · simp [phase2_key_prefix, hi, hk]

/-- Initialization bridge from allocated, separated keys to the source loop. -/
theorem phase2_packed_nal_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hw : WorldOK s) (hp : PtxPackedKeysReady s)
    (hn : locN s "nkeys" = txAccessSlots s (locN s "tx"))
    (hi : locN s "i" = 0) (hk : locN s "k" = 0)
    (ht : Disj (locN s "tx", 384)
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hr : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hkw : ∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k)))
    (hiw : ∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hh : globN s "heap_ptr" ≤ 2 ^ 64)
    (hnw : ∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n)))
    (he : locN s "nal" = memW s (locN s "tx" + 216)) :
    PtxPackedNalIteration s :=
  ⟨⟨hw, phase2_packed_outer_zero s hp hn hi hk, ht, hr, hkw, hiw, hh⟩, hnw, he⟩

/-- Resources required before the source resets the two packing counters. -/
def PtxPackedInitReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ PtxPackedKeysReady s ∧
  locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
  Disj (locN s "tx", 384)
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
  Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
    (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
  globN s "heap_ptr" ≤ 2 ^ 64 ∧
  (∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
  locN s "nal" = memW s (locN s "tx" + 216)

/-- The actual declaration and assignment establish the packing-loop entry. -/
theorem phase2_packed_init_state {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedInitReady s) :
    PtxPackedNalIteration
      (setVarHOLFinite (ofString "i") (.val (.word 0))
        (setVarHOLFinite (ofString "k") (.val (.word 0)) s)) := by
  let t := setVarHOLFinite (ofString "i") (.val (.word 0))
    (setVarHOLFinite (ofString "k") (.val (.word 0)) s)
  have hl : ∀ n ∈ (["al_keys", "nkeys", "tx", "nal"] : List String),
      t.locals.lookup (ofString n) = s.locals.lookup (ofString n) := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;>
      simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  have hn (n : String) (hm : n ∈ (["al_keys", "nkeys", "tx", "nal"] : List String)) :
      locN t n = locN s n := by simp only [locN, hl n hm]
  have hready : PtxPackedKeysReady t := by
    apply phase2_packed_keys_with_locals s t.locals s.clock hp.2.1
    intro n hm
    apply hl n
    simp only [List.mem_cons, List.mem_singleton] at hm ⊢
    tauto
  change PtxPackedNalIteration t
  have hm : t.memory = s.memory := rfl
  apply phase2_packed_nal_zero t
  · exact phase2_packed_ready_worldOK t
      ((arenaReady_with_locals s t.locals s.clock).mpr hp.1.1) hready
  · exact hready
  · simpa only [hn "nkeys" (by simp), hn "tx" (by simp), txAccessSlots, memW, hm] using hp.2.2.1
  · simp [t, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simp [t, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  · simpa only [hn "tx" (by simp), hn "al_keys" (by simp), hn "nkeys" (by simp)]
      using hp.2.2.2.1
  · simpa only [hn "tx" (by simp), hn "al_keys" (by simp), hn "nkeys" (by simp), memW, hm]
      using hp.2.2.2.2.1
  · exact ⟨0, by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]⟩
  · exact ⟨0, by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
  · exact hp.2.2.2.2.2.1
  · simpa only [hl "nal" (by simp)] using hp.2.2.2.2.2.2.1
  · simpa only [hn "nal" (by simp), hn "tx" (by simp), memW, hm] using hp.2.2.2.2.2.2.2

/-- The source's counter initialization feeds the proved packing loop directly. -/
theorem phase2_packed_initialized_loop_hoare (h : PtxCallees) :
    Hoare PtxPackedInitReady
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      (fun r s => r = none → PtxPackedKeysReady s) := by
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx"])
    (P' := fun s => ∃ before, PtxPackedInitReady before ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before) (by decide)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · apply Hoare.seq_fall (R := PtxPackedNalIteration)
    · apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        exact fun _ => phase2_packed_init_state before hp
      · exact fun _ _ hr => by cases hr
    · refine ⟨?_⟩
      intro F s hc hp hnt hr
      exact ((phase2_packed_source_outer_loop_hoare h).run s hc hp hnt hr).1.1.2.1.1
  · intro F r s locals hl hp hr
    exact phase2_packed_keys_with_locals s locals s.clock (hp hr) hl
  · exact fun _ _ hr => by cases hr

/-- Packed allocation retains the arena needed to turn its joint witness into
the world component of the packing-loop entry invariant. -/
theorem phase2_packed_keys_alloc_world_ready (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s => WorldOK s ∧ PtxPackedKeysReady s)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hready := phase2_packed_keys_alloc_ready h s vs body callee ret v post hc hp ha hl hb
  have hcount : PtxAccessCountReady s := hp.1.1.1.1
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hcount.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hpost := hw (Or.inl ⟨v, rfl⟩)
  refine ⟨phase2_packed_ready_worldOK _ ?_ hready, hready⟩
  exact (arenaReady_with_locals post _ post.clock).mpr hpost.1

/-- Restoring the packed allocation result preserves every transaction-header word. -/
theorem phase2_packed_alloc_header_words (h : PtxCallees)
    (k value : Nat) (hk : k % 8 = 0) (hkle : k + 8 ≤ 384) :
    DecCallResumeOn
      (fun s => PtxAddressCountInv s ∧ memW s (locN s "tx" + k) = value)
      (fun s => memW s (locN s "tx" + k) = value)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have he := phase2_alloc_header_words h _ k value hk hkle
    s vs body callee ret v post hc ⟨hp.1.1.1.1.1, hp.2⟩ ha hl hb
  simpa [locN, memW, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "al_addrs" ≠ ofString "tx" by decide,
    show ofString "al_keys" ≠ ofString "tx" by decide] using he

/-- The positive-count branch retains its cached record bound across allocation. -/
theorem phase2_packed_alloc_nal (h : PtxCallees) :
    DecCallResumeOn
      (fun s => PtxAddressCountInv s ∧ locN s "nal" = memW s (locN s "tx" + 216))
      (fun s => (∃ n : BitVec 64, s.locals.lookup (ofString "nal") = some (.val (.word n))) ∧
        locN s "nal" = memW s (locN s "tx" + 216))
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have he := phase2_packed_alloc_header_words h 216 (locN s "nal") (by decide) (by decide)
    s vs body callee ret v post hc ⟨hp.1, hp.2.symm⟩ ha hl hb
  have hr : PtxAccessCountReady s := hp.1.1.1.1.1
  constructor
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nal" by decide] using hr.2.1
  · rw [he]
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nal" by decide]

/-- The fresh packed buffer remains separate from the transaction and record array
after restoring the caller's locals, including the empty-record case. -/
theorem phase2_packed_alloc_input_separated (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountInv
      (fun s =>
        Disj (locN s "tx", 384)
          (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8) ∧
        Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
          (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have h208 := phase2_packed_alloc_header_words h 208 (memW s (locN s "tx" + 208))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  have h216 := phase2_packed_alloc_header_words h 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp, rfl⟩ ha hl hb
  obtain ⟨w, rfl, hf⟩ := phase2_packed_keys_alloc_fresh h s vs body callee ret v post
    hc hp ha hl hb
  have hs := phase2_packed_keys_input_separation s post callee w.toNat hp hf
  rw [h208, h216]
  simp only [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    show ofString "al_keys" ≠ ofString "tx" by decide,
    show ofString "al_keys" ≠ ofString "nkeys" by decide, if_false, if_true]
  constructor
  · exact hs.2.1
  · by_cases hz : memW s (locN s "tx" + 216) = 0
    · exact Or.inl (by change 24 * memW s (locN s "tx" + 216) = 0; rw [hz])
    · exact hs.2.2 (Nat.pos_of_ne_zero hz)

/-- Allocation frames each access-record key count, preserving the total used
to size the packed buffer. -/
theorem phase2_packed_alloc_total (h : PtxCallees) (value : Nat) :
    DecCallResumeOn
      (fun s => PtxAddressCountInv s ∧ txAccessSlots s (locN s "tx") = value)
      (fun s => txAccessSlots s (locN s "tx") = value)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr : PtxAccessCountReady s := hp.1.1.1.1.1
  have h208 := phase2_packed_alloc_header_words h 208 (memW s (locN s "tx" + 208))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp.1, rfl⟩ ha hl hb
  have h216 := phase2_packed_alloc_header_words h 216 (memW s (locN s "tx" + 216))
    (by decide) (by decide) s vs body callee ret v post hc ⟨hp.1, rfl⟩ ha hl hb
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hr.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hW, hT, _⟩ := hr.1.2
  obtain ⟨S', Nd', _, _, _, hframe, _⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hfields : ∀ i, i < memW s (locN s "tx" + 216) →
      memW post (memW s (locN s "tx" + 208) + 24 * i + 16) =
        memW s (memW s (locN s "tx" + 208) + 24 * i + 16) := by
    intro i hi
    exact phase2_tx_count_world_frame s post S Nd [] (locN s "tx") i
      hr.1.1.1.1.1.1.1.1.2 hW hT hi hframe (by simp) (by simp)
  unfold txAccessSlots
  rw [h216, h208]
  trans txAccessSlots s (locN s "tx")
  · unfold txAccessSlots
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hfields i (List.mem_range.mp hi)
  · exact hp.2

/-- Allocation assembles all resources consumed by the concrete counter reset. -/
theorem phase2_packed_alloc_init_ready (h : PtxCallees) :
    DecCallResumeOn
      (fun s => PtxAddressCountInv s ∧
        locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
        locN s "nal" = memW s (locN s "tx" + 216))
      PtxPackedInitReady (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hw := phase2_packed_keys_alloc_world_ready h s vs body callee ret v post hc hp.1 ha hl hb
  have hs := phase2_packed_alloc_input_separated h s vs body callee ret v post hc hp.1 ha hl hb
  have hn := phase2_packed_alloc_nal h s vs body callee ret v post hc ⟨hp.1, hp.2.2⟩ ha hl hb
  have ht := phase2_packed_alloc_total h (locN s "nkeys") s vs body callee ret v post
    hc ⟨hp.1, hp.2.1.symm⟩ ha hl hb
  refine ⟨hw.1, hw.2, ?_, hs.1, hs.2, ?_, hn⟩
  · rw [ht]
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide]
  · unfold globN
    split
    · exact Nat.le_of_lt (BitVec.isLt _)
    · exact Nat.zero_le _

/-- The counting-loop exit supplies both equalities required by packed allocation. -/
theorem phase2_count_exit_alloc_pre {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountInv s ∧ locN s "i" = locN s "nal") :
    PtxAddressCountInv s ∧ locN s "nkeys" = txAccessSlots s (locN s "tx") ∧
      locN s "nal" = memW s (locN s "tx" + 216) :=
  ⟨hp.1, phase2_address_count_exit_total hp.1 hp.2, hp.1.2.1⟩

/-- Packed allocation is ready for initialization directly from counting-loop exit. -/
theorem phase2_count_exit_alloc_ready (h : PtxCallees) :
    DecCallResumeOn
      (fun s => PtxAddressCountInv s ∧ locN s "i" = locN s "nal")
      PtxPackedInitReady (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  exact phase2_packed_alloc_init_ready h s vs body callee ret v post hc
    (phase2_count_exit_alloc_pre s hp) ha hl hb

/-- The counted allocation exposes the full initialization predicate to its tail. -/
theorem phase2_count_exit_alloc_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxPackedInitReady tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxAddressCountInv s ∧ locN s "i" = locN s "nal")
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxPackedInitReady) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr : PtxAccessCountReady s := hp.1.1.1.1.1
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact phase2_count_exit_alloc_ready h
  · exact ht

/-- A zero cached access count skips either source loop, independently of its body. -/
theorem phase2_zero_nal_loop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (body : ProgHOL 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word 0)))
    (hn : s.locals.lookup (ofString "nal") = some (.val (.word 0))) :
    evaluateHOLFiniteState s
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) =
      (none, s) := by
  rw [evaluateHOLFiniteState_while_total]
  simp [evalHOLExact, hi, hn]
  intro h
  have hf : Compiler.Encoders.Asm.wordCmpHOL .less (0#64) (0#64) ≠ true := by decide
  exact False.elim (hf h)

/-- Scalar shape plus a zero numeric projection identifies the actual zero word. -/
theorem phase2_local_zero_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : String)
    (hw : ∃ w : BitVec 64, s.locals.lookup (ofString name) = some (.val (.word w)))
    (hz : locN s name = 0) :
    s.locals.lookup (ofString name) = some (.val (.word 0)) := by
  obtain ⟨w, hw⟩ := hw
  have hn : w.toNat = 0 := by simpa [locN, hw] using hz
  have he : w = 0 := BitVec.eq_of_toNat_eq hn
  simpa [he] using hw

/-- The address-copy invariant alone suffices to skip a zero-count loop. -/
theorem phase2_address_zero_loop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (body : ProgHOL 64) (hp : PtxAddressCopyInv s) (hn : locN s "nal" = 0) :
    evaluateHOLFiniteState s
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) =
      (none, s) := by
  apply phase2_zero_nal_loop
  · apply phase2_local_zero_word s "i" hp.2.1
    have hi := hp.2.2.2
    omega
  · exact phase2_local_zero_word s "nal" hp.1.1.1.2.1 hn

/-- Counting entry includes the no-access-list case without equating a disabled
cached count with the transaction's unused header field. -/
def PtxAddressCountCases {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxAddressCountInv s ∨
    (PtxAddressCopyInv s ∧ locN s "nal" = 0 ∧ locN s "nkeys" = 0)

theorem phase2_address_count_cases_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressJoint s) :
    PtxAddressCountCases (setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "nkeys") (.val (.word 0)) s)) := by
  by_cases hn : locN s "nal" = 0
  · refine Or.inr ⟨phase2_address_copy_init s hp, ?_, ?_⟩
    · simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
        show ofString "i" ≠ ofString "nal" by decide,
        show ofString "nkeys" ≠ ofString "nal" by decide] using hn
    · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · exact Or.inl (phase2_address_count_init s hp hn)

/-- Both counting cases exit with a complete allocation size: the active case
has the full key sum, and the disabled case retains its initialized zero. -/
def PtxAddressCountExit {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (PtxAddressCountInv s ∧ locN s "i" = locN s "nal") ∨
    (PtxAddressCopyInv s ∧ locN s "nal" = 0 ∧ locN s "nkeys" = 0)

theorem phase2_count_cases_while_hoare {body : ProgHOL 64}
    (hb : Hoare PtxAddressCountInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → PtxAddressCountInv s ∧ locN s "i" = locN s "nal")) :
    Hoare PtxAddressCountCases
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → PtxAddressCountExit s) := by
  refine ⟨?_⟩
  intro F s hc hp hnt hr
  rcases hp with hp | hp
  · exact Or.inl (hb.run s hc hp hnt hr)
  · rw [phase2_address_zero_loop s body hp.1 hp.2.1]
    exact Or.inr hp

/-- The disabled count has the same allocation bound without using any header
count equality. -/
theorem phase2_count_cases_alloc_size {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountExit s) : locN s "nkeys" * 52 + 8 < 2 ^ 64 := by
  rcases hp with hp | hp
  · exact phase2_address_count_alloc_bound hp.1
  · rw [hp.2.2]
    decide

/-- The concrete packed-allocation expression is nonwrapping in both cases. -/
theorem phase2_count_cases_alloc_eval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountExit s) :
    ∃ w : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52],
        .const 8]) = some (.val (.word w)) ∧
      w.toNat = locN s "nkeys" * 52 + 8 ∧
      locN s "nkeys" * 52 ≤ (w.toNat + 7) / 8 * 8 := by
  apply phase2_key_alloc_size_nonwrapping s
  · rcases hp with hp | hp
    · exact hp.1.1
    · exact hp.1
  · exact phase2_count_cases_alloc_size s hp

/-- Fresh allocation is valid for both the counted and disabled access-list cases. -/
theorem phase2_count_cases_alloc_fresh (h : PtxCallees) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hp : PtxAddressCountExit s)
    (ha : @evalListHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hb : (callEntryStateHOLFinite s callee).evaluateHOLFiniteState body =
      (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      FreshBlock (callEntryStateHOLFinite s callee) post w.toNat (locN s "nkeys" * 52 + 8) := by
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_count_cases_alloc_eval s hp
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hready : PtxAccessCountReady s := by
    rcases hp with hp | hp
    · exact hp.1.1.1.1.1
    · exact hp.1.1.1.1
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hready.1.1.1.1.1.1.1.1)
    (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, hv, _, _, hf⟩ := hr v rfl
  exact ⟨w, hv, by simpa only [hcn] using hf⟩

theorem phase2_count_exit_access_ready {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountExit s) : PtxAccessCountReady s := by
  rcases hp with hp | hp
  · exact hp.1.1.1.1.1
  · exact hp.1.1.1.1

/-- The disabled case also obtains a live, world-separated packed buffer. -/
theorem phase2_count_cases_packed_ready (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountExit PtxPackedKeysReady
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hready := phase2_count_exit_access_ready hp
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_count_cases_alloc_eval s hp
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
  obtain ⟨w, rfl, hf⟩ := phase2_count_cases_alloc_fresh h s vs body callee ret v post hc hp ha hl hb
  obtain ⟨w', hv, hav⟩ := hret (.val (.word w)) rfl
  cases hv
  dsimp only at hav
  rw [hcn] at hav
  let out := setVarHOLFinite (ofString "al_keys") (.val (.word w)) { post with locals := s.locals }
  have hptr : locN out "al_keys" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nkeys" = locN s "nkeys" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide]
  refine ⟨⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩, ?_, ?_, ?_,
    S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_⟩
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
  · have ht := R16Shards.PtxP1.txAccessListAt_with_locals post out.locals post.clock hTp
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "tx" by decide] using ht
  · change IvlsDisj [(locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned post S' Nd')
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide] using hav

/-- Packing entry separates the enabled input-count invariant from a disabled
loop whose freshly allocated buffer is already ready. -/
def PtxPackedInitCases {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedInitReady s ∨ (PtxPackedKeysReady s ∧
    s.locals.lookup (ofString "nal") = some (.val (.word 0)))

theorem phase2_count_cases_alloc_init (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountExit PtxPackedInitCases
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  rcases hp with hp | hp
  · exact Or.inl (phase2_count_exit_alloc_ready h s vs body callee ret v post hc hp ha hl hb)
  · refine Or.inr ⟨phase2_count_cases_packed_ready h s vs body callee ret v post
      hc (Or.inr hp) ha hl hb, ?_⟩
    have hn := phase2_local_zero_word s "nal" hp.1.1.1.1.2.1 hp.2.1
    simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nal" by decide] using hn

/-- Resetting counters in the disabled case preserves the packed allocation and
provides literal zero words for the source loop test. -/
theorem phase2_packed_zero_init {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxPackedKeysReady s)
    (hn : s.locals.lookup (ofString "nal") = some (.val (.word 0))) :
    let t := setVarHOLFinite (ofString "i") (.val (.word 0))
      (setVarHOLFinite (ofString "k") (.val (.word 0)) s)
    PtxPackedKeysReady t ∧
      t.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
      t.locals.lookup (ofString "nal") = some (.val (.word 0)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply phase2_packed_keys_with_locals s _ s.clock hp
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using hn

/-- The source packing loop is correct for enabled and disabled access lists. -/
theorem phase2_packed_cases_initialized_loop_hoare (h : PtxCallees) :
    Hoare PtxPackedInitCases
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      (fun r s => r = none → PtxPackedKeysReady s) := by
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx"])
    (P' := fun s => ∃ before, PtxPackedInitCases before ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before) (by decide)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · apply Hoare.seq_fall (R := fun s => PtxPackedNalIteration s ∨
      (PtxPackedKeysReady s ∧
        s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
        s.locals.lookup (ofString "nal") = some (.val (.word 0))))
    · apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        rcases hp with hp | hp
        · exact Or.inl (phase2_packed_init_state before hp)
        · exact Or.inr (phase2_packed_zero_init before hp.1 hp.2)
      · exact fun _ _ hr => by cases hr
    · refine ⟨?_⟩
      intro F s hc hp hnt hr
      rcases hp with hp | hp
      · exact ((phase2_packed_source_outer_loop_hoare h).run s hc hp hnt hr).1.1.2.1.1
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.1 hp.2.2]
        exact hp.1
  · intro F r s locals hl hp hr
    exact phase2_packed_keys_with_locals s locals s.clock (hp hr) hl
  · exact fun _ _ hr => by cases hr

/-- The cached-count inner loop has a uniform rank bound once its active body
bound is supplied; the rank is the remaining signed counter range. -/
theorem phase2_packed_ns_nal_while_bound {body : ProgHOL 64} {B : Nat}
    (hb : Hoare PtxPackedNsNalCopy body (fun r s => r = none → PtxPackedNsNalIteration s))
    (hbody : TerminatingProgBoundedOn PtxPackedNsNalCopy body B)
    (hinc : IncrBody (ofString "j") body) :
    TerminatingProgBoundedOn PtxPackedNsNalIteration
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      ((2 ^ 63 + 1) * (B + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "j")
  · intro F s hp
    exact ⟨phase2_packed_ns_iteration_decClock s hp.1, hp.2⟩
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_ns_guard_eval s w hp.1.1 hw).mp hnz
    exact hbody s hc ⟨⟨phase2_packed_iteration_guard_pre s hp.1.1.1 hg, hp.1.1.2⟩, hp.1.2⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_ns_guard_eval s w hp.1 hw).mp hnz
    have hd : PtxPackedNsNalIteration (decClockHOLFinite s) :=
      ⟨phase2_packed_ns_iteration_decClock s hp.1, hp.2⟩
    obtain ⟨j, hj⟩ := hp.1.1.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) j hj
    have hnone := hf.resolve_right hnc
    have hpost := hb.run (decClockHOLFinite s) hc
      ⟨⟨phase2_packed_iteration_guard_pre _ hd.1.1 hg, hd.1.2⟩, hd.2⟩
      (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hjn : locN s "j" = j.toNat := by simp [locN, hj]
    have hlt := (phase2_packed_inner_signed_bounds hp.1.1.2.1.1).1
    have hpl := (phase2_packed_inner_signed_bounds hpost.1.1.2.1.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s) body).2 "j" =
        (j.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hjn] at hlt ⊢
    rw [hpn]
    have hmod : (j.toNat + 1) % 2 ^ 64 = j.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at *
    omega

/-- Each concrete memcpy is bounded from the packed-copy world invariant. -/
theorem phase2_packed_ns_nal_memcpy_bound (h : PtxCallees) (args : List (ExpHOL 64)) :
    TerminatingProgBoundedOn PtxPackedNsNalCopy
      (.call (some (none, none)) (ofString "memcpy") args) (K.memcpy + 1) := by
  apply TerminatingProgBoundedOn.call_on h.fb_memcpy
  intro F s vs body callee ret hc hp ha hl
  exact guestInv_callEntry s callee (worldOK_guestInv s hp.1.1.1)

/-- Two copies and the two clock-neutral counter assignments give the exact
active inner-body budget used by the source Phase 2 cost. -/
theorem phase2_packed_ns_nal_body_bound (h : PtxCallees) (addressSrc keySrc : ExpHOL 64) :
    TerminatingProgBoundedOn PtxPackedNsNalCopy
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      ((K.memcpy + 1) + (K.memcpy + 1)) := by
  have hc : TerminatingProgBoundedOn PtxPackedNsNalCopy
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1]))) 0 := by
    intro F s hcode hp hn
    have he := phase2_clock_seq
      (fun t => clock_assign t .local (ofString "k")
        (.op .add [.var .local (ofString "k"), .const 1]))
      (fun t => clock_assign t .local (ofString "j")
        (.op .add [.var .local (ofString "j"), .const 1])) s
    rw [he]
    exact ⟨by omega, le_rfl⟩
  intro F s hcode hp
  simpa only [Nat.add_zero] using seq_bound_trans
    (phase2_packed_ns_nal_memcpy_bound h _) (phase2_packed_address_copy_ns_nal_hoare h addressSrc)
    (fun t ht hpt => seq_bound_trans (phase2_packed_ns_nal_memcpy_bound h _)
      (phase2_packed_storage_copy_ns_nal_hoare h keySrc) hc t ht hpt) s hcode hp

/-- The actual source inner loop and following record increment have the
advertised nested-loop clock budget. -/
theorem phase2_packed_source_inner_tail_bound (h : PtxCallees) :
    TerminatingProgBoundedOn PtxPackedNsNalIteration phase2_packed_source_inner_tail
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_inner_tail
  have hb : TerminatingProgBoundedOn PtxPackedNsNalIteration _
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) :=
    phase2_packed_ns_nal_while_bound
    (phase2_packed_body_ns_nal_hoare h
      (.load .one (.op .add [.var .local (ofString "acc2"), .const 0]))
      (.op .add [.load .one (.op .add [.var .local (ofString "acc2"), .const 8]),
        .panop .mul [.var .local (ofString "j"), .const 32]]))
    (phase2_packed_ns_nal_body_bound h _ _) (by ptx_incr)
  have ht : TerminatingProgBoundedOn
      (fun s => PtxPackedNsNalIteration s ∧ locN s "k" = phase2_key_prefix s (locN s "i" + 1))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) 0 := by
    intro F s hc hp hn
    rw [clock_assign]
    exact ⟨by omega, le_rfl⟩
  intro F s hc hp
  simpa only [Nat.add_zero] using seq_bound_trans hb
    (phase2_packed_ns_nal_while (phase2_packed_body_ns_nal_hoare h _ _) (by decide) (by decide))
    ht s hc hp

/-- The record-local declarations preserve the inner-loop clock budget. -/
theorem phase2_packed_source_outer_body_bound (h : PtxCallees) :
    TerminatingProgBoundedOn (fun s => PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) phase2_packed_source_outer_body
      ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1)) := by
  unfold phase2_packed_source_outer_body
  apply dec_bound_trans (Q := fun s => PtxPackedNalIteration s ∧
    locN s "i" < memW s (locN s "tx" + 216) ∧
    locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i")
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.1.1 hp.2 v he
    exact ⟨phase2_packed_nal_set_other s hp.1 _ _ (by decide), hd.2⟩
  · apply dec_bound_trans (Q := fun s => PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
      locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16))
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.1.1 hp.2.1 hp.2.2 v he
      exact ⟨phase2_packed_nal_set_other s hp.1 _ _ (by decide), hd.2⟩
    · apply dec_bound_trans (Q := PtxPackedNsNalIteration)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        refine ⟨phase2_packed_ns_reset s hp.1.1 hp.2.1 hp.2.2.1 hp.2.2.2, ?_⟩
        exact (phase2_packed_nal_set_other s hp.1 (ofString "j") (.val (.word 0)) (by decide)).2
      · exact phase2_packed_source_inner_tail_bound h

/-- A decreasing record counter bounds the concrete outer packing loop. -/
theorem phase2_packed_source_outer_loop_bound (h : PtxCallees) :
    TerminatingProgBoundedOn PtxPackedNalIteration
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
  apply TerminatingProgBoundedOn.while_rank_active (fun s => 2 ^ 63 - locN s "i")
  · intro F s hp
    exact phase2_packed_nal_iteration_decClock s hp
  · intro F s hc hp
    obtain ⟨w, hw, hnz⟩ := hp.2
    have hg := (phase2_packed_outer_nal_guard s w hp.1.1 hp.1.2.1 hp.1.2.2 hw).mp hnz
    exact phase2_packed_source_outer_body_bound h s hc ⟨hp.1, hg⟩
  · intro F s hc hp ha
    omega
  · intro F s hc hp ha hf
    obtain ⟨w, hw, hnz⟩ := ha
    have hg := (phase2_packed_outer_nal_guard s w hp.1 hp.2.1 hp.2.2 hw).mp hnz
    have hd := phase2_packed_nal_iteration_decClock s hp
    have hinc : IncrBody (ofString "i") phase2_packed_source_outer_body := by
      unfold phase2_packed_source_outer_body phase2_packed_source_inner_tail
      ptx_incr
    obtain ⟨i, hi⟩ := hp.1.2.2.2.2.2.1
    obtain ⟨hnc, hnext⟩ := hinc.run (decClockHOLFinite s) i hi
    have hnone := hf.resolve_right hnc
    have hpost := (phase2_packed_source_outer_body_nal_hoare h).run
      (decClockHOLFinite s) hc ⟨hd, hg⟩ (by rw [hnone]; simp) hnone
    refine ⟨hpost, ?_⟩
    have hin : locN s "i" = i.toNat := by simp [locN, hi]
    have hlt := (phase2_packed_outer_signed_bounds hp.1).1
    have hpn : locN (evaluateHOLFiniteState (decClockHOLFinite s)
        phase2_packed_source_outer_body).2 "i" = (i.toNat + 1) % 2 ^ 64 := by
      simp [locN, hnext hnone, BitVec.toNat_add]
    rw [hin] at hlt ⊢
    rw [hpn, Nat.mod_eq_of_lt (by omega : i.toNat + 1 < 2 ^ 64)]
    omega

/-- Counter initialization and the disabled-access branch share the concrete
packing-loop budget. -/
theorem phase2_packed_cases_initialized_loop_bound (h : PtxCallees) :
    TerminatingProgBoundedOn PtxPackedInitCases
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
  let P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    ∃ before, PtxPackedInitCases before ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before
  let Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    PtxPackedNalIteration s ∨ (PtxPackedKeysReady s ∧
      s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
      s.locals.lookup (ofString "nal") = some (.val (.word 0)))
  apply dec_bound_trans (Q := P)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · have ha : Hoare P (.assign .local (ofString "i") (.const 0))
        (fun r s => r = none → Q s) := by
      apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        rcases hp with hp | hp
        · exact Or.inl (phase2_packed_init_state before hp)
        · exact Or.inr (phase2_packed_zero_init before hp.1 hp.2)
      · exact fun _ _ hr => by cases hr
    have hb : TerminatingProgBoundedOn P
        (.assign .local (ofString "i") (.const 0)) 0 := by
      intro F s hc hp hn
      rw [clock_assign]
      exact ⟨by omega, le_rfl⟩
    have hl : TerminatingProgBoundedOn Q
        (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
          phase2_packed_source_outer_body)
        ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1)) := by
      intro F s hc hp hn
      rcases hp with hp | hp
      · exact phase2_packed_source_outer_loop_bound h s hc hp hn
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.1 hp.2.2]
        exact ⟨by dsimp; omega, le_rfl⟩
    intro F s hc hp
    simpa only [Nat.zero_add] using seq_bound_trans hb ha hl s hc hp

/-- Both counting exits support the fresh packed allocation and its continuation. -/
theorem phase2_count_cases_alloc_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn PtxPackedInitCases tail b) :
    TerminatingProgBoundedOn PtxAddressCountExit
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := PtxPackedInitCases) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact phase2_count_cases_alloc_init h
  · exact ht

/-- Disabling access lists cannot increase the counting-loop clock budget. -/
theorem phase2_count_cases_while_bound {body : ProgHOL 64} {b : Nat}
    (hb : TerminatingProgBoundedOn PtxAddressCountInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) b) :
    TerminatingProgBoundedOn PtxAddressCountCases
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body) b := by
  intro F s hc hp hn
  rcases hp with hp | hp
  · exact hb s hc hp hn
  · rw [phase2_address_zero_loop s body hp.1 hp.2.1]
    exact ⟨by dsimp; omega, le_rfl⟩

/-- Packing retains the world needed by the subsequent transaction setup calls. -/
theorem phase2_packed_cases_initialized_world_hoare (h : PtxCallees) :
    Hoare (fun s => WorldOK s ∧ PtxPackedInitCases s)
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      (fun r s => r = none → WorldOK s ∧ PtxPackedKeysReady s) := by
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx"])
    (P' := fun s => ∃ before, (WorldOK before ∧ PtxPackedInitCases before) ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before) (by decide)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · apply Hoare.seq_fall (R := fun s => PtxPackedNalIteration s ∨
      (WorldOK s ∧ PtxPackedKeysReady s ∧
        s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
        s.locals.lookup (ofString "nal") = some (.val (.word 0))))
    · apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        rcases hp.2 with hp' | hp'
        · exact Or.inl (phase2_packed_init_state before hp')
        · have hz := phase2_packed_zero_init before hp'.1 hp'.2
          exact Or.inr ⟨phase2_packed_ready_worldOK _
            ((arenaReady_with_locals before _ before.clock).mpr hp.1.1) hz.1, hz⟩
      · exact fun _ _ hr => by cases hr
    · refine ⟨?_⟩
      intro F s hc hp hnt hr
      rcases hp with hp | hp
      · have ho := ((phase2_packed_source_outer_loop_hoare h).run s hc hp hnt hr).1
        exact ⟨ho.1.1, ho.1.2.1.1⟩
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hp.2.2.1 hp.2.2.2]
        exact ⟨hp.1, hp.2.1⟩
  · intro F r s locals hl hp hr
    have hk := phase2_packed_keys_with_locals s locals s.clock (hp hr).2 hl
    exact ⟨phase2_packed_ready_worldOK _
      ((arenaReady_with_locals s locals s.clock).mpr (hp hr).1.1) hk, hk⟩
  · exact fun _ _ hr => by cases hr

/-- Allocation provides the world component for both packing entry cases. -/
theorem phase2_count_cases_alloc_world_init (h : PtxCallees) :
    DecCallResumeOn PtxAddressCountExit (fun s => WorldOK s ∧ PtxPackedInitCases s)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hi := phase2_count_cases_alloc_init h s vs body callee ret v post hc hp ha hl hb
  have hk := phase2_count_cases_packed_ready h s vs body callee ret v post hc hp ha hl hb
  have hr := phase2_count_exit_access_ready hp
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hr.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have hs := hw (Or.inl ⟨v, rfl⟩)
  exact ⟨phase2_packed_ready_worldOK _
    ((arenaReady_with_locals post _ post.clock).mpr hs.1) hk, hi⟩

/-- The packed allocation exposes its retained world to any subsequent setup. -/
theorem phase2_count_cases_alloc_world_bound (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => WorldOK s ∧ PtxPackedInitCases s) tail b) :
    TerminatingProgBoundedOn PtxAddressCountExit
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] tail)
      (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => WorldOK s ∧ PtxPackedInitCases s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact phase2_count_cases_alloc_world_init h
  · exact ht

/-- Initialized packing composes with a world-aware continuation. -/
theorem phase2_packed_world_continuation_bound (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s => WorldOK s ∧ PtxPackedKeysReady s) tail b) :
    TerminatingProgBoundedOn (fun s => WorldOK s ∧ PtxPackedInitCases s)
      (.seq
        (.dec (ofString "k") .one (.const 0)
          (.seq (.assign .local (ofString "i") (.const 0))
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
              phase2_packed_source_outer_body))) tail)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
  intro F s hc hp
  exact seq_bound_trans
    (fun t hct hpt => phase2_packed_cases_initialized_loop_bound h t hct hpt.2)
    (phase2_packed_cases_initialized_world_hoare h) ht s hc hp

/-- A live caller buffer separated from world ownership and the copy destination
retains every aligned word through the supplied memcpy contract. -/
theorem phase2_memcpy_eval_live_buffer (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat) (buffer : Ivl)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hin : Inside buffer InitE.sourceBase (globN s "heap_ptr"))
    (hsep : ∀ region ∈ worldOwned (callEntryStateHOLFinite s callee) S Nd,
      Disj buffer region)
    (hcopy : Disj buffer (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    ∀ p, buffer.1 ≤ p → p + 8 ≤ buffer.1 + buffer.2 → p % 8 = 0 →
      memW post p = memW s p := by
  obtain ⟨S', Nd', hw', hg, hf⟩ :=
    phase2_memcpy_eval_world_frame h s post vs body callee ret r S Nd hc hl he hn hr hp hw hd
  intro p hlo hhi hal
  apply phase2_world_frame_heap_disjoint s {post with locals := s.locals}
    (worldOwned (callEntryStateHOLFinite s callee) S Nd)
    [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] buffer p
    hp.1.2 hin ⟨hlo, hhi⟩ hal hf hsep
  · intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hcopy
  · exact worldOwned_zero_aligned hw
  · intro region hm hz
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at hz
    omega

/-- Caller-owned word contents carried alongside a world witness. -/
def PtxLiveBufferAt {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (buffer : Ivl) (contents : Nat → BitVec 64) : Prop :=
  Inside buffer InitE.sourceBase (globN s "heap_ptr") ∧
  IvlsDisj [buffer] (worldOwned s S Nd) ∧
  ∀ p, buffer.1 ≤ p → p + 8 ≤ buffer.1 + buffer.2 → p % 8 = 0 →
    memW s p = (contents p).toNat

/-- A world step with separated writes preserves a caller buffer's contents
and ownership, allowing the same frame to be reused by the next call. -/
theorem phase2_live_buffer_step {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat)
    (buffer : Ivl) (contents : Nat → BitVec 64) (writes : List Ivl)
    (hp : PtxLiveBufferAt s S Nd buffer contents)
    (ha : ArenaOK s) (hw : WorldTypedWith s S Nd)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ writes ++ [freeGap s]) (heapFree s))
    (hd : ∀ region ∈ writes, Disj buffer region)
    (hz : ∀ region ∈ writes, region.2 = 0 → region.1 % 8 = 0) :
    PtxLiveBufferAt post S' Nd' buffer contents := by
  refine ⟨⟨hp.1.1, hp.1.2.trans hh⟩,
    phase2_packed_owned_growth s post _ _ buffer hp.1 hg hp.2.1, ?_⟩
  intro p hlo hhi hal
  rw [phase2_world_frame_heap_disjoint s post _ writes buffer p ha hp.1
    ⟨hlo, hhi⟩ hal hf (hp.2.1 buffer (by simp)) hd (worldOwned_zero_aligned hw) hz]
  exact hp.2.2 p hlo hhi hal

/-- The live-buffer predicate is independent of caller-local scope and clock. -/
theorem phase2_live_buffer_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (S Nd : List Nat) (buffer : Ivl) (contents : Nat → BitVec 64) :
    PtxLiveBufferAt {s with locals := locals, clock := clock} S Nd buffer contents ↔
      PtxLiveBufferAt s S Nd buffer contents := by
  rfl

/-- A concrete copy returns a joint world/live-buffer witness suitable for
the next iteration, rather than only pointwise memory equalities. -/
theorem phase2_memcpy_eval_live_buffer_next (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (S Nd : List Nat)
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (hw : WorldTypedWith (callEntryStateHOLFinite s callee) S Nd)
    (hb : PtxLiveBufferAt s S Nd buffer contents)
    (hd : IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")]
      (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hcopy : Disj buffer (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    ∃ S' Nd', WorldTypedWith {post with locals := s.locals} S' Nd' ∧
      PtxLiveBufferAt {post with locals := s.locals} S' Nd' buffer contents := by
  obtain ⟨S', Nd', hw', hg, hf⟩ :=
    phase2_memcpy_eval_world_frame h s post vs body callee ret r S Nd hc hl he hn hr hp hw hd
  have hglobals := phase2_memcpy_eval_globals h s post vs body callee ret r hc hl he hn hr hp
  have hh := (phase2_copy_globals_heap_eq s {post with locals := s.locals} hglobals).symm.le
  refine ⟨S', Nd', (worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hw', ?_⟩
  apply phase2_live_buffer_step s {post with locals := s.locals} S Nd S' Nd'
    buffer contents [(locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n")] hb hp.1.2
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mp hw) hh hg hf
  · intro region hm
    simp only [List.mem_singleton] at hm
    subst region
    exact hcopy
  · intro region hm hz
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at hz
    omega

/-- Packing and a saved caller buffer share the same ownership witness. -/
def PtxPackedLiveCopy {F : Type} (s : PanSemStateFiniteExact 64 F)
    (buffer : Ivl) (contents : Nat → BitVec 64) : Prop :=
  PtxPackedSeparatedCopy s ∧
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd) ∧ PtxLiveBufferAt s S Nd buffer contents

/-- Restore packing and caller contents from one copy frame, keeping their
world witnesses synchronized for the following copy. -/
theorem phase2_packed_live_copy_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (S Nd S' Nd' : List Nat) (dst len : Nat)
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hi : PtxPackedSeparatedCopy s) (ha : ArenaReady s) (hpost : GuestInv post)
    (hg : GlobalsKept [] s post)
    (hw : WorldTypedWith s S Nd) (hw' : WorldTypedWith post S' Nd')
    (ht : TxAccessListAt s S Nd (locN s "tx"))
    (hs : IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd))
    (hb : PtxLiveBufferAt s S Nd buffer contents)
    (ho : OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd'))
    (hf : FrameOutside s post (worldOwned s S Nd ++ [(dst, len)] ++ [freeGap s]) (heapFree s))
    (htx : Disj (locN s "tx", 384) (dst, len))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216)) (dst, len))
    (hbuf : Disj buffer (dst, len)) (hlen : 0 < len) :
    PtxPackedLiveCopy {post with locals := s.locals} buffer contents := by
  have hh := (phase2_copy_globals_heap_eq s post hg).symm.le
  have hz : ∀ region ∈ ([(dst, len)] : List Ivl), region.2 = 0 → region.1 % 8 = 0 := by
    intro region hm he
    simp only [List.mem_singleton] at hm
    subst region
    dsimp at he
    omega
  have ht' := R16Shards.PtxP1.txAccessListOK_survives_step ha hpost hh hw hz ho hf ht
    (by simpa only [List.mem_singleton, forall_eq] using htx)
    (by simpa only [List.mem_singleton, forall_eq] using (fun _ => hrec :
      0 < memW s (locN s "tx" + 216) → _)) (locals := s.locals) rfl
  refine ⟨phase2_packed_separated_of_copy_frame s post S Nd S' Nd' dst len
    hi ha hpost hg hw hw' ht hs ho hf htx hrec hlen,
    S', Nd', (worldTypedWith_with_locals post s.locals post.clock S' Nd').mpr hw', ht', ?_, ?_⟩
  · exact phase2_packed_owned_growth s post _ _ _ hi.1.1.2.1 ho hs
  · exact phase2_live_buffer_step s {post with locals := s.locals} S Nd S' Nd'
      buffer contents [(dst, len)] hb ha.2 hw hh ho hf
      (by simpa only [List.mem_singleton, forall_eq] using hbuf) hz

/-- A concrete resuming copy preserves packing together with caller contents. -/
theorem phase2_memcpy_eval_packed_live (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (buffer : Ivl) (contents : Nat → BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedLiveCopy s buffer contents)
    (hd : ∀ S Nd, WorldTypedWith s S Nd →
      IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
        (worldOwned s S Nd) →
      IvlsDisj [(locN (callEntryStateHOLFinite s callee) "dst",
        locN (callEntryStateHOLFinite s callee) "n")]
        (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (htx : Disj (locN s "tx", 384) (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hrec : Disj (memW s (locN s "tx" + 208), 24 * memW s (locN s "tx" + 216))
      (locN (callEntryStateHOLFinite s callee) "dst", locN (callEntryStateHOLFinite s callee) "n"))
    (hbuf : Disj buffer (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n"))
    (hlen : 0 < locN (callEntryStateHOLFinite s callee) "n") :
    PtxPackedLiveCopy {post with locals := s.locals} buffer contents := by
  obtain ⟨hindex, S, Nd, hw, ht, hsep, hb⟩ := hi
  have hs := R16Shards.PtxP1.funSpec_at_lookup h.wk_memcpy
    s hc vs body callee ret hl hp (by rw [he]; exact hn)
  rw [he] at hs
  have step := hs hr
  have hwe := (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw
  obtain ⟨S', Nd', _, hw', ho, hf, _⟩ := step.2.2.2.2 S Nd hwe (hd S Nd hw hsep)
  exact phase2_packed_live_copy_frame s post S Nd S' Nd' _ _ buffer contents
    hindex ha step.1.1 step.2.2.1 hw hw' ht hsep hb ho hf htx hrec hbuf hlen

/-- Either concrete packed destination preserves the shared caller resource. -/
theorem phase2_memcpy_eval_packed_live_destination (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (buffer : Ivl) (contents : Nat → BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedLiveCopy s buffer contents)
    (hb : Disj buffer (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hdest : (locN (callEntryStateHOLFinite s callee) "dst",
      locN (callEntryStateHOLFinite s callee) "n") ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedLiveCopy {post with locals := s.locals} buffer contents := by
  have hregions := phase2_packed_copy_input_regions s hi.1.1 hi.1.2.1 hi.1.2.2 _ hdest
  have hbuffer := phase2_packed_guarded_input_disjoint s hi.1.1 buffer hb
  refine phase2_memcpy_eval_packed_live h s post vs body callee ret r buffer contents
    hc hl he hn hr hp ha hi ?_ hregions.1 hregions.2 ?_ ?_
  · intro S Nd hw hs
    apply phase2_packed_typed_of_owned (callEntryStateHOLFinite s callee) S Nd
    intro dest hmem region hregion
    simp only [List.mem_singleton] at hmem
    subst dest
    have hdis := hs (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)
      (by simp) region hregion
    have hc' := phase2_packed_guarded_input_disjoint s hi.1.1 region (disj_symm hdis)
    rcases List.mem_cons.mp hdest with heq | hm
    · rw [heq]
      exact disj_symm hc'.1
    · have heq := List.mem_singleton.mp hm
      rw [heq]
      exact disj_symm hc'.2
  · rcases List.mem_cons.mp hdest with heq | hm
    · rw [heq]
      exact hbuffer.1
    · rw [List.mem_singleton.mp hm]
      exact hbuffer.2
  · rcases List.mem_cons.mp hdest with heq | hm
    · have heq' := congrArg Prod.snd heq
      change locN (callEntryStateHOLFinite s callee) "n" = 20 at heq'
      omega
    · have heq' := congrArg Prod.snd (List.mem_singleton.mp hm)
      change locN (callEntryStateHOLFinite s callee) "n" = 32 at heq'
      omega

/-- Evaluated source arguments connect the live-resource invariant to either
of the actual packing calls. -/
theorem phase2_memcpy_packed_arguments_live (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (dst src len : ExpHOL 64)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL)
    (r : Option (PanSemResultExact 64)) (d n : BitVec 64)
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dst, src, len] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "memcpy") vs = some (body, callee, ret))
    (he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (r, post))
    (hn : r ≠ some .timeOut) (hr : Resumes r)
    (hp : WorldOK (callEntryStateHOLFinite s callee))
    (ha : ArenaReady s) (hi : PtxPackedLiveCopy s buffer contents)
    (hb : Disj buffer (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8))
    (hd : evalAt s dst = some (.val (.word d)))
    (hlen : evalAt s len = some (.val (.word n)))
    (hpair : (d.toNat, n.toNat) ∈
      [(locN s "al_keys" + 52 * locN s "k", 20),
       (locN s "al_keys" + 52 * locN s "k" + 20, 32)]) :
    PtxPackedLiveCopy {post with locals := s.locals} buffer contents ∧
      Disj buffer (locN {post with locals := s.locals} "al_keys",
        (locN {post with locals := s.locals} "nkeys" * 52 + 8 + 7) / 8 * 8) := by
  refine ⟨?_, hb⟩
  have hentry := phase2_memcpy_entry_destination s dst src len vs body callee ret d n
    hc hargs hl hd hlen
  apply phase2_memcpy_eval_packed_live_destination h s post vs body callee ret r
    buffer contents hc hl he hn hr hp ha hi hb
  change (locN {s with locals := callee, clock := s.clock - 1} "dst",
    locN {s with locals := callee, clock := s.clock - 1} "n") ∈ _
  rw [hentry.1, hentry.2]
  exact hpair

/-- Call-ready packing state carrying a fixed caller buffer through both copies. -/
def PtxPackedLiveCall {F : Type} (buffer : Ivl) (contents : Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ PtxPackedLiveCopy s buffer contents ∧
    (∃ k : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word k))) ∧
    globN s "heap_ptr" ≤ 2 ^ 64 ∧
    Disj buffer (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

/-- The source address-copy command preserves the caller-buffer call invariant. -/
theorem phase2_packed_address_copy_live_hoare (h : PtxCallees) (src : ExpHOL 64)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (PtxPackedLiveCall buffer contents)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52]], src, .const 20])
      (fun r t => r = none → PtxPackedLiveCall buffer contents t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1 callee
  have hcopy := phase2_memcpy_packed_arguments_live h s post _ src (.const 20)
    vs body callee ret (some (.returned v)) (base + k * 52) 20 buffer contents
    hc hargs hl he (by simp) (by simp [Resumes]) hentry hp.1.1 hp.2.1 hp.2.2.2.2
    (phase2_packed_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) (by
      rw [phase2_packed_destination_toNat s hp.2.1.1.1 base k hbase hk hp.2.2.2.1]
      simp)
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.2.2.2.1
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  have hn := phase2_packed_next_call_pre s post harena.1 hcopy.1.1 ⟨k, hk⟩ hg hp.2.2.2.1
  exact ⟨hn.1, hcopy.1, hn.2.2.1, hn.2.2.2, hcopy.2⟩

/-- The source key-copy command preserves the caller-buffer call invariant. -/
theorem phase2_packed_storage_copy_live_hoare (h : PtxCallees) (src : ExpHOL 64)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (PtxPackedLiveCall buffer contents)
      (.call (some (none, none)) (ofString "memcpy")
        [.op .add [.var .local (ofString "al_keys"),
          .panop .mul [.var .local (ofString "k"), .const 52], .const 20], src, .const 32])
      (fun r t => r = none → PtxPackedLiveCall buffer contents t) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp hargs hl he
  obtain ⟨base, hbase⟩ := hp.2.1.1.1.1.1
  obtain ⟨k, hk⟩ := hp.2.2.1
  have hentry := R16Shards.PtxP1.worldOK_callEntry hp.1 callee
  have hcopy := phase2_memcpy_packed_arguments_live h s post _ src (.const 32)
    vs body callee ret (some (.returned v)) (base + k * 52 + 20) 32 buffer contents
    hc hargs hl he (by simp) (by simp [Resumes]) hentry hp.1.1 hp.2.1 hp.2.2.2.2
    (phase2_packed_key_destination_eval s base k hbase hk)
    (by simp [evalAt, evalHOLExact]) (by
      rw [phase2_packed_key_destination_toNat s hp.2.1.1.1 base k hbase hk hp.2.2.2.1]
      simp)
  have harena := phase2_memcpy_eval_next_arena h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry hp.2.2.2.1
  have hg := phase2_memcpy_eval_globals h s post vs body callee ret
    (some (.returned v)) hc hl he (by simp) (by simp [Resumes]) hentry
  have hn := phase2_packed_next_call_pre s post harena.1 hcopy.1.1 ⟨k, hk⟩ hg hp.2.2.2.1
  exact ⟨hn.1, hcopy.1, hn.2.2.1, hn.2.2.2, hcopy.2⟩

/-- Both source-order copies retain the same saved caller contents. -/
theorem phase2_packed_copies_live_hoare (h : PtxCallees)
    (addressSrc keySrc : ExpHOL 64) (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (PtxPackedLiveCall buffer contents)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32]))
      (fun r t => r = none → PtxPackedLiveCall buffer contents t) := by
  exact Hoare.seq_fall (phase2_packed_address_copy_live_hoare h addressSrc buffer contents)
    (phase2_packed_storage_copy_live_hoare h keySrc buffer contents)

/-- Saved caller resources at loop boundaries, independent of the loop indices. -/
def PtxPackedLiveResource {F : Type} (buffer : Ivl) (contents : Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
    IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)]
      (worldOwned s S Nd) ∧ PtxLiveBufferAt s S Nd buffer contents

/-- Local counter changes retain the shared ownership witness and saved contents. -/
theorem phase2_packed_live_resource_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (buffer : Ivl) (contents : Nat → BitVec 64)
    (hp : PtxPackedLiveResource buffer contents s)
    (ht : locN {s with locals := locals, clock := clock} "tx" = locN s "tx")
    (ha : locN {s with locals := locals, clock := clock} "al_keys" = locN s "al_keys")
    (hn : locN {s with locals := locals, clock := clock} "nkeys" = locN s "nkeys") :
    PtxPackedLiveResource buffer contents {s with locals := locals, clock := clock} := by
  obtain ⟨S, Nd, hw, htx, hs, hb⟩ := hp
  refine ⟨S, Nd, (worldTypedWith_with_locals s locals clock S Nd).mpr hw, ?_, ?_, hb⟩
  · rw [ht]
    exact R16Shards.PtxP1.txAccessListAt_with_locals s locals clock htx
  · rw [ha, hn]
    exact hs

/-- Any assignment away from the resource pointers preserves the caller frame. -/
theorem phase2_packed_live_resource_assign (buffer : Ivl) (contents : Nat → BitVec 64)
    (name : MlS) (e : ExpHOL 64)
    (ht : name ≠ ofString "tx") (ha : name ≠ ofString "al_keys")
    (hn : name ≠ ofString "nkeys") :
    Hoare (PtxPackedLiveResource buffer contents) (.assign .local name e)
      (fun r s => r = none → PtxPackedLiveResource buffer contents s) := by
  apply Hoare.assign
  · intro F s v hp he hr
    apply phase2_packed_live_resource_locals s _ s.clock buffer contents hp
    all_goals simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ht, ha, hn]
  · exact fun _ _ hr => by cases hr

/-- Both loop-counter assignments preserve the saved caller frame. -/
theorem phase2_packed_live_resource_counters (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (PtxPackedLiveResource buffer contents)
      (.seq
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
        (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))
      (fun r s => r = none → PtxPackedLiveResource buffer contents s) := by
  exact Hoare.seq_fall
    (phase2_packed_live_resource_assign buffer contents _ _ (by decide) (by decide) (by decide))
    (phase2_packed_live_resource_assign buffer contents _ _ (by decide) (by decide) (by decide))

/-- The complete source-order copy/counter body preserves the saved caller frame. -/
theorem phase2_packed_body_live_resource_hoare (h : PtxCallees)
    (addressSrc keySrc : ExpHOL 64) (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (PtxPackedLiveCall buffer contents)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedLiveResource buffer contents s) := by
  apply Hoare.seq_fall (phase2_packed_address_copy_live_hoare h addressSrc buffer contents)
  apply Hoare.seq_fall (phase2_packed_storage_copy_live_hoare h keySrc buffer contents)
  exact Hoare.mono (phase2_packed_live_resource_counters buffer contents)
    (fun _ hp => hp.2.1.2)

def PtxPackedLiveFrame {F : Type} (buffer : Ivl) (contents : Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxPackedLiveResource buffer contents s ∧
    Disj buffer (locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8)

theorem phase2_packed_live_frame_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (buffer : Ivl) (contents : Nat → BitVec 64)
    (hp : PtxPackedLiveFrame buffer contents s)
    (ht : locN {s with locals := locals, clock := clock} "tx" = locN s "tx")
    (ha : locN {s with locals := locals, clock := clock} "al_keys" = locN s "al_keys")
    (hn : locN {s with locals := locals, clock := clock} "nkeys" = locN s "nkeys") :
    PtxPackedLiveFrame buffer contents {s with locals := locals, clock := clock} := by
  exact ⟨phase2_packed_live_resource_locals s locals clock buffer contents hp.1 ht ha hn,
    by rw [ha, hn]; exact hp.2⟩

theorem phase2_packed_live_frame_assign (buffer : Ivl) (contents : Nat → BitVec 64)
    (name : MlS) (e : ExpHOL 64)
    (ht : name ≠ ofString "tx") (ha : name ≠ ofString "al_keys")
    (hn : name ≠ ofString "nkeys") :
    Hoare (PtxPackedLiveFrame buffer contents) (.assign .local name e)
      (fun r s => r = none → PtxPackedLiveFrame buffer contents s) := by
  apply Hoare.assign
  · intro F s v hp he hr
    apply phase2_packed_live_frame_locals s _ s.clock buffer contents hp
    all_goals simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ht, ha, hn]
  · exact fun _ _ hr => by cases hr

theorem phase2_packed_body_live_iteration_hoare (h : PtxCallees)
    (addressSrc keySrc : ExpHOL 64) (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (fun s => PtxPackedNsNalCopy s ∧ PtxPackedLiveFrame buffer contents s)
      (.seq
        (.call (some (none, none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "al_keys"),
            .panop .mul [.var .local (ofString "k"), .const 52]], addressSrc, .const 20])
        (.seq
          (.call (some (none, none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "al_keys"),
              .panop .mul [.var .local (ofString "k"), .const 52], .const 20], keySrc, .const 32])
          (.seq
            (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"), .const 1]))
            (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
      (fun r s => r = none → PtxPackedNsNalIteration s ∧ PtxPackedLiveFrame buffer contents s) := by
  have hf := Hoare.seq_fall (phase2_packed_address_copy_live_hoare h addressSrc buffer contents)
    (Hoare.seq_fall (phase2_packed_storage_copy_live_hoare h keySrc buffer contents)
      (Hoare.mono (Hoare.seq_fall
        (phase2_packed_live_frame_assign buffer contents (ofString "k")
          (.op .add [.var .local (ofString "k"), .const 1]) (by decide) (by decide) (by decide))
        (phase2_packed_live_frame_assign buffer contents (ofString "j")
          (.op .add [.var .local (ofString "j"), .const 1]) (by decide) (by decide) (by decide)))
        (fun _ hp => ⟨hp.2.1.2, hp.2.2.2.2⟩)))
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨(phase2_packed_body_ns_nal_hoare h addressSrc keySrc).run s hc hp.1 hnt hr,
    hf.run s hc ⟨hp.1.1.1.1, ⟨hp.1.1.1.2.1, hp.2.1⟩,
      hp.1.1.1.2.2.1, hp.1.1.1.2.2.2, hp.2.2⟩ hnt hr⟩

theorem phase2_packed_live_inner_while {body : ProgHOL 64}
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hb : Hoare (fun s => PtxPackedNsNalCopy s ∧ PtxPackedLiveFrame buffer contents s)
      body (fun r s => r = none → PtxPackedNsNalIteration s ∧ PtxPackedLiveFrame buffer contents s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => PtxPackedNsNalIteration s ∧ PtxPackedLiveFrame buffer contents s)
      (.while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))) body)
      (fun r s => r = none → (PtxPackedNsNalIteration s ∧
        locN s "k" = phase2_key_prefix s (locN s "i" + 1)) ∧ PtxPackedLiveFrame buffer contents s) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "j")) (.var .local (ofString "ns"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode →
      (PtxPackedNsNalIteration st ∧ PtxPackedLiveFrame buffer contents st) →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      (PtxPackedNsNalIteration post ∧ locN post "k" = phase2_key_prefix post (locN post "i" + 1)) ∧
        PtxPackedLiveFrame buffer contents post from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_ns_guard_eval st w hp.1.1 (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_ns_iteration_decClock st hp.1.1
          have hf := phase2_packed_live_frame_locals st st.locals (st.clock - 1)
            buffer contents hp.2 rfl rfl rfl
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc
              ⟨⟨⟨phase2_packed_iteration_guard_pre _ hd.1 (hguard.mp hnz), hd.2⟩, hp.1.2⟩, hf⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            exact ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨⟨hp.1, (phase2_packed_separated_inner_exit hp.1.1.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).1⟩, hp.2⟩
    · simp at he

theorem phase2_packed_source_inner_tail_live_hoare (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (fun s => PtxPackedNsNalIteration s ∧ PtxPackedLiveFrame buffer contents s)
      phase2_packed_source_inner_tail
      (fun r s => r = none → PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s) := by
  apply Hoare.seq_fall (phase2_packed_live_inner_while buffer contents
    (phase2_packed_body_live_iteration_hoare h _ _ buffer contents) rfl rfl)
  refine ⟨fun s hc hp hnt hr => ?_⟩
  exact ⟨phase2_packed_ns_nal_outer_increment_hoare.run s hc hp.1 hnt hr,
    (phase2_packed_live_frame_assign buffer contents (ofString "i") _
      (by decide) (by decide) (by decide)).run s hc hp.2 hnt hr⟩

theorem phase2_packed_live_frame_localsOnly (buffer : Ivl) (contents : Nat → BitVec 64) :
    LocalsOnly ["al_keys", "nkeys", "tx", "i", "k", "nal"] (PtxPackedLiveFrame buffer contents) := by
  intro F s locals clock hl hp
  apply phase2_packed_live_frame_locals s locals clock buffer contents hp
  · simp only [locN, hl "tx" (by simp)]
  · simp only [locN, hl "al_keys" (by simp)]
  · simp only [locN, hl "nkeys" (by simp)]

theorem phase2_packed_source_outer_body_live_hoare (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (fun s => (PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) ∧ PtxPackedLiveFrame buffer contents s)
      phase2_packed_source_outer_body
      (fun r s => r = none → PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s) := by
  have hf : LocalsOnly ["al_keys", "nkeys", "tx", "i", "k", "nal"]
      (PtxPackedLiveFrame buffer contents) := phase2_packed_live_frame_localsOnly buffer contents
  have hrestore : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) locals,
      (∀ n ∈ (["al_keys", "nkeys", "tx", "i", "k", "nal"] : List String),
        locals.lookup (ofString n) = s.locals.lookup (ofString n)) →
      (PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s) →
      PtxPackedNalIteration {s with locals := locals} ∧
        PtxPackedLiveFrame buffer contents {s with locals := locals} := by
    intro F s locals hl hp
    exact ⟨phase2_packed_nal_iteration_with_locals s locals s.clock hp.1 hl,
      hf s locals s.clock hl hp.2⟩
  unfold phase2_packed_source_outer_body
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
    (P' := fun s => (PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216) ∧
      locN s "acc2" = memW s (locN s "tx" + 208) + 24 * locN s "i") ∧
      PtxPackedLiveFrame buffer contents s) (by decide)
  · intro F s v hp he
    have hd := phase2_packed_outer_declare_acc2 s hp.1.1.1 hp.1.2 v he
    exact ⟨⟨phase2_packed_nal_set_other s hp.1.1 _ _ (by decide), hd.2⟩,
      LocalsOnly.setVar hf (by decide) v s hp.2⟩
  · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
      (P' := fun s => (PtxPackedNalIteration s ∧
        locN s "i" < memW s (locN s "tx" + 216) ∧
        (∃ n : BitVec 64, s.locals.lookup (ofString "ns") = some (.val (.word n))) ∧
        locN s "ns" = memW s (memW s (locN s "tx" + 208) + 24 * locN s "i" + 16)) ∧
        PtxPackedLiveFrame buffer contents s) (by decide)
    · intro F s v hp he
      have hd := phase2_packed_outer_declare_ns s hp.1.1.1 hp.1.2.1 hp.1.2.2 v he
      exact ⟨⟨phase2_packed_nal_set_other s hp.1.1 _ _ (by decide), hd.2⟩,
        LocalsOnly.setVar hf (by decide) v s hp.2⟩
    · apply Hoare.dec (names := ["al_keys", "nkeys", "tx", "i", "k", "nal"])
        (P' := fun s => PtxPackedNsNalIteration s ∧ PtxPackedLiveFrame buffer contents s) (by decide)
      · intro F s v hp he
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        exact ⟨⟨phase2_packed_ns_reset s hp.1.1.1 hp.1.2.1 hp.1.2.2.1 hp.1.2.2.2,
          (phase2_packed_nal_set_other s hp.1.1 (ofString "j") (.val (.word 0)) (by decide)).2⟩,
          LocalsOnly.setVar hf (by decide) _ s hp.2⟩
      · exact phase2_packed_source_inner_tail_live_hoare h buffer contents
      · intro F r s locals hl hp hr
        exact hrestore s locals hl (hp hr)
      · exact fun _ _ hr => by cases hr
    · intro F r s locals hl hp hr
      exact hrestore s locals hl (hp hr)
    · exact fun _ _ hr => by cases hr
  · intro F r s locals hl hp hr
    exact hrestore s locals hl (hp hr)
  · exact fun _ _ hr => by cases hr

theorem phase2_packed_live_outer_while {body : ProgHOL 64}
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hb : Hoare (fun s => (PtxPackedNalIteration s ∧
      locN s "i" < memW s (locN s "tx" + 216)) ∧ PtxPackedLiveFrame buffer contents s)
      body (fun r s => r = none → PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s))
    (hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak body = true)
    (hnc : InitECandidate.Solver.PanRunBounded.noTopContinue body = true) :
    Hoare (fun s => PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))) body)
      (fun r s => r = none → (PtxPackedNalIteration s ∧ locN s "k" = locN s "nkeys") ∧
        PtxPackedLiveFrame buffer contents s) := by
  let guard : ExpHOL 64 := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal"))
  refine ⟨fun {F} s hc hp _ hr => ?_⟩
  generalize he : evaluateHOLFiniteState s (.while guard body) = out at hr ⊢
  obtain ⟨r, post⟩ := out
  dsimp only at hr
  subst r
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F), st.clock = k →
      st.code = originalRuntimeCode →
      (PtxPackedNalIteration st ∧ PtxPackedLiveFrame buffer contents st) →
      evaluateHOLFiniteState st (.while guard body) = (none, post) →
      (PtxPackedNalIteration post ∧ locN post "k" = locN post "nkeys") ∧
        PtxPackedLiveFrame buffer contents post from
    this s.clock s rfl hc hp he
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk hc hp he
    rw [evaluateHOLFiniteState_while_total] at he
    split at he
    · rename_i w hw
      have hguard := phase2_packed_outer_nal_guard st w hp.1.1 hp.1.2.1 hp.1.2.2
        (by simpa [evalAt, guard] using hw)
      split at he
      · rename_i hnz
        split at he
        · simp at he
        · dsimp only at he
          rw [fixClockHOLFinite_evaluateState] at he
          have hd := phase2_packed_nal_iteration_decClock st hp.1
          have hf := phase2_packed_live_frame_locals st st.locals (st.clock - 1)
            buffer contents hp.2 rfl rfl rfl
          have hm := (InitECandidate.Solver.PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite st) body).1
          have hclk := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hbr := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak body hnb (decClockHOLFinite st)
          have hco := InitECandidate.Solver.PanRunBounded.evaluate_noTopContinue body hnc (decClockHOLFinite st)
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r, mid⟩
          rw [hrun] at he hm hclk hbr hco
          cases r with
          | none =>
            have hmid := hb.run (decClockHOLFinite st) hc ⟨⟨hd, hguard.mp hnz⟩, hf⟩
              (by rw [hrun]; simp) (by rw [hrun])
            rw [hrun] at hmid
            exact ih mid.clock (by change mid.clock ≤ st.clock - 1 at hclk; omega)
              mid rfl (hm.trans hc) hmid he
          | some r => cases r <;> simp_all
      · rename_i hz
        simp at he
        obtain ⟨_, rfl⟩ := he
        exact ⟨⟨hp.1, (phase2_packed_outer_exit hp.1.1.2.1
          (fun hlt => hz (hguard.mpr hlt))).2⟩, hp.2⟩
    · simp at he

theorem phase2_packed_source_outer_loop_live_hoare (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (fun s => PtxPackedNalIteration s ∧ PtxPackedLiveFrame buffer contents s)
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
        phase2_packed_source_outer_body)
      (fun r s => r = none → (PtxPackedNalIteration s ∧ locN s "k" = locN s "nkeys") ∧
        PtxPackedLiveFrame buffer contents s) := by
  exact phase2_packed_live_outer_while buffer contents
    (phase2_packed_source_outer_body_live_hoare h buffer contents) rfl rfl

theorem phase2_packed_live_frame_set_other {F : Type}
    (s : PanSemStateFiniteExact 64 F) (buffer : Ivl) (contents : Nat → BitVec 64)
    (hp : PtxPackedLiveFrame buffer contents s) (name : MlS) (v : ValueHOL 64)
    (ht : name ≠ ofString "tx") (ha : name ≠ ofString "al_keys")
    (hn : name ≠ ofString "nkeys") :
    PtxPackedLiveFrame buffer contents (setVarHOLFinite name v s) := by
  apply phase2_packed_live_frame_locals s _ s.clock buffer contents hp
  all_goals simp [locN, HolFiniteMapExact.update, FUPDATE, ht, ha, hn]

theorem phase2_packed_cases_initialized_live_hoare (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    Hoare (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧ PtxPackedLiveFrame buffer contents s)
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      (fun r s => r = none → (WorldOK s ∧ PtxPackedKeysReady s) ∧ PtxPackedLiveFrame buffer contents s) := by
  apply Hoare.dec (names := ["al_keys", "nkeys", "tx"])
    (P' := fun s => ∃ before,
      ((WorldOK before ∧ PtxPackedInitCases before) ∧ PtxPackedLiveFrame buffer contents before) ∧
      s = setVarHOLFinite (ofString "k") (.val (.word 0)) before) (by decide)
  · intro F s v hp he
    have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
    subst v
    exact ⟨s, hp, rfl⟩
  · apply Hoare.seq_fall (R := fun s => (PtxPackedNalIteration s ∨
      (WorldOK s ∧ PtxPackedKeysReady s ∧
        s.locals.lookup (ofString "i") = some (.val (.word 0)) ∧
        s.locals.lookup (ofString "nal") = some (.val (.word 0)))) ∧
      PtxPackedLiveFrame buffer contents s)
    · apply Hoare.assign
      · intro F s v hp he
        obtain ⟨before, hp, rfl⟩ := hp
        have hv : v = .val (.word 0) := by simpa [evalAt, evalHOLExact] using he.symm
        subst v
        intro _
        refine ⟨?_, phase2_packed_live_frame_set_other _ buffer contents
          (phase2_packed_live_frame_set_other before buffer contents hp.2 _ _
            (by decide) (by decide) (by decide)) _ _ (by decide) (by decide) (by decide)⟩
        rcases hp.1.2 with hp' | hp'
        · exact Or.inl (phase2_packed_init_state before hp')
        · have hz := phase2_packed_zero_init before hp'.1 hp'.2
          exact Or.inr ⟨phase2_packed_ready_worldOK _
            ((arenaReady_with_locals before _ before.clock).mpr hp.1.1.1) hz.1, hz⟩
      · exact fun _ _ hr => by cases hr
    · refine ⟨?_⟩
      intro F s hc hp hnt hr
      rcases hp.1 with hi | hi
      · have ho := (phase2_packed_source_outer_loop_live_hoare h buffer contents).run s hc ⟨hi, hp.2⟩ hnt hr
        exact ⟨⟨ho.1.1.1.1, ho.1.1.1.2.1.1⟩, ho.2⟩
      · rw [phase2_zero_nal_loop s phase2_packed_source_outer_body hi.2.2.1 hi.2.2.2]
        exact ⟨⟨hi.1, hi.2.1⟩, hp.2⟩
  · intro F r s locals hl hp hr
    have hk := phase2_packed_keys_with_locals s locals s.clock (hp hr).1.2 hl
    refine ⟨⟨phase2_packed_ready_worldOK _
      ((arenaReady_with_locals s locals s.clock).mpr (hp hr).1.1.1) hk, hk⟩, ?_⟩
    apply phase2_packed_live_frame_locals s locals s.clock buffer contents (hp hr).2
    · simp only [locN, hl "tx" (by simp)]
    · simp only [locN, hl "al_keys" (by simp)]
    · simp only [locN, hl "nkeys" (by simp)]
  · exact fun _ _ hr => by cases hr

theorem phase2_packed_live_continuation_bound (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedKeysReady s) ∧ PtxPackedLiveFrame buffer contents s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧ PtxPackedLiveFrame buffer contents s)
      (.seq
        (.dec (ofString "k") .one (.const 0)
          (.seq (.assign .local (ofString "i") (.const 0))
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
              phase2_packed_source_outer_body))) tail)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
  intro F s hc hp
  exact seq_bound_trans
    (fun t hct hpt => phase2_packed_cases_initialized_loop_bound h t hct hpt.1.2)
    (phase2_packed_cases_initialized_live_hoare h buffer contents) ht s hc hp

/-- Several saved caller buffers can be carried through the same packing run.
Each buffer retains its own joint world witness and its original contents. -/
theorem phase2_packed_cases_initialized_live_family_hoare (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) :
    Hoare (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧
      ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s)
      (.dec (ofString "k") .one (.const 0)
        (.seq (.assign .local (ofString "i") (.const 0))
          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
            phase2_packed_source_outer_body)))
      (fun r s => r = none → (WorldOK s ∧ PtxPackedKeysReady s) ∧
        ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  refine ⟨(phase2_packed_cases_initialized_world_hoare h).run s hc hp.1 hnt hr, ?_⟩
  intro i
  exact ((phase2_packed_cases_initialized_live_hoare h (buffers i) (contents i)).run
    s hc ⟨hp.1, hp.2 i⟩ hnt hr).2

/-- The warm-state continuation may consume all retained buffers at once. -/
theorem phase2_packed_live_family_continuation_bound (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedKeysReady s) ∧
        ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s) tail b) :
    TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧
        ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s)
      (.seq
        (.dec (ofString "k") .one (.const 0)
          (.seq (.assign .local (ofString "i") (.const 0))
            (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
              phase2_packed_source_outer_body))) tail)
      ((2 ^ 63 + 1) * ((2 ^ 63 + 1) * ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) := by
  intro F s hc hp
  exact seq_bound_trans
    (fun t hct hpt => phase2_packed_cases_initialized_loop_bound h t hct hpt.1.2)
    (phase2_packed_cases_initialized_live_family_hoare h buffers contents) ht s hc hp

/-- Packed allocation establishes the shared live frame used by the loops. -/
theorem phase2_count_cases_alloc_live (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    DecCallResumeOn (fun s => PtxAddressCountExit s ∧
      ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        PtxLiveBufferAt s S Nd buffer contents)
      (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧ PtxPackedLiveFrame buffer contents s)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hi := phase2_count_cases_alloc_world_init h s vs body callee ret v post hc hp.1 ha hl hb
  have hr := phase2_count_exit_access_ready hp.1
  obtain ⟨S, Nd, hW, hT, hbuf⟩ := hp.2
  obtain ⟨nv, he, hn⟩ := R16Shards.PtxP1.params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact R16Shards.PtxP1.lookup_alloc) _ vs body callee ret ha hl
  obtain ⟨n, hen, hsize, _⟩ := phase2_count_cases_alloc_eval s hp.1
  rw [hen] at he
  cases he
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = locN s "nkeys" * 52 + 8 := by
    simpa [locN, callEntryStateHOLFinite, hn] using hsize
  have hw := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hr.1.1.1.1.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hw
  have step := hw (Or.inl ⟨v, rfl⟩)
  obtain ⟨S', Nd', _, hW', hgrow, hframe, hret⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  have hTp := R16Shards.PtxP1.txAccessListOK_survives_step
    hr.1.1.1.1.1.1.1.1 step.1.1 step.2.1 hW (R := []) (by simp)
    hgrow hframe hT (by simp) (by simp) (locals := s.locals) rfl
  have hbp := phase2_live_buffer_step s post S Nd S' Nd' buffer contents [] hbuf
    hr.1.1.1.1.1.1.1.1.2 hW step.2.1 hgrow hframe (by simp) (by simp)
  obtain ⟨w, rfl, hf⟩ := phase2_count_cases_alloc_fresh h s vs body callee ret v post hc hp.1 ha hl hb
  obtain ⟨w', hv, hav⟩ := hret (.val (.word w)) rfl
  cases hv
  dsimp only at hav
  rw [hcn] at hav
  let out := setVarHOLFinite (ofString "al_keys") (.val (.word w)) {post with locals := s.locals}
  have hptr : locN out "al_keys" = w.toNat := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have hcount : locN out "nkeys" = locN s "nkeys" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "nkeys" by decide]
  refine ⟨hi, ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hW', ?_, ?_, hbp⟩, ?_⟩
  · have ht := R16Shards.PtxP1.txAccessListAt_with_locals post out.locals post.clock hTp
    simpa [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "al_keys" ≠ ofString "tx" by decide] using ht
  · change IvlsDisj [(locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)] _
    rw [hptr, hcount]
    exact hav
  · change Disj buffer (locN out "al_keys", (locN out "nkeys" * 52 + 8 + 7) / 8 * 8)
    rw [hptr, hcount]
    exact Or.inr (Or.inr (Or.inl (hbuf.1.2.trans hf.2.1.1)))

/-- Allocation and both packing loops compose while retaining a saved caller buffer. -/
theorem phase2_alloc_packing_live_bound (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedKeysReady s) ∧ PtxPackedLiveFrame buffer contents s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧
      ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        PtxLiveBufferAt s S Nd buffer contents)
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.seq
          (.dec (ofString "k") .one (.const 0)
            (.seq (.assign .local (ofString "i") (.const 0))
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
                phase2_packed_source_outer_body))) tail))
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧ PtxPackedLiveFrame buffer contents s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp.1
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact phase2_count_cases_alloc_live h buffer contents
  · exact phase2_packed_live_continuation_bound h buffer contents ht

/-- Allocation preserves a whole family of caller buffers, including an empty family. -/
theorem phase2_count_cases_alloc_live_family (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) :
    DecCallResumeOn (fun s => PtxAddressCountExit s ∧
      ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      (fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧
        ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s)
      (ofString "al_keys") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]] := by
  intro F s vs body callee ret v post hc hp ha hl hb
  refine ⟨phase2_count_cases_alloc_world_init h s vs body callee ret v post hc hp.1 ha hl hb, ?_⟩
  intro i
  exact (phase2_count_cases_alloc_live h (buffers i) (contents i)
    s vs body callee ret v post hc ⟨hp.1, hp.2 i⟩ ha hl hb).2

/-- The allocation-to-packing segment exposes all retained buffers to its tail. -/
theorem phase2_alloc_packing_live_family_bound (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (WorldOK s ∧ PtxPackedKeysReady s) ∧
        ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧
      ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.seq
          (.dec (ofString "k") .one (.const 0)
            (.seq (.assign .local (ofString "i") (.const 0))
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
                phase2_packed_source_outer_body))) tail))
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => (WorldOK s ∧ PtxPackedInitCases s) ∧
      ∀ i, PtxPackedLiveFrame (buffers i) (contents i) s) h.fb_alloc
  · intro F s vs body callee ret hc hp ha hl
    have hr := phase2_count_exit_access_ready hp.1
    exact guestInv_callEntry s callee hr.1.1.1.1.1.1.1.1.1
  · exact phase2_count_cases_alloc_live_family h buffers contents
  · exact phase2_packed_live_family_continuation_bound h buffers contents ht

/-- The three caller-owned buffers already present when packed-key allocation starts. -/
inductive PtxWarmBuffer where
  | environment
  | sender
  | addresses

def phase2_warm_buffer {F : Type} (s : PanSemStateFiniteExact 64 F) : PtxWarmBuffer → Ivl
  | .environment => (locN s "te", 200)
  | .sender => (locN s "sender", 24)
  | .addresses => (locN s "al_addrs", (locN s "nal" + 1) * 8)

/-- Save actual words, so the continuation can recover pointer-valued array entries. -/
def phase2_saved_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p : Nat) : BitVec 64 :=
  match s.memory (BitVec.ofNat 64 p) with
  | .word w => w

theorem phase2_saved_word_value {F : Type} (s : PanSemStateFiniteExact 64 F) (p : Nat) :
    (phase2_saved_word s p).toNat = memW s p := by
  cases h : s.memory (BitVec.ofNat 64 p) with
  | word w => rfl

/-- Initializing a snapshot requires ownership, but no extra content hypothesis. -/
theorem phase2_live_buffer_snapshot {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (buffer : Ivl)
    (hi : Inside buffer InitE.sourceBase (globN s "heap_ptr"))
    (hd : IvlsDisj [buffer] (worldOwned s S Nd)) :
    PtxLiveBufferAt s S Nd buffer (phase2_saved_word s) := by
  refine ⟨hi, hd, ?_⟩
  intro p _ _ _
  exact (phase2_saved_word_value s p).symm

/-- Concrete warm-state resources exported by allocation and packing. The reference
state fixes the buffer addresses even while the loop modifies its local counters. -/
def PtxWarmPacked {F₀ : Type} (before : PanSemStateFiniteExact 64 F₀)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (WorldOK s ∧ PtxPackedKeysReady s) ∧
    ∀ i, PtxPackedLiveFrame (phase2_warm_buffer before i) (phase2_saved_word before) s

theorem phase2_warm_packed_word {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (hp : PtxWarmPacked before s) (i : PtxWarmBuffer) (p : Nat)
    (hlo : (phase2_warm_buffer before i).1 ≤ p)
    (hhi : p + 8 ≤ (phase2_warm_buffer before i).1 + (phase2_warm_buffer before i).2)
    (hal : p % 8 = 0) : memW s p = memW before p := by
  obtain ⟨S, Nd, _, _, _, hb⟩ := (hp.2 i).1
  exact (hb.2.2 p hlo hhi hal).trans (phase2_saved_word_value before p)

/-- Instantiate the family continuation with the environment, sender, and address array. -/
theorem phase2_alloc_packing_warm_bound (h : PtxCallees) {F₀ : Type}
    (before : PanSemStateFiniteExact 64 F₀) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxWarmPacked before) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧
      ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        PtxLiveBufferAt s S Nd (phase2_warm_buffer before i) (phase2_saved_word before))
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.seq
          (.dec (ofString "k") .one (.const 0)
            (.seq (.assign .local (ofString "i") (.const 0))
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
                phase2_packed_source_outer_body))) tail))
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  exact phase2_alloc_packing_live_family_bound h (phase2_warm_buffer before)
    (fun _ => phase2_saved_word before) ht

/-- Counting retains the joint environment/address ownership witness in both cases. -/
theorem phase2_count_exit_joint {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxAddressCountExit s) : PtxAddressJoint s := by
  rcases hp with hp | hp
  · exact hp.1.1.1
  · exact hp.1.1

/-- The two buffers allocated in Phase 2 can be snapshotted directly at the cut.
Sender ownership is supplied by the Phase 1 caller frame. -/
theorem phase2_count_exit_warm_snapshots {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountExit s)
    (hs : ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "sender", 24)] (worldOwned s S Nd)) :
    ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      PtxLiveBufferAt s S Nd (phase2_warm_buffer s i) (phase2_saved_word s) := by
  have hj := phase2_count_exit_joint hp
  have hr := phase2_count_exit_access_ready hp
  intro i
  cases i with
  | environment =>
    obtain ⟨S, Nd, hw, ht, _, hd⟩ := hj.2
    exact ⟨S, Nd, hw, ht, phase2_live_buffer_snapshot s S Nd _ hr.1.1.2.2.1 hd⟩
  | sender =>
    obtain ⟨S, Nd, hw, ht, hd⟩ := hs
    exact ⟨S, Nd, hw, ht, phase2_live_buffer_snapshot s S Nd _ hr.1.1.1.1.2.1 hd⟩
  | addresses =>
    obtain ⟨S, Nd, hw, ht, hd, _⟩ := hj.2
    exact ⟨S, Nd, hw, ht, phase2_live_buffer_snapshot s S Nd _ hj.1.2.2.1 hd⟩

/-- Recover any environment slot after packing from the concrete snapshot. -/
theorem phase2_warm_packed_environment {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (hp : PtxWarmPacked before s) (hal : locN before "te" % 8 = 0)
    (k : Nat) (hk : k < 25) :
    memW s (locN before "te" + 8 * k) = memW before (locN before "te" + 8 * k) := by
  apply phase2_warm_packed_word before s hp .environment
  · simp [phase2_warm_buffer]
  · simp only [phase2_warm_buffer]
    omega
  · simp [Nat.add_mod, Nat.mul_mod, hal]

/-- Address entries, including the beneficiary at zero, survive packing verbatim. -/
theorem phase2_warm_packed_address {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (hp : PtxWarmPacked before s) (hal : locN before "al_addrs" % 8 = 0)
    (k : Nat) (hk : k ≤ locN before "nal") :
    memW s (locN before "al_addrs" + 8 * k) =
      memW before (locN before "al_addrs" + 8 * k) := by
  apply phase2_warm_packed_word before s hp .addresses
  · simp [phase2_warm_buffer]
  · simp only [phase2_warm_buffer]
    omega
  · simp [Nat.add_mod, Nat.mul_mod, hal]

/-- Select the snapshot at the actual count-exit state. Thus callers supply only
the sender ownership frame, rather than three independent content invariants. -/
theorem phase2_alloc_packing_warm_cut (h : PtxCallees)
    {tail : ProgHOL 64} {b : Nat}
    (ht : ∀ {F : Type} (before : PanSemStateFiniteExact 64 F),
      PtxAddressCountExit before →
      TerminatingProgBoundedOn (PtxWarmPacked before) tail b) :
    TerminatingProgBoundedOn (fun s => PtxAddressCountExit s ∧
      ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
        IvlsDisj [(locN s "sender", 24)] (worldOwned s S Nd))
      (.decCall (ofString "al_keys") .one (ofString "alloc")
        [.op .add [.panop .mul [.var .local (ofString "nkeys"), .const 52], .const 8]]
        (.seq
          (.dec (ofString "k") .one (.const 0)
            (.seq (.assign .local (ofString "i") (.const 0))
              (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nal")))
                phase2_packed_source_outer_body))) tail))
      (K.alloc + ((2 ^ 63 + 1) * ((2 ^ 63 + 1) *
        ((K.memcpy + 1) + (K.memcpy + 1) + 1) + 1) + b) + 1) := by
  intro F s hc hp
  exact phase2_alloc_packing_warm_bound h s (ht s hp.1) s hc
    ⟨hp.1, phase2_count_exit_warm_snapshots s hp.1 hp.2⟩

/-- All three saved buffers have typed cells at the count exit. -/
theorem phase2_count_exit_warm_words {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hp : PtxAddressCountExit s) (i : PtxWarmBuffer) :
    WordsOK s (phase2_warm_buffer s i) := by
  have hj := phase2_count_exit_joint hp
  have hr := phase2_count_exit_access_ready hp
  cases i with
  | environment => exact hr.1.1.2.2.2.2.1
  | sender => exact hr.1.1.1.1.2.2.1
  | addresses => exact hj.1.2.2.2.2.1

/-- Packing retains the typed cells of a snapshot, even across state type parameters. -/
theorem phase2_warm_packed_words {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (hb : PtxAddressCountExit before) (hp : PtxWarmPacked before s)
    (i : PtxWarmBuffer) : WordsOK s (phase2_warm_buffer before i) := by
  have hw := phase2_count_exit_warm_words before hb i
  have hg : GuestInv before :=
    (phase2_count_exit_access_ready hb).1.1.1.1.1.1.1.1.1
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hd, _⟩ := hw.2.2 k hk
  cases hm : s.memory (BitVec.ofNat 64 ((phase2_warm_buffer before i).1 + 8 * k)) with
  | word w =>
    refine ⟨w, ?_, hm⟩
    rw [hp.1.1.1.1.memaddrs, ← hg.memaddrs]
    exact hd

/-- Recover placement, cell typing, and world separation together for a warm buffer.
The ownership witness also contains the transaction and packed-key allocation. -/
theorem phase2_warm_packed_buffer_ready {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (hb : PtxAddressCountExit before) (hp : PtxWarmPacked before s)
    (i : PtxWarmBuffer) :
    Inside (phase2_warm_buffer before i) InitE.sourceBase (globN s "heap_ptr") ∧
    WordsOK s (phase2_warm_buffer before i) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListAt s S Nd (locN s "tx") ∧
      IvlsDisj [(locN s "al_keys", (locN s "nkeys" * 52 + 8 + 7) / 8 * 8),
        phase2_warm_buffer before i] (worldOwned s S Nd) := by
  obtain ⟨S, Nd, hw, ht, hk, hi, hd, _⟩ := (hp.2 i).1
  refine ⟨hi, phase2_warm_packed_words before s hb hp i, S, Nd, hw, ht, ?_⟩
  intro j hj o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact hk _ (by simp) o ho
  · exact hd _ (by simp) o ho

/-- Saved numeric words determine the actual memory cells on an aligned buffer.
This converts the snapshot interface to the frame interface used by later calls. -/
theorem phase2_warm_packed_unhit {F : Type}
    (before s : PanSemStateFiniteExact 64 F)
    (hb : PtxAddressCountExit before) (hp : PtxWarmPacked before s)
    (i : PtxWarmBuffer) : IvlUnhit before s (phase2_warm_buffer before i) := by
  have hw := phase2_count_exit_warm_words before hb i
  intro a ha hh
  have hlo : (phase2_warm_buffer before i).1 ≤ a.toNat := by
    have := hw.1
    obtain ⟨h1, h2⟩ := hh
    omega
  have hhi : a.toNat + 8 ≤
      (phase2_warm_buffer before i).1 + (phase2_warm_buffer before i).2 := by
    have := hw.1
    have := hw.2.1
    obtain ⟨h1, h2⟩ := hh
    omega
  have hm := phase2_warm_packed_word before s hp i a.toNat hlo hhi ha
  simp only [memW, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hm
  cases hs : s.memory a with
  | word ws =>
    cases hb' : before.memory a with
    | word wb =>
      have hsN := congrArg (fun v : HolWordLab 64 =>
        match v with | .word w => w.toNat) hs
      have hbN := congrArg (fun v : HolWordLab 64 =>
        match v with | .word w => w.toNat) hb'
      exact congrArg HolWordLab.word (BitVec.eq_of_toNat_eq (hsN.symm.trans (hm.trans hbN)))

/-- Warm snapshots are independent of bookkeeping locals and the execution clock. -/
theorem phase2_warm_packed_with_locals {F₀ F : Type}
    (before : PanSemStateFiniteExact 64 F₀) (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hp : PtxWarmPacked before s)
    (hl : ∀ n ∈ (["al_keys", "nkeys", "tx"] : List String),
      locals.lookup (ofString n) = s.locals.lookup (ofString n)) :
    PtxWarmPacked before {s with locals := locals, clock := clock} := by
  refine ⟨⟨localsFree_worldOK s locals clock hp.1.1,
    phase2_packed_keys_with_locals s locals clock hp.1.2 hl⟩, ?_⟩
  intro i
  apply phase2_packed_live_frame_locals s locals clock _ _ (hp.2 i)
  · exact locN_congr s locals clock "tx" (hl "tx" (by simp))
  · exact locN_congr s locals clock "al_keys" (hl "al_keys" (by simp))
  · exact locN_congr s locals clock "nkeys" (hl "nkeys" (by simp))

/-- Read-only classification calls in the suffix retain all three warm snapshots. -/
theorem phase2_warm_packed_readonly_resume {F₀ : Type}
    (before : PanSemStateFiniteExact 64 F₀) (name fn : MlS) (args : List (ExpHOL 64))
    (hr : ReadOnlyFn fn)
    (ha : name ≠ ofString "al_keys") (hn : name ≠ ofString "nkeys")
    (ht : name ≠ ofString "tx") :
    DecCallResumeOn (PtxWarmPacked before) (PtxWarmPacked before) name fn args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup hr s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hh
  have hstate := hh (Or.inl ⟨v, rfl⟩)
  dsimp only at hstate
  have hrestore : ({post with locals := s.locals} : PanSemStateFiniteExact 64 F) =
      {s with locals := s.locals, clock := post.clock} := by rw [hstate]; rfl
  have hp' : PtxWarmPacked before {post with locals := s.locals} := by
    rw [hrestore]
    exact phase2_warm_packed_with_locals before s s.locals post.clock hp (fun _ _ => rfl)
  apply phase2_warm_packed_with_locals before _ _ _ hp'
  intro n hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;>
    simp [HolFiniteMapExact.update, FUPDATE, ha, hn, ht]

/-- Allocation in the suffix preserves a saved caller buffer and its ownership witness. -/
theorem phase2_alloc_live_buffer_resume (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd buffer contents)
      (fun s => WorldOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd buffer contents)
      name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have step := hh (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hw, hbuf⟩ := hp.2
  obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) (by simp [IvlsDisj])
  have hbuf' : PtxLiveBufferAt post S' Nd' buffer contents := by
    apply phase2_live_buffer_step (callEntryStateHOLFinite s callee) post S Nd S' Nd'
      buffer contents [] hbuf hp.1.1.2
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw)
      step.2.1 hg hf
    · simp
    · simp
  refine ⟨?_, S', Nd', ?_, hbuf'⟩
  · exact localsFree_worldOK post _ post.clock
      ⟨step.1, S', (worldTyped_iff_with post S').mpr ⟨Nd', hw'⟩⟩
  · exact (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw'

/-- A suffix allocation preserves an arbitrary family of saved buffers. -/
theorem phase2_alloc_live_family_resume (h : PtxCallees) {ι : Type}
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      (fun s => WorldOK s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  constructor
  · have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
      (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
    rw [hb] at hh
    have step := hh (Or.inl ⟨v, rfl⟩)
    obtain ⟨S, hw⟩ := hp.1.2
    obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hw
    obtain ⟨S', Nd', _, hw', _⟩ := step.2.2.2.2 S Nd
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) (by simp [IvlsDisj])
    exact localsFree_worldOK post _ post.clock
      ⟨step.1, S', (worldTyped_iff_with post S').mpr ⟨Nd', hw'⟩⟩
  · intro i
    exact (phase2_alloc_live_buffer_resume h (buffers i) (contents i) name args
      s vs body callee ret v post hc ⟨hp.1, hp.2 i⟩ he hl hb).2

/-- Compose a suffix allocation with a continuation that consumes all saved buffers. -/
theorem phase2_alloc_live_family_bound (h : PtxCallees) {ι : Type}
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (name : MlS) (args : List (ExpHOL 64)) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => WorldOK s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i)) tail b) :
    TerminatingProgBoundedOn
      (fun s => WorldOK s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      (.decCall name .one (ofString "alloc") args tail) (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => WorldOK s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
      PtxLiveBufferAt s S Nd (buffers i) (contents i)) h.fb_alloc
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1
  · exact phase2_alloc_live_family_resume h buffers contents name args
  · exact ht

/-- Stores to a separate caller allocation preserve a saved buffer's contents.
The same world witness is retained, allowing subsequent stores to reuse it. -/
theorem phase2_live_buffer_store {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) (hE : TxEnv s) {S Nd : List Nat}
    (hW : WorldTypedWith s S Nd) {buffer blk : Ivl} {contents : Nat → BitVec 64}
    (hb : PtxLiveBufferAt s S Nd buffer contents)
    (hd : ∀ o ∈ worldOwned s S Nd, Disj blk o)
    (hsep : Disj buffer blk) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) blk.1 (blk.1 + blk.2))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    WorldTypedWith {s with memory := mem} S Nd ∧ TxEnv {s with memory := mem} ∧
      PtxLiveBufferAt {s with memory := mem} S Nd buffer contents := by
  obtain ⟨hw, how, he⟩ := store_outside_worldOwned hA hE hW hd hx hin hm
  refine ⟨hw, he, hb.1, ?_, ?_⟩
  · rw [how]; exact hb.2.1
  · intro p hlo hhi hal
    have hbound := (ivl_allocated_bound hA.2 (Or.inl hb.1)).2
    have hp : p < 2 ^ 64 := by omega
    have hne : BitVec.ofNat 64 p ≠ x := by
      intro heq
      have hp' : p = x.toNat := by
        have hh := congrArg BitVec.toNat heq
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using hh
      have hs := disj_of_inside_right hin hsep
      rcases hs with hs | hs | hs | hs <;> omega
    change memW {s with memory := mem} p = (contents p).toNat
    change (match mem (BitVec.ofNat 64 p) with | .word w => w.toNat) = (contents p).toNat
    rw [hm _ hne]
    exact hb.2.2 p hlo hhi hal

/-- Message allocation retains a saved buffer and separates the new message from
the same world witness. This is the ownership cut for the message-field stores. -/
theorem phase2_msg_new_live_buffer_resume (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd buffer contents)
      (fun s => WorldOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd buffer contents ∧
        IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd))
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_msg_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have step := hh (Or.inl ⟨v, rfl⟩)
  obtain ⟨S, Nd, hw, hbuf⟩ := hp.2
  obtain ⟨S', Nd', _, hw', hg, hf, hr⟩ := step.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) (by simp [IvlsDisj])
  have hbuf' : PtxLiveBufferAt post S' Nd' buffer contents := by
    apply phase2_live_buffer_step (callEntryStateHOLFinite s callee) post S Nd S' Nd'
      buffer contents [] hbuf hp.1.1.2
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw)
      step.2.1 hg hf
    · simp
    · simp
  obtain ⟨w, rfl, hd⟩ := hr v rfl
  refine ⟨?_, S', Nd', ?_, hbuf', ?_⟩
  · exact localsFree_worldOK post _ post.clock
      ⟨step.1, S', (worldTyped_iff_with post S').mpr ⟨Nd', hw'⟩⟩
  · exact (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw'
  · change IvlsDisj [(locN (setVarHOLFinite (ofString "m") (.val (.word w))
      {post with locals := s.locals}) "m", 176)] (worldOwned post S' Nd')
    simpa [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE] using hd

/-- The message allocator supplies its full initialized heap extent. -/
theorem phase2_msg_new_geometry (h : PtxCallees) :
    DecCallResumeOn WorldOK
      (fun s =>
        (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w))) ∧
        Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") ∧
        WordsOK s (locN s "m", 176) ∧
        ∀ k, k < 22 → memW s (locN s "m" + 8 * k) = 0)
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_msg_new s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1) (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, rfl, _, _, hf, hz⟩ := hr v rfl
  have hm : locN (setVarHOLFinite (ofString "m") (.val (.word w))
      {post with locals := s.locals}) "m" = w.toNat := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  refine ⟨⟨w, ?_⟩, ?_, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [hm]
    exact ⟨hp.1.2.1.trans hf.2.1.1, hf.2.1.2⟩
  · rw [hm]; exact hf.2.2
  · rw [hm]; exact hz

/-- Fresh message storage is disjoint from every previously allocated caller buffer. -/
theorem phase2_msg_new_buffer_separation (h : PtxCallees) (buffer : Ivl) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ Inside buffer InitE.sourceBase (globN s "heap_ptr"))
      (fun s => Disj buffer (locN s "m", 176))
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup h.rt_msg_new s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  obtain ⟨w, rfl, _, _, hf, _⟩ := hr v rfl
  have hm : locN (setVarHOLFinite (ofString "m") (.val (.word w))
      {post with locals := s.locals}) "m" = w.toNat := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  rw [hm]
  exact Or.inr (Or.inr (Or.inl (hp.2.2.trans hf.2.1.1)))

/-- Joint cut after message allocation: the message is initialized and owned,
and its stores cannot hit the saved caller buffer. -/
theorem phase2_msg_new_live_ready (h : PtxCallees)
    (buffer : Ivl) (contents : Nat → BitVec 64) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd buffer contents)
      (fun s => WorldOK s ∧
        (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w))) ∧
        Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") ∧
        WordsOK s (locN s "m", 176) ∧
        (∀ k, k < 22 → memW s (locN s "m" + 8 * k) = 0) ∧
        Disj buffer (locN s "m", 176) ∧
        ∃ S Nd, WorldTypedWith s S Nd ∧ PtxLiveBufferAt s S Nd buffer contents ∧
          IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd))
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hg := phase2_msg_new_geometry h s vs body callee ret v post hc hp.1 he hl hb
  have hw := phase2_msg_new_live_buffer_resume h buffer contents
    s vs body callee ret v post hc hp he hl hb
  obtain ⟨S, Nd, _, hbuf⟩ := hp.2
  have hd := phase2_msg_new_buffer_separation h buffer
    s vs body callee ret v post hc ⟨hp.1, hbuf.1⟩ he hl hb
  exact ⟨hw.1, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2, hd, hw.2⟩

/-- Reusable message-store cut, retaining all saved warm buffers and the
nonzero block-output backing pointers carried by `TxEnv`. -/
def PtxMessageStoreReady {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  WorldOK s ∧ TxEnv s ∧
  (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w))) ∧
  Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") ∧
  WordsOK s (locN s "m", 176) ∧
  ∀ i, Disj (buffers i) (locN s "m", 176) ∧
    ∃ S Nd, WorldTypedWith s S Nd ∧ PtxLiveBufferAt s S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd)

/-- Every single-word message-field write preserves the complete saved-buffer
family and its separating world witnesses. -/
theorem phase2_message_store_ready_store {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxMessageStoreReady buffers contents {s with memory := mem} := by
  have hA : ArenaReady {s with memory := mem} :=
    ⟨guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1, hp.1.1.2⟩
  have hf : ∀ i, ∃ S Nd, WorldTypedWith {s with memory := mem} S Nd ∧
      PtxLiveBufferAt {s with memory := mem} S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned {s with memory := mem} S Nd) ∧
      TxEnv {s with memory := mem} := by
    intro i
    obtain ⟨hd, S, Nd, hw, hb, hsep⟩ := hp.2.2.2.2.2 i
    have hdw : ∀ o ∈ worldOwned s S Nd, Disj (locN s "m", 176) o :=
      fun o ho => hsep _ (by simp) o ho
    obtain ⟨hw', he', hb'⟩ := phase2_live_buffer_store hp.1.1 hp.2.1 hw hb hdw hd hx hin hm
    have how := (store_outside_worldOwned hp.1.1 hp.2.1 hw hdw hx hin hm).2.1
    exact ⟨S, Nd, hw', hb', by rw [how]; exact hsep, he'⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨S, Nd, hw, _, _, he⟩ := hf i
  refine ⟨⟨hA, S, (worldTyped_iff_with _ S).mpr ⟨Nd, hw⟩⟩,
    he, hp.2.2.1, hp.2.2.2.1, ?_, ?_⟩
  · exact wordsOK_transfer hp.1.1.1 hA.1 hp.2.2.2.2.1
  · intro j
    obtain ⟨S', Nd', hw', hb', hd', _⟩ := hf j
    exact ⟨(hp.2.2.2.2.2 j).1, S', Nd', hw', hb', hd'⟩

/-- Message offsets do not wrap and remain inside the allocated record. -/
theorem phase2_message_offset_inside {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    (off : Nat) (hoff : off + 8 ≤ 176) {x : BitVec 64}
    (hx : evalAt s (.op .add [.var .local (ofString "m"), .const off]) =
      some (.val (.word x))) :
    Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176) := by
  obtain ⟨w, hw⟩ := hp.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have hhi := (ivl_allocated_bound hp.1.1.2 (Or.inl hp.2.2.2.1)).2
  have he : x = w + BitVec.ofNat 64 off := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr] using hx.symm
  have ho : off < 2 ^ 64 := by omega
  have hn : x.toNat = w.toNat + off := by
    rw [he, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho,
      Nat.mod_eq_of_lt (by dsimp at hhi; rw [hl] at hhi; omega)]
  rw [hn, hl]
  constructor <;> dsimp <;> omega

/-- Any scalar-valued message-field expression can be stored while retaining
the saved warm buffers and the nonzero backing-pointer environment. -/
theorem phase2_message_offset_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxMessageStoreReady buffers contents s → evalAt s value = some v →
      ∃ w, v = .val (.word w)) :
    Hoare (PtxMessageStoreReady buffers contents)
      (.store (.op .add [.var .local (ofString "m"), .const off]) value)
      (fun r s => r = none → PtxMessageStoreReady buffers contents s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, rfl⟩ := hv s v hp he
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact phase2_message_store_ready_store buffers contents hp hdom
    (phase2_message_offset_inside hp off hoff hx) hmem

/-- Message allocation retains the transaction environment after restoring the
caller locals, including both nonzero block-output backing pointers. -/
theorem phase2_msg_new_txEnv (h : PtxCallees) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s) TxEnv
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_msg_new s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" := by
    have hg := hs.2.2.1 (ofString "bo") (by decide)
    change s.globals.lookup (ofString "bo") = post.globals.lookup (ofString "bo") at hg
    simp only [globN, hg]
  have hj : globN post "journal_cap" = globN s "journal_cap" := by
    have hg := hs.2.2.1 (ofString "journal_cap") (by decide)
    change s.globals.lookup (ofString "journal_cap") = post.globals.lookup (ofString "journal_cap") at hg
    simp only [globN, hg]
  have hk : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    apply hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz k
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    · simp
  have hi : locN (setVarHOLFinite (ofString "m") v {post with locals := s.locals}) "index" =
      locN s "index" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "m" ≠ ofString "index" by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "bo" ≠ 0; rw [hbo]; exact hp.2.bo_nz
  · change memW post (globN post "bo" + 24) ≠ 0; rw [hbo, hk 24 (by simp)]; exact hp.2.bo24
  · change memW post (globN post "bo" + 32) ≠ 0; rw [hbo, hk 32 (by simp)]; exact hp.2.bo32
  · change memW post (globN post "bo" + 40) ≠ 0; rw [hbo, hk 40 (by simp)]; exact hp.2.bo40
  · change memW post (globN post "bo" + 72) ≠ 0; rw [hbo, hk 72 (by simp)]; exact hp.2.bo72
  · change locN (setVarHOLFinite (ofString "m") v {post with locals := s.locals}) "index" <
      memW post (globN post "bo" + 80)
    rw [hi, hbo, hk 80 (by simp)]; exact hp.2.idx_lt
  · change globN post "journal_cap" ≠ 0; rw [hj]; exact hp.2.jcap_nz

/-- Allocation establishes the reusable message-store invariant for all saved
warm buffers while preserving the block-output backing pointers. -/
theorem phase2_msg_new_store_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) :
    DecCallResumeOn
      (fun s => WorldOK s ∧ TxEnv s ∧ ∀ i, ∃ S Nd, WorldTypedWith s S Nd ∧
        PtxLiveBufferAt s S Nd (buffers i) (contents i))
      (PtxMessageStoreReady buffers contents)
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hg := phase2_msg_new_geometry h s vs body callee ret v post hc hp.1 he hl hb
  have henv := phase2_msg_new_txEnv h s vs body callee ret v post hc
    ⟨hp.1, hp.2.1⟩ he hl hb
  have hf := fun i => phase2_msg_new_live_ready h (buffers i) (contents i)
    s vs body callee ret v post hc ⟨hp.1, hp.2.2 i⟩ he hl hb
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨(hf i).1, henv, hg.1, hg.2.1, hg.2.2.1,
    fun j => ⟨(hf j).2.2.2.2.2.1, (hf j).2.2.2.2.2.2⟩⟩

/-- Every aligned message slot is allocated and its address does not wrap. -/
theorem phase2_message_slot {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    (k : Nat) (hk : k < 22) :
    let x := BitVec.ofNat 64 (locN s "m" + 8 * k)
    x.toNat = locN s "m" + 8 * k ∧ s.memaddrs x ∧
      Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176) := by
  have hhi := (ivl_allocated_bound hp.1.1.2 (Or.inl hp.2.2.2.1)).2
  have hlt : locN s "m" + 8 * k < 2 ^ 64 := by dsimp at hhi; omega
  have heq : (BitVec.ofNat 64 (locN s "m" + 8 * k)).toNat = locN s "m" + 8 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  refine ⟨heq, ?_, ?_⟩
  · exact (hp.2.2.2.2.1.2.2 k (by omega)).choose_spec.1
  · rw [heq]
    constructor <;> dsimp <;> omega

/-- Consecutive message writes preserve every saved buffer and the transaction
environment; in particular this covers the four-word value field at offset 56. -/
theorem phase2_message_store_ready_words {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (ws : List (HolWordLab 64)) {s : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageStoreReady buffers contents s) (k : Nat) (hk : k + ws.length ≤ 22)
    {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "m" + 8 * k)) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxMessageStoreReady buffers contents {s with memory := mem} := by
  induction ws generalizing s k mem with
  | nil =>
    simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst mem
    exact hp
  | cons w ws ih =>
    have hk' : k < 22 := by simp only [List.length_cons] at hk; omega
    have hslot := phase2_message_slot hp k hk'
    let x := BitVec.ofNat 64 (locN s "m" + 8 * k)
    let mem1 := fun a => if a = x then w else s.memory a
    have hp1 : PtxMessageStoreReady buffers contents {s with memory := mem1} :=
      phase2_message_store_ready_store buffers contents hp hslot.2.1 hslot.2.2
        (fun a ha => if_neg ha)
    have he : x + BitVec.ofNat 64 8 = BitVec.ofNat 64 (locN s "m" + 8 * (k + 1)) := by
      simp only [x, ← BitVec.ofNat_add]
      congr 1
    simp only [panMemStoresHOL, panMemStoreHOL, hslot.2.1, ↓reduceIte] at hst
    apply ih hp1 (k + 1) (by simp only [List.length_cons] at hk; omega)
    change @panMemStoresHOL 64 _ (BitVec.ofNat 64 (locN s "m" + 8 * (k + 1))) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem
    change @panMemStoresHOL 64 _ (x + BitVec.ofNat 64 8) ws
      s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) mem1 = some mem at hst
    rw [he] at hst
    exact hst

/-- A shape-sized source expression may initialize any fitting message slice. -/
theorem phase2_message_expr_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (src : ExpHOL 64) (k n : Nat) (hk : k + n ≤ 22)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxMessageStoreReady buffers contents s → evalAt s src = some v →
      (flattenHOL v).length = n) :
    Hoare (PtxMessageStoreReady buffers contents)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) src)
      (fun r s => r = none → PtxMessageStoreReady buffers contents s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "m" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact phase2_message_store_ready_words buffers contents (flattenHOL v) hp k
    (by rw [hlen s v hp hv]; exact hk) hst

/-- The transaction value is copied as four words into message slots 7 through 10. -/
theorem phase2_message_value_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) :
    Hoare (PtxMessageStoreReady buffers contents)
      (.store (.op .add [.var .local (ofString "m"), .const 56])
        (.load (.comb [.one, .one, .one, .one])
          (.op .add [.var .local (ofString "tx"), .const 160])))
      (fun r s => r = none → PtxMessageStoreReady buffers contents s) := by
  exact phase2_message_expr_store_hoare buffers contents _ 7 4 (by decide)
    (fun s v _ hv => phase2_load_quad_length s _ v hv)

/-- Scalar caller witnesses needed by message stores, retained with the spatial cut. -/
def PtxMessageScalarReady {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  PtxMessageStoreReady buffers contents s ∧
    ∀ name ∈ names, ∃ w : BitVec 64,
      s.locals.lookup (ofString name) = some (.val (.word w))

/-- A message write changes memory only, so caller scalar witnesses survive. -/
theorem phase2_message_scalar_expr_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (src : ExpHOL 64) (k n : Nat) (hk : k + n ≤ 22)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxMessageScalarReady buffers contents names s → evalAt s src = some v →
      (flattenHOL v).length = n) :
    Hoare (PtxMessageScalarReady buffers contents names)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) src)
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "m" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact ⟨phase2_message_store_ready_words buffers contents (flattenHOL v) hp.1 k
    (by rw [hlen s v hp hv]; exact hk) hst, hp.2⟩

theorem phase2_message_scalar_local_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (name : String) (hn : name ∈ names) (k : Nat) (hk : k < 22) :
    Hoare (PtxMessageScalarReady buffers contents names)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)])
        (.var .local (ofString name)))
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  apply phase2_message_scalar_expr_store buffers contents names _ k 1 (by omega)
  intro F s v hp hv
  obtain ⟨w, hw⟩ := hp.2 name hn
  have he : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  simp [he, flattenHOL]

theorem phase2_message_scalar_load_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (addr : ExpHOL 64) (k : Nat) (hk : k < 22) :
    Hoare (PtxMessageScalarReady buffers contents names)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) (.load .one addr))
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  exact phase2_message_scalar_expr_store buffers contents names _ k 1 (by omega)
    (fun s v _ hv => phase2_load_one_length s addr v hv)

theorem phase2_message_scalar_const_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (w : BitVec 64) (k : Nat) (hk : k < 22) :
    Hoare (PtxMessageScalarReady buffers contents names)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) (.const w))
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  apply phase2_message_scalar_expr_store buffers contents names _ k 1 (by omega)
  intro F s v _ hv
  have he : v = .val (.word w) := by simpa [evalAt, evalHOLExact] using hv.symm
  simp [he, flattenHOL]

/-- The six ordinary-call branch stores set recipient, input and code fields. -/
def phase2_message_call_stores : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "m"), .const 32])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 88])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 192])))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 96])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 200])))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 112])
      (.var .local (ofString "empty")))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 120]) (.const 0))
    (.store (.op .add [.var .local (ofString "m"), .const 104])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))))))

theorem phase2_message_call_stores_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (he : "empty" ∈ names) :
    Hoare (PtxMessageScalarReady buffers contents names) phase2_message_call_stores
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  unfold phase2_message_call_stores
  apply Hoare.seq_fall (phase2_message_scalar_load_store buffers contents names _ 4 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_load_store buffers contents names _ 11 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_load_store buffers contents names _ 12 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_local_store buffers contents names "empty" he 14 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_const_store buffers contents names 0 15 (by decide))
  exact phase2_message_scalar_load_store buffers contents names _ 13 (by decide)

/-- The six create-branch stores following contract-address computation. -/
def phase2_message_create_stores : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "m"), .const 32])
      (.var .local (ofString "ct")))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 88])
      (.var .local (ofString "empty")))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 96]) (.const 0))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 112])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 192])))
  (.seq (.store (.op .add [.var .local (ofString "m"), .const 120])
      (.load .one (.op .add [.var .local (ofString "tx"), .const 200])))
    (.store (.op .add [.var .local (ofString "m"), .const 104]) (.const 0))))))

theorem phase2_message_create_stores_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (hc : "ct" ∈ names) (he : "empty" ∈ names) :
    Hoare (PtxMessageScalarReady buffers contents names) phase2_message_create_stores
      (fun r s => r = none → PtxMessageScalarReady buffers contents names s) := by
  unfold phase2_message_create_stores
  apply Hoare.seq_fall (phase2_message_scalar_local_store buffers contents names "ct" hc 4 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_local_store buffers contents names "empty" he 11 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_const_store buffers contents names 0 12 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_load_store buffers contents names _ 14 (by decide))
  apply Hoare.seq_fall (phase2_message_scalar_load_store buffers contents names _ 15 (by decide))
  exact phase2_message_scalar_const_store buffers contents names 0 13 (by decide)

/-- Evaluating a message-field address identifies its exact non-wrapping offset. -/
theorem phase2_message_offset_eq {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    (off : Nat) (hoff : off + 8 ≤ 176) {x : BitVec 64}
    (hx : evalAt s (.op .add [.var .local (ofString "m"), .const off]) =
      some (.val (.word x))) : x.toNat = locN s "m" + off := by
  obtain ⟨w, hw⟩ := hp.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have hhi := (ivl_allocated_bound hp.1.1.2 (Or.inl hp.2.2.2.1)).2
  have he : x = w + BitVec.ofNat 64 off := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr] using hx.symm
  have ho : off < 2 ^ 64 := by omega
  rw [he, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho,
    Nat.mod_eq_of_lt (by dsimp at hhi; rw [hl] at hhi; omega), hl]

/-- A scalar store records the selected field and frames every other message word. -/
theorem phase2_message_store_fields {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    (off : Nat) (hoff : off + 8 ≤ 176) {x w : BitVec 64}
    (hx : evalAt s (.op .add [.var .local (ofString "m"), .const off]) =
      some (.val (.word x))) {mem : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x [.word w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem) :
    PtxMessageStoreReady buffers contents {s with memory := mem} ∧
    memW {s with memory := mem} (locN s "m" + off) = w.toNat ∧
    ∀ k, k < 22 → 8 * k ≠ off →
      memW {s with memory := mem} (locN s "m" + 8 * k) =
        memW s (locN s "m" + 8 * k) := by
  obtain ⟨hd, hw, hm⟩ := panMemStoresHOL_word_spec hst
  have he := phase2_message_offset_eq hp off hoff hx
  refine ⟨phase2_message_store_ready_store buffers contents hp hd
    (phase2_message_offset_inside hp off hoff hx) hm, ?_, ?_⟩
  · have hx' : BitVec.ofNat 64 (locN s "m" + off) = x := by
      rw [← he]; simp
    simp [memW, hx', hw]
  · intro k hk hne
    have hslot := phase2_message_slot hp k hk
    have hx' : BitVec.ofNat 64 (locN s "m" + 8 * k) ≠ x := by
      intro hh
      have he' := congrArg BitVec.toNat hh
      rw [hslot.1, he] at he'
      omega
    simp only [memW]
    rw [hm _ hx']

/-- Any surviving message-store cut exposes the two required backing pointers. -/
theorem phase2_message_backing_nonzero {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s) :
    memW s (globN s "bo" + 40) ≠ 0 ∧ memW s (globN s "bo" + 72) ≠ 0 :=
  ⟨hp.2.1.bo40, hp.2.1.bo72⟩

/-- A world step with no caller-buffer writes preserves the allocated message
and every saved buffer. The caller supplies its restored environment and message local. -/
theorem phase2_message_store_ready_world_step {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxMessageStoreReady buffers contents s)
    (ha : ArenaReady post) (he : TxEnv post)
    (hl : post.locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hs : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ S' Nd', WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s)) :
    PtxMessageStoreReady buffers contents post := by
  have hm : locN post "m" = locN s "m" := by simp only [locN, hl]
  have hf : ∀ i, ∃ S Nd, WorldTypedWith post S Nd ∧
      PtxLiveBufferAt post S Nd (buffers i) (contents i) ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned post S Nd) := by
    intro i
    obtain ⟨hd, S, Nd, hw, hb, hmd⟩ := hp.2.2.2.2.2 i
    obtain ⟨S', Nd', hw', hg, hfr⟩ := hs S Nd hw
    refine ⟨S', Nd', hw', ?_, ?_⟩
    · exact phase2_live_buffer_step s post S Nd S' Nd' (buffers i) (contents i) []
        hb hp.1.1.2 hw hh hg hfr (by simp) (by simp)
    · exact phase2_packed_owned_growth s post _ _ (locN s "m", 176)
        hp.2.2.2.1 hg hmd
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨S, Nd, hw, _, _⟩ := hf i
  refine ⟨⟨ha, S, (worldTyped_iff_with post S).mpr ⟨Nd, hw⟩⟩, he, ?_, ?_, ?_, ?_⟩
  · simpa only [hl] using hp.2.2.1
  · rw [hm]
    exact ⟨hp.2.2.2.1.1, hp.2.2.2.1.2.trans hh⟩
  · rw [hm]
    exact wordsOK_transfer hp.1.1.1 ha.1 hp.2.2.2.2.1
  · intro j
    rw [hm]
    exact ⟨(hp.2.2.2.2.2 j).1, hf j⟩

/-- Restoring caller locals transports the message-store cut when `m` and
the transaction index are unchanged. -/
theorem phase2_message_store_ready_with_locals {ι F : Type}
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) (hp : PtxMessageStoreReady buffers contents s)
    (hm : locals.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hi : locals.lookup (ofString "index") = s.locals.lookup (ofString "index")) :
    PtxMessageStoreReady buffers contents {s with locals := locals, clock := clock} := by
  have hm' := locN_congr s locals clock "m" hm
  have hi' := locN_congr s locals clock "index" hi
  refine ⟨localsFree_worldOK s locals clock hp.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hp.2.1.bo_nz, hp.2.1.bo24, hp.2.1.bo32, hp.2.1.bo40,
      hp.2.1.bo72, by rw [hi']; exact hp.2.1.idx_lt, hp.2.1.jcap_nz⟩
  · simpa only [hm] using hp.2.2.1
  · rw [hm']; exact hp.2.2.2.1
  · rw [hm']; exact hp.2.2.2.2.1
  · intro i
    obtain ⟨hd, S, Nd, hw, hb, hmd⟩ := hp.2.2.2.2.2 i
    rw [hm']
    exact ⟨hd, S, Nd, (worldTypedWith_with_locals s locals clock S Nd).mpr hw, hb, hmd⟩

/-- An allocation-style world step frames every initialized message field. -/
theorem phase2_message_world_step_fields {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (s post : PanSemStateFiniteExact 64 F)
    (hp : PtxMessageStoreReady buffers contents s)
    (hs : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ S' Nd', WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd') ∧
        FrameOutside s post (worldOwned s S Nd ++ [] ++ [freeGap s]) (heapFree s)) :
    ∀ k, k < 22 → memW post (locN s "m" + 8 * k) = memW s (locN s "m" + 8 * k) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨_, S, Nd, hw, _, hd⟩ := hp.2.2.2.2.2 i
  obtain ⟨S', Nd', _, _, hf⟩ := hs S Nd hw
  intro k hk
  apply phase2_world_frame_heap_disjoint s post _ [] (locN s "m", 176)
    (locN s "m" + 8 * k) hp.1.1.2 hp.2.2.2.1
  · constructor <;> dsimp <;> omega
  · have hal := hp.2.2.2.2.1.1
    simp [Nat.add_mod, hal]
  · exact hf
  · exact hd _ (by simp)
  · simp
  · exact worldOwned_zero_aligned hw
  · simp

/-- Suffix allocations retain the backing-pointer environment after caller restoration. -/
theorem phase2_alloc_txEnv (h : PtxCallees) (name : MlS) (args : List (ExpHOL 64))
    (hi : name ≠ ofString "index") :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s) TxEnv name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" := by
    have hg := hs.2.2.1 (ofString "bo") (by decide)
    change s.globals.lookup (ofString "bo") = post.globals.lookup (ofString "bo") at hg
    simp only [globN, hg]
  have hj : globN post "journal_cap" = globN s "journal_cap" := by
    have hg := hs.2.2.1 (ofString "journal_cap") (by decide)
    change s.globals.lookup (ofString "journal_cap") = post.globals.lookup (ofString "journal_cap") at hg
    simp only [globN, hg]
  have hk : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    apply hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz k
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    · simp
  have hi' : locN (setVarHOLFinite name v {post with locals := s.locals}) "index" =
      locN s "index" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "bo" ≠ 0; rw [hbo]; exact hp.2.bo_nz
  · change memW post (globN post "bo" + 24) ≠ 0; rw [hbo, hk 24 (by simp)]; exact hp.2.bo24
  · change memW post (globN post "bo" + 32) ≠ 0; rw [hbo, hk 32 (by simp)]; exact hp.2.bo32
  · change memW post (globN post "bo" + 40) ≠ 0; rw [hbo, hk 40 (by simp)]; exact hp.2.bo40
  · change memW post (globN post "bo" + 72) ≠ 0; rw [hbo, hk 72 (by simp)]; exact hp.2.bo72
  · change locN (setVarHOLFinite name v {post with locals := s.locals}) "index" <
      memW post (globN post "bo" + 80)
    rw [hi', hbo, hk 80 (by simp)]; exact hp.2.idx_lt
  · change globN post "journal_cap" ≠ 0; rw [hj]; exact hp.2.jcap_nz

/-- Allocating `empty` or `ct` preserves the reusable message-store invariant. -/
theorem phase2_alloc_message_store_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index") :
    DecCallResumeOn (PtxMessageStoreReady buffers contents)
      (PtxMessageStoreReady buffers contents) name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  apply phase2_message_store_ready_world_step buffers contents s _ hp
  · exact (arenaReady_with_locals post _ post.clock).mpr hs.1
  · exact phase2_alloc_txEnv h name args hi s vs body callee ret v post hc
      ⟨hp.1, hp.2.1⟩ he hl hb
  · simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm]
  · exact hs.2.1
  · intro S Nd hw
    obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := hs.2.2.2.2 S Nd
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) (by simp [IvlsDisj])
    exact ⟨S', Nd', (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw', hg, hf⟩

/-- Final message readiness from one joint world witness for the two access tables.
The message geometry and transaction environment come from the store cut. -/
theorem phase2_message_ready_of_tables {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (ha : memW s (locN s "m" + 152) ∈ S)
    (hk : memW s (locN s "m" + 160) ∈ S)
    (hd : IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd))
    (hg : memW s (locN s "m" + 40) < 2 ^ 63)
    (hr : RolesOK s S (worldRoleSlots s ++
      [(memW s (locN s "m" + 152), "frame.addr"),
        (memW s (locN s "m" + 160), "frame.key")]) (journalRoleSlots s)) :
    PtxMessageReady s := by
  have hbound := (ivl_allocated_bound hp.1.1.2 (Or.inl hp.2.2.2.1)).2
  have hm : locN (setVarHOLFinite (ofString "msg")
      (.val (.word (BitVec.ofNat 64 (locN s "m")))) s) "msg" = locN s "m" := by
    change (BitVec.ofNat 64 (locN s "m")).toNat = locN s "m"
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp at hbound; omega)]
  refine ⟨⟨hp.1, hp.2.1⟩, ?_⟩
  unfold MsgReady
  rw [hm]
  refine ⟨(arenaReady_with_locals s _ s.clock).mpr hp.1.1, S,
    (worldTyped_with_locals s _ s.clock S).mpr ((worldTyped_iff_with s S).mpr ⟨Nd, hw⟩),
    ha, hk, hp.2.2.2.1, hp.2.2.2.2.1, ?_, ?_, ?_, hg, hr⟩
  · intro t ht i hi
    exact hd _ (by simp) i (by
      simp only [worldOwned, List.mem_append]
      exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hi⟩)))
  · intro j hj
    exact hd _ (by simp) j (by
      simp only [worldOwned, List.mem_append]
      exact Or.inl (Or.inr hj))
  · refine ⟨Nd, hw.2.2.2, ?_⟩
    intro o ho j hj
    exact hd o ho j (by simp only [worldOwned, List.mem_append]; exact Or.inr hj)

/-- Two fresh access tables can be assigned the message roles. -/
theorem phase2_roles_access_tables {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (ht : TablesTyped s S) {aa ak : Nat}
    (ha : aa ∈ S) (hk : ak ∈ S)
    (hal : hdr s aa 0 = 20) (hkl : hdr s ak 0 = 52)
    (haf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa)
    (hkf : ∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) :
    RolesOK s S (worldRoleSlots s ++ [(aa, "frame.addr"), (ak, "frame.key")])
      (journalRoleSlots s) := by
  have hne : aa ≠ ak := by intro he; rw [he, hkl] at hal; contradiction
  obtain ⟨hr1, hr2, hr3⟩ := ht.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a hmem
    rw [List.append_assoc] at hmem
    rcases List.mem_append.1 hmem with hw | hrest
    · exact hr1 a (List.mem_append.2 (Or.inl hw))
    · rcases List.mem_append.1 hrest with hfk | hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact ⟨ha, hal⟩
        · exact ⟨hk, hkl⟩
      · exact hr1 a (List.mem_append.2 (Or.inr hj))
  · rw [List.pairwise_append]
    refine ⟨hr2, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨fun b hb he => ?_, List.pairwise_singleton _ _⟩
      simp only [List.mem_singleton] at hb
      subst b
      exact (hne he).elim
    · intro a ha b hb he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (haf a (List.mem_append.2 (Or.inl ha)) he).elim
      · exact (hkf a (List.mem_append.2 (Or.inl ha)) he).elim
  · intro a ha b hb he
    rw [List.append_assoc] at hb
    rcases List.mem_append.1 hb with hw | hrest
    · exact hr3 a ha b (List.mem_append.2 (Or.inl hw)) he
    · rcases List.mem_append.1 hrest with hfk | hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfk
        rcases hfk with rfl | rfl
        · exact (haf a (List.mem_append.2 (Or.inr ha)) he).elim
        · exact (hkf a (List.mem_append.2 (Or.inr ha)) he).elim
      · exact hr3 a ha b (List.mem_append.2 (Or.inr hj)) he

/-- A joint world witness retains the access tables and message separation. -/
def PtxMessageTables {F : Type} (s : PanSemStateFiniteExact 64 F)
    (aa ak : Nat) : Prop :=
  ∃ S Nd, WorldTypedWith s S Nd ∧ aa ∈ S ∧ ak ∈ S ∧
    hdr s aa 0 = 20 ∧ hdr s ak 0 = 52 ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ aa) ∧
    (∀ a ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 ≠ ak) ∧
    IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd)

theorem phase2_message_ready_of_access_tables {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (ha : memW s (locN s "m" + 152) = aa)
    (hk : memW s (locN s "m" + 160) = ak)
    (hg : memW s (locN s "m" + 40) < 2 ^ 63) : PtxMessageReady s := by
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := ht
  apply phase2_message_ready_of_tables hp hw
  · rw [ha]; exact ham
  · rw [hk]; exact hkm
  · exact hd
  · exact hg
  · rw [ha, hk]
    exact phase2_roles_access_tables hw.1 ham hkm hal hkl haf hkf

/-- Table membership and message separation survive world growth. Header and
role preservation are explicit because arbitrary world steps may mutate tables. -/
theorem phase2_message_tables_world_step {F : Type}
    (s post : PanSemStateFiniteExact 64 F) {aa ak : Nat}
    (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hm : locN post "m" = locN s "m")
    (hwr : worldRoleSlots post = worldRoleSlots s)
    (hjr : journalRoleSlots post = journalRoleSlots s)
    (haa : hdr post aa 0 = hdr s aa 0) (hak : hdr post ak 0 = hdr s ak 0)
    (hs : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd')) :
    PtxMessageTables post aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  obtain ⟨S', Nd', hsub, hw', hg⟩ := hs S Nd hw
  refine ⟨S', Nd', hw', hsub aa ha, hsub ak hk, haa.trans hal, hak.trans hkl,
    ?_, ?_, ?_⟩
  · rw [hwr, hjr]; exact haf
  · rw [hwr, hjr]; exact hkf
  · rw [hm]
    exact phase2_packed_owned_growth s post _ _ _ hin hg hd

/-- Transport the joint witness when world roles change but still exclude the
two private access tables. This permits account creation to add world roles. -/
theorem phase2_message_tables_world_step_roles {F : Type}
    (s post : PanSemStateFiniteExact 64 F) {aa ak : Nat}
    (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hm : locN post "m" = locN s "m")
    (haf : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ aa)
    (hkf : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ ak)
    (haa : hdr post aa 0 = hdr s aa 0) (hak : hdr post ak 0 = hdr s ak 0)
    (hs : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd')) :
    PtxMessageTables post aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, _, _, hd⟩ := ht
  obtain ⟨S', Nd', hsub, hw', hg⟩ := hs S Nd hw
  refine ⟨S', Nd', hw', hsub aa ha, hsub ak hk, haa.trans hal, hak.trans hkl,
    haf, hkf, ?_⟩
  rw [hm]
  exact phase2_packed_owned_growth s post _ _ _ hin hg hd

/-- Restoring caller locals only needs to preserve the message pointer. -/
theorem phase2_message_tables_with_locals {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hm : locals.lookup (ofString "m") = s.locals.lookup (ofString "m")) :
    PtxMessageTables {s with locals := locals, clock := clock} aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  refine ⟨S, Nd, (worldTypedWith_with_locals s locals clock S Nd).mpr hw,
    ha, hk, hal, hkl, haf, hkf, ?_⟩
  rw [locN_congr s locals clock "m" hm]
  exact hd

/-- Concrete allocation preserves the joint access-table witness. -/
theorem phase2_alloc_message_tables (h : PtxCallees) {ι : Type}
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") :
    DecCallResumeOn (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak)
      (fun s => PtxMessageTables s aa ak) name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := R16Shards.PtxP1.funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  have hn : ∃ n : BitVec 64, callee.lookup (ofString "n") = some (.val (.word n)) := by
    have hx := hl
    rw [hc] at hx
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hx
    split at hx
    · cases hx
    rename_i b ls rs hraw
    have heq := Option.some.inj hx
    have hcal := congrArg (fun z => z.2.1.lookup) heq
    simp only at hcal
    rw [← hcal]
    simp only [lookupCodeHOLExact, InitECandidate.Solver.Wave8Contracts.M27.lookup_alloc_te] at hraw
    cases vs with
    | nil => simp at hraw
    | cons nv rest =>
      cases rest with
      | cons nv2 rest => simp at hraw
      | nil =>
        cases nv with
        | val w =>
          cases w with
          | word n =>
            simp [shapeEqHOL, shapeOfHOLExact] at hraw
            obtain ⟨_, hcal, _⟩ := hraw
            subst ls
            exact ⟨n, by rw [← hcal]; rfl⟩
        | rStruct fs => simp [shapeEqHOL, shapeOfHOLExact] at hraw
        | nStruct nm fs => simp [shapeEqHOL, shapeOfHOLExact] at hraw
  obtain ⟨n, hn⟩ := hn
  have hheap : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    have hpos : globN s "heap_ptr" ≠ 0 := by
      have hh := hp.1.1.1.2.1
      have : 0 < InitE.sourceBase := by decide
      omega
    cases hg : s.globals.lookup (ofString "heap_ptr") with
    | none => simp [globN, hg] at hpos
    | some val =>
      rcases val with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨w, rfl⟩
      · simp [globN, hg] at hpos
      · simp [globN, hg] at hpos
  obtain ⟨p, hpw⟩ := hheap
  have hbody : body = InitECandidate.Solver.GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_alloc := by
    have hx := InitECandidate.Solver.GuestGlobalKeep.lookupCode_installed hl
    rw [hc, R16Shards.PtxP1.lookup_alloc] at hx
    obtain ⟨params, rs, hx⟩ := hx
    exact congrArg (fun z => z.2.1) (Option.some.inj hx).symm
  have hrun := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
    (callEntryStateHOLFinite s callee) p n hc hpw hn v
  rw [← hbody, hb] at hrun
  have hpost := (hrun rfl).2.2.2
  dsimp only at hpost
  have hmem : post.memory = s.memory := congrArg (fun t => t.memory) hpost
  have hgn : ∀ g, ofString "heap_ptr" ≠ ofString g → globN post g = globN s g := by
    intro g hne
    rw [hpost]
    simp [globN, HolFiniteMapExact.update, FUPDATE, hne, callEntryStateHOLFinite]
  have hwr : worldRoleSlots post = worldRoleSlots s := by
    simp only [worldRoleSlots, recRoles, nestRoles, balRecords, htabValues, nodeF, hdr, memW, hmem,
      hgn "ws" (by decide), hgn "bs" (by decide), hgn "ts" (by decide),
      hgn "bal_accounts" (by decide), hgn "bal_idx_accts" (by decide), hgn "bal_idx_stor" (by decide)]
    rfl
  have hjr : journalRoleSlots post = journalRoleSlots s := by
    simp only [journalRoleSlots, journalRole, memW, hmem, hgn "journal_n" (by decide),
      hgn "journal" (by decide), hgn "ts" (by decide)]
    rfl
  apply phase2_message_tables_world_step s _ hp.2 hp.1.2.2.2.1
  · simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm]
  · exact hwr
  · exact hjr
  · simp only [hdr, memW, hmem]; rfl
  · simp only [hdr, memW, hmem]; rfl
  · intro S Nd hw
    obtain ⟨S', Nd', hsub, hw', hg, hf, _⟩ := hs.2.2.2.2 S Nd
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) (by simp [IvlsDisj])
    exact ⟨S', Nd', hsub, (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw', hg⟩

/-- Allocation preserves both the saved-buffer cut and the joint table witness. -/
theorem phase2_alloc_message_tables_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index") :
    DecCallResumeOn (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak)
      (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak)
      name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  exact ⟨phase2_alloc_message_store_ready h buffers contents name args hm hi
    s vs body callee ret v post hc hp.1 he hl hb,
    phase2_alloc_message_tables h buffers contents aa ak name args hm
      s vs body callee ret v post hc hp he hl hb⟩

/-- The suffix allocation can be composed with a table-aware continuation. -/
theorem phase2_alloc_message_tables_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak)
      (.decCall name .one (ofString "alloc") args tail) (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) h.fb_alloc
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1
  · exact phase2_alloc_message_tables_ready h buffers contents aa ak name args hm hi
  · exact ht

open R16Shards

/-- A write outside world-owned objects preserves the nested list backing words. -/
theorem phase2_backing_store_outside_world {F : Type}
    {s : PanSemStateFiniteExact 64 F} (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd) (hb : TxBacking s)
    {blk : Ivl} (hd : ∀ o ∈ worldOwned s S Nd, Disj blk o)
    {x : BitVec 64} (_hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) blk.1 (blk.1 + blk.2))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    TxBacking {s with memory := mem} := by
  have hu : ∀ i ∈ fixedObjects s, IvlUnhit s {s with memory := mem} i := by
    intro i hi
    apply ivlUnhit_single hm
    · intro hz; rw [fixedObjects_zero_aligned i hi hz]
    · exact disj_of_inside_right hin (disj_symm (hd i
        (List.mem_append_left _ (List.mem_append_right _ hi))))
  have hf : ∀ i ∈ fixedObjects s, i.2 ≠ 0 →
      Allocated s i ∧ WordsOK s i := by
    intro i hi hn
    rcases hw.2.2.1.1 i hi with hz | hh
    · exact (hn hz).elim
    · exact hh
  have hbo : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hl : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
  apply PtxP34.txBacking_of_unhit_headers (post := {s with memory := mem}) hb rfl
  · exact (hf _ hbo (by simp)).2.1
  · exact (ivl_allocated_bound ha.2 (hf _ hbo (by simp)).1).2
  · exact hu _ hbo
  · intro k hk; exact (hf _ (hl k hk) (by simp)).2.1
  · intro k hk; exact (ivl_allocated_bound ha.2 (hf _ (hl k hk) (by simp)).1).2
  · intro k hk; exact hu _ (hl k hk)

/-- Message writes retain both the saved buffers and the true nested backing guard. -/
theorem phase2_message_store_backing {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    (hb : TxBacking s) {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxMessageStoreReady buffers contents {s with memory := mem} ∧
      TxBacking {s with memory := mem} := by
  refine ⟨phase2_message_store_ready_store buffers contents hp hx hin hm, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨_, S, Nd, hw, _, hd⟩ := hp.2.2.2.2.2 i
  exact phase2_backing_store_outside_world (blk := (locN s "m", 176)) hp.1.1 hp.2.1 hw hb
    (fun o ho => hd _ (by simp) o ho) hx hin hm

/-- Scalar message stores compose with backing-aware continuations. -/
theorem phase2_message_offset_store_backing_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxMessageStoreReady buffers contents s → evalAt s value = some v →
      ∃ w, v = .val (.word w)) :
    Hoare (fun s => PtxMessageStoreReady buffers contents s ∧ TxBacking s)
      (.store (.op .add [.var .local (ofString "m"), .const off]) value)
      (fun r s => r = none → PtxMessageStoreReady buffers contents s ∧ TxBacking s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, rfl⟩ := hv s v hp.1 he
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact phase2_message_store_backing buffers contents hp.1 hp.2 hdom
    (phase2_message_offset_inside hp.1 off hoff hx) hmem

/-- Message-field writes preserve the joint access-table witness, including
the absence of pre-existing world and journal roles for both tables. -/
theorem phase2_message_tables_store {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxMessageTables {s with memory := mem} aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  let post := {s with memory := mem}
  have hdw : ∀ o ∈ worldOwned s S Nd, Disj (locN s "m", 176) o :=
    fun o ho => hd _ (by simp) o ho
  have hu : ∀ o ∈ worldOwned s S Nd, IvlUnhit s post o := by
    intro o ho
    exact ivlUnhit_single hm (worldOwned_zero_aligned hw o ho)
      (disj_of_inside_right hin (disj_symm (hdw o ho)))
  have huf : ∀ o ∈ fixedObjects s, IvlUnhit s post o :=
    fun o ho => hu o (List.mem_append_left _ (List.mem_append_right _ ho))
  have hut : ∀ t ∈ S, ∀ o ∈ htabFootprint s t, IvlUnhit s post o :=
    fun t ht o ho => hu o (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨t, ht, ho⟩)))
  have hur : ∀ g sz, (g, sz) ∈ typedRecords → globN s g ≠ 0 →
      IvlUnhit s post (globN s g, sz) := by
    intro g sz hg hn
    apply huf
    simpa [hn] using typedRecord_mem_fixedObjects s hg
  have hgs : R16Shards.WorldGlobalsSame s post := by
    unfold R16Shards.WorldGlobalsSame
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  have hlow : memW post 8 = memW s 8 ∧ memW post 16 = memW s 16 := by
    have hlo := ((ordinaryDomain_iff x).mp (hp.1.1.1.memaddrs ▸ hx)).2.1
    have hsb : 16 < InitE.sourceBase := by decide
    constructor
    · simp only [memW, post]
      rw [hm (BitVec.ofNat 64 8) (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
    · simp only [memW, post]
      rw [hm (BitVec.ofNat 64 16) (by
        intro he; have := congrArg BitVec.toNat he; norm_num at this; omega)]
  have hwr : worldRoleSlots post = worldRoleSlots s := by
    apply R16Shards.worldRoleSlots_eq_of_unhit hp.1.1.2 hw.1 hw.2.2.1 hgs hut
      (hur "ws" 40 (by decide)) (hur "bs" 80 (by decide)) (hur "ts" 72 (by decide))
    · intro i hi; exact huf i (List.mem_append_right _ hi)
    · exact hlow
  have hjr : journalRoleSlots post = journalRoleSlots s := by
    apply (R16Shards.journalRoleSlots_eq_of_unhit (post := post) hp.1.1.1
      (guestInv_congr (s := s) rfl rfl rfl rfl hp.1.1.1) hp.1.1.2
      (show AllocatorGrows s post from ⟨le_rfl, le_rfl⟩)
      (fun t (ht : t ∈ S) => ht) hw.2.1 hw.2.2.1 hgs (hur "ts" 72 (by decide)) ?_).1
    intro hn
    apply huf
    simp [fixedObjects, hn]
  have hhdr : ∀ t ∈ S, hdr post t 0 = hdr s t 0 := by
    intro t ht
    have hf : (t, 88) ∈ htabFootprint s t := by simp [htabFootprint]
    have hb := (hw.1.2.1 t ht).1.1 _ hf
    have hbound : t + 88 ≤ 2 ^ 64 := by
      have hh := hb.1.2
      have he : InitE.heapEnd ≤ 2 ^ 64 := by decide
      dsimp at hh; omega
    exact (htabFootprint_eq_of_hdr_unhit hb.2.1 hbound (hut t ht _ hf)).1 0 (by decide)
  obtain ⟨hw', how, _⟩ := store_outside_worldOwned hp.1.1 hp.2.1 hw hdw hx hin hm
  refine ⟨S, Nd, hw', ha, hk, (hhdr aa ha).trans hal, (hhdr ak hk).trans hkl, ?_, ?_, ?_⟩
  · change ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ aa
    rw [hwr, hjr]; exact haf
  · change ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ ak
    rw [hwr, hjr]; exact hkf
  · rw [how]; exact hd

/-- One message write simultaneously preserves saved buffers, access tables,
and the nested block-output backing pointers. -/
theorem phase2_message_tables_backing_store {ι F : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak) (hb : R16Shards.TxBacking s)
    {x : BitVec 64} (hx : s.memaddrs x)
    (hin : Inside (x.toNat, 8) (locN s "m") (locN s "m" + 176))
    {mem : BitVec 64 → HolWordLab 64} (hm : ∀ a, a ≠ x → mem a = s.memory a) :
    PtxMessageStoreReady buffers contents {s with memory := mem} ∧
      PtxMessageTables {s with memory := mem} aa ak ∧
      R16Shards.TxBacking {s with memory := mem} := by
  have hh := phase2_message_store_backing buffers contents hp hb hx hin hm
  exact ⟨hh.1, phase2_message_tables_store hp ht hx hin hm, hh.2⟩

/-- Hoare form of the joint table-and-backing message-store frame. -/
theorem phase2_message_tables_backing_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxMessageStoreReady buffers contents s → evalAt s value = some v →
      ∃ w, v = .val (.word w)) :
    Hoare (fun s => PtxMessageStoreReady buffers contents s ∧
      PtxMessageTables s aa ak ∧ R16Shards.TxBacking s)
      (.store (.op .add [.var .local (ofString "m"), .const off]) value)
      (fun r s => r = none → PtxMessageStoreReady buffers contents s ∧
        PtxMessageTables s aa ak ∧ R16Shards.TxBacking s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, rfl⟩ := hv s v hp.1 he
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact phase2_message_tables_backing_store buffers contents hp.1 hp.2.1 hp.2.2 hdom
    (phase2_message_offset_inside hp.1 off hoff hx) hmem

/-- Exactly the caller locals required by the Phase-4 shape guard. -/
theorem phase2_phase4_shapes_localsOnly :
    LocalsOnly ["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"]
      PtxPhase4LocalShapes := by
  intro F s locals clock hl hp
  refine ⟨?_, ?_, ?_⟩
  · intro name hn
    change ∃ w, locals.lookup (ofString name) = some (.val (.word w))
    rw [hl name (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢
      tauto)]
    exact hp.1 name hn
  · change ∃ v, locals.lookup (ofString "price") = some v ∧ _
    rw [hl "price" (by simp)]; exact hp.2.1
  · change ∃ v, locals.lookup (ofString "intrinsic") = some v ∧ _
    rw [hl "intrinsic" (by simp)]; exact hp.2.2

/-- The full suffix store invariant also retains the Phase-4 caller shapes. -/
theorem phase2_message_tables_backing_shapes_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    (off : Nat) (hoff : off + 8 ≤ 176) (value : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxMessageStoreReady buffers contents s → evalAt s value = some v →
      ∃ w, v = .val (.word w)) :
    Hoare (fun s => (PtxMessageStoreReady buffers contents s ∧
      PtxMessageTables s aa ak ∧ TxBacking s) ∧ PtxPhase4LocalShapes s)
      (.store (.op .add [.var .local (ofString "m"), .const off]) value)
      (fun r s => r = none → (PtxMessageStoreReady buffers contents s ∧
        PtxMessageTables s aa ak ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, rfl⟩ := hv s v hp.1.1 he
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec
    (by simpa only [flattenHOL] using hst)
  exact ⟨phase2_message_tables_backing_store buffers contents hp.1.1 hp.1.2.1 hp.1.2.2 hdom
    (phase2_message_offset_inside hp.1.1 off hoff hx) hmem, hp.2⟩

/-- Discharge the exact postcondition of the backing-aware Phase-1/2 cut once
the message fields, nested backing guard, and caller shapes are established. -/
theorem phase2_message_ready_backing_shapes {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s : PanSemStateFiniteExact 64 F} (hp : PtxMessageStoreReady buffers contents s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hb : TxBacking s) (hs : PtxPhase4LocalShapes s)
    (ha : memW s (locN s "m" + 152) = aa)
    (hk : memW s (locN s "m" + 160) = ak)
    (hg : memW s (locN s "m" + 40) < 2 ^ 63) :
    (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s :=
  ⟨⟨phase2_message_ready_of_access_tables hp ht ha hk hg, hb⟩, hs⟩

/-- Concrete allocation changes neither memory nor the block-output root,
so it preserves both nested backing pointers. -/
theorem phase2_alloc_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxBacking s) TxBacking
      name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hl' := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "alloc")
    vs body callee ret hl
  unfold lookupCodeHOLExact at hl'
  rw [hc, InitECandidate.Solver.Wave8Contracts.M27.lookup_alloc_te] at hl'
  dsimp only at hl'
  split at hl'
  · rename_i hcond
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj hl')
    obtain ⟨hlocal, _⟩ := Prod.mk.inj hrest
    rcases vs with _ | ⟨nv, _ | _⟩
    · simp at hcond
    · rcases nv with ⟨⟨n⟩⟩ | _ | _
      · have hn : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
            some (.val (.word n)) := by
          change callee.lookup (ofString "n") = _
          rw [← hlocal]; simp [List.zip, List.foldl]
        obtain ⟨p, hpl⟩ := hp.1.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
        have hr := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
          (callEntryStateHOLFinite s callee) p n hc hpl hn v
        rw [hb] at hr
        have hpost := (hr rfl).2.2.2
        dsimp only at hpost
        have hm : post.memory = s.memory := congrArg (fun t => t.memory) hpost
        have hg : globN post "bo" = globN s "bo" := by
          rw [hpost]
          simp [globN, HolFiniteMapExact.update, FUPDATE, callEntryStateHOLFinite,
            show ofString "heap_ptr" ≠ ofString "bo" by decide]
        change memW post (memW post (globN post "bo" + 40)) ≠ 0 ∧
          memW post (memW post (globN post "bo" + 72)) ≠ 0
        simpa only [TxBacking, hg, memW, hm] using hp.2
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
    · simp at hcond
  · cases hl'

/-- Suffix allocation retains the table-aware cut and nested backing together. -/
theorem phase2_alloc_message_tables_backing_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index") :
    DecCallResumeOn (fun s => (PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) ∧ TxBacking s)
      (fun s => (PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) ∧ TxBacking s)
      name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  exact ⟨phase2_alloc_message_tables_ready h buffers contents aa ak name args hm hi
    s vs body callee ret v post hc hp.1 he hl hb,
    phase2_alloc_backing name args s vs body callee ret v post hc ⟨hp.1.1.1, hp.2⟩ he hl hb⟩

/-- A suffix allocation composes with the complete table, backing, and
Phase-4-shape continuation at its exact clock cost. -/
theorem phase2_alloc_message_tables_backing_shapes_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      name ≠ ofString n)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (fun s =>
      ((PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) ∧ TxBacking s) ∧
        PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (fun s =>
      ((PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) ∧ TxBacking s) ∧
        PtxPhase4LocalShapes s)
      (.decCall name .one (ofString "alloc") args tail) (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on (Q := fun s =>
    ((PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak) ∧ TxBacking s) ∧
      PtxPhase4LocalShapes s) h.fb_alloc
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · intro F s vs body callee ret v post hc hp he hl hb
    refine ⟨phase2_alloc_message_tables_backing_ready h buffers contents aa ak name args hm hi
      s vs body callee ret v post hc hp.1 he hl hb, ?_⟩
    apply phase2_phase4_shapes_localsOnly s _ post.clock
      (fun n hmem => ?_) hp.2
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn n hmem]
  · exact ht

/-- The branch-store cut retains the initialized gas and access-table fields,
as well as caller scalars, backing, and Phase-4 shapes. -/
def PtxMessageSuffixReady {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  PtxMessageScalarReady buffers contents names s ∧ PtxMessageTables s aa ak ∧
    TxBacking s ∧ PtxPhase4LocalShapes s ∧
    memW s (locN s "m" + 152) = aa ∧ memW s (locN s "m" + 160) = ak ∧
    memW s (locN s "m" + 40) < 2 ^ 63

/-- Stores to branch-specific fields frame all three readiness fields. -/
theorem phase2_message_suffix_store_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak off : Nat) (hoff : off + 8 ≤ 176)
    (ha : off ≠ 152) (hk : off ≠ 160) (hg : off ≠ 40) (value : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      PtxMessageScalarReady buffers contents names s → evalAt s value = some v →
      ∃ w, v = .val (.word w)) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak)
      (.store (.op .add [.var .local (ofString "m"), .const off]) value)
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, rfl⟩ := hv s v hp.1 he
  have hst' : @panMemStoresHOL 64 _ x [.word w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem := by
    simpa only [flattenHOL] using hst
  obtain ⟨hd, _, hm⟩ := panMemStoresHOL_word_spec hst'
  have ht := phase2_message_tables_backing_store buffers contents hp.1.1 hp.2.1 hp.2.2.1 hd
    (phase2_message_offset_inside hp.1.1 off hoff hx) hm
  have hf := (phase2_message_store_fields buffers contents hp.1.1 off hoff hx hst').2.2
  refine ⟨⟨ht.1, hp.1.2⟩, ht.2.1, ht.2.2, hp.2.2.2.1, ?_, ?_, ?_⟩
  · exact (hf 19 (by decide) (by omega)).trans hp.2.2.2.2.1
  · exact (hf 20 (by decide) (by omega)).trans hp.2.2.2.2.2.1
  · change memW {s with memory := mem} (locN s "m" + 40) < 2 ^ 63
    rw [hf 5 (by decide) (by omega)]; exact hp.2.2.2.2.2.2

theorem phase2_message_suffix_load_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak off : Nat) (hoff : off + 8 ≤ 176)
    (ha : off ≠ 152) (hk : off ≠ 160) (hg : off ≠ 40) (addr : ExpHOL 64) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak)
      (.store (.op .add [.var .local (ofString "m"), .const off]) (.load .one addr))
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply phase2_message_suffix_store_hoare buffers contents names aa ak off hoff ha hk hg
  intro F s v hp hv
  simp [evalAt, evalHOLExact] at hv
  split at hv
  · simp [memLoadHOLExact] at hv
    rcases hv with ⟨_, rfl⟩
    cases s.memory _ with
    | word w => exact ⟨w, rfl⟩
  · cases hv

theorem phase2_message_suffix_local_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak off : Nat) (hoff : off + 8 ≤ 176)
    (ha : off ≠ 152) (hk : off ≠ 160) (hg : off ≠ 40)
    (name : String) (hn : name ∈ names) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak)
      (.store (.op .add [.var .local (ofString "m"), .const off]) (.var .local (ofString name)))
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply phase2_message_suffix_store_hoare buffers contents names aa ak off hoff ha hk hg
  intro F s v hp hv
  obtain ⟨w, hw⟩ := hp.2 name hn
  exact ⟨w, by simpa [evalAt, evalHOLExact, hw] using hv.symm⟩

theorem phase2_message_suffix_const_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak off : Nat) (hoff : off + 8 ≤ 176)
    (ha : off ≠ 152) (hk : off ≠ 160) (hg : off ≠ 40) (w : BitVec 64) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak)
      (.store (.op .add [.var .local (ofString "m"), .const off]) (.const w))
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply phase2_message_suffix_store_hoare buffers contents names aa ak off hoff ha hk hg
  intro F s v hp hv
  exact ⟨w, by simpa [evalAt, evalHOLExact] using hv.symm⟩

/-- The concrete ordinary-call stores retain the complete readiness cut. -/
theorem phase2_message_call_stores_suffix_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (he : "empty" ∈ names) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak) phase2_message_call_stores
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  unfold phase2_message_call_stores
  apply Hoare.seq_fall (phase2_message_suffix_load_store buffers contents names aa ak 32
    (by decide) (by decide) (by decide) (by decide) _)
  apply Hoare.seq_fall (phase2_message_suffix_load_store buffers contents names aa ak 88
    (by decide) (by decide) (by decide) (by decide) _)
  apply Hoare.seq_fall (phase2_message_suffix_load_store buffers contents names aa ak 96
    (by decide) (by decide) (by decide) (by decide) _)
  apply Hoare.seq_fall (phase2_message_suffix_local_store buffers contents names aa ak 112
    (by decide) (by decide) (by decide) (by decide) "empty" he)
  apply Hoare.seq_fall (phase2_message_suffix_const_store buffers contents names aa ak 120
    (by decide) (by decide) (by decide) (by decide) 0)
  exact phase2_message_suffix_load_store buffers contents names aa ak 104
    (by decide) (by decide) (by decide) (by decide) _

/-- The concrete create stores retain the complete readiness cut. -/
theorem phase2_message_create_stores_suffix_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (hc : "ct" ∈ names) (he : "empty" ∈ names) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak) phase2_message_create_stores
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  unfold phase2_message_create_stores
  apply Hoare.seq_fall (phase2_message_suffix_local_store buffers contents names aa ak 32
    (by decide) (by decide) (by decide) (by decide) "ct" hc)
  apply Hoare.seq_fall (phase2_message_suffix_local_store buffers contents names aa ak 88
    (by decide) (by decide) (by decide) (by decide) "empty" he)
  apply Hoare.seq_fall (phase2_message_suffix_const_store buffers contents names aa ak 96
    (by decide) (by decide) (by decide) (by decide) 0)
  apply Hoare.seq_fall (phase2_message_suffix_load_store buffers contents names aa ak 112
    (by decide) (by decide) (by decide) (by decide) _)
  apply Hoare.seq_fall (phase2_message_suffix_load_store buffers contents names aa ak 120
    (by decide) (by decide) (by decide) (by decide) _)
  exact phase2_message_suffix_const_store buffers contents names aa ak 104
    (by decide) (by decide) (by decide) (by decide) 0

/-- The branch-store cut supplies the exact backing-aware continuation guard. -/
theorem phase2_message_suffix_ready {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names : List String} {aa ak : Nat} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageSuffixReady buffers contents names aa ak s) :
    (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s :=
  phase2_message_ready_backing_shapes hp.1.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2

/-- Both concrete branch-store blocks are clock-neutral. -/
theorem phase2_message_call_stores_clock {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s phase2_message_call_stores).2.clock = s.clock := by
  unfold phase2_message_call_stores
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  exact fun t => clock_store t _ _

theorem phase2_message_create_stores_clock {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s phase2_message_create_stores).2.clock = s.clock := by
  unfold phase2_message_create_stores
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  apply phase2_clock_seq (fun t => clock_store t _ _)
  exact fun t => clock_store t _ _

/-- The ordinary-call stores feed the exact backing-aware tail guard at zero cost. -/
theorem phase2_message_call_stores_suffix_bound {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (he : "empty" ∈ names)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      (.seq phase2_message_call_stores tail) b := by
  have hb : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      phase2_message_call_stores 0 := PtxP1.bound_of_clock
    (P := PtxMessageSuffixReady buffers contents names aa ak) phase2_message_call_stores_clock
  have ht' : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak) tail b :=
    fun s hc hp => ht s hc (phase2_message_suffix_ready hp)
  intro F s hcode hp
  simpa only [Nat.zero_add] using seq_bound_trans hb
    (phase2_message_call_stores_suffix_hoare buffers contents names aa ak he) ht' s hcode hp

/-- The create stores feed the exact backing-aware tail guard at zero cost. -/
theorem phase2_message_create_stores_suffix_bound {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (hc : "ct" ∈ names) (he : "empty" ∈ names)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      (.seq phase2_message_create_stores tail) b := by
  have hb : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      phase2_message_create_stores 0 := PtxP1.bound_of_clock
    (P := PtxMessageSuffixReady buffers contents names aa ak) phase2_message_create_stores_clock
  have ht' : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak) tail b :=
    fun s hc hp => ht s hc (phase2_message_suffix_ready hp)
  intro F s hcode hp
  simpa only [Nat.zero_add] using seq_bound_trans hb
    (phase2_message_create_stores_suffix_hoare buffers contents names aa ak hc he) ht' s hcode hp

/-- Successful allocation changes the heap frontier but leaves caller memory intact. -/
theorem phase2_alloc_memory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (vs : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL) (v : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F)
    (hc : s.code = InitECandidate.Solver.GuestCodeLookup.originalRuntimeCode)
    (hp : WorldOK s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    post.memory = s.memory := by
  have hl' := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "alloc")
    vs body callee ret hl
  unfold lookupCodeHOLExact at hl'
  rw [hc, InitECandidate.Solver.Wave8Contracts.M27.lookup_alloc_te] at hl'
  dsimp only at hl'
  split at hl'
  · rename_i hcond
    obtain ⟨rfl, hrest⟩ := Prod.mk.inj (Option.some.inj hl')
    obtain ⟨hlocal, _⟩ := Prod.mk.inj hrest
    rcases vs with _ | ⟨nv, _ | _⟩
    · simp at hcond
    · rcases nv with ⟨⟨n⟩⟩ | _ | _
      · have hn : (callEntryStateHOLFinite s callee).locals.lookup (ofString "n") =
            some (.val (.word n)) := by
          change callee.lookup (ofString "n") = _
          rw [← hlocal]; simp [List.zip, List.foldl]
        obtain ⟨p, hpl⟩ := hp.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
        have hr := InitECandidate.Solver.Wave8Contracts.M27.alloc_body_run
          (callEntryStateHOLFinite s callee) p n hc hpl hn v
        rw [hb] at hr
        exact congrArg (fun t => t.memory) (hr rfl).2.2.2
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
      · simp [List.zip, shapeOfHOLExact, shapeEqHOL] at hcond
    · simp at hcond
  · cases hl'

/-- Allocation frames the full suffix invariant, including initialized message fields. -/
theorem phase2_alloc_message_suffix_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hs : ∀ n ∈ names, name ≠ ofString n)
    (hn : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      name ≠ ofString n) :
    DecCallResumeOn (PtxMessageSuffixReady buffers contents names aa ak)
      (PtxMessageSuffixReady buffers contents names aa ak) name (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have ht := phase2_alloc_message_tables_backing_ready h buffers contents aa ak name args hm hi
    s vs body callee ret v post hc ⟨⟨hp.1.1, hp.2.1⟩, hp.2.2.1⟩ he hl hb
  have hmem := phase2_alloc_memory s vs body callee ret v post hc hp.1.1.1 hl hb
  have hloc : locN (setVarHOLFinite name v {post with locals := s.locals}) "m" = locN s "m" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm]
  refine ⟨⟨ht.1.1, ?_⟩, ht.1.2, ht.2, ?_, ?_, ?_, ?_⟩
  · intro n hns
    obtain ⟨w, hw⟩ := hp.1.2 n hns
    exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hs n hns] using hw⟩
  · apply phase2_phase4_shapes_localsOnly s _ post.clock (fun n hns => ?_) hp.2.2.2.1
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn n hns]
  · rw [hloc]
    simpa only [memW, setVarHOLFinite, hmem] using hp.2.2.2.2.1
  · rw [hloc]
    simpa only [memW, setVarHOLFinite, hmem] using hp.2.2.2.2.2.1
  · rw [hloc]
    simpa only [memW, setVarHOLFinite, hmem] using hp.2.2.2.2.2.2

/-- The full suffix invariant composes through allocation at the exact callee cost. -/
theorem phase2_alloc_message_suffix_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hs : ∀ n ∈ names, name ≠ ofString n)
    (hn : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      name ≠ ofString n)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      (.decCall name .one (ofString "alloc") args tail) (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := PtxMessageSuffixReady buffers contents names aa ak) h.fb_alloc
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · exact phase2_alloc_message_suffix_ready h buffers contents names aa ak name args hm hi hs hn
  · exact ht

/-- Allocation extends the suffix scalar witnesses with its returned word. -/
theorem phase2_alloc_message_suffix_word_ready (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : String) (args : List (ExpHOL 64))
    (hm : ofString name ≠ ofString "m") (hi : ofString name ≠ ofString "index")
    (hs : ∀ n ∈ names, ofString name ≠ ofString n)
    (hn : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      ofString name ≠ ofString n) :
    DecCallResumeOn (PtxMessageSuffixReady buffers contents names aa ak)
      (PtxMessageSuffixReady buffers contents (name :: names) aa ak)
      (ofString name) (ofString "alloc") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have ht := phase2_alloc_message_suffix_ready h buffers contents names aa ak
    (ofString name) args hm hi hs hn s vs body callee ret v post hc hp he hl hb
  have hrt := PtxP1.funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hrt
  obtain ⟨w, hv, _⟩ := hrt v rfl
  refine ⟨⟨ht.1.1, ?_⟩, ht.2⟩
  intro n hns
  rcases List.mem_cons.mp hns with rfl | hns
  · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hv]⟩
  · exact ht.1.2 n hns

/-- The word-producing allocation feeds a continuation using the extended locals. -/
theorem phase2_alloc_message_suffix_word_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : String) (args : List (ExpHOL 64))
    (hm : ofString name ≠ ofString "m") (hi : ofString name ≠ ofString "index")
    (hs : ∀ n ∈ names, ofString name ≠ ofString n)
    (hn : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      ofString name ≠ ofString n)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents (name :: names) aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      (.decCall (ofString name) .one (ofString "alloc") args tail) (K.alloc + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := PtxMessageSuffixReady buffers contents (name :: names) aa ak) h.fb_alloc
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · exact phase2_alloc_message_suffix_word_ready h buffers contents names aa ak name args hm hi hs hn
  · exact ht

/-- Empty-buffer allocation followed by the ordinary-call stores supplies the tail guard. -/
theorem phase2_message_empty_call_suffix_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents [] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const 0]
        (.seq phase2_message_call_stores tail)) (K.alloc + b + 1) := by
  apply phase2_alloc_message_suffix_word_bound h buffers contents [] aa ak "empty" _
    (by decide) (by decide) (by simp)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact phase2_message_call_stores_suffix_bound buffers contents ["empty"] aa ak (by simp) ht

/-- Empty allocation at any size feeds the ordinary-call branch stores. -/
theorem phase2_message_alloc_empty_call_suffix_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    (size : BitVec 64) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents [] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const size]
        (.seq phase2_message_call_stores tail)) (K.alloc + b + 1) := by
  apply phase2_alloc_message_suffix_word_bound h buffers contents [] aa ak "empty" _
    (by decide) (by decide) (by simp)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact phase2_message_call_stores_suffix_bound buffers contents ["empty"] aa ak (by simp) ht

/-- The source's eight-byte empty allocation supplies the ordinary-call store cut. -/
theorem phase2_message_empty8_call_suffix_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents [] aa ak)
      (.decCall (ofString "empty") .one (ofString "alloc") [.const 8]
        (.seq phase2_message_call_stores tail)) (K.alloc + b + 1) :=
  phase2_message_alloc_empty_call_suffix_bound h buffers contents aa ak 8 ht

/-- The create branch's address allocation supplies the scalar needed by its stores.
The address-computation call is handled by its own preservation cut. -/
theorem phase2_message_ct_alloc_suffix_bound (h : PtxCallees) {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (PtxMessageSuffixReady buffers contents ["ct", "empty"] aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents ["empty"] aa ak)
      (.decCall (ofString "ct") .one (ofString "alloc") [.const 24] tail)
      (K.alloc + b + 1) := by
  exact phase2_alloc_message_suffix_word_bound h buffers contents ["empty"] aa ak "ct" _
    (by decide) (by decide) (by intro n hn; simp only [List.mem_singleton] at hn; subst n; decide)
    (by intro n hn; simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) ht

/-- Allocating the create address and executing its stores discharges the suffix guard. -/
theorem phase2_message_ct_alloc_create_stores_suffix_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (aa ak : Nat)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents ["empty"] aa ak)
      (.decCall (ofString "ct") .one (ofString "alloc") [.const 24]
        (.seq phase2_message_create_stores tail)) (K.alloc + b + 1) := by
  apply phase2_message_ct_alloc_suffix_bound h buffers contents aa ak
  exact phase2_message_create_stores_suffix_bound buffers contents ["ct", "empty"] aa ak
    (by simp) (by simp) ht

/-- Readiness before the final two access-table pointer stores. -/
def PtxMessageTableStoreReady {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  PtxMessageScalarReady buffers contents names s ∧ PtxMessageTables s aa ak ∧
    TxBacking s ∧ PtxPhase4LocalShapes s ∧
    memW s (locN s "m" + 40) < 2 ^ 63 ∧ locN s "aa" = aa ∧ locN s "ak" = ak

/-- A final table-pointer store preserves the pre-initialization cut and records its value. -/
theorem phase2_message_table_pointer_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak off : Nat) (hoff : off + 8 ≤ 176)
    (hg : off ≠ 40) (name : String) (hn : name ∈ names) :
    Hoare (PtxMessageTableStoreReady buffers contents names aa ak)
      (.store (.op .add [.var .local (ofString "m"), .const off]) (.var .local (ofString name)))
      (fun r s => r = none → PtxMessageTableStoreReady buffers contents names aa ak s ∧
        memW s (locN s "m" + off) = locN s name) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, hw⟩ := hp.1.2 name hn
  have hv : v = .val (.word w) := by simpa [evalAt, evalHOLExact, hw] using he.symm
  subst v
  have hst' : @panMemStoresHOL 64 _ x [.word w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem := by
    simpa only [flattenHOL] using hst
  obtain ⟨hd, _, hm⟩ := panMemStoresHOL_word_spec hst'
  have ht := phase2_message_tables_backing_store buffers contents hp.1.1 hp.2.1 hp.2.2.1 hd
    (phase2_message_offset_inside hp.1.1 off hoff hx) hm
  have hf := phase2_message_store_fields buffers contents hp.1.1 off hoff hx hst'
  refine ⟨⟨⟨ht.1, hp.1.2⟩, ht.2.1, ht.2.2, hp.2.2.2.1, ?_, hp.2.2.2.2.2⟩, ?_⟩
  · change memW {s with memory := mem} (locN s "m" + 40) < 2 ^ 63
    rw [hf.2.2 5 (by decide) (by omega)]
    exact hp.2.2.2.2.1
  · simpa [locN, hw] using hf.2.1

/-- Writing the second table pointer completes the suffix invariant. -/
theorem phase2_message_ak_store_suffix {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (hn : "ak" ∈ names) :
    Hoare (fun s => PtxMessageTableStoreReady buffers contents names aa ak s ∧
        memW s (locN s "m" + 152) = aa)
      (.store (.op .add [.var .local (ofString "m"), .const 160]) (.var .local (ofString "ak")))
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx he hst
  obtain ⟨w, hw⟩ := hp.1.1.2 "ak" hn
  have hv : v = .val (.word w) := by simpa [evalAt, evalHOLExact, hw] using he.symm
  subst v
  have hst' : @panMemStoresHOL 64 _ x [.word w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem := by
    simpa only [flattenHOL] using hst
  obtain ⟨hd, _, hm⟩ := panMemStoresHOL_word_spec hst'
  have ht := phase2_message_tables_backing_store buffers contents hp.1.1.1 hp.1.2.1 hp.1.2.2.1 hd
    (phase2_message_offset_inside hp.1.1.1 160 (by decide) hx) hm
  have hf := phase2_message_store_fields buffers contents hp.1.1.1 160 (by decide) hx hst'
  refine ⟨⟨ht.1, hp.1.1.2⟩, ht.2.1, ht.2.2, hp.1.2.2.2.1, ?_, ?_, ?_⟩
  · exact (hf.2.2 19 (by decide) (by decide)).trans hp.2
  · have hw' : w.toNat = ak := by simpa [locN, hw] using hp.1.2.2.2.2.2.2
    exact hf.2.1.trans hw'
  · change memW {s with memory := mem} (locN s "m" + 40) < 2 ^ 63
    rw [hf.2.2 5 (by decide) (by decide)]
    exact hp.1.2.2.2.2.1

/-- The concrete final pointer stores establish readiness from uninitialized fields. -/
theorem phase2_message_table_stores_suffix_hoare {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (ha : "aa" ∈ names) (hk : "ak" ∈ names) :
    Hoare (PtxMessageTableStoreReady buffers contents names aa ak)
      (.seq
        (.store (.op .add [.var .local (ofString "m"), .const 152]) (.var .local (ofString "aa")))
        (.store (.op .add [.var .local (ofString "m"), .const 160]) (.var .local (ofString "ak"))))
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  apply Hoare.seq_fall (R := fun s => PtxMessageTableStoreReady buffers contents names aa ak s ∧
    memW s (locN s "m" + 152) = aa)
  · refine ⟨fun s hc hp ht hr => ?_⟩
    have hf := (phase2_message_table_pointer_store buffers contents names aa ak 152
      (by decide) (by decide) "aa" ha).run s hc hp ht hr
    exact ⟨hf.1, hf.2.trans hf.1.2.2.2.2.2.1⟩
  · exact phase2_message_ak_store_suffix buffers contents names aa ak hk

/-- The two final table-pointer stores initialize the suffix without consuming clock. -/
theorem phase2_message_table_stores_suffix_bound {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (ha : "aa" ∈ names) (hk : "ak" ∈ names)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageTableStoreReady buffers contents names aa ak)
      (.seq (.seq
        (.store (.op .add [.var .local (ofString "m"), .const 152]) (.var .local (ofString "aa")))
        (.store (.op .add [.var .local (ofString "m"), .const 160]) (.var .local (ofString "ak")))) tail) b := by
  have hb : TerminatingProgBoundedOn (PtxMessageTableStoreReady buffers contents names aa ak)
      (.seq
        (.store (.op .add [.var .local (ofString "m"), .const 152]) (.var .local (ofString "aa")))
        (.store (.op .add [.var .local (ofString "m"), .const 160]) (.var .local (ofString "ak")))) 0 :=
    PtxP1.bound_of_clock (P := PtxMessageTableStoreReady buffers contents names aa ak)
      (fun s => phase2_clock_seq (fun t => clock_store t _ _) (fun t => clock_store t _ _) s)
  intro F s hc hp
  simpa only [Nat.zero_add] using seq_bound_trans hb
    (phase2_message_table_stores_suffix_hoare buffers contents names aa ak ha hk) ht s hc hp

/-- Scalar witnesses can be restricted before passing to a suffix continuation. -/
theorem phase2_message_suffix_restrict_names {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names names' : List String} {aa ak : Nat} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageSuffixReady buffers contents names aa ak s)
    (hn : ∀ n ∈ names', n ∈ names) :
    PtxMessageSuffixReady buffers contents names' aa ak s :=
  ⟨⟨hp.1.1, fun n hm => hp.1.2 n (hn n hm)⟩, hp.2⟩

/-- Pointer initialization followed by the source-sized empty allocation and
ordinary-call stores supplies the backing-aware Phase-4 continuation. -/
theorem phase2_message_table_init_call_suffix_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (ha : "aa" ∈ names) (hk : "ak" ∈ names)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s) tail b) :
    TerminatingProgBoundedOn (PtxMessageTableStoreReady buffers contents names aa ak)
      (.seq (.seq
        (.store (.op .add [.var .local (ofString "m"), .const 152]) (.var .local (ofString "aa")))
        (.store (.op .add [.var .local (ofString "m"), .const 160]) (.var .local (ofString "ak"))))
        (.decCall (ofString "empty") .one (ofString "alloc") [.const 8]
          (.seq phase2_message_call_stores tail))) (K.alloc + b + 1) := by
  apply phase2_message_table_stores_suffix_bound buffers contents names aa ak ha hk
  intro F s hc hp
  exact phase2_message_empty8_call_suffix_bound h buffers contents aa ak ht s hc
    (phase2_message_suffix_restrict_names hp (by simp))

/-- A framed message interval retains every initialized field across a call. -/
theorem phase2_message_unhit_fields {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {s post : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageStoreReady buffers contents s)
    (hu : IvlUnhit s post (locN s "m", 176)) :
    ∀ k, k < 22 → memW post (locN s "m" + 8 * k) = memW s (locN s "m" + 8 * k) := by
  intro k hk
  apply R16Shards.memW_eq_of_ivlUnhit hu
  · have hm := hp.2.2.2.2.1.1
    simp [Nat.add_mod, hm]
  · have hi := hp.2.2.2.1.2
    have hh := hp.1.1.2.2.1
    have hlim : heapLimit < 2 ^ 64 := by decide
    dsimp at hi ⊢
    omega
  · constructor <;> dsimp <;> omega

/-- Reassemble the complete suffix after a call that frames the message interval.
The structural, backing, and caller-local obligations are kept separate from
the three initialized message-field obligations. -/
theorem phase2_message_suffix_of_unhit {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names names' : List String} {aa ak : Nat}
    {s post : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageSuffixReady buffers contents names aa ak s)
    (hm : locN post "m" = locN s "m")
    (hu : R13Shards.IvlUnhit s post (locN s "m", 176))
    (hs : PtxMessageScalarReady buffers contents names' post)
    (ht : PtxMessageTables post aa ak)
    (hb : TxBacking post) (hl : PtxPhase4LocalShapes post) :
    PtxMessageSuffixReady buffers contents names' aa ak post := by
  have hf := phase2_message_unhit_fields hp.1.1 hu
  refine ⟨hs, ht, hb, hl, ?_, ?_, ?_⟩
  · rw [hm, show 152 = 8 * 19 from rfl, hf 19 (by decide)]
    exact hp.2.2.2.2.1
  · rw [hm, show 160 = 8 * 20 from rfl, hf 20 (by decide)]
    exact hp.2.2.2.2.2.1
  · rw [hm, show 40 = 8 * 5 from rfl, hf 5 (by decide)]
    exact hp.2.2.2.2.2.2

/-- Before pointer initialization, only the gas field needs memory transport;
the access-table pointers are retained as caller-local equalities. -/
theorem phase2_message_table_store_ready_of_unhit {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names names' : List String} {aa ak : Nat}
    {s post : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageTableStoreReady buffers contents names aa ak s)
    (hm : locN post "m" = locN s "m")
    (ha : locN post "aa" = locN s "aa") (hk : locN post "ak" = locN s "ak")
    (hu : R13Shards.IvlUnhit s post (locN s "m", 176))
    (hs : PtxMessageScalarReady buffers contents names' post)
    (ht : PtxMessageTables post aa ak)
    (hb : TxBacking post) (hl : PtxPhase4LocalShapes post) :
    PtxMessageTableStoreReady buffers contents names' aa ak post := by
  refine ⟨hs, ht, hb, hl, ?_, ha.trans hp.2.2.2.2.2.1, hk.trans hp.2.2.2.2.2.2⟩
  rw [hm, show 40 = 8 * 5 from rfl, phase2_message_unhit_fields hp.1.1 hu 5 (by decide)]
  exact hp.2.2.2.2.1

/-- The create-branch account lookup retains the transaction environment. -/
theorem phase2_get_account_txEnv (h : PtxCallees) (name : MlS) (args : List (ExpHOL 64))
    (hi : name ≠ ofString "index") :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s) TxEnv name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := PtxP1.funSpec_at_lookup h.wk_get_account s hc vs body callee ret hl
    (PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  have hbo : globN post "bo" = globN s "bo" := by
    have hg := hs.2.2.1 (ofString "bo") (by decide)
    change s.globals.lookup (ofString "bo") = post.globals.lookup (ofString "bo") at hg
    simp only [globN, hg]
  have hj : globN post "journal_cap" = globN s "journal_cap" := by
    have hg := hs.2.2.1 (ofString "journal_cap") (by decide)
    change s.globals.lookup (ofString "journal_cap") = post.globals.lookup (ofString "journal_cap") at hg
    simp only [globN, hg]
  have hk : ∀ k ∈ ([24, 32, 40, 72, 80] : List Nat),
      memW post (globN s "bo" + k) = memW s (globN s "bo" + k) := by
    intro k hk
    apply hs.2.2.2.1 ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
      (by simp) hp.2.bo_nz k
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp
    · intro i hi
      change i ∈ [("keccak_pad", 136, 136), ("keccak_st", 200, 200),
        ("mpt_nib_scratch", 64, 64)].map
          (fun e => bufferRegion s (e.1, e.2.2)) at hi
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
      have hspec : PtxP1.ScratchSpec [("keccak_pad", 136, 136),
          ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)] := by
        unfold PtxP1.ScratchSpec; decide
      obtain ⟨hgb, hnu, hpos, hle⟩ := hspec e he
      obtain ⟨S, hW⟩ := hp.1.2
      obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hW
      have hd := bufferRegion_disj_le hw (e.1, e.2.1) hgb hnu e.2.2 hle
        (globN s "bo", 88) (PtxP1.bo_mem_typed hp.2.bo_nz)
      have h8 := (bo_words hw.2.2.1 hp.2.bo_nz).2.1
      apply not_cellHits_of_disj (i := (globN s "bo", 88))
      · change (globN s "bo" + k) % 8 = 0
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [Nat.add_mod, h8]
      · exact PtxP1.bufferRegion_zero_aligned s e.1 e.2.2 (by omega)
      · change globN s "bo" ≤ globN s "bo" + k ∧ globN s "bo" + k + 8 ≤ globN s "bo" + 88
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
      · exact disj_symm hd
  have hi' : locN (setVarHOLFinite name v {post with locals := s.locals}) "index" =
      locN s "index" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change globN post "bo" ≠ 0; rw [hbo]; exact hp.2.bo_nz
  · change memW post (globN post "bo" + 24) ≠ 0; rw [hbo, hk 24 (by simp)]; exact hp.2.bo24
  · change memW post (globN post "bo" + 32) ≠ 0; rw [hbo, hk 32 (by simp)]; exact hp.2.bo32
  · change memW post (globN post "bo" + 40) ≠ 0; rw [hbo, hk 40 (by simp)]; exact hp.2.bo40
  · change memW post (globN post "bo" + 72) ≠ 0; rw [hbo, hk 72 (by simp)]; exact hp.2.bo72
  · change locN (setVarHOLFinite name v {post with locals := s.locals}) "index" <
      memW post (globN post "bo" + 80)
    rw [hi', hbo, hk 80 (by simp)]; exact hp.2.idx_lt
  · change globN post "journal_cap" ≠ 0; rw [hj]; exact hp.2.jcap_nz

/-- Account lookup frames all initialized message words, despite scratch writes. -/
theorem phase2_get_account_message_fields (h : PtxCallees) {ι F : Type} [Nonempty ι]
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64)
    (hc : s.code = GuestCodeLookup.originalRuntimeCode)
    (hp : PtxMessageStoreReady buffers contents s)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∀ k, k < 22 → memW post (locN s "m" + 8 * k) = memW s (locN s "m" + 8 * k) := by
  have hh := PtxP1.funSpec_at_lookup h.wk_get_account s hc vs body callee ret hl
    (PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨_, S, Nd, hw, _, hd⟩ := hp.2.2.2.2.2 i
  let gs : List (String × Nat × Nat) :=
    [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)]
  have hspec : PtxP1.ScratchSpec gs := by unfold PtxP1.ScratchSpec gs; decide
  have hsafe : IvlsDisj (gs.map (fun e => bufferRegion s (e.1, e.2.2)))
      (worldTypedIvls s S Nd) := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hgb, hnu, _, hle⟩ := hspec e he
    exact bufferRegion_disj_le hw (e.1, e.2.1) hgb hnu e.2.2 hle y hy
  obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := hs.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) hsafe
  intro k hk
  apply phase2_world_frame_heap_disjoint s post (worldOwned s S Nd)
    (gs.map (fun e => bufferRegion s (e.1, e.2.2))) (locN s "m", 176)
    (locN s "m" + 8 * k) hp.1.1.2 hp.2.2.2.1
  · constructor <;> dsimp <;> omega
  · have hm := hp.2.2.2.2.1.1
    simp [Nat.add_mod, hm]
  · exact hf
  · exact hd _ (by simp)
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact PtxP1.heap_ivl_disj_bufferRegion_le (hd _ (by simp))
      (e.1, e.2.1) (hspec e he).1 e.2.2 (hspec e he).2.2.2
  · exact worldOwned_zero_aligned hw
  · intro x hx hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact PtxP1.bufferRegion_zero_aligned s e.1 e.2.2 (by have := (hspec e he).2.2.1; omega) hz

/-- Account lookup preserves a saved heap buffer and its separating message witness. -/
theorem phase2_get_account_live_buffer (h : PtxCallees) {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (ret : ShapeHOL) (v : ValueHOL 64) (S Nd : List Nat)
    (buffer : Ivl) (contents : Nat → BitVec 64)
    (hc : s.code = GuestCodeLookup.originalRuntimeCode) (ha : ArenaReady s)
    (hw : WorldTypedWith s S Nd) (hp : PtxLiveBufferAt s S Nd buffer contents)
    (hm : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hd : IvlsDisj [(locN s "m", 176)] (worldOwned s S Nd))
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "get_account") vs = some (body, callee, ret))
    (hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), post)) :
    ∃ S' Nd', WorldTypedWith post S' Nd' ∧ PtxLiveBufferAt post S' Nd' buffer contents ∧
      IvlsDisj [(locN s "m", 176)] (worldOwned post S' Nd') := by
  have hworld : WorldOK s := ⟨ha, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw⟩⟩
  have hh := PtxP1.funSpec_at_lookup h.wk_get_account s hc vs body callee ret hl
    (PtxP1.worldOK_callEntry hworld callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  let gs : List (String × Nat × Nat) :=
    [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)]
  have hspec : PtxP1.ScratchSpec gs := by unfold PtxP1.ScratchSpec gs; decide
  have hsafe : IvlsDisj (gs.map (fun e => bufferRegion s (e.1, e.2.2)))
      (worldTypedIvls s S Nd) := by
    intro x hx y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hgb, hnu, _, hle⟩ := hspec e he
    exact bufferRegion_disj_le hw (e.1, e.2.1) hgb hnu e.2.2 hle y hy
  obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := hs.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) hsafe
  refine ⟨S', Nd', hw', ?_, phase2_packed_owned_growth s post _ _ _ hm hg hd⟩
  apply phase2_live_buffer_step s post S Nd S' Nd' buffer contents
    (gs.map (fun (e : String × Nat × Nat) => bufferRegion s (e.1, e.2.2))) hp ha.2 hw hs.2.1 hg hf
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact PtxP1.heap_ivl_disj_bufferRegion_le (hp.2.1 _ (by simp))
      (e.1, e.2.1) (hspec e he).1 e.2.2 (hspec e he).2.2.2
  · intro x hx hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact PtxP1.bufferRegion_zero_aligned s e.1 e.2.2 (by have := (hspec e he).2.2.1; omega) hz

/-- Restoring caller locals after lookup retains the entire saved-buffer family. -/
theorem phase2_get_account_message_store_ready (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index") :
    DecCallResumeOn (PtxMessageStoreReady buffers contents)
      (PtxMessageStoreReady buffers contents) name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hh := PtxP1.funSpec_at_lookup h.wk_get_account s hc vs body callee ret hl
    (PtxP1.worldOK_callEntry hp.1 callee) (by rw [hb]; simp)
  rw [hb] at hh
  have hs := hh (Or.inl ⟨v, rfl⟩)
  let out := setVarHOLFinite name v {post with locals := s.locals}
  have hm' : locN out "m" = locN s "m" := by
    simp [out, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm]
  have hworld : WorldOK out := by
    obtain ⟨S, hW⟩ := hp.1.2
    obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hW
    let gs : List (String × Nat × Nat) :=
      [("keccak_pad", 136, 136), ("keccak_st", 200, 200), ("mpt_nib_scratch", 64, 64)]
    have hspec : PtxP1.ScratchSpec gs := by unfold PtxP1.ScratchSpec gs; decide
    have hsafe : IvlsDisj (gs.map (fun e => bufferRegion s (e.1, e.2.2)))
        (worldTypedIvls s S Nd) := by
      intro x hx y hy
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact bufferRegion_disj_le hw (e.1, e.2.1) (hspec e he).1
        (hspec e he).2.1 e.2.2 (hspec e he).2.2.2 y hy
    obtain ⟨S', Nd', _, hw', _⟩ := hs.2.2.2.2 S Nd
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) hsafe
    exact localsFree_worldOK post _ post.clock
      ⟨hs.1, S', (worldTyped_iff_with post S').mpr ⟨Nd', hw'⟩⟩
  refine ⟨hworld, phase2_get_account_txEnv h name args hi
    s vs body callee ret v post hc ⟨hp.1, hp.2.1⟩ he hl hb, ?_, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hp.2.2.1
    exact ⟨w, by simpa [out, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm] using hw⟩
  · change Inside (locN out "m", 176) InitE.sourceBase (globN post "heap_ptr")
    rw [hm']
    exact ⟨hp.2.2.2.1.1, hp.2.2.2.1.2.trans hs.2.1⟩
  · change WordsOK out (locN out "m", 176)
    rw [hm']
    exact wordsOK_transfer hp.1.1.1 hworld.1.1 hp.2.2.2.2.1
  · intro i
    obtain ⟨hd, S, Nd, hw, hpbuf, hsep⟩ := hp.2.2.2.2.2 i
    obtain ⟨S', Nd', hw', hbuf', hsep'⟩ := phase2_get_account_live_buffer h
      s post vs body callee ret v S Nd (buffers i) (contents i) hc hp.1.1 hw hpbuf
      hp.2.2.2.1 hsep hl hb
    refine ⟨?_, S', Nd', ?_, hbuf', ?_⟩
    · rw [hm']; exact hd
    · exact (worldTypedWith_with_locals post _ post.clock S' Nd').mpr hw'
    · change IvlsDisj [(locN out "m", 176)] (worldOwned post S' Nd')
      rw [hm']; exact hsep'

/-- Account lookup retains the caller scalar witnesses used by the message suffix. -/
theorem phase2_get_account_message_scalar_ready (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ names, name ≠ ofString n) :
    DecCallResumeOn (PtxMessageScalarReady buffers contents names)
      (PtxMessageScalarReady buffers contents names) name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp he hl hb
  refine ⟨phase2_get_account_message_store_ready h buffers contents name args hm hi
    s vs body callee ret v post hc hp.1 he hl hb, ?_⟩
  intro n hmem
  obtain ⟨w, hw⟩ := hp.2 n hmem
  exact ⟨w, by simpa [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hn n hmem] using hw⟩

/-- Transport nested backing through a call that frames the fixed world objects. -/
theorem phase2_backing_of_fixed_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd) (hb : TxBacking s)
    (hg : globN post "bo" = globN s "bo")
    (hu : ∀ i ∈ fixedObjects s, IvlUnhit s post i) : TxBacking post := by
  have hf : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → Allocated s i ∧ WordsOK s i := by
    intro i hi hn
    rcases hw.2.2.1.1 i hi with hz | hh
    · exact (hn hz).elim
    · exact hh
  have hbo : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hl : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
  apply PtxP34.txBacking_of_unhit_headers hb hg
  · exact (hf _ hbo (by simp)).2.1
  · exact (ivl_allocated_bound ha.2 (hf _ hbo (by simp)).1).2
  · exact hu _ hbo
  · intro k hk; exact (hf _ (hl k hk) (by simp)).2.1
  · intro k hk; exact (ivl_allocated_bound ha.2 (hf _ (hl k hk) (by simp)).1).2
  · intro k hk; exact hu _ (hl k hk)

/-- A narrow concrete effect frames any aligned interval disjoint from its writes. -/
theorem phase2_worldEff_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {R : List Ivl} {B : List (String × Nat)} {gw : List String} {i : Ivl}
    (h : R16Shards.WorldEff s post R B gw)
    (hi : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hR : ∀ j ∈ R, Disj i j)
    (hB : ∀ b ∈ B, Disj i (bufferRegion s b))
    (hgap : Disj i (freeGap s)) (hheap : Disj i (heapFree s)) :
    IvlUnhit s post i := by
  intro a ha hh
  by_contra he
  have hh' : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hh
    omega
  have hne : post.memory a ≠ s.memory a := he
  have exclude : ∀ j, Disj i j → ¬ Fast_C08WkShard03.CellHitsPos a.toNat j := by
    intro j hd hc
    unfold Disj at hd
    simp only [Fast_C08WkShard03.CellHitsPos, CellHits] at hc
    rcases hd with hz | hz | hl | hr <;> dsimp at * <;> omega
  rcases h.cell_frame _ hne with ⟨j, hj, hc⟩ | ⟨b, hb, hc⟩ | hc | hc
  · exact exclude j (hR j hj) hc
  · exact exclude _ (hB b hb) hc
  · exact exclude _ hgap hc
  · exact exclude _ hheap hc

/-- Existing allocated intervals avoid both allocation gaps in a concrete effect. -/
theorem phase2_worldEff_allocated_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {R : List Ivl} {B : List (String × Nat)} {gw : List String} {i : Ivl}
    (h : R16Shards.WorldEff s post R B gw) (hs : ArenaReady s)
    (hi : i.1 % 8 = 0 ∧ i.2 % 8 = 0) (ha : Allocated s i)
    (hR : ∀ j ∈ R, Disj i j)
    (hB : ∀ b ∈ B, Disj i (bufferRegion s b)) : IvlUnhit s post i := by
  apply phase2_worldEff_unhit h hi hR hB
  · unfold Allocated Inside at ha
    unfold Disj freeGap
    rcases ha with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl (by
        have horder := hs.2
        rcases horder with ⟨_, hp, hf, hsc, _⟩
        dsimp at *
        have sep : heapLimit ≤ InitE.scratchStart := by decide
        omega)))
    · exact Or.inr (Or.inr (Or.inr (by
        have horder := hs.2
        rcases horder with ⟨_, hp, hf, hsc, _⟩
        dsimp at *
        omega)))
  · unfold Allocated Inside at ha
    unfold Disj heapFree
    rcases ha with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
    · exact Or.inr (Or.inr (Or.inl hhi))
    · exact Or.inr (Or.inr (Or.inr (by
        have horder := hs.2
        rcases horder with ⟨_, hp, hf, hsc, _⟩
        dsimp at *
        have sep : heapLimit ≤ InitE.scratchStart := by decide
        omega)))

/-- Backing needs only three headers framed, allowing writes to fixed scratch buffers. -/
theorem phase2_backing_of_header_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd) (hb : R16Shards.TxBacking s)
    (hg : globN post "bo" = globN s "bo")
    (hbo : IvlUnhit s post (globN s "bo", 88))
    (hl : ∀ k ∈ ([40, 72] : List Nat),
      IvlUnhit s post (memW s (globN s "bo" + k), 24)) : R16Shards.TxBacking post := by
  have hf : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → Allocated s i ∧ WordsOK s i := by
    intro i hi hn
    exact (hw.2.2.1.1 i hi).resolve_left hn
  have hbo_mem : (globN s "bo", 88) ∈ fixedObjects s := by
    simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  have hl_mem : ∀ k ∈ ([40, 72] : List Nat),
      (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
  apply PtxP34.txBacking_of_unhit_headers hb hg
  · exact (hf _ hbo_mem (by simp)).2.1
  · exact (ivl_allocated_bound ha.2 (hf _ hbo_mem (by simp)).1).2
  · exact hbo
  · intro k hk; exact (hf _ (hl_mem k hk) (by simp)).2.1
  · intro k hk; exact (ivl_allocated_bound ha.2 (hf _ (hl_mem k hk) (by simp)).1).2
  · exact hl

/-- Concrete world-state account decoding frames existing objects outside its scratch buffers. -/
theorem phase2_ws_get_account_optional_unhit {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) {i : Ivl} (hi : i.1 % 8 = 0 ∧ i.2 % 8 = 0)
    (hal : Allocated s i)
    (hd : ∀ b ∈ R16Shards.wsBufs, Disj i (bufferRegion s b))
    (hnt : (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    IvlUnhit s (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2 i := by
  have he := R16Shards.worldEff_ws_get_account_optional s s ha.2
    (R16Shards.WorldEff.refl s [] R16Shards.wsBufs R16Shards.wsGw ha hc) hnt hr
  exact phase2_worldEff_allocated_unhit he ha hi hal (by simp) hd

/-- Fixed-object separation puts both nested list headers outside world-state scratch buffers. -/
theorem phase2_nested_header_disj_wsBufs {F : Type}
    {s : PanSemStateFiniteExact 64 F} (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    {k : Nat} (hk : k ∈ ([40, 72] : List Nat)) :
    ∀ b ∈ R16Shards.wsBufs,
      Disj (memW s (globN s "bo" + k), 24) (bufferRegion s b) := by
  have hm : (memW s (globN s "bo" + k), 24) ∈ blockOutObjects s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [blockOutObjects, he.bo_nz, he.bo40]
    · simp [blockOutObjects, he.bo_nz, he.bo72]
  obtain ⟨_, _, hd, _, _⟩ := fixedObjects_disj_parts hw.2.2.1
  intro b hb
  have hbg : b ∈ globalBuffers := by
    simp only [R16Shards.wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> decide
  have hg := hd (bufferRegion s b) (List.mem_map.2 ⟨b, hbg, rfl⟩)
    _ (List.mem_append_left _ (List.mem_append_right _ hm))
  exact disj_symm hg

/-- The concrete world-state lookup preserves both nested backing headers. -/
theorem phase2_ws_get_account_optional_nested_unhit {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (hnt : (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    ∀ k ∈ ([40, 72] : List Nat), IvlUnhit s
      (evaluateHOLFiniteState s
        (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
      (memW s (globN s "bo" + k), 24) := by
  intro k hk
  have hm : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
  have hf := (hw.2.2.1.1 _ hm).resolve_left (by simp)
  exact phase2_ws_get_account_optional_unhit s hc ha
    ⟨hf.2.1, by norm_num⟩ hf.1 (phase2_nested_header_disj_wsBufs he hw hk) hnt hr

/-- Table insertion frames allocated headers separated from its old footprint. -/
theorem phase2_htabExit_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (hx : HtabExit s post) {i : Ivl}
    (hi : i.1 % 8 = 0 ∧ i.2 % 8 = 0) (hal : Allocated s i)
    (ht : ∀ j ∈ htabFootprint s (locN s "t"), j.1 % 8 = 0)
    (hd : ∀ j ∈ htabFootprint s (locN s "t"), Disj i j) :
    IvlUnhit s post i := by
  intro a ha hh
  have hin : i.1 ≤ a.toNat ∧ a.toNat + 8 ≤ i.1 + i.2 := by
    unfold CellHits at hh
    omega
  apply hx.2.2.2.2.2.2.1 a
  · intro j hj
    have hja := ht j hj
    have hdis := hd j hj
    unfold Disj at hdis
    unfold CellHits
    rcases hdis with hz | hz | hl | hr <;> omega
  · have hdis : Disj i (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") := by
      rcases hal with h | h
      · exact Or.inr (Or.inr (Or.inl h.2))
      · apply Or.inr; apply Or.inr; apply Or.inr
        have hsp := hs.2
        have hpp := hx.1.2
        have hmono := hx.2.2.2.2.1
        have hsep : heapLimit ≤ InitE.scratchStart := by decide
        unfold Inside at h
        rcases hsp with ⟨_, hp, hf, hsc, _⟩
        rcases hpp with ⟨_, hp', hf', hsc', _⟩
        dsimp at *
        omega
    have hhp8 := hs.2.2.2.2.2.2.1
    unfold Disj at hdis
    unfold CellHits
    rcases hdis with hz | hz | hl | hr <;> dsimp at * <;> omega

/-- An insertion cannot modify the footprint of a different jointly typed table. -/
theorem phase2_htabExit_other_table_unhit {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S) (hx : HtabExit s post)
    {u : Nat} (hu : u ∈ S) (hne : u ≠ locN s "t")
    {i : Ivl} (hi : i ∈ htabFootprint s u) : IvlUnhit s post i := by
  have hui := (hw.1.2.1 u hu).1.1 i hi
  apply phase2_htabExit_unhit hs hx ⟨hui.2.1, hui.2.2.1⟩
    ((hw.1.2.1 u hu).2 i hi).1
  · intro j hj
    exact ((hw.1.2.1 _ ht).1.1 j hj).2.1
  · intro j hj
    exact hw.1.2.2.1 u hu (locN s "t") ht hne i hi j hj

/-- Warming a different table preserves every header word of a private table. -/
theorem phase2_htabExit_other_table_header {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S) (hx : HtabExit s post)
    {u : Nat} (hu : u ∈ S) (hne : u ≠ locN s "t")
    (k : Nat) (hk : k < 11) : hdr post u k = hdr s u k := by
  have hi : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
  have hf := (hw.1.2.1 u hu).1.1 (u, 88) hi
  have hb := (ivl_allocated_bound hs.2 ((hw.1.2.1 u hu).2 (u, 88) hi).1).2
  have he := phase2_htabExit_other_table_unhit hs hw ht hx hu hne hi
  unfold hdr
  apply memW_eq_of_ivlUnhit he
  · have ha := hf.2.1
    omega
  · exact hb
  · constructor <;> omega

/-- The transaction warming table is distinct from both private message tables. -/
theorem phase2_message_tables_ne_ts8 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (ht : PtxMessageTables s aa ak) (hts : globN s "ts" ≠ 0)
    (hn : memW s (globN s "ts" + 8) ≠ 0) :
    aa ≠ memW s (globN s "ts" + 8) ∧ ak ≠ memW s (globN s "ts" + 8) := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  have hm := R16WkAcctWs.mem_worldRoleSlots_recRole s "ts" 8 "ts+8" hts hn
    (by simp [recRoles, hts])
  exact ⟨Ne.symm (haf _ (List.mem_append_left _ hm)),
    Ne.symm (hkf _ (List.mem_append_left _ hm))⟩

/-- A warming insertion preserves the key lengths of both message access tables. -/
theorem phase2_htabExit_message_table_headers {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (hs : ArenaReady s) (hm : PtxMessageTables s aa ak)
    (hts : globN s "ts" ≠ 0) (hn : memW s (globN s "ts" + 8) ≠ 0)
    (ht : locN s "t" = memW s (globN s "ts" + 8))
    (hx : HtabExit s post) : hdr post aa 0 = 20 ∧ hdr post ak 0 = 52 := by
  have hne := phase2_message_tables_ne_ts8 hm hts hn
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := hm
  have hmem : locN s "t" ∈ S := by
    rw [ht]
    exact (hw.1.2.2.2.2.2.1 8 (by simp [tsTableSlots]) hts).resolve_left hn
  constructor
  · exact (phase2_htabExit_other_table_header hs hw hmem hx ha
      (by rw [ht]; exact hne.1) 0 (by decide)).trans hal
  · exact (phase2_htabExit_other_table_header hs hw hmem hx hk
      (by rw [ht]; exact hne.2) 0 (by decide)).trans hkl

/-- World table typing discharges the footprint separation for fixed headers. -/
theorem phase2_htabExit_fixed_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (ht : locN s "t" ∈ S) (hx : HtabExit s post)
    {i : Ivl} (him : i ∈ fixedObjects s) (hin : i.2 ≠ 0)
    (hi8 : i.2 % 8 = 0) : IvlUnhit s post i := by
  have hf := (hw.2.2.1.1 i him).resolve_left hin
  have htab := hw.1.2.1 _ ht
  exact phase2_htabExit_unhit hs hx ⟨hf.2.1, hi8⟩ hf.1
    (fun j hj => (htab.1.1 j hj).2.1)
    (fun j hj => disj_symm ((htab.2 j hj).2 i him))

/-- Inserting into an existing world table preserves the transaction's nested backing. -/
theorem phase2_htabExit_backing {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) (he : TxEnv s) {S Nd : List Nat}
    (hw : WorldTypedWith s S Nd) (ht : locN s "t" ∈ S)
    (hb : R16Shards.TxBacking s) (hx : HtabExit s post) : R16Shards.TxBacking post := by
  apply phase2_backing_of_header_unhit hs he hw hb
  · have hg := hx.2.2.2.2.2.2.2 (ofString "bo") (by decide)
    simp only [globN, ← hg]
  · apply phase2_htabExit_fixed_unhit hs hw ht hx
    · simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    · simp
    · norm_num
  · intro k hk
    apply phase2_htabExit_fixed_unhit hs hw ht hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
      · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
    · simp
    · norm_num

/-- Table calls preserve backing even though callee locals do not retain the transaction index. -/
theorem phase2_htabExit_callEntry_backing {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hs : ArenaReady s) (he : TxEnv s) {S Nd : List Nat}
    (hw : WorldTypedWith s S Nd)
    (ht : locN (callEntryStateHOLFinite s callee) "t" ∈ S)
    (hb : R16Shards.TxBacking s)
    (hx : HtabExit (callEntryStateHOLFinite s callee) post) :
    R16Shards.TxBacking {post with locals := s.locals} := by
  have hu : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → i.2 % 8 = 0 → IvlUnhit s post i := by
    intro i hi hn hi8
    exact phase2_htabExit_fixed_unhit
      ((arenaReady_with_locals s callee (s.clock - 1)).mpr hs)
      ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw)
      ht hx hi hn hi8
  apply phase2_backing_of_header_unhit hs he hw hb
  · have hg := hx.2.2.2.2.2.2.2 (ofString "bo") (by decide)
    simp only [globN, ← hg]; rfl
  · apply hu _ _ (by simp) (by norm_num)
    simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
  · intro k hk
    apply hu _ _ (by simp) (by norm_num)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
    · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]

/-- The concrete table insertion shared by both account lookup bodies preserves backing. -/
theorem phase2_htab_set_ts8_backing (key value : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → R16Shards.TxBacking s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  obtain ⟨tw, rfl, htw, hts⟩ := R16WkAcctWs.evalAt_loadG_nz s hp.1.1.1 "ts" 8
    (by decide) v1 he1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "ts" + 8) := by
    simp [locN, callEntryStateHOLFinite, hct, htw]
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1) (by rw [hr]; simp)
  rw [hr] at hn
  have hnz : memW s (globN s "ts" + 8) ≠ 0 := by
    rw [← ht]; exact hn (Or.inl ⟨v, rfl⟩)
  have hmem := (R16WkAcctWs.nonValueSlot_ts8 s S hw.1 hts hnz).1
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hmem).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hmem).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl
    harg (by rw [hr]; simp)
  rw [hr] at hx
  exact phase2_htabExit_callEntry_backing callee hp.1.1 hp.2.1 hw
    (ht.symm ▸ hmem) hp.2.2 (hx v rfl)

/-- The concrete world-state lookup preserves the complete nested backing guard. -/
theorem phase2_ws_get_account_optional_backing {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd) (hb : R16Shards.TxBacking s)
    (hnt : (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    R16Shards.TxBacking (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2 := by
  have hx := R16Shards.worldEff_ws_get_account_optional s s ha.2
    (R16Shards.WorldEff.refl s [] R16Shards.wsBufs R16Shards.wsGw ha hc) hnt hr
  apply phase2_backing_of_header_unhit ha he hw hb
  · have hg := hx.gw_kept (ofString "bo") (by decide)
    simp only [globN, hg]
  · have hm : (globN s "bo", 88) ∈ fixedObjects s := by
      simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    have hf := (hw.2.2.1.1 _ hm).resolve_left (by simp)
    apply phase2_ws_get_account_optional_unhit s hc ha ⟨hf.2.1, by norm_num⟩ hf.1 _ hnt hr
    intro b hmem
    have hbg : b ∈ globalBuffers := by
      simp only [R16Shards.wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;> decide
    exact disj_symm (bufferRegion_disj_le hw b hbg (by
      simp only [R16Shards.wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;> decide) b.2 (by omega)
      (globN s "bo", 88) (R16Shards.PtxP1.bo_mem_typed he.bo_nz))
  · exact phase2_ws_get_account_optional_nested_unhit s hc ha he hw hnt hr

/-- Account callees omit the transaction index; its default zero still satisfies the bound. -/
theorem phase2_txEnv_callEntry_without_index {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (he : TxEnv s) (hi : callee.lookup (ofString "index") = none) :
    TxEnv (callEntryStateHOLFinite s callee) := by
  refine ⟨he.bo_nz, he.bo24, he.bo32, he.bo40, he.bo72, ?_, he.jcap_nz⟩
  have hb := he.idx_lt
  change locN (callEntryStateHOLFinite s callee) "index" < memW s (globN s "bo" + 80)
  simp only [locN, callEntryStateHOLFinite, hi]
  omega

/-- Lift concrete world-state backing preservation to its account-call entry. -/
theorem phase2_ws_get_account_optional_callEntry_backing {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s) (he : TxEnv s)
    {S Nd : List Nat} (hw : WorldTypedWith s S Nd) (hb : R16Shards.TxBacking s)
    (hi : callee.lookup (ofString "index") = none)
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    R16Shards.TxBacking (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2 := by
  exact phase2_ws_get_account_optional_backing (callEntryStateHOLFinite s callee) hc
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr ha)
    (phase2_txEnv_callEntry_without_index s callee he hi)
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hw) hb hnt hr

/-- Resolve the concrete world-state callee and restore its caller with backing intact. -/
theorem phase2_ws_get_account_optional_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "ws_get_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "ws_get_account_optional")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.lookup_ws_get_account_optional_top] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hcallee]
    simp [show ofString "index" ≠ ofString "addr" by decide]
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  have hb := phase2_ws_get_account_optional_callEntry_backing s callee hc hp.1.1 hp.2.1 hw hp.2.2 hi
    (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at hb
  exact hb

/-- A successful call without a destination restores the caller locals. -/
theorem phase2_call0_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call] at hnone ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rfl
  · simp only [hargs] at hnone ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · rfl
    · simp only [hl] at hnone ⊢
      by_cases hclk : s.clock = 0
      · simp [hclk] at hnone
      · rw [if_neg hclk] at hnone ⊢
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        simp only [hb] at hnone ⊢
        cases rb with
        | none => simp at hnone
        | some rb' =>
          cases rb' with
          | returned rv =>
            dsimp only at hnone ⊢
            split at hnone
            · rename_i hok; rw [if_pos hok]
            · simp at hnone
          | _ => simp at hnone

/-- The account table insertion preserves the whole guard needed by subsequent calls. -/
theorem phase2_htab_set_ts8_world_backing (key value : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hb := (phase2_htab_set_ts8_backing key value).run s hc hp hnt hr
  have hs := R16WkAcctWs.progWStep_call0_htab_set_recSlot (B := []) (gw := ["heap_ptr"])
    "ts" "ts+8" 8 key value (by simp) (by decide)
    (fun s S hT hts ht0 => R16WkAcctWs.nonValueSlot_ts8 s S hT hts ht0)
    s hc hp.1 hnt (Or.inl hr)
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  have he := txEnv_preserved_by_worldStep hs.1 (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by decide) (by intro k hk; simp at hk ⊢; tauto)
    (by simp [R16WkAcctWs.bufRegions]) (bo_words hw.2.2.1 hp.2.1.bo_nz).2.1
    (by simp [R16WkAcctWs.bufRegions]) hp.2.1 (locals := s.locals) rfl
  have hl := phase2_call0_locals s (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value] hr
  obtain ⟨S', Nd', _, hw', _⟩ := hs.1.2.2.2.2 S Nd hw (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  refine ⟨⟨hs.1.1, S', (worldTyped_iff_with _ S').mpr ⟨Nd', hw'⟩⟩, ?_, hb⟩
  rw [← hl] at he
  exact he

/-- Read-only account-table queries retain the complete backing-aware continuation guard. -/
theorem phase2_resume_ro_world_backing {fname name : MlS}
    (hro : ReadOnlyFn fname) (hi : name ≠ ofString "index")
    (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) name fname args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have hrestore : ({post with locals := s.locals} : PanSemStateFiniteExact 64 F) =
      {s with locals := s.locals, clock := post.clock} := by rw [he]; rfl
  rw [hrestore]
  refine ⟨?_, ?_, hp.2.2⟩
  · obtain ⟨S, hS⟩ := hp.1.2
    obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
    exact ⟨(arenaReady_with_locals s _ post.clock).mpr hp.1.1,
      S, (worldTyped_iff_with _ S).mpr ⟨Nd,
        (worldTypedWith_with_locals s _ post.clock S Nd).mpr hw⟩⟩
  · apply txEnv_with_locals s _ post.clock _ hp.2.1
    simp [HolFiniteMapExact.update, FUPDATE, hi]

/-- Recording a pre-state read preserves the transaction backing headers. -/
theorem phase2_htab_set_bs72_backing (key value : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), key, value])
      (fun r s => r = none → R16Shards.TxBacking s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  obtain ⟨tw, rfl, htw, hbs⟩ := R16WkAcctWs.evalAt_loadG_nz s hp.1.1.1 "bs" 72
    (by decide) v1 he1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "bs" + 72) := by
    simp [locN, callEntryStateHOLFinite, hct, htw]
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1) (by rw [hr]; simp)
  rw [hr] at hn
  have hnz : memW s (globN s "bs" + 72) ≠ 0 := by
    rw [← ht]; exact hn (Or.inl ⟨v, rfl⟩)
  have hmem := (R16WkAcctWs.nonValueSlot_bs72 s S hw.1 hbs hnz).1
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hmem).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hmem).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl
    harg (by rw [hr]; simp)
  rw [hr] at hx
  exact phase2_htabExit_callEntry_backing callee hp.1.1 hp.2.1 hw
    (ht.symm ▸ hmem) hp.2.2 (hx v rfl)

/-- The pre-state-read table insertion retains the complete continuation guard. -/
theorem phase2_htab_set_bs72_world_backing (key value : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), key, value])
      (fun r s => r = none → WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hb := (phase2_htab_set_bs72_backing key value).run s hc hp hnt hr
  have hs := R16WkAcctWs.progWStep_call0_htab_set_recSlot (B := []) (gw := ["heap_ptr"])
    "bs" "bs+72" 72 key value (by simp) (by decide)
    (fun s S hT hbs ht0 => R16WkAcctWs.nonValueSlot_bs72 s S hT hbs ht0)
    s hc hp.1 hnt (Or.inl hr)
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  have he := txEnv_preserved_by_worldStep hs.1 (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by decide) (by intro k hk; simp at hk ⊢; tauto)
    (by simp [R16WkAcctWs.bufRegions]) (bo_words hw.2.2.1 hp.2.1.bo_nz).2.1
    (by simp [R16WkAcctWs.bufRegions]) hp.2.1 (locals := s.locals) rfl
  have hl := phase2_call0_locals s (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), key, value] hr
  obtain ⟨S', Nd', _, hw', _⟩ := hs.1.2.2.2.2 S Nd hw (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  refine ⟨⟨hs.1.1, S', (worldTyped_iff_with _ S').mpr ⟨Nd', hw'⟩⟩, ?_, hb⟩
  rw [← hl] at he
  exact he

/-- Returning from a lookup clears locals but retains its backing-aware guard. -/
theorem phase2_return_world_backing (e : ExpHOL 64) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.return e) (fun r s => Resumes r → WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  rw [evaluateHOLFiniteState_return] at hr ⊢
  split
  · exact hp
  · split
    · refine ⟨?_, ?_, hp.2.2⟩
      · obtain ⟨S, hS⟩ := hp.1.2
        obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
        exact ⟨(arenaReady_with_locals s _ s.clock).mpr hp.1.1,
          S, (worldTyped_iff_with _ S).mpr ⟨Nd,
            (worldTypedWith_with_locals s _ s.clock S Nd).mpr hw⟩⟩
      · have he := hp.2.1
        refine ⟨he.bo_nz, he.bo24, he.bo32, he.bo40, he.bo72, ?_, he.jcap_nz⟩
        have hi := he.idx_lt
        change 0 < memW s (globN s "bo" + 80)
        omega
    · exact hp

/-- A destination-free call consumes its callee's return rather than returning itself. -/
theorem phase2_call0_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp_all
        split <;> simp

/-- Compose the concrete pre-state-read insertion and return with backing intact. -/
theorem phase2_record_pre_state_read_backing {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hp : WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read) =
      (some (.returned v), post)) :
    R16Shards.TxBacking post := by
  change evaluateHOLFiniteState s (.seq
    (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1]) (.return (.const 0))) = _ at hr
  rw [evaluateHOLFiniteState_seq] at hr
  dsimp only at hr
  rw [fixClockHOLFinite_evaluateState] at hr
  generalize he : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1]) = out at hr
  obtain ⟨r, t⟩ := out
  cases r with
  | none =>
    have hb := (phase2_htab_set_bs72_backing (.var .local (ofString "addr")) (.const 1)).run
      s hc hp (by rw [he]; simp) (by rw [he])
    rw [he] at hb
    simp only [evaluateHOLFiniteState_return] at hr
    simp [evalHOLExact, shapeOfHOLExact] at hr
    obtain ⟨_, rfl⟩ := hr
    exact hb
  | some r =>
    have hn := phase2_call0_ne_returned s (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1] v
    rw [he] at hn
    exact (hn (congrArg Prod.fst hr)).elim

/-- Resolve the pre-state-read call and restore its caller's transaction backing. -/
theorem phase2_record_pre_state_read_call_backing (args : List (ExpHOL 64)) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "record_pre_state_read") args)
      (fun r s => r = none → R16Shards.TxBacking s) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "record_pre_state_read")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16WkAcctWs.lookup_record_pre_state_read] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hcallee]
    simp [show ofString "index" ≠ ofString "addr" by decide]
  exact phase2_record_pre_state_read_backing (callEntryStateHOLFinite s callee) hc
    ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
      phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩ v post hr

/-- The miss-path pre-state-read call preserves the full backing-aware guard. -/
theorem phase2_record_pre_state_read_world_backing (args : List (ExpHOL 64)) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "record_pre_state_read") args)
      (fun r s => r = none → WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hb := (phase2_record_pre_state_read_call_backing args).run s hc hp hnt hr
  have hs := R16WkAcctWs.progWStep_call0 (B := []) (gw := ["heap_ptr"])
    (fun _ h => h) (fun _ h => h) R16WkAcctWs.wkSc_record_pre_state_read
    (args := args) s hc hp.1 hnt (Or.inl hr)
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  have he := txEnv_preserved_by_worldStep hs.1 (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])
    (by decide) (by intro k hk; simp at hk ⊢; tauto)
    (by simp [R16WkAcctWs.bufRegions]) (bo_words hw.2.2.1 hp.2.1.bo_nz).2.1
    (by simp [R16WkAcctWs.bufRegions]) hp.2.1 (locals := s.locals) rfl
  have hl := phase2_call0_locals s (ofString "record_pre_state_read") args hr
  obtain ⟨S', Nd', _, hw', _⟩ := hs.1.2.2.2.2 S Nd hw (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  refine ⟨⟨hs.1.1, S', (worldTyped_iff_with _ S').mpr ⟨Nd', hw'⟩⟩, ?_, hb⟩
  rw [← hl] at he
  exact he

/-- Compose returning lookup continuations without losing backing at binder restoration. -/
theorem phase2_decCall_backing
    {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {name fname : MlS} {shape : ShapeHOL} {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare R cont (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t)) :
    Hoare P (.decCall name shape fname arguments cont)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  obtain ⟨vout, hr⟩ := hr
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst r
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
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
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
              have hQc := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc
              dsimp only
              rw [← hpost_eq]
              exact hQc ⟨vout, rfl⟩
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

theorem phase2_return_backing (e : ExpHOL 64) :
    Hoare R16Shards.TxBacking (.return e)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  refine ⟨fun s _ hp _ _ => ?_⟩
  rw [evaluateHOLFiniteState_return]
  split
  · exact hp
  · split <;> exact hp

/-- A void call can reach a returned result only through its continuation. -/
theorem phase2_call0_seq_backing
    {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hcall : Hoare P (.call (some (none, none)) fname args) (fun r t => r = none → R t))
    (hcont : Hoare R cont (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t)) :
    Hoare P (.seq (.call (some (none, none)) fname args) cont)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  apply Hoare.seq
  · refine ⟨fun s hc hp hn => ⟨hcall.run s hc hp hn, ?_⟩⟩
    intro _ hr
    obtain ⟨v, hv⟩ := hr
    exact (phase2_call0_ne_returned s fname args v hv).elim
  · exact hcont

/-- The complete pre-state account miss tail preserves transaction backing. -/
theorem phase2_pre_state_account_tail_backing :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.seq (.call (some (none, none)) (ofString "record_pre_state_read")
        [.var .local (ofString "addr")])
        (.decCall (ofString "a") .one (ofString "ws_get_account_optional")
          [.var .local (ofString "addr")] (.return (.var .local (ofString "a")))))
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  apply phase2_call0_seq_backing (phase2_record_pre_state_read_world_backing _)
  exact phase2_decCall_backing (phase2_ws_get_account_optional_resume_backing _ _)
    (phase2_return_backing _)

/-- Preserve backing across an early cache hit or a returning miss continuation. -/
theorem phase2_lookup_hit_or_miss_backing
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (c e : ExpHOL 64) (cont : ProgHOL 64)
    (hp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → R16Shards.TxBacking s)
    (hcont : Hoare P cont (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t)) :
    Hoare P (.seq (.ite c (.return e) .skip) cont)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  apply Hoare.seq
  · apply Hoare.ite
    · refine ⟨fun s hc hs hn => ⟨?_, ?_⟩⟩
      · intro hr
        exact (return_ne_none s e hr).elim
      · intro _ hr
        exact (phase2_return_backing e).run s hc (hp s hs.1) hn hr
    · exact Hoare.skip (fun s hs => ⟨fun _ => hs.1, fun hn => (hn rfl).elim⟩)
    · intro F s hs
      refine ⟨?_, ?_⟩
      · intro hr; cases hr
      · intro _ hr
        obtain ⟨v, hv⟩ := hr
        cases hv
  · exact hcont

/-- The full pre-state account lookup preserves backing on both cache branches. -/
theorem phase2_get_pre_state_account_optional_backing :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  dsimp only [GuestTrapAndLookup.sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply phase2_call0_seq_backing (phase2_htab_set_ts8_world_backing _ _)
  apply phase2_decCall_backing (R := fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
    (phase2_resume_ro_world_backing (name := ofString "w") EvmFrameSpecs.ro_htab_get (by decide) _)
  exact phase2_lookup_hit_or_miss_backing _ _ _ (fun _ h => h.2.2)
    phase2_pre_state_account_tail_backing

/-- Restore backing after the concrete pre-state account lookup. -/
theorem phase2_get_pre_state_account_optional_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "get_pre_state_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "get_pre_state_account_optional")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_get_pre_state_account_optional] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_get_pre_state_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hcallee]
    simp [show ofString "index" ≠ ofString "addr" by decide]
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_pre_state_account_optional) =
      (some (.returned v), post) at hr
  have hb := phase2_get_pre_state_account_optional_backing.run (callEntryStateHOLFinite s callee) hc
    ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
      phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩
    (by rw [hr]; simp) (by rw [hr]; exact ⟨v, rfl⟩)
  rw [hr] at hb
  exact hb

/-- The outer optional account lookup preserves backing through insertion and both cache branches. -/
theorem phase2_get_account_optional_backing :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account_optional)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  dsimp only [GuestTrapAndLookup.sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply phase2_call0_seq_backing (phase2_htab_set_ts8_world_backing _ _)
  apply phase2_decCall_backing (R := fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
    (phase2_resume_ro_world_backing (name := ofString "w") EvmFrameSpecs.ro_htab_get (by decide) _)
  apply phase2_lookup_hit_or_miss_backing _ _ _ (fun _ h => h.2.2)
  exact phase2_decCall_backing (phase2_get_pre_state_account_optional_resume_backing _ _)
    (phase2_return_backing _)

/-- Lift the complete optional account lookup to a caller-local restoration boundary. -/
theorem phase2_get_account_optional_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "get_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "get_account_optional")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_get_account_optional] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account_optional,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_get_account_optional,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hcallee]
    simp [show ofString "index" ≠ ofString "addr" by decide]
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account_optional) =
      (some (.returned v), post) at hr
  have hb := phase2_get_account_optional_backing.run (callEntryStateHOLFinite s callee) hc
    ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
      phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩
    (by rw [hr]; simp) (by rw [hr]; exact ⟨v, rfl⟩)
  rw [hr] at hb
  exact hb

/-- Fresh allocation effects preserve the three existing transaction backing headers. -/
theorem phase2_fresh_worldEff_backing {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {gw : List String}
    (ha : ArenaReady s) (he : TxEnv s) {S Nd : List Nat}
    (hw : WorldTypedWith s S Nd) (hb : R16Shards.TxBacking s)
    (hg : globN post "bo" = globN s "bo")
    (hf : R16Shards.WorldEff s post [] [] gw) : R16Shards.TxBacking post := by
  apply phase2_backing_of_header_unhit ha he hw hb hg
  · have hm : (globN s "bo", 88) ∈ fixedObjects s := by
      simpa [he.bo_nz] using typedRecord_mem_fixedObjects s (r := ("bo", 88)) (by decide)
    have hi := (hw.2.2.1.1 _ hm).resolve_left (by simp)
    exact phase2_worldEff_allocated_unhit hf ha ⟨hi.2.1, by norm_num⟩ hi.1
      (by simp) (by simp)
  · intro k hk
    have hm : (memW s (globN s "bo" + k), 24) ∈ fixedObjects s := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo40]
      · simp [fixedObjects, blockOutObjects, he.bo_nz, he.bo72]
    have hi := (hw.2.2.1.1 _ hm).resolve_left (by simp)
    exact phase2_worldEff_allocated_unhit hf ha ⟨hi.2.1, by norm_num⟩ hi.1
      (by simp) (by simp)

/-- Concrete account allocation and initialization preserve existing transaction backing. -/
theorem phase2_acct_new_backing {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hp : WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
    {wn wc : BitVec 64} {vb : ValueHOL 64}
    (hb : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true)
    (hn : s.locals.lookup (ofString "nonce") = some (.val (.word wn)))
    (hbal : s.locals.lookup (ofString "balance") = some vb)
    (hcode : s.locals.lookup (ofString "code_hash") = some (.val (.word wc)))
    (hnt : (evaluateHOLFiniteState s (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1) :
    R16Shards.TxBacking (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).2 := by
  have hf := R16Shards.EvmEkFk.worldEff_acct_new s s (Rl := []) (B := []) (gw := ["heap_ptr"])
    (by decide) (R16Shards.WorldEff.refl s [] [] ["heap_ptr"] hp.1.1 hc)
    hb hn hbal hcode hnt hr
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  apply phase2_fresh_worldEff_backing hp.1.1 hp.2.1 hw hp.2.2 _ hf
  have hg := hf.gw_kept (ofString "bo") (by decide)
  unfold globN
  rw [← hg]

/-- Resolve account-constructor parameters and restore the caller backing. -/
theorem phase2_acct_new_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "acct_new") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "acct_new") vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_acct_new] at hx
  rcases vs with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | rest⟩⟩⟩ <;> try simp at hx
  rcases vn with ⟨⟨wn⟩⟩ | fs | ⟨nm, fs⟩ <;>
    rcases vc with ⟨⟨wc⟩⟩ | fs | ⟨nm, fs⟩ <;>
    try simp [shapeOfHOLExact, shapeEqHOL] at hx
  simp [show ofString "nonce" ≠ ofString "balance" by decide,
    show ofString "nonce" ≠ ofString "code_hash" by decide,
    show ofString "balance" ≠ ofString "code_hash" by decide] at hx
  obtain ⟨hsh, rfl, hL, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hL]; simp [show ofString "index" ≠ ofString "nonce" by decide,
      show ofString "index" ≠ ofString "balance" by decide,
      show ofString "index" ≠ ofString "code_hash" by decide]
  have hn : callee.lookup (ofString "nonce") = some (.val (.word wn)) := by
    rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide]
  have hb : callee.lookup (ofString "balance") = some vb := by
    rw [← hL]; simp [show ofString "balance" ≠ ofString "code_hash" by decide]
  have hw : callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
    rw [← hL]; simp
  have hback := phase2_acct_new_backing (callEntryStateHOLFinite s callee) hc
    ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
      phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩ hsh hn hb hw
    (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at hback
  exact hback

/-- The empty-account constructor preserves transaction backing. -/
theorem phase2_acct_empty_backing :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  dsimp only [GuestTrapAndLookup.sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  exact phase2_decCall_backing (phase2_acct_new_resume_backing _ _) (phase2_return_backing _)

/-- Resolve the empty-account constructor and retain backing across caller restoration. -/
theorem phase2_acct_empty_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "acct_empty") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "acct_empty") vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_acct_empty] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  cases vs with
  | cons a rest => simp at hx
  | nil =>
    simp at hx
    obtain ⟨rfl, hL, rfl⟩ := hx
    have hi : callee.lookup (ofString "index") = none := by rw [← hL]
    change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty) =
        (some (.returned v), post) at hr
    have hb := phase2_acct_empty_backing.run (callEntryStateHOLFinite s callee) hc
      ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
        phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩
      (by rw [hr]; simp) (by rw [hr]; exact ⟨v, rfl⟩)
    rw [hr] at hb
    exact hb

/-- Installing a newly created empty account in a caller local preserves backing. -/
theorem phase2_acct_empty_call_backing (name : MlS) (args : List (ExpHOL 64)) :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (.call (some (some (.local, name), none)) (ofString "acct_empty") args)
      (fun r t => r = none → R16Shards.TxBacking t) := by
  exact Hoare.callLocal_resume (phase2_acct_empty_resume_backing name args)

/-- Optional lookup restores the full guard needed by the empty-account branch. -/
theorem phase2_get_account_optional_resume_world_backing (name : MlS)
    (args : List (ExpHOL 64)) (hi : name ≠ ofString "index") :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      name (ofString "get_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hb := phase2_get_account_optional_resume_backing name args s vs body callee ret v post hc hp ha hl hr
  have hh := R16Shards.PtxP1.funSpec_at_lookup
    R16Shards.EvmEkFk.wkSc_get_account_optional s hc vs body callee ret hl
    (R16Shards.PtxP1.worldOK_callEntry hp.1 callee) (by rw [hr]; simp)
  rw [hr] at hh
  have hs := (R16WkAcctWs.WorldStepSc.of_pre_locals_clock
    (hh (Or.inl ⟨v, rfl⟩))).1
  obtain ⟨S, hS⟩ := hp.1.2
  obtain ⟨Nd, hw⟩ := (worldTyped_iff_with s S).mp hS
  have hd : ∀ i ∈ R16WkAcctWs.bufRegions R16Shards.EvmEkFk.wsAcctBufs s,
      Disj i (globN s "bo", 88) := by
    intro i hi
    simp only [R16WkAcctWs.bufRegions, R16Shards.EvmEkFk.wsAcctBufs, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact bufferRegion_disj_le hw ("keccak_pad", 136) (by decide) (by decide) 136 (by omega) _ (R16Shards.PtxP1.bo_mem_typed hp.2.1.bo_nz)
    · exact bufferRegion_disj_le hw ("keccak_st", 200) (by decide) (by decide) 200 (by omega) _ (R16Shards.PtxP1.bo_mem_typed hp.2.1.bo_nz)
    · exact bufferRegion_disj_le hw ("mpt_nib_scratch", 64) (by decide) (by decide) 64 (by omega) _ (R16Shards.PtxP1.bo_mem_typed hp.2.1.bo_nz)
  have hz : ∀ i ∈ R16WkAcctWs.bufRegions R16Shards.EvmEkFk.wsAcctBufs s,
      i.2 = 0 → i.1 % 8 = 0 := by
    intro i hi
    simp only [R16WkAcctWs.bufRegions, R16Shards.EvmEkFk.wsAcctBufs, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals exact R16Shards.PtxP1.bufferRegion_zero_aligned s _ _ (by omega)
  have he := txEnv_preserved_by_worldStep hs (by decide) (by decide)
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (by decide)
    (by intro k hk; simp at hk ⊢; tauto) hd
    (bo_words hw.2.2.1 hp.2.1.bo_nz).2.1 hz
    hp.2.1 (locals := (setVarHOLFinite name v {post with locals := s.locals}).locals)
    (by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hi])
  have hwpost := R16WkAcctWs.WorldStepSc.worldOK_bufs
    R16Shards.EvmEkFk.validBufList_wsAcctBufs hp.1
    (R16WkAcctWs.WorldStepSc.of_pre_locals_clock (hh (Or.inl ⟨v, rfl⟩)))
  exact ⟨localsFree_worldOK post _ post.clock hwpost, he, hb⟩

/-- A call installing a local result cannot propagate a returned result. -/
theorem phase2_callLocal_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (some (.local, name), none)) fname args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp_all
        split <;> try simp
        split <;> simp

/-- Full non-optional account lookup preserves backing on both existing and fresh accounts. -/
theorem phase2_get_account_backing :
    Hoare (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account)
      (fun r t => (∃ v, r = some (.returned v)) → R16Shards.TxBacking t) := by
  dsimp only [GuestTrapAndLookup.sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_get_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply phase2_decCall_backing (R := fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
    (phase2_get_account_optional_resume_world_backing (ofString "a") _ (by decide))
  apply Hoare.seq
  · apply Hoare.ite
    · refine ⟨fun s hc hp hn => ⟨?_, ?_⟩⟩
      · exact (phase2_acct_empty_call_backing _ _).run s hc hp.1 hn
      · intro hne hr
        obtain ⟨v, hv⟩ := hr
        exact (phase2_callLocal_ne_returned s _ _ _ v hv).elim
    · exact Hoare.skip (fun s hp => ⟨fun _ => hp.1.2.2, fun hn => (hn rfl).elim⟩)
    · intro F s hp
      constructor
      · intro h; cases h
      · intro _ h
        obtain ⟨v, hv⟩ := h
        cases hv
  · exact phase2_return_backing _

/-- Restore transaction backing after the complete non-optional account lookup. -/
theorem phase2_get_account_resume_backing (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s)
      R16Shards.TxBacking name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "get_account") vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_get_account] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_get_account,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hi : callee.lookup (ofString "index") = none := by
    rw [← hcallee]
    simp [show ofString "index" ≠ ofString "addr" by decide]
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_get_account) =
      (some (.returned v), post) at hr
  have hb := phase2_get_account_backing.run (callEntryStateHOLFinite s callee) hc
    ⟨R16Shards.PtxP1.worldOK_callEntry hp.1 callee,
      phase2_txEnv_callEntry_without_index s callee hp.2.1 hi, hp.2.2⟩
    (by rw [hr]; simp) (by rw [hr]; exact ⟨v, rfl⟩)
  rw [hr] at hb
  exact hb

/-- Account lookup jointly preserves message buffers, scalar locals and transaction backing. -/
theorem phase2_get_account_message_scalar_backing (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ names, name ≠ ofString n) :
    DecCallResumeOn (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  exact ⟨phase2_get_account_message_scalar_ready h buffers contents names name args hm hi hn
    s vs body callee ret v post hc hp.1 ha hl hr,
    phase2_get_account_resume_backing name args s vs body callee ret v post hc
      ⟨hp.1.1.1, hp.1.1.2.1, hp.2⟩ ha hl hr⟩

/-- The backing-aware account lookup feeds the next Phase-2 assembly cut. -/
theorem phase2_get_account_message_scalar_backing_bound (h : PtxCallees)
    {ι : Type} (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ names, name ≠ ofString n)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s) tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      (.decCall name .one (ofString "get_account") args tail) (K.get_account + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
    h.fb_get_account
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · exact phase2_get_account_message_scalar_backing h buffers contents names name args hm hi hn
  · exact ht

/-- Warming an account in the transaction table retains the message assembly guard. -/
theorem phase2_htab_set_ts8_message_scalar_backing
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (key value : ExpHOL 64) :
    Hoare (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none →
        PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hb := (phase2_htab_set_ts8_world_backing key value).run s hc
    ⟨hp.1.1.1, hp.1.1.2.1, hp.2⟩ hnt hr
  have hs := R16WkAcctWs.progWStep_call0_htab_set_recSlot (B := []) (gw := ["heap_ptr"])
    "ts" "ts+8" 8 key value (by simp) (by decide)
    (fun s S hT hts ht0 => R16WkAcctWs.nonValueSlot_ts8 s S hT hts ht0)
    s hc hp.1.1.1 hnt (Or.inl hr)
  have hl := phase2_call0_locals s (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value] hr
  refine ⟨⟨phase2_message_store_ready_world_step buffers contents s _ hp.1.1
    hb.1.1 hb.2.1 (by rw [hl]) hs.1.2.1 ?_, ?_⟩, hb.2.2⟩
  · intro S Nd hw
    obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := hs.1.2.2.2.2 S Nd hw
      (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
    exact ⟨S', Nd', hw', hg, hf⟩
  · intro n hn
    obtain ⟨w, hw⟩ := hp.1.2 n hn
    exact ⟨w, by rw [hl]; exact hw⟩

/-- The message-aware warming call also exposes the original world/backing cut. -/
theorem phase2_htab_set_ts8_message_world_backing
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (key value : ExpHOL 64) :
    Hoare (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → WorldOK s ∧ TxEnv s ∧ R16Shards.TxBacking s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have h := (phase2_htab_set_ts8_message_scalar_backing buffers contents names key value).run
    s hc hp hnt hr
  exact ⟨h.1.1.1, h.1.1.2.1, h.2⟩

/-- Transaction-table warming composes with a backing-aware message continuation. -/
theorem phase2_htab_set_ts8_message_scalar_backing_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (key value : ExpHOL 64)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s) tail b) :
    TerminatingProgBoundedOn
      (fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value]) tail)
      (K.htab_set + 1 + b) := by
  intro F s hc hp
  refine seq_bound_trans
    (P := fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
    (Q := fun s => PtxMessageScalarReady buffers contents names s ∧ R16Shards.TxBacking s)
    ?_ ?_ ht s hc hp
  · apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · exact phase2_htab_set_ts8_message_scalar_backing buffers contents names key value

/-- Warming the transaction account table preserves every initialized message word. -/
theorem phase2_htab_set_ts8_message_fields
    {ι F : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (s : PanSemStateFiniteExact 64 F) (key value : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hp : PtxMessageStoreReady buffers contents s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])).1 ≠ some .timeOut)
    (hr : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])).1 = none) :
    let post := (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])).2
    ∀ k, k < 22 → memW post (locN post "m" + 8 * k) = memW s (locN s "m" + 8 * k) := by
  dsimp only
  have hs := R16WkAcctWs.progWStep_call0_htab_set_recSlot (B := []) (gw := ["heap_ptr"])
    "ts" "ts+8" 8 key value (by simp) (by decide)
    (fun s S hT hts ht0 => R16WkAcctWs.nonValueSlot_ts8 s S hT hts ht0)
    s hc hp.1 hnt (Or.inl hr)
  have hl := phase2_call0_locals s (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value] hr
  have hm : locN (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])).2 "m" = locN s "m" := by
    simp only [locN, hl]
  rw [hm]
  apply phase2_message_world_step_fields buffers contents s _ hp
  intro S Nd hw
  obtain ⟨S', Nd', _, hw', hg, hf, _⟩ := hs.1.2.2.2.2 S Nd hw
    (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  exact ⟨S', Nd', hw', hg, hf⟩

/-- The initialized message words and Phase-4 locals carried across account calls. -/
def PtxMessageInitialized {ι : Type} (buffers : ι → Ivl)
    (contents : ι → Nat → BitVec 64) (names : List String) (aa ak : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
  (PtxMessageScalarReady buffers contents names s ∧ TxBacking s) ∧
    PtxPhase4LocalShapes s ∧
    memW s (locN s "m" + 152) = aa ∧ memW s (locN s "m" + 160) = ak ∧
    memW s (locN s "m" + 40) < 2 ^ 63

/-- Account lookup preserves all initialized readiness fields and caller shapes. -/
theorem phase2_get_account_message_initialized (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ names, name ≠ ofString n)
    (hshape : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      name ≠ ofString n) :
    DecCallResumeOn (PtxMessageInitialized buffers contents names aa ak)
      (PtxMessageInitialized buffers contents names aa ak) name (ofString "get_account") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hs := phase2_get_account_message_scalar_backing h buffers contents names name args hm hi hn
    s vs body callee ret v post hc hp.1 ha hl hr
  have hf := phase2_get_account_message_fields h s post vs body callee ret v hc hp.1.1.1 hl hr
  have hmp : locN (setVarHOLFinite name v {post with locals := s.locals}) "m" = locN s "m" := by
    simp [locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hm]
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · apply phase2_phase4_shapes_localsOnly s _ post.clock (fun n hmem => ?_) hp.2.1
    simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hshape n hmem]
  · change memW post (_ + 152) = aa
    rw [hmp, show 152 = 8 * 19 from rfl, hf 19 (by decide)]
    exact hp.2.2.1
  · change memW post (_ + 160) = ak
    rw [hmp, show 160 = 8 * 20 from rfl, hf 20 (by decide)]
    exact hp.2.2.2.1
  · change memW post (_ + 40) < 2 ^ 63
    rw [hmp, show 40 = 8 * 5 from rfl, hf 5 (by decide)]
    exact hp.2.2.2.2

/-- Transaction-table warming preserves the initialized readiness fields and shapes. -/
theorem phase2_htab_set_ts8_message_initialized
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (key value : ExpHOL 64) :
    Hoare (PtxMessageInitialized buffers contents names aa ak)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → PtxMessageInitialized buffers contents names aa ak s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hs := (phase2_htab_set_ts8_message_scalar_backing buffers contents names key value).run
    s hc hp.1 hnt hr
  have hf := phase2_htab_set_ts8_message_fields buffers contents s key value hc hp.1.1.1 hnt hr
  have hl := phase2_call0_locals s (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value] hr
  refine ⟨hs, ?_, ?_, ?_, ?_⟩
  · exact phase2_phase4_shapes_localsOnly s _ (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])).2.clock
      (fun n _ => congrArg (fun locals => locals.lookup (ofString n)) hl) hp.2.1
  · exact (hf 19 (by decide)).trans hp.2.2.1
  · exact (hf 20 (by decide)).trans hp.2.2.2.1
  · rw [show 40 = 8 * 5 from rfl, hf 5 (by decide)]
    exact hp.2.2.2.2

/-- Account lookup feeds a continuation without dropping initialized message words. -/
theorem phase2_get_account_message_initialized_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (name : MlS) (args : List (ExpHOL 64))
    (hm : name ≠ ofString "m") (hi : name ≠ ofString "index")
    (hn : ∀ n ∈ names, name ≠ ofString n)
    (hshape : ∀ n ∈ (["tx", "index", "sender", "gas", "tx_blob_gas_used", "price", "intrinsic"] : List String),
      name ≠ ofString n)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageInitialized buffers contents names aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageInitialized buffers contents names aa ak)
      (.decCall name .one (ofString "get_account") args tail) (K.get_account + b + 1) := by
  apply TerminatingProgBoundedOn.decCall_on
    (Q := PtxMessageInitialized buffers contents names aa ak) h.fb_get_account
  · intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · exact phase2_get_account_message_initialized h buffers contents names aa ak name args hm hi hn hshape
  · exact ht

/-- Warming composes at its original clock cost with initialized message continuations. -/
theorem phase2_htab_set_ts8_message_initialized_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (key value : ExpHOL 64)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageInitialized buffers contents names aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageInitialized buffers contents names aa ak)
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value]) tail)
      (K.htab_set + 1 + b) := by
  intro F s hc hp
  refine seq_bound_trans (P := PtxMessageInitialized buffers contents names aa ak)
    (Q := PtxMessageInitialized buffers contents names aa ak) ?_ ?_ ht s hc hp
  · apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1.1
  · exact phase2_htab_set_ts8_message_initialized buffers contents names aa ak key value

/-- The initialized-call guard and joint access-table witness recover the complete suffix. -/
theorem phase2_message_initialized_tables_iff_suffix {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names : List String} {aa ak : Nat} {s : PanSemStateFiniteExact 64 F} :
    (PtxMessageInitialized buffers contents names aa ak s ∧ PtxMessageTables s aa ak) ↔
      PtxMessageSuffixReady buffers contents names aa ak s := by
  constructor
  · rintro ⟨⟨⟨hs, hb⟩, hl, ha, hk, hg⟩, ht⟩
    exact ⟨hs, ht, hb, hl, ha, hk, hg⟩
  · rintro ⟨hs, ht, hb, hl, ha, hk, hg⟩
    exact ⟨⟨⟨hs, hb⟩, hl, ha, hk, hg⟩, ht⟩

/-- A completed initialized-call cut discharges the exact downstream backing-aware guard. -/
theorem phase2_message_initialized_ready {ι F : Type}
    {buffers : ι → Ivl} {contents : ι → Nat → BitVec 64}
    {names : List String} {aa ak : Nat} {s : PanSemStateFiniteExact 64 F}
    (hp : PtxMessageInitialized buffers contents names aa ak s)
    (ht : PtxMessageTables s aa ak) :
    (PtxMessageReady s ∧ TxBacking s) ∧ PtxPhase4LocalShapes s := by
  exact phase2_message_ready_backing_shapes hp.1.1.1 ht hp.1.2 hp.2.1
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2

open R10Shards.P26_P28 in
/-- Insertion into any non-value table preserves all world and journal roles. -/
theorem phase2_htabExit_nonValue_roles {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (hnv : locN s "t" ∈ S ∧
      (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ locN s "t") ∧
      (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ locN s "t") ∧
      globN s "bal_accounts" ≠ locN s "t" ∧
      (∀ ad ∈ balRecords s, memW s ad ≠ locN s "t") ∧
      (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ locN s "t"))
    (hx : HtabExit s post) :
    worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s := by
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "heap_ptr" := by revert g hg; decide
    exact R16Shards.globN_eq_of_lookup (hx.2.2.2.2.2.2.2 _ (by simpa using hne))
  have hu : ∀ i ∈ fixedObjects s, i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hi hpos
    have hf := (hw.2.2.1.1 i hi).resolve_left hpos
    have hal : ∀ j ∈ htabFootprint s (locN s "t"), j.1 % 8 = 0 ∧ j.2 % 8 = 0 := by
      intro j hj
      have hjw := ((hw.1.2.1 _ hnv.1).1.1 j hj).2
      exact ⟨hjw.1, hjw.2.1⟩
    have hfresh : (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
      have ha := hs.2.2.2.2.2.2.1
      have hb := hx.1.2.2.2.2.2.2.1
      omega
    exact R10Shards.P26_P28.ivlUnhit_of_frameOutside_aligned hpos hx.2.2.2.2.2.2.1
      hal ⟨hs.2.2.2.2.2.2.1, hfresh⟩
      (fun j hj => disj_symm (((hw.1.2.1 _ hnv.1).2 j hj).2 i hi))
      (R16WkAcctWs.disj_fresh_of_zero_or_allocated hs.2 hx.1.2 hx.2.2.2.2.1 (Or.inr hf.1))
  have hur : ∀ (g : String) (n : Nat), (g, n) ∈ typedRecords → n ≠ 0 →
      globN s g ≠ 0 → IvlUnhit s post (globN s g, n) := by
    intro g n hg hn hg0
    apply hu _ _ hn
    simpa [hg0] using typedRecord_mem_fixedObjects s hg
  have huts := hur "ts" 72 (by decide) (by decide)
  have hujr : globN s "journal_cap" ≠ 0 →
      IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := by
    intro h
    apply hu _ _ (by dsimp; omega)
    simp [fixedObjects, h]
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" :=
    R16Shards.globN_eq_of_lookup (hx.2.2.2.2.2.2.2 _ (by decide))
  have hag : AllocatorGrows s post := ⟨hx.2.2.2.2.1, hsp.le⟩
  have hjr := journalRoleSlots_eq_of_unhit hs.1 hx.1.1 hs.2 hag
    (fun (x : Nat) (hm : x ∈ S) => hm) hw.2.1 hw.2.2.1 hcore huts hujr
  refine ⟨?_, hjr.1⟩
  apply R16WkAcctWs.worldRoleSlots_eq_of_unhit_except hs.2 hw.1 hw.2.2.1 hcore
    (fun u hu hne i hi => phase2_htabExit_other_table_unhit hs hw hnv.1 hx hu hne hi)
    ⟨hnv.2.1, hnv.2.2.1, hnv.2.2.2.1, hnv.2.2.2.2.1⟩
    (hur "ws" 40 (by decide) (by decide))
    (hur "bs" 80 (by decide) (by decide)) huts
    (fun i hi hn => hu i (by simp only [fixedObjects]; exact List.mem_append_right _ hi) hn)
  have hlow : ∀ a : Nat, a + 8 ≤ InitE.sourceBase → memW post a = memW s a := by
    intro a ha
    have hal : a < 2 ^ 64 := by
      have : InitE.sourceBase < 2 ^ 64 := by decide
      omega
    have hm := hx.2.2.2.2.2.2.1 (BitVec.ofNat 64 a)
      (fun j hj hh => ?_) (fun hh => ?_)
    · unfold memW; rw [hm]
    · obtain ⟨h1, _⟩ := hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal] at h1
      have hlo := ((hw.1.2.1 _ hnv.1).1.1 j hj).1.1
      omega
    · obtain ⟨h1, _⟩ := hh
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal] at h1
      have hlo := hs.2.1
      dsimp at h1
      omega
  exact ⟨hlow 0 (by decide), hlow 8 (by decide), hlow 16 (by decide)⟩

/-- Transaction-table insertion is an instance of non-value role preservation. -/
theorem phase2_htabExit_ts8_roles {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (hts : globN s "ts" ≠ 0) (hn : memW s (globN s "ts" + 8) ≠ 0)
    (ht : locN s "t" = memW s (globN s "ts" + 8)) (hx : HtabExit s post) :
    worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s := by
  apply phase2_htabExit_nonValue_roles hs hw _ hx
  rw [ht]
  exact R16WkAcctWs.nonValueSlot_ts8 s S hw.1 hts hn

/-- Recording a pre-state read preserves all world and journal roles. -/
theorem phase2_htabExit_bs72_roles {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (hbs : globN s "bs" ≠ 0) (hn : memW s (globN s "bs" + 72) ≠ 0)
    (ht : locN s "t" = memW s (globN s "bs" + 72)) (hx : HtabExit s post) :
    worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s := by
  apply phase2_htabExit_nonValue_roles hs hw _ hx
  rw [ht]
  exact R16WkAcctWs.nonValueSlot_bs72 s S hw.1 hbs hn

/-- Warming the transaction table retains the complete private-table witness. -/
theorem phase2_htabExit_ts8_message_tables {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (hs : ArenaReady s) (hm : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hl : locN post "m" = locN s "m") (hbe : post.be = s.be)
    (hts : globN s "ts" ≠ 0) (hn : memW s (globN s "ts" + 8) ≠ 0)
    (ht : locN s "t" = memW s (globN s "ts" + 8))
    (hx : HtabExit s post) : PtxMessageTables post aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := hm
  have hm : PtxMessageTables s aa ak := ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩
  have hroles := phase2_htabExit_ts8_roles hs hw hts hn ht hx
  have hheaders := phase2_htabExit_message_table_headers hs hm hts hn ht hx
  apply phase2_message_tables_world_step s post hm hin hl hroles.1 hroles.2
    (hheaders.1.trans hal.symm) (hheaders.2.trans hkl.symm)
  have hstep := R16WkAcctWs.worldStepSc_of_htabExit_nonValue
    (r := none) (gw := ["heap_ptr"])
    ⟨hs, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw⟩⟩ hbe hx.2.2.2.2.2.2.2
    hx.2.2.2.2.2.2.2
    (t0 := locN s "t") (fun S hT => by
      rw [ht]
      exact R16WkAcctWs.nonValueSlot_ts8 s S hT hts hn)
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1
  intro S Nd hw
  obtain ⟨S', Nd', hsub, hw', hg, _⟩ := hstep.1.2.2.2.2 S Nd hw
    (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  exact ⟨S', Nd', hsub, hw', hg⟩

/-- Restore the private table witness after a concrete transaction-table call. -/
theorem phase2_htab_set_ts8_message_tables {ι : Type}
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (aa ak : Nat) (key value : ExpHOL 64) :
    Hoare (fun s => PtxMessageStoreReady buffers contents s ∧ PtxMessageTables s aa ak)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → PtxMessageTables s aa ak) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := hp.2
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  obtain ⟨tw, rfl, htw, hts⟩ := R16WkAcctWs.evalAt_loadG_nz s hp.1.1.1.1 "ts" 8
    (by decide) v1 he1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "ts" + 8) := by
    simp [locN, callEntryStateHOLFinite, hct, htw]
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1.1.1) (by rw [hr]; simp)
  rw [hr] at hn
  have hnz : memW s (globN s "ts" + 8) ≠ 0 := by
    rw [← ht]; exact hn (Or.inl ⟨v, rfl⟩)
  have hmem := (R16WkAcctWs.nonValueSlot_ts8 s S hw.1 hts hnz).1
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1.1.1, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hmem).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hmem).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hx := hx v rfl
  let pre := setVarHOLFinite (ofString "t") (.val (.word tw)) s
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "m" by decide]
  have hmt : locN pre "m" = locN s "m" := by
    exact locN_congr s pre.locals s.clock "m" hmp
  have hpt : locN pre "t" = locN (callEntryStateHOLFinite s callee) "t" := by
    simp [pre, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, callEntryStateHOLFinite, hct]
  have hxp : HtabExit pre {post with locals := s.locals} := by
    change ArenaReady _ ∧ HtabWF _ _ ∧ _
    refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr hx.1,
      (htabWF_with_locals post s.locals post.clock _).mpr (hpt.symm ▸ hx.2.1), ?_⟩
    change hdr post (locN pre "t") 0 = hdr s (locN pre "t") 0 ∧ _
    rw [hpt]
    exact hx.2.2
  have hbe := (PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hr] at hbe
  apply phase2_htabExit_ts8_message_tables (s := pre) (post := {post with locals := s.locals})
    ((arenaReady_with_locals s pre.locals s.clock).mpr hp.1.1.1)
    (phase2_message_tables_with_locals s pre.locals s.clock
      ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ hmp)
    (by
      change Inside (locN pre "m", 176) InitE.sourceBase (globN s "heap_ptr")
      rw [hmt]
      exact hp.1.2.2.2.1)
    hmt.symm hbe hts hnz (hpt.trans ht) hxp

/-- Warming preserves the full suffix cut, including the joint table witness. -/
theorem phase2_htab_set_ts8_message_suffix
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (key value : ExpHOL 64) :
    Hoare (PtxMessageSuffixReady buffers contents names aa ak)
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value])
      (fun r s => r = none → PtxMessageSuffixReady buffers contents names aa ak s) := by
  refine ⟨fun s hc hp hnt hr => ?_⟩
  have hi := (phase2_message_initialized_tables_iff_suffix).mpr hp
  apply phase2_message_initialized_tables_iff_suffix.mp
  exact ⟨(phase2_htab_set_ts8_message_initialized buffers contents names aa ak key value).run
      s hc hi.1 hnt hr,
    (phase2_htab_set_ts8_message_tables buffers contents aa ak key value).run
      s hc ⟨hi.1.1.1.1, hi.2⟩ hnt hr⟩

/-- The full suffix witness survives warming at its original clock cost. -/
theorem phase2_htab_set_ts8_message_suffix_bound (h : PtxCallees)
    {ι : Type} [Nonempty ι] (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64)
    (names : List String) (aa ak : Nat) (key value : ExpHOL 64)
    {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak) tail b) :
    TerminatingProgBoundedOn (PtxMessageSuffixReady buffers contents names aa ak)
      (.seq (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), key, value]) tail)
      (K.htab_set + 1 + b) := by
  intro F s hc hp
  refine seq_bound_trans (P := PtxMessageSuffixReady buffers contents names aa ak)
    (Q := PtxMessageSuffixReady buffers contents names aa ak) ?_ ?_ ht s hc hp
  · apply TerminatingProgBoundedOn.call_on h.fb_htab_set none _
    intro F s vs body callee ret hc hp he hl
    exact guestInv_callEntry s callee hp.1.1.1.1.1
  · exact phase2_htab_set_ts8_message_suffix buffers contents names aa ak key value

/-- Newly allocated role targets cannot alias either existing private access table. -/
theorem phase2_message_tables_fresh_roles {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (hs : ArenaReady s) (ht : PtxMessageTables s aa ak)
    (hr : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post,
      (∃ b ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 = b.1) ∨
        (globN s "heap_ptr" ≤ a.1 ∧ a.1 < heapLimit)) :
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ aa) ∧
    (∀ a ∈ worldRoleSlots post ++ journalRoleSlots post, a.1 ≠ ak) := by
  obtain ⟨S, Nd, hw, ha, hk, _, _, haf, hkf, _⟩ := ht
  have hbound : ∀ u ∈ S, u < globN s "heap_ptr" ∨ heapLimit ≤ u := by
    intro u hu
    have hi : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
    have hb := ((hw.1.2.1 u hu).2 (u, 88) hi).1
    rcases hb with hb | hb
    · have hb := hb.2
      dsimp at hb
      exact Or.inl (by omega)
    · have hlo := hs.2.2.2.1
      have hsp := hs.2.2.2.2.1
      have hsep : heapLimit ≤ InitE.scratchStart := by decide
      exact Or.inr (by dsimp [Inside] at *; omega)
  constructor
  · intro a ham heq
    rcases hr a ham with ⟨b, hb, he⟩ | hf
    · exact haf b hb (he.symm.trans heq)
    · have := hbound aa ha
      omega
  · intro a ha heq
    rcases hr a ha with ⟨b, hb, he⟩ | hf
    · exact hkf b hb (he.symm.trans heq)
    · have := hbound ak hk
      omega

/-- World growth may introduce fresh roles while preserving the private-table witness. -/
theorem phase2_message_tables_world_step_fresh_roles {F : Type}
    (s post : PanSemStateFiniteExact 64 F) {aa ak : Nat}
    (ha : ArenaReady s) (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hm : locN post "m" = locN s "m")
    (hr : ∀ a ∈ worldRoleSlots post ++ journalRoleSlots post,
      (∃ b ∈ worldRoleSlots s ++ journalRoleSlots s, a.1 = b.1) ∨
        (globN s "heap_ptr" ≤ a.1 ∧ a.1 < heapLimit))
    (haa : hdr post aa 0 = hdr s aa 0) (hak : hdr post ak 0 = hdr s ak 0)
    (hs : ∀ S Nd, WorldTypedWith s S Nd →
      ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
        OwnedGrows s post (worldOwned s S Nd) (worldOwned post S' Nd')) :
    PtxMessageTables post aa ak := by
  have hf := phase2_message_tables_fresh_roles ha ht hr
  exact phase2_message_tables_world_step_roles s post ht hin hm hf.1 hf.2 haa hak hs

/-- A fresh-only effect preserves every existing table header outside its buffers. -/
theorem phase2_worldEff_table_header {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {gw : List String}
    (hs : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (he : WorldEff s post [] B gw) {u : Nat} (hu : u ∈ S)
    (hB : ∀ b ∈ B, Disj (u, 88) (bufferRegion s b))
    (k : Nat) (hk : k < 11) : hdr post u k = hdr s u k := by
  have hi : (u, 88) ∈ htabFootprint s u := by simp [htabFootprint]
  have hf := (hw.1.2.1 u hu).1.1 (u, 88) hi
  have ha := ((hw.1.2.1 u hu).2 (u, 88) hi).1
  have heq := phase2_worldEff_allocated_unhit he hs ⟨hf.2.1, by norm_num⟩ ha
    (by simp) hB
  unfold hdr
  apply memW_eq_of_ivlUnhit heq
  · have h8 := hf.2.1
    omega
  · exact (ivl_allocated_bound hs.2 ha).2
  · constructor <;> omega

/-- Fresh-only effects preserve both access-table key lengths. -/
theorem phase2_worldEff_message_table_headers {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {gw : List String}
    {aa ak : Nat} (hs : ArenaReady s) (ht : PtxMessageTables s aa ak)
    (he : WorldEff s post [] B gw)
    (ha : ∀ b ∈ B, Disj (aa, 88) (bufferRegion s b))
    (hk : ∀ b ∈ B, Disj (ak, 88) (bufferRegion s b)) :
    hdr post aa 0 = 20 ∧ hdr post ak 0 = 52 := by
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, _⟩ := ht
  exact ⟨(phase2_worldEff_table_header hs hw he ham ha 0 (by decide)).trans hal,
    (phase2_worldEff_table_header hs hw he hkm hk 0 (by decide)).trans hkl⟩

/-- Untyped world buffers are disjoint from every jointly typed table header. -/
theorem phase2_table_header_disj_buffer {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (hw : WorldTypedWith s S Nd) {u : Nat} (hu : u ∈ S)
    (b : String × Nat) (hb : b ∈ globalBuffers)
    (hnt : b.1 ∉ typedRecords.map Prod.fst) :
    Disj (u, 88) (bufferRegion s b) := by
  apply disj_symm
  apply R10Shards.P26_P28.untypedBuf_disj_worldTypedIvls hw b hb hnt
  simp only [worldTypedIvls, List.mem_append]
  left; left; left; left; left
  exact List.mem_flatMap.mpr ⟨u, hu, by simp [htabFootprint]⟩

/-- The concrete world-state lookup preserves both private access-table key lengths. -/
theorem phase2_ws_get_account_optional_table_headers {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hnt : (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    let post := (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
    hdr post aa 0 = 20 ∧ hdr post ak 0 = 52 := by
  have he := worldEff_ws_get_account_optional s s ha.2
    (WorldEff.refl s [] wsBufs wsGw ha hc) hnt hr
  apply phase2_worldEff_message_table_headers ha ht he
  all_goals
    intro b hb
    obtain ⟨S, Nd, hw, ham, hkm, _⟩ := ht
    apply phase2_table_header_disj_buffer hw (by assumption) b
    · simp only [wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide
    · simp only [wsBufs, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl <;> decide

open R10Shards.P26_P28 in
/-- Fresh-only effects on untyped buffers preserve world and journal roles. -/
theorem phase2_worldEff_roles {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {gw : List String}
    (ha : ArenaReady s) {S Nd : List Nat} (hw : WorldTypedWith s S Nd)
    (he : WorldEff s post [] B gw)
    (hB : ∀ b ∈ B, b ∈ globalBuffers ∧ b.1 ∉ typedRecords.map Prod.fst)
    (hg : ∀ g ∈ coreWorldGlobals, ofString g ∉ gw.map ofString) :
    worldRoleSlots post = worldRoleSlots s ∧ journalRoleSlots post = journalRoleSlots s := by
  have hcore : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hgm
    exact R16Shards.globN_eq_of_lookup (he.gw_kept _ (hg g hgm))
  have hu : ∀ i ∈ worldTypedIvls s S Nd, Allocated s i → i.1 % 8 = 0 → i.2 % 8 = 0 →
      IvlUnhit s post i := by
    intro i hi hal h1 h2
    apply phase2_worldEff_allocated_unhit he ha ⟨h1, h2⟩ hal (by simp)
    intro b hb
    exact disj_symm (untypedBuf_disj_worldTypedIvls hw b (hB b hb).1 (hB b hb).2 i hi)
  have huf : ∀ i ∈ worldTypedIvls s S Nd, i ∈ fixedObjects s → i.2 ≠ 0 → IvlUnhit s post i := by
    intro i hi hf hn
    have hh := (hw.2.2.1.1 i hf).resolve_left hn
    exact hu i hi hh.1 hh.2.1 hh.2.2.1
  have hut : ∀ t ∈ S, ∀ i ∈ htabFootprint s t, IvlUnhit s post i := by
    intro t ht i hi
    have hf := ((hw.1.2.1 t ht).1.1 i hi).2
    apply hu i _ ((hw.1.2.1 t ht).2 i hi).1 hf.1 hf.2.1
    simp only [worldTypedIvls, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatMap.mpr ⟨t, ht, hi⟩)))))
  have hur : ∀ (g : String) (n : Nat), (g, n) ∈ typedRecords → n ≠ 0 →
      globN s g ≠ 0 → IvlUnhit s post (globN s g, n) := by
    intro g n hrec hn hgn
    apply huf _ _ _ hn
    · simp only [worldTypedIvls, List.mem_append]
      left; left; left; left; right
      exact List.mem_map.mpr ⟨(g, n), hrec, by simp [hgn]⟩
    · simpa [hgn] using typedRecord_mem_fixedObjects s hrec
  have huts := hur "ts" 72 (by decide) (by decide)
  have hujr : globN s "journal_cap" ≠ 0 →
      IvlUnhit s post (globN s "journal", 32 * globN s "journal_cap") := by
    intro hn
    apply huf _ _ _ (by dsimp; omega)
    · simp [worldTypedIvls, hn]
    · simp [fixedObjects, hn]
  have hjr := R10Shards.P26_P28.journalRoleSlots_eq_of_unhit ha.1 he.arena.1 ha.2
    ⟨he.hp_lo, he.sp_hi⟩ (fun (x : Nat) (hx : x ∈ S) => hx) hw.2.1 hw.2.2.1 hcore huts hujr
  refine ⟨?_, hjr.1⟩
  apply R10Shards.P26_P28.worldRoleSlots_eq_of_unhit ha.2 hw.1 hw.2.2.1 hcore hut
    (hur "ws" 40 (by decide) (by decide)) (hur "bs" 80 (by decide) (by decide)) huts
  · intro i hi hn
    apply huf i _ _ hn
    · simp only [worldTypedIvls, List.mem_append]
      exact Or.inl (Or.inr hi)
    · simp only [fixedObjects, List.mem_append]
      exact Or.inr hi
  · exact ⟨mem_low_eq_of_domain_writes he.out_dom ha.1 (by decide),
      mem_low_eq_of_domain_writes he.out_dom ha.1 (by decide)⟩

/-- Fresh-only world effects retain the complete message-table witness. -/
theorem phase2_worldEff_message_tables {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {B : List (String × Nat)} {gw : List String}
    {aa ak : Nat} (ha : ArenaReady s) (ht : PtxMessageTables s aa ak)
    (he : WorldEff s post [] B gw)
    (hB : ∀ b ∈ B, b ∈ globalBuffers ∧ b.1 ∉ typedRecords.map Prod.fst)
    (hg : ∀ g ∈ R10Shards.P26_P28.coreWorldGlobals, ofString g ∉ gw.map ofString)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hm : locN post "m" = locN s "m") : PtxMessageTables post aa ak := by
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := ht
  have ht : PtxMessageTables s aa ak := ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩
  have hr := phase2_worldEff_roles ha hw he hB hg
  apply phase2_message_tables_world_step s post ht hin hm hr.1 hr.2
    (phase2_worldEff_table_header ha hw he ham (fun b hb =>
      phase2_table_header_disj_buffer hw ham b (hB b hb).1 (hB b hb).2) 0 (by decide))
    (phase2_worldEff_table_header ha hw he hkm (fun b hb =>
      phase2_table_header_disj_buffer hw hkm b (hB b hb).1 (hB b hb).2) 0 (by decide))
  have hstep := WorldEff.to_worldStep_Q (R := fun _ => []) (r := none) (Q := NoExtra)
    ⟨ha, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw⟩⟩ hB hg he
    (fun _ _ _ _ _ _ _ _ => trivial)
  intro S Nd hw
  obtain ⟨S', Nd', hsub, hw', hg', _⟩ := hstep.2.2.2.2 S Nd hw (by simp [IvlsDisj])
  exact ⟨S', Nd', hsub, hw', hg'⟩

/-- World-state account lookup retains private tables when the message local is restored. -/
theorem phase2_ws_get_account_optional_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hnt : (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    let post := (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
    PtxMessageTables {post with locals := s.locals} aa ak := by
  have he := worldEff_ws_get_account_optional s s ha.2
    (WorldEff.refl s [] wsBufs wsGw ha hc) hnt hr
  apply phase2_worldEff_message_tables ha ht (he.locals_clock s.locals _) _ _ hin rfl
  · decide
  · decide

/-- Account lookup transports the private tables across the actual call-entry boundary. -/
theorem phase2_ws_get_account_optional_callEntry_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).1) :
    let post := (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
    PtxMessageTables {post with locals := s.locals} aa ak := by
  have he := worldEff_ws_get_account_optional s (callEntryStateHOLFinite s callee) ha.2
    ((WorldEff.refl s [] wsBufs wsGw ha hc).locals_clock callee (s.clock - 1)) hnt hr
  exact phase2_worldEff_message_tables ha ht (he.locals_clock s.locals _) (by decide) (by decide) hin rfl

/-- Restore the message-table witness after a concrete returning account lookup call. -/
theorem phase2_ws_get_account_optional_resume_message_tables
    (aa ak : Nat) (name : MlS) (hne : name ≠ ofString "m") (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => PtxMessageTables s aa ak) name (ofString "ws_get_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "ws_get_account_optional")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.lookup_ws_get_account_optional_top] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hb := phase2_ws_get_account_optional_callEntry_message_tables s callee hc hp.1 hp.2.1 hp.2.2
    (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at hb
  exact phase2_message_tables_with_locals _ _ _ hb
    (by simp [HolFiniteMapExact.update, FUPDATE, hne])

/-- Fresh account construction preserves the private message tables. -/
theorem phase2_acct_new_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (ha : ArenaReady s) {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    {wn wc : BitVec 64} {vb : ValueHOL 64}
    (hb : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true)
    (hn : s.locals.lookup (ofString "nonce") = some (.val (.word wn)))
    (hbal : s.locals.lookup (ofString "balance") = some vb)
    (hcode : s.locals.lookup (ofString "code_hash") = some (.val (.word wc)))
    (hnt : (evaluateHOLFiniteState s (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState s (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1) :
    let post := (evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).2
    PtxMessageTables {post with locals := s.locals} aa ak := by
  have he := R16Shards.EvmEkFk.worldEff_acct_new s s (Rl := []) (B := []) (gw := ["heap_ptr"])
    (by decide) (WorldEff.refl s [] [] ["heap_ptr"] ha hc)
    hb hn hbal hcode hnt hr
  exact phase2_worldEff_message_tables ha ht (he.locals_clock s.locals _) (by simp) (by decide) hin rfl

/-- The constructor's effect is relative to the caller, so its private tables survive entry. -/
theorem phase2_acct_new_callEntry_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    {wn wc : BitVec 64} {vb : ValueHOL 64}
    (hb : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact vb) = true)
    (hn : callee.lookup (ofString "nonce") = some (.val (.word wn)))
    (hbal : callee.lookup (ofString "balance") = some vb)
    (hcode : callee.lookup (ofString "code_hash") = some (.val (.word wc)))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1) :
    let post := (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).2
    PtxMessageTables {post with locals := s.locals} aa ak := by
  have he := R16Shards.EvmEkFk.worldEff_acct_new s (callEntryStateHOLFinite s callee)
    (Rl := []) (B := []) (gw := ["heap_ptr"]) (by decide)
    ((WorldEff.refl s [] [] ["heap_ptr"] ha hc).locals_clock callee (s.clock - 1))
    hb hn hbal hcode hnt hr
  exact phase2_worldEff_message_tables ha ht (he.locals_clock s.locals _) (by simp) (by decide) hin rfl

/-- Restore private tables after a returning account constructor. -/
theorem phase2_acct_new_resume_message_tables
    (aa ak : Nat) (name : MlS) (hne : name ≠ ofString "m") (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => PtxMessageTables s aa ak) name (ofString "acct_new") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "acct_new") vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_acct_new] at hx
  rcases vs with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | rest⟩⟩⟩ <;> try simp at hx
  rcases vn with ⟨⟨wn⟩⟩ | fs | ⟨nm, fs⟩ <;>
    rcases vc with ⟨⟨wc⟩⟩ | fs | ⟨nm, fs⟩ <;>
    try simp [shapeOfHOLExact, shapeEqHOL] at hx
  simp [show ofString "nonce" ≠ ofString "balance" by decide,
    show ofString "nonce" ≠ ofString "code_hash" by decide,
    show ofString "balance" ≠ ofString "code_hash" by decide] at hx
  obtain ⟨hsh, rfl, hL, rfl⟩ := hx
  have hn : callee.lookup (ofString "nonce") = some (.val (.word wn)) := by
    rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide]
  have hb : callee.lookup (ofString "balance") = some vb := by
    rw [← hL]; simp [show ofString "balance" ≠ ofString "code_hash" by decide]
  have hw : callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
    rw [← hL]; simp
  have ht := phase2_acct_new_callEntry_message_tables s callee hc hp.1 hp.2.1 hp.2.2
    hsh hn hb hw (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
  rw [hr] at ht
  exact phase2_message_tables_with_locals _ _ _ ht
    (by simp [HolFiniteMapExact.update, FUPDATE, hne])

/-- Resolve constructor parameters while retaining an effect relative to the outer caller. -/
theorem phase2_acct_new_lookup_effect {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {gw : List String} (hg : "heap_ptr" ∈ gw) (he : WorldEff s cur Rl B gw)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vs : List (ValueHOL 64))
    (hl : lookupCodeHOLFinite cur.code.lookup (ofString "acct_new") vs =
      some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new, callee, .one))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite cur callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite cur callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).1) :
    WorldEff s (evaluateHOLFiniteState (callEntryStateHOLFinite cur callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_new)).2 Rl B gw := by
  have hx := lookupCodeHOLFinite_eq_some cur.code.lookup (ofString "acct_new") vs _ callee _ hl
  rw [he.code] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_acct_new] at hx
  rcases vs with _ | ⟨vn, _ | ⟨vb, _ | ⟨vc, _ | rest⟩⟩⟩ <;> try simp at hx
  rcases vn with ⟨⟨wn⟩⟩ | fs | ⟨nm, fs⟩ <;>
    rcases vc with ⟨⟨wc⟩⟩ | fs | ⟨nm, fs⟩ <;>
    try simp [shapeOfHOLExact, shapeEqHOL] at hx
  simp [show ofString "nonce" ≠ ofString "balance" by decide,
    show ofString "nonce" ≠ ofString "code_hash" by decide,
    show ofString "balance" ≠ ofString "code_hash" by decide] at hx
  obtain ⟨hsh, hL⟩ := hx
  have hn : callee.lookup (ofString "nonce") = some (.val (.word wn)) := by
    rw [← hL]; simp [show ofString "nonce" ≠ ofString "balance" by decide,
      show ofString "nonce" ≠ ofString "code_hash" by decide]
  have hb : callee.lookup (ofString "balance") = some vb := by
    rw [← hL]; simp [show ofString "balance" ≠ ofString "code_hash" by decide]
  have hw : callee.lookup (ofString "code_hash") = some (.val (.word wc)) := by
    rw [← hL]; simp
  exact R16Shards.EvmEkFk.worldEff_acct_new s (callEntryStateHOLFinite cur callee)
    (List.mem_map.mpr ⟨"heap_ptr", hg, rfl⟩) (he.locals_clock callee (cur.clock - 1)) hsh hn hb hw hnt hr

/-- Empty-account construction has only fresh heap effects. -/
theorem phase2_acct_empty_effect {F : Type}
    {s cur : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {gw : List String} (hg : "heap_ptr" ∈ gw) (he : WorldEff s cur Rl B gw)
    (hnt : (evaluateHOLFiniteState cur
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState cur
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).1) :
    WorldEff s (evaluateHOLFiniteState cur
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).2 Rl B gw := by
  dsimp only [GuestTrapAndLookup.sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil] at hnt hr ⊢
  apply worldEff_decCall_eff he _ _ _ _ _ _ _ R16Shards.EvmEkFk.lookup_acct_new
    (fun callee vs _ hl hn hr => phase2_acct_new_lookup_effect hg he callee vs hl hn hr)
    _ hnt (Or.inr (Or.inr (Or.inr hr)))
  intro callee vs rv post _ _ _ _ he'
  dsimp only
  intro _ _
  exact worldEff_return (he'.locals_clock _ _) _

/-- Empty-account construction preserves caller-private tables across callee entry. -/
theorem phase2_acct_empty_callEntry_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hc : s.code = originalRuntimeCode) (ha : ArenaReady s)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).1 ≠ some .timeOut)
    (hr : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).1) :
    let post := (evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty)).2
    PtxMessageTables {post with locals := s.locals} aa ak := by
  have he := phase2_acct_empty_effect (by simp : "heap_ptr" ∈ ["heap_ptr"])
    ((WorldEff.refl s [] [] ["heap_ptr"] ha hc).locals_clock callee (s.clock - 1)) hnt hr
  exact phase2_worldEff_message_tables ha ht (he.locals_clock s.locals _) (by simp) (by decide) hin rfl

/-- Restore the private tables after the empty-account constructor returns. -/
theorem phase2_acct_empty_resume_message_tables
    (aa ak : Nat) (name : MlS) (hne : name ≠ ofString "m") (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => PtxMessageTables s aa ak) name (ofString "acct_empty") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "acct_empty") vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.EvmEkFk.lookup_acct_empty] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_acct_empty,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  cases vs with
  | cons a rest => simp at hx
  | nil =>
    simp at hx
    obtain ⟨rfl, hL, rfl⟩ := hx
    change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_acct_empty) =
        (some (.returned v), post) at hr
    have ht := phase2_acct_empty_callEntry_message_tables s callee hc hp.1 hp.2.1 hp.2.2
      (by rw [hr]; simp) (by rw [hr]; exact Or.inl ⟨v, rfl⟩)
    rw [hr] at ht
    exact phase2_message_tables_with_locals _ _ _ ht
      (by simp [HolFiniteMapExact.update, FUPDATE, hne])

/-- The pre-state read table is distinct from both private message tables. -/
theorem phase2_message_tables_ne_bs72 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (ht : PtxMessageTables s aa ak) (hbs : globN s "bs" ≠ 0)
    (hn : memW s (globN s "bs" + 72) ≠ 0) :
    aa ≠ memW s (globN s "bs" + 72) ∧ ak ≠ memW s (globN s "bs" + 72) := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  have hm := R16WkAcctWs.mem_worldRoleSlots_recRole s "bs" 72 "bs+72" hbs hn
    (by simp [recRoles, hbs])
  exact ⟨Ne.symm (haf _ (List.mem_append_left _ hm)),
    Ne.symm (hkf _ (List.mem_append_left _ hm))⟩

/-- Recording a pre-state read retains the complete private-table witness. -/
theorem phase2_htabExit_bs72_message_tables {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {aa ak : Nat}
    (hs : ArenaReady s) (hm : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hl : locN post "m" = locN s "m") (hbe : post.be = s.be)
    (hbs : globN s "bs" ≠ 0) (hn : memW s (globN s "bs" + 72) ≠ 0)
    (ht : locN s "t" = memW s (globN s "bs" + 72))
    (hx : HtabExit s post) : PtxMessageTables post aa ak := by
  have hne := phase2_message_tables_ne_bs72 hm hbs hn
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := hm
  have hm : PtxMessageTables s aa ak := ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩
  have hroles := phase2_htabExit_bs72_roles hs hw hbs hn ht hx
  have hmem : locN s "t" ∈ S := by
    rw [ht]
    exact (R16WkAcctWs.nonValueSlot_bs72 s S hw.1 hbs hn).1
  apply phase2_message_tables_world_step s post hm hin hl hroles.1 hroles.2
    (phase2_htabExit_other_table_header hs hw hmem hx ha
      (by rw [ht]; exact hne.1) 0 (by decide))
    (phase2_htabExit_other_table_header hs hw hmem hx hk
      (by rw [ht]; exact hne.2) 0 (by decide))
  have hstep := R16WkAcctWs.worldStepSc_of_htabExit_nonValue
    (r := none) (gw := ["heap_ptr"])
    ⟨hs, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw⟩⟩ hbe hx.2.2.2.2.2.2.2
    hx.2.2.2.2.2.2.2
    (t0 := locN s "t") (fun S hT => by
      rw [ht]
      exact R16WkAcctWs.nonValueSlot_bs72 s S hT hbs hn)
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1
  intro S Nd hw
  obtain ⟨S', Nd', hsub, hw', hg, _⟩ := hstep.1.2.2.2.2 S Nd hw
    (by simp [R16WkAcctWs.bufRegions, IvlsDisj])
  exact ⟨S', Nd', hsub, hw', hg⟩

/-- Restore private tables after inserting into the pre-state read table. -/
theorem phase2_htab_set_bs72_message_tables
    (aa ak : Nat) (key value : ExpHOL 64) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), key, value])
      (fun r s => r = none → PtxMessageTables s aa ak) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := hp.2.1
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  obtain ⟨tw, rfl, htw, hbs⟩ := R16WkAcctWs.evalAt_loadG_nz s hp.1.1 "bs" 72
    (by decide) v1 he1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "bs" + 72) := by
    simp [locN, callEntryStateHOLFinite, hct, htw]
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1) (by rw [hr]; simp)
  rw [hr] at hn
  have hnz : memW s (globN s "bs" + 72) ≠ 0 := by
    rw [← ht]; exact hn (Or.inl ⟨v, rfl⟩)
  have hmem := (R16WkAcctWs.nonValueSlot_bs72 s S hw.1 hbs hnz).1
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw.1.2.1 _ hmem).1
    · rw [ht]
      exact fun i hi => ((hw.1.2.1 _ hmem).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hx := hx v rfl
  let pre := setVarHOLFinite (ofString "t") (.val (.word tw)) s
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "t" ≠ ofString "m" by decide]
  have hmt : locN pre "m" = locN s "m" := by
    exact locN_congr s pre.locals s.clock "m" hmp
  have hpt : locN pre "t" = locN (callEntryStateHOLFinite s callee) "t" := by
    simp [pre, locN, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, callEntryStateHOLFinite, hct]
  have hxp : HtabExit pre {post with locals := s.locals} := by
    change ArenaReady _ ∧ HtabWF _ _ ∧ _
    refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr hx.1,
      (htabWF_with_locals post s.locals post.clock _).mpr (hpt.symm ▸ hx.2.1), ?_⟩
    change hdr post (locN pre "t") 0 = hdr s (locN pre "t") 0 ∧ _
    rw [hpt]
    exact hx.2.2
  have hbe := (PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hr] at hbe
  apply phase2_htabExit_bs72_message_tables (s := pre) (post := {post with locals := s.locals})
    ((arenaReady_with_locals s pre.locals s.clock).mpr hp.1)
    (phase2_message_tables_with_locals s pre.locals s.clock
      ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ hmp)
    (by
      change Inside (locN pre "m", 176) InitE.sourceBase (globN s "heap_ptr")
      rw [hmt]
      exact hp.2.2)
    hmt.symm hbe hbs hnz (hpt.trans ht) hxp

/-- The concrete pre-state-read body preserves its private-table witness on return. -/
theorem phase2_record_pre_state_read_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    {aa ak : Nat} (hp : ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read) =
      (some (.returned v), post)) :
    PtxMessageTables {post with locals := s.locals} aa ak := by
  change evaluateHOLFiniteState s (.seq
    (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1]) (.return (.const 0))) = _ at hr
  rw [evaluateHOLFiniteState_seq] at hr
  dsimp only at hr
  rw [fixClockHOLFinite_evaluateState] at hr
  generalize he : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1]) = out at hr
  obtain ⟨r, t⟩ := out
  cases r with
  | none =>
    have hb := (phase2_htab_set_bs72_message_tables aa ak
      (.var .local (ofString "addr")) (.const 1)).run
      s hc hp (by rw [he]; simp) (by rw [he])
    rw [he] at hb
    simp only [evaluateHOLFiniteState_return] at hr
    simp [evalHOLExact, shapeOfHOLExact] at hr
    obtain ⟨_, rfl⟩ := hr
    have hl := phase2_call0_locals s (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1] (by rw [he])
    apply phase2_message_tables_with_locals t s.locals t.clock hb
    rw [← hl, he]
  | some r =>
    have hn := phase2_call0_ne_returned s (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
        .var .local (ofString "addr"), .const 1] v
    rw [he] at hn
    exact (hn (congrArg Prod.fst hr)).elim

/-- Read-only cache queries preserve private tables and their message allocation guard. -/
theorem phase2_resume_ro_message_tables {fname name : MlS}
    (hro : ReadOnlyFn fname) (hm : name ≠ ofString "m")
    (aa ak : Nat) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
      Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => ArenaReady s ∧ PtxMessageTables s aa ak ∧
        Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr")) name fname args := by
  intro F s vs body callee ret v post hc hp ha hl hb
  have hr := R16Shards.PtxP1.funSpec_at_lookup hro s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1) (by rw [hb]; simp)
  rw [hb] at hr
  have he := hr (Or.inl ⟨v, rfl⟩)
  dsimp only at he
  have hrestore : ({post with locals := s.locals} : PanSemStateFiniteExact 64 F) =
      {s with locals := s.locals, clock := post.clock} := by rw [he]; rfl
  rw [hrestore]
  have hlm : (s.locals.update (name, v)).lookup (ofString "m") =
      s.locals.lookup (ofString "m") := by
    simp [HolFiniteMapExact.update, FUPDATE, hm]
  refine ⟨(arenaReady_with_locals s _ post.clock).mpr hp.1,
    phase2_message_tables_with_locals s _ post.clock hp.2.1 hlm, ?_⟩
  change Inside (locN {s with locals := s.locals.update (name, v), clock := post.clock} "m", 176)
    InitE.sourceBase (globN s "heap_ptr")
  rw [locN_congr s _ post.clock "m" hlm]
  exact hp.2.2

/-- The private-table witness depends on a local environment only through its message pointer. -/
theorem phase2_message_tables_with_locN {F : Type}
    (s : PanSemStateFiniteExact 64 F) (locals : HolFiniteMapExact MlS (ValueHOL 64))
    (clock : Nat) {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    (hm : locN {s with locals := locals, clock := clock} "m" = locN s "m") :
    PtxMessageTables {s with locals := locals, clock := clock} aa ak := by
  obtain ⟨S, Nd, hw, ha, hk, hal, hkl, haf, hkf, hd⟩ := ht
  refine ⟨S, Nd, (worldTypedWith_with_locals s locals clock S Nd).mpr hw,
    ha, hk, hal, hkl, haf, hkf, ?_⟩
  rw [hm]
  exact hd

/-- A return clears locals but preserves the witness once the caller environment is restored. -/
theorem phase2_return_message_tables {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    {aa ak : Nat} (ht : PtxMessageTables s aa ak)
    {v : ValueHOL 64} {post : PanSemStateFiniteExact 64 F}
    (hr : evaluateHOLFiniteState s (.return e) = (some (.returned v), post)) :
    PtxMessageTables {post with locals := s.locals} aa ak := by
  simp only [evaluateHOLFiniteState_return] at hr
  split at hr
  · cases hr
  · split at hr
    · obtain ⟨_, rfl⟩ := Prod.mk.inj hr
      exact ht
    · cases hr

/-- Pre-state insertion transports an outer message witness even when callee locals omit it. -/
theorem phase2_htabExit_bs72_callEntry_message_tables {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hs : ArenaReady s) {aa ak : Nat} (hm : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hbe : post.be = s.be) (hbs : globN s "bs" ≠ 0)
    (hn : memW s (globN s "bs" + 72) ≠ 0)
    (ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "bs" + 72))
    (hx : HtabExit (callEntryStateHOLFinite s callee) post) :
    PtxMessageTables {post with locals := s.locals} aa ak := by
  let pre := {s with locals := s.locals.update (ofString "t",
      .val (.word (BitVec.ofNat 64 (locN (callEntryStateHOLFinite s callee) "t"))))}
  have htlt : locN (callEntryStateHOLFinite s callee) "t" < 2 ^ 64 := by
    unfold locN
    split <;> simp_all
    exact BitVec.isLt _
  have hpt : locN pre "t" = locN (callEntryStateHOLFinite s callee) "t" := by
    change (BitVec.ofNat 64 (locN (callEntryStateHOLFinite s callee) "t")).toNat = _
    exact Nat.mod_eq_of_lt htlt
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, HolFiniteMapExact.update, FUPDATE, show ofString "t" ≠ ofString "m" by decide]
  have hmt : locN pre "m" = locN s "m" := locN_congr s pre.locals s.clock "m" hmp
  have hxp : HtabExit pre {post with locals := s.locals} := by
    change ArenaReady _ ∧ HtabWF _ _ ∧ _
    refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr hx.1,
      (htabWF_with_locals post s.locals post.clock _).mpr (hpt.symm ▸ hx.2.1), ?_⟩
    change hdr post (locN pre "t") 0 = hdr s (locN pre "t") 0 ∧ _
    rw [hpt]
    exact hx.2.2
  apply phase2_htabExit_bs72_message_tables (s := pre) (post := {post with locals := s.locals})
    ((arenaReady_with_locals s pre.locals s.clock).mpr hs)
    (phase2_message_tables_with_locals s pre.locals s.clock hm hmp)
    (by change Inside (locN pre "m", 176) InitE.sourceBase (globN s "heap_ptr"); rw [hmt]; exact hin)
    hmt.symm hbe hbs hn (hpt.trans ht) hxp

/-- Transaction warming retains outer private tables across a callee-local boundary. -/
theorem phase2_htabExit_ts8_callEntry_message_tables {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hs : ArenaReady s) {aa ak : Nat} (hm : PtxMessageTables s aa ak)
    (hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr"))
    (hbe : post.be = s.be) (hts : globN s "ts" ≠ 0)
    (hn : memW s (globN s "ts" + 8) ≠ 0)
    (ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "ts" + 8))
    (hx : HtabExit (callEntryStateHOLFinite s callee) post) :
    PtxMessageTables {post with locals := s.locals} aa ak := by
  let pre := {s with locals := s.locals.update (ofString "t",
      .val (.word (BitVec.ofNat 64 (locN (callEntryStateHOLFinite s callee) "t"))))}
  have htlt : locN (callEntryStateHOLFinite s callee) "t" < 2 ^ 64 := by
    unfold locN
    split <;> simp_all
    exact BitVec.isLt _
  have hpt : locN pre "t" = locN (callEntryStateHOLFinite s callee) "t" := by
    change (BitVec.ofNat 64 (locN (callEntryStateHOLFinite s callee) "t")).toNat = _
    exact Nat.mod_eq_of_lt htlt
  have hmp : pre.locals.lookup (ofString "m") = s.locals.lookup (ofString "m") := by
    simp [pre, HolFiniteMapExact.update, FUPDATE, show ofString "t" ≠ ofString "m" by decide]
  have hmt : locN pre "m" = locN s "m" := locN_congr s pre.locals s.clock "m" hmp
  have hxp : HtabExit pre {post with locals := s.locals} := by
    change ArenaReady _ ∧ HtabWF _ _ ∧ _
    refine ⟨(arenaReady_with_locals post s.locals post.clock).mpr hx.1,
      (htabWF_with_locals post s.locals post.clock _).mpr (hpt.symm ▸ hx.2.1), ?_⟩
    change hdr post (locN pre "t") 0 = hdr s (locN pre "t") 0 ∧ _
    rw [hpt]
    exact hx.2.2
  apply phase2_htabExit_ts8_message_tables (s := pre) (post := {post with locals := s.locals})
    ((arenaReady_with_locals s pre.locals s.clock).mpr hs)
    (phase2_message_tables_with_locals s pre.locals s.clock hm hmp)
    (by change Inside (locN pre "m", 176) InitE.sourceBase (globN s "heap_ptr"); rw [hmt]; exact hin)
    hmt.symm hbe hts hn (hpt.trans ht) hxp

/-- Pre-state insertion preserves a private witness in an arbitrary saved caller environment. -/
theorem phase2_htab_set_bs72_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64))
    (aa ak : Nat) (key value : ExpHOL 64) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), key, value])
      (fun r s => r = none → PtxMessageTables {s with locals := saved} aa ak) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  obtain ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ := hp.2.1
  have hw0 := (worldTypedWith_with_locals s saved s.clock S Nd).mp hw
  obtain ⟨v1, _, _, he1, _, _, hct, _, _⟩ := R16WkAcctWs.callee_param_three s
    (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    .one .one .one _ _ (by rw [hc]; exact EvmFrameSpecs.lookup_htab_set)
    _ _ _ vs body callee ret ha hl
  obtain ⟨tw, rfl, htw, hbs⟩ := R16WkAcctWs.evalAt_loadG_nz s hp.1.1 "bs" 72
    (by decide) v1 he1
  have ht : locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s "bs" + 72) := by
    simp [locN, callEntryStateHOLFinite, hct, htw]
  have hn := FunSpec.at_lookup EvmFrameSpecs.nz_htab_set s hc vs body callee ret hl
    (guestInv_callEntry s callee hp.1.1) (by rw [hr]; simp)
  rw [hr] at hn
  have hnz : memW s (globN s "bs" + 72) ≠ 0 := by
    rw [← ht]; exact hn (Or.inl ⟨v, rfl⟩)
  have hmem := (R16WkAcctWs.nonValueSlot_bs72 s S hw0.1 hbs hnz).1
  have harg : HtabArgWF (callEntryStateHOLFinite s callee) := by
    refine ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1, ?_, ?_⟩
    · rw [ht]
      exact (htabWF_with_locals s callee (s.clock - 1) _).mpr (hw0.1.2.1 _ hmem).1
    · rw [ht]
      exact fun i hi => ((hw0.1.2.1 _ hmem).2 i hi).1
  have hx := FunSpec.at_lookup htab_set_spec s hc vs body callee ret hl harg (by rw [hr]; simp)
  rw [hr] at hx
  have hbe := (PanRunBounded.evaluateHOLFiniteState_metadata
    (callEntryStateHOLFinite s callee) body).2.2.1
  rw [hr] at hbe
  exact phase2_htabExit_bs72_callEntry_message_tables {s with locals := saved} post callee
    ((arenaReady_with_locals s saved s.clock).mpr hp.1)
    ⟨S, Nd, hw, ham, hkm, hal, hkl, haf, hkf, hd⟩ hp.2.2 hbe hbs hnz ht (hx v rfl)

/-- Compose the complete pre-state-read body while retaining the outer caller's tables. -/
theorem phase2_record_pre_state_read_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read)
      (fun r s => (∃ v, r = some (.returned v)) →
        PtxMessageTables {s with locals := saved} aa ak) := by
  change Hoare _ (.seq (.call (some (none, none)) (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
      .var .local (ofString "addr"), .const 1]) (.return (.const 0))) _
  apply Hoare.seq (R := fun s => PtxMessageTables {s with locals := saved} aa ak)
  · refine ⟨fun s hc hp hn => ⟨?_, ?_⟩⟩
    · exact (phase2_htab_set_bs72_saved_tables saved aa ak
        (.var .local (ofString "addr")) (.const 1)).run s hc hp hn
    · intro _ hr
      obtain ⟨v, hv⟩ := hr
      exact (phase2_call0_ne_returned s (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
          .var .local (ofString "addr"), .const 1] v hv).elim
  · refine ⟨fun s hc hp hn hr => ?_⟩
    simpa [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
      emptyLocalsHOLFinite] using hp

/-- The concrete pre-state-read call restores the outer saved table witness. -/
theorem phase2_record_pre_state_read_call_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (.call (some (none, none)) (ofString "record_pre_state_read") args)
      (fun r s => r = none → PtxMessageTables {s with locals := saved} aa ak) := by
  apply Hoare.call0_resume
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "record_pre_state_read")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16WkAcctWs.lookup_record_pre_state_read] at hx
  change (if _ then some (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read,
    _, .one) else none) = some (body, callee.lookup, ret) at hx
  dsimp [sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  change evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_record_pre_state_read) =
      (some (.returned v), post) at hr
  have ht := (phase2_record_pre_state_read_saved_tables saved aa ak).run
    (callEntryStateHOLFinite s callee) hc
    ⟨(arenaReady_with_locals s callee (s.clock - 1)).mpr hp.1,
      phase2_message_tables_with_locals {s with locals := saved} saved (s.clock - 1) hp.2.1 rfl,
      hp.2.2⟩ (by rw [hr]; simp) (by rw [hr]; exact ⟨v, rfl⟩)
  rw [hr] at ht
  exact ht

/-- World-state lookup preserves tables in an outer saved environment, independently of result locals. -/
theorem phase2_ws_get_account_optional_resume_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat)
    (name : MlS) (args : List (ExpHOL 64)) :
    DecCallResumeOn (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (fun s => PtxMessageTables {s with locals := saved} aa ak)
      name (ofString "ws_get_account_optional") args := by
  intro F s vs body callee ret v post hc hp ha hl hr
  have hx := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "ws_get_account_optional")
    vs body callee ret hl
  rw [hc] at hx
  simp only [lookupCodeHOLExact, R16Shards.lookup_ws_get_account_optional_top] at hx
  rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> try simp at hx
  rcases a with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩ <;>
    simp [shapeOfHOLExact, shapeEqHOL] at hx
  obtain ⟨rfl, hcallee, rfl⟩ := hx
  have hb := phase2_ws_get_account_optional_callEntry_message_tables
    {s with locals := saved} callee hc
    ((arenaReady_with_locals s saved s.clock).mpr hp.1) hp.2.1 hp.2.2
    (by change (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) _).1 ≠ _; rw [hr]; simp)
    (by change Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) _).1
        rw [hr]; exact Or.inl ⟨v, rfl⟩)
  change PtxMessageTables {(evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
    (GuestTrapAndLookup.sourceFnBody Guest.Software.guestFn_ws_get_account_optional)).2
      with locals := saved} aa ak at hb
  rw [hr] at hb
  exact hb

/-- Returning a local account result does not disturb any saved private-table witness. -/
theorem phase2_return_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat) (e : ExpHOL 64) :
    Hoare (fun s => PtxMessageTables {s with locals := saved} aa ak) (.return e)
      (fun r s => (∃ v, r = some (.returned v)) →
        PtxMessageTables {s with locals := saved} aa ak) := by
  refine ⟨fun s _ hp _ _ => ?_⟩
  rw [evaluateHOLFiniteState_return]
  split
  · exact hp
  · split <;> exact hp

/-- Compose a returning call with a continuation over saved private tables. -/
theorem phase2_decCall_saved_tables
    {P R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat)
    {name fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hcall : DecCallResumeOn P R name fname args)
    (hcont : Hoare R cont (fun r s => (∃ v, r = some (.returned v)) →
      PtxMessageTables {s with locals := saved} aa ak)) :
    Hoare P (.decCall name .one fname args cont)
      (fun r s => (∃ v, r = some (.returned v)) →
        PtxMessageTables {s with locals := saved} aa ak) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  obtain ⟨vout, hr⟩ := hr
  rcases hrun : evaluateHOLFiniteState s (.decCall name .one fname args cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst r
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee) body').1
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
              have hresR : R resumed := hcall s values body' callee ret' v bpost hcode hP hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc
              dsimp only
              rw [← hpost_eq]
              exact hQc ⟨vout, rfl⟩
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

/-- Recording a pre-state read preserves the full guard needed by the following lookup. -/
theorem phase2_record_pre_state_read_saved_guard
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat)
    (args : List (ExpHOL 64)) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (.call (some (none, none)) (ofString "record_pre_state_read") args)
      (fun r s => r = none → ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
        Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr")) := by
  refine ⟨fun s hc hp hn hr => ?_⟩
  have ht := (phase2_record_pre_state_read_call_saved_tables saved aa ak args).run s hc hp hn hr
  obtain ⟨S, Nd, hw, _⟩ := hp.2.1
  have hw0 := (worldTypedWith_with_locals s saved s.clock S Nd).mp hw
  have hs := R16WkAcctWs.progWStep_call0 (B := []) (gw := ["heap_ptr"])
    (fun _ h => h) (fun _ h => h) R16WkAcctWs.wkSc_record_pre_state_read
    (args := args) s hc ⟨hp.1, S, (worldTyped_iff_with s S).mpr ⟨Nd, hw0⟩⟩ hn (Or.inl hr)
  refine ⟨hs.1.1, ht, ?_⟩
  have hg := hs.1.2.1
  have hi := hp.2.2
  dsimp [Inside, locN] at hi ⊢
  omega

/-- The pre-state cache-miss path records the read and returns a world-state lookup safely. -/
theorem phase2_pre_state_account_tail_saved_tables
    (saved : HolFiniteMapExact MlS (ValueHOL 64)) (aa ak : Nat) :
    Hoare (fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
      Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
      (.seq (.call (some (none, none)) (ofString "record_pre_state_read")
        [.var .local (ofString "addr")])
        (.decCall (ofString "a") .one (ofString "ws_get_account_optional")
          [.var .local (ofString "addr")] (.return (.var .local (ofString "a")))))
      (fun r s => (∃ v, r = some (.returned v)) → PtxMessageTables {s with locals := saved} aa ak) := by
  apply Hoare.seq (R := fun s => ArenaReady s ∧ PtxMessageTables {s with locals := saved} aa ak ∧
    Inside (locN {s with locals := saved} "m", 176) InitE.sourceBase (globN s "heap_ptr"))
  · refine ⟨fun s hc hp hn => ⟨?_, ?_⟩⟩
    · exact (phase2_record_pre_state_read_saved_guard saved aa ak _).run s hc hp hn
    · intro _ hr
      obtain ⟨v, hv⟩ := hr
      exact (phase2_call0_ne_returned s (ofString "record_pre_state_read")
        [.var .local (ofString "addr")] v hv).elim
  · exact phase2_decCall_saved_tables saved aa ak
      (phase2_ws_get_account_optional_resume_saved_tables saved aa ak _ _)
      (phase2_return_saved_tables saved aa ak _)

end InitECandidate.Solver.Wave8GuestInv.R13Shards
