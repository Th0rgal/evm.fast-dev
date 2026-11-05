import InitECandidate.Solver.Wave8GuestInv.R13Shards.PtxPhase45R11
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PtxPhase1R11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shape information needed by the untyped stores of Phase 2. `price` is
the four-word fee value, whereas `mgas` and `reservoir` are scalar words. -/
structure PtxPhase2LocalShapes {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  scalar : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir"] : List String),
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
    (hl : ∀ name ∈ (["tx", "index", "sender", "mgas", "reservoir", "price", "enc", "intrinsic"] : List String),
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
    (hne : ∀ n ∈ (["tx", "index", "sender", "mgas", "reservoir", "price", "enc", "intrinsic"] : List String),
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
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · simpa only [hkeep "tx" (by decide)] using hprefix.1 "tx" (by simp)
    · simpa only [hkeep "index" (by decide)] using hprefix.1 "index" (by simp)
    · simpa only [hkeep "sender" (by decide)] using hprefix.1 "sender" (by simp)
    · simpa only [hkeep "mgas" (by decide)] using hgas
    · exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩
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

end InitECandidate.Solver.Wave8GuestInv.R13Shards
