import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase2BackingE

/-!
# Phase 2 backing replay, region D' (guest spine 69..77)

Region D' opens with the `msg_new` allocation call that carves the 176-byte
message buffer out of the warm heap, followed by the seven message-field
stores: the beacon roots, the transaction-extras word, the sender, the word
loaded from `tx+152`, the message gas at slot 5, the reservoir, and the
four-word fee value loaded from `tx+160`.

The region entry guard is the region-E exit invariant itself, so regions E
and D' compose without an adapter. The exit guard carries the scalar message
frame of the degenerate saved-buffer family together with the message-gas
bound born at the slot-5 store: the value written there is the caller's
`mgas` word, bounded by `2 ^ 28` in the validated caller frame, and it is
the source of the `2 ^ 63` message-gas bound of the Phase 2 backing cut.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards

/-! ## The degenerate saved-buffer family

`msg_new` needs no saved warm buffer to resume: its saved-buffer hypothesis
is satisfied by the empty interval at the arena base, whose ownership clause
is trivial (an empty interval is disjoint from everything) and whose content
clause is vacuous. -/

/-- The degenerate saved-buffer positions: the empty interval at the base. -/
def ptxPhase2FDegBuf : Unit → Ivl := fun _ => (InitE.sourceBase, 0)

/-- The degenerate saved-buffer contents: the zero word everywhere. -/
def ptxPhase2FDegCont : Unit → Nat → BitVec 64 := fun _ _ => 0

/-- The caller scalars witnessed by the message frame after `msg_new`. -/
def ptxPhase2FNames : List String := ["te", "sender", "mgas", "reservoir"]

/-- The message-gas bound at slot 5 (`m+40`), born by the region's fifth
store and carried to the htab region as the source of the `2 ^ 63`
message-gas bound. -/
def ptxPhase2FM40 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (locN s "m" + 40) < 2 ^ 63

/-- The scalar message frame over the degenerate family. -/
def ptxPhase2FBScalar {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s

/-- Region D' entry guard: the region-E exit invariant itself. -/
def ptxPhase2FDPrime {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ptxPhase2EInv s

/-! ## The empty live buffer at the arena base -/

/-- The empty interval at the arena base is a live buffer under any world
witness: the `Inside` bound holds by the arena order, the ownership clause
holds because an empty interval is disjoint from everything, and the
contents clause is vacuous. -/
theorem ptxPhase2F_degLive {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {S Nd : List Nat} :
    PtxLiveBufferAt s S Nd (InitE.sourceBase, 0) (fun _ => 0) := by
  refine ⟨⟨le_rfl, hA.2.1⟩, ?_, ?_⟩
  · intro o ho j hj
    simp only [List.mem_singleton] at ho
    subst o
    exact Or.inl rfl
  · intro p h1 h2 _
    have hcon : p + 8 ≤ InitE.sourceBase := by simpa using h2
    exact absurd h1 (by omega)

/-! ## A `memW` transfer lemma -/

/-- Replacing the memory leaves `memW` unchanged at any address whose cell
image is unchanged. -/
theorem ptxPhase2F_memW_transfer {F : Type} {s : PanSemStateFiniteExact 64 F}
    {mem : BitVec 64 → HolWordLab 64} {a : Nat}
    (h : mem (BitVec.ofNat 64 a) = s.memory (BitVec.ofNat 64 a)) :
    memW { s with memory := mem } a = memW s a := by
  simp only [memW]
  rw [h]

/-! ## Call entry -/

/-- Any callee entered from a region-D' state keeps the guest invariant. -/
theorem ptxPhase2F_callEntry {fname : MlS} (arguments : List (ExpHOL 64)) :
    CallEntryOn ptxPhase2FDPrime GuestInv fname arguments := by
  intro F state values body callee ret hcode hP hargs hl
  exact guestInv_callEntry state callee hP.1.1.1.1.1.1.1.1.1.1.1

/-! ## Source-value sizes for the message stores -/

/-- The beacon-roots global holds a word, so its flatten is a single word. -/
theorem ptxPhase2F_be_length {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxMessageScalarReady buffers contents names s)
    (hv : evalAt s (.var .global (ofString "be")) = some v) :
    (flattenHOL v).length = 1 := by
  have hgw : GlobalsWord s := hp.1.1.1.2.2.2.2.2.2.2.2.2
  obtain ⟨w, hw⟩ := hgw "be" (by decide)
  simp only [evalAt, evalHOLExact] at hv
  rw [hw] at hv
  have hve : v = .val (.word w) := (Option.some.inj hv).symm
  subst hve
  simp [flattenHOL]

/-- A caller local holds a word, so its flatten is a single word. -/
theorem ptxPhase2F_local_length {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (name : String) (hn : name ∈ names)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hp : PtxMessageScalarReady buffers contents names s)
    (hv : evalAt s (.var .local (ofString name)) = some v) :
    (flattenHOL v).length = 1 := by
  obtain ⟨w, hw⟩ := hp.2 name hn
  have he : v = .val (.word w) := by
    simpa [evalAt, evalHOLExact, hw] using hv.symm
  simp [he, flattenHOL]

/-! ## The message stores -/

/-- A message write that misses the message-gas slot keeps the B-frame
together with the caller's message-gas word bound (a local, untouched by
memory writes). -/
theorem ptxPhase2F_keepMgasW_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (src : ExpHOL 64) (k n : Nat) (hk : k + n ≤ 22)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxMessageScalarReady buffers contents names s → evalAt s src = some v →
      (flattenHOL v).length = n) :
    Hoare (fun s => PtxMessageBScalarReady buffers contents names s ∧ PtxPhase2MgasW s)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) src)
      (fun r s => r = none →
        PtxMessageBScalarReady buffers contents names s ∧ PtxPhase2MgasW s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.1.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "m" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  exact ⟨⟨⟨phase2_message_store_ready_words buffers contents (flattenHOL v) hp.1.1.1 k
    (by rw [hlen s v hp.1.1 hv]; exact hk) hst, hp.1.1.2⟩,
    phase2_txBacking_message_words buffers contents (flattenHOL v) hp.1.1.1 hp.1.2.1 k
    (by rw [hlen s v hp.1.1 hv]; exact hk) hst, hp.1.2.2⟩, hp.2⟩

/-- A message write that misses the message-gas slot keeps the B-frame
together with the message-gas bound: the slot-5 cell is outside the write's
footprint, so its word is carried across the store. -/
theorem ptxPhase2F_keepM40_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (src : ExpHOL 64) (k n : Nat) (hk : k + n ≤ 22)
    (hmiss : k + n ≤ 5 ∨ 6 ≤ k)
    (hlen : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v,
      PtxMessageScalarReady buffers contents names s → evalAt s src = some v →
      (flattenHOL v).length = n) :
    Hoare (fun s => PtxMessageBScalarReady buffers contents names s ∧ ptxPhase2FM40 s)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * k)]) src)
      (fun r s => r = none →
        PtxMessageBScalarReady buffers contents names s ∧ ptxPhase2FM40 s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.1.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * k) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "m" + 8 * k) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  refine ⟨⟨⟨phase2_message_store_ready_words buffers contents (flattenHOL v) hp.1.1.1 k
    (by rw [hlen s v hp.1.1 hv]; exact hk) hst, hp.1.1.2⟩,
    phase2_txBacking_message_words buffers contents (flattenHOL v) hp.1.1.1 hp.1.2.1 k
    (by rw [hlen s v hp.1.1 hv]; exact hk) hst, hp.1.2.2⟩, ?_⟩
  have hA : ArenaOK s := hp.1.1.1.1.1.2
  have hin : Inside (locN s "m", 176) InitE.sourceBase (globN s "heap_ptr") :=
    hp.1.1.1.2.2.2.1
  have hb := (ivl_allocated_bound hA (Or.inl hin)).2
  have hlenv : (flattenHOL v).length = n := hlen s v hp.1.1 hv
  have hframe : mem (BitVec.ofNat 64 (locN s "m" + 40)) =
      s.memory (BitVec.ofNat 64 (locN s "m" + 40)) :=
    panMemStoresHOL_frame (flattenHOL v) (BitVec.ofNat 64 (locN s "m" + 8 * k))
      s.memory mem hst (BitVec.ofNat 64 (locN s "m" + 40))
      (fun j hj => by
        rw [hlenv] at hj
        rw [← BitVec.ofNat_add]
        intro heq
        have h1 : locN s "m" + 40 < 2 ^ 64 := by omega
        have h2 : locN s "m" + 8 * k + 8 * j < 2 ^ 64 := by omega
        have h3 := congrArg BitVec.toNat heq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h3
        omega)
  show ptxPhase2FM40 { s with memory := mem }
  show memW { s with memory := mem } (locN s "m" + 40) < 2 ^ 63
  rw [ptxPhase2F_memW_transfer hframe]
  exact hp.2

/-- The `mgas` store at slot 5 births the message-gas bound: the value
written is the caller's `mgas` word, bounded by `2 ^ 28` in the validated
caller frame. -/
theorem ptxPhase2F_mgasM40_store {ι : Type} [Nonempty ι]
    (buffers : ι → Ivl) (contents : ι → Nat → BitVec 64) (names : List String)
    (hn : ("mgas" : String) ∈ names) :
    Hoare (fun s => PtxMessageBScalarReady buffers contents names s ∧ PtxPhase2MgasW s)
      (.store (.op .add [.var .local (ofString "m"), .const (8 * 5)])
        (.var .local (ofString "mgas")))
      (fun r s => r = none →
        PtxMessageBScalarReady buffers contents names s ∧ ptxPhase2FM40 s) := by
  apply Hoare.store_fall
  intro F s x v mem hp hx hv hst
  obtain ⟨w, hw⟩ := hp.1.1.1.2.2.1
  have hl : locN s "m" = w.toNat := by simp [locN, hw]
  have he : x = w + BitVec.ofNat 64 (8 * 5) := by
    simpa [evalAt, evalHOLExact, evalListHOLExact, hw, valueIsWord, valueWord,
      panOpHOL, wordOpHOL, wordOp, List.foldr, BitVec.ofNat_mul] using hx.symm
  have hx' : x = BitVec.ofNat 64 (locN s "m" + 40) := by
    simp [he, hl, BitVec.ofNat_add]
  rw [hx'] at hst
  obtain ⟨wg, hwg⟩ := hp.1.1.2 "mgas" hn
  have hve : v = .val (.word wg) := by
    simpa [evalAt, evalHOLExact, hwg] using hv.symm
  have hfl : flattenHOL v = [HolWordLab.word wg] := by
    rw [hve]
    simp [flattenHOL]
  rw [hfl] at hst
  obtain ⟨hdom, hmem, hkeep⟩ := panMemStoresHOL_word_spec hst
  obtain ⟨wm2, hwg2, hbd⟩ := hp.2
  have hsame : wg = wm2 := by
    have h8 : ValueHOL.val (HolWordLab.word wg) = ValueHOL.val (HolWordLab.word wm2) :=
      Option.some.inj (hwg.symm.trans hwg2)
    injection h8 with h9
    injection h9 with h10
  rw [← hsame] at hbd
  refine ⟨⟨⟨phase2_message_store_ready_words buffers contents [HolWordLab.word wg] hp.1.1.1 5
    (by simp) hst, hp.1.1.2⟩,
    phase2_txBacking_message_words buffers contents [HolWordLab.word wg] hp.1.1.1 hp.1.2.1 5
    (by simp) hst, hp.1.2.2⟩, ?_⟩
  show ptxPhase2FM40 { s with memory := mem }
  show memW { s with memory := mem } (locN s "m" + 40) < 2 ^ 63
  have hval : memW { s with memory := mem } (locN s "m" + 40) = wg.toNat := by
    show (match mem (BitVec.ofNat 64 (locN s "m" + 40)) with
      | .word w => w.toNat) = wg.toNat
    rw [hmem]
  rw [hval]
  omega

/-! ## Resuming after `msg_new` -/

/-- Resuming after `msg_new` with the B-frame over the degenerate family:
the store-ready part from the allocation spec, `TxBacking` from the
tight-frame spec, the Phase 4 shapes survive the local restoration because
`m` is not a Phase 4 local, the four caller scalars survive because `m` is
not one of them, and the caller's message-gas word bound survives for the
same reason. -/
theorem ptxPhase2F_msg_new_resume (h : PtxCallees) :
    DecCallResumeOn ptxPhase2FDPrime
      (fun s => ptxPhase2FBScalar s ∧ PtxPhase2MgasW s)
      (ofString "m") (ofString "msg_new") [] := by
  intro F s vs body callee ret v post hc hp he hl hb
  have hW : WorldOK s := hp.1.1.1.1.1.1.1.1.1
  have hE : TxEnv s := hp.2.2.2.1
  have hTB : TxBacking s := hp.2.2.1
  have hp4 : R16Shards.PtxPhase4LocalShapes s := hp.2.2.2.2
  have hmg : PtxPhase2MgasW s := ptxValidatedStrong_mgas hp.1.1.1.1.1
  obtain ⟨S, Nd, hWT, -⟩ := hp.1.1.1.2
  have hdeg : ∀ i : Unit, ∃ S Nd, WorldTypedWith s S Nd ∧
      PtxLiveBufferAt s S Nd (ptxPhase2FDegBuf i) (ptxPhase2FDegCont i) :=
    fun _ => ⟨S, Nd, hWT, ptxPhase2F_degLive hW.1⟩
  have hsr := phase2_msg_new_store_ready h ptxPhase2FDegBuf ptxPhase2FDegCont s vs body
    callee ret v post hc ⟨hW, hE, hdeg⟩ he hl hb
  have htx := phase2_msg_new_txBacking s vs body callee ret v post hc ⟨hW, hE, hTB⟩ he hl hb
  refine ⟨⟨⟨hsr, ?_⟩, htx, phase2_p4Shapes_msg_new_resume s post v hp4⟩, ?_⟩
  · intro name hn
    simp only [ptxPhase2FNames, List.mem_cons] at hn
    rcases hn with rfl | rfl | rfl | rfl | hnil
    · have hlk : (setVarHOLFinite (ofString "m") v {post with locals := s.locals}).locals.lookup
          (ofString "te") = s.locals.lookup (ofString "te") := by
        have hne : ofString "m" ≠ ofString "te" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
      rw [hlk]
      exact hp.1.1.1.1.2.1
    · have hlk : (setVarHOLFinite (ofString "m") v {post with locals := s.locals}).locals.lookup
          (ofString "sender") = s.locals.lookup (ofString "sender") := by
        have hne : ofString "m" ≠ ofString "sender" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
      rw [hlk]
      exact hp.1.1.1.1.1.2.scalar "sender" (by simp)
    · have hlk : (setVarHOLFinite (ofString "m") v {post with locals := s.locals}).locals.lookup
          (ofString "mgas") = s.locals.lookup (ofString "mgas") := by
        have hne : ofString "m" ≠ ofString "mgas" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
      rw [hlk]
      exact hp.1.1.1.1.1.2.scalar "mgas" (by simp)
    · have hlk : (setVarHOLFinite (ofString "m") v {post with locals := s.locals}).locals.lookup
          (ofString "reservoir") = s.locals.lookup (ofString "reservoir") := by
        have hne : ofString "m" ≠ ofString "reservoir" := by decide
        simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
      rw [hlk]
      exact hp.1.1.1.1.1.2.scalar "reservoir" (by simp)
    · simp at hnil
  · obtain ⟨wg, hwg, hbd⟩ := hmg
    refine ⟨wg, ?_, hbd⟩
    have hlk : (setVarHOLFinite (ofString "m") v {post with locals := s.locals}).locals.lookup
        (ofString "mgas") = s.locals.lookup (ofString "mgas") := by
      have hne : ofString "m" ≠ ofString "mgas" := by decide
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne]
    rw [hlk]
    exact hwg

/-! ## The region bound -/

/-- The message-construction region (positions 69..77) as a bounded program:
the `msg_new` call, seven stores, and the tail, entering from the region-E
exit invariant and leaving with the scalar message frame together with the
message-gas bound. -/
theorem ptxPhase2F_bound (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (ht : TerminatingProgBoundedOn
      (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
        ptxPhase2FM40 s) tail b) :
    TerminatingProgBoundedOn ptxPhase2FDPrime
      (spinePlug 8 (spineAt 69 ptxCode) tail)
      (K.«msg_new» + b + 1) := by
  have he : spinePlug 8 (spineAt 69 ptxCode) tail =
      .decCall (ofString "m") .one (ofString "msg_new") []
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 0])
          (.var .global (ofString "be")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 8])
          (.var .local (ofString "te")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 16])
          (.var .local (ofString "sender")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 24])
          (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 40])
          (.var .local (ofString "mgas")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 48])
          (.var .local (ofString "reservoir")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 56])
          (.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "tx"), .const 160])))
          tail))))))) := by
    simp only [ptxCode, sourceFunctionEntry, Guest.Software.guestFn_process_transaction,
      spineAt, spinePlug]
    rfl
  have hs (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (addr src : ExpHOL 64) :
      TerminatingProgBoundedOn P (.store addr src) 0 := by
    intro F s hc hp hn
    rw [clock_store]
    exact ⟨by omega, le_rfl⟩
  have hcont : TerminatingProgBoundedOn
      (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
        PtxPhase2MgasW s)
      (.seq (.store (.op .add [.var .local (ofString "m"), .const 0])
          (.var .global (ofString "be")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 8])
            (.var .local (ofString "te")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 16])
            (.var .local (ofString "sender")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 24])
            (.load .one (.op .add [.var .local (ofString "tx"), .const 152])))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 40])
            (.var .local (ofString "mgas")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 48])
            (.var .local (ofString "reservoir")))
        (.seq (.store (.op .add [.var .local (ofString "m"), .const 56])
            (.load (.comb [.one, .one, .one, .one])
              (.op .add [.var .local (ofString "tx"), .const 160])))
          tail))))))) (0 + (0 + (0 + (0 + (0 + (0 + (0 + b))))))) := by
    exact seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          PtxPhase2MgasW s) _ _)
      (ptxPhase2F_keepMgasW_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
        (.var .global (ofString "be")) 0 1 (by decide)
        (ptxPhase2F_be_length ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames))
      (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          PtxPhase2MgasW s) _ _)
        (ptxPhase2F_keepMgasW_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
          (.var .local (ofString "te")) 1 1 (by decide)
          (ptxPhase2F_local_length ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
            "te" (by simp [ptxPhase2FNames])))
        (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          PtxPhase2MgasW s) _ _)
          (ptxPhase2F_keepMgasW_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
            (.var .local (ofString "sender")) 2 1 (by decide)
            (ptxPhase2F_local_length ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
              "sender" (by simp [ptxPhase2FNames])))
          (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          PtxPhase2MgasW s) _ _)
            (ptxPhase2F_keepMgasW_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
              (.load .one (.op .add [.var .local (ofString "tx"), .const 152])) 3 1
              (by decide)
              (fun s v hp hv => phase2_load_one_length s _ v hv))
            (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          PtxPhase2MgasW s) _ _)
              (ptxPhase2F_mgasM40_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
                (by simp [ptxPhase2FNames]))
              (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          ptxPhase2FM40 s) _ _)
                (ptxPhase2F_keepM40_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
                  (.var .local (ofString "reservoir")) 6 1 (by decide)
                  (Or.inr (by omega))
                  (ptxPhase2F_local_length ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
                    "reservoir" (by simp [ptxPhase2FNames])))
                (seq_bound_trans (hs (fun s => PtxMessageBScalarReady ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames s ∧
          ptxPhase2FM40 s) _ _)
                  (ptxPhase2F_keepM40_store ptxPhase2FDegBuf ptxPhase2FDegCont ptxPhase2FNames
                    (.load (.comb [.one, .one, .one, .one])
                      (.op .add [.var .local (ofString "tx"), .const 160])) 7 4 (by decide)
                    (Or.inr (by omega))
                    (fun s v hp hv => phase2_load_quad_length s _ v hv))
                  ht))))))
  have hmain : TerminatingProgBoundedOn ptxPhase2FDPrime
      (spinePlug 8 (spineAt 69 ptxCode) tail)
      (K.«msg_new» + (0 + (0 + (0 + (0 + (0 + (0 + (0 + b))))))) + 1) := by
    rw [he]
    exact TerminatingProgBoundedOn.decCall_on h.fb_msg_new (ofString "m") .one []
      (ptxPhase2F_callEntry [])
      (ptxPhase2F_msg_new_resume h) hcont
  intro F s hc hp hnt
  obtain ⟨h1, h2⟩ := hmain s hc hp hnt
  exact ⟨by omega, h2⟩

end InitECandidate.Solver.Wave8GuestInv.R13Shards
